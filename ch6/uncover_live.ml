open Types

module X = X86_var_global

(* Flag; when true, extra debugging information is printed. *)
let _debug = ref false

let rflags_reg = X.Reg Rflags


(* Compute the live sets for the instructions of a single labelled block.
 * The `live_before_map` is the live-before sets for each block named
 * by the given labels. *)
let uncover_live_in_block
      (live_before_map : LocSet.t LabelMap.t) (instrs : X.instr list)
        : X.live =
        let arg_to_location arg =
          match arg with 
          | X.Imm _ -> None
          | X.Reg r -> Some (RegL r)
          | X.ByteReg br -> Some (RegL (reg_of_bytereg br))
          (* Changed from StackL (r, i) in ch5 *)
          | X.Deref (r, _) -> Some (RegL r)
          | X.Var v -> Some (VarL v)
          | X.GlobalArg _ -> None
      in
    
      let add_to_locset (arg : X.arg) (set : LocSet.t) : LocSet.t = 
        let loc_opt = arg_to_location arg in
          if loc_opt = None then set
          else LocSet.add (Option.get loc_opt) set
      and remove_from_locset (arg : X.arg) (set : LocSet.t) : LocSet.t = 
        let loc_opt = arg_to_location arg in
          if loc_opt = None then set
          else LocSet.remove (Option.get loc_opt) set
      in
      
      let find_label lbl m = 
        let opt = LabelMap.find_opt lbl m in
        if opt != None then Option.get opt else failwith 
            ("uncover live: no mapping found for label " ^ (string_of_label lbl)
            ^ " in uncover_live_in_block")
      in
      let compute_live_before_instr (live_sets : LocSet.t list) (instr : X.instr)
                                                              : LocSet.t list = 
        let after = List.hd live_sets in
        let before = match instr with 
          | X.JmpIf (_, lbl) -> 
            let after' = LocSet.union (find_label lbl live_before_map) after
            in add_to_locset rflags_reg after'
          | X.Jmp lbl -> find_label lbl live_before_map
          | X.Addq (r1, r2)
          | X.Subq (r1, r2) 
          | X.Andq (r1, r2)
          | X.Xorq (r1, r2) -> 
            let after' = add_to_locset r1 after in
            add_to_locset r2 after'
          | X.Cmpq (r1, r2) ->
            let after' = remove_from_locset rflags_reg after in
            let after'' = add_to_locset r1 after' in
              add_to_locset r2 after''
          | X.Set (_, w) -> 
            let after' = add_to_locset rflags_reg after in
            remove_from_locset w after'
          | X.Movzbq (r, w)
          | X.Movq (r, w) -> 
            let after' = remove_from_locset w after in
            add_to_locset r after'
          | X.Negq r 
          | X.Sarq (_, r)
          | X.Pushq r
          | X.Popq r -> add_to_locset r after
          | X.Retq -> after
          | X.Callq (_, i) ->
              let after' =
                RegSet.fold 
                  (fun reg aft -> LocSet.remove (RegL reg) aft)
                Types.caller_save_regs after
              in
              let rec add_read_regs idx args aft = 
                if idx = 0 then aft
                else add_read_regs (idx - 1) (List.tl args) 
                        (LocSet.add (RegL (List.hd args)) aft)
              in add_read_regs i Types.arg_passing_regs after'
        in before :: live_sets 
      in
    
      let rev_instrs = List.rev instrs in
      let final_set = 
        match (List.hd rev_instrs) with 
          | X.Jmp lbl -> find_label lbl live_before_map
          | _ -> failwith 
                  "uncover live: Last instruction should be a jmp instruction"
      in
        let live_sets = List.fold_left compute_live_before_instr 
                  [final_set; LocSet.empty] (List.tl rev_instrs)
        in {initial = List.hd live_sets; afters = List.tl live_sets}

(* Get the next jump labels, if any.
 * The jump instructions should only be at the end of the block,
 * but we can accumulate all of them, since you can have two
 * jumps at the end (one conditional, one not). *)
let get_next_labels (block : 'a X.block) : LabelSet.t =
  let (X.Block (_, instrs)) = block in
  let rec collect_jmp_labels 
          (instrs : X.instr list) (lbls : LabelSet.t) : LabelSet.t =
      match instrs with
        | [] -> lbls
        | h :: t -> 
            let lbls' = match h with
              | Jmp lbl
              | JmpIf (_, lbl) -> LabelSet.add lbl lbls
              | _ -> lbls
            in collect_jmp_labels t lbls'
    in collect_jmp_labels instrs LabelSet.empty

(* Liveness algorithm (dataflow analysis, but not generic):
 * - Create an empty (imperative) queue.
 * - Create an initial liveness map from labels to empty locsets
 *   (except for the "conclusion" label, which has a fixed set of registers).
 * - Add all the labels (except "conclusion") to a queue.
 * - Repeat until the queue is empty:
 *   - Pop a label off the queue.
 *   - Get the instructions corresponding to the label.
 *   - Use the liveness map to get the old live-before set for the instructions.
 *   - Compute the new live-before set for the instructions.
 *   - If the live-before set has changed:
 *     - Update the liveness map.
 *     - Find the labels of the blocks that project to the current label's
 *       block, and add them to the queue.
 * - Return the liveness map.
 * NOTE: Make sure to never add the label "conclusion" to the queue!
 * It has no corresponding instructions.
 *)
let compute_liveness
    (g    : LabelDgraph.t)
    (imap : (X.instr list) LabelMap.t)
      : LocSet.t LabelMap.t =
      let find_label lbl m = 
        let opt = LabelMap.find_opt lbl m in
        if opt != None then Option.get opt else failwith 
            ("uncover live: no mapping found for label " ^ (string_of_label lbl)
            ^ " in compute_liveness")
      in
      let queue = Queue.create () in
      let qpush lbl = 
        if (string_of_label lbl) != "conclusion" then Queue.add lbl queue
      in
      let (live_before_map : LocSet.t LabelMap.t) = 
        LabelMap.map (fun _ -> LocSet.empty) imap in
      let _ = LabelMap.iter (fun lbl _ -> qpush lbl) live_before_map in
      let live_before_map' = LabelMap.add (Label "conclusion") 
                  (LocSet.of_list [RegL Rax; RegL Rsp]) live_before_map in
      let rec fixpoint_iter livemap = 
        let top = (Queue.take_opt queue) in  
          if top = None then livemap
        else let lbl = Option.get top in
        let (instrs : X.instr list) = find_label lbl imap in
        let (old_live_before : LocSet.t) = find_label lbl livemap in
        let (new_live : X.live) = uncover_live_in_block livemap instrs in
        if (LocSet.equal old_live_before new_live.initial) 
          then fixpoint_iter livemap
          else 
            let livemap' = LabelMap.add lbl new_live.initial livemap in
            let (points_to : label list) = LabelDgraph.neighbors_in g lbl in
            let _ = List.iter (fun lbl -> qpush lbl) points_to in
              fixpoint_iter livemap'
      in fixpoint_iter live_before_map'

let uncover_live
    (prog : (X.info1, X.binfo1) X.program) : (X.info1, X.binfo2) X.program =
  let (X.X86Program (info, lbs)) = prog in

  (* Generate the control-flow graph from the (label, block) pairs. *)
  let cfg =
    LabelDgraph.of_alist lbs
      (fun bl -> get_next_labels bl |> LabelSet.elements)
  in

  (* Create a label->instrs map. *)
  let (imap : (X.instr list) LabelMap.t) =
    lbs
      |> List.map (fun (lbl, X.Block (_, instrs)) -> (lbl, instrs))
      |> LabelMap.of_list
  in

  (* Compute all the live-before sets. *)
  let (live_before_sets : LocSet.t LabelMap.t) =
    compute_liveness cfg imap
  in

  (* We run the liveness computation one last time after computing
   * all the live-before sets to get the full liveness information
   * for a block.  This is a little inefficient; we could generate it
   * in the `compute_liveness` function while computing the
   * live-before sets and return that directly.
   * IMO this is a bit cleaner and easier to debug. *)
  let get_live (lbl : label) : X.live =
    let instrs =
      LabelMap.find_or_fail lbl imap
        ~err_msg:
          (Printf.sprintf "uncover_live: no instructions for label (%s)"
             (string_of_label lbl))
    in
      uncover_live_in_block live_before_sets instrs
  in

  (* Rewrite the label/block information with new block info containing
   * the liveness information. *)
  let lbs' =
    List.map
      (fun (lbl, X.Block (_, instrs)) ->
         let b = X.Binfo2 (get_live lbl) in
           (lbl, X.Block (b, instrs)))
      lbs
  in
    X.X86Program (info, lbs')
