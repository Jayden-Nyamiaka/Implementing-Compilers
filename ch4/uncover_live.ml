open Types

module X = X86_var_if

let rflags_reg = X.Reg Rflags


(* Compute the live sets for the instructions of a single labelled block.
 * The `live_before_map` is the live-before sets for each block named
 * by the given labels. *)
let uncover_live_in_block
      (label_map : LocSet.t LabelMap.t) (instrs : X.instr list) : X.live =
  let arg_to_location = function
    | X.Imm _ -> None
    | X.Reg r -> Some (RegL r)
    | X.ByteReg br -> Some (RegL (reg_of_bytereg br))
    | X.Deref (r, i) -> Some (StackL (r, i))
    | X.Var v -> Some (VarL v)
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
  
  let compute_live_before_instr (live_sets : LocSet.t list) (instr : X.instr) 
                                                          : LocSet.t list = 
    let after = List.hd live_sets in
    let before = match instr with 
      | X.JmpIf (_, lbl) -> 
        let after' = LocSet.union (LabelMap.find lbl label_map) after in
          add_to_locset rflags_reg after'
      | X.Jmp lbl -> LabelMap.find lbl label_map
      | X.Addq (r1, r2)
      | X.Subq (r1, r2) 
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
      | X.Jmp lbl -> LabelMap.find lbl label_map
      | _ -> failwith "Uncover live: Last instruction should be a jmp instruction"
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
    let rec collect_jmp_labels (instrs : X.instr list) (lbls : LabelSet.t) : LabelSet.t =
      match instrs with
        | [] -> lbls
        | h :: t -> 
            let lbls' = match h with
              | Jmp lbl
              | JmpIf (_, lbl) -> LabelSet.add lbl lbls
              | _ -> lbls
            in collect_jmp_labels t lbls'
    in collect_jmp_labels instrs LabelSet.empty


(* Find the correct order of the labels for liveness analysis.
 * Algorithm:
 * 1) Compute the next labels for each block.
 * 2) Use the block labels and next labels to define a list of CFG edges.
 * 3) Filter out any edges that have "conclusion" as their target.
 *    a) If the graph has no edges, it should only have one label;
 *       return a singleton list of that label.
 *    b) Otherwise:
 *       1) Construct a label graph from the list of edges.
 *       2) Do a topological sort of the transpose of the graph. *)
let order_labels (lbs : (label * 'a X.block) list) : label list =
  (* Makes a map from each block label to a LabelSet of its next labels *)
  let make_next_labels_map 
          (lbs : (label * 'a X.block) list) : LabelSet.t LabelMap.t = 
    List.fold_left 
      (fun m (lbl, block) -> LabelMap.add lbl (get_next_labels block) m) 
      LabelMap.empty lbs 
  in
  let list_graph_edges 
          (lbl_map : LabelSet.t LabelMap.t) : (label * label) list =
    LabelMap.fold 
      (fun (from : label) (tos : LabelSet.t) 
            (lbls : (label * label) list) : (label * label) list ->
        (List.concat_map 
          (fun (Label s as next) -> 
            if s = "conclusion" then [] else [(from, next)])
          (LabelSet.elements tos)
        ) @ lbls) 
      lbl_map []
  in 
    match lbs with 
      | [] -> failwith "Uncover live: There should be at least one label"
      | [(lbl, _)] -> [lbl]
      | _ -> 
        let next_lbls_map = make_next_labels_map lbs in
        let graph_edges_lst = list_graph_edges next_lbls_map in
        let lbl_graph = LabelMgraph.of_list graph_edges_lst in
          LabelMgraph.topological_sort (LabelMgraph.transpose lbl_graph)
    
          
let uncover_live
    (prog : (X.info1, X.binfo1) X.program) : (X.info1, X.binfo2) X.program =
  let (X.X86Program (info, lbs)) = prog in
  let labels_ordered = order_labels lbs in
  (* `live_before_labels` is a map from labels to live-before sets,
   * for the benefit of any `jmp` instructions.
   * To start with, there is only one relevant label: `conclusion`. *)
  let (live_before_labels : LocSet.t LabelMap.t) =
    let concset = LocSet.of_list [RegL Rax; RegL Rsp] in
      LabelMap.singleton (Label "conclusion") concset
  in
  let lbs_map = LabelMap.of_list lbs in
  (* Go through the labels in the correct order and
   * 1) extract the instructions for the label,
   * 2) compute the liveness data for the instructions,
   * 3) compute the new info field and the new block,
   *    and add it to the new label/block map,
   * 4) and update the live_before_labels for future labels.
   *)
  let (_, lbs_map') =
    List.fold_left
      (fun (live_before_labels_prev, new_lbs_map) lbl ->
        let block_opt = LabelMap.find_opt lbl lbs_map in
        let (X.Block (_, instrs)) = 
          if block_opt = None 
            then failwith "Uncover live: No binding for label"
            else Option.get block_opt
        in
        let live = uncover_live_in_block live_before_labels_prev instrs in
          (LabelMap.add lbl (live.initial) live_before_labels_prev, 
          LabelMap.add lbl (X.Block (X.Binfo2 live, instrs)) new_lbs_map))
      (live_before_labels, LabelMap.empty) labels_ordered
  in
  let lbs' = LabelMap.bindings lbs_map' in
    X.X86Program (info, lbs')
