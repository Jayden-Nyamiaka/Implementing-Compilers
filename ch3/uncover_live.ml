open Types

module X = X86_var


(* Compute the live sets for the instructions of a single labelled block. *)
let uncover_live_in_block
      (label_map : LocSet.t LabelMap.t) (instrs : X.instr list) : X.live =
  let arg_to_location = function
    | X.Imm _ -> None
    | X.Reg r -> Some (RegL r)
    | X.Deref (r, i) -> Some (StackL (r, i))
    | X.Var v -> Some (VarL v)
  in

  let add_to_locset (arg : X.arg) (set : LocSet.t) : LocSet.t = 
    match arg_to_location arg with
      | None -> set
      | Some x -> LocSet.add x set
  and remove_from_locset (arg :X.arg) (set : LocSet.t) : LocSet.t = 
    match arg_to_location arg with
      | None -> set
      | Some x -> LocSet.remove x set
  in
  
  let compute_live_before_instr (live_sets : LocSet.t list) (instr : X.instr) 
                                                          : LocSet.t list = 
    let after = List.hd live_sets in
    let before = match instr with 
      | X.Jmp lbl -> LabelMap.find lbl label_map
      | X.Addq (r1, r2)
      | X.Subq (r1, r2) -> 
        let after' = add_to_locset r1 after in
        add_to_locset r2 after'
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
            match (idx, args) with
              | (0, _) -> aft
              | (_, []) -> failwith
                   "add_read_regs: at least one register required for call"
              | (_, h :: t) ->
                add_read_regs (idx - 1) t (LocSet.add (RegL h) aft)
          in add_read_regs i Types.arg_passing_regs after'
    in before :: live_sets 
  in

  let rev_instrs = List.rev instrs in
  let final_set = 
    match (List.hd rev_instrs) with 
      | X.Jmp lbl -> LabelMap.find lbl label_map
      | _ -> failwith "last instruction should be a jmp instruction"
  in
    let live_sets = List.fold_left compute_live_before_instr 
              [final_set; LocSet.empty] (List.tl rev_instrs)
    in {initial = List.hd live_sets; afters = List.tl live_sets}

let uncover_live
      (prog : (X.info1, X.binfo1) X.program)
      : (X.info1, X.binfo2) X.program =
  let (X.X86Program (info, lbs)) = prog in
  (* `live_before_labels` is a map from labels to live-before sets,
   * for the benefit of any `jmp` instructions.
   * Here there is only one relevant label: `conclusion`.
   * We assume that the conclusion uses the registers %rax and %rsp. *)
  let (live_before_labels : LocSet.t LabelMap.t) =
    let concset = LocSet.of_list [RegL Rax; RegL Rsp] in
      LabelMap.singleton (Label "conclusion") concset
  in
  let (lbs' : (label * X.binfo2 X.block) list) =
    List.map
      (fun (lbl, block) ->
         let (X.Block (_, instrs)) = block in
         let live = uncover_live_in_block live_before_labels instrs in
         let block' = X.Block (X.Binfo2 live, instrs) in
           (lbl, block'))
      lbs
  in
    X.X86Program (info, lbs')
