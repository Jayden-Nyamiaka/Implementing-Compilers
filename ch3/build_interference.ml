open Types
open X86_var

let convert_sexp_to_loc s =
  match s with
  | Var i -> VarL i
  | Reg i -> RegL i
  | Deref (a, b) -> StackL (a, b)
  | _ -> failwith "unhandled"

(* Build the interference graph. *)
let make_graph (g : LocUgraph.t) (lbs : (label * binfo2 block) list) :
    LocUgraph.t =
  let add_edge lst g curr =
    List.fold_left
      (fun g h -> if h <> curr then LocUgraph.add_edge_new g curr h else g)
      g lst
  in
  let add_edge_comp_two g (lst : location list) s d : LocUgraph.t =
    List.fold_left
      (fun g h -> if h <> s && h <> d then LocUgraph.add_edge_new g d h else g)
      g lst
  in
  let rec instr_helper g instr_lst initials afters_lst =
    match afters_lst with
    | [] -> g
    | afters :: tail -> (
        match instr_lst with
        | Addq (_, a) :: t | Subq (_, a) :: t | Negq a :: t | Popq a :: t ->
            let afters' = LocSet.elements afters in
            let g' = add_edge afters' g (convert_sexp_to_loc a) in
            instr_helper g' t initials tail
        | Movq (_, Imm _) :: t -> instr_helper g t initials tail
        | Movq (Imm _, b) :: t ->
            let afters' = LocSet.elements afters in
            let g' = add_edge afters' g (convert_sexp_to_loc b) in
            instr_helper g' t initials tail
        | Movq (a, b) :: t ->
            let afters' = LocSet.elements afters in
            let g' =
              add_edge_comp_two g afters' (convert_sexp_to_loc a)
                (convert_sexp_to_loc b)
            in
            instr_helper g' t initials tail
        | Callq (_, _) :: t ->
            let afters' = LocSet.elements afters in
            let g' =
              List.fold_left (add_edge afters') g
                (List.map (fun r -> RegL r) (RegSet.elements caller_save_regs))
            in
            instr_helper g' t initials tail
        | Jmp _ :: t | Pushq _ :: t | Retq :: t ->
            instr_helper g t initials tail
        | _ -> g)
  in
  let rec run_helper g (bls : binfo2 block list) =
    match bls with
    | Block (Binfo2 live, instrs) :: t ->
        let initial = live.initial in
        let afters = live.afters in
        let g' = instr_helper g instrs initial afters in
        run_helper g' t
    | _ -> g
  in
  let _, bls = List.split lbs in
  run_helper g bls

(* Replace the Binfo2 field in blocks with a placeholder Binfo1 field. *)
let replace_binfo (lbs : (label * binfo2 block) list) :
    (label * binfo1 block) list =
  List.map (fun (lbl, Block (_, instrs)) -> (lbl, Block (Binfo1, instrs))) lbs

let build_interference (program : (info1, binfo2) program) :
    (info2, binfo1) program =
  let (X86Program (info1, lbs)) = program in
  let (Info1 { locals_types = lts }) = info1 in
  let conflicts = make_graph LocUgraph.empty lbs in
  let lbs' = replace_binfo lbs in
  let info2 = Info2 { locals_types = lts; conflicts } in
  X86Program (info2, lbs')
