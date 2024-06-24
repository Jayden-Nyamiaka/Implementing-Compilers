open Types
open X86_var_global

(* converts sexp to location *)
let convert_sexp_to_loc s = 
  match s with
    | Var i ->  VarL i
    | Reg i ->  RegL i
    | Deref (a, _) ->  RegL a
    | ByteReg reg -> RegL (reg_of_bytereg reg)
    | _ -> failwith "convert_sexp_to_loc: unhandled cases"

(* Build the interference graph.
   `vvs` are the vector-valued variables. *)
let make_graph
  (g : LocUgraph.t) (lbs : (label * binfo2 block) list) (vvs : VarSet.t)
      : LocUgraph.t =
      let add_edge lst g curr = 
      List.fold_left
      (fun g -> fun h -> if h <> curr
                          then LocUgraph.add_edge_new g curr h else g)
      g lst
    in 
    let add_edge_comp_two g (lst : location list) s d : LocUgraph.t = 
      List.fold_left
      (fun g -> fun h -> if h <> s && h <> d 
                          then LocUgraph.add_edge_new g d h else g)
      g lst
    in 
    let rec get_regs afters' res =
      match afters' with
        | VarL v :: t when VarSet.mem v vvs -> get_regs t (VarL v :: res)
        | _ :: t -> get_regs t res
        | _ -> res
    in
    let rec instr_helper g instr_lst initials afters_lst = 
      match afters_lst with
        | [] -> g
        | afters :: tail ->
          let afters' = LocSet.elements afters in
          match instr_lst with
            | Addq (_, a) :: t
            | Subq (_, a) :: t
            | Negq a :: t
            | Set (_, a) :: t
            | Andq (_, a) :: t
            | Sarq (_, a) :: t
            | Xorq (_, a) :: t
            | Popq a :: t ->
              begin 
              match a with
                | GlobalArg _ -> instr_helper g t initials tail
                | _ ->
                  let g' = add_edge afters' g (convert_sexp_to_loc a) in 
                  instr_helper g' t initials tail
              end
            | Cmpq (_, _) :: t ->
              let g' = add_edge afters' g (RegL Rflags) in
              instr_helper g' t initials tail
            | Movzbq (a, b) :: t
            | Movq (a, b) :: t ->
              begin
                match a, b with
                  | _, GlobalArg _ -> instr_helper g t initials tail
                  | GlobalArg _, _ 
                  | Imm _, _ ->
                    let g' = add_edge afters' g (convert_sexp_to_loc b) in 
                    instr_helper g' t initials tail
                  | _, Imm _ ->
                    instr_helper g t initials tail
                  | _, _ -> 
                    let g' = add_edge_comp_two g afters' 
                        (convert_sexp_to_loc a) (convert_sexp_to_loc b) in
                    instr_helper g' t initials tail
              end
            | Callq (Label "collect", _) :: t ->
              let g' = List.fold_left (add_edge afters') g 
                (List.map (fun r -> RegL r) (RegSet.elements caller_save_regs)) in
              let g'' = List.fold_left (add_edge (get_regs afters' [])) g'
              (List.map (fun r -> RegL r) (RegSet.elements callee_save_regs)) in
              instr_helper g'' t initials tail
            | Callq (_, _) :: t ->
              let g' = List.fold_left 
                (add_edge afters') g 
                (List.map (fun r -> RegL r) (RegSet.elements caller_save_regs)) in
              instr_helper g' t initials tail
            | Jmp _ :: t
            | Pushq _ :: t
            | Retq :: t -> instr_helper g t initials tail
            | _ -> g
    in
    let rec run_helper g (bls : (binfo2 block) list)  = 
      match bls with
        | Block (Binfo2 live, instrs) :: t -> 
          let initial = live.initial in
          let afters = live.afters in
          let g' = instr_helper g instrs initial afters in 
          run_helper g' t
        | _ -> g
    in
    let (_, bls) = List.split lbs in 
    run_helper g bls

(* Replace the Binfo2 field in blocks with a placeholder Binfo1 field. *)
let replace_binfo (lbs : (label * binfo2 block) list)
      : (label * binfo1 block) list =
  List.map
    (fun (lbl, Block (_, instrs)) -> (lbl, Block (Binfo1, instrs)))
    lbs

(* Collect the vector-typed vars. *)
let vector_vars (lts : (var * ty) list) : VarSet.t =
  let is_vector = function
    | Vector _ -> true
    | _ -> false
  in
    lts
     |> List.filter_map (fun (v, t) -> if is_vector t then Some v else None)
     |> VarSet.of_list

let build_interference
      (program : (info1, binfo2) program) : (info2, binfo1) program =
  let (X86Program (info1, lbs)) = program in
  let Info1 { locals_types = lts } = info1 in
  let vvs = vector_vars lts in
  let conflicts = make_graph LocUgraph.empty lbs vvs in
  let lbs' = replace_binfo lbs in
  let info2 = Info2 { locals_types = lts; conflicts } in
    X86Program (info2, lbs')
