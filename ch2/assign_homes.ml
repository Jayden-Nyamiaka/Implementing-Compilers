open Support
open Types
open X86_var

let assign_homes (prog : info1 program) : info2 program =
  let create_homes_map (info: info1) : (int VarMap.t) = 
    let rec add_vars_to_homes_map lst m counter = 
      match lst with
        | [] -> m
        | (v, _) :: t -> 
          add_vars_to_homes_map t (VarMap.add v (counter) m) (counter - 8)
    in
    match info with 
      | Info1 tup -> 
          add_vars_to_homes_map tup.locals_types VarMap.empty (-8)
  in 
  match prog with 
    | X86Program (info1, prog_lst) ->
      let map = create_homes_map info1 in
        let info2 = 
          Info2 ({stack_space = (Utils.align_16 ((VarMap.cardinal map) * 8)) })
        and convert_var_to_deref (a: arg) : arg =
          match a with 
            | Imm _
            | Reg _
            | Deref (_, _) -> a
            | Var v -> 
              match VarMap.find_opt v map with
                | Some loc -> Deref (Rbp, loc)
                | None -> 
                    failwith "assign homes: var has no assigned stack location"
        in
        let rec switch_vars_to_derefs 
              (old_lst: instr list) (new_lst: instr list) : (instr list) = 
          match old_lst with 
            | [] -> List.rev new_lst
            | instr :: old_tail ->
              let instr' = match instr with 
                | Addq (a, b) -> 
                    Addq (convert_var_to_deref a, convert_var_to_deref b)
                | Subq (a, b) -> 
                    Subq (convert_var_to_deref a, convert_var_to_deref b)
                | Negq a -> 
                    Negq (convert_var_to_deref a)
                | Movq (a, b) -> 
                    Movq (convert_var_to_deref a, convert_var_to_deref b)
                | Pushq a -> 
                    Pushq (convert_var_to_deref a)
                | Popq a -> 
                    Popq (convert_var_to_deref a)
                | Callq (_, _)
                | Retq
                | Jmp _ -> instr
              in switch_vars_to_derefs old_tail (instr' :: new_lst)
        in
        let prog_lst' =
          match (List.hd prog_lst) with 
            | (label, block) ->
              match block with 
                | Block instr_lst -> 
          [(label, Block (switch_vars_to_derefs instr_lst []))]
        in X86Program (info2, prog_lst')    
