open Types
open X86_global
module X = X86_var_global

let needs_patching (a: arg) (b: arg) : bool =
  match (a, b) with 
    | (Deref (_, _), Deref (_, _))
    | (Deref (_, _), GlobalArg _)
    | (GlobalArg _, Deref (_, _))
    | (GlobalArg _, GlobalArg _) -> true
    | _ -> false

let is_imm = function 
  | Imm _ -> true
  | _ -> false 

let is_reg = function 
  | Reg _ -> true
  | _ -> false 

let convert_block (b : X.binfo1 X.block) : block =
  let convert_arg (arg: X.arg) : arg = 
    match arg with
    | X.Imm i -> Imm i
    | X.Reg r -> Reg r
    | X.ByteReg br -> ByteReg br
    | X.Deref (r, i) -> Deref (r, i)
    | X.GlobalArg l -> GlobalArg l
    | X.Var _ -> 
        failwith "patch instructions: var encountered, error in assign homes"
  in
  let convert_instr (instr: X.instr) : instr list = 
    match instr with
    | X.Addq (a, b) -> 
        let a' = convert_arg a and b' = convert_arg b in
        if not (needs_patching a' b') then [Addq (a', b')]
        else [Addq (Reg Rax, b'); Movq (a', Reg Rax)]
    | X.Subq (a, b) -> 
        let a' = convert_arg a and b' = convert_arg b in
        if not (needs_patching a' b') then [Subq (a', b')]
        else [Subq (Reg Rax, b'); Movq (a', Reg Rax)]
    | X.Xorq (a, b) -> 
        let a' = convert_arg a and b' = convert_arg b in
        if not (needs_patching a' b') then [Xorq (a', b')]
        else [Xorq (Reg Rax, b'); Movq (a', Reg Rax)]
    | X.Andq (a, b) ->
        let a' = convert_arg a and b' = convert_arg b in
        if not (needs_patching a' b') then [Andq (a', b')]
        else [Andq (Reg Rax, b'); Movq (a', Reg Rax)]
    | X.Sarq (a, b) ->
      let a' = convert_arg a and b' = convert_arg b in
      if not (needs_patching a' b') then [Sarq (a', b')]
      else [Sarq (Reg Rax, b'); Movq (a', Reg Rax)]
    | X.Cmpq (a, b) ->
        let a' = convert_arg a and b' = convert_arg b in
        if needs_patching a' b' 
          then [Cmpq (Reg Rax, b'); Movq (a', Reg Rax)]
        else if (is_imm b')
          then [Cmpq (a', Reg Rax); Movq (b', Reg Rax)]
        else [Cmpq (a', b')]
    | X.Movq (a, a') when a = a' -> []
    | X.Movq (a, b) ->
        let a' = convert_arg a and b' = convert_arg b in
        if not (needs_patching a' b') then [Movq (a', b')]
        else [Movq (Reg Rax, b'); Movq (a', Reg Rax)]
    | X.Movzbq (a, a') when a = a' -> []
    | X.Movzbq (a, b) ->
        let a' = convert_arg a and b' = convert_arg b in
        if is_reg b' then [Movzbq (a', b')]
        else [Movq (Reg Rax, b'); Movzbq (a', Reg Rax)]
    | X.Set (c, a) -> [Set (c, convert_arg a)]
    | X.Negq a -> [Negq (convert_arg a)]
    | X.Pushq a -> [Pushq (convert_arg a)]
    | X.Popq a -> [Popq (convert_arg a)]
    | X.Callq (lbl, i) -> [Callq (lbl, i)]
    | X.Retq -> [Retq]
    | X.Jmp lbl -> [Jmp lbl]
    | X.JmpIf (c, lbl) -> [JmpIf (c, lbl)]
  in
  let (X.Block (X.Binfo1, instr_lst) ) = b in
    let instr_lst' =
      let rec convert_instructions
          (old_lst: X.instr list) (new_lst: instr list) : (instr list) = 
        match old_lst with 
          | [] -> List.rev new_lst
          | instr :: old_tail ->
              let new_lst' = List.append (convert_instr instr) new_lst 
              in convert_instructions old_tail new_lst'
      in convert_instructions instr_lst []
    in Block instr_lst'

let convert_info (i : X.info3) : info =
  let (X.Info3 info) = i in
  Info
    { locals_types= info.locals_types
    ; num_spilled= info.num_spilled
    ; num_spilled_root= info.num_spilled_root
    ; used_callee= info.used_callee }

let patch_instructions (prog : (X.info3, X.binfo1) X.program) : program =
  let (X.X86Program (info, lbs)) = prog in
  let info' = convert_info info in
  let lbs' = List.map (fun (lbl, block) -> (lbl, convert_block block)) lbs in
  X86Program (info', lbs')
