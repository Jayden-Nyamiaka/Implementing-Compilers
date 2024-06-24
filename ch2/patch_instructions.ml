open Types
open X86_int

module X = X86_var

let needs_patching (a: arg) (b: arg) : bool =
  match (a, b) with 
    | (Deref (_, _), Deref (_, _)) -> true
    | _ -> false

let convert_block (block : X.block) : block =
  let convert_arg (arg: X.arg) : arg = match arg with
    | X.Imm i -> Imm i
    | X.Reg r -> Reg r
    | X.Deref (r, i) -> Deref (r, i)
    | X.Var _ -> 
        failwith "patch instructions: var encountered, error in assign homes"
  in
  let convert_instr (instr: X.instr) : instr list = match instr with
    | X.Addq (a, b) -> 
        let a' = convert_arg a and b' = convert_arg b in
        if not (needs_patching a' b') then [Addq (a', b')]
        else [Addq (Reg Rax, b'); Movq (a', Reg Rax)]
    | X.Subq (a, b) -> 
        let a' = convert_arg a and b' = convert_arg b in
        if not (needs_patching a' b') then [Subq (a', b')]
        else [Subq (Reg Rax, b'); Movq (a', Reg Rax)]
    | X.Movq (a, b) -> 
        let a' = convert_arg a and b' = convert_arg b in
        if not (needs_patching a' b') then [Movq (a', b')]
        else [Movq (Reg Rax, b'); Movq (a', Reg Rax)]
    | X.Negq a -> [Negq (convert_arg a)]
    | X.Pushq a -> [Pushq (convert_arg a)]
    | X.Popq a -> [Popq (convert_arg a)]
    | X.Callq (lbl, i) -> [Callq (lbl, i)]
    | X.Retq -> [Retq]
    | X.Jmp lbl -> [Jmp lbl]
  in
  match block with
    | X.Block instr_lst ->
        let instr_lst' =
          let rec convert_instructions
              (old_lst: X.instr list) (new_lst: instr list) : (instr list) = 
            match old_lst with 
              | [] -> List.rev new_lst
              | instr :: old_tail ->
                  let new_lst' = List.append (convert_instr instr) new_lst in
                  convert_instructions old_tail new_lst'
          in convert_instructions instr_lst []
        in Block instr_lst'

(* x86var `Info2` corresponds to x86int `Info` *)
let convert_info (i : X.info2) : info =
  let (X.Info2 { stack_space = i }) = i in
    Info { stack_space = i }

let patch_instructions (prog : X.info2 X.program) : program =
  let (X.X86Program (info, lbs)) = prog in
  let info' = convert_info info in
  let lbs' =
    List.map
      (fun (lbl, block) -> (lbl, convert_block block))
      lbs
  in
    X86Program (info', lbs')
