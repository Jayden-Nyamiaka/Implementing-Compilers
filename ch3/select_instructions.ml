open Support
open Utils
open Types
module C = Cvar
open X86_var


let tail_instructions (i : C.tail) : instr list =
  let convert_atm (atm : C.atm) : arg =
    match atm with
      | Int i -> Imm i
      | Var i -> Var i
  in
  let convert_exp (exp: C.exp) bl dest =
    match exp with 
      | Atm i -> 
         Movq (convert_atm i, dest) :: bl
      | Negate i -> 
        Negq dest :: (Movq (convert_atm i, dest) :: bl)
      | Add (e1, e2) -> 
        Addq (convert_atm e2, dest) :: (Movq (convert_atm e1, dest) :: bl)
      | Sub (e1, e2) -> 
        Subq (convert_atm e2, dest) :: (Movq (convert_atm e1, dest) :: bl)
      | Read -> 
        ( match dest with
          | Reg Rax -> Callq (Label (fix_label "read_int"), 0) :: bl
          | _ -> Movq (Reg Rax, dest) :: (Callq (Label (fix_label "read_int"), 0) :: bl)
        )
  in
  let rec helper (tail : C.tail) lst =
    match tail with
      | Return r -> Jmp (Label "conclusion") :: (convert_exp r lst (Reg Rax))
      | Seq (Assign (v, e), t) -> (
          let block = convert_exp e lst (Var v) in
          helper t block
        )
  in List.rev (helper i [])

let convert_lt (lt : (Types.label * C.tail)) : Types.label * binfo1 block =
  let (lbl, tail) = lt in
  let block = Block (Binfo1, tail_instructions tail) in
    (lbl, block)

let convert_info (info : C.info) : info1 =
  let (C.Info { locals_types = vts }) = info in
    Info1 { locals_types = vts }

let select_instructions (prog : C.program) : (info1, binfo1) program =
  let (C.CProgram (info, lts)) = prog in
    X86Program (convert_info info, List.map convert_lt lts)  
