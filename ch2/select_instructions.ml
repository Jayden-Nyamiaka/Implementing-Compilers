 open Support
open Utils
module C = Cvar
open X86_var

let convert_tail (tail : C.tail) : block = 
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
  let rec helper (tail : C.tail) bl =
    match tail with
      | Return r -> Jmp (Label "conclusion") :: (convert_exp r bl (Reg Rax))
      | Seq (Assign (v, e), t) -> (
          let block = convert_exp e bl (Var v) in
          helper t block
        )
  in Block (List.rev (helper tail []))


let convert_lt (l, t : (Types.label * C.tail)) : Types.label * block =
  l, convert_tail t

let convert_info (info : C.info) : info1 =
  let (C.Info { locals_types = vts }) = info in
    Info1 { locals_types = vts }

let select_instructions (prog : C.program) : info1 program =
  let (C.CProgram (info, lts)) = prog in
    X86Program (convert_info info, List.map convert_lt lts)  

