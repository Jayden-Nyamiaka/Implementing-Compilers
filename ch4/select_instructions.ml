open Support
open Utils
open Types
module C = Cif
open X86_var_if


let tail_instructions (i : C.tail) : instr list =
  let convert_atm (atm : C.atm) : arg =
    match atm with
      | C.Int i -> Imm i
      | C.Var i -> Var i
      | C.Bool b -> if b then Imm 1 else Imm 0
  in
  let convert_exp (exp: C.exp) bl dest =
    match exp with 
      | C.Atm i -> 
         Movq (convert_atm i, dest) :: bl
      | C.Prim (op, es) -> (
        match op, es with
          | `Add, [e1;e2] -> 
            Addq (convert_atm e2, dest) :: Movq (convert_atm e1, dest) :: bl
          | `Sub, [e1;e2] ->
            Subq (convert_atm e2, dest) :: Movq (convert_atm e1, dest) :: bl
          | `Read, [] ->
            (match dest with
              | Reg Rax -> Callq (Label (fix_label "read_int"), 0) :: bl
              | _ -> 
                Movq (Reg Rax, dest) :: 
                  Callq (Label (fix_label "read_int"), 0) :: bl)
          | `Negate, [i] ->
            Negq dest :: Movq (convert_atm i, dest) :: bl
          | `Not, [C.Var a] -> 
            (match dest with
                | Var v when a = v ->
                  Xorq (Imm 1, dest) :: bl
                | _ ->  
                  Xorq (Imm 1, dest) :: 
                  Movq (Var a, dest) :: bl)
          | `Not, [a] ->
            Xorq (Imm 1, dest) :: Movq (convert_atm a, dest) :: bl
          | #cmp_op as c_op, [e1;e2] ->
            let set = Set (cc_of_op c_op, ByteReg Al) in
              Movzbq (ByteReg Al, dest) :: set 
                :: Cmpq (convert_atm e2, convert_atm e1) :: bl
            | _ -> failwith "convert_exp: unexpected forms"
      )
  in
  let rec helper (tail : C.tail) lst =
    match tail with
      | Return r -> Jmp (Label "conclusion") :: (convert_exp r lst (Reg Rax))
      | Seq (Assign (v, e), t) -> (
          let block = convert_exp e lst (Var v) in
          helper t block)
      | Goto l -> Jmp l :: lst
      | IfStmt {op; arg1; arg2; jump_then; jump_else} ->
        let jmp_set = match op with
          | `Eq -> JmpIf (CC_e, jump_then)
          | `Gt -> JmpIf (CC_g, jump_then)
          | `Ge -> JmpIf (CC_ge, jump_then)
          | `Lt -> JmpIf (CC_l, jump_then)
          | `Le -> JmpIf (CC_le, jump_then) in
        Jmp jump_else :: jmp_set :: 
          Cmpq (convert_atm arg2, convert_atm arg1) :: lst
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
