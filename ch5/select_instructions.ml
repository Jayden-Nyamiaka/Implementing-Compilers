open Support
open Utils
open Types
module C = Cloop
open X86_var_loop

(* Converts a C.tail into the equivalent X86_var instr list *)
let tail_instructions (i : C.tail) : instr list =
  let convert_atm (atm : C.atm) : arg =
    match atm with
      | C.Void -> Imm 0
      | C.Int i -> Imm i
      | C.Var i -> Var i
      | C.Bool b -> if b then Imm 1 else Imm 0
  in
  (* Helpers for selecting read and print instructions
   * Note that call_read is not a function *)
  let call_read = Callq (Label (fix_label "read_int"), 0)
  and call_print (arg : C.atm)  = 
    Callq (Label (fix_label "print_int"), 1) :: 
    Movq (convert_atm arg, Reg Rdi) :: []
  in
  let convert_assign (exp: C.exp) bl dest =
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
              | Reg Rax -> call_read :: bl
              | _ -> Movq (Reg Rax, dest) :: call_read :: bl)
          | `Read, _ -> failwith 
              "select instructions: calls to read should have no arguments"
          | `Print, [x] -> Movq (Imm 0, dest) :: (call_print x) @ bl
          | `Print, _ -> failwith 
              "select instructions: calls to print should have exactly 1 argument"
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
          | #cmp_op as c_op, [e1;e2]->
            let set = (match c_op with
              | `Eq -> Set (CC_e, ByteReg Al)
              | `Gt -> Set (CC_g, ByteReg Al)
              | `Ge -> Set (CC_ge, ByteReg Al)
              | `Lt -> Set (CC_l, ByteReg Al)
              | `Le -> Set (CC_le, ByteReg Al)
            ) in
              Movzbq (ByteReg Al, dest) :: set 
                :: Cmpq (convert_atm e2, convert_atm e1) :: bl
            | _ -> failwith 
                    "select instructions: convert_assign unexpected forms"
      )
  in
  let convert_primS (sop: stmt_op) (args: C.atm list) bl = 
    match (sop, args) with 
      | `Read, [] -> call_read :: bl
      | `Read, _ -> failwith 
          "select instructions: calls to read should have no arguments"
      | `Print, [x] -> (call_print x) @ bl
      | `Print, _ -> failwith 
          "select instructions: calls to print should have exactly 1 argument"
  in
  let rec helper (tail : C.tail) lst =
    match tail with
      | Return r -> Jmp (Label "conclusion") :: (convert_assign r lst (Reg Rax))
      | Seq (stmt, t) -> 
        let lst' =
          begin
            match stmt with 
              | Assign (v, e) -> convert_assign e lst (Var v)   
              | PrimS (sop, args) -> convert_primS sop args lst
          end
        in helper t lst'
      | Goto l -> Jmp l :: lst
      | IfStmt {op; arg1; arg2; jump_then; jump_else} ->
        Jmp jump_else :: JmpIf (cc_of_op op, jump_then) :: 
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
