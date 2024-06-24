open Support
open Types
open Utils
module C = Ctup
open X86_var_global

(* NOTE: `fix_label` is needed for global variables as well as functions.
   MacOS, for instance, puts `_` before the names of both in assembly code. *)


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
    Movq (convert_atm arg, Reg Rdi) :: [] in 
  let make_tuple_tag (len : int) (vec : ty array) : int =
    if len < 0 || len > 50 then
      failwith "make_tuple_tag: len out of bound"
    else
      let rec dec_to_bin y str count = 
        match y, count with 
        | 0, 6 -> str
        | 0, i -> 
          dec_to_bin 0 ("0" ^ str) (i + 1)
        | _ -> dec_to_bin (y/2) ((string_of_int (y mod 2)) ^ str) (count + 1)
      in
      let rec helper res vec =
        match vec with
          | [] -> res
          | Vector _ :: t -> helper (res ^ "1") t
          | _ :: t -> helper (res ^ "0") t
      in
      int_of_string ("0b" ^ helper "" (Array.to_list vec) ^ (dec_to_bin len "" 0) ^ "1")
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
      | C.GlobalVal v ->
        Movq (GlobalArg (Label (fix_label v)), dest) :: bl
      | C.Allocate (i, Vector tys) ->
        let tag = make_tuple_tag i tys in 
        [Movq (Reg R11, dest); Movq (Imm tag, Deref (R11, 0)); 
          Addq (Imm (8 * (i + 1)), GlobalArg (Label (fix_label "free_ptr")));
          Movq (GlobalArg (Label (fix_label "free_ptr")), Reg R11)] @ bl
      | C.VecLen a ->
        [Movq (Reg Rax, dest); Sarq (Imm 1, Reg Rax); Andq (Imm 126, Reg Rax);
        Movq (Deref (R11, 0), Reg Rax); Movq (convert_atm a, Reg R11)] @ bl
      | C.VecRef (a, i) ->
        Movq (Deref (R11, 8 * (i + 1)), dest) :: Movq (convert_atm a, Reg R11) :: bl
      | C.VecSet (a1, i, a2) ->
        [Movq (Imm 0, dest); Movq (convert_atm a2, Deref (R11, 8 * (i + 1))); 
        Movq (convert_atm a1, Reg R11)] @ bl
      | _ -> failwith "convert_assign: unexpected type"
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
              | Collect i ->
                [Callq (Label (fix_label "collect"), 2); Movq (Imm i, Reg Rsi); 
                Movq (Reg R15, Reg Rdi)] @ lst
              | VecSetS (a1, i, a2) -> 
                [Movq (convert_atm a2, Deref (R11, 8 * (i + 1)));
                Movq (convert_atm a1, Reg R11)] @ lst
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

