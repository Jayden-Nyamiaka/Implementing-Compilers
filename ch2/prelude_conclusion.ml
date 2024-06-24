open Support
open Types
open Utils
module X = X86_int
open X86_asm

(* Code that has to be added to each program at the end. 
   It's parametrized on the stack space. *)
let epilog (ss : int) : instr list = 
  let main = fix_label "main" in
    [Global (Label main);

    Label main;
    Pushq (Reg Rbp);
    Movq ( (Reg Rsp), (Reg Rbp) );
    Subq ( (Imm ss), (Reg Rsp) ) ;
    Jmp (Label "start");

    Label "conclusion";
    Addq ( (Imm ss), (Reg Rsp) );
    Popq (Reg Rbp);
    Retq]

(* Convert a labelled block to a list of instructions. *)
let asm_of_lb (lb : (Types.label * X.block)) : instr list =
  let convert_arg = function
    | X.Imm i -> Imm i
    | X.Reg r -> Reg r
    | X.Deref (r, i) -> Deref (r, i)
  in
  let convert_instr = function
    | X.Addq (a, b) -> Addq (convert_arg a, convert_arg b)
    | X.Subq (a, b) -> Subq (convert_arg a, convert_arg b)
    | X.Negq a -> Negq (convert_arg a)
    | X.Movq (a, b) -> Movq (convert_arg a, convert_arg b)
    | X.Pushq a -> Pushq (convert_arg a)
    | X.Popq a -> Popq (convert_arg a)
    | X.Callq (lbl, _) -> Callq lbl
    | X.Retq -> Retq
    | X.Jmp lbl -> Jmp lbl
  in 
  match lb with 
    | (Types.Label lbl_str, X.Block instr_lst) -> 
        let instr_lst' = List.map convert_instr instr_lst in
        Label lbl_str :: instr_lst'

let prelude_conclusion (prog : X.program) : program =
  let (X.X86Program (info, lbs)) = prog in
  let Info { stack_space = ss } = info in
  let ep = epilog ss in
  let lbs' = List.concat_map asm_of_lb lbs in
    X86Program (lbs' @ ep)
