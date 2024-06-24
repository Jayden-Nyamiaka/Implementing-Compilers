open Support
open Types
open Utils
module X = X86_int
open X86_asm

(* Code that has to be added to each program at the end. 
   It's parameterized on the stack space
   and the callee-save registers. *)
let epilog (callee_saves : RegSet.t) (ss : int) : instr list = 
  let callee_regs = RegSet.elements callee_saves
  and main = fix_label "main" in
    Global (Label main) ::

    Label main ::
    Pushq (Reg Rbp) ::
    Movq ( (Reg Rsp), (Reg Rbp) ) ::

    (List.map (fun r -> Pushq (Reg r)) callee_regs) @

    Subq ( (Imm ss), (Reg Rsp) ) ::
    Jmp (Label "start") ::

    Label "conclusion" ::
    Addq ( (Imm ss), (Reg Rsp) ) ::

    (List.map (fun r -> Popq (Reg r)) (List.rev callee_regs) ) @

    [Popq (Reg Rbp);
    Retq]


(* Convert a labelled block to a list of instructions. *)
let asm_of_lb (deref_adjust : int) (lb : label * X.block) : instr list =
  let convert_arg = function
    | X.Imm i -> Imm i
    | X.Reg r -> Reg r
    | X.Deref (r, i) -> Deref (r, i - deref_adjust)
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


let prelude_conclusion (X.X86Program (info, lbs)) =
  let X.Info { num_spilled; used_callee; _ } = info in
  let num_callees = RegSet.cardinal used_callee in
  (* Amount to shift all stack locations that are relative to %rbp: *)
  let deref_adjust = 8 * num_callees in
  let extra_stack_space =
    align_16 (8 * (num_spilled + num_callees)) - 8 * num_callees
  in
  let ep = epilog used_callee extra_stack_space in
  let lbs' = List.concat_map (asm_of_lb deref_adjust) lbs in
    X86Program (lbs' @ ep)
