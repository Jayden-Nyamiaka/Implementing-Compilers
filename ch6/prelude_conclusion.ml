open Support
open Utils
open Types
open Alloc_utils
module X = X86_global
open X86_asm

let resize_initial_heap_size (n : int) : unit =
  begin
    if n < min_heap_size || n mod 8 <> 0 then
      failwithf "heap size must be divisible by 8 and >= %d" min_heap_size;
    init_heap_size := n
  end


(* Code that has to be added to each program at the end. 
   It's parameterized on the set of callee-save registers (`callee_saves`),
   the stack space (`ss`), and on the number of rootstack items (`rs`). *)
let epilog (callee_saves : RegSet.t) (ss : int) (rs : int) : instr list = 
  let callee_regs = RegSet.elements callee_saves in
  let main = fix_label "main" in
  let root_stack_bytes = 8 * rs in
  let rec clear_root_stack count = 
    if count == rs then []
    else Movq (Imm 0, Deref (R15, count * 8)) :: clear_root_stack (count + 1)
  in 
    Global (Label main) ::

    (* PRELUDE *)
    Label main ::

    (* Sets up base pointer *)
    Pushq (Reg Rbp) ::
    Movq (Reg Rsp, Reg Rbp) ::

    (* Pushes all callee-saved registers onto the stack *)
    (List.map (fun r -> Pushq (Reg r)) callee_regs) @

    (* Reserves extra stack space for stack-resident variables *)
    Subq ( (Imm ss), (Reg Rsp) ) ::

    (* Initializes garbage collector by calling the initialize function *)
    Movq (Imm !init_heap_size, Reg Rdi) :: (* arg1 = root stack size *)
    Movq (Imm !init_heap_size, Reg Rsi) :: (* arg2 = heap size *)
    Callq (Label (fix_label "initialize")) ::

    (* Initializes root stack by setting all root stack pointers to 0 *)
    Movq (GlobalArg (Rip, Label (fix_label "rootstack_begin")), Reg R15) ::
    (clear_root_stack 0) @

    (* Moves root stack pointer to the end of the rs *)
    Addq (Imm root_stack_bytes, Reg R15) :: 

    (* Ends prelude by jumping to start label *)
    Jmp (Label "start") ::

    (* CONCLUSION *)
    Label "conclusion" ::

    (* Resets root stack pointer by moving it back to the start of the rs *)
    Subq (Imm root_stack_bytes, Reg R15) ::

    (* Reclaim the extra stack space for stack-resident variables *)
    Addq (Imm ss, Reg Rsp) ::

    (* Pops all callee-saved registers off the stack *)
    (List.map (fun r -> Popq (Reg r)) (List.rev callee_regs) ) @

    (* Resets the base pointer and returns *)
    [Popq (Reg Rbp);
    Retq]


(* Convert a labelled block to a list of instructions. *)
let asm_of_lb (deref_adjust : int) (lb : label * X.block) : instr list =
  let convert_arg = function
    | X.Imm i -> Imm i
    | X.Reg r -> Reg r
    | X.ByteReg br -> ByteReg br
    | X.Deref (r, i) -> Deref (r, i - deref_adjust)
    | X.GlobalArg l -> GlobalArg (Rip, l)
  in
  let convert_instr = function
    | X.Addq (a, b) -> Addq (convert_arg a, convert_arg b)
    | X.Subq (a, b) -> Subq (convert_arg a, convert_arg b)
    | X.Negq a -> Negq (convert_arg a)
    | X.Xorq (a, b) -> Xorq (convert_arg a, convert_arg b)
    | X.Cmpq (a, b) -> Cmpq (convert_arg a, convert_arg b)
    | X.Andq (a, b) -> Andq (convert_arg a, convert_arg b)
    | X.Sarq (a, b) -> Sarq (convert_arg a, convert_arg b)
    | X.Set (c, a) -> Set (c, convert_arg a)
    | X.Movq (a, b) -> Movq (convert_arg a, convert_arg b)
    | X.Movzbq (a, b) -> Movzbq (convert_arg a, convert_arg b)
    | X.Pushq a -> Pushq (convert_arg a)
    | X.Popq a -> Popq (convert_arg a)
    | X.Callq (lbl, _) -> Callq lbl
    | X.Retq -> Retq
    | X.Jmp lbl -> Jmp lbl
    | X.JmpIf (c, lbl) -> JmpIf (c, lbl)
  in 
  match lb with 
    | (Types.Label lbl_str, X.Block instr_lst) -> 
        let instr_lst' = List.map convert_instr instr_lst in
        Label lbl_str :: instr_lst'


let prelude_conclusion (prog : X.program) : program =
  let X.X86Program (info, lbs) = prog in
  let X.Info { num_spilled; num_spilled_root; used_callee; _ } = info in
  let num_callees = RegSet.cardinal used_callee in
  (* Amount to shift all stack locations that are relative to %rbp: *)
  let deref_adjust = 8 * num_callees in
  let extra_stack_space =
    align_16 (8 * (num_spilled + num_callees)) - 8 * num_callees
  in
  let ep = epilog used_callee extra_stack_space num_spilled_root in
  let lbs' = List.concat_map (asm_of_lb deref_adjust) lbs in
    X86Program (lbs' @ ep)
