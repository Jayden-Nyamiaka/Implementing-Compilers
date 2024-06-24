(** Abstract x86 assembly language. *)

open Types

type arg =
  | Imm       of int
  | Reg       of reg
  | ByteReg   of bytereg
  | Deref     of reg * int
  | GlobalArg of reg * label  (* address of label, offset by %rip register *)
[@@deriving sexp]

type instr = 
  | Addq   of arg * arg
  | Subq   of arg * arg
  | Negq   of arg
  | Xorq   of arg * arg
  | Cmpq   of arg * arg
  | Andq   of arg * arg
  | Sarq   of arg * arg
  | Set    of cc * arg
  | Movq   of arg * arg
  | Movzbq of arg * arg
  | Pushq  of arg
  | Popq   of arg
  | Callq  of label
  | Retq
  | Jmp    of label
  | JmpIf  of cc * label
  | Label  of string
  | Global of label
[@@deriving sexp]

(** The type of an x86 program. *)
type program = 
  X86Program of instr list
[@@deriving sexp]
