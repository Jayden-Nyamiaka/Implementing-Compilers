(** Common types. *)

open Sexplib
open Support.Functors

type sexp = Sexp.t

(** Variable names. *)
type var = string
[@@deriving sexp]

module VarSet : SetS.S with type elt = var
module VarMap : MapS.S with type key = var
              
(** Environments. *)
module Env = VarMap

(** Jump labels. *)
type label = Label of string
[@@deriving sexp]

(** Registers. *)
type reg =
  | Rsp | Rbp | Rax | Rbx | Rcx | Rdx | Rsi | Rdi
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15
[@@deriving sexp]

(** Convert a register to a string. *)
val string_of_reg : reg -> string

(** Types. *)
type ty = Integer
[@@deriving sexp]

