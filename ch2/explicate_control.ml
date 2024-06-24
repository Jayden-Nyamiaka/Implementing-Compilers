open Types
open Cvar

module L = Lvar_mon

let convert_atom (a : L.atm) : atm =
  match a with
    | Int v -> Int v
    | Var v -> Var v

let convert_exp (e : L.exp) : exp =
  match e with
    | Atm v -> Atm (convert_atom v)
    | Read -> Read
    | Negate v -> Negate (convert_atom v)
    | Add (e1, e2) -> Add (convert_atom e1, convert_atom e2)
    | Sub (e1, e2) -> Sub (convert_atom e1, convert_atom e2)
    | _ -> failwith "Convert_exp received an unhandled case"

(* Convert expressions on the right-hand side of a `let` binding.
 * These are ultimately converted to assignments.
 * The `tail` is the continuation (what to do after the binding). *)
let rec explicate_assign (e : L.exp) (v : var) (tl : tail) : tail =
  match e with
    | Let (v', e1, e2) -> explicate_assign e1 v' (explicate_assign e2 v tl)
    | _ -> Seq (Assign (v, convert_exp e), tl)

(* Convert expressions in tail position.
 * This includes:
 * 1) any top-level expression
 * 2) any expression at the end of a larger expression
 *    that will be evaluated to give the result of the entire expression
 * Example of (2): the body of a `let`. *)
let rec explicate_tail (e : L.exp) : tail =
  match e with
    | Atm _ 
    | Negate _ 
    | Add _
    | Sub _ -> Return (convert_exp e)
    | Read -> Return Read
    | Let (v, e1, e2) -> explicate_assign e1 v (explicate_tail e2)


let explicate_control (prog : L.program) : program =
  let (L.Program e) = prog in
  let t = explicate_tail e in
  let p = CProgram (Info { locals_types = [] }, [(Label "start", t)]) in
    (* Add type information to the program for later use. *)
    add_type_info p
