open Support.Utils
open Types
open Cif

module L = Lif_mon

(* Variable to hold gensym function. *)
let fresh = ref (make_gensym ())

(* Variable to hold labelled blocks. *)
let basic_blocks = ref LabelMap.empty

let convert_atom (a : L.atm) : atm =
  match a with
    | L.Bool b -> Bool b
    | L.Int i -> Int i
    | L.Var v -> Var v

let convert_exp (e : L.exp) : exp =
  match e with
    | L.Atm a -> Atm (convert_atom a)
    | Prim (op, es) -> Prim (op, List.map convert_atom es)
    | _ -> failwith "convert_exp: received unexpected form"

(* Convert expressions which are the binding expression of a `let` expression
 * (i.e. in `(let (var <exp1>) <exp2>)` the binding expression is `<exp1>`).
 * These are ultimately converted to assignments.
 * The `tail` is the continuation (what to do after the binding). *)
let rec explicate_assign (e : L.exp) (v : var) (tl : tail) : tail =
  match e with
    | L.If (e1, e2, e3)->
      let bl = Goto (create_block tl) in
      explicate_pred e1 (explicate_assign e2 v bl) (explicate_assign e3 v bl)
    | L.Let (v', e1, e2) -> explicate_assign e1 v' (explicate_assign e2 v tl)
    | _ -> Seq (Assign (v, convert_exp e), tl)

(* Convert `if` expressions.
 * `e` is the condition part of the expression (evaluating to boolean).
 * The `then_tl` and `else_tl` are the two possible continuations. *)
and explicate_pred (e : L.exp) (then_tl : tail) (else_tl : tail) : tail =
  match e with
    | L.Prim (#cmp_op as c_op, [a; b]) ->
      let then_bl = create_block then_tl in
      let else_bl = create_block else_tl in 
      IfStmt {
        op = c_op;
        arg1 = convert_atom a;
        arg2 = convert_atom b;
        jump_then = then_bl;
        jump_else = else_bl;
      }
    | L.Atm (L.Bool b) -> if b then then_tl else else_tl
    | L.Prim(`Not, [L.Bool b]) -> if b then else_tl else then_tl
    | L.Prim(`Not, [L.Var v]) ->
      let then_bl = create_block then_tl in
      let else_bl = create_block else_tl in
      IfStmt {
        op = `Eq;
        arg1 = Var v;
        arg2 = Bool false;
        jump_then = then_bl;
        jump_else = else_bl;
      }
    | L.Atm (L.Var v) -> 
      let then_bl = create_block then_tl in
      let else_bl = create_block else_tl in
      IfStmt {
        op = `Eq;
        arg1 = Var v;
        arg2 = Bool true;
        jump_then = then_bl;
        jump_else = else_bl;
      }
    | L.Let (v, e1, e2) ->
      explicate_assign e1 v (explicate_pred e2 then_tl else_tl)
    | L.If (e1, e2, e3) ->
      let then_bl = Goto (create_block then_tl) in
      let else_bl = Goto (create_block else_tl) in
      explicate_pred e1 (explicate_pred e2 then_bl else_bl) 
                        (explicate_pred e3 then_bl else_bl)
    | _ -> failwith "explicate_pred: unexpected forms"

(* Convert expressions in tail position.
 * This includes:
 * 1) any top-level expression
 * 2) any expression at the end of a larger expression
 *    that will be evaluated to give the result of the entire expression
 * Examples of (2):
 * - the body of a `let`
 * - the then/else clauses of an `if`
 *)
and explicate_tail (e : L.exp) : tail =
  match e with
    | L.Atm _
    | L.Prim _ -> Return (convert_exp e)
    | L.Let (v, e1, e2) -> explicate_assign e1 v (explicate_tail e2)
    | L.If (e1, e2, e3) -> explicate_pred e1 (explicate_tail e2) (explicate_tail e3)

(* Create a block from a tail.
 * Return a "goto" label to the block. *)
and create_block (tl : tail) : label =
  match tl with
    | Goto lbl -> lbl
    | Return _ | Seq _ | IfStmt _ ->
        let name = !fresh ~base:"block" ~sep:"_" in
        let lbl = Label name in
          begin
            basic_blocks := LabelMap.add lbl tl !basic_blocks;
            lbl
          end

let init_globals () =
  fresh := make_gensym ();
  basic_blocks := LabelMap.empty

let explicate_control (L.Program e) =
  let _ = init_globals () in
  let t = explicate_tail e in
  (* The info field is empty here;
   * it will be filled in by the type checker. *)
  let info = Info { locals_types = [] } in
  let lts = [(Label "start", t)] @ LabelMap.bindings !basic_blocks in
  let lts' = tsort_lts lts in
    CProgram (info, lts')
