open Support.Utils
open Types
open Cloop

module L = Lwhile_mon

(* Variable to hold gensym function. *)
let fresh = ref (make_gensym ())

(* Variable to hold labelled blocks. *)
let basic_blocks = ref LabelMap.empty

let convert_atom (a : L.atm) : atm =
  match a with
    | L.Bool b -> Bool b
    | L.Int i -> Int i
    | L.Var v -> Var v
    | L.Void -> Void

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
    | L.Begin (es, e1) -> 
      List.fold_right explicate_effect es (explicate_assign e1 v tl) 
    | L.While (e1, e2) -> 
      let tl' = explicate_effect e tl in
      explicate_pred e1 (explicate_effect e2 tl') 
                        (explicate_assign (L.Atm Void) v tl)
    | L.SetBang (v', e') -> explicate_assign (Atm Void) v (explicate_assign e' v' tl)
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
    | L.Begin (es, e) -> 
      List.fold_right explicate_effect es (explicate_pred e then_tl else_tl)
    | _ -> failwith "explicate_pred: unexpected forms"

(* Convert expressions in effect position.
 * Effect position includes:
 * - the expressions before the last expression in a `begin` expression
 * - the body expressions in a `while` loop
 * These are expressions that are only evaluated for their side effects.
 * Pure expressions in effect position are discarded,
 * since they can't have any effect. *)
and explicate_effect (e : L.exp) (tl : tail) : tail =
  match e with
    | While (e1, e2) -> 
      let lbl = Label (!fresh ~base:"loop" ~sep:"_") in
      let body = explicate_effect e2 (Goto lbl) in
      let cnd = explicate_pred e1 body tl in
      begin
        basic_blocks := LabelMap.add lbl cnd !basic_blocks;
        Goto lbl
      end
    | Prim (`Read as op, es)
    | Prim (`Print as op, es) -> Seq (PrimS (op, List.map convert_atom es), tl)
    | If (e1, e2, e3) -> 
      let tl_block = Goto (create_block tl) in
      explicate_pred e1 (explicate_effect e2 tl_block) (explicate_effect e3 tl_block)
    | SetBang (v, e1) -> explicate_assign e1 v tl
    | Begin (es, e) -> 
      List.fold_right explicate_effect (es @ [e]) tl
    | Let (v, e1, e2) -> explicate_assign e1 v (explicate_effect e2 tl)
    | _ -> tl

(* Convert expressions in tail position.
 * This includes:
 * 1) any top-level expression
 * 2) any expression at the end of a larger expression
 *    that will be evaluated to give the result of the entire expression
 * Examples of (2):
 * - the body of a `let`
 * - the then/else clauses of an `if`
 * - the last expression of a `begin`
 *)
and explicate_tail (e : L.exp) : tail =
  match e with
    | L.Atm _
    | L.Prim _ -> Return (convert_exp e)
    | L.Let (v, e1, e2) ->
      let tl = explicate_tail e2 in
      explicate_assign e1 v tl
    | L.If (e1, e2, e3) -> explicate_pred e1 (explicate_tail e2) (explicate_tail e3)
    | L.While _ -> explicate_effect e (Return (Atm Void))
    | L.Begin (es, e) -> 
      List.fold_right explicate_effect es (explicate_tail e)
    | L.SetBang (v, e') -> explicate_assign e' v (Return (Atm Void))

(* Create a block from a tail.
 * Return a "goto" label to the block. *)
and create_block (tl : tail) : label =
  match tl with
    | Goto lbl -> lbl
    | Return _
    | Seq _
    | IfStmt _ ->
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
    CProgram (info, lts)
