open Support
open Types
open Lwhile_mon

module L = Lwhile_get

let fresh = Utils.make_gensym ()
let gen_temp_name () = fresh ~base:"$tmp" ~sep:"."


(* Convert an expression which needs to become atomic.
 * Return the atomic expression as well as a list of
 * names bound to complex operands. *)
let rec rco_atom (e : L.exp) : ((var * exp) list) * atm =
  match e with 
    | L.Bool b -> [], Bool b
    | L.Int i -> [], Int i
    | L.Var v -> [], Var v
    | L.Void -> [], Void
    | L.Let (v, e1, e2) -> 
      let e1_bind = (v, rco_exp e1) in
      let e2_bindings, e2' = rco_atom e2 in
        e2_bindings @ [e1_bind], e2'
    | L.Prim (op, es) ->
      let atm, bindings = prim_helper op es [] [] in
      let temp = gen_temp_name () in
        (temp, atm) :: bindings, Var temp
    | L.If _ ->
      let e' = rco_exp e in 
      let temp = gen_temp_name () in
        [temp, e'], Var temp
    | L.SetBang _
    | L.While _ ->
      let dummy = "$_" in
      let e' = rco_exp e in
        [dummy, e'], Void
    | L.Begin (es, e) ->
      let es' = List.map rco_exp es in
      let e' = rco_exp e in
      let temp = gen_temp_name () in
        [temp, Begin (es', e')], Var temp
    | L.GetBang v ->
      let temp = gen_temp_name () in
        [temp, Atm (Var v)], Var temp 

and prim_helper (op: core_op) es bindings atms =
  match es with
    | h :: t ->
      let bs, atm = rco_atom h in
      prim_helper op t (bs @ bindings) (atm :: atms)
    | _ -> Prim (op, List.rev atms), bindings

and rco_exp (e : L.exp) : exp =
  let nest_lets (bindings : (var * exp) list) (base : exp) : exp = 
    List.fold_left (fun base -> fun (v, e) -> Let (v, e, base)) base bindings
  in
  match e with 
    | L.Bool b -> Atm (Bool b)
    | L.Int i -> Atm (Int i)
    | L.Var v -> Atm (Var v)
    | L.Void -> Atm (Void)
    | L.Let (v, e1, e2) -> 
      let e1' = rco_exp e1 in
      let e2' = rco_exp e2 in
        Let (v, e1', e2')
    | L.Prim (op, es) -> 
      let atm, bindings = prim_helper op es [] [] in
      nest_lets bindings atm
    | L.If (e1, e2, e3) ->
      let e1' = rco_exp e1 in 
      let e2' = rco_exp e2 in
      let e3' = rco_exp e3 in
        If (e1', e2', e3')
    | L.While (e1, e2) ->
      let e1' = rco_exp e1 in
      let e2' = rco_exp e2 in
        While (e1', e2')
    | L.SetBang (v, e1) ->
      let e1' = rco_exp e1 in
        SetBang (v, e1')
    | L.Begin (es, e) ->
      let es' = List.map rco_exp es in
      let e' = rco_exp e in
        Begin (es', e')
    | L.GetBang v -> Atm (Var v)

let remove_complex_operands (prog : L.program) : program =
  let (L.Program exp) = prog in
    Program (rco_exp exp)
