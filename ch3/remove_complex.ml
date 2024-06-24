open Support
open Types
open Lvar_mon

module L = Lvar

let fresh = Utils.make_gensym ()
let gen_temp_name () = fresh ~base:"$tmp" ~sep:"."


(* Convert an expression which needs to become atomic.
 * Return the atom as well as a list of
 * names bound to expressions. *)
let rec rco_atom (e : L.exp) : (atm * ((var * exp) list)) = 
  match e with 
    | L.Int i -> (Int i, [])
    | L.Var v -> (Var v, [])
    | L.Let (v, e1, e2) -> 
      let e1_bind = (v, rco_exp e1) in
      let (e2', e2_bindings) = rco_atom e2 in
        (e2', e2_bindings @ [e1_bind])
    | L.Read -> 
      let temp = gen_temp_name() in
        (Var temp, [ (temp, rco_exp e) ])
    | L.Negate a -> 
      let atm, bindings = rco_atom a in
      let temp = gen_temp_name() in
        (Var temp, (temp, Negate atm) :: bindings )
    | L.Add (a, b) ->
      let atm1, bindings1 = rco_atom a in 
      let atm2, bindings2 = rco_atom b in
      let temp = gen_temp_name() in
        (Var temp, (temp, Add (atm1, atm2)) :: bindings2 @ bindings1)
    | L.Sub (a, b) ->
      let atm1, bindings1 = rco_atom a in 
      let atm2, bindings2 = rco_atom b in
      let temp = gen_temp_name() in
        (Var temp, (temp, Sub (atm1, atm2)) :: bindings2 @ bindings1)


and rco_exp (e : L.exp) : exp =
  let nest_lets (bindings : (var * exp) list) (base : exp) : exp = 
    List.fold_left (fun base -> fun (v, e) -> Let (v, e, base)) base bindings
  in

  match e with 
    | L.Int i -> Atm (Int i)
    | L.Var v -> Atm (Var v)
    | L.Read -> Read
    | L.Let (v, e1, e2) -> 
      let e1' = rco_exp e1 in
      let e2' = rco_exp e2 in
        Let (v, e1', e2')
    | L.Negate a ->
      let atm1, bindings1 = rco_atom a in 
          nest_lets bindings1 (Negate atm1)
    | L.Add (a, b) ->
      let atm1, bindings1 = rco_atom a in 
      let atm2, bindings2 = rco_atom b in
        nest_lets (bindings2 @ bindings1) (Add (atm1, atm2))
    | L.Sub (a, b) ->
      let atm1, bindings1 = rco_atom a in 
      let atm2, bindings2 = rco_atom b in
        nest_lets (bindings2 @ bindings1) (Sub (atm1, atm2))


let remove_complex_operands (prog : L.program) : program =
  let (L.Program exp) = prog in
    Program (rco_exp exp)