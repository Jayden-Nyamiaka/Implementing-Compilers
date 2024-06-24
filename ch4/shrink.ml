open Lif_shrink
module L = Lif

let rec shrink_exp (e : L.exp) : exp =
  match e with
    | L.Int i -> Int i
    | L.Bool b -> Bool b
    | L.Var x -> Var x
    | L.Prim (op, exp_lst) ->
      Prim (op, List.map shrink_exp exp_lst)
    | L.And (a, b) -> If (shrink_exp a, shrink_exp b, Bool (false))
    | L.Or (a, b) -> If (shrink_exp a, Bool (true), shrink_exp b)
    | L.If (e1, e2, e3) -> If (shrink_exp e1, shrink_exp e2, shrink_exp e3)
    | L.Let (v, e1, e2) -> Let (v, shrink_exp e1, shrink_exp e2)


let shrink (prog : L.program) : program =
  let (L.Program e) = prog in
    Program (shrink_exp e)
