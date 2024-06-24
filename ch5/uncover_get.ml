open Types
open Lwhile_get
module L = Lwhile_shrink
module S = VarSet

let collect_set_vars (e : L.exp) : S.t =
  let rec add_to_set_vars (exp: L.exp) (s : S.t) =
    let add_all_exps (es : L.exp list) (s : S.t) = 
      List.fold_left (fun s e -> add_to_set_vars e s) s es 
    in
    match exp with
      | L.SetBang (v, e) -> 
          let s' = S.add v s in
          add_to_set_vars e s'
      | L.Void
      | L.Bool _
      | L.Int _
      | L.Var _ -> s
      | L.Prim (_, es) -> add_all_exps es s
      | L.Begin (es, e) ->
          let s' = add_all_exps es s in
          add_to_set_vars e s'
      | L.If (e1, e2, e3) -> add_all_exps [e1; e2; e3] s
      | L.While (e1, e2) -> add_all_exps [e1; e2] s
      | L.Let (_, e1, e2) -> add_all_exps [e1; e2] s
  in add_to_set_vars e S.empty  

let rec uncover_get_exp (s : S.t) (e : L.exp) : exp =
  match e with
    | L.Var v -> if (S.mem v s) then (GetBang v) else (Var v)
    | L.Void -> Void
    | L.Bool b -> Bool b
    | L.Int i -> Int i
    | L.Prim (cop, args) -> Prim (cop, List.map (uncover_get_exp s) args)
    | L.SetBang (v, e) -> SetBang (v, uncover_get_exp s e)
    | L.Begin (es, e) -> 
        Begin (List.map (uncover_get_exp s) es, uncover_get_exp s e)
    | L.If (e1, e2, e3) -> 
        If (uncover_get_exp s e1, uncover_get_exp s e2, uncover_get_exp s e3)
    | L.While (e1, e2) -> While (uncover_get_exp s e1, uncover_get_exp s e2)
    | L.Let (v, e1, e2) -> Let (v, uncover_get_exp s e1, uncover_get_exp s e2)

let uncover_get (prog : L.program) : program =
  let (L.Program e) = prog in
  let set_vars = collect_set_vars e in
    Program (uncover_get_exp set_vars e)
