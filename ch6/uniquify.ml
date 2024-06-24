open Support
open Support.Utils
open Types
open Ltup_shrink

let fresh = Utils.make_gensym ()

let uniquify_exp (e : exp) : exp =
  let rec aux (m: var VarMap.t) (e : exp) : exp =
    match e with
      | Void
      | Int _
      | Bool _ -> e
      | Var v -> 
        (match VarMap.find_opt v m with
          | Some x -> Var x
          | None -> e)
      | Let (v, e1, e2) ->
        let cond = aux m e1 in
        let name = fresh ~base:v ~sep: "." in
        let body = aux (VarMap.add v name m) e2 in
          Let (name, cond, body)
      | Prim (op, es) -> Prim (op, List.map (aux m) es)
      | If (e1, e2, e3) ->
          let e1' = aux m e1 in
          let e2' = aux m e2 in
          let e3' = aux m e3 in
          If (e1', e2', e3')
      | SetBang (v, e') -> 
        if not (VarMap.mem v m) then
          failwithf "uniquify: uniquify_exp: unbound variable %s in set! form" v
        else
          SetBang (VarMap.find v m, aux m e')
      | While (e1, e2) -> While (aux m e1, aux m e2)
      | Begin (es, e') -> Begin (List.map (aux m) es, aux m e')
      | Vec (es, ty) -> Vec (List.map (aux m) es, ty)
      | VecLen e' -> VecLen (aux m e')
      | VecRef (e1, i) -> VecRef (aux m e1, i)
      | VecSet (e1, i, e2) -> VecSet (aux m e1, i, aux m e2)
  in aux VarMap.empty e

let validate (e : exp) : unit =
  let rec aux (s : VarSet.t) (e : exp) : VarSet.t  =
    match e with
      | Void
      | Bool _
      | Int _
      | Var _ -> s
      | Prim (_, es) ->
          List.fold_left aux s es
      | SetBang (v, e) ->
          if not (VarSet.mem v s) then
            failwithf
              "uniquify: validate: unbound variable %s in set! form" v
          else
            aux s e
      | Begin (es, e) ->
          List.fold_left aux s (es @ [e])
      | If (e1, e2, e3) ->
          List.fold_left aux s [e1; e2; e3]
      | While (e1, e2) ->
          List.fold_left aux s [e1; e2]
      | Let (v, e1, e2) ->
          if VarSet.mem v s then
            failwithf
              "uniquify: validate: variable %s bound more than once" v
          else
            let s1 = VarSet.add v s in
            let s2 = aux s1 e1 in
              aux s2 e2
      | Vec (es, _) ->
          List.fold_left aux s es
      | VecLen e
      | VecRef (e, _) ->
          aux s e
      | VecSet (e1, _, e2) ->
          List.fold_left aux s [e1; e2]
  in
    let _ = aux VarSet.empty e in ()

let uniquify (prog : program) : program =
  let (Program e) = prog in
  let ue = uniquify_exp e in
  let _  = validate ue in
    Program ue

