open Support
open Support.Utils
open Types
open Lvar

let fresh = Utils.make_gensym ()

let uniquify_exp (e : exp) : exp =
  let rec aux (m: var VarMap.t) (e : exp) : exp =
    match e with
      | Int _
      | Read -> e
      | Negate e -> Negate (aux m e)
      | Add (e1, e2) -> 
        let e1' = aux m e1 in Add (e1', aux m e2)
      | Sub (e1, e2) -> 
        let e1' = aux m e1 in Sub (e1', aux m e2)
      | Var v -> 
        (match VarMap.find_opt v m with
          | Some x -> Var x
          | None -> e)
      | Let (v, e1, e2) ->
        let cond = aux m e1 in
          let name = fresh ~base:v ~sep: "." in
          let body = aux (VarMap.add v name m) e2 in
          Let (name, cond, body)
  in aux VarMap.empty e

let validate (e : exp) : unit =
  let rec aux (s : VarSet.t) (e : exp) : VarSet.t  =
    match e with
      | Int _
      | Var _
      | Read -> s
      | Negate e1 -> aux s e1
      | Add (e1, e2)
      | Sub (e1, e2) ->
          let s1 = aux s e1 in
            aux s1 e2
      | Let (v, e1, e2) ->
          if VarSet.mem v s then
            failwithf
              "uniquify: validate: variable %s bound more than once" v
          else
            let s1 = VarSet.add v s in
            let s2 = aux s1 e1 in
              aux s2 e2
  in
    let _ = aux VarSet.empty e in ()

let uniquify (Program e) =
  let ue = uniquify_exp e in
  let _  = validate ue in
    Program ue