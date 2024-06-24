open Support
open Types
open Lalloc
module L = Ltup_shrink

let fresh = Utils.make_gensym ()
let new_var () = fresh ~base:"$ea" ~sep:"."
let new_void_var () = fresh ~base:"_" ~sep:"."


let rec expose_allocation_exp (e : L.exp) : exp =
  (* let function to compute nbytes *)
  let is_atom (e : exp) : bool = 
    match e with
      | Void 
      | Bool _ 
      | Int _ 
      | Var _ -> true
      | Prim (_, _)
      | SetBang (_, _)
      | Begin (_, _)
      | If (_, _, _)
      | While (_, _)
      | Let (_, _, _)
      | Collect _ 
      | Allocate (_, _)
      | GlobalVal _
      | VecLen _
      | VecRef (_, _)
      | VecSet (_, _, _) -> false
  in
  let transform_vec_exp (es : exp list) (typ : ty) : exp =
    (* Finishes transformation with conditional the garbage collection,  
     * vector allocation, and vector set forms 
     * Note this is called in transform_params *)
    let transform_body (len : int) (vals : exp list) : exp = 
      let compute_nbytes_needed (len : int) : int =
        8 * (len + 1) (* 8 byte vector tag + 8 bytes per slot *)
      in
      let nbytes = compute_nbytes_needed len in
      let vec = new_var () in
      let vector_set_exp =
        let rec build_vector_sets vals idx =
          match vals with 
            | [] -> Var vec
            | vl :: t -> 
              Let (new_void_var (), VecSet (Var vec, idx, vl), 
                build_vector_sets t (idx + 1))
        in build_vector_sets vals 0
      in
        Let 
          (new_void_var (), 
          (If (Prim (`Lt, 
            [Prim (`Add, [GlobalVal "free_ptr"; Int nbytes]);
            GlobalVal "fromspace_end"]),
            Void, Collect nbytes)),
          Let (vec, Allocate (len, typ), vector_set_exp))
    in
    (* Iterates over all the function parameters, 
     * constructing all necessary Let (x, e) for all non_atomic params e,
     * counting the length of the arguments,
     * and building the map of atomized exps for the vector_set forms 
     * Note: function calls transform_body at end to finish transformation *)
    let rec transform_params (es : exp list) (count : int) 
          (atomized_es : exp list) : exp =
      match es with
        | [] -> transform_body count (List.rev atomized_es)
        | e :: t -> 
          if is_atom e then
            transform_params t (count + 1) (e :: atomized_es)
          else 
            let name = new_var () in
            Let (name, e, 
              transform_params t (count + 1) ( (Var name) :: atomized_es))
    in transform_params es 0 []
  in 
  match e with 
    | L.Void -> Void
    | L.Bool b -> Bool b
    | L.Int i -> Int i
    | L.Var v -> Var v
    | L.Prim (op, es) -> Prim (op, List.map expose_allocation_exp es)
    | L.SetBang (v, e) -> SetBang (v, expose_allocation_exp e)
    | L.Begin (es, e) -> 
      let es' = List.map expose_allocation_exp es in
      let e' = expose_allocation_exp e in
        Begin (es', e')
    | L.If (e1, e2, e3) -> 
      let e1' = expose_allocation_exp e1 in
      let e2' = expose_allocation_exp e2 in
      let e3' = expose_allocation_exp e3 in
        If (e1', e2', e3')
    | L.While (e1, e2) -> 
      let e1' = expose_allocation_exp e1 in
      let e2' = expose_allocation_exp e2 in
        While (e1', e2')
    | L.Let (v, e1, e2) -> 
      let e1' = expose_allocation_exp e1 in
      let e2' = expose_allocation_exp e2 in
        Let (v, e1', e2')
    | L.Vec (es, ty) -> 
      transform_vec_exp (List.map expose_allocation_exp es) ty
    | L.VecLen e -> VecLen (expose_allocation_exp e)
    | L.VecRef (e, i) -> VecRef (expose_allocation_exp e, i)
    | L.VecSet (e1, i, e2) -> 
      let e1' = expose_allocation_exp e1 in
      let e2' = expose_allocation_exp e2 in
        VecSet (e1', i, e2')

let expose_allocation (prog : L.program) : program =
  let (L.Program e) = prog in
    Program (expose_allocation_exp e)
