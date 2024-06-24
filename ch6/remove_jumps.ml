open Support
open Utils
open Types
open X86_var_global

module M = LabelMap
module G = LabelDgraph

(*

Algorithm:

- Convert the (label, block) list into a label graph
  (a directed graph, using the `LabelDgraph` module).
- Find all blocks which have only a single out edge.
- If the target of these out edges has only a single in edge,
    merge the two blocks.
- Repeat until there are no more mergeable blocks.

*)

(* Get a list of all the jump labels in a block.
   NOTE: This is not the same as the similarly-named function
   from the `Ctup` module. *)
let get_jump_labels (Block (_, instrs) : 'a block) : label list =
  let rec collect_jmp_labels (instrs : instr list) (lbls : label list) 
            : label list =
    match instrs with
      | [] -> lbls
      | h :: t -> 
          let lbls' = match h with
            | Jmp lbl
            | JmpIf (_, lbl) -> lbl :: lbls
            | _ -> lbls
          in collect_jmp_labels t lbls'
  in collect_jmp_labels instrs []

let make_graph (lbs : (label * 'a block) list) : LabelDgraph.t =
  let make_jump_labels_map 
          (lbs : (label * 'a block) list) : (label list) M.t = 
    List.fold_left 
      (fun m (Label s as lbl, block) -> 
        (* filters out the conclusion block from calling get_jmp_labels *)
        if s = "conclusion" then m
        else M.add lbl (get_jump_labels block) m) 
      M.empty lbs 
  in
  let list_graph_edges 
          (lbl_map : (label list) M.t) : (label * label) list =
    M.fold 
      (fun (from : label) (tos : label list) 
            (lbls : (label * label) list) : (label * label) list ->
        (List.concat_map 
          (fun (Label s as jmp_to) -> 
            (* filters out target jump labels to conclusion *)
            if s = "conclusion" then [] else [(from, jmp_to)])
          tos
        ) @ lbls) 
      lbl_map []
  in 
    let jmp_lbls_map = make_jump_labels_map lbs in
    let graph_edges_lst = list_graph_edges jmp_lbls_map in
      G.of_list graph_edges_lst

(* Get a pair of mergeable labels from the graph if there are any. *)
let get_mergeable_labels (g : G.t) : (label * label) option =
  let is_vertex_mergeable (from : label) : bool =
    (* Gets Some (only elem in a list) or None if there's no or > 1 elems *)
    let get_only_elem (lst : label list) : label option =
      match lst with 
        | [only] -> Some (only)
        | _ -> None
    in
    (* Checks that from has exactly one out neighbor *)
    let from_outs = G.neighbors_out g from in
    let from_only_elem = get_only_elem from_outs in
    if from_only_elem = None
      then false
      (* If so, check that that out neighbor has exactly one in neighbor *)
      else 
        let to_ins = G.neighbors_in g (Option.get from_only_elem) in
        if (get_only_elem to_ins) = None 
          then false
          else true 
  in
  let (from_opt : label option) = 
    List.find_opt is_vertex_mergeable (G.vertices g)
  in
    if from_opt = None 
      then None
      else 
        let (from : label) = Option.get from_opt in
          Some (from, List.hd (G.neighbors_out g from))

(* Merge two blocks. *)
let merge_blocks (Block (_, instrs1) : 'a block) (Block (_, instrs2) : 'a block) : 'a block =
  let new_instrs = (butlast instrs1) @ instrs2 in
    Block (Binfo1, new_instrs)

(* Merge two blocks A and B if block A only jumps to block B
   and block B is only jumped to from block A.
   The merged block will have the label of the original block A. *)
let process_blocks (lbs : (label * 'a block) list) : ((label * 'a block) list) =
  if List.length lbs < 2 then
    lbs (* no blocks to merge! *)
  else
    let map = M.of_list lbs in
    let graph = make_graph lbs in
      let rec merge_until_cant m g = 
        let mergeable = get_mergeable_labels g in
        if mergeable = None 
          then M.bindings m
        else 
          let (lbl1, lbl2) = Option.get mergeable in
          let m' = 
            M.add lbl1 (merge_blocks (M.find lbl1 m) (M.find lbl2 m)) m in
          let m'' = M.remove lbl2 m' in
          let g' = G.merge_vertices g lbl1 lbl2 in
            merge_until_cant m'' g'
      in merge_until_cant map graph

let remove_jumps (prog : ('a, binfo1) program) : ('a, binfo1) program =
  let (X86Program (info, lbs)) = prog in
    X86Program (info, process_blocks lbs)
