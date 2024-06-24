open Types
open Cloop


(* Return all the (label, tail) pairs that are reachable
 * from the "start" label. *)
let process_blocks (lts : (label * tail) list) : (label * tail) list =
  let map = LabelMap.of_list lts in
  let (lbl, tl) = List.hd lts in 
  let rec iter lbl_lst res (incl: label list) =
    match lbl_lst with
      | [] -> res
      | h :: t -> 
        (* added incl because it gets stuck in the loop *)
        if List.exists (fun x -> x = h) incl then
          iter t res incl
        else
          let tl = LabelMap.find h map in
          iter (t @ (get_jump_labels tl)) (LabelMap.add h tl res) (h :: incl) 
  in 
  let result = iter (get_jump_labels tl) 
                    (LabelMap.add lbl tl (LabelMap.empty)) [] in
  LabelMap.bindings result 

let remove_unused_blocks (prog : program) : program =
  let (CProgram (info, lts)) = prog in
    CProgram (info, process_blocks lts)
