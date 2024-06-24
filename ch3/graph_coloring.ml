open Sexplib.Std

open Support
open Functors
open Types
open Priority_queue

(* Use this to turn debugging code on or off. *)
let _debug_gc = ref false

module type GraphColor =
  sig
    type elt
    type graph
    type pqueue
    type 'a eltmap

    val color : graph -> int eltmap -> int eltmap
  end

module Make (Elt   : OrderedTypeS)
            (EMap  : MapS.S        with type key = Elt.t)
            (PQ    : PriorityQueue with type elt = Elt.t)
            (Graph : Ugraph.S      with type elt = Elt.t):
  GraphColor with type elt       = Elt.t
             and  type 'a eltmap = 'a EMap.t
             and  type pqueue    = PQ.t
             and  type graph     = Graph.t =
  struct
    type elt       = Elt.t
    type 'a eltmap = 'a EMap.t
    [@@deriving sexp]
    type graph     = Graph.t
    type pqueue    = PQ.t

    (* Where node information is stored. *)
    type node = {
      color      : int option;
      saturation : IntSet.t;
    }
    [@@deriving sexp]

    (* Map between graph elements and nodes.
     * This is what gets updated as the algorithm unfolds. *)
    type nodemap = node eltmap
    [@@deriving sexp]

    (* ------------------------------------------------------------ *)

    (* Debugging. *)

    let _print_nodemap msg (map : nodemap) : unit =
      Printf.printf "\n%s:\n%s\n\n%!"
        msg (Utils.pretty_print (sexp_of_nodemap map))

    let _string_of_elt (e : elt) : string =
      Elt.sexp_of_t e |> Sexplib.Sexp.to_string

    (* ------------------------------------------------------------ *)

    (* Colors an element's node in the nodemap with the given color. *)
    let color_node (e : elt) (c : int) (map : nodemap) = 
      let prev = 
        EMap.find_or_fail e map 
          ~err_msg:"color_node: elem not in map!"
      in 
        EMap.add e {color=Some c; saturation=prev.saturation} map 

    (* Saturates all the neighbors in the nodemap with a given color,
     * to be used coloring a node. Note that this doesn't do any coloring. 
     *)
    let saturate_neighbors (c : int) (neighbors : elt list) 
                                (map : nodemap) : nodemap =
      List.fold_left 
        (fun (map' : nodemap) (nb : elt) : nodemap -> 
          let prev = 
            EMap.find_or_fail nb map' 
              ~err_msg:"saturate_neighbors: neighbor not in map!"
          in
          EMap.add nb 
            {color=prev.color; saturation=IntSet.add c prev.saturation} 
            map')
        map neighbors

    (* Same as saturate_neighbors but also updates the priorities of 
     * all the neighbors in the given priority queue.
     *)
    let saturate_neighbors_with_priority (c : int) (neighbors : elt list)
                      (map : nodemap) (pq : PQ.t): (nodemap * pqueue) =
      List.fold_left 
        (fun ( (map' : nodemap), (pq' : pqueue) ) (nb : elt) -> 
          let prev = 
            EMap.find_or_fail nb map' 
              ~err_msg:"saturate_neighbors_with_priority: neighbor not in map!"
          in
          let new_saturation = IntSet.add c prev.saturation in
          let map'' = EMap.add nb 
            {color=prev.color; saturation=new_saturation} 
            map'
          and pq'' = PQ.update nb (IntSet.cardinal new_saturation) pq' 
            in (map'', pq'') )
        (map, pq) neighbors

    (* Return `true` if an element's node in a nodemap is uncolored. *)
    let is_uncolored (e : elt) (map : nodemap) : bool =
      let mapping = 
          EMap.find_or_fail e map 
            ~err_msg:"is_uncolored: element not in map!"
        in
        mapping.color = None

    (* Starting from an initial partial mapping
     * between graph elements and colors (the precolored map),
     * compute an initial nodemap.
     * Also compute the initial saturation sets for all nodes.
     * Note that if an element is in the precolored_map but not 
     * in the graph, it doesn't get added to the nodemap.
     *)
    let initial_nodemap (g : graph) (precolored_map : int eltmap) : nodemap =
      let bindings = List.map
        (fun (e : elt) -> (e, {color=None; saturation=IntSet.empty}))
        (Graph.vertices g)
      in EMap.fold 
        (fun (e : elt) (c : int) (map : nodemap) ->
          if not (EMap.mem e map) then map
          else
            let map' = color_node e c map
              in saturate_neighbors c (Graph.neighbors g e) map')
        precolored_map (EMap.of_list bindings)

    (* Initialize the priority queue with uncolored nodes only. *)
    let initial_priority_queue (map : nodemap) : pqueue =
      (* Priority queue elements are (elt, int) pairs,
       * where the int is the priority. *)
      let node_bindings = 
        List.filter (fun (_, n) -> n.color = None) (EMap.bindings map)
      in 
      let int_bindings = List.map
        (fun ((e : elt), (n : node)) -> (e, IntSet.cardinal n.saturation))
        node_bindings
      in 
        PQ.of_list int_bindings

    (* Pick the smallest non-negative integer not in the set. *)
    let pick_color (set : IntSet.t) : int =
      let rec find_lowest_outside_set i = 
        if not (IntSet.mem i set) 
          then i
          else find_lowest_outside_set (i + 1)
      in find_lowest_outside_set 0

    (* Add a color to:
     * a) an element's node
     * b) the element's neighbors' saturation maps
     * Also, every time a saturation map increases in size,
     * adjust the element's position in the priority queue.
     * This version is purely functional.
     *)
    let add_color (g : graph) (e : elt) (c : int)
        (map : nodemap) (pq : PQ.t) : nodemap * PQ.t =
      let map' = color_node e c map in
        saturate_neighbors_with_priority c (Graph.neighbors g e) map' pq 

    (* Generate the final int eltmap from the final nodemap. *)
    let make_final_color_map (map : nodemap) : int eltmap =
      EMap.map (fun (n : node) -> Option.get n.color) map

    let color (g : graph) (precolored_map : int eltmap) : int eltmap =
      (* Algorithm:
       * - find_or_fail the uncolored location with the highest priority
       * - remove it from the queue
       * - pick a color for it based on its neighbor colors
       *   (the saturation set)
       * - add the color to all the neighbors' saturation sets
       *   (updating their places in the priority queue)
       * - continue until the queue is empty
       *)
      let init_map = initial_nodemap g precolored_map in
      (* let _ = _print_nodemap "INIT" init_map in *)
      let init_pq  = initial_priority_queue init_map in
      let rec iter (map : node eltmap) (pq : PQ.t) : node eltmap =
        if PQ.is_empty pq then
          map  (* all colors assigned *)
        else
          let (e, pq') = PQ.remove_top pq in
          if not (is_uncolored e map) then
            failwith "color: colored nodes are not allowed in priority queue"
          else
            let node =
              EMap.find_or_fail e map
                ~err_msg:"color: element not in map!"
            in
            let color = pick_color node.saturation in
            let (map', pq'') = add_color g e color map pq' in
            (* let _ = _print_nodemap "NEXT" map' in *)
              iter map' pq''
      in
        make_final_color_map (iter init_map init_pq)
  end
