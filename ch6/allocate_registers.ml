open Support
open Types
open Utils
open X86_var_global

module PQ = Priority_queue.Simple (OrderedLoc)

module Color =
  Graph_coloring.Make (OrderedLoc) (LocMap) (PQ) (LocUgraph)

(* Registers that are relevant to register allocation.
 * NOTE: We leave out reserved registers: 
 *   rax (return value)
 *   rsp (stack pointer)
 *   rbp (base pointer)
 *   r11 (temporary register for vector operations)
 *   r15 (root stack pointer for garbage collection)
 *   NOTE: r15 should point to the end of the root stack.
 *)
let registers_used =
  [Rcx; Rdx; Rsi; Rdi; R8; R9; R10;  (* caller-saved *)
   Rbx; R12; R13; R14]               (* callee-saved *)

(* We use references for these parameters so they can be
 * overridden by command-line arguments. *)
let last_register_color = ref 0
let register_color_list : (location * int) list ref = ref []

(* Counters for spilled stack locations. *)
let next_stack_index = ref 0
let next_root_stack_index = ref 0

let register_list_ok regs =
  List.for_all (fun r -> List.mem r registers_used) regs

let set_register_color_list regs =
  if not (register_list_ok regs) then
    failwith "set_register_color_list: invalid register list"
  else
    let nums        = range 0 (List.length regs) in
    let reg_colors  = List.combine regs nums in
    let assignments = [(Rflags, -6); (Rsp, -2); (Rax, -1)] @ reg_colors in
    let rc_list     =
      List.map (fun (r, i) -> (RegL r, i)) assignments
    in
      begin
        register_color_list := rc_list;
        last_register_color := List.length regs - 1
      end

(* Default color assignments to registers. *)
let _ = set_register_color_list registers_used

let register_color_map () : int LocMap.t =
  LocMap.of_list !register_color_list

let color_register_map () : location IntMap.t =
  List.fold_left
    (fun m (l, i) -> IntMap.add i l m)
    IntMap.empty
    !register_color_list

(* Hash table mapping ints to locations. *)
let spilled_location_dict : (int, location) Hashtbl.t = Hashtbl.create 20

(* Get the location corresponding to a color (int).
 * Usually this will be a register, but if there aren't
 * enough registers, it will be a stack location.
 * If the `vector_typed` argument is `true`, 
 * choose a root stack location when spilling;
 * otherwise choose the regular stack.
 * When spilling, choose the next available stack location
 * in whichever stack is being spilled to.
 * Added spilled locations to `spilled_location_dict`,
 * unless re-using a previously-spilled location.
 *)
let location_of_color (i : int) (vector_typed : bool) : location =
  match IntMap.find_opt i (color_register_map ()) with
    | None -> (
      match vector_typed, Hashtbl.find_opt spilled_location_dict i with
        | _, Some loc -> loc
        | true, None -> 
          let new_loc = StackL (R15, -8 * !next_root_stack_index) in
          next_root_stack_index := !next_root_stack_index + 1; 
          Hashtbl.add spilled_location_dict i new_loc;
          new_loc 
        | false, None ->
          let new_loc = StackL (Rbp, -8 * !next_stack_index) in
          next_stack_index := !next_stack_index + 1;
          Hashtbl.add spilled_location_dict i new_loc;
          new_loc  
      )
    | Some loc -> loc

(* ----------------------------------------------------------------- *) 

(* Extract just the variable mappings from a graph coloring,
 * and map them to their (register and stack) locations. *)
let varmap_of_colormap
      (vvs : VarSet.t) (color_map : int LocMap.t) : location VarMap.t =
  let rec helper (color_map : (location * int) list) (location : location VarMap.t) = 
    match color_map with
      | (VarL loc, i) :: t -> 
        helper t (VarMap.add loc (location_of_color i (VarSet.mem loc vvs)) location)
      | _ :: t -> helper t location
      | _ -> location
  in helper (LocMap.bindings color_map) (VarMap.empty)

(* Determine the variable -> location mapping based on the
 * interference graph. *)
let get_variable_location_map
      (g : LocUgraph.t) (vvs : VarSet.t) : location VarMap.t =
  (* Reset the spill counters and location dictionary. *)
  next_stack_index := 1;       (* index 1 --> -8(%rbp) *)
  next_root_stack_index := 1;  (* index 1 --> -8(%r15) *)
  Hashtbl.clear spilled_location_dict;
  (* Perform the graph coloring, and convert to var -> loc map. *)
  varmap_of_colormap vvs (Color.color g (register_color_map ()))

(* Get the location of var *)
let get_var_loc (v : var) (map : location VarMap.t) =
  match VarMap.find_opt v map with
    | Some (RegL i) -> Reg i
    | Some (StackL (r, i)) -> Deref (r, i)
    | Some (VarL _) -> failwith "get_var_loc: unexpected error; var mapped to var"
    | None -> failwith "get_var_loc: unexpected error; var mapping not found"

(* Convert all the instructions with arguments. *)
let convert_instr (map : location VarMap.t) (ins : instr) : instr =
  let check_for_var (a : arg) =
    match a with
      | Var v -> get_var_loc v map
      | _ -> a in
  match ins with
    | Addq (a, b) -> Addq (check_for_var a, check_for_var b)
    | Subq (a, b) -> Subq (check_for_var a, check_for_var b)
    | Negq (a) -> Negq (check_for_var a)
    | Xorq (a, b) -> Xorq (check_for_var a, check_for_var b)
    | Cmpq (a, b) -> Cmpq (check_for_var a, check_for_var b)
    | Set (c, a) -> Set (c, check_for_var a)
    | Movq (a, b) -> Movq (check_for_var a, check_for_var b)
    | Movzbq (a, b) -> Movzbq (check_for_var a, check_for_var b)
    | Pushq a ->  Pushq (check_for_var a)
    | Popq a -> Popq (check_for_var a)
    | Andq (a, b) -> Andq (check_for_var a, check_for_var b)
    | Sarq (a, b) -> Sarq (check_for_var a, check_for_var b)
    | _ -> ins

(* Convert a block.  Block info is empty, so it's just passed through. *)
let convert_block (map : location VarMap.t) (bl : 'a block) : 'a block =
  let (Block (bi, ins)) = bl in
    Block (bi, List.map (convert_instr map) ins)

(* Get the number of spilled locations.
 * The first returned int is the number of variables
 * spilled onto the regular stack.
 * The second is the number of vector-valued variables
 * spilled onto the root stack.
 *)
let get_num_spilled () : int * int =
  (!next_stack_index - 1, !next_root_stack_index - 1)

(* Compute the set of callee-save registers used. *)
let get_used_callee (map : location VarMap.t) : RegSet.t =
  let bindings = VarMap.bindings map in 
  let (_, locs) = List.split bindings in 
  RegSet.filter (fun x -> List.mem (RegL x) locs) callee_save_regs

(* Collect the vector-typed vars. *)
let vector_vars (lts : (var * ty) list) : VarSet.t =
  let is_vector = function
    | Vector _ -> true
    | _ -> false
  in
    lts
     |> List.filter_map (fun (v, t) -> if is_vector t then Some v else None)
     |> VarSet.of_list

(* Validation function: checks that there are no remaining
 * variable references in the code. *)
let check_no_variables (prog : (info3, binfo1) program) : unit =
  let is_var = function
    | Var _ -> true
    | _ -> false
  in
  let has_var = function
    | Addq   (a1, a2)
    | Subq   (a1, a2)
    | Xorq   (a1, a2)
    | Cmpq   (a1, a2)
    | Movq   (a1, a2)
    | Andq   (a1, a2)
    | Sarq   (a1, a2)
    | Movzbq (a1, a2) -> is_var a1 || is_var a2
    | Negq   a
    | Set    (_, a)
    | Pushq  a
    | Popq   a -> is_var a
    | _ -> false
  in
  let X86Program (_, lbs) = prog in
  let (_, bs) = List.split lbs in
  let get_instrs (Block (_, b)) = b in
  let (ins : instr list) = bs |> List.map get_instrs |> List.concat in
  if List.exists has_var ins then
    failwith 
      ("allocate_registers: check_no_variables: " ^
       "variables still present in code after pass")
  else ()

(* Allocate registers to variables in the code. *)
let allocate_registers (prog : (info2, binfo1) program)
      : (info3, binfo1) program =
  let (X86Program (Info2 info, lbs)) = prog in
  let vvs = vector_vars info.locals_types in
  let (map : location VarMap.t) =
    get_variable_location_map info.conflicts vvs
  in
  let (num_spilled, num_spilled_root) = get_num_spilled () in
  let info' = Info3 
    { 
      locals_types= info.locals_types;
      num_spilled;
      num_spilled_root;
      used_callee = get_used_callee map
    }
  in
  (* Rewrite the code using the variable->register map. *)
  let lbs' =
    List.map 
      (fun (label, block) -> (label, convert_block map block))
      lbs 
  in
  let prog' = X86Program (info', lbs') in
  let () = check_no_variables prog' in
    prog'
