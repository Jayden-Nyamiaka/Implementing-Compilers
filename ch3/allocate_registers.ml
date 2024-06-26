open Support
open Types
open Utils
open X86_var

module PQ = Priority_queue.Simple (OrderedLoc)

module Color =
  Graph_coloring.Make (OrderedLoc) (LocMap) (PQ) (LocUgraph)

(* Registers that are relevant to register allocation.
 * NOTE: We leave out reserved registers: 
 *   rax (return value)
 *   rsp (stack pointer)
 *   rbp (base pointer)
 *   r11 (used in later compilers)
 *   r15 (used in later compilers)
 *)
let registers_used : reg list =
  [Rcx; Rdx; Rsi; Rdi; R8; R9; R10;  (* caller-saved *)
   Rbx; R12; R13; R14]               (* callee-saved *)

(* We use references for these parameters so they can be
 * overridden by command-line arguments. *)
let last_register_color : int ref = ref 0
let register_color_list : (location * int) list ref = ref []

let register_list_ok (regs : reg list) : bool =
  List.for_all (fun r -> List.mem r registers_used) regs

let set_register_color_list (regs : reg list) : unit =
  if not (register_list_ok regs) then
    failwith "set_register_color_list: invalid register list"
  else
    let nums        = range 0 (List.length regs) in
    let reg_colors  = List.combine regs nums in
    let assignments = [(Rsp, -2); (Rax, -1)] @ reg_colors in
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

(* Get the location corresponding to a color (int).
 * Usually this will be a register, but if there aren't
 * enough registers, it will be a stack location. *)
let location_of_color (i : int) : location =
  let map = color_register_map () in 
  match IntMap.find_opt i map with
    | None ->
      StackL (Rbp, -8 * (i - !last_register_color))
    | Some l -> l

(* ----------------------------------------------------------------- *) 

(* Extract just the variable mappings from a graph coloring,
 * and map them to their (register and stack) locations. *)
let varmap_of_colormap (color_map : int LocMap.t) : location VarMap.t =
  let rec helper color_map location = 
    match color_map with
      | (VarL loc, i) :: t -> helper t (VarMap.add loc (location_of_color i) location)
      | _ :: t -> helper t location
      | _ -> location
  in helper (LocMap.bindings color_map) (VarMap.empty)

(* Determine the variable -> location mapping based on the
 * interference graph. *)
let get_variable_location_map (g : LocUgraph.t) : location VarMap.t =
  (* Perform the graph coloring, and convert to var -> loc map. *)
  varmap_of_colormap (Color.color g (register_color_map ()))

(* Get the location of var *)
let get_var_loc (v : var) (map : location VarMap.t) =
  match VarMap.find_opt v map with
    | Some (RegL i) -> Reg i
    | Some (StackL (r, i)) -> Deref (r, i)
    | Some (VarL _) -> failwith "get_var_loc: unexpected error; var mapped to var"
    | None -> failwith "get_var_loc: unexpected error; var mapping not found"

let check_for_var (a : arg) map =
  match a with
    | Var v -> get_var_loc v map
    | _ -> a

(* Convert all the instructions with arguments. *)
let convert_instr (map : location VarMap.t) (ins : instr) : instr =
  match ins with
    | Addq (a, b) -> Addq (check_for_var a map, check_for_var b map)
    | Subq (a, b) -> Subq (check_for_var a map, check_for_var b map)
    | Negq (a) -> Negq (check_for_var a map)
    | Movq (a, b) -> Movq (check_for_var a map, check_for_var b map)
    | Pushq a ->  Pushq (check_for_var a map)
    | Popq a -> Popq (check_for_var a map)
    | _ -> ins

(* Convert a block.  Block info is empty, so it's just passed through. *)
let convert_block (map : location VarMap.t) (bl : 'a block) : 'a block =
  let (Block (bi, ins)) = bl in
    Block (bi, List.map (convert_instr map) ins)

(* Get the count of the number of variables spilled to the stack. *)
let get_num_spilled (map : location VarMap.t) : int =
  let _, locs = List.split (VarMap.bindings map) in 
  let rec counter locs set = 
    match locs with
      | StackL(a, b) :: t -> counter t (LocSet.add (StackL (a,b)) set)
      | _ :: t -> counter t set
      | _ -> set
  in 
  let locs' = counter locs LocSet.empty in 
  LocSet.cardinal locs'

(* Compute the set of callee-save registers used. *)
let get_used_callee (map : location VarMap.t) : RegSet.t =
  let bindings = VarMap.bindings map in 
  let (_, locs) = List.split bindings in 
  RegSet.filter (fun x -> List.mem (RegL x) locs) callee_save_regs


(* Allocate registers to variables in the code. *)
let allocate_registers (prog : (info2, binfo1) program)
      : (info3, binfo1) program =
  let (X86Program (Info2 info, lbs)) = prog in
  let (map : location VarMap.t) =
    get_variable_location_map info.conflicts
  in
  let info' = Info3 
    { 
      locals_types = info.locals_types;
      num_spilled  = get_num_spilled map;
      used_callee  = get_used_callee map
    }
  in
  (* Rewrite the code using the variable->register map. *)
  let lbs' =
    List.map 
      (fun (label, block) -> (label, convert_block map block))
      lbs 
  in
    X86Program (info', lbs')
