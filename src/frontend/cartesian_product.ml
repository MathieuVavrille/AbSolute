open Csp

module Env = Map.Make(struct type t=string let compare=compare end)

let rec power x n = if n = 0 then 1 else begin
  if n > 0 then x*power x (n-1) else failwith "power of non positive value" end

module Prog_int = struct
  type t = prog * bexpr Env.t

  let create prog =
    let res = List.fold_left (fun acc var ->
      Env.add var [] acc
    ) Env.empty (get_vars prog)
    in (prog, List.fold_left (fun acc constr ->
      List.fold_left (fun acc2 var ->
	Env.add var (constr::(Env.find var acc2)) acc2
      ) acc (variables_of_c constr [])
    ) res prog.constraints)
    
  let list_constraints_of_var (prog, constraints_of_var) var =
    Env.find var constraints_of_var
    
end
    
module Cartesian_int = struct
  type domain = int list  
  module IntEnv = Map.Make(struct type t=int let compare=compare end)
  type t = domain Env.t

  let empty : t = Env.empty

  let add_var_bounds (abs:t) (var:string) (l,h:int*int) =
    let rec aux acc a b = match a = b with
    | true -> a::acc
    | false -> aux (b::acc) a (b-1)
    in Env.add var (List.sort compare (aux [] l h)) abs

  let add_var_enum (abs:t) (var:string) (dom:int list) =
    Env.add var (List.sort compare dom) abs

  let find (abs:t) (var:string) =
    Env.find var abs

  (* A really simple printing function *)
  let print abs = Env.iter (fun k d ->
    print_string ("Variable "^k^":\n");
    List.iter (fun v -> print_int v; print_string ", ") d;
    print_newline ()) abs
    
  (*delete from the list but keeps the order*)
  let delete_from_list l x =
    let rec aux acc l = match l with
      | [] -> acc
      | v::q when v = x -> List.rev_append acc q
      | v::q when v < x -> aux (v::acc) q
      | _ -> List.rev_append acc l
    in aux [] l
      
  let delete (abs:t) (var:string) (value:int) =
    Env.add var (delete_from_list (find abs var) value) abs

  let rec value_expr e vars = match e with
    | Unary(op, e1) -> (match op with
      | NEG -> -value_expr e1 vars
      | ABS -> abs (value_expr e1 vars)
      | _ -> failwith "unary operation over floats not implemented")
    | Binary(op, e1, e2) -> let v1, v2 = value_expr e1 vars, value_expr e2 vars in (match op with
      | ADD -> v1 + v2
      | SUB -> v1 - v2
      | MUL -> v1 * v2
      | DIV -> v1 / v2
      | POW -> power v1 v2
      | NROOT -> failwith "nroot not implemented"
      | MIN -> min v1 v2
      | MAX -> max v1 v2)
    | Var(v) -> Env.find v vars
    | Cst(i) -> int_of_float i
      
  (* sees if the constraint is satisfied *)
  let rec is_satisfied c vars = match c with
    | Cmp(cmp, e1, e2) -> (match cmp with
      | EQ -> value_expr e1 vars = value_expr e2 vars
      | LEQ -> value_expr e1 vars <= value_expr e2 vars
      | GEQ -> value_expr e1 vars >= value_expr e2 vars
      | NEQ -> value_expr e1 vars <> value_expr e2 vars
      | GT -> value_expr e1 vars > value_expr e2 vars
      | LT -> value_expr e1 vars < value_expr e2 vars)
    | And(e1, e2) -> is_satisfied e1 vars && is_satisfied e2 vars
    | Or(e1, e2) -> is_satisfied e1 vars || is_satisfied e2 vars
    | Not(e1) -> not (is_satisfied e1 vars)

  let print_support s = 
       Env.iter (fun k data ->
	 IntEnv.iter (fun i  valeur ->
	   print_string ("\nSUPPORT: "^k^" val "^string_of_int i^" verite "^(if valeur then "true" else "false"))
	 ) data
       ) s

  let print_instance ins = Env.iter (fun k d -> print_string ("\nInstance "^k^" value "^string_of_int d)) ins
	 
  (* Consistance d'arc sur une contrainte, pour l'instant on n'est pas intelligent *)
  let ac (abs:t) c =
    (* Pour savoir quelles valeurs ont des supports *)
    let supported = List.fold_left (fun acc var ->
      let ajout = List.fold_left (fun acc2 value ->
	IntEnv.add value false acc2) IntEnv.empty (Env.find var abs) in
      Env.add var ajout acc
    ) Env.empty (variables_of_c c []) in
    
    (* auxilliary function to search for all the solutions of the constraint, ins is the instanciation of the variables *)
    let rec aux l sup ins = match l with
      (* Case where all the variables are instanciated: if the constraint is satisfied, we check in supported that there is a support *)
      | [] -> if is_satisfied c ins then begin
	Env.fold (fun k d acc ->
	  let support_var = Env.find k acc in
	  Env.add k (IntEnv.add d true support_var) acc
	) ins sup
      end
	else sup
      (* Else, we have to instanciate the variables (like in a backtrack) *)
      | (k, dom)::q -> List.fold_left (fun acc value ->
	aux q acc (Env.add k value ins)
      ) sup dom
	 
    in let new_supports = aux (Env.bindings abs) supported Env.empty in
       List.fold_left (fun acc (v, values) ->
	 List.fold_left (fun acc2 (valeur, present) ->
	   if present then acc2 else (v, valeur, c)::acc2
	 ) acc (IntEnv.bindings values)
       ) [] (Env.bindings new_supports)

  let full_ac prog abs =
    let (_, constr_of_var) = Prog_int.create prog in
    let rec add_to_list l c = match l with
      | [] -> [c]
      | x::q when x = c -> l
      | x::q -> x::add_to_list q c in
    (* Fonction qui va parcourir les contraintes et les rendre consistantes *)
    let rec propagate l abs = match l with
      | [] -> abs
      | c::q -> let to_delete = ac abs c in
		let new_abs = List.fold_left (fun acc (var,value,_) ->
		  delete acc var value
		) abs to_delete in
		let new_list = List.fold_left (fun acc (var,_,constr) ->
		  List.fold_left (fun acc2 c ->
		    if c <> constr then add_to_list acc2 c else acc2
		  ) acc (Env.find var constr_of_var)
		) q to_delete in
		propagate new_list new_abs 
    in propagate prog.constraints abs

  let best_var abs = Env.fold (fun k l (best, nom) ->
    if List.length l <> 1 && (List.length l < best || best = -1) then (List.length l, k) else (best, nom)
  ) abs (-1, "")

  let split abs = match best_var abs with
    | (-1, "") -> []
    | (best, nom) -> List.map (fun value ->
      Env.add nom [value] abs) (Env.find nom abs)


  (* Encore des bugs... *)
  let rec backtrack prog abs =
    let new_abs = full_ac prog abs in
    match split new_abs with
    | [] -> print_string "Une solution\n"; print abs; print_newline ()
    | l -> List.iter (fun dom_a -> backtrack prog dom_a) l
    
end

let c1 = Cmp(GEQ, Var("y"), Binary(SUB, Binary(MUL, Cst(2.0), Var("x")), Cst(2.0)))

let c2 = Cmp(LEQ, Binary(MUL, Cst(2.0), Var("y")), Binary(SUB, Cst(6.0), Var("x")))

let d1 = Cmp(GEQ, Binary(ADD, Var("x"), Var("y")), Cst(7.0))

let d2 = Cmp(LEQ, Binary(ADD, Var("x"), Var("y")), Cst(1.0))

let d3 = Cmp(GEQ, Binary(SUB, Var("x"), Var("y")), Cst(-3.0))

let d4 = Cmp(LEQ, Binary(SUB, Var("x"), Var("y")), Cst(3.0))

let prog = empty
let prog = {prog with init= [(INT, "x", Finite(0.0, 4.0)); (INT, "y", Finite(0.0,4.0))]}
let prog = {prog with constraints = [c1;c2]}

let abs = Cartesian_int.empty
let abs = Cartesian_int.add_var_bounds abs "x" (0,4)
let abs = Cartesian_int.add_var_bounds abs "y" (0,4)

let abs = Cartesian_int.backtrack prog abs
  

let ins = Env.empty
let ins = Env.add "x" 1 ins
let ins = Env.add "y" 4 ins

  let _ = print_string "\nTEST\n\n"
let _ = if Cartesian_int.is_satisfied c1 ins then print_string "true" else print_string "false"

let _ = print_newline()
