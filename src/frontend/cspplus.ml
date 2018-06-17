(**************************************************************)
(* This module defines new programs that are easier to use    *)
(* in integer solver. We stock a lot of data in order to have *)
(* fast operations afterward.                                 *)
(**************************************************************)

module Env = Map.Make(struct type t=string let compare=compare end)
module IntEnv = Map.Make(struct type t=int let compare=compare end)
module VarSet = Set.Make(struct type t=int*int let compare= fun (_, v1) (_, v2) -> compare v1 v2 end)

(*Redifinition of type of programs to have constant access to variables (now ints) *)
(* variables are identified by an int *)
type var = int

(* constants are int (the domain of the variable *)
type i = int

(* unary arithmetic operators *)
type unop = NEG | ABS

let csp_to_unop op = match op with
  | Csp.NEG -> NEG
  | Csp.ABS -> ABS
  | _ -> failwith "Unary operation not allowed on integers"

(* binary arithmetic operators *)
type binop = ADD | SUB | MUL | DIV | POW | MIN | MAX

let csp_to_binop op = match op with
  | Csp.ADD -> ADD
  | Csp.SUB -> SUB
  | Csp.MUL -> MUL
  | Csp.DIV -> DIV
  | Csp.POW -> POW
  | Csp.MIN -> MIN
  | Csp.MAX -> MAX
  | _ -> failwith "Binary operation not allowed on integers"

(* numeric expressions *)
type expr =
  | Unary of unop * expr
  | Binary of binop * expr * expr
  | Var of var
  | Cst of i

(* boolean expressions *)
type bexpr =
  | Alldif of var list
  | Cmp of Csp.cmpop * expr * expr
  | And of bexpr * bexpr
  | Or of bexpr * bexpr
  | Not of bexpr

type domain_to_add = Finite of int * int | Enumerated of int list

type domain = int * int * int list (* min, max, valeurs. Remplacer int list par (int*int) list, ou bool Array?*)

(* Contraintes générales *)
type compteur = int IntEnv.t array (* On compte le nombre de supports *)

type support = (int array) list IntEnv.t array (* pour toute variable, valeur on a une liste de supports *)

(* Contraintes linéaires *)
type 'a lin_expr = Add_lin of 'a lin_expr * 'a lin_expr
		   | Mul_lin of int * 'a
		   | Cst_lin of int

type value = Min_lin of var | Max_lin of var

type ineq_lin_data = LT_lin of int * value lin_expr
		     | GT_lin of int * value lin_expr
		     | LEQ_lin of int * value lin_expr
		     | GEQ_lin of int * value lin_expr

type eq_lin_data = EQ_lin of int * int lin_expr
		   | NEQ_lin of int * int lin_expr

type matching_graph = {mutable graph: int list array; mutable matching: (int*int) list;
		       mutable val_to_int: int IntEnv.t; mutable int_to_val: int array}

(* Can be increased with other types (other global constraints) *)
type qualification = Other of compteur * support
		     | Eq_lin of eq_lin_data array
		     | Ineq_lin of ineq_lin_data array
		     | All_dif of matching_graph

type constr = bexpr * var list * qualification (* * rang *)

(* presence is the array of the constraints where the variable is involved *)
type prog_plus = { constraints: constr list; presence: constr list array; bijection: string array * int Env.t}

let rec power x n = if n = 0 then 1 else begin
  if n > 0 then x*power x (n-1) else failwith "power of non positive value" end

(******************************************)
(*          Printing                      *)
(******************************************)

let print_unop fmt = function
  | NEG -> Format.fprintf fmt "-"
  | ABS -> Format.fprintf fmt "abs"

let print_binop fmt = function
  | ADD -> Format.fprintf fmt "+"
  | SUB -> Format.fprintf fmt "-"
  | MUL -> Format.fprintf fmt "*"
  | DIV -> Format.fprintf fmt "/"
  | POW -> Format.fprintf fmt "^"
  | MIN -> Format.fprintf fmt "min"
  | MAX -> Format.fprintf fmt "max"

let rec print_expr fmt = function
  | Unary (NEG, e) ->
    Format.fprintf fmt "(- %a)" print_expr e
  | Unary (u, e) ->
    Format.fprintf fmt "%a %a" print_unop u print_expr e
  | Binary (b, e1 , e2) ->
    Format.fprintf fmt "%a %a %a" print_expr e1 print_binop b print_expr e2
  | Var v -> Format.fprintf fmt "%d" v
  | Cst c -> Format.fprintf fmt "CST(%d)" c

let rec print_list fmt = function
  | [] -> ()
  | [x] -> Format.fprintf fmt "%d" x
  | x::q -> Format.fprintf fmt "%d, %a" x print_list q

let rec print_bexpr fmt = function
  | Cmp (c,e1,e2) ->
    Format.fprintf fmt "%a %a %a" print_expr e1 Csp.print_cmpop c print_expr e2
  | And (b1,b2) ->
    Format.fprintf fmt "%a && %a" print_bexpr b1 print_bexpr b2
  | Or  (b1,b2) ->
    Format.fprintf fmt "%a || %a" print_bexpr b1 print_bexpr b2
  | Not b -> Format.fprintf fmt "not %a" print_bexpr b
  | Alldif l -> Format.fprintf fmt "all_different(%a)" print_list l

let print_constr (c, _, _) = Format.printf "%a\n" print_bexpr c

let rec min_max_to_string m = match m with
  | Add_lin(m1, m2) -> min_max_to_string m1^" + "^min_max_to_string m2
  | Mul_lin(coeff, Min_lin(var)) -> string_of_int coeff^"*Min("^string_of_int var^")"
  | Mul_lin(coeff, Max_lin(var)) -> string_of_int coeff^"*Max("^string_of_int var^")"
  | Cst_lin(i) -> string_of_int i

let ineq_to_string ineq = match ineq with
  | LT_lin(coeff, minmax) -> string_of_int coeff^"*VAR < "^min_max_to_string minmax
  | GT_lin(coeff, minmax) -> string_of_int coeff^"*VAR > "^min_max_to_string minmax
  | LEQ_lin(coeff, minmax) -> string_of_int coeff^"*VAR <= "^min_max_to_string minmax
  | GEQ_lin(coeff, minmax) -> string_of_int coeff^"*VAR >= "^min_max_to_string minmax

let ineq_lin_to_string tab =
  Array.fold_left (fun acc constr ->
    acc^"\n"^ineq_to_string constr^";") "[|" tab^"|]\n"

let rec eq_to_string m = match m with
  | Add_lin(m1, m2) -> eq_to_string m1^" + "^eq_to_string m2
  | Mul_lin(coeff, var) -> string_of_int coeff^"*"^string_of_int var
  | Cst_lin(i) -> string_of_int i

let eq_to_string ineq = match ineq with
  | EQ_lin(coeff, minmax) -> string_of_int coeff^"*VAR = "^eq_to_string minmax
  | NEQ_lin(coeff, minmax) -> string_of_int coeff^"*VAR <> "^eq_to_string minmax

let eq_lin_to_string tab =
  Array.fold_left (fun acc constr ->
    acc^"\n"^eq_to_string constr^";") "[|" tab^"|]\n"



(* Useful functions on constraints/programs *)
(* ----------- *)
let rec add_to_list l i = match l with
  | [] -> [i]
  | x::q when x < i -> x::add_to_list q i
  | x::q when x = i -> l
  | x::q -> i::l

let rec get_vars_expr expr l = match expr with
  | Unary(_, e) -> get_vars_expr e l
  | Binary(_, e1, e2) -> get_vars_expr e1 (get_vars_expr e2 l)
  | Var(i) -> add_to_list l i
  | Cst(_) -> l

(* If you want all the vars, start with l=[]. It will be sorted in increasing order *)
let rec get_vars_constr constr l = match constr with
  | Cmp(_, e1, e2) -> get_vars_expr e2 (get_vars_expr e1 l)
  | And(e1, e2) -> get_vars_constr e1 (get_vars_constr e2 l)
  | Or(e1, e2) -> get_vars_constr e1 (get_vars_constr e2 l)
  | Not(e1) -> get_vars_constr e1 l
  | Alldif(ldif) -> List.fold_left (fun acc i -> add_to_list acc i) l ldif

let is_support_empty sup =
  Array.for_all (fun env -> env = IntEnv.empty) sup

let appears_in_constr var (_, l, _) =
  List.mem var l


(* Transformation des contraintes pour les rendre plus facilement manipulables: les variables deviennent des entiers *)
(* ----------- *)
let rec transform_list l bij = match l with
  | [] -> []
  | x::q -> (Env.find x bij)::(transform_list q bij)

let rec transform_expr expr bij = match expr with
  | Csp.Unary(op, e1) -> Unary(csp_to_unop op, transform_expr e1 bij)
  | Csp.Binary(op, e1, e2) -> Binary(csp_to_binop op, transform_expr e1 bij, transform_expr e2 bij)
  | Csp.Var(v) -> Var(Env.find v bij)
  | Csp.Cst(i) -> Cst(int_of_float i)

let rec transform_constr constr bij = match constr with
  | Csp.Alldif(l) -> Alldif(transform_list l bij)
  | Csp.Cmp(op, e1, e2) -> Cmp(op, transform_expr e1 bij, transform_expr e2 bij)
  | Csp.And(c1, c2) -> And(transform_constr c1 bij, transform_constr c2 bij)
  | Csp.Or(c1, c2) -> Or(transform_constr c1 bij, transform_constr c2 bij)
  | Csp.Not(c1) -> Not(transform_constr c1 bij)

let to_dom_int dom = match dom with
  | Csp.Finite(a, b) -> Finite(int_of_float a, int_of_float b)
  | Csp.Enumerated(l) -> Enumerated(List.map int_of_float l)
  | _ -> failwith "We don't deal with infinite domains"


(* Transformation of the linear constraints *)
(* -------------- *)

(* Hypothesis: A variable doesn't appear twice or more in the constraint *)

(* Inequalities *)

let is_ineq op = match op with
  | Csp.EQ | Csp.NEQ -> false
  | _ -> true

let rec is_expr_linear expr = match expr with
  | Cst(i) | Var(i) -> true
  | Binary(ADD, e1, e2) | Binary(SUB, e1, e2) -> is_expr_linear e1 && is_expr_linear e2
  | Binary(MUL, const, Var(v)) | Binary(MUL, Var(v), const) -> (match const with
    | Cst(i) -> true
    | Unary(NEG, Cst(i)) -> true
    | _ -> false)
  | Unary(NEG, e1) -> is_expr_linear e1
  | _ -> false

let is_constr_linear constr = match constr with
  | Cmp(op, e1, e2) -> is_expr_linear e1 && is_expr_linear e2
  | _ -> false

(* To separate the monomes of the constraint, and put them all in the left side of the constraint \sum a_ix_i - \sum a_ix_i + cst \le 0 *)
let rec split_pos_neg_expr expr pos neg cst = match expr with
  | Cst(coeff) -> pos, neg, cst+coeff
  | Var(var) -> VarSet.add (1, var) pos, neg, cst
  | Unary(NEG, Var(var)) -> pos, VarSet.add (1, var) neg, cst
  | Binary(MUL, const, Var(var)) | Binary(MUL, Var(var), const) ->
     let x = match const with
       | Cst(i) -> i
       | Unary(NEG, Cst(i)) -> -i
       | _ -> failwith "Not a linear expression" in
     if x > 0 then VarSet.add (x, var) pos, neg, cst else
       if x < 0 then pos, VarSet.add (-x, var) neg, cst else
	 pos, neg, cst
  | Unary(NEG, expr1) -> let neg2, pos2, cst2 = split_pos_neg_expr expr1 neg pos (-cst) in
			 pos2, neg2, -cst2
  | Binary(ADD, expr1, expr2) ->
     let pos1, neg1, cst1 = split_pos_neg_expr expr1 pos neg cst in
     split_pos_neg_expr expr2 pos1 neg1 cst1
  | Binary(SUB, expr1, expr2) ->
     let neg2, pos2, cst2 = split_pos_neg_expr expr2 neg pos 0 in
     split_pos_neg_expr expr1 pos2 neg2 (-cst2+cst)
  | _ -> failwith "This is not a linear expression"

let rec split_pos_neg_constr constr = match constr with
  | Cmp(_, e1, e2) -> let neg, pos, cst = split_pos_neg_expr e2 VarSet.empty VarSet.empty 0 in
		      split_pos_neg_expr e1 pos neg (-cst)
  | _ -> failwith "This is not a linear constraint"

let rec to_right_side do_min do_neg s acc =
  VarSet.fold (fun (coeff, var) acc ->
    let new_coeff = if do_neg then -coeff else coeff in
    let new_var = if do_min then Min_lin(var) else Max_lin(var) in
    Add_lin(Mul_lin(new_coeff, new_var),acc)
  ) s acc

let rec to_right_side_eq do_neg s acc =
  VarSet.fold (fun (coeff, var) acc ->
    let new_coeff = if do_neg then -coeff else coeff in
    Add_lin(Mul_lin(new_coeff, var), acc)
  ) s acc

(* Assume the constraint is a linear inequality *)
let transform_to_linear constr nb_total_var = match constr with
  | Cmp(op, _, _) when op <> Csp.NEQ && op <> Csp.EQ ->
     let constr_data = Array.make nb_total_var (LT_lin(0, Cst_lin(0))) in
     let pos, neg, cst = split_pos_neg_constr constr in
     (* We don't want to compute too many times the same thing *)
     let neg_min_right = to_right_side true false neg (Cst_lin(-cst)) in
     let neg_max_right = to_right_side false false neg (Cst_lin(-cst)) in
     let pos_min_left = to_right_side true false pos (Cst_lin(cst)) in
     let pos_max_left = to_right_side false false pos (Cst_lin(cst)) in
     (* Rules for the bound consistency on linear constraints, with min and max of a variable, see CLP(FD) *)
     VarSet.iter (fun (coeff, var) ->
       let pos_removed = VarSet.remove (coeff, var) pos in
       match op with
       | Csp.LT -> constr_data.(var) <- LT_lin(coeff, to_right_side true true pos_removed neg_max_right)
       | Csp.GT -> constr_data.(var) <- GT_lin(coeff, to_right_side false true pos_removed neg_min_right)
       | Csp.LEQ -> constr_data.(var) <- LEQ_lin(coeff, to_right_side true true pos_removed neg_max_right)
       | Csp.GEQ -> constr_data.(var) <- GEQ_lin(coeff, to_right_side false true pos_removed neg_min_right)
       | _ -> failwith "This time it is really impossible"
     ) pos;
     VarSet.iter (fun (coeff, var) ->
       let neg_removed = VarSet.remove (coeff, var) neg in
       match op with
       | Csp.LT -> constr_data.(var) <- GT_lin(coeff, to_right_side false true neg_removed pos_min_left)
       | Csp.GT -> constr_data.(var) <- LT_lin(coeff, to_right_side true true neg_removed pos_max_left)
       | Csp.LEQ -> constr_data.(var) <- GEQ_lin(coeff, to_right_side false true neg_removed pos_min_left)
       | Csp.GEQ -> constr_data.(var) <- LEQ_lin(coeff, to_right_side true true neg_removed pos_max_left)
       | _ -> failwith "This time it is really impossible"
     ) neg; Ineq_lin(constr_data)
  | Cmp(op, _, _) ->
     let constr_data = Array.make nb_total_var (EQ_lin(0, Cst_lin(0))) in
     let pos, neg, cst = split_pos_neg_constr constr in
     let neg_right = to_right_side_eq false neg (Cst_lin(-cst)) in
     let pos_right = to_right_side_eq false pos (Cst_lin(cst)) in
     VarSet.iter (fun (coeff, var) ->
       let pos_removed = VarSet.remove (coeff, var) pos in
       match op with
       | Csp.EQ -> constr_data.(var) <- EQ_lin(coeff, to_right_side_eq true pos_removed neg_right)
       | Csp.NEQ -> constr_data.(var) <- NEQ_lin(coeff, to_right_side_eq true pos_removed neg_right)
       | _ -> failwith "This time it is really impossible"
     ) pos;
     VarSet.iter (fun (coeff, var) ->
       let neg_removed = VarSet.remove (coeff, var) neg in
       match op with
       | Csp.EQ -> constr_data.(var) <- EQ_lin(coeff, to_right_side_eq true neg_removed pos_right)
       | Csp.NEQ -> constr_data.(var) <- NEQ_lin(coeff, to_right_side_eq true neg_removed pos_right)
       | _ -> failwith "This time it is really impossible"
     ) neg; Eq_lin(constr_data)
  | _ -> failwith "We assumed the constraint was linear!!"



(* Creation of the program++ *)
(* --------- *)
let compteur =
  let cpt = ref 0 in
  fun () -> incr cpt; !cpt-1

let create prog =
  let all_var = Csp.get_vars prog in
  let nb_vars = List.length all_var in
  let int_to_vars = Array.make nb_vars "" in (* bijection from integers to variables, to be able to use arrays *)
  let vars_to_int = List.fold_left (fun acc var -> (* and from variables to integer *)
    let suiv = compteur () in
    int_to_vars.(suiv) <- var;Env.add var suiv acc
  ) Env.empty all_var in
  let list_constr_of_var = Array.make nb_vars [] in (* List of constraints in which there is the variable *)
  let constraints = List.map (fun constr -> (* List of constraints++ *)
    let constr_plus = transform_constr constr vars_to_int in
    let vars = get_vars_constr constr_plus [] in
    let new_constr = if is_constr_linear constr_plus then
	constr_plus, vars, transform_to_linear constr_plus nb_vars
      else
	match constr_plus with
	  | Alldif(l) -> constr_plus, vars, All_dif({graph = Array.make 0 [];matching = []; val_to_int = IntEnv.empty; int_to_val = Array.make 0 0})
	| _ -> constr_plus, vars, Other(Array.make nb_vars IntEnv.empty, Array.make nb_vars IntEnv.empty) in
    (* the list of constraints for each variable *)
    List.iter (fun var ->
      list_constr_of_var.(var) <- new_constr::list_constr_of_var.(var)
    ) vars; new_constr
  ) prog.Csp.constraints in
  (* variables, domains for creation of abstract domain *)
  let vars_to_add = List.map (fun (_, v, d) ->
    Env.find v vars_to_int, to_dom_int d
  ) prog.Csp.init in
  { constraints = constraints; presence = list_constr_of_var; bijection = int_to_vars, vars_to_int}, vars_to_add

(* We also have to update the list of presence because the we don't have the correct reference to the constraint *)
let copy prog =
  let list_constr_of_var = Array.make (Array.length prog.presence) [] in
  let constr = List.map (fun (c, var_list, qual) -> match qual with
    | Other(compt, sup) ->
       let new_constr = (c, var_list, Other(Array.copy compt, Array.copy sup)) in
       List.iter (fun var ->
	 list_constr_of_var.(var) <- new_constr::list_constr_of_var.(var)
       ) var_list; new_constr
    | All_dif(data) ->
       let new_constr = (c, var_list, All_dif({graph=Array.copy data.graph; matching = data.matching;val_to_int = data.val_to_int; int_to_val = data.int_to_val})) in
       List.iter (fun var ->
	 list_constr_of_var.(var) <- new_constr::list_constr_of_var.(var)
       ) var_list; new_constr
    |  _ ->
       let new_constr = (c, var_list, qual) in
       List.iter (fun var ->
	 list_constr_of_var.(var) <- new_constr::list_constr_of_var.(var)
       ) var_list; new_constr
    ) prog.constraints in
  { constraints = constr; presence = list_constr_of_var; bijection = prog.bijection}
