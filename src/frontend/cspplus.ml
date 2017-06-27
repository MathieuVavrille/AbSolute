(**************************************************************)
(* This module defines new programs that are easier to use    *)
(* in integer solver. We stock a lot of data in order to have *)
(* fast operations afterward.                                 *)
(**************************************************************)

module Env = Map.Make(struct type t=string let compare=compare end)
module IntEnv = Map.Make(struct type t=int let compare=compare end)

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

(* arithmetic comparison operators *)
type cmpop =
  | EQ | LEQ | GEQ | NEQ | GT | LT

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

type compteur = int IntEnv.t array (* On compte le nombre de supports *)

type support = (int array) list IntEnv.t array (* pour toute variable, valeur on a une liste de supports *)

type qualification = Other of compteur * support

type constr = bexpr * var list * qualification (* * rang *)

type prog_plus = { constraints: constr list; presence: constr list array; bijection: string array * int Env.t}

let rec power x n = if n = 0 then 1 else begin
  if n > 0 then x*power x (n-1) else failwith "power of non positive value" end

(* Useful functions on constraints/programs *)
(* ----------- *)
let rec add_to_list l i = match l with
  | [] -> []
  | x::q when x < i -> x::add_to_list q i
  | _ -> l

let rec get_vars_expr expr l = match expr with
  | Unary(_, e) -> get_vars_expr e l
  | Binary(_, e1, e2) -> get_vars_expr e1 (get_vars_expr e2 l)
  | Var(i) -> add_to_list l i
  | Cst(_) -> l

(* If you want all the vars, start with l=[]. It will be sorted in increasing order *)
let rec get_vars_constr constr l = match constr with
  | Cmp(_, e1, e2) -> get_vars_expr e1 (get_vars_expr e2 l)
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

(* Creation of the program++ *)
(* --------- *)
let compteur =
  let cpt = ref 0 in
  fun () -> incr cpt; !cpt

let create prog =
  let all_var = Csp.get_vars prog in
  let nb_vars = List.length all_var in
  let int_to_vars = Array.make nb_vars "" in (* bijection from integers to variables, to be able to use arrays *)
  let vars_to_int = List.fold_left (fun acc var ->
    let suiv = compteur () in int_to_vars.(suiv) <- var;Env.add var suiv acc
  ) Env.empty all_var in
  let list_constr_of_var = Array.make nb_vars [] in (* List of constraints in which there is the variable *)
  let constraints = List.map (fun constr -> (* List of constraints++ *)
    let constr_plus = transform_constr constr vars_to_int in
    let vars = get_vars_constr constr_plus [] in
    let n = List.length vars in
    let new_constr = constr_plus, vars, Other(Array.make n IntEnv.empty, Array.make n IntEnv.empty) in
    List.iter (fun var ->
      list_constr_of_var.(var) <- new_constr::list_constr_of_var.(var)
    ) vars; new_constr
  ) prog.Csp.constraints in
  let vars_to_add = List.map (fun (_, v, d) ->
    Env.find v vars_to_int, to_dom_int d
  ) prog.Csp.init in
  { constraints = constraints; presence = list_constr_of_var; bijection = int_to_vars, vars_to_int}, vars_to_add
