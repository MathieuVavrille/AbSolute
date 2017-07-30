module Env = Map.Make(struct type t=string let compare=compare end)
module IntEnv = Map.Make(struct type t=int let compare=compare end)
module A_d = All_different

open Cspplus

type action = Nothing | Affect of int * int * int list | Newmin of var * int | Newmax of var * int

module type Int_set =
sig
  type t

  val empty : t

  val length : t -> int
  val of_bounds : int -> int -> t
  val of_list : int list -> t
  val delete : t -> int -> t
  val is_empty : t -> bool
  val is_singleton : t -> bool
  val min : t -> int
  val max : t -> int
  val list_greater_eq : t -> int -> int list
  val list_smaller_eq : t -> int -> int list
  val to_list : t -> int list
  val to_singleton : t -> int
  val add_cst : t -> int -> t -> t
  val add_domains : t -> t -> t
  val mul_cst : t -> int -> t
  val divise : t -> int -> t
  val diff : t -> t -> t
  val inter : t -> t -> t

end


module Cartesian_int (S:Int_set) = struct

  (* Type mutable, les fonctions de modifications renvoient unit! *)
  type t = S.t array

  let empty = Array.make 0 S.empty

  let create_from_list l =
    let abs = Array.make (List.length l) S.empty in
    List.iter (fun (var, dom) ->
      match dom with
      | Finite(mini, maxi) -> abs.(var) <- S.of_bounds mini maxi
      | Enumerated(d) -> abs.(var) <- S.of_list d
    ) l; abs

  let string_of_list l =
    let rec aux l = match l with
      | [] -> ""
      | [x] -> string_of_int x
      | x::q -> string_of_int x^"; "^aux q
    in "["^aux l^"] "

  (* Simple printing function *)
  let print abs prog = let i_to_v = fst prog.bijection in print_string "Domaine: ";
    Array.iteri (fun ind dom ->
      print_string (i_to_v.(ind)^"="^string_of_list (S.to_list dom))
    ) abs; print_newline ()

  (*let print fmt (abs,prog) = let i_to_v = fst prog.bijection in
    let print_list fmt l =
      Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ";")
	(fun fmt -> Format.fprintf fmt "%i") fmt l
    in
    Array.iteri (fun ind (_,_,l) ->
      Format.fprintf fmt "%s=%a\n" i_to_v.(ind) print_list l
    ) abs*)

  let rec add_to_list x l equal = match l with
    | [] -> [x]
    | y::q when equal y x -> l
    | y::q -> y::add_to_list x q equal

  let rec concat_lists l1 l2 equal = match l1 with
    | [] -> l2
    | x::q -> concat_lists q (add_to_list x l2 equal) equal

  let rec remove_from_list x l = match l with
    | [] -> []
    | y::q when y = x -> q
    | y::q -> y::remove_from_list x q

  let copy = Array.copy

  (* true si le domaine devient inconsistent *)
  let delete abs var value =
    abs.(var) <- S.delete abs.(var) value; S.is_empty abs.(var)

  let is_inconsistent abs =
    Array.exists (fun (_, _, l) -> l=[]) abs

  let is_singleton_var abs v =
    S.is_singleton abs.(v)

  let is_singleton abs =
    Array.for_all S.is_singleton abs

  let singleton_to_array abs =
    Array.map S.to_singleton abs

  let rec value_expr e vars = match e with
    | Unary(op, e1) -> (match op with
      | NEG -> -value_expr e1 vars
      | ABS -> abs (value_expr e1 vars))
    | Binary(op, e1, e2) -> let v1, v2 = value_expr e1 vars, value_expr e2 vars in (match op with
      | ADD -> v1 + v2
      | SUB -> v1 - v2
      | MUL -> v1 * v2
      | DIV -> v1 / v2
      | POW -> power v1 v2
      | MIN -> min v1 v2
      | MAX -> max v1 v2)
    | Var(v) -> vars.(v)
    | Cst(i) -> i

  (* sees if the constraint is satisfied *)
  let rec is_satisfied c vars = match c with
    | Cmp(cmp, e1, e2) -> (match cmp with
      | Csp.EQ -> value_expr e1 vars = value_expr e2 vars
      | Csp.LEQ -> value_expr e1 vars <= value_expr e2 vars
      | Csp.GEQ -> value_expr e1 vars >= value_expr e2 vars
      | Csp.NEQ -> value_expr e1 vars <> value_expr e2 vars
      | Csp.GT -> value_expr e1 vars > value_expr e2 vars
      | Csp.LT -> value_expr e1 vars < value_expr e2 vars)
    | And(e1, e2) -> is_satisfied e1 vars && is_satisfied e2 vars
    | Or(e1, e2) -> is_satisfied e1 vars || is_satisfied e2 vars
    | Not(e1) -> not (is_satisfied e1 vars)
    (* A better algorithme is used for alldiff constraint consistency *)
    | Alldif(l) -> let rec aux l varl = match varl with
      | [] -> true
      | x::q when List.mem (vars.(x)) l -> false
      | x::q -> aux (vars.(x)::l) q
		   in aux [] l

  let is_a_solution abs constrs =
    if is_singleton abs then begin
      let sol = singleton_to_array abs in
      List.for_all (fun c -> is_satisfied c sol) constrs end
    else false

  let delete_all abs =
    let l = ref [] in
    Array.iteri (fun var vals ->
      List.iter (fun value ->
	l:= (var, value)::!l
      ) (S.to_list vals)
    ) abs;
    !l

  let rec eval_ineq ineq abs = match ineq with
    | Add_lin(i1, i2) -> eval_ineq i1 abs + eval_ineq i2 abs
    | Mul_lin(coeff, Min_lin(var)) -> coeff * S.min abs.(var)
    | Mul_lin(coeff, Max_lin(var)) -> coeff * S.max abs.(var)
    | Cst_lin(c) -> c

  let rec eval_eq eq abs = match eq with
    | Add_lin(i1, i2) -> S.add_domains (eval_eq i1 abs)  (eval_eq i2 abs)
    | Mul_lin(coeff, var) -> S.mul_cst abs.(var) coeff
    | Cst_lin(c) -> S.of_list [c]


  let print_env affiche env = print_string "{";
    IntEnv.iter (fun i v ->
      print_int i; print_string ":"; affiche v; print_string "|") env;
    print_string "}"

  let print_ins affiche ins = print_string "[|";
    Array.iteri (fun var i -> print_int var; print_string ":";affiche i;print_string ";") ins;
    print_string "|]"

  let print_list affiche l = print_string "[";
    List.iter (fun v -> affiche v; print_string ";") l;
    print_string "]\n"

  let print_sup = print_ins (print_env (print_list (print_ins print_int)))

  let print_comp = print_ins (print_env print_int)

  let print_graph = print_ins (print_list print_int)

  let print_couple affiche (x, y) = print_string "(";affiche x; print_string ",";affiche y;print_string ")"

  let create_intenv values param =
    List.fold_left (fun acc value ->
      IntEnv.add value param acc) IntEnv.empty values

  (* Consistency of linear inequality, in O(n^2), can be in O(n) *)
  let bc_ineq abs tab var_list =
    let add_cpl var l = List.map (fun value -> var, value) l in
    List.fold_left (fun acc var ->
      match tab.(var) with
      | LT_lin(coeff, expr) ->
	 let value = eval_ineq expr abs in
	 let value_bound = if value mod coeff = 0 then value/coeff
	   else if value < 0 then value/coeff
	   else value/coeff + 1 in
	 List.rev_append (add_cpl var (S.list_greater_eq abs.(var) value_bound)) acc
      | GT_lin(coeff, expr) ->
	 let value = eval_ineq expr abs in
	 let value_bound = if value mod coeff = 0 then value/coeff
	   else if value < 0 then value/coeff-1
	   else value/coeff in
	 List.rev_append (add_cpl var (S.list_smaller_eq abs.(var) value_bound)) acc
      | LEQ_lin(coeff, expr) ->
	 let value = eval_ineq expr abs in
	 let value_bound = if value mod coeff = 0 then value/coeff+1
	   else if value < 0 then value/coeff
	   else value/coeff + 1 in
	 List.rev_append (add_cpl var (S.list_greater_eq abs.(var) value_bound)) acc
      | GEQ_lin(coeff, expr) ->
	 let value = eval_ineq expr abs in
	 let value_bound = if value mod coeff = 0 then value/coeff-1
	   else if value < 0 then value/coeff-1
	   else value/coeff in
	 List.rev_append (add_cpl var (S.list_smaller_eq abs.(var) value_bound)) acc
    ) [] var_list

  (* Consistency of linear equation (=, !=) *)
  let ac_eq_lin abs tab var_list =
    let add_cpl var l = List.map (fun value -> var, value) l in
    List.fold_left (fun acc var ->
      match tab.(var) with
      | EQ_lin(coeff, expr) ->
	 let right_set = eval_eq expr abs in
	 let multiples = S.divise right_set coeff in
	 let to_delete = add_cpl var (S.to_list (S.diff abs.(var) multiples)) in
	 List.rev_append to_delete acc
      | NEQ_lin(coeff, expr) ->
	 let right_set = eval_eq expr abs in
	 let multiples = S.divise right_set coeff in
	 let to_delete = add_cpl var (S.to_list (S.inter abs.(var) multiples)) in
	 if S.is_singleton multiples then List.rev_append to_delete acc
	 else acc
    ) [] var_list


  let all_dif_incremental data nb_vars = (*print_string "all_dif_incremental\n";print_graph data.graph;*)
    let start = Array.length data.graph - 2 in
    let g = Array.make start [] in
    Array.iteri (fun i l ->
      List.iter (fun v -> if v < start then
	  g.(v) <- i::g.(v)
      ) data.graph.(i)
    ) g;
    let all_unmatched = Array.make start false in
    List.iter (fun (v, w) ->
      all_unmatched.(v) <- true;
      all_unmatched.(w) <- true
    ) data.matching;
    let l = ref [] in
    Array.iteri (fun i v -> if not v then l:= i::!l) all_unmatched;
    let possible_unmatched = A_d.comp_fort_connex g in
    let unmatched = A_d.all_from_unmatched g !l possible_unmatched in
    let real_unmatched = List.fold_left (fun acc edge ->
      A_d.Cset.remove edge acc
    ) unmatched data.matching in
    let to_delete_tab = A_d.Cset.elements real_unmatched in
    let to_delete = List.map (fun (x, y) ->
      x, data.int_to_val.(y-nb_vars)
    ) to_delete_tab in to_delete



  (* We create all the graph each time, and the implementation is not efficient TODO: improve *)
  (* Consistency of all_different constraint *)
  let ac_all_dif abs data var_list = (*print_string "Ac_all_dif\n";*)
    if data.matching = [] then begin
      let nb_var = List.length var_list in
      let nb_all_vars = Array.length abs in
      let compteur =
	let cpt = ref 0 in
	fun () -> incr cpt; !cpt-1
      in
      let list_all_var_val, val_to_int = List.fold_left (fun (l_acc, env_acc) var ->
	List.fold_left (fun (l_acc2, env_acc2) value ->
	  (var, value)::l_acc2, if IntEnv.mem value env_acc2 then env_acc2 else IntEnv.add value (compteur ()) env_acc2
	) (l_acc, env_acc) (S.to_list abs.(var))
      ) ([], IntEnv.empty) var_list in
      let nb_values = IntEnv.cardinal val_to_int in
      let int_to_val = Array.make (compteur ()) 0 in
      IntEnv.iter (fun value compt ->
	int_to_val.(compt) <- value
      ) val_to_int;
      let start = nb_all_vars + nb_values in
      let g = Array.make (start+2) [] in
      List.iter (fun var ->
	g.(var) <- List.map (fun value -> (IntEnv.find value val_to_int) + nb_all_vars) (S.to_list abs.(var));
	g.(start) <- var::g.(start)
      ) var_list;
      Array.iteri (fun i value ->
	g.(nb_all_vars+i) <- [start+1]
      ) int_to_val;
      let flot_max = A_d.max_flow g start (start+1) in
      let couplage =  List.fold_left (fun acc v -> (List.hd g.(v), v)::acc) [] g.(start+1) in
      if flot_max <> nb_var then delete_all abs
      else begin
	data.graph <- g; data.matching <- couplage; data.val_to_int <- val_to_int; data.int_to_val <- int_to_val;
	all_dif_incremental data nb_all_vars
      end
    end
    else
      all_dif_incremental data (Array.length abs)


  (* Function that will do the consistency on a constraint, depending on its kind (for linear, it will be bound consistency for example *)
  let ac abs (constr, var_list, qual) prog =
    match qual with
    | Other(compt, sup) ->
    (* Function to find all the values to delete *)
    let find_non_supported () =
      List.fold_left (fun acc var ->
	IntEnv.fold (fun value nb_sup acc2 ->
	  if nb_sup = 0 then (var, value)::acc2 else acc2
	) compt.(var) acc
      ) [] var_list
    in if is_support_empty compt && is_support_empty sup then begin
      let instanciation = Array.make (Array.length prog.presence) 0 in
      List.iter (fun var ->
	let value_list = S.to_list abs.(var) in
	let list_env = create_intenv value_list [] in
	let compt_env = create_intenv value_list 0 in
	for i=0 to Array.length compt do
	  sup.(var) <- list_env; compt.(var) <- compt_env
	done) var_list;
      (* The recursive function used to search in all the possible instanciations *)
      let rec aux l = match l with
	| [] -> if is_satisfied constr instanciation then begin
	  List.iter (fun var ->
	    let value = instanciation.(var) in
	    let new_compteur = try IntEnv.find value compt.(var) + 1 with _ -> 1 in
	    compt.(var) <- IntEnv.add value new_compteur compt.(var);
	    let new_support = try IntEnv.find value sup.(var) with _ -> [] in
	    sup.(var) <- IntEnv.add value (Array.copy instanciation::new_support) sup.(var)
	  ) var_list
	end
	| x::q ->
	   let values = S.to_list abs.(x) in
	   List.iter (fun value ->
	     instanciation.(x) <- value; aux q
	   ) values
      in aux var_list;
      find_non_supported ()
    end
      else find_non_supported ()

    | Ineq_lin(tab) -> bc_ineq abs tab var_list
    | Eq_lin(tab) -> ac_eq_lin abs tab var_list
    | All_dif(data) -> ac_all_dif abs data var_list


  (* Function that will delete the value from the constraint, and return the list of variables/values to delete *)
  let delete_from_constr abs var value (constr, var_list, qual)  = match qual with
    | Other(compt, sup) -> if not (is_support_empty compt && is_support_empty sup) then begin
      let tuple_list = IntEnv.find value sup.(var) in
       (* Dans toutes les listes de supports on supprime ceux à supprimer, et on décrémente les compteurs *)
       List.fold_left (fun new_to_delete inst ->
	 List.fold_left (fun to_delete d_var ->
	   let d_value = inst.(d_var) in
	   let d_sup = sup.(d_var) in
	   sup.(d_var) <- IntEnv.add d_value (remove_from_list inst (IntEnv.find d_value d_sup)) d_sup;
	   let d_compt = compt.(d_var) in
	   let nb_sup = IntEnv.find d_value d_compt in
	   compt.(d_var) <- IntEnv.add d_value (nb_sup - 1) d_compt;
	   match nb_sup with
	   | 1 when d_var <> var-> (d_var, d_value)::to_delete
	   | x when x < 1 ->failwith "Erreur lors de la suppression du support, compteur trop petit"
	   | _ -> to_delete
	 ) new_to_delete var_list
       ) [] tuple_list end else []
    | Ineq_lin(tab) -> bc_ineq abs tab var_list
    | Eq_lin(tab) -> ac_eq_lin abs tab var_list
    | All_dif(data) ->
       let deleted = IntEnv.find value data.val_to_int + Array.length abs in
       if List.mem deleted data.graph.(var) then begin (* the matching is unchanged *)
	 data.graph.(var) <- List.filter (fun x -> x <> deleted) data.graph.(var);
	 all_dif_incremental data (Array.length abs)
       end
       else begin (* we compute a new matching *)
	 let start = Array.length data.graph - 2 in
	 data.graph.(deleted) <- (start+1)::List.filter (fun x -> x <> var) data.graph.(deleted);
	 data.graph.(start+1) <- List.filter (fun x -> x <> deleted) data.graph.(start+1);
	 data.graph.(var) <- List.filter (fun x -> x <> start) data.graph.(var);
	 data.graph.(start) <- var::data.graph.(start);
	 let f =  A_d.max_flow data.graph start (start+1) in
	 if f <> 1 then begin (*print_string ("deleta_all "^string_of_int f^"\n");*)delete_all abs end
	 else begin
	   data.matching <- List.fold_left (fun acc v -> (List.hd data.graph.(v), v)::acc) [] data.graph.(start+1);
	   all_dif_incremental data (Array.length abs)
	 end
       end

  (* Makes the domain arc consistent, returns true if the domain is inconsistent *)
  let full_ac abs prog action = (*print_string "fullac\n"; print abs prog;*)
    let rec propagate_var l = (*print_string "Propagate_var\n";print_list (print_couple print_int) l;*)match l with
      | [] -> false
      | (var, value)::q -> if delete abs var value then true else begin
	(*print_string "appel "; print_list (fun (v, w) -> print_int v;print_int w) l; print_newline ();print abs prog;*)
	(*print_string ("min "^string_of_int var^" = "^string_of_int (S.min abs.(var))^" et max = "^string_of_int (S.max abs.(var))^"\n");*)
	let to_delete = List.fold_left (fun acc constr ->
	  let new_delete = delete_from_constr abs var value constr in
	  concat_lists new_delete acc (fun a b -> a = b)
	) q prog.presence.(var) in
	propagate_var to_delete
      end
    in
    (* Fonction qui va parcourir les contraintes et les rendre consistantes *)
    let rec propagate_constr l = (*print_string "Propagate_constr\n";*)match l with
      | [] -> false
      | c::q -> let to_delete = ac abs c prog in
		propagate_var to_delete || propagate_constr q
    in match action with
    | Nothing -> (*print_string "Nothing ";print_int (List.length prog.constraints);*)propagate_constr prog.constraints (* impose the consistency on all constraints *)
    | Affect(var, value, all_deleted) -> let useful_all_deleted = List.map (fun value -> (var, value)) all_deleted in
       propagate_var useful_all_deleted (* search for the consistency only in the possibly modified constraints *)
    | _ -> failwith "Split affect a value (currently, other forms of split are not implemented)"

  (* find the variable with the smallest domain , assume the abstract domain is not a singleton *)
  let variable_to_split abs =
    let var_mini = ref 0 in
    let mini = ref (S.length abs.(!var_mini)) in
    Array.iteri (fun var dom ->
      let new_mini = S.length dom in
      if new_mini > 1 && (new_mini < !mini || !mini <= 1) then begin mini := new_mini; var_mini := var end
    ) abs; !var_mini

  let compteur =
    let cpt = ref 0 in
    fun () -> incr cpt; !cpt-1

  let rec backtrack prog abs action =
    if not (full_ac abs prog action) then begin
    match is_singleton abs with
    | true -> if is_a_solution abs (List.map (fun (a, _, _) -> a ) prog.constraints) then begin
      if false then (print_string ("Resultat "^string_of_int (compteur ())^": "); print abs prog;1)
      else let _ = compteur () in 1 end
      else begin
	print_string "Erreur: ";print abs prog;1 end
    | false -> (*List.iter (fun (_, _, Other(compt, sup)) -> print_string "Compteur = "; print_comp compt;
		 print_string "\nSupport = ";print_sup sup; print_newline () ) prog.constraints;*)
       let var_split = variable_to_split abs in
       let list_split = S.to_list abs.(var_split) in
       1 + List.fold_left (fun acc value -> (*print_string ("SPLIT sur "^string_of_int var_split^" val "^string_of_int value^"\n");*)
	 let new_abs = copy abs in
	 let new_prog = Cspplus.copy prog in
	 let all_deleted = remove_from_list value list_split in
	 acc + (backtrack new_prog new_abs (Affect(var_split, value, all_deleted)))
       ) 0 list_split end
    else 1

end


let anonymous_arg = Constant.set_prob

let parse_args () = Arg.parse [("-trace", Constant.(Arg.Set trace), "Prints the solutions on standard output")] anonymous_arg ""

  (*module Cart = Cartesian_int (Int_dom_list)*)
module Cart_plus = Cartesian_int (Int_dom_set)

let go () =
  let open Constant in
  parse_args ();
  let prog = File_parser.parse !problem in
  if !trace then Format.printf "%a" Csp.print prog;
  let progplus, to_add = Cspplus.create prog in
  let abs = Cart_plus.create_from_list to_add in
  let nb_nodes = Cart_plus.backtrack progplus abs Nothing in
  print_int nb_nodes;print_newline ()
