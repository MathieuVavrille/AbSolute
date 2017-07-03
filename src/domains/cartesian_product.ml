module Env = Map.Make(struct type t=string let compare=compare end)
module IntEnv = Map.Make(struct type t=int let compare=compare end)

open Cspplus

type action = Nothing | Affect of int * int * int list | Newmin of var * int | Newmax of var * int

module Cartesian_int = struct
  module S = Set_int

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
    Array.iteri (fun ind (_, _, l) ->
      print_string (i_to_v.(ind)^"="^string_of_list l)
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

  let enumerate_var abs var =
    let (_, _, l) = abs.(var) in l

  let is_inconsistent abs =
    Array.exists (fun (_, _, l) -> l=[]) abs

  let is_singleton_var abs v =
    S.is_singleton abs.(v)

  let is_singleton abs =
    Array.for_all S.is_singleton abs

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
    (* A better algorithme will be used for alldiff constraint *)
    | Alldif(l) -> let rec aux l varl = match varl with
      | [] -> true
      | x::q when List.mem (vars.(x)) l -> false
      | x::q -> aux (vars.(x)::l) q
		   in aux [] l

  let rec eval_ineq ineq abs = match ineq with
    | Add_lin(i1, i2) -> eval_ineq i1 abs + eval_ineq i2 abs
    | Mul_lin(coeff, Min_lin(var)) -> coeff * S.min abs.(var)
    | Mul_lin(coeff, Max_lin(var)) -> coeff * S.max abs.(var)
    | Cst_lin(c) -> c

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

  let create_intenv values param =
    List.fold_left (fun acc value ->
      IntEnv.add value param acc) IntEnv.empty values

  let bc_ineq abs tab var_list = List.fold_left (fun acc var ->
      match tab.(var) with
      | LT_lin(coeff, expr) ->
	 let value = eval_ineq expr abs in
	 if value mod coeff = 0 then List.rev_append S.list_greater_eq abs.(var)
      | GT_lin(coeff, expr) ->
      | LEQ_lin(coeff, expr) ->
      | GEQ_lin(coeff, expr) ->



    ) var_list


  let ac abs (constr, var_list, qual) prog = (*print_string "ac\n";*)
    match qual with
    | Other(compt, sup) ->
    (* Function to find all the values to delete *)
    let find_non_supported () =
      List.fold_left (fun acc var ->
	IntEnv.fold (fun value nb_sup acc2 ->
	  if nb_sup = 0 then (*print_string ("Non_supported "^string_of_int var^" "^string_of_int value^"\n");*)(var, value)::acc2 else (*(print_string ("Supported "^string_of_int var^" "^string_of_int value^" "^string_of_int nb_sup^"\n"); *)acc2
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
	| [] -> if is_satisfied constr instanciation then begin (*print_string "Ins: "; print_ins print_int instanciation; print_newline ();*)
	  List.iter (fun var ->
	    let value = instanciation.(var) in
	    let new_compteur = try IntEnv.find value compt.(var) + 1 with _ -> 1 in
	    compt.(var) <- IntEnv.add value new_compteur compt.(var);
	    let new_support = try IntEnv.find value sup.(var) with _ -> [] in
	    sup.(var) <- IntEnv.add value (Array.copy instanciation::new_support) sup.(var)
	  ) var_list
	end
	| x::q -> (*print_int x; print_newline ();*)
	   let values = enumerate_var abs x in
	   List.iter (fun value -> (*print_int x; print_string " "; print_int value;print_newline ();*)
	     instanciation.(x) <- value; aux q
	   ) values
      in (*print_list print_int var_list;*)aux var_list;
      find_non_supported ()
    end
      else find_non_supported ()

    | Ineq_lin(tab) ->

  (* Function that will delete the value from the constraint, and return the list of variables/values to delete *)
  let delete_from_constr var value ((constr, vars_list, qual) as c) = (*print_constr c;print_string ("dddelete_from_constr "^string_of_int var^" "^string_of_int value^"\n");*)match qual with
    | Other(compt, sup) -> if not (is_support_empty compt && is_support_empty sup) then begin
      let tuple_list = IntEnv.find value sup.(var) in
       (*print_list tuple_list print_ins;*)
       (* Dans toutes les listes de supports on supprime ceux à supprimer, et on décrémente les compteurs *)
       List.fold_left (fun new_to_delete inst ->
	 List.fold_left (fun to_delete d_var ->
	   let d_value = inst.(d_var) in
	   let d_sup = sup.(d_var) in
	   sup.(d_var) <- IntEnv.add d_value (remove_from_list inst (IntEnv.find d_value d_sup)) d_sup;
	   let d_compt = compt.(d_var) in
	   let nb_sup = IntEnv.find d_value d_compt in
	   compt.(d_var) <- IntEnv.add d_value (nb_sup - 1) d_compt;
	   (*print_string ("Deleting "^string_of_int d_var^" "^string_of_int d_value^" "^string_of_int nb_sup^" "^string_of_int (List.length (IntEnv.find d_value sup.(d_var)))^"\n");*)
	   match nb_sup with
	   | 1 when d_var <> var-> (d_var, d_value)::to_delete
	   | x when x < 1 -> (*print_string ("Compt:"^string_of_int d_var^" "^string_of_int d_value);*)failwith "Erreur lors de la suppression du support, compteur trop petit"
	   | _ -> to_delete
	 ) new_to_delete vars_list
       ) [] tuple_list end else []

  (* Makes the domain arc consistent, returns true if the domain is inconsistent *)
  let full_ac abs prog action = (*print_string "fullac\n"; print abs prog;*)
    let rec propagate_var l = match l with
      | [] -> false
      | (var, value)::q -> (*print_string "appel "; print_list (fun (v, w) -> print_int v;print_int w) l; print abs prog;*)if delete abs var value then true else begin
	let to_delete = List.fold_left (fun acc constr ->
	  let new_delete = delete_from_constr var value constr in
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

  let rec backtrack prog abs action =
    if not (full_ac abs prog action) then begin
    match is_singleton abs with
    | true -> print_string "Resultat: "; print abs prog;(*Format.printf "%a\n" print (abs,prog); *)print_newline ()
    | false -> (*List.iter (fun (_, _, Other(compt, sup)) -> print_string "Compteur = "; print_comp compt;
		 print_string "\nSupport = ";print_sup sup; print_newline () ) prog.constraints;*)
       let var_split = variable_to_split abs in
       let list_split = S.to_list abs.(var_split) in
       let nom_var = (fst prog.bijection).(var_split) in
       print_string ("List_split "^nom_var); print_newline ();
       List.iter (fun value -> (*print_string ("SPLIT sur "^string_of_int var_split^" val "^string_of_int value^"\n");*)
	 let new_abs = copy abs in
	 let new_prog = Cspplus.copy prog in
	 let all_deleted = remove_from_list value list_split in
	 backtrack new_prog new_abs (Affect(var_split, value, all_deleted))
       ) list_split end

end


let anonymous_arg = Constant.set_prob

let parse_args () = Arg.parse [("-trace", Constant.(Arg.Set trace), "Prints the solutions on standard output")] anonymous_arg ""

let go () =
  let open Constant in
  parse_args ();
  let prog = File_parser.parse !problem in
  if !trace then Format.printf "%a" Csp.print prog;
  let progplus, to_add = Cspplus.create prog in
  let abs = Cartesian_int.create_from_list to_add in
  Cartesian_int.backtrack progplus abs Nothing


(*let _ = add_to_list 9 [1;5;4;7;6;2;8] (fun a b -> a = b)

  let _ = concat_lists [1;2;3;5;9] [1;5;4;7;6;2;8] (fun a b -> a = b)*)

let generate_n_queens n = for i=1 to n do
    for j = i+1 to n do
      let s, t = "x"^string_of_int i, "x"^string_of_int j in
      print_string (s^" != "^t^";\n");
      print_string (s^"-"^t^" != "^string_of_int (i-j)^";\n");
      print_string (s^"-"^t^" != "^string_of_int (j-i)^";\n");
    done;done



let _ = 5/(-2)
