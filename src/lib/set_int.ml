(******************************************************************************)
(* Set of integer variables, the goal is to have a good implementation to fit *)
(* to the problem. For the moment, it is sorted lists with min and max. It is *)
(* possible to use double linked lists (see batterie) or interval lists, etc. *)
(******************************************************************************)

type t = int * int * int list

let empty : int * int * int list = 0, 0, []

let find_min_old_lists l =
  List.fold_left (fun acc x ->
    if x < acc then x else acc) (List.hd l) l

let find_max_old_lists l =
  List.fold_left (fun acc x ->
    if x > acc then x else acc) (List.hd l) l

(* Creates a domain from a list, if the list is empty, min and max are irrelevant *)
let of_list l : t = match l with
  | [] -> 0, 0, []
  | _ -> let new_l = List.sort compare l in
	 List.hd new_l, find_max_old_lists l, new_l

let of_bounds mini maxi =
  let rec aux acc a b = match a = b with
    | true -> a::acc
    | false -> aux (b::acc) a (b-1)
  in mini, maxi, aux [] mini maxi

let min ((m, _, _):t) = m

let max ((_, m, _):t) = m

let delete_min (_, m, l) = match l with
  | [] -> failwith "No min of empty list"
  | [x] -> 0, m, []
  | x::y::q -> y, m, y::q

let delete_max (mini, _, l) =
  let rec aux l = match l with
    | [] -> failwith "No max to delete in list"
    | [y] -> mini, 0, []
    | [x;y] -> mini, x, [x]
    | x::q -> let mini, maxi, q2 = aux q in
	      mini, maxi, x::q2
  in aux l

let delete ((mini, maxi, l) as l_plus) x = match mini = x, maxi = x with
  | true, _ -> delete_min l_plus
  | false, true -> delete_max l_plus
  | false, false ->
     let rec aux l = match l with
       | [] -> failwith ("Value "^string_of_int x^" not found while deleting")
       | y::q when x = y -> q
       | y::q -> y::aux q
     in mini, maxi, aux l

let is_empty (_, _, l) = l = []

let of_singleton x = (x, x, [x])

let is_singleton (mini, maxi, l) = (mini = maxi && l!=[])

let length (mini, maxi, l) = List.length l

let to_list (_, _, l) = l

let _ = delete (2, 4, [2;3;4]) 2
