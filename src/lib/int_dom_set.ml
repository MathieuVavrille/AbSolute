module S = Set.Make (struct type t=int let compare=compare end)

type t = S.t

let empty = S.empty

let length = S.cardinal

let of_list = S.of_list

let of_bounds mini maxi =
  let rec aux acc a b = match a = b with
    | true -> a::acc
    | false -> aux (b::acc) a (b-1)
  in of_list (aux [] mini maxi)

let delete ens x = S.remove x ens

let is_empty = S.is_empty

let is_singleton ens = S.cardinal ens = 1

let min = S.min_elt

let max = S.max_elt

let list_greater_eq ens b =
  S.fold (fun x acc ->
    if x >= b then x::acc else acc
  ) ens []

let list_smaller_eq ens b =
  S.fold (fun x acc ->
    if x <= b then x::acc else acc
  ) ens []

let to_list = S.elements

let to_singleton ens =
  if is_singleton ens then
    S.max_elt ens
  else
    failwith "The domain is not a singleton, we can't restrict it"

let add_cst ens c acc =
  S.fold (fun x acc2 ->
    S.add (x+c) acc2
  ) ens acc

let add_domains ens1 ens2 =
  S.fold (fun x acc2 ->
    add_cst ens1 x acc2
  ) ens2 S.empty

let mul_cst ens c =
  S.map (fun x -> x*c) ens

(* return all the elements that are divisible by m, (return their division) *)
let divise ens m =
  S.fold (fun x acc ->
    if x mod m = 0 then S.add (x/m) acc
    else acc
  ) ens S.empty


(* ens1\ens2 *)
let diff = S.diff

let inter = S.inter
