module Cartesian_int = struct
  type domain = int list  
  module Env = Map.Make(struct type t=string let compare=compare end)
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

end
