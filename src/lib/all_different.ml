let print_list affiche l = print_string "[";
    List.iter (fun v -> affiche v; print_string ";") l;
    print_string "]\n"

module Q = Queue

let shortest_path g visited start finish =
  let q = Q.create () in
  Q.add (start, []) q;
  let continuer = ref true in
  let chemin_final = ref [] in
  while !continuer && not (Q.is_empty q) do
    let (s, chemin) = Q.pop q in
    if not visited.(s) then begin
      visited.(s) <- true;
      if s = finish then begin
	chemin_final := finish::chemin;
	continuer := false end
      else
	List.iter (fun v -> Q.add (v, s::chemin) q) g.(s)
    end
  done;
  !chemin_final

(* Just gives the value of the max flow *)
let max_flow g start finish =
  let rec invert g l = match l with
    | [] -> failwith "no list"
    | [x] -> ()
    | x::y::q -> g.(y) <- List.filter (fun v -> x <> v) g.(y);
      g.(x) <- y::g.(x); invert g (y::q);
  in
  let compteur = ref 0 in
  let continue = ref true in
  while !continue do
    let visited = Array.make (Array.length g) false in
    let l = shortest_path g visited start finish in
    if l = [] then continue := false
    else begin
      invert g l; incr compteur
    end
  done;
  !compteur(*, List.fold_left (fun acc v -> (List.hd g.(v), v)::acc) [] g.(finish)*)

(* let g = [| [5;6;7;8;9;10;11;12;13];
	   [5;6;7;8;9;10;11;12;13];
	   [5;6;7;8;9;10;11;12;13];
	   [5;6;7;8;9;10;11;12;13];
	   [5;6;7;8;9;10;11;12;13];
	   [15];
	   [15];
	   [15];
	   [15];
	   [15];
	   [15];
	   [15];
	   [15];
	   [15];
	   [4;3;2;1;0];[] |]

let _ = max_flow g 14 15

   let _ = g *)

let delete_from_list2 l x1 x2 = List.filter (fun x -> x <> x1 && x <> x2) l

let delete_vertices g start finish =
  Array.iteri (fun i l ->
    g.(i) <- if i = start || i = finish then []
      else delete_from_list2 g.(i) start finish
  ) g

let compare_couples (x1, y1) (x2, y2) =
  let c = compare x1 x2 in
  if c = 0 then compare y1 y2 else c

module Cset = Set.Make (struct type t = int*int let compare = compare_couples end)

(* DFS to topological order, it is necessary to mark the first node visited!!! *)
let rec dfs_topo g visited s acc =
  s::List.fold_left (fun acc2 v ->
    if visited.(v) then acc2 else begin
      visited.(v) <- true;
      dfs_topo g visited v acc2 end) acc g.(s)

let rec dfs_not_comp g visited s acc r =
  List.fold_left (fun acc2 v ->
    if !(visited.(v)) = 2 then
      Cset.add (if s < v then (s, v) else (v, s)) acc2
    else begin
      if !(visited.(v)) = 0 then begin
	visited.(v) <- r;
	dfs_not_comp g visited v acc2 r end
      else acc2 end) acc g.(s)

let transpose g =
  let gT = Array.make (Array.length g) [] in
  Array.iteri (fun i l ->
    List.iter (fun v -> gT.(v) <- i::gT.(v)) l ) g;gT

(* All edges that are not in an alternating circuit *)
let comp_fort_connex g =
  let compteur1 =
    let x = ref (-1) in
    fun () -> incr x;!x in
  let visited = Array.make (Array.length g) false in
  let topo_order = Array.fold_left (fun acc b -> let i = compteur1 () in
    if not b then begin
      visited.(i) <- true;
      dfs_topo g visited i acc
    end
    else acc) [] visited in
  let visited = Array.make (Array.length g) (ref 0) in
  let gT = transpose g in
  List.fold_left (fun acc s ->
    if !(visited.(s)) = 2 then acc
    else begin
      let r = ref 1 in
      visited.(s) <- r;
      let res = dfs_not_comp gT visited s acc r in
      r := 2; res end) Cset.empty topo_order

let rec dfs_delete g visited s acc =
  List.fold_left (fun acc2 v ->
    if visited.(v) then Cset.remove (if s < v then (s, v) else (v, s)) acc2
    else begin
      visited.(v) <- true;
      dfs_delete g visited v (Cset.remove (if s < v then (s, v) else (v, s)) acc2) end
  ) acc g.(s)

(* All the edges that are not in an alterning path *)
let all_from_unmatched g present possible=
  let visited = Array.make (Array.length g) false in
  List.fold_left (fun acc s ->
    if visited.(s) then acc
    else begin
      visited.(s) <- true;
      dfs_delete g visited s acc
    end
  ) possible present
