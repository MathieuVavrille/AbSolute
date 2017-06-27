open Itv_sig
open Abstract_box.BoxIRat

type t = Abstract_box.BoxIRat.t

let print = Abstract_box.BoxIRat.print

let bound abs v = find v abs |> fst |> I.to_float_range

let draw draw_f fillpol abs (v1,v2) col =
  let (xl,xu) = bound abs v1 and (yl,yu) = bound abs v2 in
  let xl, xu, yl, yu = xl -. 0.1, xu +. 0.1, yl -. 0.1, yu +. 0.1 in
  fillpol [(xl, yl);(xl, yu);(xu, yu);(xu, yl)] col;
  let draw_seg vert value (b,c) =
    if vert then draw_f (value, b) (value,c) Graphics.black
    else draw_f (b,value) (c,value) Graphics.black
  in
  draw_seg true xl (yl, yu);
  draw_seg true xu (yl, yu);
  draw_seg false yl (xl, xu);
  draw_seg false yu (xl, xu)

let fill fillbox abs (v1,v2) col =
  let (xl,xu) = bound abs v1 and (yl,yu) = bound abs v2 in
  fillbox (xl -. 0.1, yl +. 0.1) (xu -. 0.1, yu +. 0.1) col

let draw2d = View.(draw draw_seg fill_poly)

let print_latex fmt = Latex.(fill (filldrawbox fmt))

let draw3d fmt abs_list (v1,v2,v3) =
  let make_cube (a,b) (c,d) (e,f) = ((a,c,e), b-.a, d-.c, f-.e) in
  let cube e = make_cube (bound e v1) (bound e v2) (bound e v3) in
  let cubes = List.rev_map (fun e -> cube e) abs_list in
  let o = Objgen.build_cube_list cubes in
  Format.fprintf fmt "%a" Objgen.print o
