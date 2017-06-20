
type t = int

(* ordering *)

let compare (a:t) (b:t) = compare a b
let equal (a:t) (b:t) = a = b
let leq (x:t) (y:t) : bool = x <= y
let geq (x:t) (y:t) : bool = x >= y
let lt (x:t) (y:t) : bool = x < y
let gt (x:t) (y:t) : bool = x > y
let neq (x:t) (y:t) : bool = x <> y

let odd (x:t) : bool = x mod 2 = 1
let even (x:t) : bool = x mod 2 = 0

let min (x:t) (y:t) : t = min x y
let max (x:t) (y:t) : t = max x y

let sign (x:t) : int =
  if x > 0 then 1 else
  if x < 0 then -1 else 0

(* conversion, printing *)

let of_int_up (a:int) : t = a
let of_int_down (a:int) : t = a
let of_float_up a : t = int_of_float a
let of_float_down a : t = int_of_float a

let of_string x = int_of_string x

let of_string_up = of_string
let of_string_down = of_string

(* enumerates the values between a and b for splitting, only called in discrete domains *)
let enumerate (a:t) (b:t):t list =
  let rec aux acc a b = match equal a b with
    | true -> a::acc
    | false -> aux (b::acc) a (b-1)
  in aux [] a b

(* Note: adds 0. to favor positive 0 *)
let to_string x = string_of_int x

let to_float_up x = float_of_int x
let to_float_down x = float_of_int x

(* printing *)
let output chan x = output_string chan (to_string x)
let sprint () x = to_string x
let bprint b x = Buffer.add_string b (to_string x)
let pp_print f x = Format.pp_print_string f (to_string x)


(* classification *)

type kind = FINITE | MINF | INF | INVALID

let classify (x:t) : kind = FINITE

let fin = (1.0/.0.0)

(* useful constants *)
  
let zero : t = 0
let one : t = 1
let two : t = 2
let minus_one : t = -1
let inf : t = max_int/2
let minus_inf : t = min_int/2
let nan : t = 0


(* exact operators *)

let neg x = x
let abs x = abs x


(* operators with rounding *)
let add_up a b = a + b
let sub_up a b = a - b
let mul_up a b = a * b
let div_up a b = 
  match sign a, sign b with
  |  0,_ -> zero
  |  1,0 -> inf
  | -1,0 -> minus_inf
  | _ -> a / b

let add_down a b = add_up a b
let sub_down a b = sub_up a b
let mul_down a b = mul_up a b
let div_down a b = div_up a b

(* helper: oo * 0 = 0 when multiplying bounds *)
let bound_mul f x y =
  if sign x = 0 || sign y = 0 then zero else f x y

(* helper: 0/0 = 0, x/0 = sign(x) oo *)
let bound_div f x y =
  match sign x, sign y with
  |  0,_ -> zero
  |  1,0 -> inf
  | -1,0 -> minus_inf
  | _ -> f x y

(* TODO: improve and check soundness *)
let sqrt_up x = failwith "No squared rood on integers"
let sqrt_down x = sqrt_up x

let rec pow_up x n = match n with
  | 0 -> 1
  | _ -> x * pow_up x (n-1)
let pow_down x n = pow_up x n

let root_up x n = failwith "No root on integers"

let root_down x n = failwith "No root on integers"

let pi = 3.141592653589793
let twopi = 2.*.pi

(* returns true is cos is monotonic and strictly decreasing around x; x in [0;2pi] *)
let is_cos_decreasing x = failwith "No trigo on integers"

let to_zero_twopi x = failwith "No trigo on integers"

(* returns true is cos is monotonic and strictly decreasing around x*)
let is_cos_decreasing x = failwith "No trigo on integers"

let is_sin_decreasing x = failwith "No trigo on integers"

(* let cos_up x = if is_cos_decreasing x then cos x else -.(cos (-.x)) *)

(* let cos_down x =  *)
(*   if is_cos_decreasing x then -. (cos (-.x)) else cos x *)

(* let sin_up x =  *)
(*   if is_sin_decreasing x then sin x else -.(sin (-.x)) *)

(* let sin_down x =  *)
(*   if is_sin_decreasing x then -.(sin (-.x)) else sin x *)

let cos_up = fun x -> failwith "No trigo on integers"
let cos_down = fun x ->failwith "No trigo on integers"

let sin_up = fun x ->failwith "No trigo on integers"
let sin_down =fun x -> failwith "No trigo on integers"

let tan_up = fun x ->failwith "No trigo on integers"
let tan_down = fun x ->failwith "No trigo on integers"

let acos_up = fun x -> failwith "No trigo on integers"
let acos_down x = failwith "No trigo on integers"

let asin_up = fun x -> failwith "No trigo on integers"
let asin_down x = failwith "No trigo on integers"

let atan_up = fun x -> failwith "No trigo on integers"
let atan_down = fun x -> failwith "No trigo on integers"

let exp_up = fun x -> failwith "No trigo on integers"
let exp_down x = failwith "No trigo on integers"

let ln_up = fun x -> failwith "No trigo on integers"
let ln_down = fun x -> failwith "No trigo on integers"

let log_up = fun x -> failwith "No trigo on integers"
let log_down = fun x -> failwith "No trigo on integers"


(* double-precision characteristics *)

let mant_size = 52
let min_exp = -1022
let max_exp = 1023
let min_denormal = ldexp 1. (min_exp-mant_size)
let min_normal = ldexp 1. min_exp
let max_normal = ldexp (2. -. ldexp 1. (-mant_size)) max_exp
let max_exact = ldexp 1. mant_size
let ulp = ldexp 1. (-mant_size)

let floor x = x
let ceil x = x
