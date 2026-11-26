external print_int : int -> unit = "prim_print_int_clot"

let compose f g = fun x -> f (g x)
let twice f = compose f f

let out =
  let rec id x = x in
  let a = id 1 in
  let b = id true in
  let _ = print_int (if b then a else 0) in
  print_int (twice (fun x -> x * 3) 2)
