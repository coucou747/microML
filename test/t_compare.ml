external print_int : int -> unit = "prim_print_int_clot"

let b2i b = if b then 1 else 0

let out =
  let _ = print_int (b2i (1 < 2)) in
  let _ = print_int (b2i (2 < 1)) in
  let _ = print_int (b2i (2 <= 2)) in
  let _ = print_int (b2i (3 > 2)) in
  let _ = print_int (b2i (2 >= 3)) in
  let _ = print_int (b2i (1 <> 2)) in
  let _ = print_int (b2i ((1, 2) <> (1, 2))) in
  print_int (b2i (1 = 1))
