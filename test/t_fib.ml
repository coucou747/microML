external print_int : int -> unit = "prim_print_int_clot"

(* used to make the typer loop: two recursive calls under + *)
let rec fib n = if n = 0 then 0 else if n = 1 then 1 else fib (n - 1) + fib (n - 2)

let out = print_int (fib 20)
