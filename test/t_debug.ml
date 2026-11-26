external print_int : int -> unit = "prim_print_int_clot"

let compose f g = fun x -> f (g x)
let twice f = compose f f
let add n = fun x -> x + n

let out = print_int ((twice (add 1)) 0)
