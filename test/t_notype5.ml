(* x is constrained to int by x + n: add must not be generalised over x *)
let add n = fun x -> x + n
let bad = add 1 true
