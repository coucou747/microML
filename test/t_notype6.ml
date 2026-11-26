(* a lambda-bound variable stays monomorphic, even when re-bound by let *)
let bad = fun f -> let g = f in (g 0, g true)
