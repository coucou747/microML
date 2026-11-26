
let file = ref None
let debug = ref []
let specs = [
    ("--debug", Arg.String (fun s -> debug := s::!debug), "add debug (args must be parsing, bindings, fields, eval or backend)");
    ("--trace", Arg.Unit (fun () -> debug := "trace"::!debug), "print each checked derivation tree as a JSON line (TRACE {...})");
  ]
let anon s = match !file with
  | None -> file := Some s
  | Some _ -> raise (Arg.Bad "only one input file allowed")

let options name = List.mem name !debug

let () =
  Arg.parse specs anon "usage: poule <file>";
  let filename =
    match !file with
    | Some f -> f
    | None -> raise (Arg.Bad "missing input file") in
  try
    ignore (Poulelib.Passes.pipeline options filename)
  with (Failure msg) as e ->
    Format.printf "%s\n\n" msg;
    raise e

