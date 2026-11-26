open LibCore.Passes

let parse_file filename =
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try
    let p = Parser.main Lexer.token lexbuf in
    close_in ic;
    p
  with
  | Parser.Error ->
     let p = lexbuf.lex_curr_p in
     let tok = Lexing.lexeme lexbuf in
     failwith
       (Printf.sprintf "parse error at %s:%d:%d near %S"
          p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol) tok)
  |  e -> close_in_noerr ic; raise e

let pipeline options filename =
  parse_file filename
  |>~ (handle_option "parsing" options (print_pass Types.ParsedProg.pp)
       ++> PassProof.passe)
