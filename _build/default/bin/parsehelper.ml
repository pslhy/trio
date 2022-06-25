let get_lexbuf channel fname : Lexing.lexbuf =
  (* let inc = open_in fname in *)
  let lexbuf = Lexing.from_channel channel in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fname };
  (* let _ = close_in inc in *)
  lexbuf

let unprocessed_problem channel fname : Specification.t_unprocessed = 
  let lexbuf = get_lexbuf channel fname in
  Parser.unprocessed_problem Lexer.token lexbuf

let import_decls_start channel fname : string list * Expr.declaration list =
  let lexbuf = get_lexbuf channel fname in
  Parser.imports_decls_start Lexer.token lexbuf

let add_dir dir fname =
  dir ^ "/" ^ fname

let update_import (import_list:string list) (fname:string) =
let dir = Filename.dirname fname in
List.map (add_dir dir) import_list

let update_all (import_list, decls, synth_type, uspec) (fname:string) =
let ss = update_import import_list fname in
(ss, decls, synth_type, uspec)