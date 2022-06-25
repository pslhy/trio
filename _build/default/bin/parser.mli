
(* The type of tokens. *)

type token = 
  | WITH
  | WILDCARD
  | UNIT
  | UID of (string)
  | TYPE
  | SYNTH
  | STR of (string)
  | STAR
  | SEMI
  | SATISFYING
  | RPAREN
  | RBRACKET
  | PIPE
  | OF
  | NEQ
  | MATCH
  | LPAREN
  | LID of (string)
  | LET
  | LBRACKET
  | INT of (int)
  | INCLUDE
  | FUN
  | FIX
  | FATEQ
  | EQ
  | EOF
  | DOT
  | COMMA
  | COLON
  | ARR

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val unprocessed_problem: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Specification.t_unprocessed)

val imports_decls_start: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (string list * Expr.declaration list)

val exp: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Expr.t)
