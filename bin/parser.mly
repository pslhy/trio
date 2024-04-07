%{
open Expr

let rec appify (e:Expr.t) (es:Expr.t list) : Expr.t =
  match es with
  | [] -> e
  | e'::es -> appify (App (e, e')) es

let mk_unctor_or_ctor_by_name
      (c:string)
      (e:Expr.t)
    : Expr.t =
  if String.length c > 3 && String.equal (String.sub c 0 3) "Un_" then
    let c = String.sub c 3 (String.length c - 3) in
    Unctor (c, e)
  else
    Ctor (c, e)
%}

%token <string> LID
%token <string> UID
%token <string> STR
                (*%token <int> PROJ*)

%token <int> INT

%token FUN
%token MATCH
%token WITH
%token TYPE
%token OF
%token LET
%token LBRACKET
%token RBRACKET
(*%token IN*)
(*%token REC*)
%token UNIT

%token EQ
%token FATEQ
%token NEQ
%token ARR
%token COMMA
%token COLON
%token WILDCARD
%token FIX
%token SYNTH
%token SATISFYING
%token SEMI
%token STAR
%token PIPE
%token LPAREN
%token RPAREN
%token DOT
%token EOF
%token INCLUDE

%start unprocessed_problem
%start exp
%start imports_decls_start
%type <Specification.t_unprocessed> unprocessed_problem
%type <Expr.t> exp
%type <string list * declaration list> imports_decls_start

%%

unprocessed_problem:
    | ids=imports_decls SYNTH st=typ SATISFYING s=spec EOF
		  (* import files, decls, type, ?, spec *)
      { (fst ids,snd ids,st,s) }

imports_decls_start:
    | ids=imports_decls EOF
      { ids }

imports_decls:
    | is=imports ds=decl_list
      { (is,ds) }

imports:
    | INCLUDE s=STR is=imports
      { s::is }
    | { [] }

spec:
    | exs=examples
      {Specification.UIOEs exs}

examples:
  | exs=nonempty_examples
    { exs }
  | { [] }

nonempty_examples:
  | ex=example COMMA exs=examples
    { ex::exs }
  | ex=example
    { [ex] }

example:
  | LBRACKET es=exp_list RBRACKET ARR e=exp
    { (es,e) }

exp_list:
  | es=nonempty_exp_list
    { es }
  | { [] }

nonempty_exp_list:
  | e=exp COMMA es=exp_list
    { e::es }
  | e=exp
    { [e] }

(***** Declarations {{{ *****)

decl_list:
  | (* empty *)
    { [] }
  | d=decl ds=decl_list
    { d::ds }

decl:
  | TYPE i=LID EQ t=typ
    { TypeDeclaration (i, t) }
  | LET i=LID EQ e=exp SEMI SEMI
    { ExprDeclaration (i, e) }

typ:
  | t=typ_arrow   { t }
  | t=typ_tuple   { t }
  | t=typ_base    { t }
  | t=typ_paren   { t }
  | t=typ_unit    { t }
  | t=typ_variant { t }

typ_variant: (* (string * Type.t)  *)
  | t=typ_single_variant ts=typ_variant
    { Type.Variant (t::(Type.destruct_variant ts)) }
  | t=typ_single_variant
    { Type.Variant [t] }

typ_single_variant:
  | PIPE i=UID OF t=typ_non_variant
    { (i,t) }
  | PIPE i=UID
    { (i, (Tuple [])) }

typ_non_variant:
  | t=typ_arrow   { t }
  | t=typ_tuple   { t }
  | t=typ_base    { t }
  | t=typ_paren   { t }
  | t=typ_unit    { t }

typ_arrow:
  | t=typ_non_arrow ARR t2=typ { Type.Arrow (t, t2) }

typ_non_arrow:
  | t=typ_tuple { t }
  | t=typ_base  { t }
  | t=typ_paren { t }
  | t=typ_unit  { t }

typ_tuple:
  | ts=typ_tuple_list { Type.Tuple ts }

(* STAR binds more tightly than ARR, so we can't have an arrow type on the left. *)
typ_tuple_list:
  | t=typ_base  STAR ts=typ_tuple_list_one { t :: List.rev ts }
  | t=typ_paren STAR ts=typ_tuple_list_one { t :: List.rev ts }
  | t=typ_unit  STAR ts=typ_tuple_list_one { t :: List.rev ts }

typ_tuple_list_one: (* NOTE: reversed *)
  | t=typ_base  { [t] }
  | t=typ_paren { [t] }
  | t=typ_unit  { [t] }
  | ts=typ_tuple_list_one STAR t=typ_base  { t :: ts }
  | ts=typ_tuple_list_one STAR t=typ_paren { t :: ts }
  | ts=typ_tuple_list_one STAR t=typ_unit  { t :: ts }

typ_base:
  | d=LID { Type.Named (d) }

typ_paren:
  | LPAREN t=typ RPAREN { t }

typ_unit:
  | UNIT { Type.Tuple [] }

(***** }}} *****)

(***** Expressions {{{ *****)

exp:
  | e=exp_app
    { e }

exp_app:
  | e=exp_base es=exp_app_list
    { appify e (List.rev es) }
  | e=exp_base
    { e }

exp_app_list:     (* NOTE: reversed *)
  | e=exp_base
    { [e] }
  | es=exp_app_list e=exp_base
    { e::es }

arg:
  | LPAREN x=LID COLON t=typ RPAREN
    { (x, t) }

(*arg_list:   (* NOTE: reversed *)
  | (* Empty *)
    { [] }
  | xs=arg_list x=arg
    { x :: xs }*)

exp_base:
  | x=LID
    { Expr.Var x }
  | FUN x=arg ARR e=exp_base
    { Expr.Func (x, e) }
  | FIX a=arg EQ e=exp_base
    { Expr.Fix ((fst a), (snd a), e) }
  | c=INT
    { Expr.from_int c }
  | c=UID
    {
      mk_unctor_or_ctor_by_name c unit_
    }
  | c=UID LPAREN e=exp RPAREN
    { mk_unctor_or_ctor_by_name c e }
  | c1=UID c2=UID                                         (* Sugar: ctor with ctor argument.   *)
    { mk_unctor_or_ctor_by_name c1 (mk_unctor_or_ctor_by_name c2 unit_) }
  | c=UID x=LID                                           (* Sugar: ctor with var argument.    *)
    { mk_unctor_or_ctor_by_name c (Expr.Var x) }
  | c=UID LPAREN RPAREN                                   (* Sugar: ctor with unit argument.   *)
    { mk_unctor_or_ctor_by_name c unit_ }
  | c=UID LPAREN e=exp COMMA es=exp_comma_list_one RPAREN (* Sugar: ctor with tuple argument.  *)
    { mk_unctor_or_ctor_by_name c (Expr.Tuple (e :: List.rev es)) }
  | MATCH e=exp WITH bs=branches
    { Expr.Match (e, (List.rev bs)) }
  | LPAREN e=exp COMMA es=exp_comma_list_one RPAREN
    { Expr.Tuple (e :: List.rev es) }
  | e=exp_base DOT n=INT
    { Expr.Proj (n, e) }
  | e1=exp_base FATEQ e2=exp_base
    { Expr.Eq (true, e1, e2) }
  | e1=exp_base NEQ e2=exp_base
    { Expr.Eq (false, e1, e2) }
  | LPAREN e=exp RPAREN
    { e }
  | LPAREN RPAREN
    { unit_ }

exp_comma_list_one:    (* NOTE: reversed *)
  | e=exp
    { [e] }
  | es=exp_comma_list_one COMMA e=exp
    { e :: es }


branches:   (* NOTE: reversed *)
  | (* empty *)
    { [] }
  | bs=branches b=branch
    { b::bs }

branch:
  | PIPE p=pattern ARR e=exp
    { (p, e) }

pattern:
  | c=UID
    { (Pattern.Ctor (c, Pattern.Wildcard)) }
  | c=UID p=pattern
    { (Pattern.Ctor (c, p)) }
  | WILDCARD
    { Pattern.Wildcard }
  | LPAREN RPAREN
    { Pattern.Tuple [] }
  | LPAREN p=pattern COMMA ps=pattern_list RPAREN
    { Pattern.Tuple (p :: List.rev ps) }
  | x=LID
    { Pattern.Var x }

pattern_list: (* Reversed *)
  | p=pattern
    { [p] }
  | ps=pattern_list COMMA p=pattern
    { p::ps }

(***** }}} *****)

