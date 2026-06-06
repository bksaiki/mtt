%token <string> ID
%token <int> INT
%token FUN PI TYPE CHECK EVAL CHECK_EQUAL AXIOM DEF THEOREM LPAREN RPAREN COLON ARROW DARROW EQUALS EOF

%start <Ast.t> main
%start <Stmt.t> stmt
%start <Stmt.t list> file

%%

main:
  | t = term; EOF { t }

(* a single REPL line: a declaration, or a bare term *)
stmt:
  | s = decl; EOF { s }
  | t = term; EOF { Stmt.Expr t }

(* a file is a sequence of declarations; bare terms are REPL-only, since
   without a statement terminator adjacent terms would parse as one
   application *)
file:
  | ss = list(decl); EOF { ss }

decl:
  | CHECK; t = term { Stmt.Check t }
  | EVAL; t = term { Stmt.Eval t }
  | AXIOM; x = ID; COLON; a = term { Stmt.Axiom (x, a) }
  | DEF; x = ID; COLON; a = term; EQUALS; t = term { Stmt.Def (x, Some a, t) }
  | DEF; x = ID; EQUALS; t = term { Stmt.Def (x, None, t) }
  | THEOREM; x = ID; COLON; a = term; EQUALS; t = term
    { Stmt.Theorem (x, a, t) }
  | CHECK_EQUAL; t = atom; u = atom { Stmt.CheckEqual (t, u) }

term:
  | FUN; LPAREN; x = ID; COLON; a = term; RPAREN; DARROW; b = term
    { Ast.Lam (x, a, b) }
  | PI; LPAREN; x = ID; COLON; a = term; RPAREN; DARROW; b = term
    { Ast.Pi (x, a, b) }
  | t = pi_term { t }

(* arrows are right-associative; the domain is one level tighter. There is
   no dedicated pi-binder production: "(x : A)" parses as an ascription
   atom, and an ascribed *variable* directly left of an arrow is read as a
   dependent pi binder. (Consequently extra parens cannot force the
   ascription reading there.) *)
pi_term:
  | a = app_term; ARROW; b = pi_term
    { match a with
      | Ast.Ascribe (Ast.Var x, ty) -> Ast.Pi (x, ty, b)
      | a -> Ast.Arrow (a, b) }
  | t = app_term { t }

(* application is left-associative *)
app_term:
  | f = app_term; a = atom { Ast.App (f, a) }
  | t = atom { t }

atom:
  | x = ID { Ast.Var x }
  | TYPE; i = INT { Ast.Univ i }
  | TYPE { Ast.Univ 0 }
  | LPAREN; t = term; RPAREN { t }
  | LPAREN; t = term; COLON; a = term; RPAREN { Ast.Ascribe (t, a) }
