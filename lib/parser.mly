%token <string> ID
%token <int> INT
%token FUN TYPE LPAREN RPAREN COLON ARROW DARROW EOF

%start <Ast.t> main

%%

main:
  | t = term; EOF { t }

term:
  | FUN; LPAREN; x = ID; COLON; a = term; RPAREN; DARROW; b = term
    { Ast.Lam (x, a, b) }
  | t = pi_term { t }

(* arrows are right-associative; the domain is one level tighter *)
pi_term:
  | LPAREN; x = ID; COLON; a = term; RPAREN; ARROW; b = pi_term
    { Ast.Pi (x, a, b) }
  | a = app_term; ARROW; b = pi_term { Ast.Arrow (a, b) }
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
