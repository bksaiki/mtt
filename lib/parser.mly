%token <string> ID
%token <int> INT
%token FUN PI TYPE PROP UNIT TT CHECK EVAL CHECK_EQUAL AXIOM DEF THEOREM LPAREN RPAREN COLON ARROW DARROW EQUALS EOF

%start <Ast.t> main
%start <Stmt.t> stmt
%start <Stmt.t list> file

%%

main:
  | t = term; EOF { t }

(* a single REPL line: a declaration, or a bare term *)
stmt:
  | s = decl; EOF { s }
  | t = term; EOF { { Stmt.loc = $loc; desc = Stmt.Expr t } }

(* a file is a sequence of declarations; bare terms are REPL-only, since
   without a statement terminator adjacent terms would parse as one
   application *)
file:
  | ss = list(decl); EOF { ss }

(* declarations take parameter telescopes: [def f (A : Type) (x y : A) : A]
   means [def f : (A : Type) -> (x : A) -> (y : A) -> A] with a body wrapped
   in the matching lambdas *)
decl:
  | d = decl_desc { { Stmt.loc = $loc; desc = d } }

decl_desc:
  | CHECK; t = term { Stmt.Check t }
  | EVAL; t = term { Stmt.Eval t }
  | AXIOM; x = ID; bs = list(binder_group); COLON; a = term
    { Stmt.Axiom (x, Ast.pis $loc bs a) }
  | DEF; x = ID; bs = list(binder_group); COLON; a = term; EQUALS; t = term
    { Stmt.Def (x, Some (Ast.pis $loc bs a), Ast.lams $loc bs t) }
  | DEF; x = ID; bs = list(binder_group); EQUALS; t = term
    { Stmt.Def (x, None, Ast.lams $loc bs t) }
  | THEOREM; x = ID; bs = list(binder_group); COLON; a = term; EQUALS; t = term
    { Stmt.Theorem (x, Ast.pis $loc bs a, Ast.lams $loc bs t) }
  | CHECK_EQUAL; t = atom; u = atom { Stmt.CheckEqual (t, u) }

(* a binder group: one annotation shared by one or more names *)
binder_group:
  | LPAREN; xs = nonempty_list(ID); COLON; a = term; RPAREN { (xs, a) }

term:
  | FUN; bs = nonempty_list(binder_group); DARROW; b = term
    { Ast.lams $loc bs b }
  | PI; bs = nonempty_list(binder_group); DARROW; b = term
    { Ast.pis $loc bs b }
  (* a single binder may drop its parens: λ x : A ⇒ b *)
  | FUN; x = ID; COLON; a = term; DARROW; b = term
    { Ast.mk $loc (Ast.Lam (x, a, b)) }
  | PI; x = ID; COLON; a = term; DARROW; b = term
    { Ast.mk $loc (Ast.Pi (x, a, b)) }
  | t = pi_term { t }

(* arrows are right-associative; the domain is one level tighter. There is
   no dedicated pi-binder production: "(x : A)" parses as an ascription
   atom, and an ascribed *variable* directly left of an arrow is read as a
   dependent pi binder. (Consequently extra parens cannot force the
   ascription reading there.) *)
pi_term:
  | a = app_term; ARROW; b = pi_term
    { match a.Ast.desc with
      | Ast.Ascribe (e, ty) -> (
          (* an ascribed variable spine [(x y : A)] is a pi binder group *)
          match Ast.var_spine e with
          | Some xs -> Ast.pis $loc [ (xs, ty) ] b
          | None -> Ast.mk $loc (Ast.Arrow (a, b)))
      | _ -> Ast.mk $loc (Ast.Arrow (a, b)) }
  | t = app_term { t }

(* application is left-associative *)
app_term:
  | f = app_term; a = atom { Ast.mk $loc (Ast.App (f, a)) }
  | t = atom { t }

atom:
  | x = ID { Ast.mk $loc (Ast.Var x) }
  (* surface universes name sorts: Prop = Sort 0, Type i = Sort (i+1) *)
  | TYPE; i = INT { Ast.mk $loc (Ast.Sort (i + 1)) }
  | TYPE { Ast.mk $loc (Ast.Sort 1) }
  | PROP { Ast.mk $loc (Ast.Sort 0) }
  | UNIT { Ast.mk $loc Ast.Unit }
  | TT { Ast.mk $loc Ast.Tt }
  | LPAREN; t = term; RPAREN { t }
  | LPAREN; t = term; COLON; a = term; RPAREN
    { Ast.mk $loc (Ast.Ascribe (t, a)) }
