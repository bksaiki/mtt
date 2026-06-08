%token <string> ID
%token <int> INT
%token <int> TYPELEVEL (* a universe literal "Type n", lexed whole *)
%token FUN PI SIGMA TYPE PROP UNIT EMPTY ABSURD TIMES PLUS INL INR CASE EQ REFL J NAT SUCC NATREC COMMA FST SND CHECK EVAL CHECK_EQUAL AXIOM DEF THEOREM LPAREN RPAREN COLON ARROW DARROW EQUALS EOF

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
  | SIGMA; bs = nonempty_list(binder_group); DARROW; b = term
    { Ast.sigmas $loc bs b }
  (* a single binder may drop its parens: λ x : A ⇒ b *)
  | FUN; x = ID; COLON; a = term; DARROW; b = term
    { Ast.mk $loc (Ast.Lam (x, a, b)) }
  | PI; x = ID; COLON; a = term; DARROW; b = term
    { Ast.mk $loc (Ast.Pi (x, a, b)) }
  | SIGMA; x = ID; COLON; a = term; DARROW; b = term
    { Ast.mk $loc (Ast.Sigma (x, a, b)) }
  | t = pi_term { t }

(* arrows are right-associative; the domain is one level tighter. There is
   no dedicated pi-binder production: "(x : A)" parses as an ascription
   atom, and an ascribed *variable* directly left of an arrow is read as a
   dependent pi binder. (Consequently extra parens cannot force the
   ascription reading there.) *)
pi_term:
  | a = sum_term; ARROW; b = pi_term
    { match a.Ast.desc with
      | Ast.Ascribe (e, ty) -> (
          (* an ascribed variable spine [(x y : A)] is a pi binder group *)
          match Ast.var_spine e with
          | Some xs -> Ast.pis $loc [ (xs, ty) ] b
          | None -> Ast.mk $loc (Ast.Arrow (a, b)))
      | _ -> Ast.mk $loc (Ast.Arrow (a, b)) }
  | t = sum_term { t }

(* sums sit between arrows and products; right-associative *)
sum_term:
  | a = prod_term; PLUS; b = sum_term { Ast.mk $loc (Ast.Sum (a, b)) }
  | t = prod_term { t }

(* products bind tighter than sums, looser than application;
   right-associative *)
prod_term:
  | a = app_term; TIMES; b = prod_term { Ast.mk $loc (Ast.Prod (a, b)) }
  | t = app_term { t }

(* application is left-associative *)
app_term:
  | f = app_term; a = atom { Ast.mk $loc (Ast.App (f, a)) }
  (* the eliminator for Empty is primitive syntax: motive, then proof *)
  | ABSURD; a = atom; h = atom { Ast.mk $loc (Ast.Absurd (a, h)) }
  (* injections, and the sum recursor: motive, scrutinee, branches *)
  | INL; t = atom { Ast.mk $loc (Ast.Inl t) }
  | INR; t = atom { Ast.mk $loc (Ast.Inr t) }
  | CASE; p = atom; s = atom; u = atom; v = atom
    { Ast.mk $loc (Ast.Case (p, s, u, v)) }
  (* equality former (explicit type) and its eliminator J *)
  | EQ; a = atom; x = atom; y = atom { Ast.mk $loc (Ast.Eq (a, x, y)) }
  | J; p = atom; d = atom; pr = atom { Ast.mk $loc (Ast.J (p, d, pr)) }
  (* Nat successor and recursor *)
  | SUCC; n = atom { Ast.mk $loc (Ast.Succ n) }
  | NATREC; p = atom; z = atom; s = atom; n = atom
    { Ast.mk $loc (Ast.NatRec (p, z, s, n)) }
  | t = atom { t }

atom:
  | x = ID { Ast.mk $loc (Ast.Var x) }
  (* surface universes name sorts: Prop = Sort 0, Type i = Sort (i+1) *)
  | i = TYPELEVEL { Ast.mk $loc (Ast.Sort (i + 1)) }
  | TYPE { Ast.mk $loc (Ast.Sort 1) }
  | PROP { Ast.mk $loc (Ast.Sort 0) }
  | UNIT { Ast.mk $loc Ast.Unit }
  | EMPTY { Ast.mk $loc Ast.Empty }
  | REFL { Ast.mk $loc Ast.Refl }
  | NAT { Ast.mk $loc Ast.Nat }
  (* a decimal literal is a Nat numeral: succ (succ ... 0) *)
  | n = INT { Ast.numeral $loc n }
  (* () is the unit element, like OCaml; whitespace between the parens is
     fine since this is a grammar rule, not a lexeme *)
  | LPAREN; RPAREN { Ast.mk $loc Ast.MkUnit }
  | LPAREN; t = term; RPAREN { t }
  (* tuples are right-nested pairs *)
  | LPAREN; t = term; COMMA; ts = separated_nonempty_list(COMMA, term); RPAREN
    { let rec build = function
        | [ x ] -> x
        | x :: rest -> Ast.mk $loc (Ast.Pair (x, build rest))
        | [] -> assert false
      in
      build (t :: ts) }
  (* postfix projections bind tightest: f p.1 is f (p.1) *)
  | p = atom; FST { Ast.mk $loc (Ast.Fst p) }
  | p = atom; SND { Ast.mk $loc (Ast.Snd p) }
  | LPAREN; t = term; COLON; a = term; RPAREN
    { Ast.mk $loc (Ast.Ascribe (t, a)) }
