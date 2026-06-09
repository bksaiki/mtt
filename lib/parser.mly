%token <string> ID
%token <string> DOTID (* a named projection ".f", e.g. ".rec" *)
%token <int> INT
%token <int> TYPELEVEL (* a universe literal "Type n", lexed whole *)
%token FUN PI SIGMA TYPE PROP TIMES PLUS EQOP COMMA FST SND CHECK EVAL CHECK_EQUAL AXIOM DEF THEOREM INDUCTIVE BAR PRELUDE LPAREN RPAREN LBRACE RBRACE COLON ARROW DARROW EQUALS ATTR_OPEN ATTR_CLOSE AT MATCH WITH END EOF

%start <Ast.t> main
%start <Stmt.t> stmt
%start <Stmt.t list> file

%%

(* a standalone term (not a statement): backs Parse.term_of_string, used by
   the term-level tests/tooling that need a term with faithful locations *)
main:
  | t = term; EOF { t }

(* a single REPL line is one declaration *)
stmt:
  | s = decl; EOF { s }

(* a file is a sequence of declarations. There are no bare-term statements:
   use #check / #eval to evaluate a term — and without a statement terminator
   adjacent terms would parse as one application anyway *)
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
  (* an inductive type declaration: a parameter telescope, a result sort, and a
     bar-separated list of constructors. The parameters are explicit and in
     scope for the sort and every constructor. A type with no constructors (e.g.
     Empty) drops the [:=] entirely: [inductive Empty : Prop]. *)
  | a = ioption(attribute); INDUCTIVE; x = ID; ps = list(binder_group); COLON;
    s = term; cs = ctors_opt
    { Stmt.Inductive
        { Stmt.iname = x
        ; iparams = List.concat_map (fun (_, xs, a) -> List.map (fun y -> (y, a)) xs) ps
        ; isort = s
        ; ictors = cs
        ; iattr = a
        } }
  (* a directive (first statement only) that opts out of the auto-loaded
     standard prelude *)
  | PRELUDE { Stmt.Prelude }

(* a declaration attribute [@[name arg]], e.g. [@[notation unit]]. The name and
   argument are bare identifiers; their meaning is validated when the statement
   is run, not here. *)
attribute:
  | ATTR_OPEN; name = ID; arg = ID; ATTR_CLOSE { (name, arg) }

(* the constructors of an inductive: omitted entirely for an empty type, else
   [:=] followed by a bar-separated list (the [:=] with no constructors after it
   is also accepted) *)
ctors_opt:
  | { [] }
  | EQUALS; cs = list(ctor) { cs }

(* one constructor of an inductive: [| name : type] *)
ctor:
  | BAR; c = ID; COLON; t = term { (c, t) }

(* a binder group: one annotation shared by one or more names, explicit
   [(x y : A)] or implicit [{x y : A}] *)
binder_group:
  | LPAREN; xs = nonempty_list(ID); COLON; a = term; RPAREN
    { (Type.Explicit, xs, a) }
  | LBRACE; xs = nonempty_list(ID); COLON; a = term; RBRACE
    { (Type.Implicit, xs, a) }

term:
  | FUN; bs = nonempty_list(binder_group); DARROW; b = term
    { Ast.lams $loc bs b }
  | PI; bs = nonempty_list(binder_group); DARROW; b = term
    { Ast.pis $loc bs b }
  | SIGMA; bs = nonempty_list(binder_group); DARROW; b = term
    { Ast.sigmas $loc bs b }
  (* a single binder may drop its parens: λ x : A ⇒ b (always explicit) *)
  | FUN; x = ID; COLON; a = term; DARROW; b = term
    { Ast.mk $loc (Ast.Lam (Type.Explicit, x, a, b)) }
  | PI; x = ID; COLON; a = term; DARROW; b = term
    { Ast.mk $loc (Ast.Pi (Type.Explicit, x, a, b)) }
  | SIGMA; x = ID; COLON; a = term; DARROW; b = term
    { Ast.mk $loc (Ast.Sigma (x, a, b)) }
  (* case analysis [match e with | C x… => b … end]; the [end] terminator keeps
     nested matches unambiguous (no dangling-arm conflict) *)
  | MATCH; e = term; WITH; arms = nonempty_list(match_arm); END
    { Ast.mk $loc (Ast.Match (e, arms)) }
  | t = pi_term { t }

(* one match arm: an unqualified constructor name, its pattern variables, and a
   body. The constructor is resolved against the scrutinee's inductive. *)
match_arm:
  | BAR; c = ID; xs = list(ID); DARROW; b = term { (c, xs, b) }

(* arrows are right-associative; the domain is one level tighter. There is
   no dedicated pi-binder production: "(x : A)" parses as an ascription
   atom, and an ascribed *variable* directly left of an arrow is read as a
   dependent pi binder. (Consequently extra parens cannot force the
   ascription reading there.) *)
pi_term:
  | a = eq_term; ARROW; b = pi_term
    { match a.Ast.desc with
      | Ast.Ascribe (e, ty) -> (
          (* an ascribed variable spine [(x y : A)] is a pi binder group *)
          match Ast.var_spine e with
          | Some xs -> Ast.pis $loc [ (Type.Explicit, xs, ty) ] b
          | None -> Ast.mk $loc (Ast.Arrow (a, b)))
      | _ -> Ast.mk $loc (Ast.Arrow (a, b)) }
  (* an implicit binder group left of an arrow: [{x y : A} -> B]. (Explicit
     [(x : A) -> B] rides the ascription path above; braces have no ascription
     form, so they need their own production.) *)
  | LBRACE; xs = nonempty_list(ID); COLON; a = term; RBRACE; ARROW; b = pi_term
    { Ast.pis $loc [ (Type.Implicit, xs, a) ] b }
  | t = eq_term { t }

(* equality infix sits between arrows and sums; non-associative, and the type
   argument is inferred (so [x = y], not [Eq A x y]) *)
eq_term:
  | x = sum_term; EQOP; y = sum_term { Ast.mk $loc (Ast.EqInfix (x, y)) }
  | t = sum_term { t }

(* sums sit between equalities and products; right-associative *)
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
  | t = atom { t }

(* an atom is a projection chain, optionally prefixed by [@]. Splitting [@] off
   from the projection level ([proj_atom]) keeps it unambiguous: [@] always takes
   a whole projection chain, so [@T.rec] is [@(T.rec)] — no shift/reduce against
   the postfix projections. *)
atom:
  | a = proj_atom { a }
  (* [@f] makes every argument explicit (no implicit insertion for this head) *)
  | AT; a = proj_atom { Ast.mk $loc (Ast.At a) }

(* postfix projections bind tightest: [f p.1] is [f (p.1)] *)
proj_atom:
  | p = proj_atom; FST { Ast.mk $loc (Ast.Fst p) }
  | p = proj_atom; SND { Ast.mk $loc (Ast.Snd p) }
  (* a named projection: the recursor [Nat.rec], or a record field [p.fst] *)
  | e = proj_atom; f = DOTID { Ast.mk $loc (Ast.Field (e, f)) }
  | a = base_atom { a }

base_atom:
  (* a bare [_] is an elaboration hole; any other identifier is a variable *)
  | x = ID
    { Ast.mk $loc (if String.equal x "_" then Ast.Hole else Ast.Var x) }
  (* surface universes name sorts: Prop = Sort 0, Type i = Sort (i+1) *)
  | i = TYPELEVEL { Ast.mk $loc (Ast.Sort (i + 1)) }
  | TYPE { Ast.mk $loc (Ast.Sort 1) }
  | PROP { Ast.mk $loc (Ast.Sort 0) }
  (* a decimal literal; the elaborator expands it to the registered nat's
     succ/zero chain *)
  | n = INT { Ast.mk $loc (Ast.Numeral n) }
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
  | LPAREN; t = term; COLON; a = term; RPAREN
    { Ast.mk $loc (Ast.Ascribe (t, a)) }
