open Mtt

(* the standard prelude, loaded once: sessions start from it, as the REPL and
   file runner do, so the standard types (Unit, Empty, ...) are in scope *)
let prelude = Prelude.load Stmt.initial

(* feed lines through a toplevel session, printing each response *)
let session lines =
  let step sess line =
    match Stmt.run sess (Parse.stmt_of_string line) with
    | sess, message ->
        Option.iter print_endline message;
        sess
    | exception Ast.Unbound_variable (loc, x) ->
        Printf.printf "%s: unbound variable: %s\n" (Loc.to_string loc) x;
        sess
    | exception Error.Type_error frags ->
        Printf.printf "type error: %s\n"
          (Notation.render_error sess.notation frags);
        sess
  in
  ignore (List.fold_left step prelude lines)

let%expect_test "axioms postulate stuck constants" =
  session
    [ "axiom N : Type"
    ; "axiom zero : N"
    ; "axiom suc : N -> N"
    ; "#check suc (suc zero)"
    ];
  [%expect {| suc (suc zero) : N |}]

let%expect_test "defs unfold (delta), theorems do not (opaque)" =
  session
    [ "axiom N : Type"
    ; "axiom zero : N"
    ; "def d : N := zero"
    ; "theorem t : N := zero"
    ; "#check d"
    ; "#check t"
    ];
  [%expect {|
    zero : N
    t : N
    |}]

let%expect_test "def with inferred type, used at two types" =
  session
    [ "def id := fun (A : Type) => fun (x : A) => x"
    ; "axiom N : N"
    ; "axiom N : Type"
    ; "axiom zero : N"
    ; "#check id N zero"
    ; "#check id (N -> N) (id N)"
    ];
  [%expect
    {|
    1:11: unbound variable: N
    zero : N
    fun (x : N) => x : N -> N
    |}]

let%expect_test "a theorem and its use" =
  session
    [ "axiom P : Type"
    ; "axiom Q : Type"
    ; "axiom f : P -> Q"
    ; "axiom p : P"
    ; "theorem q : Q := f p"
    ; "theorem bad : Q := p"
    ];
  [%expect {| type error: this term has type P but Q was expected |}]

let%expect_test "declared names are in scope for later annotations" =
  session
    [ "axiom N : Type"
    ; "def arrow : Type := N -> N"
    ; "axiom g : arrow"
    ; "#check g"
    ];
  [%expect {| g : N -> N |}]

let%expect_test "#eval reports just the normal form" =
  session
    [ "axiom N : Type"
    ; "axiom zero : N"
    ; "def two := fun (f : N -> N) => fun (x : N) => f (f x)"
    ; "def add := fun (m : (N -> N) -> N -> N) => fun (n : (N -> N) -> N -> N) \
       => fun (f : N -> N) => fun (x : N) => m f (n f x)"
    ; "#eval add two two"
    ; "#eval Type Type"
    ];
  [%expect
    {|
    fun (f : N -> N) => fun (x : N) => f (f (f (f x)))
    type error: expected a function, but Type has type Type 1
    |}]

let%expect_test "#check_equal succeeds silently and fails loudly" =
  session
    [ "axiom N : Type"
    ; "axiom zero : N"
    ; "#check_equal zero zero"
    ; "#check_equal ((fun (x : N) => x) zero) zero"
    ; "#check_equal zero N"
    ];
  [%expect {| type error: this term has type Type but N was expected |}]

let%expect_test "#check with ascription, and #check_equal" =
  session
    [ "axiom N : Type"
    ; "axiom zero : N"
    ; "#check (zero : N)"
    ; "#check ((fun (A : Type) => fun (x : A) => x) : (B : Type) -> B -> B)"
    ; "#check (zero : Type)"
    ; "#check_equal (zero : N) zero"
    ];
  [%expect
    {|
    zero : N
    fun (A : Type) => fun (x : A) => x : (B : Type) -> B -> B
    type error: this term has type N but Type was expected
    |}]

let%expect_test "definitions accept := and unicode binders" =
  session
    [ "axiom N : Type"
    ; "axiom zero : N"
    ; "def id : Π (A : Type) ⇒ A → A := λ (A : Type) ⇒ λ (x : A) ⇒ x"
    ; "#check_equal (id N zero) zero"
    ; "#check id"
    ];
  [%expect {| fun (A : Type) => fun (x : A) => x : (A : Type) -> A -> A |}]

let%expect_test "declaration telescopes" =
  session
    [ "axiom N : Type"
    ; "axiom zero : N"
    ; "def const (A B : Type) (x : A) (y : B) : A := x"
    ; "#check const"
    ; "#check_equal (const N N zero zero) zero"
    ; "axiom plus (m n : N) : N"
    ; "#check plus"
    ; "theorem plus_self (n : N) : N := plus n n"
    ; "def bad (A : Type) (x : A) : A := A"
    ];
  [%expect
    {|
    fun (A : Type) => fun (B : Type) => fun (x : A) => fun (y : B) => x : (A : Type) -> (B : Type) -> A -> B -> A
    plus : N -> N -> N
    type error: this term has type Type but A was expected
    |}]

let%expect_test "def return annotations are optional, with telescopes" =
  session
    [ "axiom N : Type"
    ; "def twice (f : N -> N) (n : N) := f (f n)"
    ; "#check twice"
    ; "def Bool := Π (A : Type) ⇒ A → A → A"
    ; "#check Bool"
    ];
  [%expect
    {|
    fun (f : N -> N) => fun (n : N) => f (f n) : (N -> N) -> N -> N
    (A : Type) -> A -> A -> A : Type 1
    |}]

let%expect_test "proof irrelevance" =
  session
    [ "axiom p : Prop"
    ; "axiom h1 : p"
    ; "axiom h2 : p"
    ; (* any two proofs of the same proposition are equal *)
      "#check_equal h1 h2"
    ; (* ... including inside neutral spines: P h1 and P h2 are the same type,
         so coercion between them checks *)
      "axiom P : p -> Type"
    ; "def coerce (y : P h1) : P h2 := y"
    ; (* proofs of different propositions are not equated *)
      "axiom q : Prop"
    ; "#check_equal p q"
    ];
  [%expect {| type error: #check_equal failed: p is not convertible with q |}]

let%expect_test "eta for Unit: every element is definitionally ()" =
  session
    [ "axiom u : Unit"
    ; "#check_equal u ()"
    ; (* by Pi-eta then Unit-eta, all functions into Unit are equal *)
      "axiom f : Unit -> Unit"
    ; "#check_equal f (λ x : Unit ⇒ ())"
    ; (* but Unit is not equal to other types *)
      "#check_equal Unit Prop"
    ];
  [%expect
    {| type error: #check_equal failed: Unit is not convertible with Prop |}]

let%expect_test "Empty: irrelevance and stuck absurd" =
  (* Empty and absurd come from the prelude *)
  session
    [ "axiom N : Type"
    ; "axiom h1 : Empty"
    ; "axiom h2 : Empty"
    ; (* all proofs of Empty are equal (it is a Prop) *)
      "#check_equal h1 h2"
    ; (* and so stuck eliminations of them are equal too *)
      "#check_equal (absurd N h1) (absurd N h2)"
    ; (* native negation, and double-negation introduction *)
      "def negate (A : Prop) := A → Empty"
    ; "#check negate"
    ; "axiom p : Prop"
    ; "theorem dni (x : p) : negate (negate p) := λ k : negate p ⇒ k x"
    ];
  [%expect {| fun (A : Prop) => A -> Empty : Prop -> Prop |}]

(* a hole [_] elaborates to a metavariable that unification solves from the
   surrounding term; an unsolvable one is rejected. *)
let%expect_test "holes: solved by unification, rejected when unsolvable" =
  session
    [ (* the type argument is recovered from the value argument *)
      "#check id _ 0"
    ; "#eval id _ 0"
    ; "#check_equal (id _ 0) 0"
    ; (* solved from a local variable, under binders: the solution is read back
         as a reuse-safe de Bruijn index, so the def is usable at other types *)
      "def appId (A : Type) (x : A) : A := id _ x"
    ; "#check appId"
    ; "#check_equal (appId Nat 0) 0"
    ; (* nothing determines the hole: rejected *)
      "#check (_ : Nat)"
    ];
  [%expect
    {|
    0 : Nat
    0
    fun (A : Type) => fun (x : A) => x : (A : Type) -> A -> A
    type error: could not infer a hole (_); add a type annotation
    |}]

(* implicit arguments ([{x : A}]): the elaborator inserts a fresh metavariable
   for each leading implicit binder when an explicit argument follows, and
   solves it by unifying that argument's type. The prelude's equality lemmas
   ([cong]/[symm]/[trans]) take their type and endpoint arguments implicitly. *)
let%expect_test "implicit arguments: insertion and inference" =
  session
    [ (* an implicit type argument, inferred from the value argument *)
      "def myid {A : Type} (x : A) : A := x"
    ; "#check myid 0"
    ; (* a bare implicit-arg function is not applied, so nothing is inserted:
         its full implicit type prints with braces *)
      "#check myid"
    ; (* the prelude's lemmas now take type/endpoints implicitly *)
      "theorem e : Eq Nat 1 1 := rfl"
    ; "#check symm e"
    ; "#check cong (fun n : Nat => Nat.succ n) e"
    ; (* a standalone implicit function type round-trips through the printer *)
      "axiom dup : {A : Type} -> A -> A"
    ; "#check dup"
    ];
  [%expect
    {|
    0 : Nat
    fun {A : Type} => fun (x : A) => x : {A : Type} -> A -> A
    Eq.rec Nat 1 (fun (z : Nat) => fun (q : 1 = z) => z = 1) rfl 1 e : 1 = 1
    Eq.rec Nat 1 (fun (z : Nat) => fun (q : 1 = z) => 2 = Nat.succ z) rfl 1 e : 2 = 2
    dup : {A : Type} -> A -> A
    |}]

(* a hole [_] in a (non-indexed) recursor's motive position, in checking mode,
   is inferred by abstracting the major premise out of the goal. (An indexed
   recursor like [Eq.rec] abstracts the indices too, which is not yet done, so
   its motive must be written out — see the equality lemmas below.) *)
let%expect_test "motive inference for recursors" =
  session
    [ (* abstract the major [n] out of the goal [add n 0 = n], recovering the
         motive [fun m => add m 0 = m] *)
      "theorem azr (n : Nat) : add n 0 = n :=\n\
      \   Nat.rec _ rfl (fun (k : Nat) (ih : add k 0 = k) => cong Nat.succ ih) \
       n"
    ; "#check azr 3"
    ; (* a non-dependent goal: abstraction finds no occurrence, giving a
         constant motive (ordinary, non-dependent recursion) *)
      "def dbl (n : Nat) : Nat := Nat.rec _ 0 (fun (k s : Nat) => Nat.succ \
       (Nat.succ s)) n"
    ; "#eval dbl 3"
    ; (* nothing determines a hole motive without a goal: rejected *)
      "#check (fun (n : Nat) => Nat.rec _ 0 (fun (k s : Nat) => s) n)"
    ];
  [%expect
    {|
    azr 3 : 3 = 3
    6
    type error: cannot infer the type of a hole _; use it where its type is determined
    |}]

(* a recursor's parameters and indices may be written [_]: they are recovered
   from the major premise's type [T params indices]. (The motive is still
   explicit for an indexed recursor.) *)
let%expect_test "recursor parameters and indices recovered from the major" =
  session
    [ (* Eq.rec's A, x (params) and y (index) recovered from [p : x = y] *)
      "def symm (A : Type) (x y : A) (p : x = y) : y = x :="
      ^ " Eq.rec _ _ (fun (z : A) (q : x = z) => z = x) rfl _ p"
    ; "#check_equal (symm Nat 0 0 rfl) rfl"
    ; (* an indexed family: Vec.rec's parameter [A] and length index recovered
         from the vector *)
      "inductive Vec (A : Type) : Nat -> Type := | vnil : Vec A 0 | vcons : (n \
       : Nat) -> A -> Vec A n -> Vec A (Nat.succ n)"
    ; "def v : Vec Nat 2 := Vec.vcons Nat 1 7 (Vec.vcons Nat 0 5 (Vec.vnil \
       Nat))"
    ; "def len (n : Nat) (xs : Vec Nat n) : Nat := Vec.rec _ (fun (m : Nat) (w \
       : Vec Nat m) => Nat) 0 (fun (k : Nat) (a : Nat) (w : Vec Nat k) (ih : \
       Nat) => Nat.succ ih) _ xs"
    ; "#eval len 2 v"
    ; (* the major's type isn't the right inductive: recovery fails clearly *)
      "axiom n : Nat"
    ; "#check Eq.rec _ _ (fun (z : Nat) (q : Nat) => Nat) 0 _ n"
    ];
  [%expect
    {|
    2
    type error: cannot recover Eq's parameters and indices: the major premise is not Eq applied to arguments
    |}]

(* Σ is the prelude record [Sigma]: pairs check against it (recovering the
   parameters), projections are the generic record projections, and η comes from
   the record rule. Fixed at Type, so the old "a pair of props is an irrelevant
   Prop" no longer holds (it awaits universe polymorphism). *)
let%expect_test "sigma: beta, eta, dependent pairs" =
  session
    [ "axiom N : Type"
    ; "axiom zero : N"
    ; (* beta: projecting a literal pair *)
      "def p : N × N := (zero, zero)"
    ; "#check_equal p.1 zero"
    ; (* a dependent pair, recovered by checking against the Σ; its second
         component's type mentions the first *)
      "def package : Σ (n : Nat) ⇒ Eq Nat n n := (0, rfl)"
    ; "#check package.2"
    ; (* eta (surjective pairing) on a neutral pair *)
      "axiom q : N × N"
    ; "#check_equal q (q.1, q.2)"
    ; (* eta and unit-eta compose: any two pairs of units are equal *)
      "axiom r : Unit × Unit"
    ; "#check_equal r ((), ())"
    ];
  [%expect {| rfl : 0 = 0 |}]

(* the binary sum is the prelude inductive [Sum]: [+] is notation, the
   injections and eliminator are the qualified [Sum.inl]/[Sum.inr]/[Sum.rec].
   Fixed at Type, so the old proof-irrelevant disjunction of Props is gone. *)
let%expect_test "sums: iota, stuck recursions" =
  session
    [ "axiom A : Type"
    ; "axiom B : Type"
    ; "axiom a : A"
    ; "axiom b : B"
    ; "def swap (s : A + B) : B + A :="
      ^ " Sum.rec A B (λ x : A + B ⇒ B + A) (λ x : A ⇒ (Sum.inr x : B + A)) (λ \
         y : B ⇒ (Sum.inl y : B + A)) s"
    ; (* ι-reduction picks each branch *)
      "#check_equal (swap (Sum.inl a)) (Sum.inr a)"
    ; "#check_equal (swap (Sum.inr b)) (Sum.inl b)"
    ; (* a stuck recursion is equal to itself, and not to a sibling with other
         branches *)
      "axiom s : A + B"
    ; "#check swap s"
    ; "#check_equal (swap s) (swap s)"
    ; (* same type, different branches: conv compares the stuck branches *)
      "axiom t : A + A"
    ; "def same (s : A + A) : A + A :="
      ^ " Sum.rec A A (λ x : A + A ⇒ A + A) (λ x : A ⇒ (Sum.inl x : A + A)) (λ \
         y : A ⇒ (Sum.inr y : A + A)) s"
    ; "def cross (s : A + A) : A + A :="
      ^ " Sum.rec A A (λ x : A + A ⇒ A + A) (λ x : A ⇒ (Sum.inr x : A + A)) (λ \
         y : A ⇒ (Sum.inl y : A + A)) s"
    ; "#check_equal (same t) (same t)"
    ; "#check_equal (same t) (cross t)"
    ; (* no η for sums: a stuck value is not its recursion-rebuilt self *)
      "#check_equal (same t) t"
    ];
  [%expect
    {|
    Sum.rec A B (fun (x : A + B) => B + A) (fun (x : A) => Sum.inr B A x)
    (fun (y : B) => Sum.inl B A y) s : B + A
    type error: #check_equal failed: Sum.rec A A (fun (x : A + A) => A + A) (fun (x : A) => Sum.inl A A x)
    (fun (y : A) => Sum.inr A A y) t is not convertible with Sum.rec A A (fun (x : A + A) => A + A) (fun (x : A) => Sum.inr A A x)
    (fun (y : A) => Sum.inl A A y) t
    type error: #check_equal failed: Sum.rec A A (fun (x : A + A) => A + A) (fun (x : A) => Sum.inl A A x)
    (fun (y : A) => Sum.inr A A y) t is not convertible with t
    |}]

let%expect_test "equality: Eq.rec lemmas, iota, stuck recursion, UIP" =
  session
    [ "axiom A : Type"
    ; "axiom B : Type"
    ; "axiom a : A"
    ; "axiom b : A"
    ; (* the standard lemmas, each one Eq.rec at a different motive *)
      "def symm (x y : A) (p : Eq A x y) : Eq A y x :="
      ^ " Eq.rec A x (λ z : A ⇒ λ q : Eq A x z ⇒ Eq A z x) rfl y p"
    ; "def trans (x y z : A) (p : Eq A x y) (q : Eq A y z) : Eq A x z :="
      ^ " Eq.rec A y (λ w : A ⇒ λ r : Eq A y w ⇒ Eq A x w) p z q"
    ; "def cong (f : A → B) (x y : A) (p : Eq A x y) : Eq B (f x) (f y) :="
      ^ " Eq.rec A x (λ z : A ⇒ λ q : Eq A x z ⇒ Eq B (f x) (f z)) rfl y p"
    ; (* subst is large elimination: the motive lands in Type *)
      "def subst (P : A → Type) (x y : A) (p : Eq A x y) (h : P x) : P y :="
      ^ " Eq.rec A x (λ z : A ⇒ λ q : Eq A x z ⇒ P z) h y p"
    ; "#check symm"
    ; "#check subst"
    ; (* ι: transport along rfl is the identity, definitionally *)
      "axiom P : A → Type"
    ; "axiom h : P a"
    ; "#check_equal (subst P a a rfl h) h"
    ; (* a stuck recursion (proof is a variable) is a neutral, equal to
         itself *)
      "axiom q : Eq A a b"
    ; "#check symm a b q"
    ; "#check_equal (symm a b q) (symm a b q)"
    ; (* UIP for free: any two proofs of the same equation are equal *)
      "axiom q2 : Eq A a b"
    ; "#check_equal q q2"
    ];
  [%expect
    {|
    fun (x : A) =>
    fun (y : A) =>
    fun (p : x = y) =>
    Eq.rec A x (fun (z : A) => fun (q : x = z) => z = x) rfl y p : (x : A) -> (y : A) -> x = y -> y = x
    fun (P : A -> Type) =>
    fun (x : A) =>
    fun (y : A) =>
    fun (p : x = y) =>
    fun (h : P x) => Eq.rec A x (fun (z : A) => fun (q : x = z) => P z) h y p : (P : A -> Type) -> (x : A) -> (y : A) -> x = y -> P x -> P y
    Eq.rec A a (fun (z : A) => fun (q' : a = z) => z = a) rfl b q : b = a
    |}]

let%expect_test "constructor parameters may be omitted in checking position" =
  session
    [ "inductive Box (A : Type) : Type := | wrap : A -> Box A"
    ; (* checked against [Box A], so the parameter [A] is recovered from the
         expected type and the constructor application drops it *)
      "def b1 (A : Type) (a : A) : Box A := Box.wrap a"
    ; "#check b1"
    ; (* the elaborated core is identical to spelling the parameter out *)
      "def b2 (A : Type) (a : A) : Box A := Box.wrap A a"
    ; "#check_equal b1 b2"
    ; (* omission also reaches into a lambda body checked against a Pi ... *)
      "def b3 (A : Type) : A -> Box A := fun (a : A) => Box.wrap a"
    ; (* ... and into a function argument checked against its domain *)
      "def use (A : Type) (x : Box A) : Box A := x"
    ; "def b4 (A : Type) (a : A) : Box A := use A (Box.wrap a)"
    ; "#check_equal b3 (fun (A : Type) => fun (a : A) => b4 A a)"
    ; (* a second parameter is recovered just the same *)
      "inductive Prod2 (A B : Type) : Type := | mk : A -> B -> Prod2 A B"
    ; "def p (A B : Type) (a : A) (b : B) : Prod2 A B := Prod2.mk a b"
    ; "#check p"
    ; (* inference position is unchanged: the parameters stay explicit *)
      "#check Prod2.mk"
    ];
  [%expect
    {|
    fun (A : Type) => fun (a : A) => Box.wrap A a : (A : Type) -> A -> Box A
    fun (A : Type) =>
    fun (B : Type) => fun (a : A) => fun (b : B) => Prod2.mk A B a b : (A : Type) -> (B : Type) -> A -> B -> Prod2 A B
    Prod2.mk : (A : Type) -> (B : Type) -> A -> B -> Prod2 A B
    |}]

(* the surface-inference conveniences that sit above the kernel: expected-type
   implicit insertion, the [@f] escape, named field projections, and
   inference-position constructor intros. *)
let%expect_test "surface inference: implicits, @, named projections, intros" =
  session
    [ "axiom A : Type"
    ; "axiom a : A"
    ; "axiom b : A"
    ; "axiom p : a = b"
    ; (* a bare fully-implicit term ([rfl : {A}{x} -> x = x]) checked against a
         concrete goal inserts and solves its implicits *)
      "def e : a = a := rfl"
    ; "#check e"
    ; (* [@f] passes the normally-implicit arguments explicitly, agreeing with
         the insertion that [symm p] gets *)
      "#check_equal (symm p) (@symm A a b p)"
    ; (* named field projections on a record, alongside the positional ones *)
      "def pr : Σ (n : Nat) ⇒ Eq Nat n n := (0, rfl)"
    ; "#check_equal pr.fst pr.1"
    ; "#check pr.snd"
    ; (* inference position: the parameter is solved from the field argument,
         with no expected type to recover it from *)
      "inductive Box (T : Type) : Type := | wrap : T -> Box T"
    ; "#check Box.wrap a"
    ];
  [%expect {|
    rfl : a = a
    rfl : 0 = 0
    Box.wrap A a : Box A
    |}]

(* [match] is flat case-analysis sugar: it desugars to the inductive's recursor
   with the motive recovered from the expected type, one branch per constructor
   (unqualified constructor names, binding the fields), the recursive
   constructors' induction hypotheses bound but ignored. *)
let%expect_test "match: case analysis desugars to the recursor" =
  session
    [ "axiom A : Type"
    ; "axiom B : Type"
    ; "axiom a : A"
    ; "axiom b : B"
    ; (* case analysis on a sum; the result injections' parameters are
         recovered, and [#check] shows the desugared [Sum.rec] *)
      "def swap (s : A + B) : B + A := match s with | inl x => Sum.inr B A x | \
       inr y => Sum.inl B A y end"
    ; "#check swap"
    ; (* the desugaring is *exactly* the hand-written recursor *)
      "def swap2 (s : A + B) : B + A := Sum.rec A B (fun x : A + B => B + A) \
       (fun x : A => Sum.inr B A x) (fun y : B => Sum.inl B A y) s"
    ; "#check_equal swap swap2"
    ; (* ι-reduction fires on a constructor scrutinee *)
      "#check_equal (swap (Sum.inl a)) (Sum.inr a)"
    ; (* on a recursive type the branch binds the field, ignoring the IH *)
      "def pred (n : Nat) : Nat := match n with | zero => 0 | succ k => k end"
    ; "#eval pred 3"
    ; "#eval pred 0"
    ];
  [%expect
    {|
    fun (s : A + B) =>
    Sum.rec A B (fun (x : A + B) => B + A) (fun (x : A) => Sum.inr B A x)
    (fun (y : B) => Sum.inl B A y) s : A + B -> B + A
    2
    0
    |}]

let%expect_test "match: coverage and well-formedness are checked" =
  let case s = session [ "axiom A : Type"; "axiom a : A"; s ] in
  (* a missing branch *)
  case "def f (s : A + A) : A := match s with | inl x => x end";
  [%expect {| type error: match is missing a branch for Sum.inr |}];
  (* an unknown constructor *)
  case "def f (n : Nat) : Nat := match n with | zero => 0 | bogus k => k end";
  [%expect {| type error: bogus is not a constructor of Nat |}];
  (* wrong pattern arity *)
  case "def f (n : Nat) : Nat := match n with | zero => 0 | succ => 0 end";
  [%expect
    {| type error: the pattern for Nat.succ binds 0 variable(s) but the constructor has 1 field(s) |}];
  (* the result type must be known (no inference-mode match) *)
  case "def f (n : Nat) := match n with | zero => 0 | succ j => j end";
  [%expect
    {| type error: cannot infer the result type of a match; annotate it (e.g. (match … end : T)) |}]

(* a [_] in a field position binds that field anonymously; a [| _ => b] branch
   is a catch-all covering every unlisted constructor *)
let%expect_test "match: wildcard fields and a catch-all branch" =
  session
    [ "inductive RGB : Type := | red : RGB | green : RGB | blue : RGB"
    ; (* catch-all covers green and blue *)
      "def isRed (c : RGB) : Nat := match c with | red => 1 | _ => 0 end"
    ; "#eval isRed RGB.red"
    ; "#eval isRed RGB.blue"
    ; (* a wildcard field pattern, and the catch-all desugars to the same core
         as the explicit recursor *)
      "def isZero (n : Nat) : Nat := match n with | zero => 1 | succ _ => 0 end"
    ; "def isZero2 (n : Nat) : Nat := match n with | zero => 1 | _ => 0 end"
    ; "#check_equal isZero isZero2"
    ; "#eval isZero 4"
    ];
  [%expect {|
    1
    0
    0
    |}]

let%expect_test "match: catch-all must be last and bind nothing" =
  let case s = session [ s ] in
  case "def f (n : Nat) : Nat := match n with | _ => 0 | zero => 1 end";
  [%expect {| type error: a catch-all branch | _ => … must come last |}];
  case "def f (n : Nat) : Nat := match n with | zero => 0 | _ x => x end";
  [%expect {| type error: a catch-all branch | _ => … cannot bind variables |}]

let%expect_test "Nat: computation by recursion, and induction" =
  session
    [ "def add (m n : Nat) : Nat :="
      ^ " Nat.rec (λ x : Nat ⇒ Nat) n (λ k : Nat ⇒ λ ih : Nat ⇒ Nat.succ ih) m"
    ; "def mul (m n : Nat) : Nat :="
      ^ " Nat.rec (λ x : Nat ⇒ Nat) 0 (λ k : Nat ⇒ λ ih : Nat ⇒ add n ih) m"
    ; (* ι-reduction computes closed numerals *)
      "#eval add 2 3"
    ; "#eval mul 2 3"
    ; "#check_equal (add 2 3) 5"
    ; (* add zero on the left reduces definitionally; on the right it is stuck,
         so 0 + n = n holds by computation but n + 0 = n needs induction *)
      "def cong (A B : Type) (f : A → B) (x y : A) (p : Eq A x y)"
      ^ " : Eq B (f x) (f y) :="
      ^ " Eq.rec A x (λ z : A ⇒ λ q : Eq A x z ⇒ Eq B (f x) (f z)) rfl y p"
    ; "theorem add_zero (n : Nat) : Eq Nat (add n 0) n :="
      ^ " Nat.rec (λ m : Nat ⇒ Eq Nat (add m 0) m) rfl"
      ^ " (λ k : Nat ⇒ λ ih : Eq Nat (add k 0) k ⇒"
      ^ " cong Nat Nat (λ m : Nat ⇒ Nat.succ m) (add k 0) k ih) n"
    ; "#check add_zero"
    ];
  [%expect
    {|
    5
    6
    add_zero : (n : Nat) ->
    Nat.rec (fun (x : Nat) => Nat) 0
    (fun (k : Nat) => fun (ih : Nat) => Nat.succ ih) n = n
    |}]

(* indexed inductive families: a constructor result pins an index ([Vec A 0],
   [Vec A (succ n)]), the recursor's motive abstracts over the index, and the
   checker tracks the index through application. *)
let%expect_test "indexed families: Vec, its recursor, and index enforcement" =
  session
    [ "inductive Vec (A : Type) : Nat -> Type := | nil : Vec A 0 | cons : (n : \
       Nat) -> A -> Vec A n -> Vec A (Nat.succ n)"
    ; "#check Vec"
    ; "#check Vec.cons"
    ; "def v : Vec Nat 2 := Vec.cons Nat 1 7 (Vec.cons Nat 0 5 (Vec.nil Nat))"
    ; "#check v"
    ; (* length by recursion — ι must recover each tail's index *)
      "def len (A : Type) (n : Nat) (xs : Vec A n) : Nat := Vec.rec A (fun (m \
       : Nat) (w : Vec A m) => Nat) 0 (fun (k : Nat) (x : A) (w : Vec A k) (ih \
       : Nat) => Nat.succ ih) n xs"
    ; "#eval len Nat 2 v"
    ; (* the index is enforced: a Vec Nat 2 is not a Vec Nat 3 *)
      "def bad : Vec Nat 3 := v"
    ];
  [%expect
    {|
    Vec : Type -> Nat -> Type
    Vec.cons : (A : Type) -> (n : Nat) -> A -> Vec A n -> Vec A (Nat.succ n)
    Vec.cons Nat 1 7 (Vec.cons Nat 0 5 (Vec.nil Nat)) : Vec Nat 2
    2
    type error: this term has type Vec Nat 2 but Vec Nat 3 was expected
    |}]

(* universe-polymorphic inductives can be *declared* with auto-bound universe
   parameters (free [Sort u] variables) and [Sort u]/[Sort (max u v)]; the
   kernel validates the polymorphic declaration. (Using them at inferred levels
   lands with use-site level inference.) *)
let%expect_test "polymorphic inductive declarations are accepted" =
  session
    [ "inductive Box (A : Sort u) : Sort u := | wrap : A -> Box A"
    ; "inductive Pair (A : Sort u) (B : Sort v) : Sort (max u v) := | mk : A \
       -> B -> Pair A B"
    ];
  [%expect {| |}]

(* a polymorphic former applied to arguments infers its level arguments from the
   argument sorts — so the same inductive forms at Type and at Prop (no
   cumulativity needed). *)
let%expect_test "polymorphic former: level arguments inferred per use" =
  session
    [ "inductive Box (A : Sort u) : Sort u := | wrap : A -> Box A"
    ; "axiom N : Type"
    ; "axiom p : Prop"
    ; "#check Box N"
    ; "#check Box p"
    ; "inductive Pair (A : Sort u) (B : Sort v) : Sort (max u v) := | mk : A \
       -> B -> Pair A B"
    ; "#check Pair N p"
    ];
  [%expect {|
    Box N : Type
    Box p : Prop
    Pair N p : Type
    |}]
