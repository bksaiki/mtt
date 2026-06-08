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
    ; "def d : N = zero"
    ; "theorem t : N = zero"
    ; "#check d"
    ; "#check t"
    ];
  [%expect {|
    zero : N
    t : N
    |}]

let%expect_test "def with inferred type, used at two types" =
  session
    [ "def id = fun (A : Type) => fun (x : A) => x"
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
    ; "theorem q : Q = f p"
    ; "theorem bad : Q = p"
    ];
  [%expect {| type error: this term has type P but Q was expected |}]

let%expect_test "declared names are in scope for later annotations" =
  session
    [ "axiom N : Type"
    ; "def arrow : Type = N -> N"
    ; "axiom g : arrow"
    ; "#check g"
    ];
  [%expect {| g : N -> N |}]

let%expect_test "#eval reports just the normal form" =
  session
    [ "axiom N : Type"
    ; "axiom zero : N"
    ; "def two = fun (f : N -> N) => fun (x : N) => f (f x)"
    ; "def add = fun (m : (N -> N) -> N -> N) => fun (n : (N -> N) -> N -> N) \
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

let%expect_test "sigma: beta, eta, dependent pairs, irrelevance" =
  session
    [ "axiom N : Type"
    ; "axiom zero : N"
    ; (* beta: projections of a literal pair *)
      "def p : N × N := (zero, zero)"
    ; "#check_equal p.1 zero"
    ; (* a dependent pair: the type of the package depends on its head *)
      "def package : Σ (A : Type) ⇒ A := (Unit, ())"
    ; "#check package.2"
    ; (* eta (surjective pairing) on a neutral pair *)
      "axiom q : N × N"
    ; "#check_equal q (q.1, q.2)"
    ; (* eta and unit-eta compose: any two pairs of units are equal *)
      "axiom r : Unit × Unit"
    ; "#check_equal r ((), ())"
    ; (* proof pairs are props, hence irrelevant *)
      "axiom a : Prop"
    ; "axiom c1 : a × a"
    ; "axiom c2 : a × a"
    ; "#check_equal c1 c2"
    ];
  [%expect {| () : Unit |}]

let%expect_test "sums: iota, stuck cases, irrelevance" =
  session
    [ "axiom A : Type"
    ; "axiom B : Type"
    ; "axiom a : A"
    ; "axiom b : B"
    ; "def swap (s : A + B) : B + A :="
      ^ " case (λ x : A + B ⇒ B + A) s (λ x : A ⇒ (inr x : B + A)) (λ y : B ⇒ \
         (inl y : B + A))"
    ; (* ι-reduction picks each branch; injections in argument and checked
         positions need no ascription *)
      "#check_equal (swap (inl a)) (inr a)"
    ; "#check_equal (swap (inr b)) (inl b)"
    ; (* a stuck case is equal to itself, and not to a sibling with other
         branches *)
      "axiom s : A + B"
    ; "#check swap s"
    ; "#check_equal (swap s) (swap s)"
    ; (* same type, different branches: conv compares the stuck branches *)
      "axiom t : A + A"
    ; "def same (s : A + A) : A + A :="
      ^ " case (λ x : A + A ⇒ A + A) s (λ x : A ⇒ (inl x : A + A)) (λ y : A ⇒ \
         (inr y : A + A))"
    ; "def cross (s : A + A) : A + A :="
      ^ " case (λ x : A + A ⇒ A + A) s (λ x : A ⇒ (inr x : A + A)) (λ y : A ⇒ \
         (inl y : A + A))"
    ; "#check_equal (same t) (same t)"
    ; "#check_equal (same t) (cross t)"
    ; (* no η for sums: a stuck value is not its case-rebuilt self *)
      "#check_equal (same t) t"
    ; (* proofs of a disjunction are irrelevant: even different injections are
         equal *)
      "axiom p : Prop"
    ; "axiom q : Prop"
    ; "axiom hp : p"
    ; "axiom hq : q"
    ; "#check_equal (inl hp : p + q) (inr hq : p + q)"
    ];
  [%expect
    {|
    case (fun (x : A + B) => B + A) s (fun (x : A) => inr x)
    (fun (y : B) => inl y) : B + A
    type error: #check_equal failed: case (fun (x : A + A) => A + A) t (fun (x : A) => inl x)
    (fun (y : A) => inr y) is not convertible with case (fun (x : A + A) => A + A) t (fun (x : A) => inr x)
    (fun (y : A) => inl y)
    type error: #check_equal failed: case (fun (x : A + A) => A + A) t (fun (x : A) => inl x)
    (fun (y : A) => inr y) is not convertible with t
    |}]

let%expect_test "equality: J lemmas, iota, stuck J, UIP" =
  session
    [ "axiom A : Type"
    ; "axiom B : Type"
    ; "axiom a : A"
    ; "axiom b : A"
    ; (* the standard lemmas, each one J at a different motive *)
      "def sym (x y : A) (p : Eq A x y) : Eq A y x :="
      ^ " J (λ z : A ⇒ λ q : Eq A x z ⇒ Eq A z x) refl p"
    ; "def trans (x y z : A) (p : Eq A x y) (q : Eq A y z) : Eq A x z :="
      ^ " J (λ w : A ⇒ λ r : Eq A y w ⇒ Eq A x w) p q"
    ; "def cong (f : A → B) (x y : A) (p : Eq A x y) : Eq B (f x) (f y) :="
      ^ " J (λ z : A ⇒ λ q : Eq A x z ⇒ Eq B (f x) (f z)) refl p"
    ; (* subst is large elimination: the motive lands in Type *)
      "def subst (P : A → Type) (x y : A) (p : Eq A x y) (h : P x) : P y :="
      ^ " J (λ z : A ⇒ λ q : Eq A x z ⇒ P z) h p"
    ; "#check sym"
    ; "#check subst"
    ; (* ι: transport along refl is the identity, definitionally *)
      "axiom P : A → Type"
    ; "axiom h : P a"
    ; "#check_equal (subst P a a refl h) h"
    ; (* a stuck J (proof is a variable) is a neutral, equal to itself *)
      "axiom q : Eq A a b"
    ; "#check sym a b q"
    ; "#check_equal (sym a b q) (sym a b q)"
    ; (* UIP for free: any two proofs of the same equation are equal *)
      "axiom q2 : Eq A a b"
    ; "#check_equal q q2"
    ];
  [%expect
    {|
    fun (x : A) =>
    fun (y : A) =>
    fun (p : Eq A x y) =>
    J (fun (z : A) => fun (q : Eq A x z) => Eq A z x) refl p : (x : A) -> (y : A) -> Eq A x y -> Eq A y x
    fun (P : A -> Type) =>
    fun (x : A) =>
    fun (y : A) =>
    fun (p : Eq A x y) =>
    fun (h : P x) => J (fun (z : A) => fun (q : Eq A x z) => P z) h p : (P : A -> Type) -> (x : A) -> (y : A) -> Eq A x y -> P x -> P y
    J (fun (z : A) => fun (q' : Eq A a z) => Eq A z a) refl q : Eq A b a
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
      ^ " J (λ z : A ⇒ λ q : Eq A x z ⇒ Eq B (f x) (f z)) refl p"
    ; "theorem add_zero (n : Nat) : Eq Nat (add n 0) n :="
      ^ " Nat.rec (λ m : Nat ⇒ Eq Nat (add m 0) m) refl"
      ^ " (λ k : Nat ⇒ λ ih : Eq Nat (add k 0) k ⇒"
      ^ " cong Nat Nat (λ m : Nat ⇒ Nat.succ m) (add k 0) k ih) n"
    ; "#check add_zero"
    ];
  [%expect
    {|
    5
    6
    add_zero : (n : Nat) ->
    Eq Nat
    (Nat.rec (fun (x : Nat) => Nat) 0
     (fun (k : Nat) => fun (ih : Nat) => Nat.succ ih) n)
    n
    |}]
