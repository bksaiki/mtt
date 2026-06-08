open Mtt

(* parse and check against the prelude, so the standard types (Unit, Empty, ...)
   are in scope; print the inferred type (or the type error) *)
let prelude = Prelude.load Stmt.initial

let infer s =
  match
    Check.infer prelude.ctx
      (Parse.term_of_string_in prelude.ctx.signature ~notation:prelude.notation
         s)
  with
  | ty ->
      print_endline
        (Notation.show prelude.notation prelude.ctx.names prelude.ctx.lvl ty)
  | exception Error.Type_error frags ->
      Printf.printf "type error: %s\n"
        (Notation.render_error prelude.notation frags)

let%expect_test "universe rules" =
  infer "Type";
  [%expect {| Type 1 |}];
  infer "Type 1";
  [%expect {| Type 2 |}];
  (* predicative: quantifying over Type lands in Type 1 *)
  infer "(A : Type) -> A";
  [%expect {| Type 1 |}];
  infer "Type -> Type";
  [%expect {| Type 1 |}]

let%expect_test "the polymorphic identity" =
  infer "fun (A : Type) => fun (x : A) => x";
  [%expect {| (A : Type) -> A -> A |}]

let%expect_test "dependent application instantiates the codomain" =
  infer "(fun (A : Type 1) => fun (x : A) => x) Type";
  [%expect {| Type -> Type |}]

let%expect_test "annotations are evaluated: inferred types are in normal form" =
  infer "fun (x : (fun (B : Type 1) => B) Type) => x";
  [%expect {| Type -> Type |}]

let%expect_test "eta: f is convertible with fun x => f x" =
  infer
    "fun (F : (Type -> Type) -> Type) => fun (f : Type -> Type) => fun (y : F \
     f) => (fun (z : F (fun (x : Type) => f x)) => z) y";
  [%expect
    {|
    (F : (Type -> Type) -> Type) ->
    (f : Type -> Type) -> F f -> F (fun (x : Type) => f x)
    |}]

let%expect_test "applying a non-function is rejected" =
  infer "Type Type";
  [%expect {| type error: expected a function, but Type has type Type 1 |}]

let%expect_test "argument type mismatch is rejected" =
  infer "(fun (f : Type -> Type) => f) Type";
  [%expect
    {| type error: this term has type Type 1 but Type -> Type was expected |}]

let%expect_test "cumulativity: universes include upward" =
  infer "(fun (A : Type 2) => A) Type";
  [%expect {| Type 2 |}];
  infer "(fun (A : Type 3) => A) (Type -> Type 1)";
  [%expect {| Type 3 |}]

let%expect_test "cumulativity: products are covariant in the codomain" =
  (* the argument has type Type -> Type, used at Type -> Type 2 *)
  infer "(fun (f : Type -> Type 2) => f) (fun (A : Type) => A)";
  [%expect {| Type -> Type 2 |}];
  (* the bare lambda above goes through the lam-vs-pi rule; ascribed, it goes
     through pi-subtyping in subsumption *)
  infer "(fun (f : Type -> Type 2) => f) ((fun (A : Type) => A) : Type -> Type)";
  [%expect {| Type -> Type 2 |}]

let%expect_test "cumulativity: domains are invariant" =
  infer "(fun (f : Type 1 -> Type) => f) (fun (A : Type) => A)";
  [%expect
    {| type error: the annotation Type does not match the expected domain Type 1 |}];
  infer "(fun (f : Type 1 -> Type) => f) ((fun (A : Type) => A) : Type -> Type)";
  [%expect
    {| type error: this term has type Type -> Type but Type 1 -> Type was expected |}]

let%expect_test "no down-casting: a large universe never inhabits a smaller one"
    =
  (* Type : Type 1, so it cannot instantiate (A : Type) *)
  infer "(fun (A : Type) => A) Type";
  [%expect {| type error: this term has type Type 1 but Type was expected |}];
  infer "(fun (A : Type 2) => A) (Type 1)";
  [%expect {| Type 2 |}]

let%expect_test "a variable of non-function type cannot be applied" =
  infer "fun (A : Type) => fun (x : A) => x x";
  [%expect {| type error: expected a function, but x has type A |}]

let%expect_test "Prop is the bottom sort" =
  infer "Prop";
  [%expect {| Type |}];
  (* a predicate type is data, not a proposition *)
  infer "Type -> Prop";
  [%expect {| Type 1 |}]

let%expect_test "Prop is impredicative" =
  (* quantifying over all propositions yields a proposition... *)
  infer "(p : Prop) -> p";
  [%expect {| Prop |}];
  (* ...as does quantifying over a huge universe, if the codomain is a Prop *)
  infer "(A : Type 3) -> A -> ((p : Prop) -> p)";
  [%expect {| Prop |}];
  (* Prop is closed under arrows between propositions *)
  infer "(p : Prop) -> (q : Prop) -> p -> q";
  [%expect {| Prop |}]

let%expect_test "cumulativity: Prop flows into Type" =
  infer "(fun (A : Type) => A) ((p : Prop) -> p)";
  [%expect {| Type |}]

let%expect_test "Unit and its element" =
  infer "Unit";
  [%expect {| Type |}];
  infer "()";
  [%expect {| Unit |}];
  infer "Unit -> Unit";
  [%expect {| Type |}]

(* Σ is now the prelude record [Sigma], fixed at Type (the kernel has no Σ of
   its own). A universe-polymorphic Σ that forms at the max of its components —
   in particular one ranging over [Type] itself, or one of two Props landing
   back in Prop — awaits universe polymorphism. *)
let%expect_test "sigma formation sorts (Type-fixed inductive)" =
  infer "Unit × Unit";
  [%expect {| Type |}];
  infer "Unit × Nat";
  [%expect {| Type |}];
  (* a dependent Σ whose components live in Type (the proof component is a Prop,
     included into Type by cumulativity) *)
  infer {|Σ (n : Nat) ⇒ Eq Nat n n|};
  [%expect {| Type |}];
  (* fixed at Type: a Σ ranging over the universe itself no longer forms *)
  infer {|Σ (A : Type) ⇒ A|};
  [%expect {| type error: this term has type Type 1 but Type was expected |}]

let%expect_test "pair inference defaults to the constant family (Lean-style)" =
  infer "((), ())";
  [%expect {| Unit × Unit |}];
  (* the components' types may mention bound variables *)
  infer {|λ (A : Type) (x : A) ⇒ (x, x)|};
  [%expect {| (A : Type) -> A -> A × A |}];
  (* a dependent type is recovered by checking against the Σ *)
  infer {|(((), ()) : Unit × Unit)|};
  [%expect {| Unit × Unit |}];
  infer {|((0, refl) : Σ (n : Nat) ⇒ Eq Nat n n)|};
  [%expect {| Σ (n : Nat) ⇒ Eq Nat n n |}];
  (* the second projection's type mentions the first *)
  infer {|λ p : (Σ (n : Nat) ⇒ Eq Nat n n) ⇒ p.2|};
  [%expect {| (p : Σ (n : Nat) ⇒ Eq Nat n n) -> Eq Nat p.1 p.1 |}];
  infer "λ u : Unit ⇒ u.1";
  [%expect {| type error: Unit has no field .1 |}]

let%expect_test "sum formation sorts" =
  infer "Unit + Unit";
  [%expect {| Type |}];
  infer "Unit + Nat";
  [%expect {| Type |}];
  (* plain max: a sum of props is a prop (native disjunction) *)
  infer "(p : Prop) -> (q : Prop) -> (p + q : Prop) -> Unit";
  [%expect {| Type |}]

let%expect_test "injections are check-only" =
  infer "inl ()";
  [%expect
    {| type error: cannot infer the type of an injection: ascribe it, e.g. (inl a : A + B) |}];
  infer "(inl () : Unit + Nat)";
  [%expect {| Unit + Nat |}]

let%expect_test "case: typing, dependent motive, errors" =
  infer
    {|λ s : Unit + Unit ⇒ case (λ x : Unit + Unit ⇒ Unit) s (λ x : Unit ⇒ x) (λ y : Unit ⇒ y)|};
  [%expect {| Unit + Unit -> Unit |}];
  (* a Type-valued motive: large elimination of a data sum is fine *)
  infer
    {|λ s : Unit + Nat ⇒ case (λ x : Unit + Nat ⇒ Type) s (λ x : Unit ⇒ Unit) (λ h : Nat ⇒ Nat)|};
  [%expect {| Unit + Nat -> Type |}];
  (* the motive must consume the scrutinee's type *)
  infer
    {|λ s : Unit + Unit ⇒ case (λ x : Unit ⇒ Unit) s (λ x : Unit ⇒ x) (λ y : Unit ⇒ y)|};
  [%expect
    {| type error: the motive's domain Unit does not match the scrutinee's type Unit + Unit |}];
  (* and must land in a sort *)
  infer
    {|λ s : Unit + Unit ⇒ case (λ x : Unit + Unit ⇒ x) s (λ x : Unit ⇒ x) (λ y : Unit ⇒ y)|};
  [%expect {| type error: the motive must land in a sort, not Unit + Unit |}]

let%expect_test "the large-elimination restriction" =
  (* a proof of a disjunction cannot be eliminated into Type... *)
  infer
    {|λ (p q : Prop) (s : p + q) ⇒ case (λ x : p + q ⇒ Unit) s (λ x : p ⇒ ()) (λ y : q ⇒ ())|};
  [%expect
    {| type error: cannot eliminate a proof of p + q into Type: a case on a proposition must target Prop |}];
  (* ...but eliminating into Prop is fine: Or-swap by elimination *)
  infer
    {|λ (p q : Prop) (s : p + q) ⇒ case (λ x : p + q ⇒ q + p) s (λ x : p ⇒ (inr x : q + p)) (λ y : q ⇒ (inl y : q + p))|};
  [%expect {| (p : Prop) -> (q : Prop) -> p + q -> q + p |}]

let%expect_test "equality formation and refl" =
  infer "Eq Unit () ()";
  [%expect {| Prop |}];
  (* refl is check-only *)
  infer "refl";
  [%expect
    {| type error: cannot infer the type of refl: ascribe it, e.g. (refl : Eq A x x) |}];
  infer "(refl : Eq Unit () ())";
  [%expect {| Eq Unit () () |}];
  (* refl reifies definitional equality: it checks because the sides are
     convertible (here by β) *)
  infer {|(refl : Eq Type ((λ A : Type ⇒ A) Unit) Unit)|};
  [%expect {| Eq Type Unit Unit |}];
  (* but refl rejects genuinely distinct sides *)
  infer "(refl : Eq Type Unit Nat)";
  [%expect
    {| type error: refl requires the sides to be equal, but Unit is not Nat |}];
  (* the endpoints must share the type A *)
  infer "Eq Unit () Type";
  [%expect {| type error: this term has type Type 1 but Unit was expected |}]

(* Nat is now an ordinary prelude inductive: the former, its numerals, and the
   qualified constructor. Its recursor and the generic recursor's error
   behaviour are exercised directly in test_ind.ml. *)
let%expect_test "Nat formation and constructors" =
  infer "Nat";
  [%expect {| Type |}];
  infer "0";
  [%expect {| Nat |}];
  infer "Nat.succ (Nat.succ 0)";
  [%expect {| Nat |}];
  (* the constructor's argument must check against Nat *)
  infer "Nat.succ Type";
  [%expect {| type error: this term has type Type 1 but Nat was expected |}]

let%expect_test "Nat.rec at the surface (large elimination into Type)" =
  infer
    {|λ n : Nat ⇒ Nat.rec (λ x : Nat ⇒ Type) Unit (λ k : Nat ⇒ λ ih : Type ⇒ ih) n|};
  [%expect {| Nat -> Type |}]
