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
  infer {|((0, Eq.refl Nat 0) : Σ (n : Nat) ⇒ Eq Nat n n)|};
  [%expect {| Σ (n : Nat) ⇒ n = n |}];
  (* the second projection's type mentions the first *)
  infer {|λ p : (Σ (n : Nat) ⇒ Eq Nat n n) ⇒ p.2|};
  [%expect {| (p : Σ (n : Nat) ⇒ n = n) -> p.1 = p.1 |}];
  infer "λ u : Unit ⇒ u.1";
  [%expect {| type error: Unit has no field .1 |}]

(* Sum is now the prelude inductive [Sum], fixed at Type (with [+] as notation);
   its constructors and recursor are the qualified
   [Sum.inl]/[Sum.inr]/[Sum.rec]. A proof-irrelevant disjunction of Props awaits
   universe polymorphism, and the generic recursor typing / large-elimination
   behaviour lives in test_ind.ml. *)
let%expect_test "sum formation and injections (Type-fixed inductive)" =
  infer "Unit + Unit";
  [%expect {| Type |}];
  infer "Unit + Nat";
  [%expect {| Type |}];
  (* the injection's derived type; checking against the sum recovers the
     parameters, so an injection may drop them *)
  infer "Sum.inl";
  [%expect {| (A : Type) -> (B : Type) -> A -> A + B |}];
  infer "(Sum.inl () : Unit + Nat)";
  [%expect {| Unit + Nat |}];
  (* the recursor eliminating a data sum into Type (no restriction) *)
  infer
    {|λ s : Unit + Nat ⇒ Sum.rec Unit Nat (λ x : Unit + Nat ⇒ Type) (λ x : Unit ⇒ Unit) (λ h : Nat ⇒ Nat) s|};
  [%expect {| Unit + Nat -> Type |}]

let%expect_test "equality formation and Eq.refl" =
  infer "Eq Unit () ()";
  [%expect {| Prop |}];
  (* [rfl] is now an ordinary prelude def (tested in test_stmt); here we
     exercise the underlying constructor [Eq.refl], whose parameters are
     explicit *)
  infer "Eq.refl";
  [%expect {| (A : Type) -> (x : A) -> x = x |}];
  infer "Eq.refl Unit ()";
  [%expect {| () = () |}];
  (* Eq.refl reifies definitional equality: it checks against an equation whose
     endpoints are convertible (here by β) but not syntactically equal *)
  infer {|(Eq.refl Nat 0 : Eq Nat ((λ n : Nat ⇒ n) 0) 0)|};
  [%expect {| 0 = 0 |}];
  (* but it rejects genuinely distinct sides *)
  infer "(Eq.refl Nat 0 : Eq Nat 0 (Nat.succ 0))";
  [%expect {| type error: this term has type 0 = 0 but 0 = 1 was expected |}];
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
