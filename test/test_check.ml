open Mtt

(* parse, infer, print the type (or the type error) *)
let infer s =
  match Check.infer Check.empty (Parse.term_of_string s) with
  | ty -> print_endline (Type.to_string (Value.quote 0 ty))
  | exception Check.Type_error msg -> Printf.printf "type error: %s\n" msg

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

let%expect_test "Empty and absurd" =
  infer "Empty";
  [%expect {| Prop |}];
  (* negation of anything is a Prop, by imax — even negation of data *)
  infer "Type -> Empty";
  [%expect {| Prop |}];
  (* ex falso eliminates into any sort *)
  infer {|λ h : Empty ⇒ absurd Type h|};
  [%expect {| Empty -> Type |}];
  infer {|λ h : Empty ⇒ absurd (Type 3) h|};
  [%expect {| Empty -> Type 3 |}];
  (* the proof must actually be of type Empty *)
  infer "absurd Unit ()";
  [%expect {| type error: this term has type Unit but Empty was expected |}]
