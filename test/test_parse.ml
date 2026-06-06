open Mtt

(* parse, convert to de Bruijn, then pretty-print back *)
let roundtrip s = print_endline (Type.to_string (Parse.term_of_string s))

let%expect_test "universes" =
  roundtrip "Type";
  [%expect {| Type |}];
  roundtrip "Type 3";
  [%expect {| Type 3 |}]

let%expect_test "identity function and its type" =
  roundtrip "fun (A : Type) => fun (x : A) => x";
  [%expect {| fun (A : Type) => fun (x : A) => x |}];
  roundtrip "(A : Type) -> A -> A";
  [%expect {| (A : Type) -> A -> A |}]

let%expect_test "application, associativity, parens" =
  roundtrip "fun (f : Type -> Type) => fun (x : Type) => f (f x)";
  [%expect {| fun (f : Type -> Type) => fun (x : Type) => f (f x) |}];
  roundtrip "(Type -> Type) -> Type";
  [%expect {| (Type -> Type) -> Type |}];
  roundtrip "(fun (A : Type 1) => A) Type";
  [%expect {| (fun (A : Type 1) => A) Type |}]

let%expect_test "shadowing resolves to the nearest binder" =
  roundtrip "fun (x : Type) => fun (x : x) => x";
  [%expect {| fun (x : Type) => fun (x' : x) => x' |}]

let%expect_test "unbound variables are rejected" =
  (try roundtrip "fun (x : Type) => y" with
  | Ast.Unbound_variable (loc, x) ->
      Printf.printf "%s: unbound: %s\n" (Loc.to_string loc) x);
  [%expect {| 1:19: unbound: y |}];
  (* positions track newlines *)
  (try roundtrip "fun (A : Type) =>\n  B" with
  | Ast.Unbound_variable (loc, x) ->
      Printf.printf "%s: unbound: %s\n" (Loc.to_string loc) x);
  [%expect {| 2:3: unbound: B |}]

let%expect_test "ascription elaborates to the typed identity" =
  roundtrip "(Type : Type 1)";
  [%expect {| (fun (x : Type 1) => x) Type |}];
  roundtrip "fun (f : Type -> Type) => f (Type : Type)";
  [%expect {| fun (f : Type -> Type) => f ((fun (x : Type) => x) Type) |}]

let%expect_test "ascribed variable left of an arrow is a pi binder" =
  roundtrip "(A : Type) -> A";
  [%expect {| (A : Type) -> A |}];
  (* non-variable ascriptions and bare domains are plain arrows *)
  roundtrip "(Type : Type 1) -> Type";
  [%expect {| (fun (x : Type 1) => x) Type -> Type |}];
  roundtrip "fun (g : ((A : Type) -> A) -> Type) => g";
  [%expect {| fun (g : ((A : Type) -> A) -> Type) => g |}]

let%expect_test "unicode alternatives lex to the same tokens" =
  roundtrip {|λ (A : Type) ⇒ λ (x : A) ⇒ x|};
  [%expect {| fun (A : Type) => fun (x : A) => x |}];
  roundtrip {|Π (A : Type) ⇒ A → A|};
  [%expect {| (A : Type) -> A -> A |}];
  roundtrip {|∏ (P : Type → Type) ⇒ P (Type : Type 1)|};
  [%expect {| (P : Type -> Type) -> P ((fun (x : Type 1) => x) Type) |}]

let%expect_test "binder groups and telescopes desugar to nested binders" =
  roundtrip {|λ (A B : Type) (x : A) ⇒ x|};
  [%expect {| fun (A : Type) => fun (B : Type) => fun (x : A) => x |}];
  roundtrip {|Π (A B : Type) ⇒ A → B|};
  [%expect {| (A : Type) -> (B : Type) -> A -> B |}];
  roundtrip "(A B : Type) -> A -> B";
  [%expect {| (A : Type) -> (B : Type) -> A -> B |}];
  (* an ascribed non-variable spine is still just an ascription *)
  roundtrip "fun (f : Type -> Type) => (f Type : Type) -> Type";
  [%expect
    {| fun (f : Type -> Type) => (fun (x : Type) => x) (f Type) -> Type |}]

let%expect_test "line comments are skipped" =
  roundtrip "Type -- trailing comment";
  [%expect {| Type |}];
  roundtrip "Type ->-- arrows still lex next to comments\n Type";
  [%expect {| Type -> Type |}]

let%expect_test "single binders may drop their parens" =
  roundtrip {|λ y : Type ⇒ y|};
  [%expect {| fun (y : Type) => y |}];
  roundtrip {|Π C : Type ⇒ C → C|};
  [%expect {| (C : Type) -> C -> C |}]

let%expect_test "unit syntax" =
  roundtrip {|λ x : Unit ⇒ ()|};
  [%expect {| fun (x : Unit) => () |}]

let%expect_test "() is the unit element" =
  roundtrip "()";
  [%expect {| () |}];
  roundtrip "( )";
  [%expect {| () |}];
  roundtrip {|λ f : Unit → Unit ⇒ f ()|};
  [%expect {| fun (f : Unit -> Unit) => f () |}]

let%expect_test "sigma, products, pairs, projections" =
  roundtrip {|Σ (A : Type) ⇒ A|};
  [%expect {| Σ (A : Type) ⇒ A |}];
  roundtrip {|Σ (A B : Type) (x : A) ⇒ B|};
  [%expect {| Σ (A : Type) ⇒ Σ (B : Type) ⇒ A × B |}];
  roundtrip {|Σ A : Type ⇒ A|};
  [%expect {| Σ (A : Type) ⇒ A |}];
  (* * is the ascii spelling of × *)
  roundtrip "Type * Unit";
  [%expect {| Type × Unit |}];
  (* products bind tighter than arrows, looser than application *)
  roundtrip {|Unit × Unit → Unit|};
  [%expect {| Unit × Unit -> Unit |}];
  roundtrip {|λ f : Type → Type ⇒ f Unit × Unit|};
  [%expect {| fun (f : Type -> Type) => f Unit × Unit |}];
  (* × is right-associative *)
  roundtrip {|Unit × Unit × Unit|};
  [%expect {| Unit × Unit × Unit |}];
  roundtrip {|(Unit × Unit) × Unit|};
  [%expect {| (Unit × Unit) × Unit |}];
  (* tuples right-nest; projections are postfix and tightest *)
  roundtrip "((), ((), ()))";
  [%expect {| ((), ((), ())) |}];
  roundtrip "((), (), ())";
  [%expect {| ((), ((), ())) |}];
  roundtrip {|λ p : Unit × Unit ⇒ p.1|};
  [%expect {| fun (p : Unit × Unit) => p.1 |}];
  roundtrip {|λ p : Unit × (Unit × Unit) ⇒ p.2.1|};
  [%expect {| fun (p : Unit × Unit × Unit) => p.2.1 |}];
  roundtrip {|λ f : Unit → Unit × Unit ⇒ λ u : Unit ⇒ (f u).2|};
  [%expect {| fun (f : Unit -> Unit × Unit) => fun (u : Unit) => (f u).2 |}]
