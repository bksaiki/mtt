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
  | Ast.Unbound_variable x -> Printf.printf "unbound: %s\n" x);
  [%expect {| unbound: y |}]

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
