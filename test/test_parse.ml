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
