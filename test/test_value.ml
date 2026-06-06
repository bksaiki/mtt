open Mtt

(* parse, normalize, pretty-print *)
let norm s =
  print_endline (Type.to_string (Value.normalize (Parse.term_of_string s)))

let%expect_test "normal forms are unchanged" =
  norm "Type";
  [%expect {| Type |}];
  norm "fun (A : Type) => fun (x : A) => x";
  [%expect {| fun (A : Type) => fun (x : A) => x |}];
  norm "(A : Type) -> A -> A";
  [%expect {| (A : Type) -> A -> A |}]

let%expect_test "beta reduction" =
  norm "(fun (A : Type) => A) Type";
  [%expect {| Type |}];
  norm "(fun (A : Type 1) => fun (x : A) => x) Type";
  [%expect {| fun (x : Type) => x |}]

let%expect_test "reduction under binders" =
  norm "fun (A : Type) => (fun (B : Type) => B) A";
  [%expect {| fun (A : Type) => A |}];
  norm "(B : Type) -> ((fun (A : Type 1) => A) Type) -> B";
  [%expect {| (B : Type) -> Type -> B |}]

let%expect_test "stuck applications stay as neutral spines" =
  norm "fun (f : Type -> Type) => fun (x : Type) => f (f x)";
  [%expect {| fun (f : Type -> Type) => fun (x : Type) => f (f x) |}]

let%expect_test "church numerals: 2 + 2 = 4" =
  let n = "(Type -> Type) -> Type -> Type" in
  let two = "(fun (f : Type -> Type) => fun (x : Type) => f (f x))" in
  let add =
    Printf.sprintf
      "(fun (m : %s) => fun (n : %s) => fun (f : Type -> Type) => fun (x : \
       Type) => m f (n f x))"
      n n
  in
  norm (Printf.sprintf "%s %s %s" add two two);
  [%expect {| fun (f : Type -> Type) => fun (x : Type) => f (f (f (f x))) |}]

let%expect_test "applying a non-function fails" =
  (try norm "Type Type" with
  | Value.Not_a_function -> print_endline "not a function");
  [%expect {| not a function |}]
