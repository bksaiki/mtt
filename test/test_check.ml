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

let%expect_test "no cumulativity: Type is not a Type 1... but is a Type 2" =
  (* Type : Type 1, so it cannot instantiate (A : Type) *)
  infer "(fun (A : Type) => A) Type";
  [%expect {| type error: this term has type Type 1 but Type was expected |}];
  infer "(fun (A : Type 2) => A) (Type 1)";
  [%expect {| Type 2 |}]

let%expect_test "a variable of non-function type cannot be applied" =
  infer "fun (A : Type) => fun (x : A) => x x";
  [%expect {| type error: expected a function, but x has type A |}]
