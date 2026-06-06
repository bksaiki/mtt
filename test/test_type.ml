open Mtt.Type

let p t = print_endline (to_string t)

let%expect_test "atoms" =
  p (Univ 0);
  [%expect {| Type |}];
  p (Univ 1);
  [%expect {| Type 1 |}];
  p (Var 3);
  [%expect {| !3 |}]

let%expect_test "identity function and its type" =
  p (Lam ("A", Univ 0, Lam ("x", Var 0, Var 0)));
  [%expect {| fun (A : Type) => fun (x : A) => x |}];
  p (Pi ("A", Univ 0, Pi ("", Var 0, Var 1)));
  [%expect {| (A : Type) -> A -> A |}]

let%expect_test
    "application is left-associative; atoms parenthesize as arguments" =
  p (App (App (Var 0, Var 1), Univ 0));
  [%expect {| !0 !1 Type |}]

let%expect_test "application binds tighter than arrow" =
  p (Pi ("", App (Var 0, Var 1), Univ 0));
  [%expect {| !0 !1 -> Type |}]

let%expect_test "arrow is right-associative: lhs arrows need parens" =
  p (Pi ("", Pi ("", Univ 0, Univ 0), Univ 0));
  [%expect {| (Type -> Type) -> Type |}]

let%expect_test "lambdas parenthesize when applied" =
  p (App (Lam ("A", Univ 0, Var 0), Var 0));
  [%expect {| (fun (A : Type) => A) !0 |}]

let%expect_test "shadowed and empty name hints are freshened" =
  p (Lam ("x", Univ 0, Lam ("x", Var 0, Var 0)));
  [%expect {| fun (x : Type) => fun (x' : x) => x' |}];
  p (Lam ("", Univ 0, Lam ("", Var 0, Var 0)));
  [%expect {| fun (x : Type) => fun (x' : x) => x' |}]
