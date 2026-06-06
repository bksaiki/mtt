open Mtt.Type

let p t = print_endline (to_string t)

let%expect_test "atoms" =
  p (Univ 0);
  [%expect {| Type 0 |}];
  p (Var 3);
  [%expect {| !3 |}]

let%expect_test "identity function and its type" =
  p (Lam (Univ 0, Lam (Var 0, Var 0)));
  [%expect {| fun (x0 : Type 0) => fun (x1 : x0) => x1 |}];
  p (Pi (Univ 0, Pi (Var 0, Var 1)));
  [%expect {| (x0 : Type 0) -> x0 -> x0 |}]

let%expect_test
    "application is left-associative; atoms parenthesize as arguments" =
  p (App (App (Var 0, Var 1), Univ 0));
  [%expect {| !0 !1 (Type 0) |}]

let%expect_test "application binds tighter than arrow" =
  p (Pi (App (Var 0, Var 1), Univ 0));
  [%expect {| !0 !1 -> Type 0 |}]

let%expect_test "arrow is right-associative: lhs arrows need parens" =
  p (Pi (Pi (Univ 0, Univ 0), Univ 0));
  [%expect {| (Type 0 -> Type 0) -> Type 0 |}]

let%expect_test "lambdas parenthesize when applied" =
  p (App (Lam (Univ 0, Var 0), Var 0));
  [%expect {| (fun (x0 : Type 0) => x0) !0 |}]
