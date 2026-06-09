open Type

let p t = print_endline (to_string t)

let%expect_test "atoms" =
  p (Sort 0);
  [%expect {| Prop |}];
  p (Sort 1);
  [%expect {| Type |}];
  p (Sort 2);
  [%expect {| Type 1 |}];
  p (Var 3);
  [%expect {| !3 |}]

let%expect_test "identity function and its type" =
  p (Lam (Explicit, "A", Sort 1, Lam (Explicit, "x", Var 0, Var 0)));
  [%expect {| fun (A : Type) => fun (x : A) => x |}];
  p (Pi (Explicit, "A", Sort 1, Pi (Explicit, "", Var 0, Var 1)));
  [%expect {| (A : Type) -> A -> A |}]

let%expect_test
    "application is left-associative; atoms parenthesize as arguments" =
  p (App (App (Var 0, Var 1), Sort 1));
  [%expect {| !0 !1 Type |}]

let%expect_test "application binds tighter than arrow" =
  p (Pi (Explicit, "", App (Var 0, Var 1), Sort 1));
  [%expect {| !0 !1 -> Type |}]

let%expect_test "arrow is right-associative: lhs arrows need parens" =
  p (Pi (Explicit, "", Pi (Explicit, "", Sort 1, Sort 1), Sort 1));
  [%expect {| (Type -> Type) -> Type |}]

let%expect_test "lambdas parenthesize when applied" =
  p (App (Lam (Explicit, "A", Sort 1, Var 0), Var 0));
  [%expect {| (fun (A : Type) => A) !0 |}]

let%expect_test "shadowed and empty name hints are freshened" =
  p (Lam (Explicit, "x", Sort 1, Lam (Explicit, "x", Var 0, Var 0)));
  [%expect {| fun (x : Type) => fun (x' : x) => x' |}];
  p (Lam (Explicit, "", Sort 1, Lam (Explicit, "", Var 0, Var 0)));
  [%expect {| fun (x : Type) => fun (x' : x) => x' |}]

let%expect_test "implicit binders print with braces" =
  p (Pi (Implicit, "A", Sort 1, Pi (Explicit, "", Var 0, Var 1)));
  [%expect {| {A : Type} -> A -> A |}];
  p (Lam (Implicit, "A", Sort 1, Lam (Explicit, "x", Var 0, Var 0)));
  [%expect {| fun {A : Type} => fun (x : A) => x |}]
