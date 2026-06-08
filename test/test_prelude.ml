open Mtt

(* the prelude loads (type-checks) and its definitions are then in scope *)
let%expect_test "prelude is well-typed and its defs are usable" =
  let ctx = Prelude.load Check.empty in
  let check line =
    match Stmt.run ctx (Parse.stmt_of_string line) with
    | _, msg -> Option.iter print_endline msg
    | exception Check.Type_error m -> print_endline ("type error: " ^ m)
  in
  check "#check id";
  [%expect {| fun (A : Type) => fun (x : A) => x : (A : Type) -> A -> A |}];
  check "#check comp";
  [%expect
    {|
    fun (A : Type) =>
    fun (B : Type) =>
    fun (C : Type) =>
    fun (g : B -> C) => fun (f : A -> B) => fun (x : A) => g (f x) : (A : Type) -> (B : Type) -> (C : Type) -> (B -> C) -> (A -> B) -> A -> C
    |}]
