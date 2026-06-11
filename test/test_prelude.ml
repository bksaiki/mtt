open Mtt

(* the prelude loads (type-checks) and its definitions are then in scope *)
let%expect_test "prelude is well-typed and its defs are usable" =
  let sess = Prelude.load Stmt.initial in
  let check line =
    match Stmt.run sess (Parse.stmt_of_string line) with
    | _, msg -> Option.iter print_endline msg
    | exception Error.Type_error frags ->
        print_endline
          ("type error: " ^ Notation.render_error sess.notation frags)
  in
  check "#check id";
  [%expect
    {| fun {A : Sort u0} => fun (x : A) => x : {A : Sort u0} -> A -> A |}];
  check "#check comp";
  [%expect
    {|
    fun {A : Sort u0} =>
    fun {B : Sort u1} =>
    fun {C : Sort u2} =>
    fun (g : B -> C) => fun (f : A -> B) => fun (x : A) => g (f x) : {A : Sort u0} ->
    {B : Sort u1} -> {C : Sort u2} -> (B -> C) -> (A -> B) -> A -> C
    |}]
