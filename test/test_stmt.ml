open Mtt

(* feed lines through a toplevel session, printing each response *)
let session lines =
  let step ctx line =
    match Stmt.run ctx (Parse.stmt_of_string line) with
    | ctx, message ->
        Option.iter print_endline message;
        ctx
    | exception Ast.Unbound_variable (loc, x) ->
        Printf.printf "%s: unbound variable: %s\n" (Loc.to_string loc) x;
        ctx
    | exception Check.Type_error msg ->
        Printf.printf "type error: %s\n" msg;
        ctx
  in
  ignore (List.fold_left step Check.empty lines)

let%expect_test "axioms postulate stuck constants" =
  session
    [ "axiom Nat : Type"
    ; "axiom zero : Nat"
    ; "axiom suc : Nat -> Nat"
    ; "#check suc (suc zero)"
    ];
  [%expect {| suc (suc zero) : Nat |}]

let%expect_test "defs unfold (delta), theorems do not (opaque)" =
  session
    [ "axiom Nat : Type"
    ; "axiom zero : Nat"
    ; "def d : Nat = zero"
    ; "theorem t : Nat = zero"
    ; "#check d"
    ; "#check t"
    ];
  [%expect {|
    zero : Nat
    t : Nat
    |}]

let%expect_test "def with inferred type, used at two types" =
  session
    [ "def id = fun (A : Type) => fun (x : A) => x"
    ; "axiom Nat : Nat"
    ; "axiom Nat : Type"
    ; "axiom zero : Nat"
    ; "#check id Nat zero"
    ; "#check id (Nat -> Nat) (id Nat)"
    ];
  [%expect
    {|
    1:13: unbound variable: Nat
    zero : Nat
    fun (x : Nat) => x : Nat -> Nat
    |}]

let%expect_test "a theorem and its use" =
  session
    [ "axiom P : Type"
    ; "axiom Q : Type"
    ; "axiom f : P -> Q"
    ; "axiom p : P"
    ; "theorem q : Q = f p"
    ; "theorem bad : Q = p"
    ];
  [%expect {| type error: this term has type P but Q was expected |}]

let%expect_test "declared names are in scope for later annotations" =
  session
    [ "axiom Nat : Type"
    ; "def arrow : Type = Nat -> Nat"
    ; "axiom g : arrow"
    ; "#check g"
    ];
  [%expect {| g : Nat -> Nat |}]

let%expect_test "#eval reports just the normal form" =
  session
    [ "axiom Nat : Type"
    ; "axiom zero : Nat"
    ; "def two = fun (f : Nat -> Nat) => fun (x : Nat) => f (f x)"
    ; "def add = fun (m : (Nat -> Nat) -> Nat -> Nat) => fun (n : (Nat -> Nat) \
       -> Nat -> Nat) => fun (f : Nat -> Nat) => fun (x : Nat) => m f (n f x)"
    ; "#eval add two two"
    ; "#eval Type Type"
    ];
  [%expect
    {|
    fun (f : Nat -> Nat) => fun (x : Nat) => f (f (f (f x)))
    type error: expected a function, but Type has type Type 1
    |}]

let%expect_test "#check_equal succeeds silently and fails loudly" =
  session
    [ "axiom Nat : Type"
    ; "axiom zero : Nat"
    ; "#check_equal zero zero"
    ; "#check_equal ((fun (x : Nat) => x) zero) zero"
    ; "#check_equal zero Nat"
    ];
  [%expect {| type error: this term has type Type but Nat was expected |}]

let%expect_test "#check with ascription, and #check_equal" =
  session
    [ "axiom Nat : Type"
    ; "axiom zero : Nat"
    ; "#check (zero : Nat)"
    ; "#check ((fun (A : Type) => fun (x : A) => x) : (B : Type) -> B -> B)"
    ; "#check (zero : Type)"
    ; "#check_equal (zero : Nat) zero"
    ];
  [%expect
    {|
    zero : Nat
    fun (A : Type) => fun (x : A) => x : (B : Type) -> B -> B
    type error: this term has type Nat but Type was expected
    |}]

let%expect_test "definitions accept := and unicode binders" =
  session
    [ "axiom Nat : Type"
    ; "axiom zero : Nat"
    ; "def id : Π (A : Type) ⇒ A → A := λ (A : Type) ⇒ λ (x : A) ⇒ x"
    ; "#check_equal (id Nat zero) zero"
    ; "#check id"
    ];
  [%expect {| fun (A : Type) => fun (x : A) => x : (A : Type) -> A -> A |}]

let%expect_test "declaration telescopes" =
  session
    [ "axiom Nat : Type"
    ; "axiom zero : Nat"
    ; "def const (A B : Type) (x : A) (y : B) : A := x"
    ; "#check const"
    ; "#check_equal (const Nat Nat zero zero) zero"
    ; "axiom plus (m n : Nat) : Nat"
    ; "#check plus"
    ; "theorem plus_self (n : Nat) : Nat := plus n n"
    ; "def bad (A : Type) (x : A) : A := A"
    ];
  [%expect
    {|
    fun (A : Type) => fun (B : Type) => fun (x : A) => fun (y : B) => x : (A : Type) -> (B : Type) -> A -> B -> A
    plus : Nat -> Nat -> Nat
    type error: this term has type Type but A was expected
    |}]

let%expect_test "def return annotations are optional, with telescopes" =
  session
    [ "axiom Nat : Type"
    ; "def twice (f : Nat -> Nat) (n : Nat) := f (f n)"
    ; "#check twice"
    ; "def Bool := Π (A : Type) ⇒ A → A → A"
    ; "#check Bool"
    ];
  [%expect
    {|
    fun (f : Nat -> Nat) => fun (n : Nat) => f (f n) : (Nat -> Nat) -> Nat -> Nat
    (A : Type) -> A -> A -> A : Type 1
    |}]

let%expect_test "proof irrelevance" =
  session
    [ "axiom p : Prop"
    ; "axiom h1 : p"
    ; "axiom h2 : p"
    ; (* any two proofs of the same proposition are equal *)
      "#check_equal h1 h2"
    ; (* ... including inside neutral spines: P h1 and P h2 are the same type,
         so coercion between them checks *)
      "axiom P : p -> Type"
    ; "def coerce (y : P h1) : P h2 := y"
    ; (* proofs of different propositions are not equated *)
      "axiom q : Prop"
    ; "#check_equal p q"
    ];
  [%expect {| type error: #check_equal failed: p is not convertible with q |}]

let%expect_test "eta for Unit: every element is definitionally tt" =
  session
    [ "axiom u : Unit"
    ; "#check_equal u tt"
    ; (* by Pi-eta then Unit-eta, all functions into Unit are equal *)
      "axiom f : Unit -> Unit"
    ; "#check_equal f (λ x : Unit ⇒ tt)"
    ; (* but Unit is not equal to other types *)
      "#check_equal Unit Prop"
    ];
  [%expect
    {| type error: #check_equal failed: Unit is not convertible with Prop |}]
