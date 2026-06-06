Only #check and #eval produce output: #check prints the normal form and
type, #eval just the normal form. Bare terms and declarations are checked
silently.

  $ mtt <<EOF
  > Type
  > #check Type
  > #check fun (A : Type) => fun (x : A) => x
  > #check (fun (A : Type 1) => fun (x : A) => x) Type
  > #eval (fun (A : Type 1) => fun (x : A) => x) Type
  > EOF
  Type : Type 1
  fun (A : Type) => fun (x : A) => x : (A : Type) -> A -> A
  fun (x : Type) => x : Type -> Type
  fun (x : Type) => x

Declarations extend the context; defs unfold, theorems and axioms are stuck:

  $ mtt <<EOF
  > axiom Nat : Type
  > axiom zero : Nat
  > def id = fun (A : Type) => fun (x : A) => x
  > def d : Nat = id Nat zero
  > theorem t : Nat = zero
  > #check d
  > #check t
  > EOF
  zero : Nat
  t : Nat

Errors are reported without ending the session:

  $ mtt <<EOF
  > fun (x : Type) => y
  > fun (x : ) => x
  > ?!
  > Type Type
  > (fun (A : Type) => A) Type
  > #check Type
  > EOF
  1:19: unbound variable: y
  1:10: syntax error: unexpected token
  1:1: syntax error: unexpected character '?'
  type error: expected a function, but Type has type Type 1
  type error: this term has type Type 1 but Type was expected
  Type : Type 1
