Only #check and #eval produce output (#check the normal form and type,
#eval just the normal form); declarations are silent.

  $ mtt <<EOF
  > #check Type
  > #check fun (A : Type) => fun (x : A) => x
  > #check (fun (A : Type 1) => fun (x : A) => x) Type
  > #eval (fun (A : Type 1) => fun (x : A) => x) Type
  > EOF
  Type : Type 1
  fun (A : Type) => fun (x : A) => x : (A : Type) -> A -> A
  fun (x : Type) => x : Type -> Type
  fun (x : Type) => x

Declarations extend the context; defs unfold, theorems are opaque:

  $ mtt <<EOF
  > axiom A : Type
  > axiom a : A
  > def d := a
  > theorem t : A := a
  > #check d
  > #check t
  > EOF
  a : A
  t : A

Errors are reported without ending the session:

  $ mtt <<EOF
  > #check y
  > ?!
  > #check Type Type
  > #check Type
  > EOF
  1:8: unbound variable: y
  1:1: syntax error: unexpected character '?'
  type error: expected a function, but Type has type Type 1
  Type : Type 1
