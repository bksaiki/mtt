Each line is parsed, type-checked, normalized, and printed with its type:

  $ mtt <<EOF
  > Type
  > fun (A : Type) => fun (x : A) => x
  > (A : Type) -> A -> A
  > (fun (A : Type 1) => fun (x : A) => x) Type
  > EOF
  Type : Type 1
  fun (A : Type) => fun (x : A) => x : (A : Type) -> A -> A
  (A : Type) -> A -> A : Type 1
  fun (x : Type) => x : Type -> Type

Errors are reported without ending the session:

  $ mtt <<EOF
  > fun (x : Type) => y
  > fun (x : ) => x
  > ?!
  > Type Type
  > (fun (A : Type) => A) Type
  > Type
  > EOF
  unbound variable: y
  parse error
  lex error: unexpected character '?'
  type error: expected a function, but Type has type Type 1
  type error: this term has type Type 1 but Type was expected
  Type : Type 1
