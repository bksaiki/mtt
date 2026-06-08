The standard prelude is loaded automatically; a plain file can use its
definitions with no ceremony:

  $ cat > p.mtt <<EOF
  > #check id
  > #check_equal (id Nat 0) 0
  > EOF
  $ mtt p.mtt
  fun (A : Type) => fun (x : A) => x : (A : Type) -> A -> A

A file that opens with `prelude` opts out — a bare environment, for defining
the prelude itself or a from-scratch development. Its names are then unbound:

  $ cat > bare.mtt <<EOF
  > prelude
  > #check id
  > EOF
  $ mtt bare.mtt
  bare.mtt:2:8: unbound variable: id
  [1]

`prelude` is only valid as the very first statement:

  $ cat > late.mtt <<EOF
  > axiom A : Type
  > prelude
  > EOF
  $ mtt late.mtt
  late.mtt:2:1: prelude must be the first statement
  [1]
