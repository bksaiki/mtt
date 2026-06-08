The prelude keyword brings the standard library into scope:

  $ cat > p.mtt <<EOF
  > prelude
  > #check id
  > #check_equal (id Nat 0) 0
  > EOF
  $ mtt p.mtt
  fun (A : Type) => fun (x : A) => x : (A : Type) -> A -> A

Without it, prelude names are unbound:

  $ cat > q.mtt <<EOF
  > #check id
  > EOF
  $ mtt q.mtt
  q.mtt:1:8: unbound variable: id
  [1]
