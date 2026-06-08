Checking a file: declarations may span lines, only #check/#eval print, and
the prelude (with Nat, add, ...) is available by default.

  $ cat > demo.mtt <<EOF
  > def twice (f : Nat → Nat) (n : Nat) : Nat :=
  >   f (f n)
  > #check twice
  > #eval twice (λ n : Nat ⇒ succ n) 0
  > EOF
  $ mtt demo.mtt
  fun (f : Nat -> Nat) => fun (n : Nat) => f (f n) : (Nat -> Nat) -> Nat -> Nat
  2

A type error stops checking with a nonzero exit, located at the statement:

  $ cat > bad.mtt <<EOF
  > axiom A : Type
  > def oops : A := Type
  > EOF
  $ mtt bad.mtt
  bad.mtt:2:1: type error: this term has type Type 1 but A was expected
  [1]

There are no statement terminators, so a stray term is absorbed into the
preceding declaration as an application — the failure then surfaces
downstream rather than as a clean parse error:

  $ cat > stray.mtt <<EOF
  > axiom A : Type
  > B
  > EOF
  $ mtt stray.mtt
  stray.mtt:2:1: unbound variable: B
  [1]
