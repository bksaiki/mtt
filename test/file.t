Checking a file: declarations may span lines; only #check/#eval print.

  $ cat > demo.mtt <<EOF
  > axiom Nat : Type
  > axiom zero : Nat
  > axiom suc : Nat -> Nat
  > 
  > def id = fun (A : Type) => fun (x : A) => x
  > 
  > def two : (Nat -> Nat) -> Nat -> Nat =
  >   fun (f : Nat -> Nat) => fun (x : Nat) =>
  >     f (f x)
  > 
  > theorem t : Nat = id Nat (suc zero)
  > 
  > #check two
  > #eval two suc zero
  > EOF
  $ mtt demo.mtt
  demo.mtt:1:7: syntax error: unexpected token
  [1]

A type error stops checking with a nonzero exit:

  $ cat > bad.mtt <<EOF
  > axiom Nat : Type
  > theorem bogus : Nat = Nat
  > #check bogus
  > EOF
  $ mtt bad.mtt
  bad.mtt:1:7: syntax error: unexpected token
  [1]

Bare terms are not allowed in files. Beware: since juxtaposition is
application, a stray term is absorbed into the preceding declaration's last
term (here the axiom's annotation becomes "Type Nat"), so the failure shows
up as a downstream error rather than a parse error:

  $ cat > bare.mtt <<EOF
  > axiom Nat : Type
  > Nat
  > EOF
  $ mtt bare.mtt
  bare.mtt:1:7: syntax error: unexpected token
  [1]
