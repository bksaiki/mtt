Inductive type declarations: a former, its constructors, and a recursor.
Constructors are qualified by their type (`Bool.true`, `List.cons`), as is the
recursor (`T.rec`). (`Nat`/`succ`/`Eq`/`Unit` are keywords, so user inductives
use other names.)

  $ cat > data.mtt <<'EOF'
  > inductive Bool : Type :=
  > | true : Bool
  > | false : Bool
  > 
  > def not (b : Bool) : Bool :=
  >   Bool.rec (fun (b : Bool) => Bool) Bool.false Bool.true b
  > #eval not Bool.true
  > #eval not Bool.false
  > 
  > inductive MyNat : Type :=
  > | ze : MyNat
  > | su : MyNat -> MyNat
  > 
  > def double (n : MyNat) : MyNat :=
  >   MyNat.rec (fun (k : MyNat) => MyNat) MyNat.ze
  >     (fun (k : MyNat) (ih : MyNat) => MyNat.su (MyNat.su ih)) n
  > #eval double (MyNat.su (MyNat.su MyNat.ze))
  > 
  > inductive List (A : Type) : Type :=
  > | nil : List A
  > | cons : A -> List A -> List A
  > 
  > def length (A : Type) (xs : List A) : MyNat :=
  >   List.rec A (fun (l : List A) => MyNat) MyNat.ze
  >     (fun (h : A) (t : List A) (ih : MyNat) => MyNat.su ih) xs
  > #eval length Bool (List.cons Bool Bool.true (List.cons Bool Bool.false (List.nil Bool)))
  > EOF
  $ mtt data.mtt
  Bool.false
  Bool.true
  MyNat.su (MyNat.su (MyNat.su (MyNat.su MyNat.ze)))
  MyNat.su (MyNat.su MyNat.ze)

A constructor and the former infer their derived types:

  $ cat > types.mtt <<'EOF'
  > inductive List (A : Type) : Type :=
  > | nil : List A
  > | cons : A -> List A -> List A
  > #check List
  > #check List.cons
  > EOF
  $ mtt types.mtt
  List : Type -> Type
  List.cons : (A : Type) -> A -> List A -> List A

A bare constructor name is not in scope — constructors must be qualified:

  $ cat > bare.mtt <<'EOF'
  > inductive Bool : Type :=
  > | true : Bool
  > | false : Bool
  > #check true
  > EOF
  $ mtt bare.mtt
  bare.mtt:4:8: unbound variable: true
  [1]

Strict positivity: the inductive may appear only as a direct recursive field.

  $ cat > bad_pos.mtt <<'EOF'
  > inductive Bad : Type :=
  > | mk : (Bad -> Bad) -> Bad
  > EOF
  $ mtt bad_pos.mtt
  bad_pos.mtt:1:1: type error: constructor mk: Bad may occur only as a direct recursive field, not inside Bad -> Bad (strict positivity)
  [1]

A constructor must construct the inductive it belongs to:

  $ cat > bad_result.mtt <<'EOF'
  > inductive Foo : Type :=
  > | mk : Bool
  > EOF
  $ mtt bad_result.mtt
  bad_result.mtt:2:8: unbound variable: Bool
  [1]

The Prop large-elimination restriction: a non-subsingleton proposition may
eliminate only into Prop.

  $ cat > large_elim.mtt <<'EOF'
  > inductive Or : Prop :=
  > | left : Or
  > | right : Or
  > #check Or.rec (fun (x : Or) => Nat) 0 0 Or.left
  > EOF
  $ mtt large_elim.mtt
  large_elim.mtt:4:1: type error: cannot eliminate the proposition Or into Type: only a subsingleton (at most one constructor, all fields proofs) may eliminate large
  [1]

A recursor must be fully applied (to be typed at all):

  $ cat > partial.mtt <<'EOF'
  > inductive Bool : Type :=
  > | true : Bool
  > | false : Bool
  > #check Bool.rec
  > EOF
  $ mtt partial.mtt
  partial.mtt:4:1: type error: cannot infer the type of a bare recursor; apply it to its parameters, motive, minor premises and target
  [1]
