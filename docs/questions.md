# Open design questions

Unresolved decisions, with context and the trigger that should reopen them.
(Settled decisions live in `design.md`; agreed-on work lives in `todo.md`.)

## Flat tuple projections (`t.3`)

Tuples are right-nested pairs, so flat indexing is not syntactic (the
desugaring of `.n` depends on arity) and is ambiguous even with types:
`A × A × (B × C)` is structurally identical to a 4-tuple. Lean resolves
this by fiat — the elaborator walks the type's `Prod` nesting greedily, so
a "triple ending in a pair" *is* a quadruple to `.i`. We could do the same
with a type-directed `Proj n` resolved in the checker (~30 lines, compiles
to `Fst`/`Snd` chains; no parser or kernel changes).

**Status**: rejected for now; `.n` for n ≥ 3 is a lexer error that teaches
`.2.2`. **Revisit**: when records/structures land (named fields dissolve
the question, as in Lean), or if `.2.2` chains get painful in examples.

## `True : Prop`?

`Unit : Type` deliberately (a `Prop` unit would collapse `Bool := Unit +
Unit` by irrelevance), so `logic.mtt` has no native ⊤ — trivial truth must
be encoded. Lean keeps both `Unit : Type` and `True : Prop` as separate
types.

**Status**: open; nothing has needed it yet. **Revisit**: if an example
wants ⊤ as a proposition.

## Singleton elimination, and Lean's `Eq` shape

mtt's `Eq` is `inductive Eq (A : Type) (x : A) : A → Prop := | refl : Eq A x x`
— the **first endpoint is a parameter**, so the constructor `refl` has no fields
and the generic recursor is *based-path* induction (`P : (y : A) → Eq A x y →
Sort`, `x` fixed), which is exactly Lean's `@Eq.rec`. Lean's *declaration*
instead makes both endpoints indices, with the point carried by the constructor
(`Eq : α → α → Prop`, `refl (a : α) : Eq a a`). (The surface term that builds it
is `rfl` either way.)

Adopting Lean's declaration shape in mtt is a **net regression** as the kernel
stands, for two reasons:

- **Large elimination breaks.** mtt's large-elim gate permits a `Prop` inductive
  to eliminate into `Type` only for a *subsingleton*, tested syntactically as
  "one constructor, all fields proofs." Lean-form `refl` carries a data field
  `a : A` (not a proof), so `Eq` flunks the test and `Eq.rec` into `Type` is
  rejected — killing `subst`/transport. (Verified.) mtt's current form has a
  zero-field constructor, so it passes trivially.
- **Different recursor.** mtt's recursor rule abstracts *every* index, so Lean's
  two-index declaration yields the *general* J (motive over both endpoints), not
  Lean's based-path `Eq.rec` (Lean specializes; mtt doesn't). The general J makes
  `subst` clunky (a function-valued motive) and isn't what motive inference
  recovers.

To make Lean's shape viable, the kernel would need the refined **singleton
elimination** criterion Lean/Coq use: a `Prop` inductive may eliminate large
when each constructor argument is a proof **or is determined by the indices**
(`refl`'s `a` is pinned by the result `Eq a a`). That generalizes beyond `Eq`
(`Acc`, equality-like families) and is a self-contained kernel improvement.

**Status**: deliberately not done. The current parameter encoding already gives
Lean's based-path `Eq.rec` with the crude subsingleton check, and `J` is gone in
favour of explicit `Eq.rec` (see below / `design.md`). **Revisit**: if we want
the general/HoTT J as the primitive, or the syntactic subsingleton check blocks
another genuinely-eliminable `Prop` family — then add singleton elimination
first.

## Eliminator style for sums (and later inductives)

Inductives eliminate through their generic recursor (`T.rec`, explicit
motive), the verbosity of which we worried would need `match`-style sugar.

**Status**: resolved. The recursor is implemented (qualified `T.rec`, no bespoke
`case`), the elaborator **infers the motive** (a `_` motive is recovered by
abstracting the scrutinee out of the goal), and `match` now absorbs the
remaining verbosity — `match e with | C x̄ ⇒ b … end` desugars to `T.rec` with
the minor premises bound by the branch patterns (see `design.md`, Elaboration).
The MVP is flat, non-indexed case analysis; the equation compiler and dependent
(convoy) match are tracked in `todo.md`. **Revisit**: when those land, or if the
forward-only sugar (no `match` round-trip in printing) becomes a pain.

## Statement boundaries in files

Statements have no terminator, so a stray bare term is silently absorbed
into the preceding declaration as an application (see `test/file.t`).
Options: a terminator (`.` à la Rocq, or newline-sensitivity), rejecting
top-level applications that span declaration keywords, or a heuristic
warning using the location machinery.

**Status**: open; documented footgun. **Revisit**: first time it bites
for real, or alongside parse-error recovery work.

## Universe polymorphism

Cumulativity has absorbed most everyday universe pressure. Full
polymorphism (levels as parameters, `imax` algebra on level expressions)
is the deepest rabbit hole on the board.

**Status**: open, deliberately deferred. Propositional equality (now a prelude
inductive) removed the old motivating example; `symm`/`trans`/`subst` live once
in the prelude (`std/prelude.mtt`). The remaining real test case: definitions
meant to
work at *every* level at once — e.g. the prelude's `subst` is fixed at
`P : A → Type`, so a `Prop`-valued transport needs a separate copy.
**Revisit**: when the prelude wants the same lemma at multiple sorts.

## Display of unfolded definitions

δ is eager: normal forms print fully unfolded (`#eval ten` shows ten
`suc`s). Glued evaluation (values remembering folded and unfolded forms)
is the standard fix and would also justify a real `Const` constructor.

**Status**: open; tracked as engineering work in `todo.md`, but the
design (glued values vs. printing-time refolding vs. accept it) is not
settled. **Revisit**: when example output becomes unreadable.
