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

## Eliminator style for sums (and later inductives)

Inductives eliminate through their generic recursor (`T.rec`, explicit
motive), the verbosity of which we worried would need `match`-style sugar.

**Status**: largely resolved. The recursor is implemented (qualified
`T.rec`, no bespoke `case`), and the elaborator now **infers the motive** —
a `_` in the motive position is recovered by abstracting the scrutinee out
of the goal (see `design.md`, Elaboration), so a dependent elimination no
longer writes its motive by hand. Remaining verbosity (binding the minor
premises) is what a `match`/equation compiler would absorb; that is tracked
in `todo.md`. **Revisit**: when `match` is taken on.

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

**Status**: open, deliberately deferred. The native `Eq` removed the old
motivating example; `sym`/`trans`/`subst` now live once in the prelude
(`std/prelude.mtt`). The remaining real test case: definitions meant to
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
