# Plan: replacing the hardcoded types with inductives

Working plan for retiring the kernel's built-in datatypes in favour of
surface-level `inductive` declarations, one at a time. The end state is a kernel
of just `Sort`, `Pi`, `Lam`, `App`, `Var`, `Ind`, `Ctor`, `Rec` (`Π`/`Sort`
stay primitive — they are not inductives). See `inductive-plan.md` for the
inductive machinery this builds on.

## Order of removal (by prerequisites)

1. **`Empty`** — pilot; no new kernel feature. (this document)
2. **`Sum`** — expressible now, but surfaces the implicit-argument question
   (`inl`/`inr` are bare and checking-directed; `Sum.inl` needs explicit params
   until the elaborator lands).
3. **`Nat`** — needs "blessed inductive" surface support (numeral literals
   desugaring to it, the printer folding successor chains to decimals).
4. **`Unit`, `Σ`** — need definitional η for single-constructor inductives
   ("records") + projections, else replacement silently weakens the theory.
   See `record-eta-plan.md`.
5. **`Eq`** — needs indexed inductive families; do last.

## Cross-cutting decision: availability under `prelude` opt-out

The builtins are lexer keywords, so they are in scope in *every* file, including
ones that open with the `prelude` opt-out. A prelude `inductive` is only in
scope where the prelude is loaded. This is fine for `Empty` (no opted-out file
uses it — `logic`/`church_*` use their own encodings), so the pilot needs no
new machinery. The decision escalates when a removed type is needed by an
opted-out file or by notation (numerals → `Nat`): at that point introduce a
small set of **always-loaded primitive inductives** that `prelude` does *not*
opt out of (a two-tier prelude).

---

# Pilot: move `Empty` into the prelude

Replace built-in `Empty`/`absurd` with `inductive Empty : Prop :=` (zero
constructors) and `Empty.rec`, declared in the auto-loaded `std/prelude.mtt`.

## Key insight — Prop-scrutinee irrelevance

`examples/empty.mtt` asserts `#check_equal (absurd A h1) (absurd A h2)` with
`axiom A : Type` and distinct `axiom h1 h2 : Empty`. Since the result type `A`
is not a `Prop`, this holds *only* because the two `Empty` proofs are
irrelevant — which the hardcoded `absurd` conversion special-cases (it compares
motives and ignores the proofs).

The generic recursor must do the same. Today the `Rec` case of `conv_neutral`
compares the two stuck majors *structurally* (`conv_neutral n1 n2`), so distinct
proofs would read as unequal. Fix: compare the major **type-directedly** at the
inductive type, so a `Prop` scrutinee short-circuits via proof irrelevance:

```
let ind_ty = infer_neutral ctx n1 in        (* VInd (rind, params) *)
conv ctx ind_ty (Neutral n1) (Neutral n2) && <params, motives, minors agree>
```

For a `Prop` inductive (`sort_of = 0`) this is true by irrelevance (recovers
`absurd`); for a non-`Prop` one (e.g. `Nat`) `conv` falls through to the same
structural comparison as before. This is the only *new* capability the pilot
needs — everything else is deletion + migration. It is also a uniform
correctness improvement (the recursor now respects irrelevance the way `case`
and `J` already do).

## Eliminator surface

Drop `absurd`; use `Empty.rec (fun _ => A) h`. (Keeping `absurd` as sugar would
be a keyword that secretly depends on a signature lookup — more special-casing
than the recursor it replaces. Only `examples/empty.mtt` uses the eliminator.)

## Phases (each compiles and tests green; stop for review)

1. **Generalize recursor conversion to respect Prop-scrutinee irrelevance.**
   The `conv_neutral` change above, plus a test (a `Prop` inductive, two stuck
   `.rec` on distinct proofs, asserted definitionally equal). No deletions —
   proves the generic machinery subsumes `absurd` before anything is removed.
2. **The swap.** Add `inductive Empty : Prop :=` to `std/prelude.mtt`; delete
   the built-in `Empty`/`Absurd` from `type.ml`/`value.ml`/`check.ml`(+`.mli`
   rules)/`ast.ml` and the `EMPTY`/`ABSURD` lexer keywords and parser rules;
   migrate `examples/empty.mtt` (`absurd A h` → `Empty.rec (fun _ => A) h`);
   audit tests and docs.

## Notes

- After removal `Empty` is an ordinary identifier resolved via the signature —
  in scope only where the prelude is loaded (the escalation trigger above).
- Sets the template; `Sum` is the natural next pilot (0 new kernel features, but
  raises the implicit-argument ergonomics question).
