# Plan: records (definitional η + projections)

Generalize the two hardcoded "negative" builtins — `Σ` (projections + surjective
-pairing η) and `Unit` (η: every element is `()`) — into **records**: single-
constructor inductives with field projections and definitional η. Once the
kernel has one record mechanism, `Unit`/`Σ` become prelude declarations and the
special forms (`Sigma`/`Pair`/`Fst`/`Snd`/`Unit`/`MkUnit`) are deleted. The next
step on the builtin-removal arc (see `builtin-removal-plan.md`).

## Decisions (settled)

- **A record is a single-constructor inductive with no recursive fields.**
  Covers `Unit` (0 fields), `Σ` (2 fields, second dependent), `A × B`, `And`.
  Single-constructor types *with* a recursive field keep only the constructor +
  recursor — no η or projections.
- **Projections are positional** (`.1`/`.2`/`.i`, 1-based surface → 0-based
  field index), resolved type-directedly by the checker. Named projections
  (`x.head`) need term-level name resolution from the scrutinee's type — an
  elaboration step we don't have — so they wait for the elaborator.

## What record-η is

For a record `T params := mk : (f₀ : F₀) → … → (fₙ : Fₙ) → T params`:

- **Projection** `πᵢ x : Fᵢ[params, π₀ x … π_{i-1} x]` (the field type, with
  earlier projections of *this* `x` substituted — exactly today's `Snd : B[p.1]`).
- **ι** `πᵢ (mk a₀ … aₙ) ≡ aᵢ`; a stuck projection on a neutral.
- **η** `x ≡ mk (π₀ x) … (πₙ x)`. Operationally `conv` compares two record
  values by their projections — generalizing the surjective-pairing case already
  in `conv`. The 0-field case (`Unit`) makes any two values equal.

## Representation

Projections are a **primitive** node, not derived from the recursor — going
through `T.rec` yields neither definitional η nor a clean ι on dependent
records (this is why Lean/Coq use primitive projections). It generalizes the
existing `Fst`/`Snd`:

- `Type.Proj of int * t` — field index and scrutinee. The index comes straight
  from the positional surface, so no signature is needed to build it.
- To reduce `πᵢ (mk params fields)` the evaluator must skip the parameters, so
  `Type.ctor_head` gains an `nparams` field (set by `Inductive.ctor_head`);
  then `vproj i (VCtor (h, args)) = List.nth args (h.nparams + i)`. A neutral
  scrutinee gives a stuck `Proj` neutral. The kernel stays signature-free.
- The stuck projection's *type* and the field name are recovered by the checker
  from the scrutinee's inferred type, so the node needs only the index. The
  printer renders a stuck projection positionally (`e.<i>`).

## Phases (each builds and tests green; stop for review)

1. **Kernel record machinery** (the capability; OCaml-tested, no surface — `.i`
   still means `Fst`/`Snd` for the builtin `Σ` until phase 2).
   - `type.ml`: `Proj` node, `nparams` on `ctor_head`, `occurs`/printer.
   - `value.ml`: stuck `Proj` neutral, `vproj`, `eval`/`quote`.
   - `inductive.ml`: `is_record`, `ctor_head` sets `nparams`, projection
     field-type helper.
   - `check.ml`: the `Proj` typing rule (require a record, validate the index,
     dependent field type); the record branch of the `VInd` case in `conv`
     (project-and-compare η), generalizing the `Sigma`/`Unit` η there;
     `infer_neutral` for the stuck `Proj`.
   - Tests (`test_ind`-style): a dependent-pair record — ι on each projection,
     η equating a neutral with its expansion and two neutrals, and a 0-field
     record making any two values equal (Unit-η).
2. **Surface + replace `Unit` and `Σ`.**
   - Lexer/parser: `.i` → `Proj (i-1, _)`; remove `Fst`/`Snd` and the `.digits`
     error (over-indexing becomes a checker error against the record's field
     count; `Σ` stays 2-field, so triples remain right-nested as today).
   - Prelude: `inductive Unit : Type := tt` and a dependent
     `inductive Sigma (A : Type) (B : A → Type) : Type := mk : (a : A) → B a → …`.
   - Notation, reusing the existing `Pair`/`Σ`/`×` rules retargeted to the
     record: `()` → `Unit.tt`; `A × B`/`Σ (x:A) ⇒ B` → the former applied to
     explicit args; `(a, b)` → `Sigma.mk` with the constant-family default
     inferred (the current Pair-infer rule, no general implicits needed).
   - Delete `Sigma`/`Pair`/`Fst`/`Snd`/`Unit`/`MkUnit` from the kernel and their
     `eval`/`quote`/`conv`/`infer` cases; migrate tests/examples; docs.

## Deferred

Named projections (`x.head`, needs the elaborator); η for recursive
single-constructor types; a dedicated `structure` keyword (the plain
`inductive` with one constructor suffices).
