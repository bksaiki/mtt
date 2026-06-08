# Elaborator plan

A working plan for the type-directed elaborator. Transient: each phase is
(roughly) a PR, and once the whole feature has landed this file folds into
`design.md` and is deleted, like the earlier `*-plan.md` docs. Phases 1–2 have
landed (their detail now lives in `design.md`); this file tracks what is left.

## Why

The elaborator is the keystone for the rest of the roadmap. The kernel-shrink
program was blocked on it — `Σ`/`Sum`/`Eq` can't be retired without inferring
the arguments their intro forms drop (`(a, b)` can't recover `A`/`B`; `refl`
can't recover `A`/`x`). Beyond removals it unlocks implicit arguments (so
`cong`/`sym`/`trans`/`subst` take their type/endpoint args implicitly), named
projections (`x.field`), `=` infix, and motive inference.

## Trust model and architecture (in place since Phase 1)

The elaborator is a **type-directed surface → core** pass that fills in the
arguments the kernel demands explicitly, producing fully-explicit core that the
trusted `Check` then **re-verifies** — the Lean/Rocq bargain: the elaborator is
*untrusted*, so a bug there is a usability bug, not a soundness one. It **reuses**
the kernel's NbE (`Value.eval`/`quote`, `Check.infer`/`conv`); it does not
reimplement them. So the old `Ast.to_term`-then-`Check` became
**elaborate-then-recheck** via the `Elab` module.

`Elab` is bidirectional (`go ctx mode s`, `mode = Infer | Check ty`) but
intervenes only where the expected type lets it drop an argument — constructor
applications and lambda bodies. Surface forms it does not special-case fall
through to `Ast.to_term` (the type-free scope/sugar pass), which therefore still
exists and also backs the inductive-declaration scope-check in
`Stmt.elaborate_inductive`. The kernel gains at most one elaboration-only node
in Phase 3 (see the open decision there).

## Key insight: checking-mode decomposition vs. unification

Much of the value needs **no metavariables**. When `(a, b)` is *checked against a
known expected type*, the constructor's parameters come straight out of that type
by decomposition. Full unification is only needed for *inference* position (no
expected type) and for *implicit function arguments*. That let us front-load the
removal payoff (Phases 1–2) and defer the heavy machinery (Phase 3+).

## Phases

Each phase is intended as its own PR; the larger ones may split further.

### Phase 1 — Elaborator scaffold + constructor-argument inference — **done**

`Elab` (the scaffold above) plus constructor-argument inference: a constructor
application checked against its own inductive may omit the leading parameters
(`Box.wrap a` for `Box.wrap A a`), recovered from the expected type. `Stmt.run`
elaborates-then-rechecks. See `design.md` (Pipeline, Inductive types).

### Phase 2 — Remove `Σ` and `Sum` — **done** (two PRs)

Both are now prelude inductives, **fixed at `Type`** (a Σ/sum over the universe,
or a proof-irrelevant pair/disjunction of Props, awaits universe polymorphism):

- **`Σ`** — the record `Sigma (A : Type) (B : A → Type)`, `@[notation sigma]` for
  `Σ`/`×`/`(a, b)`, `.1`/`.2` as the generic `Proj`. Needed a richer printer hook
  (`recurse`/`names` → `(prec, text)`) for infix/tuple rendering, and routed
  `Parse.term_of_string*` through `Elab` (pairs are type-directed).
- **`Sum`** — the inductive `Sum (A B : Type)`, `@[notation sum]` for the infix
  `+` only; its `Sum.inl`/`Sum.inr`/`Sum.rec` are ordinary qualified names (the
  `inl`/`inr`/`case` keywords were dropped, matching every other inductive), so
  no sum-specific elaborator code.

Both deleted their kernel nodes and machinery; the regression behaviour (generic
recursor, large elimination) now lives in `test_ind.ml`. Details in `design.md`.

### Phase 3 — Metavariables, unification, holes

The inference engine. **Has the one architectural decision (below).**

- A metacontext (store of solved/unsolved metas), Miller-pattern unification,
  and zonking; a surface hole `_` that elaborates to a fresh meta solved against
  its expected type.
- Self-contained and testable via `_`.
- **Size:** medium–large (unification is fiddly).

### Phase 4 — Implicit arguments

- `{x : A}` binder syntax; the elaborator inserts a fresh meta at each use site
  and solves it by unification.
- Lets the prelude's `cong`/`sym`/`trans`/`subst` (and user code) take their
  type/endpoint arguments implicitly — the big ergonomic win.

### Phase 5 — Remaining inference, and `Eq`

Several smaller PRs, built on Phases 3–4.

- Inference-position intros (`Sum.inl a` / `refl` with no expected type), `=`
  infix over `Eq`, named projections `x.field`, motive inference for `J`/`T.rec`.
- `Eq` removal — also needs **indexed inductive families** (a separate kernel
  feature, possibly its own track), so it is the last builtin to go.

## Open decisions

- **Metavariable representation (Phase 3).** Either a `Meta` node in the kernel
  `Type.t`/`Value.t`, used only during elaboration and rejected by `Check`
  (reuses all of NbE — the standard approach), or a separate elaborator
  representation that keeps the kernel pristine at the cost of duplicating
  NbE-with-metas. Given how hard we have pushed on kernel minimalism this is a
  real discussion; it does not block Phases 1–2.
- **Implicit-argument surface.** `{x : A}` binders (Agda/Lean-ish) is the
  expected choice; confirm at Phase 4.
- **`to_term`'s fate.** `Parse.term_of_string*` already routes through `Elab`;
  `to_term` survives only as `Elab`'s catch-all (for forms not yet special-cased)
  and the inductive-declaration scope-check. It can be retired once `Eq` is gone
  and `Elab` covers the last builtin forms.

## Out of scope (separate future work)

- `match` / an equation compiler (surface sugar compiling to `T.rec`).
- Indexed inductive families (prerequisite for `Eq`, tracked alongside Phase 5).
- General/well-founded recursion beyond the recursor's structural IH.
