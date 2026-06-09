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

### Phase 3 — Metavariables, unification, holes — **done**

The inference engine, with Option A (metavariables live in the kernel's NbE).
The kernel became meta-aware; the frontend owns solving and zonks to meta-free
core before the trusted `Check` re-verifies, so soundness is unchanged. (The
metacontext's placement in the kernel is what the follow-up above will move out.)

Kernel:

- `Type.t` / `Value.t`-neutral gain `Meta of int`; the printer renders `?n`.
- A metacontext in `value.ml` (mutable, isolated): per-meta `{ ty; blvl; soln }`
  with `fresh_meta`/`meta_type`/`meta_blvl`/`meta_soln`/`solve_meta`/`reset_metas`,
  and `force` (unfold a solved meta at a value's head).
- `eval`/`quote`/`conv`/`sort_of`/`infer` force before matching a value's shape,
  so a solved meta behaves as its solution; `Check` *tolerates* metas (returns a
  meta's recorded type), since the elaborator reuses it mid-elaboration. The
  final re-check runs on zonked, meta-free core.

Frontend:

- A surface hole `_` (`Ast.Hole`) → `Elab.fresh_meta_core`, a fresh metavariable
  of the expected type. **Non-contextual** (no spine): a contextual meta applied
  to the context would not work, because the context's `def`s are bound to values
  (not variables) and so cannot form a unification pattern. A scope check
  (`Unify.scope_ok`, by birth level) keeps solutions sound under binders.
- `Unify.unify` (in `lib/unify.ml`): forces, solves the flex-rigid case
  `?m := t` (occurs + scope check), and walks rigid-rigid structurally; lenient
  elsewhere. The elaborator calls it at application arguments — but only when the
  domain still carries an unsolved meta, so a check-only argument like `refl`
  (whose type cannot be inferred) is untouched.
- `Elab.zonk` replaces each solved meta by its solution read back **as core** at
  the use-site level (reuse-safe de Bruijn — a raw metacontext solution is a
  value with absolute levels and cannot be stored). `Stmt.run` zonks every
  elaborated term and rejects any residual `Meta` (an unsolvable hole).

**Limitation (acceptable until Phase 4):** only unapplied metavariables are
solved, and only with a solution in scope at the meta's birth — enough for holes
pinned by a sibling argument or a local variable; higher-order / late-bound
cases are left unsolved (and reported).

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

## Planned follow-up: move the metacontext out of the kernel

Phase 3 lands with the metacontext as **mutable global state in `value.ml`** and
the kernel's NbE (`eval`/`quote`/`conv`/`force`) meta-aware. That works but puts
mutable state and an elaboration concern inside the TCB. A follow-up PR (after
Phase 3) will pivot to a cleaner split, keeping the kernel pristine:

- the kernel keeps only an **inert** `Meta` node — carried as an opaque neutral,
  never forced, no metacontext, no mutable state (the final `Check` only ever
  sees zonked, meta-free core);
- a new **`lib/meta.ml`** holds the metacontext as a *functional, caller-managed*
  value (`empty`/`fresh`/`solve`/`lookup`); `force`/`unify`/`zonk` move to the
  frontend, threading it;
- consequently `Elab` grows into a proper bidirectional inferer that returns
  `(core, type)` and threads the metacontext, instead of leaning on
  `Check.infer` for meta-containing terms.

This reuses the kernel's `eval`/`quote`/`apply` via the inert node (no NbE-
reduction duplication) while pushing all meta machinery into the untrusted
frontend — the most TCB-minimal design. Deferred only to keep the Phase-3 PR
focused.

## Open decisions

- **Metavariable representation (Phase 3).** *Decided: Option A* — a `Meta` form
  in the kernel `Type.t`/`Value.t`, reusing NbE (see Phase 3). Chosen over a
  separate elaborator NbE because duplicating the reduction engine is a larger,
  more error-prone cost than one meta-aware (and, post-zonk, meta-free) kernel.
  The metacontext's *placement* (kernel-global now, frontend-functional later)
  is the follow-up above.
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
