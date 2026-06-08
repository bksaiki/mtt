# Elaborator plan

A working plan for adding a type-directed elaborator. Transient: each phase is
(roughly) a PR, and once the feature has landed this file folds into `design.md`
and is deleted, like the earlier `*-plan.md` docs.

## Why

The elaborator is the keystone for everything left on the roadmap. The
kernel-shrink program is fully blocked on it — the remaining builtins can't be
retired without it:

- `Sum` — `inl a` can't infer the other side `B`.
- `Σ` — `(a, b)` can't infer `A`/`B`.
- `Eq` — `refl` can't infer `A`/`x` (and `Eq` also needs indexed families).

Beyond removals, it unlocks implicit arguments (so `cong`/`sym`/`trans`/`subst`
take their type/endpoint args implicitly), named projections (`x.field`), `=`
infix, and motive inference for `case`/`J`/`T.rec`.

## Trust model and architecture

The elaborator is a **type-directed surface → core** pass that fills in the
arguments the kernel demands explicitly, producing fully-explicit core that the
trusted `Check` then **re-verifies**. This is the Lean/Rocq bargain: the
elaborator may be large and clever but is *untrusted* — a bug there is a
usability bug, not a soundness one, because the kernel re-checks its output. It
**reuses** the kernel's NbE (`Value.eval`/`quote`/`conv`); it does not
reimplement them.

So today's two steps — `Ast.to_term` (a syntactic, type-free translation) then
`Check` — become **elaborate-then-recheck**: a new frontend `Elab` module turns
`Ast.t` into explicit `Type.t`, and `Check` stays exactly as the authority that
verifies the result. `Elab` subsumes `to_term`'s scope resolution and sugar
expansion (it has to traverse the surface term anyway), so `to_term` is expected
to go away; `Parse.term_of_string*` re-routes through `Elab`.

The kernel stays untouched through Phases 1–2 and gains at most one
elaboration-only node in Phase 3 (see the open decision there).

## Key insight: checking-mode decomposition vs. unification

Much of the value needs **no metavariables**. When `inl a` or `(a, b)` is
*checked against a known expected type*, the constructor's parameters come
straight out of that type by decomposition — exactly how the current
bidirectional checker already handles the builtin `Inl`/`Pair`/`Refl`. Full
unification is only needed for *inference* position (no expected type) and for
*implicit function arguments*. That lets us front-load the removal payoff
(Phases 1–2) and defer the heavy machinery (Phase 3+).

## Phases

Each phase is intended as its own PR; the larger ones may split further.

### Phase 1 — Elaborator scaffold + constructor-argument inference — **done**

The foundation, metavariable-free.

- New `lib/elab.ml`/`.mli`: a bidirectional pass over `Ast.t` producing explicit
  core. `go ctx mode s` carries a `mode` (`Infer` | `Check ty`); `infer`/`check`
  are the entry points. It reuses the kernel's NbE (`Value.eval`/`quote`/
  `apply_closure`) and `Check.infer` rather than reimplementing typing.
- Constructor-argument inference: checking `T.c args` against expected
  `Ind T params` recovers the parameters from the expected type and elaborates
  only the fields, so a constructor application may omit them — `Box.wrap a`
  instead of `Box.wrap A a`. Inference position and explicit parameters keep
  today's behaviour.
- `Stmt.run` now elaborates-then-rechecks: `Def`/`Theorem` bodies (and
  `#check_equal`'s second term) elaborate in *checking* mode against the
  annotation, so omission also works in those positions and inside lambda
  bodies; the kernel `Check` re-verifies every elaborated term (re-check chosen
  over trusting the elaborator — cheap, and keeps the kernel the sole
  authority).

Two deviations from the original sketch, both deferred rather than dropped:

- **`to_term` retained, not folded in.** `Elab` handles only the application
  spine and binders natively (`Var`/`Field`/`Sort`/`Pi`/`Arrow`/`Lam`/`App`/
  `Ascribe`); every other surface form — the builtin `Σ`/`+`/`Eq` formers and
  their intro/elim, plus the `()`/numeral sugar — falls through to a catch-all
  that delegates the subtree to `Ast.to_term` (type-free, no inference inside).
  This keeps Phase 1 small and avoids duplicating the kernel's motive logic; the
  delegated set shrinks to nothing as Phases 2/5 remove those builtins, at which
  point `to_term` can go. `to_term` also still backs the inductive-declaration
  scope-check in `Stmt.elaborate_inductive`.
- **`Parse.term_of_string*` not rerouted.** Those stay on `to_term` (pure scope
  resolution, no typing); only `Stmt.run` invokes `Elab`, since elaboration
  needs a full `Check.ctx`, and routing the closed-term parser through it would
  make parsing raise type errors.

### Phase 2 — Remove `Σ` and `Sum`

Rides on Phase 1; resumes the kernel-shrink program. Two PRs.

#### Σ — **done**

- `Sigma (A : Type) (B : A → Type)` is now a prelude record with
  `@[notation sigma]`. The kernel's `Sigma`/`Pair`/`Fst`/`Snd` core+value nodes,
  `vfst`/`vsnd`, and their eval/quote/conv/infer cases are gone; `.1`/`.2` are
  the generic `Proj 0`/`Proj 1`, and η falls out of the record rule.
- Notation retargets `Σ`/`×`/`(a,b)` to the record. This needed a **richer
  printer hook**: the kernel's `sugar` callback now takes `recurse`/`names` and
  returns `(prec, text)`, so the frontend can render infix `×`/`Σ` and flatten
  tuples while the kernel stays notation-ignorant (it only provides recursion +
  parenthesization).
- Forward elaboration: pairs are the elaborator's job now (the type-free
  `to_term` cannot recover the parameters). `Ast.Pair` checks against the
  expected Σ (Phase-1 omission) or, inferring, defaults to the constant family
  (the old Pair-infer rule); `Σ`/`×` desugar to the applied former; `.1`/`.2`
  and pairs-under-them are handled in `Elab`. Consequently
  **`Parse.term_of_string*` now routes through `Elab`** (the Phase-1 deferral),
  in an empty closed-term context.
- **Universe regression (accepted):** the inductive is fixed at `Type`, so the
  builtin's `max`-rule cases are gone — `Σ (A : Type) ⇒ A` and a proof-relevant
  `p × q : Prop` no longer form. Restoring them (and a Prop-level `And`) waits on
  universe polymorphism. The sigma tests were rewritten accordingly.
- **Known transient gap:** a *bare pair literal* directly inside a still-builtin
  form that delegates to `to_term` (the `Eq`/`J` endpoints) raises "a pair
  requires a known type"; those become elaborator-native when `Eq` is removed
  (Phase 5). Not hit by the prelude or tests.

#### Sum — **done**

- `Sum (A B : Type)` is now a prelude inductive with `@[notation sum]` for the
  infix `+`. The kernel's `Sum`/`Inl`/`Inr`/`Case` core+value nodes, `vcase`, and
  their eval/quote/conv/infer cases are gone.
- **Design choice:** the `inl`/`inr`/`case` keywords were *dropped*, not
  retargeted. Every other inductive's constructors are qualified (`Nat.succ`,
  with no bare `succ`/`natrec` keyword), so `Sum`'s are too: `Sum.inl`/`Sum.inr`
  ride the ordinary constructor-application path (a checked injection drops its
  parameters via Phase-1 omission), and `Sum.rec` the recursor path — no
  sum-specific elaborator code at all. Only the symbolic `+` is notation. This
  shrinks the lexer/parser/`Ast` (three tokens, three `Ast` nodes) and aligns
  `Sum` with the other inductives; `examples/sum.mtt` and `bool.mtt` were
  rewritten to the qualified form.
- Same `Type`-fixed universe tradeoff as Σ: a proof-irrelevant disjunction
  `Or : Prop` awaits universe polymorphism. The generic recursor typing and
  large-elimination restriction are exercised in `test_ind.ml` rather than the
  old builtin-sum tests.

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

- Inference-position intros (`inl a` / `refl` with no expected type), `=` infix
  over `Eq`, named projections `x.field`, motive inference for
  `case`/`J`/`T.rec`.
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
- **`to_term`'s fate.** Expected to be subsumed by `Elab`; confirm the
  test/tooling callers (`Parse.term_of_string*`) re-route cleanly.

## Out of scope (separate future work)

- `match` / an equation compiler (surface sugar compiling to `T.rec`).
- Indexed inductive families (prerequisite for `Eq`, tracked alongside Phase 5).
- General/well-founded recursion beyond the recursor's structural IH.
