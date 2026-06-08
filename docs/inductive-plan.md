# Plan: inductive types

Working plan for the inductive-types PR. Scope decisions are settled (see
"Decisions"); this file is the reference for the phased implementation and
will be folded into `design.md` once the feature lands.

## Idea

mtt already hardcodes one instance of the general mechanism: the
`Nat`/`zero`/`succ`/`natrec` quadruple (and likewise `Eq`/`refl`/`J`,
`Sum`/`inl`/`inr`/`case`). An inductive declaration introduces exactly such a
quadruple, derived from the constructor signatures:

| piece | hardcoded `Nat` | generalized |
|---|---|---|
| type former | `Type.Nat` / `Value.Nat` | `Ind "Nat"` |
| constructors | `Zero`, `Succ` | `Ctor` heads |
| eliminator | `NatRec` | `Rec` head |
| ι-rule | `vnatrec` | generic `vrec`, driven by the spec |

The recursor's *type* and ι-rule are fully determined by the constructors: each
constructor contributes a minor premise — a Π over its arguments, with an
induction hypothesis `P aᵢ` for every recursive argument, concluding in
`P (c args)`. `natrec`'s step `Π (k : Nat) → P k → P (succ k)` is the special
case.

## The one new architectural element

mtt has no global named constants today: everything is de Bruijn, and
`def`/`axiom` work by extending the local context. An inductive's
former/constructors/recursor must be referenced by name everywhere after the
declaration, so this PR introduces a **global signature** `Σ` (name → spec),
alongside the local context `Γ`. `inductive` populates `Σ`; `def`/`axiom` are
unchanged.

The NbE core (`eval`/`quote`) stays free of any global lookup: the lightweight
*computational skeleton* (constructor index, arity, and a `bool list` marking
recursive arguments) is baked into the `Ctor`/`Rec` syntax nodes — all `vrec`
needs to fire ι. The full types (former, each constructor, the derived
recursor) live in `Σ` and are consulted only at the boundary: the scope-checker
(resolving a surface name to `Ind`/`Ctor`/`Rec`) and `infer` (which holds `Σ`
in `ctx`).

## Decisions

- **Parameters only, no indices.** Covers `Nat`, `Bool`, `List`, `Tree`,
  `Maybe`, `Sum`, `Unit`, `Empty`. The recursor generalizes `natrec`, not `J`;
  the motive is `P : Ind params → Sort`. Indices (`Vec`, `Fin`, and replacing
  the indexed `Eq`) are a follow-up PR.
- **Explicit parameters.** With no elaborator/implicits yet, parameters are
  ordinary explicit leading arguments to the former, every constructor, and the
  recursor (e.g. `cons A x (nil A)`, `List.rec A P …`). Implicit parameters
  await the elaborator already on the todo.
- **`Nat.rec` (dotted) eliminator.** A new lexer rule reads `.` followed by an
  identifier as a postfix dotted field (distinct from the `.1`/`.2` numeric
  projections); `to_term` requires the head to be an inductive and emits the
  `Rec` node. Constructors stay **bare** globals, so the only qualified name is
  the `rec` suffix (which never collides). Bare constructors ⇒ constructor
  names must be globally unique until namespacing arrives.
- **Strict positivity enforced** at declaration time. First cut allows
  *direct* recursive arguments (`T params`); a recursive occurrence anywhere
  else (under an arrow, nested) is rejected — soundly, but more conservatively
  than full strict positivity, which is a later extension.
- **Dependent eliminator**, large where sound: the Prop large-elimination
  restriction generalizes the one already in `Case` (a Prop inductive
  eliminates into any sort only if it is a subsingleton — ≤ 1 constructor with
  no data fields, like `Empty`/`Eq`).

## Phases (each compiles and tests green; stop for review between)

1. **Kernel computation.** `type.ml`/`value.ml` nodes `Ind`/`Ctor`/`Rec` +
   `eval`/`quote` + generic ι; `inductive.ml` spec data model + skeleton extraction.
   Tested by normalization. (`check.ml` typing stubbed.)
2. **Kernel typing.** `signature.ml` + a signature field in `ctx`; former /
   constructor / recursor type derivation; `infer`/`check`/`conv`/`sort_of`
   cases; universe rule + Prop large-elimination; strict positivity. Tested by
   type-checking.
3. **Surface & driver.** Lexer (`.rec`, `inductive`), parser, `Ast`, `to_term`
   via `Σ`, `Stmt.Inductive`, driver elaboration. `.mtt` files work.
4. **Examples & docs.** Re-derive `Bool`/`Maybe`/`List`/`Tree` via `inductive`
   (the hardcoded types stay, per scope); fold this plan into `design.md`, tick
   `todo.md`.

## Explicitly deferred

Pattern-matching / `match` sugar (elaborates to recursors), mutual & nested
inductives, full strict positivity (function-typed recursive arguments),
universe polymorphism, qualified/namespaced constructor names, indexed families,
and replacing the hardcoded `Nat`/`Eq`/`Sum`/`Σ`/`Unit`/`Empty`.
