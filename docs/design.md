# Design

A small dependent type theory in the Calculus of Constructions family:
Π and Σ types, binary sums, `Unit` and `Empty`, and an impredicative
`Prop` under a predicative cumulative `Type` tower — checked bidirectionally
with normalization by evaluation (NbE), type-directed conversion, and
definitional proof irrelevance.

This file records *settled* decisions; open questions live in
`questions.md`, agreed-on work in `todo.md`.

## Pipeline

```
string ─parse─▶ Ast.t ─to_term─▶ Type.t ─eval─▶ Value.t ─quote─▶ Type.t ─pp─▶ string
       lexer.mll        scope             value.ml          value.ml         type.ml
       parser.mly       check (ast.ml)
```

Type checking (`check.ml`) sits on `Type.t` and decides equality on
`Value.t`.

The trusted core — `type`/`value`/`check`/`inductive`/`signature` — is an
isolated library under `lib/kernel/` (`mtt_kernel`, left unwrapped so its
modules stay top-level). It is location-free and self-contained; the frontend
in `lib/` (lexer, parser, `ast`, `stmt`, `prelude`) depends on it, never the
reverse — so the dependency arrow enforces the layering.

## Representations

One unified syntax for terms and types (`Type.t`) — in a dependent
theory "is a type" is a judgment, not a syntactic class. Three layers:

| layer | module | variables | binders |
|---|---|---|---|
| surface | `ast.ml` | strings | names |
| core syntax | `type.ml` | de Bruijn **indices** | name *hints* (display only) |
| semantic values | `value.ml` | de Bruijn **levels** (in neutrals) | closures `{env; body}` |

- Indices in syntax make α-equivalence structural; hints are never read by
  algorithms, only by the printer (which freshens with primes on collision).
- Levels in values mean quoting under binders needs no shifting:
  index = `level_count - level - 1`.
- There is **no substitution function**: β is closure application
  (`eval (arg :: env) body`), and `B[a/x]` in the App rule is the same
  closure application.

## Evaluation (NbE)

`eval : env -> term -> value` is a standard environment interpreter.
Stuck variables become *neutral* spines (`x a₁ ... aₙ`), which is what
lets evaluation proceed under binders on open terms.
`quote : level -> value -> term` reads back β-normal forms by applying
closures to fresh neutrals. `normalize = quote 0 ∘ eval []`.

## Type checking

Bidirectional: `infer` synthesizes, `check` verifies (lambda-vs-Pi rule,
plus subsumption via conversion). The context carries `env`/`types`/
`names`/`lvl` together; binders are bound to fresh neutrals.

Definitional equality (`conv`, on values, **type-directed**: values are
compared *at a type*, reconstructing spine types via `infer_neutral`):

- **β** — already performed by evaluation
- **η** — for functions, lambda-vs-neutral case applies both to a fresh var
- **α** — free (de Bruijn)
- **δ** — `def`s unfold eagerly: a defined name is bound in the env to its
  value, so evaluation replaces it (no `Const` constructor, no kernel
  lookup). Upgrade path if unfolded output hurts: glued evaluation.
- **η for `Unit`** — at type `Unit`, any two values are equal (every
  element is `()`); the same one-line pattern as proof irrelevance.
- **η for pairs** (surjective pairing) — at a Σ type, values are compared
  by their projections, the second at the family instantiated by the
  first; `p ≡ (p.1, p.2)` holds for neutral `p`.
- **ι** — `case` on an injection picks the branch (`vcase`), `J` on `refl`
  picks the diagonal (`vj`), and `natrec` recurses on `succ` (`vnatrec`,
  feeding the step its result on the predecessor — the induction
  hypothesis). These positive types have **no η**, so a stuck eliminator
  equals only another with convertible parts.
- **proof irrelevance** — at a type in `Prop`, any two values are equal
  (a one-line guard in `conv`, made possible by type direction); applies
  inside neutral spines, so `P h1 ≡ P h2` for any proofs `h1`, `h2`.
- **cumulativity** (subsumption rule only, via `sub`): `Sort i ≤ Sort j`
  when `i ≤ j` (Rocq-flavored: `Prop ≤ Type`); products invariant in
  domains, covariant in codomains. `infer` still returns principal types
  (`Sort i : Sort (i+1)` exactly, Russell-style). Σ types are negative
  (projections, η, no eliminator) and form at plain `max` — a Σ is a
  proposition only when both components are. A bare pair infers at the
  constant family (Lean-style: `(a, b) : A × B`); only checking against an
  expected Σ produces a dependent pair, since the family is not recoverable
  from the components

## Universes

CoC-style `Sort` hierarchy: `Prop = Sort 0` (impredicative), `Type i =
Sort (i+1)` (predicative tower). Π formation lands in `Sort (imax i j)`
where `imax i 0 = 0` — a product into a proposition is a proposition, no
matter the domain — and `max i j` otherwise. The whole difference between
`Prop` and `Type` is that one `imax` in `check.ml`'s Pi rule, plus proof
irrelevance in `conv`. `Empty` (now a prelude inductive with no constructors,
not a kernel primitive — see Inductive types) eliminates into any sort via its
recursor `Empty.rec`, which the prelude wraps as `absurd` — subsingleton
elimination, the degenerate (zero-constructor) case of the generic
large-elimination rule. For
sums the general large-elimination restriction is enforced: `+` forms at
plain `max` (so `p + q : Prop` is native disjunction), proof irrelevance
makes `inl h ≡ inr h'` at a `Prop`-sum, and therefore `case` on a
proposition must target `Prop` — a `Type`-valued motive could distinguish
definitionally equal proofs. `Eq A x y : Prop` is the other side of that
coin: a single-constructor subsingleton, so — like `Empty`/`absurd` — its
eliminator `J` carries *no* restriction and may land in any sort (this is
what lets `subst` transport between types). UIP holds definitionally for
free: `Eq` is a `Prop`, so proof irrelevance already equates all of its
proofs.

## Inductive types

`inductive T (params) : sort := | c : ty | ...` declares a parameterized
inductive type (no indices yet). It generalizes the hardcoded
`Nat`/`zero`/`succ`/`natrec` quadruple: a declaration introduces a type former
(`Ind`), constructors (`Ctor`), and a recursor (`Rec`), all driven by the
constructor signatures. These are mtt's first **global named constants** — a
signature `Σ` (`signature.ml`) keyed by name, beside the de Bruijn context.

- **Representation.** The NbE core stays signature-free: the *computational
  skeleton* (constructor index/arity and a per-constructor flag list marking
  recursive fields) is baked into the `Ctor`/`Rec` syntax nodes — all `vrec`
  (the generic ι-rule) needs. The full types (former, constructors, recursor)
  are derived from the spec (`inductive.ml`) and consulted only by the
  scope-checker and `infer`, which holds `Σ` in its context.
- **Recursor.** Fully dependent: the motive is `P : T params → Sort`, with one
  minor premise per constructor — a Π over the constructor's fields, an
  induction hypothesis `P fⱼ` after each recursive field, concluding in
  `P (c …)`. A recursor is motive-polymorphic, so (like `natrec`/`J`) it has no
  type as a constant; `infer` types a saturated application as a bespoke rule.
- **Surface.** Parameters are explicit; constructors and the recursor are
  qualified by their type (`Bool.true`, `Nat'.rec`), so constructor names need
  only be unique within a type. (`Nat`/`succ`/`Eq`/`Unit` are still reserved for
  the remaining builtins.)
- **Replacing the builtins.** `Empty` is the first hardcoded type retired this
  way: it is now `inductive Empty : Prop` in `std/prelude.mtt`, with `absurd`
  a prelude `def` over `Empty.rec`. The remaining inductively-describable
  builtins (`Sum`/`Nat`/`Unit`/`Σ`/`Eq`) follow; `builtin-removal-plan.md`
  tracks the sequence and prerequisites.
- **Soundness gates** (`check.ml`): strict positivity — the inductive may occur
  only as a *direct* recursive field `T params`, never under an arrow or nested
  (more conservative than full strict positivity, a later extension);
  predicativity — a field's sort fits the inductive's, except for an
  impredicative `Prop`; and the large-elimination restriction — a `Prop`
  inductive eliminates into a larger sort only when it is a subsingleton (≤ 1
  constructor, all fields proofs), generalizing the rule on `case`.

See `examples/inductive.mtt`; the design notes and deferred work (indices,
mutual/nested, `open`, replacing the builtins) live in `inductive-plan.md`.

## Errors and locations

Syntax errors (`Parse.Error`), scope errors (`Ast.Unbound_variable`), and —
in file mode — type errors are reported with `file:line:col` locations
(`loc.ml`). Precision matches what each layer knows: lex/parse/scope errors
carry exact spans (every `Ast` node is `{ loc; desc }`, and each `Stmt.t`
records its span); type errors are located at the failing *statement*, because the
core language is deliberately location-free — the kernel doesn't care
where a term came from. Finer-grained type-error positions arrive if/when
an elaborator (with a located surface language) sits between `Ast` and the
checker.

## Top-level declarations

A program is a telescope of declarations, each scoping over the rest, so a
declaration just extends the checking context (`stmt.ml`, which holds both
the statement type and its processor, per the module-per-concept convention):

- `axiom x : A` — `bind`: a fresh neutral, stuck forever
- `def x [: A] = t` — `define`: bound to `t`'s value, unfolds (δ)
- `theorem x : A = t` — proof checked, then `bind`: opaque (Qed-style);
  a theorem behaves exactly like an axiom whose obligation was discharged
- `inductive T params : sort := | c : ty | ...` — declares an inductive type;
  see the Inductive types section
- `prelude` — a directive (first statement only) that opts *out* of the
  auto-loaded standard library; see the Prelude section

## Prelude

`std/prelude.mtt` is a standard library written in mtt (functions, `not`, the
Eq toolkit `sym`/`trans`/`cong`/`subst`, Nat arithmetic and lemmas — all
axiom-free). A dune rule embeds it into the binary as a string constant
(`prelude_data.ml`), so there is no runtime path lookup. It is loaded
**automatically** (`Prelude.load` folds `Stmt.run` over the
parsed source into the starting context). A file/REPL opts out by opening
with the `prelude` directive — a bare environment, for the prelude's own
source and from-scratch encodings (the examples in `church_*`, `logic`).
Loading is lazy: the *driver* (`main.ml`) inspects the first statement and
only loads when it is not `prelude`, so an opted-out file never pays for it;
a `prelude` anywhere but first is an error. (`Stmt` sits below
`Parse`/`Prelude`, so it cannot load — hence the driver owns this, and
`Stmt.run` treats the `Prelude` marker as a no-op.)

## Conventions

- One module per concept, type named `t`.
- Every library module has an `.mli`; doc comments live there (odoc and
  editor hover read them), `.ml` files keep implementation notes. `Check`
  hides its conversion internals (`conv_ty`, `conv_neutral`, `sort_of`,
  `sub`); the syntax/value types stay concrete — they're the shared
  vocabulary, not an implementation detail.
- Tests: `ppx_expect` snapshot tests per module (`dune promote` workflow);
  expected strings are always promoted, never hand-typed.
