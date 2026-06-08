# Design

A small dependent type theory in the Calculus of Constructions family: Π types
and parameterized inductive types — with binary sums and propositional equality
still built in, and `Σ`/`Unit`/`Empty`/`Nat` now ordinary inductive declarations
in the prelude — under an impredicative `Prop` and a predicative cumulative
`Type` tower, checked bidirectionally with normalization by evaluation (NbE),
type-directed conversion, and definitional proof irrelevance.

This file records *settled* decisions; open questions live in
`questions.md`, agreed-on work in `todo.md`.

## Pipeline

```
string ─parse─▶ Ast.t ─elab─▶ Type.t ─eval─▶ Value.t ─quote─▶ Type.t ─pp─▶ string
       lexer.mll        elab.ml         value.ml          value.ml         type.ml
       parser.mly    (re-checked by check.ml)
```

Elaboration (`elab.ml`) is a type-directed surface → core pass that fills in the
arguments the kernel demands explicitly (e.g. a constructor's parameters), then
`check.ml` **re-checks** the core it produces — so the elaborator is untrusted,
in the Lean/Rocq tradition. Type checking sits on `Type.t` and decides equality
on `Value.t`. A residual type-free `Ast.to_term` (scope resolution only) still
backs inductive-declaration checking and the forms the elaborator does not yet
handle specially.

The trusted core — `type`/`value`/`check`/`inductive`/`signature`/`error` — is
an isolated library under `lib/kernel/` (`mtt_kernel`, left unwrapped so its
modules stay top-level). It is location-free, notation-free, and
self-contained; the frontend in `lib/` (lexer, parser, `ast`, `elab`,
`notation`, `stmt`, `prelude`) depends on it, never the reverse — so the
dependency arrow enforces the layering.

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
- **η for records** (surjective pairing, generalized) — at any
  single-constructor, non-recursive inductive, two values are equal iff their
  field projections are (the second compared at the family instantiated by the
  first, etc.). The 0-field case makes any two values equal — this is how `Unit`
  (a prelude record, `()` = `Unit.unit`) gets its η — and the dependent pair
  `Σ`/`(a,b)` is just the two-field case, so `p ≡ (p.1, p.2)` for neutral `p`
  falls out of the same rule.
- **ι** — `case` on an injection picks the branch (`vcase`), `J` on `refl`
  picks the diagonal (`vj`), and a recursor on a constructor picks the matching
  minor premise (`vrec`), feeding each recursive field its induction hypothesis
  (the recursor called on that field). These positive types have **no η**, so a
  stuck eliminator equals only another with convertible parts.
- **proof irrelevance** — at a type in `Prop`, any two values are equal
  (a one-line guard in `conv`, made possible by type direction); applies
  inside neutral spines, so `P h1 ≡ P h2` for any proofs `h1`, `h2`.
- **cumulativity** (subsumption rule only, via `sub`): `Sort i ≤ Sort j`
  when `i ≤ j` (Rocq-flavored: `Prop ≤ Type`); products invariant in
  domains, covariant in codomains. `infer` still returns principal types
  (`Sort i : Sort (i+1)` exactly, Russell-style). The dependent pair `Σ` is no
  longer a kernel type — it is the prelude record `Sigma`, formed by the generic
  inductive rule (fixed at `Type`, pending universe polymorphism). A bare pair
  still infers at the constant family (Lean-style: `(a, b) : A × B`), but that —
  like recovering the family by checking against an expected `Σ` — is now the
  elaborator's job (`elab.ml`), since neither is recoverable by the type-free
  scope pass

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
inductive type (no indices yet). It generalizes what used to be the hardcoded
`Nat`/`zero`/`succ`/`natrec` quadruple (now itself a prelude inductive): a
declaration introduces a type former (`Ind`), constructors (`Ctor`), and a
recursor (`Rec`), all driven by the constructor signatures. These are mtt's
first **global named constants** — a signature `Σ` (`signature.ml`) keyed by
name, beside the de Bruijn context.

- **Representation.** The NbE core stays signature-free: the *computational
  skeleton* (constructor index/arity and a per-constructor flag list marking
  recursive fields) is baked into the `Ctor`/`Rec` syntax nodes — all `vrec`
  (the generic ι-rule) needs. The full types (former, constructors, recursor)
  are derived from the spec (`inductive.ml`) and consulted only by the
  scope-checker and `infer`, which holds `Σ` in its context.
- **Recursor.** Fully dependent: the motive is `P : T params → Sort`, with one
  minor premise per constructor — a Π over the constructor's fields, an
  induction hypothesis `P fⱼ` after each recursive field, concluding in
  `P (c …)`. A recursor is motive-polymorphic, so (like `J`) it has no type as a
  constant; `infer` types a saturated application as a bespoke rule.
- **Surface.** Parameters are explicit; constructors and the recursor are
  qualified by their type (`Bool.true`, `Nat.succ`, `Nat.rec`), so constructor
  names need only be unique within a type. (`Eq` is still reserved for the
  remaining builtin.)
- **Records.** A single-constructor, non-recursive inductive is a record: it
  has positional field projections (`x.i`) and definitional η (see "η for
  records" above). Projections are a *primitive* node (`Proj`), not derived from
  the recursor — that is what buys definitional η and a clean ι (this is how
  Lean/Coq do records too); `ctor_head` carries `nparams` so `vproj` skips
  parameters, keeping the NbE core signature-free. The stuck projection's field
  type is recovered by the checker from the scrutinee's type, so the node needs
  only the index. The surface is positional (`x.1`); named projection
  (`x.field`) awaits the elaborator. This is what let `Unit` and the dependent
  pair `Σ` become ordinary inductives (`Σ`'s `.1`/`.2` are now just `Proj`, and
  the old primitive `Fst`/`Snd` are gone).
- **Replacing the builtins.** Retired so far: `Empty` (`inductive Empty : Prop`,
  with `absurd` a prelude `def` over `Empty.rec`), `Unit` (a prelude record,
  `()` sugar for `Unit.unit`, η from the record rule), `Nat` (a prelude
  inductive; decimal literals and succ-chain printing go through the notation
  registry below, and `Nat.rec` replaces the bespoke `natrec` — deleting the
  `Nat`/`Zero`/`Succ`/`NatRec` nodes and their eval/quote/conv/infer cases), and
  `Σ` (a prelude record `Sigma (A : Type) (B : A → Type)` with `@[notation
  sigma]`; `Σ`/`×`/`(a,b)` retarget to it, `.1`/`.2` become `Proj 0`/`Proj 1`,
  and the `Sigma`/`Pair`/`Fst`/`Snd` nodes and `vfst`/`vsnd` are deleted —
  **fixed at `Type`**, so a Σ over the universe or a proof-irrelevant pair of
  Props no longer forms, pending universe polymorphism). The remaining
  inductively-describable builtins (`Sum`/`Eq`) follow; `todo.md` tracks the
  sequence and prerequisites (their introductions are gated on the elaborator).
- **Soundness gates** (`check.ml`): strict positivity — the inductive may occur
  only as a *direct* recursive field `T params`, never under an arrow or nested
  (more conservative than full strict positivity, a later extension);
  predicativity — a field's sort fits the inductive's, except for an
  impredicative `Prop`; and the large-elimination restriction — a `Prop`
  inductive eliminates into a larger sort only when it is a subsingleton (≤ 1
  constructor, all fields proofs), generalizing the rule on `case`.

See `examples/inductive.mtt`; deferred work (indices, mutual/nested, `open`,
replacing the builtins) is tracked in `todo.md`.

## Notation

Surface sugar like `()` and decimal literals is *notation*, not kernel concern:
it touches only parse and print, never checking or evaluation. A declaration
opts an inductive into a notation **role** with an attribute,
`@[notation <role>] inductive …` — `unit` (its sole nullary constructor abbreviates
`()`), `nat` (a `zero`/`succ` pair, so decimal literals expand to succ-chains
and the printer folds them back), and `sigma` (a two-parameter record, so
`Σ (x : A) ⇒ B` / `A × B` abbreviate the applied former and `(a, b)` its
constructor). Registration is **one-shot** and **shape-checked**: the role
demands a particular constructor shape, and a malformed or duplicate binding is
a type error.

**The kernel is notation-ignorant** — it never names `Unit`/`Nat` and holds no
notation type at all. The registry lives entirely in the frontend (the
`Notation` module): a `Notation.t` mapping each role to the constructors that
fill it, threaded alongside the kernel context in a `Stmt.session`. It drives
both directions:
- **forward** — the parse pass (`Ast.to_term`, and `Elab` for the type-directed
  cases) reads it to resolve `()` → the unit constructor, `5` → a succ-chain of
  the registered `Nat`, and `Σ`/`×`/`(a,b)` → the registered `Sigma` former and
  constructor (the pair's parameters recovered by the elaborator);
- **reverse** — `Notation.sugar` is the hook the kernel printer (`Type.pp_in`)
  consults to fold a subterm into surface notation. Atomic sugar (`()`, a
  decimal) needs only the subterm, but infix/mixfix forms (`A × B`, a tuple)
  need to render their pieces, so the hook takes a `recurse` callback (and the
  binders in scope) and returns `(precedence, text)` — the kernel supplies the
  recursion and parenthesizes the result, but knows nothing of what is folded.

Everything user-facing is rendered in the frontend: `#check`/`#eval`/`:env`
output via `Notation.show`, error messages via `Notation.render_error`. The
kernel emits no notation — it raises `Error.Type_error` carrying message
*fragments* (`Text` | `Term of names × term`) with the offending terms quoted
but unrendered, and the frontend delaborates them. (`Check.show` remains the
kernel's *plain* faithful view, for internal use and debugging; the error
vocabulary itself lives in the small `Error` module.)

This is the "faithful core printer + frontend delaborator" split: the kernel
emits terms, the frontend delaborates. The longer arc — a full **delaborator**
(core → surface, the elaborator's mirror) sharing this registry, plus the
remaining `+`/`=` notation — is tracked in `todo.md`.

## Errors and locations

Syntax errors (`Parse.Error`), scope errors (`Ast.Unbound_variable`), and —
in file mode — type errors are reported with `file:line:col` locations
(`loc.ml`). Precision matches what each layer knows: lex/parse/scope errors
carry exact spans (every `Ast` node is `{ loc; desc }`, and each `Stmt.t`
records its span); type errors are located at the failing *statement*, because the
core language is deliberately location-free — the kernel doesn't care
where a term came from. An elaborator (`elab.ml`) now sits between `Ast` and the
checker, but does not yet thread the surface locations through into type errors;
finer-grained positions arrive when it does.

## Top-level declarations

A program is a telescope of declarations, each scoping over the rest, so a
declaration just extends the checking context (`stmt.ml`, which holds both
the statement type and its processor, per the module-per-concept convention):

- `axiom x : A` — `bind`: a fresh neutral, stuck forever
- `def x [: A] = t` — `extend`: bound to `t`'s value, unfolds (δ)
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

Builtins retired into inductives (`Empty`, `Unit`, `Nat`, …) live here, in the
auto-loaded prelude — so they, and the notation roles they register (`()`,
numerals), are *not* in scope for a file that opts out. That is fine while no
opted-out file needs them (today none do; `church_*`/`logic` use their own
encodings, and the prelude declares `Nat` before its own numeral-using lemmas).
When one eventually does, the escalation is a small always-loaded set of
primitive inductives that `prelude` does not opt out of (a two-tier prelude).

## Conventions

- One module per concept, type named `t`.
- Every library module has an `.mli`; doc comments live there (odoc and
  editor hover read them), `.ml` files keep implementation notes. `Check`
  hides its conversion internals (`conv_ty`, `conv_neutral`, `sort_of`,
  `sub`); the syntax/value types stay concrete — they're the shared
  vocabulary, not an implementation detail.
- Tests: `ppx_expect` snapshot tests per module (`dune promote` workflow);
  expected strings are always promoted, never hand-typed.
