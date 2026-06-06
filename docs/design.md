# Design

A minimal dependent type theory: Π types and a predicative universe
hierarchy, checked with normalization by evaluation (NbE).

## Pipeline

```
string ─parse─▶ Ast.t ─to_term─▶ Type.term ─eval─▶ Value.t ─quote─▶ Type.term ─pp─▶ string
       lexer.mll        scope             value.ml          value.ml         type.ml
       parser.mly       check (ast.ml)
```

Type checking (`check.ml`) sits on `Type.term` and decides equality on
`Value.t`.

## Representations

One unified syntax for terms and types (`Type.term`) — in a dependent
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

Definitional equality (`conv`, on values):

- **β** — already performed by evaluation
- **η** — for functions, lambda-vs-neutral case applies both to a fresh var
- **α** — free (de Bruijn)
- **δ** — `def`s unfold eagerly: a defined name is bound in the env to its
  value, so evaluation replaces it (no `Const` constructor, no kernel
  lookup). Upgrade path if unfolded output hurts: glued evaluation.
- no universe cumulativity: `Type i : Type (i+1)` exactly (Russell-style);
  Π lands in `Type (max i j)` (predicative)

## Top-level declarations

A program is a telescope of declarations, each scoping over the rest, so a
declaration just extends the checking context (`stmt.ml`, which holds both
the statement type and its processor, per the module-per-concept convention):

- `axiom x : A` — `bind`: a fresh neutral, stuck forever
- `def x [: A] = t` — `define`: bound to `t`'s value, unfolds (δ)
- `theorem x : A = t` — proof checked, then `bind`: opaque (Qed-style);
  a theorem behaves exactly like an axiom whose obligation was discharged

## Conventions

- One module per concept, type named `t` (exception: `Type.term`, since
  `Type.t` reads as "types only").
- No `.mli` files while the design moves; planned kernel boundary later.
- Tests: `ppx_expect` snapshot tests per module (`dune promote` workflow);
  expected strings are always promoted, never hand-typed.
