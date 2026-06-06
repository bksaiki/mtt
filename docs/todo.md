# TODO

## Core theory

- [x] Top-level declarations (`axiom` / `def` / `theorem`) with δ for defs
- [x] Check whole files (`mtt file.mtt`)
- [ ] Local `let` expressions
- [ ] Sigma types (pairs), unit, empty
- [ ] Inductive types / naturals with eliminator (replaces Church encodings)
- [x] Universe cumulativity (subsumption-only; products covariant in codomain)
- [ ] Identity type (`Eq` / `refl` / `J`) — internalizes `#check_equal`
      (today only the Leibniz encoding is expressible; see `examples/leibniz.mtt`)
- [x] `Prop`: impredicative bottom sort à la CoC (`Sort` hierarchy, `imax`
      Pi rule); `examples/logic.mtt` now lives at one level and proves the
      sum swap by elimination
- [x] Proof irrelevance for `Prop` (conversion is now type-directed:
      `conv ctx ty v1 v2`)
- [ ] Universe polymorphism (Leibniz `sym`/`trans` are unprovable without
      it: predicates can't return `Type 1`)
- [ ] Holes / implicit arguments (elaboration with metavariables)

## Surface syntax

- [x] Parameter telescopes: `def f (A : Type) (x y : A) : A := ...`
      (also on `axiom`/`theorem`)
- [x] Unicode alternatives: `Π`/`∏ (x : A) ⇒ B`, `→`, `⇒`, `λ`, `:=`
- [x] Line comments: `-- ...`
- [ ] Block comments: `/- ... -/` (nesting)
- [ ] Unicode identifiers (needs sedlex; ocamllex handles only fixed
      keyword literals)
- [x] Multi-binder groups in `fun`/Π/arrows: `λ (t f : A) ⇒ ...`,
      `(A B : Type) -> A -> B`
- [x] Type ascription `(t : A)` as a term (desugars to the typed identity)

## Errors & UX

- [ ] Source positions in errors (menhir `$loc` + `Lexing` positions)
- [ ] Recover gracefully from parse errors with a message, not just `parse error`
- [ ] Statement boundaries in files: a stray bare term is silently absorbed
      into the preceding declaration as an application (see `test/file.t`)
- [ ] REPL niceties: command history (`ledit`/`rlwrap` note or linenoise dep),
      `:type` / `:quit` commands

## Engineering

- [x] Decide cram-test fate: restored `test/repl.t` (REPL transcript test)
- [ ] Glued evaluation: remember folded and unfolded forms of defs, so
      output prints `ten` instead of ten applications of `succ`
- [ ] QCheck property tests: `parse ∘ print = id`, normalization idempotent
- [ ] Kernel boundary `.mli`: abstract type of checked terms once the API settles
- [x] CI (GitHub Actions: build + test on push)
