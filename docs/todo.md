# TODO

## Core theory

- [x] Top-level declarations (`axiom` / `def` / `theorem`) with δ for defs
- [x] Check whole files (`mtt file.mtt`)
- [ ] Local `let` expressions
- [ ] Sigma types (pairs), unit, empty
- [ ] Inductive types / naturals with eliminator (replaces Church encodings)
- [x] Universe cumulativity (subsumption-only; products covariant in codomain)
- [ ] Holes / implicit arguments (elaboration with metavariables)

## Surface syntax

- [ ] Parameter telescopes: `def f (A : Type) (x y : A) : A = ...`
- [x] Unicode alternatives: `Π`/`∏ (x : A) ⇒ B`, `→`, `⇒`, `λ`, `:=`
- [ ] Unicode identifiers (needs sedlex; ocamllex handles only fixed
      keyword literals)
- [ ] Multi-binder groups in `fun`/Pi: `fun (t f : A) => ...`
- [x] Type ascription `(t : A)` as a term (desugars to the typed identity)

## Errors & UX

- [ ] Source positions in errors (menhir `$loc` + `Lexing` positions)
- [ ] Recover gracefully from parse errors with a message, not just `parse error`
- [ ] REPL niceties: command history (`ledit`/`rlwrap` note or linenoise dep),
      `:type` / `:quit` commands

## Engineering

- [x] Decide cram-test fate: restored `test/repl.t` (REPL transcript test)
- [ ] QCheck property tests: `parse ∘ print = id`, normalization idempotent
- [ ] Kernel boundary `.mli`: abstract type of checked terms once the API settles
- [x] CI (GitHub Actions: build + test on push)
