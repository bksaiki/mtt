# TODO

## Core theory

- [x] Top-level declarations (`axiom` / `def` / `theorem`) with δ for defs
- [x] Check whole files (`mtt file.mtt`)
- [ ] Local `let` expressions
- [ ] Sigma types (pairs), unit, empty
- [ ] Inductive types / naturals with eliminator (replaces Church encodings)
- [ ] Universe cumulativity (or document the decision not to)
- [ ] Holes / implicit arguments (elaboration with metavariables)

## Surface syntax

- [ ] Parameter telescopes: `def f (A : Type) (x y : A) : A = ...`
- [ ] Unicode alternatives: `∏`/`Π`, `→`, `⇒`, `λ`, `:=`
- [ ] Multi-binder groups in `fun`/Pi: `fun (t f : A) => ...`
- [ ] Type ascription `(t : A)` as a term (makes `assert_ty t = A` literally
      `#check (t : A)`; useful for annotating redexes generally)

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
