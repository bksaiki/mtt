# TODO

## Core theory

- [x] Top-level declarations (`axiom` / `def` / `theorem`) with δ for defs
- [ ] Check whole files (`mtt file.mtt`; parser needs a `list(item)` entry)
- [ ] Local `let` expressions
- [ ] Sigma types (pairs), unit, empty
- [ ] Inductive types / naturals with eliminator (replaces Church encodings)
- [ ] Universe cumulativity (or document the decision not to)
- [ ] Holes / implicit arguments (elaboration with metavariables)

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
