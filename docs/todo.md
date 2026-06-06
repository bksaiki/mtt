# TODO

## Core theory

- [ ] `let` definitions (top-level and local) — introduces δ-reduction;
      REPL gains `def x = ...`-style state
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

- [ ] Decide cram-test fate: restore `test/repl.t` or remove `(cram ...)` config
- [ ] QCheck property tests: `parse ∘ print = id`, normalization idempotent
- [ ] Kernel boundary `.mli`: abstract type of checked terms once the API settles
- [ ] CI (GitHub Actions: build + test on push)
