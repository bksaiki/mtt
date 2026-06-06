# TODO

## Core theory

- [ ] Local `let` expressions
- [ ] Sigma types (pairs), unit, empty
- [ ] Inductive types / naturals with eliminator (replaces Church encodings)
- [ ] Identity type (`Eq` / `refl` / `J`) — internalizes `#check_equal`
      (today only the Leibniz encoding is expressible; see `examples/leibniz.mtt`)
- [ ] Universe polymorphism (Leibniz `sym`/`trans` are unprovable without
      it: predicates can't return `Type 1`)
- [ ] Holes / implicit arguments (elaboration with metavariables)

## Surface syntax

- [ ] Block comments: `/- ... -/` (nesting)
- [ ] Unicode identifiers (needs sedlex; ocamllex handles only fixed
      keyword literals)

## Errors & UX

- [ ] Source positions in errors (menhir `$loc` + `Lexing` positions)
- [ ] Recover gracefully from parse errors with a message, not just `parse error`
- [ ] Statement boundaries in files: a stray bare term is silently absorbed
      into the preceding declaration as an application (see `test/file.t`)
- [ ] REPL niceties: command history (`ledit`/`rlwrap` note or linenoise dep),
      `:type` / `:quit` commands

## Engineering

- [ ] Glued evaluation: remember folded and unfolded forms of defs, so
      output prints `ten` instead of ten applications of `succ`
- [ ] QCheck property tests: `parse ∘ print = id`, normalization idempotent
- [ ] Kernel boundary: abstract type of *checked* terms, constructible only
      via the checker
