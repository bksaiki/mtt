# TODO

## Core theory

- [ ] Local `let` expressions
- [x] Σ types (negative: pairs + projections `.1`/`.2`, surjective
      pairing in `conv`; `A × B` as the non-dependent case, `*` ascii;
      bare pairs infer at the constant family, Lean-style)
- [x] Binary sums `A + B` (first positive type: `case` recursor with
      explicit motive, ι-reduction, stuck `case` frames, and the Prop
      large-elimination restriction enforced)
- [x] `Unit` with definitional η (`Unit : Type`, deliberately not `Prop`:
      a `Prop` unit would collapse `Bool := Unit + Unit` by irrelevance)
- [x] `Empty` (`absurd`, subsingleton elimination: `Empty : Prop` but
      eliminates into any sort)
- [x] `Bool := Unit + Unit` — derived, not kernel (`examples/bool.mtt`);
      dependent elimination on it works via Unit-η
- [ ] A prelude: definitions (Bool, elim, ...) preloaded into every
      session, once an import mechanism exists
- [ ] Inductive types / naturals with eliminator (replaces Church encodings;
      sums + Σ + unit/empty are the warm-up)
- [x] Identity type (`Eq A x y` / `refl` / `J`) — explicit type arg for now
      (`=` infix awaits an elaborator); `sym`/`trans`/`cong`/`subst` and UIP
      in `examples/eq.mtt`
- [ ] Elaborator: infer implicit arguments (would give `x = y` infix over
      the explicit `Eq A x y`, motive inference for `case`/`J`, ...)
- [ ] Universe polymorphism (level-polymorphic defs; see questions.md)
- [ ] Holes / implicit arguments (elaboration with metavariables)

## Surface syntax

- [ ] Block comments: `/- ... -/` (nesting)
- [ ] Unicode identifiers (needs sedlex; ocamllex handles only fixed
      keyword literals)

## Errors & UX

- [ ] Better parse-error messages: say *what* was expected, not just
      `syntax error: unexpected token` (menhir `.messages` files); in file
      mode, optionally recover and report multiple errors per run
- [ ] Finer type-error locations within a statement: `Ast` nodes all carry
      spans now, so error sites can pass them piecemeal (e.g. the
      annotation's span when `infer_univ` rejects it in `Stmt.run`); the
      complete fix is an elaborator that keeps locations through checking
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
