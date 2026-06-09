# TODO

## Kernel (the trusted core)

Type theory implemented in `type.ml`/`value.ml`/`check.ml` (and
`inductive.ml`/`signature.ml`); everything here is checked, not elaborated.

- [ ] Local `let` expressions
- [ ] Mutual and nested inductives
- [ ] Full strict positivity: accept strictly-positive function-typed recursive
      arguments (`(Nat -> T) -> T`); currently only direct recursive fields
      `T params` are allowed
- [ ] Universe polymorphism (level-polymorphic defs; see questions.md); also
      needed for inductive `Sum`/`Σ`/`Eq` to form at the max of their
      components' levels rather than one fixed level
- [ ] Align `absurd` with Lean. Ours is ex falso —
      `absurd (A : Type) (h : Empty) : A`, i.e. Lean's `False.elim`. Lean's
      `absurd : a → ¬a → b` instead takes `p` and `¬p` and forms the
      contradiction itself; switching would leave raw ex falso as just
      `Empty.rec`. Wants implicit args + universe polymorphism for full parity
      (`b : Sort v`)

## Elaborator (type-directed surface → core)

Inference that sits above the kernel, turning concise surface terms into fully
explicit core terms. The settled architecture is in `design.md` (Elaboration);
the remaining work is below.

- [~] `match` expressions — surface sugar compiling to recursor (`T.rec`)
      applications; the kernel never sees it. Flat case analysis is implemented
      (one branch per constructor, `_` wildcard fields, and a trailing
      `| _ => …` catch-all; see `design.md`). Remaining:
      - [ ] the equation compiler proper: nested / multiple / overlapping
            patterns → nested single-level `.rec` calls
      - [ ] dependent (convoy) matching on **indexed** families: motive and
            index generalization (the MVP gates on `nindices = 0`)
      - [ ] inference-position `match`: synthesize the result type when there is
            no expected type, instead of requiring an annotation (today a `match`
            only elaborates in checking position — the motive is recovered from
            the goal by occurrence abstraction)
      - [ ] redundant / unreachable-branch detection: a `| _ => …` catch-all
            after the constructors are already covered (or, with the equation
            compiler, an overlapped pattern) is currently accepted silently;
            reject or warn (Lean errors)
      - [ ] structural recursion through `match` (a `brecOn`-style principle);
            general / well-founded recursion needs more still
      - [ ] a delaborator that prints a recursor back as `match` (the sugar is
            forward-only today — an elaborated `match` prints as its `T.rec`)

## Surface syntax

- [ ] `open`-style form to use a type's constructors unqualified (`nil` instead
      of `List.nil`); also lets the printer drop the qualifier when unambiguous
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
- [ ] Multi-line REPL input: the REPL reads one statement per line, so a
      multi-line declaration (e.g. an `inductive` with `|`-separated
      constructors) can only be entered on a single line; accumulate lines until
      a complete statement parses
- [ ] REPL niceties: command history (`ledit`/`rlwrap` note or linenoise dep)
      and a `:type` command (`:help`/`:env`/`:quit` already exist)

## Engineering

- [ ] Glued evaluation: remember folded and unfolded forms of defs, so
      output prints `ten` instead of ten applications of `succ`
- [ ] QCheck property tests: `parse ∘ print = id`, normalization idempotent
- [ ] Kernel boundary: abstract type of *checked* terms, constructible only
      via the checker
