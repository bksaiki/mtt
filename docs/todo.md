# TODO

## Kernel (the trusted core)

Type theory implemented in `type.ml`/`value.ml`/`check.ml` (and
`inductive.ml`/`signature.ml`); everything here is checked, not elaborated.

- [ ] Local `let` expressions
- [ ] Indexed inductive families: the motive abstracts over indices and the
      target, ι matches index instances, and the recursor generalizes `J`.
      Unlocks `Vec`/`Fin` and an indexed `Eq`
- [ ] Mutual and nested inductives
- [ ] Full strict positivity: accept strictly-positive function-typed recursive
      arguments (`(Nat -> T) -> T`); currently only direct recursive fields
      `T params` are allowed
- [ ] Definitional η for single-constructor inductives ("records"): an η case in
      `conv` (eta-expand to `mk (proj₁ x) ...`) plus named projections — the
      self-contained step that lets `Unit` and `Σ` be replaced without losing
      their definitional η
- [ ] Universe polymorphism (level-polymorphic defs; see questions.md); also
      needed for inductive `Sum`/`Σ`/`Eq` to form at the max of their
      components' levels rather than one fixed level
- [~] Replace the inductively-describable builtins: move them into
      `std/prelude.mtt` as `inductive` declarations and delete their
      `Type.t`/`Value.t` constructors, eval/quote/conv/infer cases, and lexer
      keywords — collapsing the kernel to Sort/Pi/Lam/App/Var/Ind/Ctor/Rec
      (`Π`/`Sort` stay primitive), with the current builtin tests as the
      regression spec. `builtin-removal-plan.md` has the order and prerequisites.
      - [x] `Empty` (pilot): `inductive Empty : Prop`, `absurd` a prelude def
            over `Empty.rec`; generic recursor conversion now respects
            Prop-scrutinee irrelevance
      - [ ] `Sum` (surfaces the implicit-argument question for `inl`/`inr`)
      - [ ] `Nat` (needs numeral/printer "blessed inductive" support)
      - [ ] `Unit`, `Σ` (need record-η, above)
      - [ ] `Eq` (needs indexed families, above)

## Elaborator (type-directed surface → core)

Inference that sits above the kernel, turning concise surface terms into fully
explicit core terms.

- [ ] Implicit arguments: infer the type arguments the kernel demands
      explicitly — gives `x = y` infix over `Eq A x y`, motive inference for
      `case`/`J`/`T.rec`, and lets `inl a` / `refl` / `(a, b)` and inductive
      constructors omit their type/parameter arguments (the ergonomic
      prerequisite for replacing the builtins with inductives)
- [ ] Holes / metavariables (the unification engine the above is built on)
- [ ] `match` expressions — pure surface sugar that compiles to recursor
      (`T.rec`) applications; the kernel never sees it. Needs an equation
      compiler (nested/multiple/overlapping patterns → nested single-level
      `.rec` calls) and, for dependent matching once indices land, motive and
      index generalization (the convoy pattern). Structural recursion comes from
      the recursor's IH; general / well-founded recursion would need more (a
      `brecOn`-style principle)

## Surface syntax

- [ ] `open`-style form to use a type's constructors unqualified (`nil` instead
      of `List.nil`); also lets the printer drop the qualifier when unambiguous
- [ ] "Blessed" inductives in the surface: numeral literals desugaring to a
      designated `Nat`, the printer folding its successor chains to decimals,
      and `+`/`×`/`=` notation expanding to the chosen inductives (the parser
      and printer must know which inductive is "the" Nat/Sum/Σ/Eq; the `=` case
      also needs the elaborator's implicit-argument inference)
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
