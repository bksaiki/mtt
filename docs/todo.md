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
- [x] Definitional η for single-constructor inductives ("records"): an η case in
      `conv` comparing field projections, plus the positional `Proj` node — lets
      `Unit`/`Σ` be replaced without losing their η (see `design.md`). The
      surface `.i` projection syntax lands with the `Σ` removal.
- [ ] Universe polymorphism (level-polymorphic defs; see questions.md); also
      needed for inductive `Sum`/`Σ`/`Eq` to form at the max of their
      components' levels rather than one fixed level
- [~] Replace the inductively-describable builtins: move them into
      `std/prelude.mtt` as `inductive` declarations and delete their
      `Type.t`/`Value.t` constructors, eval/quote/conv/infer cases, and lexer
      keywords — collapsing the kernel to Sort/Pi/Lam/App/Var/Ind/Ctor/Rec
      (`Π`/`Sort` stay primitive), with the current builtin tests as the
      regression spec. Order and prerequisites below; `Sum`/`Σ`/`Eq`
      introductions are gated on the elaborator.
      - [x] `Empty` (pilot): `inductive Empty : Prop`, `absurd` a prelude def
            over `Empty.rec`; generic recursor conversion now respects
            Prop-scrutinee irrelevance
            - [ ] possibly align `absurd` with Lean. Ours is ex falso —
                  `absurd (A : Type) (h : Empty) : A`, i.e. Lean's `False.elim`.
                  Lean's `absurd : a → ¬a → b` instead takes `p` and `¬p` and
                  forms the contradiction itself; switching would leave raw ex
                  falso as just `Empty.rec`. Wants implicit args + universe
                  polymorphism for full parity (`b : Sort v`)
      - [x] `Unit`: a prelude record `inductive Unit : Type := unit`, `()`
            sugar for `Unit.unit`, η from the record rule
      - [x] `Nat`: a prelude inductive `zero`/`succ` with `@[notation nat]`;
            decimal literals expand to succ-chains and the printer folds them
            back (the notation registry), `Nat.rec` replaces `natrec`. Deleted
            the `Nat`/`Zero`/`Succ`/`NatRec` core nodes, `vnatrec`, `step_ty`,
            and their eval/quote/conv/infer cases — the generic recursor
            subsumes them
      - [ ] `Sum` (surfaces the implicit-argument question for `inl`/`inr`)
      - [x] `Σ`: a prelude record `inductive Sigma (A : Type) (B : A → Type)`
            with `@[notation sigma]`; `(a,b)`/`×`/`Σ` retarget to it (the
            elaborator recovers the parameters), `.1`/`.2` become the generic
            `Proj 0`/`Proj 1`, and η comes from the record rule. Deleted the
            `Sigma`/`Pair`/`Fst`/`Snd` core and value nodes, `vfst`/`vsnd`, and
            their eval/quote/conv/infer cases. **Fixed at `Type`**: a Σ ranging
            over the universe (`Σ (A : Type) ⇒ A`) or a proof-irrelevant pair of
            Props (`p × q : Prop`) no longer forms — that needs universe
            polymorphism (above), as does a Prop-level `And`
      - [ ] `Eq` (needs indexed families, above)

## Elaborator (type-directed surface → core)

Inference that sits above the kernel, turning concise surface terms into fully
explicit core terms. Its mirror — the delaborator (core → surface) — lives with
the notation registry under Surface syntax; the two share that registry.

The phased build-out (each phase ≈ a PR) is planned in `elaborator-plan.md`.

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
- [~] Notation registry + delaborator ("blessed" inductives, done right).
      The `()`/numeral/`×`/`Σ`/`=`/`+` sugar is *notation* in both directions,
      and none of it is the kernel's checking/eval concern — only parse and
      print. Replace today's hardcoded strings (the `()` printer case, the
      `Unit`/`Sigma` lookups in `to_term`) with one registry:
      - [x] a **role registry** mapping notation roles (`unit`/`nat`/`sum`/
        `sigma`/`eq`) to the inductive that fills them, populated declaratively
        by an attribute on the declaration, e.g. `@[notation unit] inductive
        Unit …`; registration is **one-shot** (no overwrite) and
        **shape-checked** (the `unit` role demands a single nullary constructor,
        `nat` demands `zero`/`succ`, …), so a malformed or duplicate binding is
        rejected. *Done for the `unit` and `nat` roles* (`@[notation unit]`/
        `@[notation nat]`, the `@[ ]` attribute surface, one-shot + shape
        check); `sum`/`sigma`/`eq` roles land with their respective builtin
        removals.
      - **forward** (parser/`to_term`): `()`→`Unit.unit` *(done)*,
        `2`→`succ (succ zero)` *(done)*, `A × B`/`Σ`/`=`/`+` → the registered
        inductive applied
      - **reverse** (a **delaborator** — the elaborator's mirror, core → surface;
        for now realized as the kernel printer parameterized by a generic
        notation config, not a separate rewriter): the registered unit ctor →
        `()` *(done)*, succ-chains of the registered `Nat` → decimals *(done)*,
        the relevant inductives → infix `×`/`+`/`=`
      - the kernel printer stays **faithful/plain** (`Unit.unit`,
        `Nat.succ (… Nat.zero)`, qualified ctors); the delaborator applies sugar
        in the frontend. This forces a decision on error messages: either accept
        plain kernel errors, or make `Type_error` carry the offending **terms**
        (not pre-rendered strings) so the driver can delaborate them — the latter
        is what lets the kernel stay entirely notation-ignorant. Pairs naturally
        with the elaborator (forward) since they share the registry.
      - [x] **rendering decision: option 3, done.** `Error.Type_error` (in the
        small kernel `Error` module) carries message *fragments* (`Text` |
        `Term of names * term`) with raw terms, not strings; the kernel quotes
        the offending values and formats no notation. The notation registry is
        gone from the kernel entirely — no `notation` type, no `Check.ctx` field;
        the printer (`Type.pp_in`) takes only a generic `sugar : t -> string
        option` hook. The registry (`Notation.t`) lives in the frontend
        (`Notation` module), threaded alongside the kernel context in a
        `Stmt.session`; output (`Notation.show`), errors
        (`Notation.render_error`), and the forward `()`/numeral parse all run
        there. `Check.show` stays as the kernel's plain faithful view. The kernel
        is fully notation-ignorant.
- [x] Print `Unit.unit` as `()` — now via the notation registry above (the
      `@[notation unit]` ctor, folded by the printer's notation config); the
      hardcoded `Unit.unit` printer case and `to_term` lookup are gone.
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
