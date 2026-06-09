# TODO

## Kernel (the trusted core)

Type theory implemented in `type.ml`/`value.ml`/`check.ml` (and
`inductive.ml`/`signature.ml`); everything here is checked, not elaborated.

- [ ] Local `let` expressions
- [x] Indexed inductive families: the motive abstracts over the indices and the
      target, the recursor's spine carries index arguments before the major, and
      its ι rule recovers each recursive field's indices (baked into the
      `rec_head` skeleton) to form the induction hypothesis (see `design.md`,
      Inductive types). Non-indexed types are the `indices = []` case; surface
      `inductive Vec (A : Type) : Nat -> Type := …` (see `examples/vec.mtt`).
      This retired the last builtin: `Eq` is now a prelude indexed inductive
      whose recursor `Eq.rec` is based-path induction (below). Motive inference
      does not yet cover indexed recursors (their motive must be written out);
      `=` is surface sugar and `rfl` an ordinary prelude def, with the eliminator
      the plain `Eq.rec` (no `J` keyword)
- [ ] Mutual and nested inductives
- [ ] Full strict positivity: accept strictly-positive function-typed recursive
      arguments (`(Nat -> T) -> T`); currently only direct recursive fields
      `T params` are allowed
- [x] Definitional η for single-constructor inductives ("records"): an η case in
      `conv` comparing field projections, plus the positional `Proj` node — lets
      `Unit`/`Σ` be replaced without losing their η (see `design.md`). The
      surface positional `.i` projection landed with the `Σ` removal; named
      field projection `x.field` (resolving to the same `Proj`) followed.
- [ ] Universe polymorphism (level-polymorphic defs; see questions.md); also
      needed for inductive `Sum`/`Σ`/`Eq` to form at the max of their
      components' levels rather than one fixed level
- [x] Replace the inductively-describable builtins: move them into
      `std/prelude.mtt` as `inductive` declarations and delete their
      `Type.t`/`Value.t` constructors, eval/quote/conv/infer cases, and lexer
      keywords. **Done** — the kernel is now collapsed to
      `Sort`/`Π`/`λ`/`App`/`Var`/`Ind`/`Ctor`/`Rec` (the generic inductive
      machinery), with the former builtin tests as the regression spec. Each
      retired builtin below.
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
      - [x] `Sum`: a prelude `inductive Sum (A B : Type)` with `@[notation sum]`
            for the infix `+`. The injections and eliminator are the *qualified*
            `Sum.inl`/`Sum.inr`/`Sum.rec` (the `inl`/`inr`/`case` keywords are
            gone — every inductive's constructors are qualified, like
            `Nat.succ`); a checked injection drops its parameters via the
            elaborator. Deleted the `Sum`/`Inl`/`Inr`/`Case` core+value nodes,
            `vcase`, and their eval/quote/conv/infer cases. **Fixed at `Type`**,
            like `Σ`: a proof-irrelevant disjunction `Or : Prop` awaits universe
            polymorphism
      - [x] `Σ`: a prelude record `inductive Sigma (A : Type) (B : A → Type)`
            with `@[notation sigma]`; `(a,b)`/`×`/`Σ` retarget to it (the
            elaborator recovers the parameters), `.1`/`.2` become the generic
            `Proj 0`/`Proj 1`, and η comes from the record rule. Deleted the
            `Sigma`/`Pair`/`Fst`/`Snd` core and value nodes, `vfst`/`vsnd`, and
            their eval/quote/conv/infer cases. **Fixed at `Type`**: a Σ ranging
            over the universe (`Σ (A : Type) ⇒ A`) or a proof-irrelevant pair of
            Props (`p × q : Prop`) no longer forms — that needs universe
            polymorphism (above), as does a Prop-level `And`
      - [x] `Eq`: a prelude indexed inductive
            `inductive Eq (A : Type) (x : A) : A -> Prop := | refl : Eq A x x`
            with `@[notation eq]`; `x = y` is the applied former (type inferred)
            and `rfl` a prelude def `Eq.refl A x` over its constructor (printed
            back as `rfl`). Its recursor `Eq.rec` is based-path induction, used directly
            (no `J` keyword) — its parameters/index recovered from the major.
            Deleted the `Eq`/`Refl`/`J` core+value nodes, `vj`, and their
            eval/quote/conv/infer cases — the last builtin gone. **Fixed at
            `Type`** like `Σ`/`Sum`: equality *of types* (`Unit = Unit`) no longer
            forms, pending universe polymorphism

## Elaborator (type-directed surface → core)

Inference that sits above the kernel, turning concise surface terms into fully
explicit core terms. Its mirror — the delaborator (core → surface) — lives with
the notation registry under Surface syntax; the two share that registry. The
settled architecture is in `design.md` (Elaboration); what is done and what
remains is below.

- [x] Constructor-argument inference in *checking* position: a constructor
      application checked against its inductive omits the leading parameters
      (`Box.wrap a`, `(a, b)`, `Sum.inl a`), recovered from the expected type —
      the metavariable-free core of the elaborator
- [x] Holes / metavariables (the unification engine): a surface `_` becomes a
      metavariable solved by unification and zonked away before the kernel
      re-checks. The kernel stays pristine — an inert `Meta` node only;
      the metacontext, `unify`, and `zonk` live in a functional `lib/meta.ml`
      threaded by `Elab` (which does its own meta-aware type synthesis).
      Non-contextual + scope-checked; only unapplied metas solved so far
- [x] Implicit arguments: `{x : A}` binders, with visibility a
      kernel-inert `icit` flag on `Pi`/`Lam` (carried but ignored by conv/infer,
      like the binder name — the Lean design). The elaborator inserts a fresh
      metavariable for each leading implicit binder when an explicit argument
      follows, solving it by unification; the prelude's `cong`/`symm`/`trans`/
      `subst` now take their type/endpoint arguments implicitly. Expected-type
      insertion and the `@f` escape are below
- [x] `x = y` infix over `Eq`: a new `eq_term` parser level (looser
      than `+`/`×`, tighter than `->`, non-associative) producing `Ast.EqInfix`;
      the elaborator synthesizes the type from the left side, and the
      delaborator prints `Eq A x y` as `x = y`. `:=` is now the sole
      definition/inductive separator (`=` is equality)
- [x] Recursor motive inference: a hole `_` motive on a **non-indexed** recursor,
      in checking mode, is inferred by **abstracting the major premise out of the
      goal** (`P := λ x ⇒ goal[major↦x]`) — one core `abstract`/`lift` primitive
      (occurrence generalization on normal forms), no higher-order unifier. The
      prelude's `add`/`mul`/`pred`/`add_zero`/… write `_` for their `Nat.rec`
      motives. An indexed recursor (`Eq.rec`) would also abstract the indices —
      not done — so its motive is written out
- [x] Recursor parameter/index recovery: a recursor's parameters and indices may
      be written `_` and are recovered from the major premise's type
      (`Eq.rec _ _ P d _ p`, `Vec.rec _ P z s _ xs`); an explicit argument is
      elaborated as written and re-checked. The prelude's equality toolkit uses
      it
- [x] Expected-type-driven implicit insertion: when a term of fully-implicit
      type `{a : A} -> …` is *checked* against a goal that is not itself an
      implicit `Pi`, the `coerce` step inserts fresh metavariables for the
      leading implicits and unifies the result against the goal (gated on having
      inserted ≥1 meta, so meta-free terms are untouched). Applied at a spine's
      tail and at bare `Var`/named-projection leaves. This let `rfl` move into the
      prelude as `def rfl {A : Type} {x : A} : x = x := Eq.refl A x`, retiring the
      `rfl` keyword and its special elaborator case (the `=` infix stays sugar)
- [x] Remaining surface inference, retiring `Ast.to_term`: inference-position
      constructor intros (`Box.wrap a` solves the parameter from the field; a
      genuinely-undetermined one like `Sum.inl a` errors), named projections
      `x.field` (alongside positional `.1`/`.2`), and an `@f` escape that passes
      every argument explicitly (suppressing implicit insertion). With these
      `Elab` covers every surface form — `()` and numerals included — so the
      type-free `Ast.to_term` is **deleted**: `Elab` is the sole surface → core
      pass, used even for inductive declarations (`Stmt.elaborate_inductive`)
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
        check). *Done for all roles: `unit`/`nat`/`sigma`/`sum`/`eq`* (the `eq`
        role registers the equality inductive, now that `Eq` is no longer a
        builtin — see the Eq removal above).
      - **forward** (parser/`Elab`): `()`→`Unit.unit` *(done)*,
        `2`→`succ (succ zero)` *(done)*, `A × B`/`Σ`/`+` → the registered
        inductive applied *(done)*; `x = y` → the `Eq` former, type inferred
        *(done)* (`rfl` is no longer notation — it is an ordinary prelude def)
      - **reverse** (a **delaborator** — the elaborator's mirror, core → surface;
        for now realized as the kernel printer parameterized by a generic
        notation config, not a separate rewriter): the registered unit ctor →
        `()` *(done)*, succ-chains of the registered `Nat` → decimals *(done)*,
        applied `Sigma`/`Sum` formers → infix `×`/`Σ`/`+` and tuples *(done)*;
        applied `Eq` former → infix `x = y` and its constructor → `rfl`
        *(done)* (a stuck `Eq.rec` still prints in full)
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
