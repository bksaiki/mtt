# Indexed inductive families — plan

A working plan for adding **indexed** inductive families to the kernel.
Transient: each phase is (roughly) a PR, and once the feature has landed this
file folds into `design.md` and is deleted, like the earlier `*-plan.md` docs.

## Why

This is the last keystone of the kernel-shrink program. With indices, `Eq`
becomes an ordinary inductive

```
inductive Eq (A : Type) (x : A) : A → Prop := | refl : Eq A x x
```

whose recursor *is* `J` (based path induction). Retiring it deletes the final
builtin (`Eq`/`Refl`/`J` nodes, `vj`, their eval/quote/conv/infer cases),
collapsing the kernel to its irreducible core: `Sort`/`Π`/`λ`/`App`/`Var` plus
`Ind`/`Ctor`/`Rec`. Indices also unlock `Vec`/`Fin` and an indexed equality —
the canonical dependent-types showcase — and explain `J` retroactively as one
instance of the generic recursor.

## Parameters vs. indices (the whole distinction)

A parameter is **fixed** across the definition; an index **varies** per
constructor result.

```
inductive Vec (A : Type) : Nat → Type :=     -- A param, Nat an index arity
| nil  : Vec A 0
| cons : (n : Nat) → A → Vec A n → Vec A (succ n)
```

- The former is `Vec : (A : Type) → Nat → Type` — params, then an **index
  telescope**, then the sort.
- Each constructor's *result* pins specific index values (`Vec A 0`,
  `Vec A (succ n)`), and a recursive field may sit at a *different* index than
  the result (`Vec A n` inside `cons`, whose result is `Vec A (succ n)`).
- Indices are **not** constructor arguments: `cons n a v` takes `n`, `a`, `v`;
  its indices (`succ n`) are read off the result, not passed.
- The motive abstracts the indices *and* the target:
  `P : (i : Nat) → Vec A i → Sort`.
- The recursor takes the index values just before the major:
  `Vec.rec (A) (P) (nil-case) (cons-case) (i) (v : Vec A i) : P i v`.

So everything that was "`Ind params`" becomes "`Ind params indices`", and the
motive/recursor grow an index telescope between the parameters and the target.

## Data model (`inductive.ml`)

```
type spec = { name; params; indices; sort; ctors }   (* + indices telescope *)
type ctor = { cname; fields; result_indices }        (* + index instances of the result *)
type arg  = { aname; aty; recursive }                (* recursive now records the field's indices *)
```

- `indices : (string * Type.t) list` — the index telescope, in context `params`.
- `result_indices : Type.t list` — each constructor's result index terms, in
  context `params, fields`.
- a recursive field records the index terms it sits at (in context
  `params, earlier fields`) — needed by the recursor's ι rule (below). Likely
  `recursive : Type.t list option` (None = not recursive).

Derived types generalize mechanically:
- `former_type` = `(params) → (indices) → Sort`
- `ctor_type i` = `(params) → (fields) → Ind params result_indices`
- `minor_type i` = `(fields) → [P field_indices fieldⱼ →]… → P result_indices (c …)`

## The crux: the ι rule and the kernel's signature-free invariant

Today the NbE core (`value.ml`) fires ι without the signature: the
`Ctor`/`Rec` **skeletons** baked into the syntax nodes hold everything `vrec`
needs (constructor index, arity, and `recs : bool list list` flagging recursive
fields). When `vrec` hits a recursive field it recurses with
`rec params motive minors **field**`.

With indices, that recursive call needs the field's **index values** too:
`rec params motive minors **field_indices** field`. Those indices are
expressions over the constructor's earlier fields (`n` for `v : Vec A n`), and
values carry no types — so `vrec` cannot recover them from the field value.

**Decision (the one TCB-shaped choice): enrich the recursor skeleton.** Keep the
NbE core signature-free by baking the recursive fields' index expressions into
`Type.rec_head`:

```
type rec_head = { rind; nparams; nindices; recs }
and recs = field_rec list list                 (* per ctor, per field *)
and field_rec = Nonrec | Rec of Type.t list    (* index exprs over params, earlier fields *)
```

At ι time `vrec` evaluates each recursive field's index expressions against the
constructor's actual argument values, then makes the recursive call with them.
This is exactly how Lean bakes the recursive calls into a recursor's computation
rule; it preserves our invariant that the NbE core never consults `Σ`. The cost
is a richer skeleton (terms, not just booleans). *(The alternative — letting
`vrec` look up field types in the signature — would break the signature-free
core, so I'm not taking it unless you prefer it.)*

The stuck case also grows: a neutral `Rec` frame records
`params @ motive :: minors @ indices` before the stuck major, and `quote` /
`conv_neutral` compare the index args alongside the rest.

## Phases

### Phase 1 — Kernel: indexed families
`type.ml`/`value.ml`/`check.ml`/`inductive.ml`: the data model, derived types,
the generalized recursor rule (`infer_rec`, `minor_type`, `vrec`, the stuck
`Rec` frame and its `conv`/`quote`), and the soundness checks (kind-check the
index telescope; each constructor result is `Ind params idxs` with well-typed
indices; positivity unchanged except a recursive field may sit at any indices).
Non-indexed inductives are the `indices = []` special case, so all existing
tests stay green. New `test_ind.ml` cases build `Vec`/`Fin` directly in core.

### Phase 2 — Surface
`parser.mly`/`stmt.ml`: the result after `:` is an arrow-chain
`(index telescope) → sort` (decompose it); a constructor result is `Ind` applied
to params then index instances (record them). `examples/` gains `vec.mtt`.

### Phase 3 — Retire `Eq` (the payoff)
`Eq` becomes a prelude indexed inductive (`@[notation eq]`), `J` becomes
`Eq.rec`, `refl` becomes `Eq.refl`; delete the `Eq`/`Refl`/`J` core+value nodes,
`vj`, and their eval/quote/conv/infer cases. The elaborator routes `refl`/`=` to
the registered inductive (the last forward-notation gap), and the `eq` notation
role lands. Mirrors the `Σ`/`Sum` removals; the current `Eq` tests become the
regression spec.

## Out of scope (separate future work)

- Mutual and nested inductives.
- Full strict positivity (function-typed recursive arguments).
- `match` / an equation compiler (the convoy pattern needs indexed motives, so
  it builds on this).
