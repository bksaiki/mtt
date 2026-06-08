# mtt

A small dependent type theory in the Calculus of Constructions family,
implemented in OCaml — a learning/research implementation, not a production
proof assistant. See `docs/design.md` for what the theory includes and why
it is built the way it is.

## Build and run

```sh
dune build           # build the library and the `mtt` binary
dune exec mtt        # start the REPL
dune exec mtt -- examples/nat.mtt   # check a file
dune test            # run the test suite (inline + cram + examples)
dune fmt             # format (CI enforces this on PRs)
```

The REPL reads one statement per line; `:help` lists the commands.

```
mtt> #check fun (A : Type) => fun (x : A) => x
fun (A : Type) => fun (x : A) => x : (A : Type) -> A -> A
mtt> :quit
```

`examples/` holds worked code for every feature (all checked by `dune test`).

## Layout

The source follows the `string → Ast → Type → Value` pipeline (diagram in
`docs/design.md`):

- `lib/lexer.mll`, `lib/parser.mly`, `lib/parse`, `lib/ast` — surface syntax
  and scope-checking to core terms.
- `lib/type`, `lib/value` — core syntax and semantic values (NbE:
  `eval`/`quote`/`normalize`).
- `lib/check` — the type checker (`infer`/`check`) and conversion (`conv`);
  the typing rules live in its module header.
- `lib/stmt`, `lib/prelude` — top-level statements and the standard library.
- `bin/main.ml` — the REPL and file runner.

Doc comments live in each module's `.mli`. Prose docs are in `docs/`:
`design.md` (settled decisions), `questions.md` (open questions), `todo.md`
(planned work).
