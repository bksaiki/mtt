(** The elaborator: a type-directed translation from surface syntax ({!Ast.t})
    to explicit core ({!Type.t}). It is the frontend's counterpart to the
    type-free {!Ast.to_term}: where that pass only resolves names, the
    elaborator additionally uses the {e expected type} to fill in arguments the
    kernel demands explicitly.

    It is {e untrusted}, in the Lean/Rocq tradition: the core it produces is
    re-verified by {!Check}, so a bug here is a usability bug, not a soundness
    one. The elaborator reuses the kernel's NbE ({!Value.eval}, conversion via
    {!Check}) rather than reimplementing it.

    What it infers in this phase: a constructor application checked against its
    own inductive type may {e omit the leading parameters}, which are recovered
    from the expected type — [Box.wrap a] in place of [Box.wrap A a]. Everywhere
    else it preserves the explicit behaviour of {!Ast.to_term}. The builtin
    type-formers ([Σ]/[+]/[Eq] and their intro/elim forms) are still translated
    syntactically, with no inference inside them. *)

(** [infer notation ctx s] elaborates [s] in inference position (no expected
    type), returning the core term. Its type is then synthesized by
    {!Check.infer}. *)
val infer : Notation.t -> Check.ctx -> Ast.t -> Type.t

(** [check notation ctx s expected] elaborates [s] against the expected type
    [expected], returning the core term. The expected type flows into
    constructor applications (so their parameters may be omitted) and through
    lambda bodies. The result is re-verified by {!Check.check}. *)
val check : Notation.t -> Check.ctx -> Ast.t -> Value.t -> Type.t

(** [zonk lvl t] replaces every solved metavariable in [t] by its solution (read
    back as core at level [lvl]), making [t] reuse-safe; a remaining
    {!Type.Meta} is an unsolved hole, which {!Type.has_meta} detects. Run on an
    elaborated term before re-checking or storing it. *)
val zonk : int -> Type.t -> Type.t
