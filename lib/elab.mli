(** The elaborator: a type-directed translation from surface syntax ({!Ast.t})
    to explicit core ({!Type.t}). It is the frontend's counterpart to the
    type-free {!Ast.to_term}: where that pass only resolves names, the
    elaborator additionally uses the {e expected type} to fill in arguments the
    kernel demands explicitly.

    It is {e untrusted}, in the Lean/Rocq tradition: the core it produces is
    re-verified by {!Check}, so a bug here is a usability bug, not a soundness
    one. The elaborator reuses the kernel's NbE ({!Value.eval}, conversion via
    {!Check}) rather than reimplementing it, adding only the meta machinery in
    {!Meta} and its own meta-aware type synthesis.

    What it infers, all driven by the expected type:
    - constructor applications may {e omit the leading parameters}, recovered
      from the expected inductive type ([Box.wrap a] for [Box.wrap A a]);
    - a surface hole [_] becomes a metavariable, solved by unification;
    - implicit binders [{x : A}] are inserted as fresh metavariables;
    - [x = y] is [Eq A x y] with [A] inferred from [x];
    - a hole motive on [J] or a recursor is synthesized by abstracting the
      scrutinee out of the expected goal.

    The result is zonked to meta-free core; an unsolved hole is reported here,
    never handed to the kernel. *)

(** [infer notation ctx s] elaborates [s] in inference position (no expected
    type), returning the core term. Its type is then synthesized by
    {!Check.infer}. *)
val infer : Notation.t -> Check.ctx -> Ast.t -> Type.t

(** [check notation ctx s expected] elaborates [s] against the expected type
    [expected], returning the core term. The expected type flows into
    constructor applications (so their parameters may be omitted) and through
    lambda bodies. The result is re-verified by {!Check.check}. *)
val check : Notation.t -> Check.ctx -> Ast.t -> Value.t -> Type.t
