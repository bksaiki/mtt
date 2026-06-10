(** The elaborator's metacontext, with the unification and zonking over it. It
    is a {e functional} value threaded by the caller (the kernel stays free of
    any metavariable state — it carries only an inert {!Type.Meta} node it never
    inspects). All knowledge of solutions lives here; the kernel's NbE is reused
    for reduction, with forcing of solutions added on top. *)

(** a metacontext: the metavariables allocated so far, with their solutions *)
type t

(** the empty metacontext *)
val empty : t

(** [fresh ms ~blvl ty] allocates a metavariable of type [ty], born at de Bruijn
    level [blvl] (the binders in scope, used by the scope check), returning the
    extended context and the new id. The metavariable occurs in a value as
    [Value.Neutral (Value.Meta id)] and in core as [Type.Meta id]. *)
val fresh : t -> blvl:int -> Value.t -> t * int

(** [fresh_level ms] allocates a {e level} metavariable — a placeholder for an
    unknown level argument of a polymorphic head — returning the extended
    context and its id. It occurs as [Level.LMeta id]; unification solves it and
    {!zonk} replaces it. (Level metas need no type or scope: a level has no
    binders.) *)
val fresh_level : t -> t * int

(** [typ ms i] is metavariable [i]'s type. *)
val typ : t -> int -> Value.t

(** [solution ms i] is its solution, if solved. *)
val solution : t -> int -> Value.t option

(** [force ms v] unfolds a solved metavariable at the head of [v] (re-applying
    its solution to the spine); a meta-free or unsolved-headed value is returned
    unchanged. The elaborator forces before matching on a value's shape, since
    the kernel does not. *)
val force : t -> Value.t -> Value.t

(** [unify ms ctx v1 v2] makes [v1] and [v2] convertible by solving
    metavariables, returning the updated context; [ctx] supplies the binders in
    scope (extended as unification descends under binders) so a solved meta's
    type can be reconciled with its solution's. Lenient: it solves what it can
    (the flex-rigid pattern and rigid-rigid structure) and leaves the rest to
    the kernel's re-check. *)
val unify : t -> Check.ctx -> Value.t -> Value.t -> t

(** [zonk ms lvl t] replaces every solved metavariable in [t] by its solution,
    read back as core at level [lvl] (reuse-safe). A remaining {!Type.Meta} is
    an unsolved hole, which {!Type.has_meta} detects. Run on an elaborated term
    before re-checking or storing it. *)
val zonk : t -> int -> Type.t -> Type.t
