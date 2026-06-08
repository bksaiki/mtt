(** The standard prelude, embedded from [std/prelude.mtt] at build time (see the
    [prelude_data] rule) and brought into scope by the [prelude] keyword. *)

(** the prelude source text *)
val source : string

(** [load ctx] type-checks the prelude and extends [ctx] with all of its
    declarations. Raises {!Check.Type_error} / {!Ast.Unbound_variable} /
    {!Parse.Error} if the prelude is ill-formed — i.e. only on a build-time bug,
    since the prelude ships with the tool. *)
val load : Check.ctx -> Check.ctx
