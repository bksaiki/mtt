(** The standard prelude, embedded from [std/prelude.mtt] at build time (see the
    [prelude_data] rule) and brought into scope by the [prelude] keyword. *)

(** the prelude source text *)
val source : string

(** raised by {!load} when the prelude is ill-formed, carrying a rendered,
    [<prelude>:line:col]-located message. Since the prelude ships with the tool
    this is a build-time bug; it is a clean substitute for the raw
    {!Error.Type_error} that would otherwise escape an auto-load as an unlocated
    [Fatal error: exception]. *)
exception Load_error of string

(** [load sess] type-checks the prelude and extends the session [sess] with all
    of its declarations (its bindings and notation). Raises {!Load_error} (with
    a located message) if the prelude is ill-formed — a build-time bug, since
    the prelude ships with the tool. *)
val load : Stmt.session -> Stmt.session
