(** The frontend's notation registry and rendering. The kernel is fully
    notation-ignorant — it never names [Unit]/[Nat] and holds no display config;
    everything user-facing (output and error messages) is rendered here, with a
    {!Type.notation} the frontend threads through its session. *)

(** [render_error notation frags] renders the fragments of a kernel error
    message ({!Check.Type_error}), applying [notation] to each embedded term *)
val render_error : Type.notation -> Check.frag list -> string

(** [show notation ctx v] renders a value, and [show_term] a term, against the
    context's binder names with [notation] applied — used for [#check]/[#eval]
    and [:env] output. (Compare {!Check.show}, the kernel's plain view.) *)
val show : Type.notation -> Check.ctx -> Value.t -> string

val show_term : Type.notation -> Check.ctx -> Type.t -> string

(** [register role spec notation] records that the inductive [spec] fills the
    notation [role] (["unit"] for [()], ["nat"] for decimal literals), returning
    the updated config. Shape-checks that [spec] can play the role (e.g. ["nat"]
    demands a nullary then a single-recursive-field constructor) and rejects
    re-registering an already-bound role. Raises {!Check.Type_error} otherwise.
*)
val register : string -> Inductive.spec -> Type.notation -> Type.notation
