(** The frontend's notation registry and rendering. The kernel is fully
    notation-ignorant — it never names [Unit]/[Nat] and holds no display config;
    everything user-facing (output and error messages) is rendered here, with a
    {!Type.notation} the frontend threads through its session. *)

(** [render_error notation frags] renders the fragments of a kernel error
    message ({!Error.Type_error}), applying [notation] to each embedded term *)
val render_error : Type.notation -> Error.frag list -> string

(** [show notation ctx v] renders a value [v] in the context [ctx] using
    [notation]. *)
val show : Type.notation -> Check.ctx -> Value.t -> string

(** [show_term notation ctx t] renders a term [t] in the context [ctx] using
    [notation]. *)
val show_term : Type.notation -> Check.ctx -> Type.t -> string

(** [register role spec notation] records that the inductive [spec] fills the
    notation [role] (["unit"] for [()], ["nat"] for decimal literals), returning
    the updated config. Shape-checks that [spec] can play the role (e.g. ["nat"]
    demands a nullary then a single-recursive-field constructor) and rejects
    re-registering an already-bound role. Raises {!Error.Type_error} otherwise.
*)
val register : string -> Inductive.spec -> Type.notation -> Type.notation
