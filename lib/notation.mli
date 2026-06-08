(** Frontend rendering of notation that the kernel does not carry.

    The kernel raises {!Check.Type_error} carrying message fragments with raw
    terms (not pre-rendered strings); this applies a notation config to turn
    those fragments into a display string. The kernel stays notation-ignorant —
    it never names [Unit]/[Nat], it just hands over the terms and the names they
    are read against. *)

(** [render_error notation frags] renders the fragments of a kernel error
    message, applying [notation] to each embedded term *)
val render_error : Type.notation -> Check.frag list -> string
