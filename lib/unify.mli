(** Unification for the elaborator: it solves (non-contextual) metavariables in
    the kernel metacontext ({!Value.fresh_meta} et al.) by side effect, reusing
    the kernel's NbE rather than reimplementing reduction.

    It is {e lenient} — it solves the flex-rigid case [?m := t] (with an
    occurs/scope check) and walks rigid-rigid structurally, doing nothing on the
    rest (an applied flex, occurs/scope failures, rigid-rigid mismatches). That
    is sound because the kernel re-checks the fully zonked term: an unsolved
    constraint surfaces later as a "cannot infer" or ordinary type error, never
    as a wrong acceptance. *)

(** [unify lvl v1 v2] makes [v1] and [v2] convertible by solving metavariables,
    where [lvl] is the number of binders in scope (both values live under it).
*)
val unify : int -> Value.t -> Value.t -> unit
