(** The frontend's notation registry, config, and rendering. The kernel is fully
    notation-ignorant — it never names [Unit]/[Nat], and its printer knows only
    a generic [sugar] hook ({!Type.pp_in}). This module owns the config that
    drives that hook in reverse (printing) and {!Ast.to_term} forward (parsing).
*)

(** which inductive constructors fill each notation role *)
type t =
  { unit_ctor : Type.ctor_head option  (** rendered as [()] *)
  ; nat : (Type.ctor_head * Type.ctor_head) option
        (** [(zero, succ)]: closed succ-chains ending in zero fold to decimals
        *)
  }

(** the empty registry: no role bound, so nothing is sugared *)
val empty : t

(** [register role spec n] records that the inductive [spec] fills the notation
    [role] (["unit"] for [()], ["nat"] for decimal literals), returning the
    updated registry. Shape-checks that [spec] can play the role (e.g. ["nat"]
    demands a nullary then a single-recursive-field constructor) and rejects
    re-registering an already-bound role. Raises {!Error.Type_error} otherwise.
*)
val register : string -> Inductive.spec -> t -> t

(** [sugar n term] renders [term] as a surface atom ([()], a decimal) if it
    matches a registered role, else [None] — the hook {!Type.pp_in} expects. *)
val sugar : t -> Type.t -> string option

(** [show n names lvl v] / [show_term n names t] render a value / term against
    the binder [names] (with de Bruijn level [lvl] to quote a value) with
    notation applied — for [#check]/[#eval]/[:env] output. Taking [names]/[lvl]
    rather than a {!Check.ctx} keeps this module independent of the checker. *)
val show : t -> string list -> int -> Value.t -> string

val show_term : t -> string list -> Type.t -> string

(** [render_error n frags] renders a kernel error message ({!Error.Type_error}),
    applying notation to each embedded term *)
val render_error : t -> Error.frag list -> string
