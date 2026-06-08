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
  ; sigma : Type.ctor_head option
        (** the [mk] constructor of the dependent-pair record: an applied former
            renders as [Σ (x : A) ⇒ B] / [A × B], an applied [mk] as a tuple *)
  ; sum : string option
        (** the binary sum's type former, by name: an applied former renders as
            [A + B]. The injections and eliminator are ordinary qualified names
            ([Sum.inl], [Sum.rec]), so they need no sugar. *)
  }

(** the empty registry: no role bound, so nothing is sugared *)
val empty : t

(** [register role spec n] records that the inductive [spec] fills the notation
    [role] (["unit"] for [()], ["nat"] for decimal literals, ["sigma"] for
    [Σ]/[×]/tuples, ["sum"] for the [+] former), returning the updated registry.
    Shape-checks that [spec] can play the role (e.g. ["nat"] demands a nullary
    then a single-recursive-field constructor; ["sigma"] a two-parameter record
    with a two-field constructor; ["sum"] a two-parameter inductive with two
    single-field constructors) and rejects re-registering an already-bound role.
    Raises {!Error.Type_error} otherwise. *)
val register : string -> Inductive.spec -> t -> t

(** [sugar n ~recurse names term] renders [term] as surface notation ([()], a
    decimal, [A × B], a tuple) if it matches a registered role, else [None] —
    the hook {!Type.pp_in} expects, returning [(prec, text)] for
    parenthesization. [recurse] renders subterms (for infix/mixfix forms) and
    [names] are the binders in scope. *)
val sugar :
     t
  -> recurse:(int -> string list -> Type.t -> string)
  -> string list
  -> Type.t
  -> (int * string) option

(** [show n names lvl v] / [show_term n names t] render a value / term against
    the binder [names] (with de Bruijn level [lvl] to quote a value) with
    notation applied — for [#check]/[#eval]/[:env] output. Taking [names]/[lvl]
    rather than a {!Check.ctx} keeps this module independent of the checker. *)
val show : t -> string list -> int -> Value.t -> string

val show_term : t -> string list -> Type.t -> string

(** [render_error n frags] renders a kernel error message ({!Error.Type_error}),
    applying notation to each embedded term *)
val render_error : t -> Error.frag list -> string
