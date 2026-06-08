(** A parameterized inductive type declaration: a type former with a parameter
    telescope and a list of constructors. Parameters are shared across the whole
    definition and passed explicitly to the former, the constructors, and the
    recursor. No indices yet (see [docs/inductive-plan.md]).

    This module is the declaration's data model and the source of the
    computational {e skeletons} ({!Type.ctor_head}, {!Type.rec_head}) baked into
    syntax nodes. The full types (former, constructors, recursor) are derived in
    the checker. *)

(** a constructor field (a non-parameter argument) *)
type arg =
  { aname : string  (** the binder name (display only) *)
  ; aty : Type.t  (** its type, in the context [params, earlier fields] *)
  ; recursive : bool
        (** whether [aty] is the inductive's own type [T params] *)
  }

(** a constructor, recording only its fields; its result is always [T params] *)
type ctor =
  { cname : string
  ; fields : arg list
  }

type spec =
  { name : string
  ; params : (string * Type.t) list  (** the parameter telescope *)
  ; sort : int  (** the result sort: [T params : Sort sort] *)
  ; ctors : ctor list
  }

(** the number of parameters *)
val nparams : spec -> int

(** [ctor_head spec i] is the skeleton of the [i]-th constructor *)
val ctor_head : spec -> int -> Type.ctor_head

(** [rec_head spec] is the skeleton of the recursor *)
val rec_head : spec -> Type.rec_head

(** [apply spec depth] is the inductive applied to its parameters as variables,
    read in a context of [depth] binders whose outermost {!nparams} are the
    parameters. This is what constructors return and the exact shape a direct
    recursive field must have. *)
val apply : spec -> int -> Type.t

(** the type former's type: [(params) -> Sort sort] *)
val former_type : spec -> Type.t

(** [ctor_type spec i] is the [i]-th constructor's type,
    [(params) -> (fields) -> Ind params] *)
val ctor_type : spec -> int -> Type.t

(** [occurs name t] is whether the inductive [name] occurs anywhere in [t] *)
val occurs : string -> Type.t -> bool
