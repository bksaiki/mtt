(** An indexed inductive type family: a type former with a parameter telescope,
    an index telescope, and a list of constructors. Parameters are {e fixed}
    across the definition (passed uniformly to the former, the constructors, and
    the recursor); indices {e vary} per constructor result, and the motive
    abstracts over them (see the Inductive types section of [docs/design.md]). A
    non-indexed type is the [indices = []] case.

    This module is the declaration's data model and the source of the
    computational {e skeletons} ({!Type.ctor_head}, {!Type.rec_head}) baked into
    syntax nodes. The full types (former, constructors, recursor) are derived in
    the checker. *)

(** a constructor field (a non-parameter argument) *)
type arg =
  { aname : string  (** the binder name (display only) *)
  ; aty : Type.t  (** its type, in the context [params, earlier fields] *)
  ; recursive : Type.t list option
        (** [None] if not recursive; [Some idxs] if [aty] is the inductive's own
            type [Ind params idxs], recording the index instances *)
  }

(** a constructor, recording its fields and the index instances of its result
    [Ind params result_indices] (in the context [params, fields]) *)
type ctor =
  { cname : string
  ; fields : arg list
  ; result_indices : Type.t list
  }

type spec =
  { name : string
  ; params : (string * Type.t) list  (** the parameter telescope *)
  ; indices : (string * Type.t) list
        (** the index telescope, in the context [params]; empty if non-indexed
        *)
  ; sort : Level.t  (** the result sort: [T params indices : Sort sort] *)
  ; ctors : ctor list
  }

(** the number of parameters *)
val nparams : spec -> int

(** the number of indices *)
val nindices : spec -> int

(** [ctor_head spec i] is the skeleton of the [i]-th constructor *)
val ctor_head : spec -> int -> Type.ctor_head

(** [rec_head spec] is the skeleton of the recursor *)
val rec_head : spec -> Type.rec_head

(** whether [spec] is a {e record}: a single-constructor, non-recursive,
    non-indexed inductive, so it has field projections and definitional η *)
val is_record : spec -> bool

(** [apply spec depth] is the inductive applied to its parameters as variables
    (indices excluded), read in a context of [depth] binders whose outermost
    {!nparams} are the parameters. This is the [Ind params] head a constructor
    result and a recursive field are built on (their indices are appended). *)
val apply : spec -> int -> Type.t

(** the type former's type: [(params) -> (indices) -> Sort sort] *)
val former_type : spec -> Type.t

(** [ctor_type spec i] is the [i]-th constructor's type,
    [(params) -> (fields) -> Ind params result_indices] *)
val ctor_type : spec -> int -> Type.t

(** [occurs name t] is whether the inductive [name] occurs anywhere in [t] *)
val occurs : string -> Type.t -> bool
