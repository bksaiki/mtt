(** Core syntax: one type for both terms and types — in a dependent theory "is a
    type" is a judgment, not a syntactic class. Variables are de Bruijn indices;
    binder names are display hints only, ignored by every algorithm
    (α-equivalence is structural equality). *)

(** The computational skeleton of an inductive constructor, carried by the
    syntax node so the NbE core can fire ι without consulting the global
    signature (which holds the full types, for the checker only). *)
type ctor_head =
  { ind : string  (** the inductive this constructs *)
  ; cname : string  (** the constructor's (globally unique) name *)
  ; cindex : int  (** its position in the inductive's constructor list *)
  ; carity : int  (** total arguments: leading parameters + fields *)
  ; nparams : int  (** leading parameters, so a projection can skip them *)
  ; clevels : Level.t list
        (** use-site level arguments instantiating the inductive's level
            parameters; empty when the inductive is monomorphic *)
  }

(** A binder's visibility. An [Explicit] [(x : A)] argument is supplied at every
    application; an [Implicit] [{x : A}] one is inserted automatically by the
    elaborator. The kernel carries this on {!Pi}/{!Lam} but ignores it in
    conversion and typing (exactly as it ignores the binder-name hint) — it is
    metadata consumed only by the frontend (argument insertion and printing). *)
type icit =
  | Explicit
  | Implicit

type t =
  | Var of int  (** de Bruijn index *)
  | Def of int * Level.t list
      (** a de Bruijn reference to a universe-polymorphic definition, carrying
          its use-site level arguments. Like {!Var} the index resolves to the
          def's context slot, where a [Value.VPoly] holds the level-abstracted
          body; evaluation instantiates it at these levels. Monomorphic defs and
          local binders use {!Var} — this node appears only for polymorphic
          ([nlevels > 0]) defs. *)
  | Sort of Level.t
      (** the Sort hierarchy: Prop = Sort 0, Type i = Sort (i+1) *)
  | Pi of icit * string * t * t  (** Π (x : A). B, where B binds index 0 *)
  | Lam of icit * string * t * t  (** λ (x : A). b, where b binds index 0 *)
  | App of t * t
  | Proj of int * t
      (** [x.(i+1)]: the [i]-th (0-based) field projection of a record (a
          single-constructor inductive) *)
  | Meta of int
      (** a metavariable, referenced by id; produced by the elaborator and
          resolved by unification, then zonked away — it never reaches the
          trusted check of final core. Its local dependencies ride the enclosing
          [App] spine ([?m a b] is [App (App (Meta m, a), b)]). *)
  | Ind of string * Level.t list
      (** an inductive type former (with use-site level arguments), applied to
          its parameters then indices via [App] *)
  | Ctor of ctor_head
      (** an inductive constructor, applied to its arguments via [App] *)
  | Rec of rec_head
      (** an inductive's recursor, applied to parameters, motive, minor
          premises, index arguments and the major premise via [App] *)

(** The skeleton of a recursor, enough to drive ι without the signature. [recs]
    has one entry per constructor (in order), each listing that constructor's
    {e fields} (its non-parameter arguments) and which are recursive. Parameters
    are shared and never recursive, so they are excluded. For an indexed family
    the recursor's spine is [params @ motive :: minors @ indices @ [major]]:
    [nindices] index arguments sit just before the major, and a recursive field
    records the index instances it sits at (so ι forms the induction hypothesis
    at the right indices). *)
and rec_head =
  { rind : string  (** the inductive being eliminated; prints as ["rind.rec"] *)
  ; nparams : int  (** leading parameter arguments, shared and fixed *)
  ; nindices : int  (** index arguments, between the minors and the major *)
  ; recs : field_rec list list
  ; rlevels : Level.t list
        (** use-site level arguments instantiating the inductive's level
            parameters; empty when the inductive is monomorphic *)
  }

(** whether a constructor field is recursive, and if so the index instances of
    its type [Ind params indices] — terms in the context
    [params, earlier fields], which ι evaluates against the constructor's actual
    arguments *)
and field_rec =
  | Nonrec
  | Recursive of t list

(** [subst_levels args t] instantiates a level-polymorphic term by replacing the
    level variables in every [Sort] and inductive-head level list of [t] with
    the level arguments [args]; identity on a monomorphic term *)
val subst_levels : Level.t list -> t -> t

(** [occurs k t] is true if de Bruijn index [k] appears free in [t] *)
val occurs : int -> t -> bool

(** [has_meta t] is true if any metavariable ({!Meta}) occurs in [t]; the
    frontend uses it (on a quoted value, where solved metas are already
    unfolded) to detect an unsolved hole before the trusted check. *)
val has_meta : t -> bool

(** [freshen names x] is [x] primed with enough trailing ['] to make it distinct
    from every name in [names] (and [x]); ["" ] becomes ["x"] first. The printer
    uses this so binder hints never shadow an enclosing binder; a frontend
    [sugar] hook that renders its own binders ([Σ (x : A) ⇒ …]) needs it too. *)
val freshen : string list -> string -> string

(** [pp_in ?sugar names fmt t] pretty-prints [t] using binder name hints,
    priming names that would shadow an enclosing binder; [names] supplies the
    names of enclosing binders for [t]'s free indices, innermost first. Unbound
    indices print as [!i].

    [sugar] (default: never fires) is the notation hook: the kernel knows no
    notation itself, so the frontend supplies this to fold a subterm into a
    surface form — the unit constructor to [()], a succ-chain to a decimal, an
    applied [Sigma] former to [A × B]. It is consulted at every node, before the
    structural printer, and receives [names] (the binders in scope) and a
    [recurse] callback rendering a subterm at a given precedence under given
    names (so it can render the pieces of an infix form). It returns
    [Some (prec, s)] — [s] being the rendered surface text and [prec] its
    precedence, so the kernel can parenthesize it in context — or [None] to fall
    through to plain core printing. *)
val pp_in :
     ?sugar:
       (   recurse:(int -> string list -> t -> string)
        -> string list
        -> t
        -> (int * string) option)
  -> string list
  -> Format.formatter
  -> t
  -> unit

(** [pp fmt t] pretty-prints the closed term [t] (core syntax only, no sugar) *)
val pp : Format.formatter -> t -> unit

(** [to_string_in ?sugar names t] is [t] rendered via {!pp_in} *)
val to_string_in :
     ?sugar:
       (   recurse:(int -> string list -> t -> string)
        -> string list
        -> t
        -> (int * string) option)
  -> string list
  -> t
  -> string

(** [to_string t] is the closed term [t] rendered via {!pp} *)
val to_string : t -> string
