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
  }

(** The skeleton of a recursor, enough to drive ι. [recs] has one entry per
    constructor; each flags, for that constructor's {e fields} (its
    non-parameter arguments), which are recursive. Parameters are shared and
    never recursive, so they are excluded. *)
type rec_head =
  { rind : string  (** the inductive being eliminated; prints as ["rind.rec"] *)
  ; nparams : int  (** leading parameter arguments, shared and fixed *)
  ; recs : bool list list
  }

type t =
  | Var of int  (** de Bruijn index *)
  | Sort of int  (** the Sort hierarchy: Prop = Sort 0, Type i = Sort (i+1) *)
  | Pi of string * t * t  (** Π (x : A). B, where B binds index 0 *)
  | Lam of string * t * t  (** λ (x : A). b, where b binds index 0 *)
  | App of t * t
  | Proj of int * t
      (** [x.(i+1)]: the [i]-th (0-based) field projection of a record (a
          single-constructor inductive) *)
  | Sum of t * t  (** A + B *)
  | Inl of t  (** left injection *)
  | Inr of t  (** right injection *)
  | Case of t * t * t * t
      (** [Case (P, s, u, v)]: the recursor — eliminates [s : A + B] at motive
          [P : A + B → Sort j], with branches [u : Π (x : A) ⇒ P (inl x)] and
          [v : Π (y : B) ⇒ P (inr y)] *)
  | Eq of t * t * t  (** [Eq A x y]: propositional equality of [x y : A] *)
  | Refl  (** the reflexivity proof [refl : Eq A x x]; check-only *)
  | J of t * t * t
      (** [J (P, d, p)]: the eliminator (based path induction) — eliminates
          [p : Eq A x y] at motive [P : Π (y : A) ⇒ Eq A x y → Sort j], given
          the diagonal case [d : P x refl]; yields [P y p] *)
  | Ind of string
      (** an inductive type former, applied to its parameters via [App] *)
  | Ctor of ctor_head
      (** an inductive constructor, applied to its arguments via [App] *)
  | Rec of rec_head
      (** an inductive's recursor, applied to parameters, motive, minor premises
          and the major premise via [App] *)

(** [occurs k t] is true if de Bruijn index [k] appears free in [t] *)
val occurs : int -> t -> bool

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
