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
  | Unit  (** the unit type, with definitional η: every element is [MkUnit] *)
  | MkUnit  (** the element of [Unit] *)
  | Var of int  (** de Bruijn index *)
  | Sort of int  (** the Sort hierarchy: Prop = Sort 0, Type i = Sort (i+1) *)
  | Pi of string * t * t  (** Π (x : A). B, where B binds index 0 *)
  | Lam of string * t * t  (** λ (x : A). b, where b binds index 0 *)
  | App of t * t
  | Sigma of string * t * t
      (** Σ (x : A) ⇒ B, where B binds index 0; prints as [A × B] when
          non-dependent *)
  | Pair of t * t  (** (a, b) *)
  | Fst of t  (** p.1 *)
  | Snd of t  (** p.2 *)
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
  | Nat  (** the natural numbers *)
  | Zero
  | Succ of t
  | NatRec of t * t * t * t
      (** [NatRec (P, pz, ps, n)]: the recursor — eliminates [n : Nat] at motive
          [P : Nat → Sort j], given [pz : P zero] and the step
          [ps : Π (k : Nat) ⇒ P k → P (succ k)] (whose [P k] argument is the
          induction hypothesis); yields [P n] *)
  | Ind of string
      (** an inductive type former, applied to its parameters via [App] *)
  | Ctor of ctor_head
      (** an inductive constructor, applied to its arguments via [App] *)
  | Rec of rec_head
      (** an inductive's recursor, applied to parameters, motive, minor premises
          and the major premise via [App] *)

(** [occurs k t] is true if de Bruijn index [k] appears free in [t] *)
val occurs : int -> t -> bool

(** [pp_in names fmt t] pretty-prints [t] using binder name hints, priming names
    that would shadow an enclosing binder; [names] supplies the names of
    enclosing binders for [t]'s free indices, innermost first. Unbound indices
    print as [!i]. *)
val pp_in : string list -> Format.formatter -> t -> unit

(** [pp fmt t] pretty-prints the closed term [t] *)
val pp : Format.formatter -> t -> unit

(** [to_string_in names t] is [t] rendered via {!pp_in} *)
val to_string_in : string list -> t -> string

(** [to_string t] is the closed term [t] rendered via {!pp} *)
val to_string : t -> string
