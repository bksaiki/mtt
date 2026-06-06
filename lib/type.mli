(** Core syntax: one type for both terms and types — in a dependent theory "is a
    type" is a judgment, not a syntactic class. Variables are de Bruijn indices;
    binder names are display hints only, ignored by every algorithm
    (α-equivalence is structural equality). *)

type t =
  | Var of int  (** de Bruijn index *)
  | Sort of int  (** the Sort hierarchy: Prop = Sort 0, Type i = Sort (i+1) *)
  | Pi of string * t * t  (** Π (x : A). B, where B binds index 0 *)
  | Lam of string * t * t  (** λ (x : A). b, where b binds index 0 *)
  | App of t * t
  | Unit  (** the unit type, with definitional η: every element is [MkUnit] *)
  | MkUnit  (** the element of [Unit] *)
  | Empty  (** the empty type: falsity, in Prop *)
  | Absurd of t * t
      (** [Absurd (A, h)]: ex falso — eliminates [h : Empty] at motive [A] in
          any sort (subsingleton elimination, sound because [Empty] has no
          introduction forms) *)

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
