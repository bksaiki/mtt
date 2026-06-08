(** Surface syntax: what the parser produces, with named binders and a source
    location on every node. Scope checking ({!to_term}) converts it to the
    (location-free) de Bruijn core. *)

type t =
  { loc : Loc.t  (** the node's source span *)
  ; desc : desc
  }

and desc =
  | Var of string
  | Field of t * string  (** a named projection, e.g. the recursor [Nat.rec] *)
  | Sort of int  (** Prop = Sort 0, Type i = Sort (i+1), as in the core *)
  | Pi of string * t * t  (** (x : A) -> B *)
  | Arrow of t * t  (** A -> B *)
  | Lam of string * t * t  (** fun (x : A) => b *)
  | App of t * t
  | Ascribe of t * t  (** (t : A) *)
  | Unit
  | MkUnit
  | Empty
  | Absurd of t * t  (** [absurd A h] *)
  | Sigma of string * t * t  (** Σ (x : A) ⇒ B *)
  | Prod of t * t  (** A × B *)
  | Pair of t * t  (** (a, b) *)
  | Fst of t  (** p.1 *)
  | Snd of t  (** p.2 *)
  | Sum of t * t  (** A + B *)
  | Inl of t  (** inl a *)
  | Inr of t  (** inr b *)
  | Case of t * t * t * t  (** case P s u v *)
  | Eq of t * t * t  (** Eq A x y *)
  | Refl  (** refl *)
  | J of t * t * t  (** J P d p *)
  | Nat  (** Nat *)
  | Zero  (** 0 *)
  | Succ of t  (** succ n *)
  | NatRec of t * t * t * t  (** natrec P pz ps n *)

(** [mk loc desc] is the node [desc] located at [loc] *)
val mk : Loc.t -> desc -> t

(** [numeral loc n] is the decimal literal [n] as [succ (... zero)] *)
val numeral : Loc.t -> int -> t

(** [lams loc groups body] wraps [body] in a lambda for every name of every
    binder group, e.g. [λ (x y : A) (z : B) ⇒ body]; the synthetic binder nodes
    are stamped with [loc], the span of the whole construct *)
val lams : Loc.t -> (string list * t) list -> t -> t

(** [pis loc groups body] is the Π counterpart of {!lams} *)
val pis : Loc.t -> (string list * t) list -> t -> t

(** [sigmas loc groups body] is the Σ counterpart of {!lams} *)
val sigmas : Loc.t -> (string list * t) list -> t -> t

(** [var_spine t] is [Some [x1; ...; xn]] if [t] is an application spine of
    variables [x1 ... xn]: used by the parser to read the ascription [(x y : A)]
    as a multi-name pi binder when it appears left of an arrow *)
val var_spine : t -> string list option

exception Unbound_variable of Loc.t * string

(** [to_term sg names s] scope-checks [s], converting named binders to de Bruijn
    indices; [names] binds local variables (innermost first), e.g. top-level
    declarations. A bare name not bound locally resolves to an inductive former
    in the signature [sg]; qualified [T.c] / [T.rec] resolve to a constructor or
    the recursor of [T]. Ascriptions [(t : A)] elaborate to the typed identity
    [(fun (x : A) => x) t]. Raises {!Unbound_variable}, with the offending
    location, if a name is not in scope. *)
val to_term : Signature.t -> string list -> t -> Type.t
