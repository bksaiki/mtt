(** Surface syntax: what the parser produces, with named binders. Scope checking
    ({!to_term}) converts it to the de Bruijn core. *)

type t =
  | Var of string
  | Sort of int  (** Prop = Sort 0, Type i = Sort (i+1), as in the core *)
  | Pi of string * t * t  (** (x : A) -> B *)
  | Arrow of t * t  (** A -> B *)
  | Lam of string * t * t  (** fun (x : A) => b *)
  | App of t * t
  | Ascribe of t * t  (** (t : A) *)

(** [lams groups body] wraps [body] in a lambda for every name of every binder
    group, e.g. [λ (x y : A) (z : B) ⇒ body] *)
val lams : (string list * t) list -> t -> t

(** [pis groups body] is the Π counterpart of {!lams} *)
val pis : (string list * t) list -> t -> t

(** [var_spine t] is [Some [x1; ...; xn]] if [t] is an application spine of
    variables [x1 ... xn]: used by the parser to read the ascription [(x y : A)]
    as a multi-name pi binder when it appears left of an arrow *)
val var_spine : t -> string list option

exception Unbound_variable of string

(** [to_term names s] scope-checks [s], converting named binders to de Bruijn
    indices; [names] binds free variables (innermost first), e.g. top-level
    declarations. Ascriptions [(t : A)] elaborate to the typed identity
    [(fun (x : A) => x) t]. Raises {!Unbound_variable} if a variable is not in
    scope. *)
val to_term : string list -> t -> Type.t
