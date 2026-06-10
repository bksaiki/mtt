(** Surface syntax: what the parser produces, with named binders and a source
    location on every node. The elaborator ({!Elab}) is the sole pass that turns
    it into the (location-free) de Bruijn core. *)

(** a surface universe level: a concrete level, a level variable (resolved
    against the level parameters in scope), or [max]/[imax] of two *)
type lvl =
  | LNat of int
  | LVar of string
  | LMax of lvl * lvl
  | LIMax of lvl * lvl

type t =
  { loc : Loc.t  (** the node's source span *)
  ; desc : desc
  }

and desc =
  | Var of string
  | Field of t * string  (** a named projection, e.g. the recursor [Nat.rec] *)
  | Sort of lvl  (** a sort at a (possibly variable) level: Prop = Sort 0, … *)
  | Pi of Type.icit * string * t * t  (** [(x : A) -> B] or [{x : A} -> B] *)
  | Arrow of t * t  (** A -> B *)
  | Lam of Type.icit * string * t * t
      (** [fun (x : A) => b] or [fun {x : A} => b] *)
  | App of t * t
  | At of t
      (** [@f]: make every argument explicit, suppressing implicit insertion *)
  | Match of t * (string * string list * t) list
      (** [match e with | C x… => b … end]: scrutinee and per-arm constructor
          name, pattern variables, and body — case-analysis sugar for the
          recursor *)
  | Ascribe of t * t  (** (t : A) *)
  | MkUnit  (** [()], sugar for the prelude's [Unit.unit] *)
  | Sigma of string * t * t  (** Σ (x : A) ⇒ B *)
  | Prod of t * t  (** A × B *)
  | Pair of t * t  (** (a, b) *)
  | Fst of t  (** p.1 *)
  | Snd of t  (** p.2 *)
  | Sum of t * t  (** A + B *)
  | EqInfix of t * t
      (** [x = y]: the registered equality former, type argument inferred *)
  | Numeral of int
      (** a decimal literal, e.g. [0], [5]; expands to succ-applications of the
          [nat] notation's zero/succ *)
  | Hole
      (** [_], an elaboration hole — a fresh metavariable for the elaborator to
          solve *)

(** [mk loc desc] is the node [desc] located at [loc] *)
val mk : Loc.t -> desc -> t

(** [lams loc groups body] wraps [body] in a lambda for every name of every
    binder group, e.g. [λ (x y : A) {z : B} ⇒ body]; each group carries its
    visibility. The synthetic binder nodes are stamped with [loc], the span of
    the whole construct. *)
val lams : Loc.t -> (Type.icit * string list * t) list -> t -> t

(** [pis loc groups body] is the Π counterpart of {!lams} *)
val pis : Loc.t -> (Type.icit * string list * t) list -> t -> t

(** [sigmas loc groups body] is the Σ counterpart of {!lams}; the visibility on
    each group is ignored (Σ binders are always explicit) *)
val sigmas : Loc.t -> (Type.icit * string list * t) list -> t -> t

(** [var_spine t] is [Some [x1; ...; xn]] if [t] is an application spine of
    variables [x1 ... xn]: used by the parser to read the ascription [(x y : A)]
    as a multi-name pi binder when it appears left of an arrow *)
val var_spine : t -> string list option

(** raised by the elaborator ({!Elab}) when a name is not in scope, with the
    offending location *)
exception Unbound_variable of Loc.t * string
