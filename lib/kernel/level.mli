(** Universe levels for the [Sort] hierarchy. A level is a CoC-style universe
    index: [Prop = Sort zero], [Type i = Sort (succ^(i+1) zero)]. The
    [Var]/[Max]/[IMax] cases support universe polymorphism (level variables and
    the [max]/[imax] algebra); until level variables are introduced every level
    in a checked term is closed, and [equal]/[leq] are exact on closed levels.
*)
type t =
  | Zero
  | Succ of t
  | Max of t * t
  | IMax of t * t
  | Var of int  (** a level parameter, by de Bruijn index *)

val zero : t

val succ : t -> t

(** [of_int n] is [Succ^n Zero] *)
val of_int : int -> t

(** [to_int l] is the value of a closed level, or [None] if [l] mentions a
    variable *)
val to_int : t -> int option

(** [max a b] is the least upper bound; reduces the closed case *)
val max : t -> t -> t

(** [imax a b] is [b] when [b] is (or normalizes to) [zero], else [max a b] — so
    a product into a proposition stays a proposition *)
val imax : t -> t -> t

(** put a level in canonical form (exact for closed levels) *)
val normalize : t -> t

(** definitional equality of levels (exact on closed levels) *)
val equal : t -> t -> bool

(** [leq a b] decides [a ≤ b] (exact on closed levels); used by predicativity *)
val leq : t -> t -> bool

(** a debug rendering ([0], [3], [u0], [max …]); surface universes print via the
    {!Type} printer, not this *)
val to_string : t -> string
