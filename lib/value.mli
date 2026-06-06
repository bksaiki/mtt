(** Semantic values: the result of evaluation (normalization by evaluation).
    Binder bodies are closures holding unevaluated syntax, and stuck variables
    are de Bruijn levels — so going under a binder during quoting needs no index
    shifting. There is no substitution function anywhere: β-reduction is closure
    application. *)

type t =
  | Sort of int
  | Pi of string * t * closure
  | Lam of string * t * closure
  | Unit
  | Tt
  | Neutral of neutral

(** a stuck term: a variable applied to a spine of arguments *)
and neutral =
  | Var of int  (** de Bruijn level *)
  | App of neutral * t

(** a suspended binder body: syntax waiting for the bound variable's value *)
and closure =
  { env : env
  ; body : Type.t
  }

and env = t list

(** raised when a non-function is applied; unreachable for type-checked terms *)
exception Not_a_function

(** [eval env t] evaluates [t] in [env], which must bind every free index.
    β-redexes never survive evaluation, and δ happens here too: a defined
    variable is bound in [env] directly to its value. *)
val eval : env -> Type.t -> t

(** [apply f a] applies a function value: β-reduction for a lambda, spine
    extension for a neutral. Raises {!Not_a_function} otherwise. *)
val apply : t -> t -> t

(** [apply_closure c a] evaluates the closure body with [a] bound — the only
    form substitution takes in this kernel *)
val apply_closure : closure -> t -> t

(** [quote l v] reads a value back into syntax; [l] is the number of binders in
    scope. Levels convert to indices by [l - k - 1]; closures are quoted by
    applying them to a fresh stuck variable. *)
val quote : int -> t -> Type.t

(** [normalize t] is the βδ-normal form of the closed term [t]:
    [quote 0 (eval [] t)] *)
val normalize : Type.t -> Type.t
