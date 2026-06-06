(** semantic values: the result of evaluation; binder bodies are closures
    holding unevaluated syntax, and stuck variables are de Bruijn levels *)
type t =
  | Univ of int
  | Pi of string * t * closure
  | Lam of string * t * closure
  | Neutral of neutral

and neutral =
  | Var of int (* de Bruijn level *)
  | App of neutral * t

and closure = {
  env : env;
  body : Type.term;
}

and env = t list

exception Not_a_function

(** [eval env t] evaluates [t] in [env], which must bind every free index *)
let rec eval env (t : Type.term) : t =
  match t with
  | Type.Var i -> List.nth env i
  | Type.Univ i -> Univ i
  | Type.Pi (x, a, b) -> Pi (x, eval env a, { env; body = b })
  | Type.Lam (x, a, b) -> Lam (x, eval env a, { env; body = b })
  | Type.App (f, a) -> apply (eval env f) (eval env a)

(* beta reduction is just evaluating the closure body in an extended
   environment: no substitution, no index shifting *)
and apply f a =
  match f with
  | Lam (_, _, c) -> apply_closure c a
  | Neutral n -> Neutral (App (n, a))
  | _ -> raise Not_a_function

and apply_closure { env; body } a = eval (a :: env) body

(** [quote l v] reads a value back into syntax; [l] is the number of binders
    in scope. Levels convert to indices by [l - k - 1]. *)
let rec quote l (v : t) : Type.term =
  match v with
  | Univ i -> Type.Univ i
  | Pi (x, a, c) -> Type.Pi (x, quote l a, quote_closure l c)
  | Lam (x, a, c) -> Type.Lam (x, quote l a, quote_closure l c)
  | Neutral n -> quote_neutral l n

(* to go under a binder, apply the closure to a fresh stuck variable *)
and quote_closure l c = quote (l + 1) (apply_closure c (Neutral (Var l)))

and quote_neutral l = function
  | Var k -> Type.Var (l - k - 1)
  | App (n, a) -> Type.App (quote_neutral l n, quote l a)

(** [normalize t] is the beta-normal form of closed term [t] *)
let normalize t = quote 0 (eval [] t)
