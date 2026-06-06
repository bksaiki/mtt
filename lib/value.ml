type t =
  | Sort of int
  | Pi of string * t * closure
  | Lam of string * t * closure
  | Unit
  | MkUnit
  | Empty
  | Neutral of neutral

and neutral =
  | Var of int (* de Bruijn level *)
  | App of neutral * t
  | Absurd of t * neutral (* a stuck ex falso: motive and stuck proof *)

and closure =
  { env : env
  ; body : Type.t
  }

and env = t list

exception Not_a_function

let rec eval env t =
  match t with
  | Type.Var i -> List.nth env i
  | Type.Sort i -> Sort i
  | Type.Unit -> Unit
  | Type.MkUnit -> MkUnit
  | Type.Empty -> Empty
  (* Empty has no introduction forms, so a well-typed scrutinee can only be
     stuck: absurd is always a neutral *)
  | Type.Absurd (a, h) -> (
      match eval env h with
      | Neutral n -> Neutral (Absurd (eval env a, n))
      | _ -> assert false)
  | Type.Pi (x, a, b) -> Pi (x, eval env a, { env; body = b })
  | Type.Lam (x, a, b) -> Lam (x, eval env a, { env; body = b })
  | Type.App (f, a) -> apply (eval env f) (eval env a)

(* β-reduction: (fun (x : A) => b) a ≡ b[a/x]. The substitution is just
   evaluating the closure body in an extended environment: no term-level
   substitution, no index shifting. Stuck applications (head is a variable)
   accumulate as neutral spines instead. *)
and apply f a =
  match f with
  | Lam (_, _, c) -> apply_closure c a
  | Neutral n -> Neutral (App (n, a))
  | _ -> raise Not_a_function

and apply_closure { env; body } a = eval (a :: env) body

let rec quote l v =
  match v with
  | Sort i -> Type.Sort i
  | Unit -> Type.Unit
  | MkUnit -> Type.MkUnit
  | Empty -> Type.Empty
  | Pi (x, a, c) -> Type.Pi (x, quote l a, quote_closure l c)
  | Lam (x, a, c) -> Type.Lam (x, quote l a, quote_closure l c)
  | Neutral n -> quote_neutral l n

(* to go under a binder, apply the closure to a fresh stuck variable *)
and quote_closure l c = quote (l + 1) (apply_closure c (Neutral (Var l)))

and quote_neutral l = function
  (* level → index: the variable bound under k other binders, seen from under l
     binders, is index l - k - 1 *)
  | Var k -> Type.Var (l - k - 1)
  | App (n, a) -> Type.App (quote_neutral l n, quote l a)
  | Absurd (a, n) -> Type.Absurd (quote l a, quote_neutral l n)

let normalize t = quote 0 (eval [] t)
