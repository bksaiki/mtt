type t =
  | Sort of int
  | Pi of string * t * closure
  | Lam of string * t * closure
  | Unit
  | MkUnit
  | Empty
  | Sigma of string * t * closure
  | Pair of t * t
  | Sum of t * t
  | Inl of t
  | Inr of t
  | Eq of t * t * t
  | Refl
  | Nat
  | Zero
  | Succ of t
  | Neutral of neutral

and neutral =
  | Var of int (* de Bruijn level *)
  | App of neutral * t
  | Absurd of t * neutral (* a stuck ex falso: motive and stuck proof *)
  | Fst of neutral (* a stuck first projection *)
  | Snd of neutral (* a stuck second projection *)
  | Case of t * neutral * t * t (* a stuck case: motive, scrutinee, branches *)
  | J of t * t * neutral (* a stuck J: motive, diagonal, stuck proof *)
  | NatRec of
      t * t * t * neutral (* a stuck recursion: motive, base, step, scrutinee *)

and closure =
  { env : env
  ; body : Type.t
  }

and env = t list

exception Not_a_function

let rec eval env t =
  match t with
  | Type.Unit -> Unit
  | Type.MkUnit -> MkUnit
  | Type.Empty -> Empty
  | Type.Var i -> List.nth env i
  | Type.Sort i -> Sort i
  | Type.Pi (x, a, b) -> Pi (x, eval env a, { env; body = b })
  | Type.Lam (x, a, b) -> Lam (x, eval env a, { env; body = b })
  | Type.App (f, a) -> apply (eval env f) (eval env a)
  (* Empty has no introduction forms, so a well-typed scrutinee can only be
     stuck: absurd is always a neutral *)
  | Type.Absurd (a, h) -> (
      match eval env h with
      | Neutral n -> Neutral (Absurd (eval env a, n))
      | _ -> assert false)
  | Type.Sigma (x, a, b) -> Sigma (x, eval env a, { env; body = b })
  | Type.Pair (a, b) -> Pair (eval env a, eval env b)
  | Type.Fst t -> vfst (eval env t)
  | Type.Snd t -> vsnd (eval env t)
  | Type.Sum (a, b) -> Sum (eval env a, eval env b)
  | Type.Inl t -> Inl (eval env t)
  | Type.Inr t -> Inr (eval env t)
  | Type.Case (p, s, u, v) ->
      vcase (eval env p) (eval env s) (eval env u) (eval env v)
  | Type.Eq (a, x, y) -> Eq (eval env a, eval env x, eval env y)
  | Type.Refl -> Refl
  | Type.J (p, d, pr) -> vj (eval env p) (eval env d) (eval env pr)
  | Type.Nat -> Nat
  | Type.Zero -> Zero
  | Type.Succ n -> Succ (eval env n)
  | Type.NatRec (p, z, s, n) ->
      vnatrec (eval env p) (eval env z) (eval env s) (eval env n)

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

(* projections: reduce on a pair, get stuck on a neutral. Anything else is
   ill-typed (unreachable for checked terms). *)
and vfst = function
  | Pair (a, _) -> a
  | Neutral n -> Neutral (Fst n)
  | _ -> assert false

and vsnd = function
  | Pair (_, b) -> b
  | Neutral n -> Neutral (Snd n)
  | _ -> assert false

(* ι-reduction: a case on an injection picks the matching branch; a stuck
   scrutinee freezes the whole case as a neutral frame *)
and vcase p s u v =
  match s with
  | Inl a -> apply u a
  | Inr b -> apply v b
  | Neutral n -> Neutral (Case (p, n, u, v))
  | _ -> assert false

(* ι-reduction: J on refl picks the diagonal case; a stuck proof freezes the
   whole elimination as a neutral frame *)
and vj p d pr =
  match pr with
  | Refl -> d
  | Neutral n -> Neutral (J (p, d, n))
  | _ -> assert false

(* recursion: the step receives the predecessor and the recursive result on it
   (the induction hypothesis); a stuck scrutinee freezes the whole recursion.
   Terminates by descending on the structurally smaller predecessor. *)
and vnatrec p z s n =
  match n with
  | Zero -> z
  | Succ m -> apply (apply s m) (vnatrec p z s m)
  | Neutral ne -> Neutral (NatRec (p, z, s, ne))
  | _ -> assert false

let rec quote l v =
  match v with
  | Sort i -> Type.Sort i
  | Unit -> Type.Unit
  | MkUnit -> Type.MkUnit
  | Empty -> Type.Empty
  | Sum (a, b) -> Type.Sum (quote l a, quote l b)
  | Inl t -> Type.Inl (quote l t)
  | Inr t -> Type.Inr (quote l t)
  | Eq (a, x, y) -> Type.Eq (quote l a, quote l x, quote l y)
  | Refl -> Type.Refl
  | Nat -> Type.Nat
  | Zero -> Type.Zero
  | Succ n -> Type.Succ (quote l n)
  | Pi (x, a, c) -> Type.Pi (x, quote l a, quote_closure l c)
  | Lam (x, a, c) -> Type.Lam (x, quote l a, quote_closure l c)
  | Sigma (x, a, c) -> Type.Sigma (x, quote l a, quote_closure l c)
  | Pair (a, b) -> Type.Pair (quote l a, quote l b)
  | Neutral n -> quote_neutral l n

(* to go under a binder, apply the closure to a fresh stuck variable *)
and quote_closure l c = quote (l + 1) (apply_closure c (Neutral (Var l)))

and quote_neutral l = function
  (* level → index: the variable bound under k other binders, seen from under l
     binders, is index l - k - 1 *)
  | Var k -> Type.Var (l - k - 1)
  | App (n, a) -> Type.App (quote_neutral l n, quote l a)
  | Absurd (a, n) -> Type.Absurd (quote l a, quote_neutral l n)
  | Fst n -> Type.Fst (quote_neutral l n)
  | Snd n -> Type.Snd (quote_neutral l n)
  | Case (p, n, u, v) ->
      Type.Case (quote l p, quote_neutral l n, quote l u, quote l v)
  | J (p, d, n) -> Type.J (quote l p, quote l d, quote_neutral l n)
  | NatRec (p, z, s, n) ->
      Type.NatRec (quote l p, quote l z, quote l s, quote_neutral l n)

let normalize t = quote 0 (eval [] t)
