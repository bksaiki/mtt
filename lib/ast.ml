type t =
  { loc : Loc.t
  ; desc : desc
  }

and desc =
  | Var of string
  | Sort of int
  | Pi of string * t * t (* (x : A) -> B *)
  | Arrow of t * t (* A -> B *)
  | Lam of string * t * t (* fun (x : A) => b *)
  | App of t * t
  | Ascribe of t * t (* (t : A) *)
  | Unit
  | MkUnit
  | Empty
  | Absurd of t * t (* absurd A h *)
  | Sigma of string * t * t (* Σ (x : A) ⇒ B *)
  | Prod of t * t (* A × B *)
  | Pair of t * t (* (a, b) *)
  | Fst of t (* p.1 *)
  | Snd of t (* p.2 *)
  | Sum of t * t (* A + B *)
  | Inl of t (* inl a *)
  | Inr of t (* inr b *)
  | Case of t * t * t * t (* case P s u v *)
  | Eq of t * t * t (* Eq A x y *)
  | Refl (* refl *)
  | J of t * t * t (* J P d p *)
  | Nat (* Nat *)
  | Zero (* 0 *)
  | Succ of t (* succ n *)
  | NatRec of t * t * t * t (* natrec P pz ps n *)

let mk loc desc = { loc; desc }

(* a decimal literal [n] is sugar for [succ (succ ... zero)] with [n] succs,
   every node sharing the literal's location *)
let numeral loc n =
  let rec go acc i =
    if i = 0 then
      acc
    else
      go (mk loc (Succ acc)) (i - 1)
  in
  go (mk loc Zero) n

(* telescopes: a binder group [(x y : A)] is a name list and an annotation;
   [lams]/[pis] fold groups into nested lambdas / pis, stamping the synthetic
   binder nodes with the span of the whole construct *)

let lams loc groups body =
  List.fold_right
    (fun (xs, a) acc ->
      List.fold_right (fun x acc -> mk loc (Lam (x, a, acc))) xs acc)
    groups body

let pis loc groups body =
  List.fold_right
    (fun (xs, a) acc ->
      List.fold_right (fun x acc -> mk loc (Pi (x, a, acc))) xs acc)
    groups body

let sigmas loc groups body =
  List.fold_right
    (fun (xs, a) acc ->
      List.fold_right (fun x acc -> mk loc (Sigma (x, a, acc))) xs acc)
    groups body

let var_spine t =
  let rec go acc t =
    match t.desc with
    | Var x -> Some (x :: acc)
    | App (f, { desc = Var x; _ }) -> go (x :: acc) f
    | _ -> None
  in
  go [] t

exception Unbound_variable of Loc.t * string

let to_term names s =
  let rec go env s =
    match s.desc with
    | Var x -> (
        match List.find_index (String.equal x) env with
        | Some i -> Type.Var i
        | None -> raise (Unbound_variable (s.loc, x)))
    | Sort i -> Type.Sort i
    | Pi (x, a, b) -> Type.Pi (x, go env a, go (x :: env) b)
    (* non-dependent: extend the env with a dummy no identifier can equal, so
       indices in [b] still shift across the binder *)
    | Arrow (a, b) -> Type.Pi ("", go env a, go ("" :: env) b)
    | Lam (x, a, b) -> Type.Lam (x, go env a, go (x :: env) b)
    | App (f, a) -> Type.App (go env f, go env a)
    | Unit -> Type.Unit
    | MkUnit -> Type.MkUnit
    | Empty -> Type.Empty
    | Absurd (a, h) -> Type.Absurd (go env a, go env h)
    | Sigma (x, a, b) -> Type.Sigma (x, go env a, go (x :: env) b)
    (* non-dependent product: same dummy-binder trick as Arrow *)
    | Prod (a, b) -> Type.Sigma ("", go env a, go ("" :: env) b)
    | Pair (a, b) -> Type.Pair (go env a, go env b)
    | Fst t -> Type.Fst (go env t)
    | Snd t -> Type.Snd (go env t)
    | Sum (a, b) -> Type.Sum (go env a, go env b)
    | Inl t -> Type.Inl (go env t)
    | Inr t -> Type.Inr (go env t)
    | Case (p, s, u, v) -> Type.Case (go env p, go env s, go env u, go env v)
    | Eq (a, x, y) -> Type.Eq (go env a, go env x, go env y)
    | Refl -> Type.Refl
    | J (p, d, pr) -> Type.J (go env p, go env d, go env pr)
    | Nat -> Type.Nat
    | Zero -> Type.Zero
    | Succ n -> Type.Succ (go env n)
    | NatRec (p, z, s, n) -> Type.NatRec (go env p, go env z, go env s, go env n)
    (* ascription is the typed identity: applying (fun (x : A) => x) to [t]
       forces the checking judgment t ⇐ A, and the redex evaporates under
       evaluation. No core constructor needed. *)
    | Ascribe (t, a) -> Type.App (Type.Lam ("x", go env a, Type.Var 0), go env t)
  in
  go names s
