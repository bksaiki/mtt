type t =
  { loc : Loc.t
  ; desc : desc
  }

and desc =
  | Var of string
  | Field of t * string (* a named projection, e.g. [Nat.rec] *)
  | Sort of int
  | Pi of string * t * t (* (x : A) -> B *)
  | Arrow of t * t (* A -> B *)
  | Lam of string * t * t (* fun (x : A) => b *)
  | App of t * t
  | Ascribe of t * t (* (t : A) *)
  | MkUnit (* (), sugar for the prelude's Unit.unit *)
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
   [telescope] folds groups into nested binders built by [node], stamping each
   synthetic node with the span of the whole construct *)
let telescope node loc groups body =
  List.fold_right
    (fun (xs, a) acc ->
      List.fold_right (fun x acc -> mk loc (node x a acc)) xs acc)
    groups body

let lams = telescope (fun x a b -> Lam (x, a, b))

let pis = telescope (fun x a b -> Pi (x, a, b))

let sigmas = telescope (fun x a b -> Sigma (x, a, b))

let var_spine t =
  let rec go acc t =
    match t.desc with
    | Var x -> Some (x :: acc)
    | App (f, { desc = Var x; _ }) -> go (x :: acc) f
    | _ -> None
  in
  go [] t

exception Unbound_variable of Loc.t * string

let to_term sg names s =
  let rec go env s =
    match s.desc with
    (* a bare name is a local binder (de Bruijn) first, otherwise a global
       inductive former. Constructors are not bare: they are qualified [T.c]
       (handled below), so their names need only be unique within their type. *)
    | Var x -> (
        match List.find_index (String.equal x) env with
        | Some i -> Type.Var i
        | None -> (
            match Signature.find sg x with
            | Some spec -> Type.Ind spec.Inductive.name
            | None -> raise (Unbound_variable (s.loc, x))))
    (* qualified access on an inductive [T]: [T.rec] is its recursor, [T.c] one
       of its constructors *)
    | Field ({ desc = Var tname; _ }, field) -> (
        match Signature.find sg tname with
        | None -> raise (Unbound_variable (s.loc, tname))
        | Some spec -> (
            if String.equal field "rec" then
              Type.Rec (Inductive.rec_head spec)
            else
              match
                List.find_index
                  (fun (c : Inductive.ctor) -> String.equal c.cname field)
                  spec.Inductive.ctors
              with
              | Some i -> Type.Ctor (Inductive.ctor_head spec i)
              | None -> raise (Unbound_variable (s.loc, tname ^ "." ^ field))))
    | Field (_, f) -> raise (Unbound_variable (s.loc, "_." ^ f))
    | Sort i -> Type.Sort i
    | Pi (x, a, b) -> Type.Pi (x, go env a, go (x :: env) b)
    (* non-dependent: extend the env with a dummy no identifier can equal, so
       indices in [b] still shift across the binder *)
    | Arrow (a, b) -> Type.Pi ("", go env a, go ("" :: env) b)
    | Lam (x, a, b) -> Type.Lam (x, go env a, go (x :: env) b)
    | App (f, a) -> Type.App (go env f, go env a)
    (* () is sugar for the unit constructor; the unit type itself is the
       ordinary prelude inductive [Unit] (resolved as a [Var] above) *)
    | MkUnit -> (
        match Signature.find sg "Unit" with
        | Some spec -> Type.Ctor (Inductive.ctor_head spec 0)
        | None -> raise (Unbound_variable (s.loc, "() (Unit is not in scope)")))
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
