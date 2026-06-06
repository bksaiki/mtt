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

let mk loc desc = { loc; desc }

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
    (* ascription is the typed identity: applying (fun (x : A) => x) to [t]
       forces the checking judgment t ⇐ A, and the redex evaporates under
       evaluation. No core constructor needed. *)
    | Ascribe (t, a) -> Type.App (Type.Lam ("x", go env a, Type.Var 0), go env t)
  in
  go names s
