(** Abstract syntax tree (AST) *)
type t =
  | Var of string
  | Sort of int
  | Pi of string * t * t (* (x : A) -> B *)
  | Arrow of t * t (* A -> B *)
  | Lam of string * t * t (* fun (x : A) => b *)
  | App of t * t
  | Ascribe of t * t (* (t : A) *)

(* telescopes: a binder group [(x y : A)] is a name list and an annotation;
   [lams]/[pis] fold groups into nested lambdas / pis *)

let lams groups body =
  List.fold_right
    (fun (xs, a) acc -> List.fold_right (fun x acc -> Lam (x, a, acc)) xs acc)
    groups body

let pis groups body =
  List.fold_right
    (fun (xs, a) acc -> List.fold_right (fun x acc -> Pi (x, a, acc)) xs acc)
    groups body

(** [var_spine t] is [Some [x1; ...; xn]] if [t] is an application spine of
    variables [x1 ... xn]: used to read the ascription [(x y : A)] as a
    multi-name pi binder when it appears left of an arrow *)
let var_spine t =
  let rec go acc = function
    | Var x -> Some (x :: acc)
    | App (f, Var x) -> go (x :: acc) f
    | _ -> None
  in
  go [] t

exception Unbound_variable of string

(** [to_term names s] scope-checks [s], converting named binders to de Bruijn
    indices; [names] binds free variables (innermost first), e.g. top-level
    declarations. Raises {!Unbound_variable} if a variable is not in scope. *)
let to_term names s =
  let rec go env = function
    | Var x -> (
        match List.find_index (String.equal x) env with
        | Some i -> Type.Var i
        | None -> raise (Unbound_variable x))
    | Sort i -> Type.Sort i
    | Pi (x, a, b) -> Type.Pi (x, go env a, go (x :: env) b)
    (* non-dependent: extend the env with a dummy no identifier can equal, so
       indices in [b] still shift across the binder *)
    | Arrow (a, b) -> Type.Pi ("", go env a, go ("" :: env) b)
    | Lam (x, a, b) -> Type.Lam (x, go env a, go (x :: env) b)
    | App (f, a) -> Type.App (go env f, go env a)
    (* ascription is the typed identity: applying (fun (x : A) => x) to [t]
       forces the checking judgment t ⇐ A, and the redex evaporates under
       evaluation. No core constructor needed. *)
    | Ascribe (t, a) -> Type.App (Type.Lam ("x", go env a, Type.Var 0), go env t)
  in
  go names s
