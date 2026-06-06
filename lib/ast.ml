(** Abstract syntax tree (AST) *)
type t =
  | Var of string
  | Univ of int
  | Pi of string * t * t (* (x : A) -> B *)
  | Arrow of t * t (* A -> B *)
  | Lam of string * t * t (* fun (x : A) => b *)
  | App of t * t

exception Unbound_variable of string

(** [to_term s] scope-checks [s], converting named binders to de Bruijn indices.
    Raises {!Unbound_variable} if a variable is not in scope. *)
let to_term s =
  let rec go env = function
    | Var x -> (
        match List.find_index (String.equal x) env with
        | Some i -> Type.Var i
        | None -> raise (Unbound_variable x))
    | Univ i -> Type.Univ i
    | Pi (x, a, b) -> Type.Pi (x, go env a, go (x :: env) b)
    (* non-dependent: extend the env with a dummy no identifier can equal, so
       indices in [b] still shift across the binder *)
    | Arrow (a, b) -> Type.Pi ("", go env a, go ("" :: env) b)
    | Lam (x, a, b) -> Type.Lam (x, go env a, go (x :: env) b)
    | App (f, a) -> Type.App (go env f, go env a)
  in
  go [] s
