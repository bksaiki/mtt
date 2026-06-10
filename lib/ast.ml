(* a surface universe level: a concrete level [n], a level variable [u]
   (resolved against the level parameters in scope), or [max]/[imax] of two *)
type lvl =
  | LNat of int
  | LVar of string
  | LMax of lvl * lvl
  | LIMax of lvl * lvl

type t =
  { loc : Loc.t
  ; desc : desc
  }

and desc =
  | Var of string
  | Field of t * string (* a named projection, e.g. [Nat.rec] *)
  | Sort of lvl (* a sort at a (possibly variable) level: Prop=Sort 0, … *)
  | Pi of Type.icit * string * t * t (* (x : A) -> B / {x : A} -> B *)
  | Arrow of t * t (* A -> B *)
  | Lam of Type.icit * string * t * t (* fun (x : A) => b / fun {x : A} => b *)
  | App of t * t
  | At of t (* @f: make every argument explicit (suppress implicit insertion) *)
  | Match of t * (string * string list * t) list
    (* match e with | C x… => b … end: scrutinee and per-arm constructor name,
       pattern variables, body — case-analysis sugar for the recursor *)
  | Ascribe of t * t (* (t : A) *)
  | MkUnit (* (), sugar for the prelude's Unit.unit *)
  | Sigma of string * t * t (* Σ (x : A) ⇒ B *)
  | Prod of t * t (* A × B *)
  | Pair of t * t (* (a, b) *)
  | Fst of t (* p.1 *)
  | Snd of t (* p.2 *)
  | Sum of t * t (* A + B *)
  | EqInfix of t * t (* x = y: the equality former, with the type inferred *)
  | Numeral of int (* a decimal literal, e.g. 0, 5; sugar for succ … zero *)
  | Hole (* _, an elaboration hole (a fresh metavariable) *)

let mk loc desc = { loc; desc }

(* the free universe-level variables occurring in [t]'s [Sort u] annotations, in
   order of first appearance (deduped). A declaration's level parameters are
   auto-bound from these — Lean-style — so no explicit binder syntax is
   needed. *)
let level_vars t =
  let seen = ref [] in
  let add x = if not (List.mem x !seen) then seen := !seen @ [ x ] in
  let rec lv = function
    | LNat _ -> ()
    | LVar x -> add x
    | LMax (a, b)
    | LIMax (a, b) ->
        lv a;
        lv b
  in
  let rec go t =
    match t.desc with
    | Sort l -> lv l
    | Var _
    | MkUnit
    | Numeral _
    | Hole ->
        ()
    | Field (e, _)
    | Fst e
    | Snd e
    | At e ->
        go e
    | Pi (_, _, a, b)
    | Lam (_, _, a, b)
    | Arrow (a, b)
    | App (a, b)
    | Ascribe (a, b)
    | Sigma (_, a, b)
    | Prod (a, b)
    | Pair (a, b)
    | Sum (a, b)
    | EqInfix (a, b) ->
        go a;
        go b
    | Match (e, arms) ->
        go e;
        List.iter (fun (_, _, b) -> go b) arms
  in
  go t;
  !seen

(* telescopes: a binder group [(x y : A)] (or implicit [{x y : A}]) is a
   visibility, a name list, and an annotation; [telescope] folds groups into
   nested binders built by [node], stamping each synthetic node with the span of
   the whole construct *)
let telescope node loc groups body =
  List.fold_right
    (fun (i, xs, a) acc ->
      List.fold_right (fun x acc -> mk loc (node i x a acc)) xs acc)
    groups body

let lams = telescope (fun i x a b -> Lam (i, x, a, b))

let pis = telescope (fun i x a b -> Pi (i, x, a, b))

(* Σ binders carry no visibility (the parser only forms explicit ones) *)
let sigmas = telescope (fun _ x a b -> Sigma (x, a, b))

let var_spine t =
  let rec go acc t =
    match t.desc with
    | Var x -> Some (x :: acc)
    | App (f, { desc = Var x; _ }) -> go (x :: acc) f
    | _ -> None
  in
  go [] t

exception Unbound_variable of Loc.t * string
