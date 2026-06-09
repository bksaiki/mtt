(* The elaborator's metacontext and the unification/zonking that act on it. This
   lives entirely in the (untrusted) frontend: the kernel carries an inert
   [Meta] node it never inspects, and all knowledge of solutions is here. The
   context is a functional value, threaded by the caller (see {!Elab}); nothing
   here is global or mutable.

   Metavariables are non-contextual (they carry no spine): a solution may
   mention variables in scope at the meta's birth, which the scope check
   enforces. They reuse the kernel's NbE ([Value.apply]/[apply_closure]/[quote])
   — only the forcing of solutions is added on top, since the kernel itself does
   not force.

   Unification is deliberately lenient: it solves the flex-rigid case [?m := t]
   and walks rigid-rigid structurally, doing nothing on anything else (an
   applied flex, an occurs/scope failure, a rigid mismatch). Soundness rests on
   the kernel re-checking the fully zonked term, so an unsolved or
   wrongly-shaped constraint surfaces later as a type error, never a wrong
   acceptance. *)

module IMap = Map.Make (Int)

type entry =
  { ty : Value.t (* the metavariable's type, valid at its birth level *)
  ; blvl : int (* the de Bruijn level in scope when it was created *)
  ; soln : Value.t option
  }

type t =
  { next : int
  ; entries : entry IMap.t
  }

let empty = { next = 0; entries = IMap.empty }

let fresh ms ~blvl ty =
  let i = ms.next in
  ( { next = i + 1; entries = IMap.add i { ty; blvl; soln = None } ms.entries }
  , i )

let typ ms i = (IMap.find i ms.entries).ty

let solution ms i = (IMap.find i ms.entries).soln

let solve ms i v =
  let e = IMap.find i ms.entries in
  { ms with entries = IMap.add i { e with soln = Some v } ms.entries }

(* peel a neutral into its head and argument spine (outermost-first) *)
let rec peel (n : Value.neutral) : Value.neutral * Value.t list =
  match n with
  | Value.App (f, a) ->
      let h, args = peel f in
      (h, args @ [ a ])
  | h -> (h, [])

(* unfold a solved metavariable at the head of [v] (re-applying its solution to
   the spine); a meta-free or unsolved-headed value is returned unchanged *)
let rec force ms (v : Value.t) : Value.t =
  match v with
  | Value.Neutral n -> (
      match peel n with
      | Value.Meta i, sp -> (
          match solution ms i with
          | Some s -> force ms (List.fold_left Value.apply s sp)
          | None -> v)
      | _ -> v)
  | _ -> v

(* a value that is a metavariable applied to a spine, if any *)
let as_flex (v : Value.t) : (int * Value.t list) option =
  match v with
  | Value.Neutral n -> (
      match peel n with
      | Value.Meta m, sp -> Some (m, sp)
      | _ -> None)
  | _ -> None

(* whether [rhs] (a value seen at level [entry]) is a legal solution for a meta
   [m] born at level [blvl]: no occurrence of [m] (occurs check) and no variable
   in [\[blvl, entry)] — those are binders introduced after the meta, capturing
   which would let the solution escape its scope. *)
let scope_ok ms blvl m entry rhs =
  let rec ok lvl v =
    match force ms v with
    | Value.Sort _
    | Value.Refl ->
        true
    | Value.Eq (a, x, y) -> ok lvl a && ok lvl x && ok lvl y
    | Value.Pi (_, a, c)
    | Value.Lam (_, a, c) ->
        ok lvl a
        && ok (lvl + 1) (Value.apply_closure c (Value.Neutral (Var lvl)))
    | Value.VInd (_, args)
    | Value.VCtor (_, args)
    | Value.VRec (_, args) ->
        List.for_all (ok lvl) args
    | Value.Neutral n -> okn lvl n
  and okn lvl n =
    match n with
    | Value.Var k -> k < blvl || k >= entry
    | Value.Meta m' -> m' <> m
    | Value.App (f, a) -> okn lvl f && ok lvl a
    | Value.Proj (_, f) -> okn lvl f
    | Value.J (p, d, f) -> ok lvl p && ok lvl d && okn lvl f
    | Value.Rec (_, pre, f) -> List.for_all (ok lvl) pre && okn lvl f
  in
  ok entry rhs

(* solve an unapplied flex [?m := rhs] when [rhs] is in scope for it; an applied
   flex [?m sp] is left alone (a higher-order case this pass does not handle) *)
let solve_flex ms entry m sp rhs =
  match sp with
  | [] ->
      if scope_ok ms (IMap.find m ms.entries).blvl m entry rhs then
        solve ms m rhs
      else
        ms
  | _ -> ms

(* unify two values at de Bruijn level [lvl], returning the updated context *)
let rec unify ms lvl (v1 : Value.t) (v2 : Value.t) : t =
  let v1 = force ms v1 and v2 = force ms v2 in
  match (as_flex v1, as_flex v2) with
  | Some (m, sp), _ -> solve_flex ms lvl m sp v2
  | _, Some (m, sp) -> solve_flex ms lvl m sp v1
  | None, None -> unify_rigid ms lvl v1 v2

and unify_rigid ms lvl v1 v2 =
  match (v1, v2) with
  | Value.Pi (_, a1, c1), Value.Pi (_, a2, c2)
  | Value.Lam (_, a1, c1), Value.Lam (_, a2, c2) ->
      let ms = unify ms lvl a1 a2 in
      let v = Value.Neutral (Value.Var lvl) in
      unify ms (lvl + 1) (Value.apply_closure c1 v) (Value.apply_closure c2 v)
  | Value.Eq (a1, x1, y1), Value.Eq (a2, x2, y2) ->
      unify (unify (unify ms lvl a1 a2) lvl x1 x2) lvl y1 y2
  | Value.VInd (n1, as1), Value.VInd (n2, as2) when String.equal n1 n2 ->
      unify_args ms lvl as1 as2
  | Value.VCtor (h1, as1), Value.VCtor (h2, as2)
    when String.equal h1.Type.cname h2.Type.cname ->
      unify_args ms lvl as1 as2
  | Value.VRec (h1, as1), Value.VRec (h2, as2)
    when String.equal h1.Type.rind h2.Type.rind ->
      unify_args ms lvl as1 as2
  | Value.Neutral n1, Value.Neutral n2 -> unify_neutral ms lvl n1 n2
  (* sorts, refl, and any rigid-rigid mismatch: nothing to solve — defer to the
     kernel's own conversion check on the zonked term *)
  | _ -> ms

and unify_args ms lvl as1 as2 =
  match (as1, as2) with
  | a1 :: r1, a2 :: r2 -> unify_args (unify ms lvl a1 a2) lvl r1 r2
  | _ -> ms

and unify_neutral ms lvl (n1 : Value.neutral) (n2 : Value.neutral) =
  match (n1, n2) with
  | Value.App (f1, a1), Value.App (f2, a2) ->
      unify (unify_neutral ms lvl f1 f2) lvl a1 a2
  | Value.Proj (i1, f1), Value.Proj (i2, f2) when i1 = i2 ->
      unify_neutral ms lvl f1 f2
  | Value.J (p1, d1, f1), Value.J (p2, d2, f2) ->
      unify_neutral (unify (unify ms lvl p1 p2) lvl d1 d2) lvl f1 f2
  | Value.Rec (h1, pre1, f1), Value.Rec (h2, pre2, f2)
    when String.equal h1.Type.rind h2.Type.rind ->
      unify_neutral (unify_args ms lvl pre1 pre2) lvl f1 f2
  | _ -> ms

(* replace every solved metavariable in [t] by its solution, read back as core
   at the use-site level [lvl] (so de Bruijn indices are reuse-safe — a stored
   solution is a value with absolute levels). An unsolved meta is left in place;
   {!Type.has_meta} on the result then detects it. *)
let rec zonk ms lvl (t : Type.t) : Type.t =
  match t with
  | Type.Meta i -> (
      match solution ms i with
      | Some v -> zonk ms lvl (Value.quote lvl v)
      | None -> t)
  | Type.Var _
  | Type.Sort _
  | Type.Refl
  | Type.Ind _
  | Type.Ctor _
  | Type.Rec _ ->
      t
  | Type.Proj (i, a) -> Type.Proj (i, zonk ms lvl a)
  | Type.Pi (x, a, b) -> Type.Pi (x, zonk ms lvl a, zonk ms (lvl + 1) b)
  | Type.Lam (x, a, b) -> Type.Lam (x, zonk ms lvl a, zonk ms (lvl + 1) b)
  | Type.App (f, a) -> Type.App (zonk ms lvl f, zonk ms lvl a)
  | Type.Eq (a, x, y) -> Type.Eq (zonk ms lvl a, zonk ms lvl x, zonk ms lvl y)
  | Type.J (p, d, pr) -> Type.J (zonk ms lvl p, zonk ms lvl d, zonk ms lvl pr)
