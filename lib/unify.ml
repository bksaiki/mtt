(* Unification for the elaborator. Operates on kernel {!Value.t}, solving
   metavariables in the kernel metacontext; it reuses the kernel's NbE
   ([force]/[apply_closure]) rather than reimplementing reduction.

   Metavariables are non-contextual (carry no spine), so the only solving rule
   is the flex-rigid one [?m := t] with an occurs/scope check (see {!scope_ok});
   everything else is a structural rigid-rigid walk. It is deliberately {e
   lenient}: on anything it cannot solve (an applied flex, an occurs/scope
   failure, a rigid-rigid mismatch) it does nothing rather than erroring.
   Soundness is not at stake — the kernel re-checks the fully zonked term — so
   an unsolved constraint surfaces later as a "cannot infer"/type error, never
   as a wrong acceptance. *)

(* peel a neutral into its head and argument spine (outermost-first) *)
let rec peel (n : Value.neutral) : Value.neutral * Value.t list =
  match n with
  | Value.App (f, a) ->
      let h, args = peel f in
      (h, args @ [ a ])
  | h -> (h, [])

(* a value that is a metavariable applied to a spine, if any *)
let as_flex (v : Value.t) : (int * Value.t list) option =
  match v with
  | Value.Neutral n -> (
      match peel n with
      | Value.Meta m, sp -> Some (m, sp)
      | _ -> None)
  | _ -> None

(* whether [rhs] (a value seen at level [entry]) is a legal solution for a meta
   [m] born at level [blvl]: it must not mention [m] (occurs check) nor any
   variable in [\[blvl, entry)] — those are binders introduced after the meta,
   so capturing them would let the solution escape its scope. Variables below
   [blvl] (in scope at the meta's birth) and variables at or above [entry]
   (bound within [rhs] itself) are fine. *)
let scope_ok blvl m entry rhs =
  let rec ok lvl v =
    match Value.force v with
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

(* solve a non-contextual meta [?m := rhs] (an unapplied flex), when [rhs] is in
   scope for it; an applied flex [?m sp] is left for the kernel (a higher-order
   case this pass does not handle) *)
let solve entry m sp rhs =
  match sp with
  | [] ->
      if scope_ok (Value.meta_blvl m) m entry rhs then Value.solve_meta m rhs
  | _ -> ()

(* unify two values at de Bruijn level [lvl] *)
let rec unify lvl (v1 : Value.t) (v2 : Value.t) : unit =
  let v1 = Value.force v1 and v2 = Value.force v2 in
  match (as_flex v1, as_flex v2) with
  | Some (m, sp), _ -> solve lvl m sp v2
  | _, Some (m, sp) -> solve lvl m sp v1
  | None, None -> unify_rigid lvl v1 v2

and unify_rigid lvl v1 v2 =
  let go_under c1 c2 =
    let v = Value.Neutral (Value.Var lvl) in
    unify (lvl + 1) (Value.apply_closure c1 v) (Value.apply_closure c2 v)
  in
  match (v1, v2) with
  | Value.Pi (_, a1, c1), Value.Pi (_, a2, c2)
  | Value.Lam (_, a1, c1), Value.Lam (_, a2, c2) ->
      unify lvl a1 a2;
      go_under c1 c2
  | Value.Eq (a1, x1, y1), Value.Eq (a2, x2, y2) ->
      unify lvl a1 a2;
      unify lvl x1 x2;
      unify lvl y1 y2
  | Value.VInd (n1, as1), Value.VInd (n2, as2) when String.equal n1 n2 ->
      unify_args lvl as1 as2
  | Value.VCtor (h1, as1), Value.VCtor (h2, as2)
    when String.equal h1.Type.cname h2.Type.cname ->
      unify_args lvl as1 as2
  | Value.VRec (h1, as1), Value.VRec (h2, as2)
    when String.equal h1.Type.rind h2.Type.rind ->
      unify_args lvl as1 as2
  | Value.Neutral n1, Value.Neutral n2 -> unify_neutral lvl n1 n2
  (* sorts, refl, and any rigid-rigid mismatch: nothing to solve — defer to the
     kernel's own conversion check on the zonked term *)
  | _ -> ()

and unify_args lvl as1 as2 =
  match (as1, as2) with
  | [], [] -> ()
  | a1 :: r1, a2 :: r2 ->
      unify lvl a1 a2;
      unify_args lvl r1 r2
  | _ -> ()

and unify_neutral lvl (n1 : Value.neutral) (n2 : Value.neutral) =
  match (n1, n2) with
  | Value.Var l1, Value.Var l2 when l1 = l2 -> ()
  | Value.App (f1, a1), Value.App (f2, a2) ->
      unify_neutral lvl f1 f2;
      unify lvl a1 a2
  | Value.Proj (i1, f1), Value.Proj (i2, f2) when i1 = i2 ->
      unify_neutral lvl f1 f2
  | Value.J (p1, d1, f1), Value.J (p2, d2, f2) ->
      unify lvl p1 p2;
      unify lvl d1 d2;
      unify_neutral lvl f1 f2
  | Value.Rec (h1, pre1, f1), Value.Rec (h2, pre2, f2)
    when String.equal h1.Type.rind h2.Type.rind ->
      unify_args lvl pre1 pre2;
      unify_neutral lvl f1 f2
  | _ -> ()
