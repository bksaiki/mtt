type ctx =
  { env : Value.env (* values of bound variables, for evaluation *)
  ; types : Value.t list (* their types, index-aligned with [env] *)
  ; names : string list (* binder names, for error messages *)
  ; lvl : int (* binders in scope = next fresh de Bruijn level *)
  ; signature : Signature.t (* the inductive types declared so far *)
  }

let empty =
  { env = []; types = []; names = []; lvl = 0; signature = Signature.empty }

(* extends the context with [x : ty] whose value is [v] *)
let extend x v ty ctx =
  { ctx with
    env = v :: ctx.env
  ; types = ty :: ctx.types
  ; names = x :: ctx.names
  ; lvl = ctx.lvl + 1
  }

(* a variable bound to a fresh neutral, so under the binder it blocks reduction
   instead of disappearing. [extend] (above) is the counterpart that binds a
   real value, so occurrences unfold (δ-reduction). *)
let bind x ty ctx = extend x (Value.Neutral (Value.Var ctx.lvl)) ty ctx

(* extends the context with a {e universe-polymorphic} def [x], abstracted over
   [nlevels] level parameters: its core [body] and [ty] (both mentioning those
   parameters as [Sort (Var j)]) are stored as [Value.VPoly] thunks over the
   current environment. A use of [x] is a [Type.Def (i, ls)] whose
   [eval]/[infer] instantiate the thunk at the use-site levels [ls].
   (Monomorphic defs use {!extend} and a plain [Var]; this is the
   level-abstracted counterpart.) *)
let extend_poly x ~nlevels ~body ~ty ctx =
  let thunk b = Value.VPoly { nlevels; denv = ctx.env; body = b } in
  { ctx with
    env = thunk body :: ctx.env
  ; types = thunk ty :: ctx.types
  ; names = x :: ctx.names
  ; lvl = ctx.lvl + 1
  }

(* registers an inductive declaration in the context's signature *)
let add_ind spec ctx = { ctx with signature = Signature.add spec ctx.signature }

(* the declared inductive [name], or a type error if it is unknown *)
let lookup_ind ctx name =
  match Signature.find ctx.signature name with
  | Some spec -> spec
  | None -> Error.type_error [ Error.txtf "unknown inductive type %s" name ]

(* the kernel's faithful renderer (no notation): a plain view of a value against
   the context's binder names, for kernel-internal use and debugging.
   User-facing output and error messages are rendered by the frontend, which
   owns notation — output via its own renderer, errors from the [tm]/[vl]
   fragments these build. *)
let show ctx v = Type.to_string_in ctx.names (Value.quote ctx.lvl v)

(* error fragments for a term and a value, capturing the binder names they are
   read against (the value is quoted now, with no notation; rendering is the
   frontend's, later). [tm] is kernel-internal; [vl] is also used by the
   driver. *)
let tm ctx (t : Type.t) = Error.Term (ctx.names, t)

let vl ctx (v : Value.t) = Error.Term (ctx.names, Value.quote ctx.lvl v)

(* imax i 0 = 0: a product into a proposition is a proposition *)
let imax = Level.imax

(* the fresh variable for going under a binder *)
let fresh ctx = Value.Neutral (Value.Var ctx.lvl)

(* builds a dependent function type [Π (name : aval) ⇒ B] as a value, where the
   codomain is computed by [k] given the extended context and the bound
   variable's value. The quote/eval round-trip handles the de Bruijn
   bookkeeping: applying the closure to an argument re-runs [k]'s result with
   the bound variable replaced by that argument. *)
let pi_val ctx name aval k =
  let ctx' = bind name aval ctx in
  let bval = k ctx' (fresh ctx) in
  Value.Pi
    ( Type.Explicit
    , name
    , aval
    , { env = ctx.env; body = Value.quote ctx'.lvl bval } )

(* The minor-premise type for the [i]-th constructor of [spec], given the
   recursor's parameter values [pvals] and motive value [pmot]:

   Π (f₀ : F₀) ⇒ [P f₀ ⇒] … Π (fₙ : Fₙ) ⇒ [P fₙ ⇒] P (c params fields)

   i.e. a binder per field, an induction hypothesis [P fⱼ] after each recursive
   field, concluding in the motive applied to the constructor. Field types come
   from the spec (in the context [params, earlier fields]) and are evaluated
   with the parameters and earlier fields substituted. *)
(* the motive [pmot] applied to a target at index instances [idxs]: [P idxs
   target] (for a non-indexed family this is just [P target]) *)
let motive_app pmot idxs target =
  List.fold_left Value.apply pmot (idxs @ [ target ])

let minor_type ?(levels = []) ctx spec pvals pmot i =
  let c = List.nth spec.Inductive.ctors i in
  let chead = Inductive.ctor_head ~levels spec i in
  (* the spec's field and index types carry the inductive's level variables;
     instantiate them with the recursor's level arguments before evaluating *)
  let inst t = Type.subst_levels levels t in
  (* fieldvals is innermost-first; a spec term read in the context [params,
     earlier fields] is evaluated against [earlier fields (newest first)] ++
     [params (reverse)] *)
  let rec go ctx fieldvals = function
    | [] ->
        let env = fieldvals @ List.rev pvals in
        let ctor =
          List.fold_left Value.apply
            (Value.VCtor (chead, []))
            (pvals @ List.rev fieldvals)
        in
        let idxs =
          List.map (fun e -> Value.eval env (inst e)) c.result_indices
        in
        motive_app pmot idxs ctor
    | (a : Inductive.arg) :: rest ->
        let env = fieldvals @ List.rev pvals in
        let aval = Value.eval env (inst a.aty) in
        pi_val ctx a.aname aval (fun ctx' fv ->
            match a.recursive with
            | Some idx_exprs ->
                (* the induction hypothesis [P field_indices field] *)
                let idxs =
                  List.map (fun e -> Value.eval env (inst e)) idx_exprs
                in
                pi_val ctx' "_ih" (motive_app pmot idxs fv) (fun ctx'' _ ->
                    go ctx'' (fv :: fieldvals) rest)
            | None -> go ctx' (fv :: fieldvals) rest)
  in
  go ctx [] c.fields

(* the type value of a constructor head: its full [(params) -> (fields) -> Ind
   params] Pi, used to walk a constructor's argument spine type-directedly *)
let ctor_type_val ctx (h : Type.ctor_head) =
  Value.eval [] (Inductive.ctor_type (lookup_ind ctx h.ind) h.cindex)

(* the type of the [i]-th field of a record value [v] of type [Ind params]: the
   field's declared type, instantiated by the parameters and by the earlier
   projections of [v] (so a dependent field sees the values it depends on) *)
let field_type spec params v i =
  let c = List.nth spec.Inductive.ctors 0 in
  let a = List.nth c.fields i in
  let proj_env =
    List.init i (fun j -> Value.vproj (i - 1 - j) v) @ List.rev params
  in
  Value.eval proj_env a.Inductive.aty

(* the type of a stuck neutral, reconstructed by walking the spine *)
let rec infer_neutral ctx (n : Value.neutral) : Value.t =
  match n with
  | Value.Var k -> List.nth ctx.types (ctx.lvl - k - 1)
  (* metavariables never reach the kernel: the elaborator zonks them away before
     any check, so an inert [Meta] head here is impossible *)
  | Value.Meta _ -> assert false
  | Value.App (m, a) -> (
      match infer_neutral ctx m with
      | Value.Pi (_, _, _, c) -> Value.apply_closure c a
      | _ -> assert false (* values are well-typed by invariant *))
  | Value.Proj (i, n) -> (
      match infer_neutral ctx n with
      | Value.VInd (name, _, params) ->
          field_type (lookup_ind ctx name) params (Value.Neutral n) i
      | _ -> assert false)
  (* T.rec params P minors major : P major; the motive sits after the params in
     the recorded pre-major spine *)
  | Value.Rec (h, pre, n) ->
      let motive = List.nth pre h.Type.nparams in
      Value.apply motive (Value.Neutral n)

(* [sort_of ctx ty] is the level [i] such that [ty : Sort i] *)
let rec sort_of ctx (ty : Value.t) : Level.t =
  match ty with
  | Value.Sort i -> Level.succ i
  | Value.Pi (_, x, a, c) ->
      let j = sort_of (bind x a ctx) (Value.apply_closure c (fresh ctx)) in
      imax (sort_of ctx a) j
  | Value.Neutral n -> (
      match infer_neutral ctx n with
      | Value.Sort i -> i
      | _ -> assert false)
  (* an inductive type lives at its declared sort, instantiated by its level
     arguments (identity while monomorphic) *)
  | Value.VInd (name, ls, _) ->
      Level.subst ls (lookup_ind ctx name).Inductive.sort
  (* not types *)
  | Value.VCtor _
  | Value.VRec _
  | Value.VPoly _
  | Value.Lam _ ->
      assert false

(* type-directed conversion: [conv] compares terms at a type, [conv_ty] compares
   types themselves (by equality — there is no cumulativity). β/δ have already
   happened during evaluation, so this is structural comparison of weak-head
   forms, going under binders with fresh variables. *)
let rec conv ctx ty v1 v2 =
  (* proof irrelevance: the type is a proposition (Sort 0) *)
  Level.equal (sort_of ctx ty) Level.zero
  ||
  match ty with
  (* η *)
  | Value.Pi (_, x, a, c) ->
      let v = fresh ctx in
      conv (bind x a ctx) (Value.apply_closure c v) (Value.apply v1 v)
        (Value.apply v2 v)
  (* at a sort, the values are types: compare strictly *)
  | Value.Sort _ -> conv_ty ctx v1 v2
  | Value.VInd (name, _, params) -> (
      let spec = lookup_ind ctx name in
      if Inductive.is_record spec then
        (* record η: equal iff every field projection is convertible (each at
           its dependent field type); the 0-field case makes any two equal *)
        let nfields = List.length (List.nth spec.Inductive.ctors 0).fields in
        let rec go i =
          i >= nfields
          || conv ctx
               (field_type spec params v1 i)
               (Value.vproj i v1) (Value.vproj i v2)
             && go (i + 1)
        in
        go 0
      else
        (* a positive inductive, like Nat: same constructor with convertible
           arguments (compared type-directedly along the constructor's type), or
           two stuck values *)
          match (v1, v2) with
        | Value.VCtor (h1, args1), Value.VCtor (h2, args2) ->
            String.equal h1.cname h2.cname
            && conv_spine ctx (ctor_type_val ctx h1) args1 args2
        | Value.Neutral n1, Value.Neutral n2 ->
            Option.is_some (conv_neutral ctx n1 n2)
        | _ -> false)
  (* at a stuck type there are no intro forms: both sides are neutral *)
  | _ -> (
      match (v1, v2) with
      | Value.Neutral n1, Value.Neutral n2 ->
          Option.is_some (conv_neutral ctx n1 n2)
      | _ -> false)

and conv_ty ctx (t1 : Value.t) (t2 : Value.t) =
  match (t1, t2) with
  (* sorts are compared by level equality — there is no cumulativity (Lean's
     model): a smaller universe is not a subtype of a larger one *)
  | Value.Sort i, Value.Sort j -> Level.equal i j
  (* pi: invariant in both domain and codomain; the binder's visibility ([icit])
     is metadata the kernel ignores, so it is not compared *)
  | Value.Pi (_, x, a1, c1), Value.Pi (_, _, a2, c2) ->
      conv_ty ctx a1 a2
      &&
      let v = fresh ctx in
      conv_ty (bind x a1 ctx) (Value.apply_closure c1 v)
        (Value.apply_closure c2 v)
  (* an inductive type former is invariant in its parameters and indices: same
     name, and arguments convertible along the combined (instantiated) telescope
     (the index types may mention the parameters, which [conv_params]
     threads) *)
  | Value.VInd (n1, ls1, ps1), Value.VInd (n2, ls2, ps2) ->
      let spec = lookup_ind ctx n1 in
      String.equal n1 n2
      && List.length ls1 = List.length ls2
      && List.for_all2 Level.equal ls1 ls2
      && conv_params ctx []
           (spec.Inductive.params @ spec.Inductive.indices)
           ps1 ps2
  | Value.Neutral n1, Value.Neutral n2 ->
      Option.is_some (conv_neutral ctx n1 n2)
  | _ -> false

(* compares two parameter spines along a parameter telescope, instantiating each
   binder's type with the earlier parameter values *)
and conv_params ctx env params ps1 ps2 =
  match (params, ps1, ps2) with
  | [], [], [] -> true
  | (_, pty) :: ps, v1 :: vs1, v2 :: vs2 ->
      conv ctx (Value.eval env pty) v1 v2
      && conv_params ctx (v1 :: env) ps vs1 vs2
  | _ -> false

(* compares two argument spines along a function type, instantiating the
   codomain with each argument as it is consumed *)
and conv_spine ctx ty args1 args2 =
  match (args1, args2) with
  | [], [] -> true
  | a1 :: r1, a2 :: r2 -> (
      match ty with
      | Value.Pi (_, _, dom, c) ->
          conv ctx dom a1 a2 && conv_spine ctx (Value.apply_closure c a1) r1 r2
      | _ -> false)
  | _ -> false

(* spine equality, returning the head's instantiated type so that arguments are
   compared type-directedly — in particular, proof arguments are ignored *)
and conv_neutral ctx n1 n2 : Value.t option =
  match (n1, n2) with
  | Value.Var k1, Value.Var k2 ->
      if k1 = k2 then
        Some (List.nth ctx.types (ctx.lvl - k1 - 1))
      else
        None
  | Value.App (m1, a1), Value.App (m2, a2) -> (
      match conv_neutral ctx m1 m2 with
      | Some (Value.Pi (_, _, dom, c)) ->
          if conv ctx dom a1 a2 then
            Some (Value.apply_closure c a1)
          else
            None
      | _ -> None)
  | Value.Proj (i1, m1), Value.Proj (i2, m2) when i1 = i2 -> (
      match conv_neutral ctx m1 m2 with
      | Some (Value.VInd (name, _, params)) ->
          Some (field_type (lookup_ind ctx name) params (Value.Neutral m1) i1)
      | _ -> None)
  (* stuck inductive recursion: the recorded pre-major spine is [params @ motive
     :: minors @ indices], each part compared along the inductive's
     telescopes *)
  | Value.Rec (h, pre1, n1), Value.Rec (h2, pre2, n2)
    when String.equal h.Type.rind h2.Type.rind ->
      let spec = lookup_ind ctx h.Type.rind in
      let rind = h.Type.rind in
      let levels = h.Type.rlevels in
      let m = h.Type.nparams and nmin = List.length h.Type.recs in
      let params1 = List.take m pre1 and params2 = List.take m pre2 in
      let motive1 = List.nth pre1 m and motive2 = List.nth pre2 m in
      let minors1 = List.take nmin (List.drop (m + 1) pre1)
      and minors2 = List.take nmin (List.drop (m + 1) pre2) in
      let indices1 = List.drop (m + 1 + nmin) pre1
      and indices2 = List.drop (m + 1 + nmin) pre2 in
      let ind_ty =
        List.fold_left Value.apply
          (Value.VInd (rind, levels, []))
          (params1 @ indices1)
      in
      (* the major is compared *at the inductive type*, not structurally: a Prop
         scrutinee is a proof, so by irrelevance two stuck recursions on
         different proofs are equal (this is what subsumes [absurd]) *)
      let majors_ok = conv ctx ind_ty (Value.Neutral n1) (Value.Neutral n2) in
      (* the motives compared extensionally over the index telescope and
         target *)
      let motives_ok =
        let rec go ctx env idxs_rev = function
          | (x, ity) :: rest ->
              let dom = Value.eval env (Type.subst_levels levels ity) in
              let v = fresh ctx in
              go (bind x dom ctx) (v :: env) (v :: idxs_rev) rest
          | [] ->
              let idxs = List.rev idxs_rev in
              let ity =
                List.fold_left Value.apply
                  (Value.VInd (rind, levels, []))
                  (params1 @ idxs)
              in
              let ctx' = bind "x" ity ctx in
              let tgt = fresh ctx in
              conv_ty ctx'
                (List.fold_left Value.apply motive1 (idxs @ [ tgt ]))
                (List.fold_left Value.apply motive2 (idxs @ [ tgt ]))
        in
        go ctx (List.rev params1) [] spec.Inductive.indices
      in
      let minors_ok =
        List.for_all2
          (fun (i, mn1) mn2 ->
            conv ctx (minor_type ~levels ctx spec params1 motive1 i) mn1 mn2)
          (List.mapi (fun i mn -> (i, mn)) minors1)
          minors2
      in
      if
        conv_params ctx [] spec.Inductive.params params1 params2
        && conv_params ctx (List.rev params1) spec.Inductive.indices indices1
             indices2
        && majors_ok
        && motives_ok
        && minors_ok
      then
        Some
          (List.fold_left Value.apply motive1 (indices1 @ [ Value.Neutral n1 ]))
      else
        None
  | _ -> None

(* subsumption is now plain type conversion — no cumulativity *)
let sub = conv_ty

(* peel an application into its head and its argument list (left-to-right) *)
let spine t =
  let rec go acc = function
    | Type.App (f, a) -> go (a :: acc) f
    | h -> (h, acc)
  in
  go [] t

(* binds a parameter telescope as fresh neutrals; returns the extended context
   and the env (newest-first) of parameter values for evaluating types that
   mention earlier parameters *)
let bind_params ctx params =
  List.fold_left
    (fun (ctx, env) (x, pty) ->
      let ctx' = bind x (Value.eval env pty) ctx in
      (ctx', fresh ctx :: env))
    (ctx, []) params

(* whether [spec] is a subsingleton — at most one constructor, all of whose
   fields are proofs (in Prop). Such a Prop inductive may eliminate into any
   sort (subsingleton elimination, like Empty and Eq); any other Prop inductive
   is restricted to Prop-valued elimination. *)
let subsingleton ctx spec =
  match spec.Inductive.ctors with
  | [] -> true
  | [ c ] ->
      let ctx0, env0 = bind_params ctx spec.Inductive.params in
      let rec fields_are_proofs ctx env = function
        | [] -> true
        | (a : Inductive.arg) :: rest ->
            Level.equal (sort_of ctx (Value.eval env a.aty)) Level.zero
            && fields_are_proofs
                 (bind a.aname (Value.eval env a.aty) ctx)
                 (fresh ctx :: env) rest
      in
      fields_are_proofs ctx0 env0 c.fields
  | _ -> false

(* the rule markers below refer to the typing rules in check.mli's header *)
let rec infer ctx t =
  match t with
  | Type.Var i -> List.nth ctx.types i (* (Var) *)
  (* a polymorphic def reference: its type is stored level-abstracted at the
     slot, so instantiate it at the use-site levels *)
  | Type.Def (i, ls) -> (
      match List.nth ctx.types i with
      | Value.VPoly p -> Value.eval p.denv (Type.subst_levels ls p.body)
      | v -> v)
  (* metavariables are an elaboration-only node; the elaborator zonks them away,
     so a meta reaching the kernel is a bug, not a typeable term *)
  | Type.Meta _ ->
      Error.type_error
        [ Error.txt "internal error: a metavariable reached the kernel" ]
  | Type.Sort i -> Value.Sort (Level.succ i) (* (Sort) *)
  (* (Pi) — visibility does not affect the formed sort *)
  | Type.Pi (_, x, a, b) ->
      let i = infer_univ ctx a in
      let j = infer_univ (bind x (Value.eval ctx.env a) ctx) b in
      Value.Sort (imax i j)
  (* (Lam) — the inferred Π keeps the lambda's visibility *)
  | Type.Lam (vis, x, a, b) ->
      let _ = infer_univ ctx a in
      let va = Value.eval ctx.env a in
      let vb = infer (bind x va ctx) b in
      (* [vb] is a value one binder deep; quote it back to syntax to form the
         codomain closure *)
      Value.Pi
        (vis, x, va, { env = ctx.env; body = Value.quote (ctx.lvl + 1) vb })
  (* (App) — but a recursor is motive-polymorphic, so it has no type as a
     constant: a fully-applied recursor spine gets a bespoke rule (like NatRec),
     detected by peeling the application head *)
  | Type.App (f, a) -> (
      match spine t with
      | Type.Rec rh, args -> infer_rec ctx rh args
      | _ -> (
          match infer ctx f with
          | Value.Pi (_, _, dom, c) ->
              check ctx a dom;
              Value.apply_closure c (Value.eval ctx.env a)
          | ty ->
              Error.type_error
                [ Error.txt "expected a function, but "
                ; tm ctx f
                ; Error.txt " has type "
                ; vl ctx ty
                ]))
  (* (Proj): the i-th field of a record, at its dependent field type *)
  | Type.Proj (i, e) -> (
      match infer ctx e with
      | Value.VInd (name, _, params) ->
          let spec = lookup_ind ctx name in
          if not (Inductive.is_record spec) then
            Error.type_error
              [ Error.txtf "%s is not a record, so it has no field projections"
                  name
              ];
          let nfields = List.length (List.nth spec.Inductive.ctors 0).fields in
          if i >= nfields then
            Error.type_error [ Error.txtf "%s has no field .%d" name (i + 1) ];
          field_type spec params (Value.eval ctx.env e) i
      | ty ->
          Error.type_error
            [ Error.txt "expected a record, but "
            ; tm ctx e
            ; Error.txt " has type "
            ; vl ctx ty
            ])
  (* an inductive type former and its constructors have fixed (non-polymorphic)
     types derived from the declaration; they ride the normal (App) machinery *)
  | Type.Ind (name, ls) ->
      Value.eval []
        (Type.subst_levels ls (Inductive.former_type (lookup_ind ctx name)))
  | Type.Ctor h ->
      Value.eval []
        (Type.subst_levels h.clevels
           (Inductive.ctor_type (lookup_ind ctx h.ind) h.cindex))
  (* a bare recursor is motive-polymorphic; only a saturated application (caught
     in (App)) can be typed *)
  | Type.Rec _ ->
      Error.type_error
        [ Error.txt
            "cannot infer the type of a bare recursor; apply it to its \
             parameters, motive, minor premises and target"
        ]

(* infers and requires a sort: used where the rules demand "a type" *)
and infer_univ ctx t =
  match infer ctx t with
  | Value.Sort i -> i
  | ty ->
      Error.type_error
        [ Error.txt "expected a type, but "
        ; tm ctx t
        ; Error.txt " has type "
        ; vl ctx ty
        ]

(* checks a spine [tms] against a telescope, each binder's type instantiated by
   the earlier values; returns the values. [env0] seeds the env (e.g. the
   parameter values, reversed, when checking the index telescope that follows
   them). With [env0 = []] this is the parameter check. *)
and check_telescope ctx env0 tele tms =
  let rec go env tele tms =
    match (tele, tms) with
    | [], [] -> []
    | (_, ty) :: ts, tm :: rest ->
        check ctx tm (Value.eval env ty);
        let v = Value.eval ctx.env tm in
        v :: go (v :: env) ts rest
    | _ ->
        Error.type_error
          [ Error.txt "wrong number of arguments for the inductive's telescope"
          ]
  in
  go env0 tele tms

(* validates a recursor motive [P : (indices) -> Ind params indices -> Sort j]
   against the inductive's index telescope (instantiated by [pvals]), returning
   [j]. Walks the index binders, then the target binder. *)
and check_motive ?(levels = []) ctx spec pvals mty =
  let rind = spec.Inductive.name in
  let rec walk ctx mty env idxs_rev = function
    | (x, ity) :: rest -> (
        match mty with
        | Value.Pi (_, _, dom, c) ->
            let expected = Value.eval env (Type.subst_levels levels ity) in
            if not (conv_ty ctx dom expected) then
              Error.type_error
                [ Error.txt "the motive's index argument has type "
                ; vl ctx dom
                ; Error.txt " but "
                ; vl ctx expected
                ; Error.txt " was expected"
                ];
            let v = fresh ctx in
            walk (bind x dom ctx) (Value.apply_closure c v) (v :: env)
              (v :: idxs_rev) rest
        | _ ->
            Error.type_error
              [ Error.txt "the motive is missing an index argument" ])
    | [] -> (
        match mty with
        | Value.Pi (_, _, dom, c) -> (
            let expected =
              List.fold_left Value.apply
                (Value.VInd (rind, levels, []))
                (pvals @ List.rev idxs_rev)
            in
            if not (conv_ty ctx dom expected) then
              Error.type_error
                [ Error.txt "the motive's target "
                ; vl ctx dom
                ; Error.txt " does not match "
                ; vl ctx expected
                ];
            match Value.apply_closure c (fresh ctx) with
            | Value.Sort j -> j
            | cod ->
                Error.type_error
                  [ Error.txt "the motive must land in a sort, not "
                  ; vl (bind "x" expected ctx) cod
                  ])
        | _ ->
            Error.type_error
              [ Error.txt "the motive must take the target of the elimination" ]
        )
  in
  walk ctx mty (List.rev pvals) [] spec.Inductive.indices

(* (Rec): the generic recursor. The motive is [P : (indices) -> Ind params
   indices -> Sort j]; each constructor contributes a minor premise (see
   {!minor_type}); applied to index arguments [i] and a major [t : Ind params i]
   the result is [P i t]. Prop inductives that are not subsingletons are
   restricted to Prop-valued elimination (the large-elimination restriction). *)
and infer_rec ctx rh args =
  let spec = lookup_ind ctx rh.Type.rind in
  let m = rh.Type.nparams in
  let nidx = rh.Type.nindices in
  let nctors = List.length rh.Type.recs in
  let expected = m + 1 + nctors + nidx + 1 in
  if List.length args <> expected then
    Error.type_error
      [ Error.txtf "%s.rec expects %d arguments but got %d" rh.Type.rind
          expected (List.length args)
      ];
  let param_tms = List.take m args in
  let motive_tm = List.nth args m in
  let minor_tms = List.take nctors (List.drop (m + 1) args) in
  let index_tms = List.take nidx (List.drop (m + 1 + nctors) args) in
  let major_tm = List.nth args (m + 1 + nctors + nidx) in
  (* the inductive's level arguments (empty if monomorphic); the spec's
     parameter/index/field types carry its level variables, so instantiate
     them *)
  let levels = rh.Type.rlevels in
  let inst_tele = List.map (fun (x, t) -> (x, Type.subst_levels levels t)) in
  let pvals =
    check_telescope ctx [] (inst_tele spec.Inductive.params) param_tms
  in
  (* the motive P : (indices) -> Ind params indices -> Sort j *)
  let pmot = Value.eval ctx.env motive_tm in
  let j = check_motive ~levels ctx spec pvals (infer ctx motive_tm) in
  if
    Level.equal spec.Inductive.sort Level.zero
    && (not (Level.equal j Level.zero))
    && not (subsingleton ctx spec)
  then
    Error.type_error
      [ Error.txtf "cannot eliminate the proposition %s into " rh.Type.rind
      ; tm ctx (Type.Sort j)
      ; Error.txt
          ": only a subsingleton (at most one constructor, all fields proofs) \
           may eliminate large"
      ];
  (* each minor premise against its derived type *)
  List.iteri
    (fun i mn -> check ctx mn (minor_type ~levels ctx spec pvals pmot i))
    minor_tms;
  (* the index arguments (against the index telescope, instantiated by the
     parameters), then the major at [Ind params indices] *)
  let ivals =
    check_telescope ctx (List.rev pvals)
      (inst_tele spec.Inductive.indices)
      index_tms
  in
  let ind_ty =
    List.fold_left Value.apply
      (Value.VInd (rh.Type.rind, levels, []))
      (pvals @ ivals)
  in
  check ctx major_tm ind_ty;
  (* result: P indices major *)
  List.fold_left Value.apply pmot (ivals @ [ Value.eval ctx.env major_tm ])

and check ctx t expected =
  match (t, expected) with
  (* a lambda against a Pi: the annotation must match the domain, then the body
     is checked against the codomain at a fresh variable. Visibility is the
     kernel-ignored [icit] metadata, so a lambda matches a Π of either kind. *)
  | Type.Lam (_, x, a, b), Value.Pi (_, _, dom, c) ->
      let _ = infer_univ ctx a in
      let va = Value.eval ctx.env a in
      if not (conv_ty ctx va dom) then
        Error.type_error
          [ Error.txt "the annotation "
          ; vl ctx va
          ; Error.txt " does not match the expected domain "
          ; vl ctx dom
          ];
      check (bind x va ctx) b
        (Value.apply_closure c (Value.Neutral (Value.Var ctx.lvl)))
  (* subsumption: infer and compare up to definitional equality (βδη plus proof
     irrelevance); no cumulativity, so this is plain type conversion *)
  | _ ->
      let ty = infer ctx t in
      if not (sub ctx ty expected) then
        Error.type_error
          [ Error.txt "this term has type "
          ; vl ctx ty
          ; Error.txt " but "
          ; vl ctx expected
          ; Error.txt " was expected"
          ]

(* the inductive applied to its parameters then the given index terms; [depth]
   is the binder count at which the parameter variables are read (see
   {!Inductive.apply}) *)
let applied_to_indices spec depth idxs =
  List.fold_left
    (fun acc i -> Type.App (acc, i))
    (Inductive.apply spec depth)
    idxs

(* Validates an inductive declaration: kind-checks the parameter and index
   telescopes, then each constructor's field types and result indices in
   context. Enforces strict positivity — the inductive may appear only as a
   direct recursive field [Ind params idxs] (never elsewhere, and never inside
   the [idxs] of such a field) — and predicativity (each field's sort fits the
   inductive's, unless it is a Prop, which is impredicative). The inductive is
   registered before checking constructors so their recursive occurrences
   resolve. *)
let check_inductive ctx spec =
  let name = spec.Inductive.name in
  let ctx = add_ind spec ctx in
  (* kind-check the parameter telescope *)
  let ctx_p =
    List.fold_left
      (fun ctx (x, pty) ->
        let _ = infer_univ ctx pty in
        bind x (Value.eval ctx.env pty) ctx)
      ctx spec.Inductive.params
  in
  (* kind-check the index telescope, under the parameters *)
  ignore
    (List.fold_left
       (fun ctx (x, ity) ->
         let _ = infer_univ ctx ity in
         bind x (Value.eval ctx.env ity) ctx)
       ctx_p spec.Inductive.indices);
  let m = Inductive.nparams spec in
  List.iter
    (fun (c : Inductive.ctor) ->
      let ctx_after, nf =
        List.fold_left
          (fun (ctx_cur, j) (a : Inductive.arg) ->
            let s = infer_univ ctx_cur a.aty in
            (match a.recursive with
            | Some idxs ->
                (* a recursive field is the inductive applied to the (fixed)
                   parameters and its own index instances; the inductive must
                   not occur inside those indices (strict positivity) *)
                let expected = applied_to_indices spec (m + j) idxs in
                if a.aty <> expected then
                  Error.type_error
                    [ Error.txtf
                        "constructor %s: a recursive field must be the \
                         inductive at its parameters and indices, "
                        c.cname
                    ; tm ctx_cur expected
                    ; Error.txt ", not "
                    ; tm ctx_cur a.aty
                    ];
                List.iter
                  (fun i ->
                    if Inductive.occurs name i then
                      Error.type_error
                        [ Error.txtf
                            "constructor %s: %s may not occur in a recursive \
                             field's indices (strict positivity)"
                            c.cname name
                        ])
                  idxs
            | None ->
                if Inductive.occurs name a.aty then
                  Error.type_error
                    [ Error.txtf
                        "constructor %s: %s may occur only as a direct \
                         recursive field, not inside "
                        c.cname name
                    ; tm ctx_cur a.aty
                    ; Error.txt " (strict positivity)"
                    ]);
            if
              (not (Level.equal spec.Inductive.sort Level.zero))
              && not (Level.leq s spec.Inductive.sort)
            then
              Error.type_error
                [ Error.txtf "constructor %s: a field of sort " c.cname
                ; tm ctx_cur (Type.Sort s)
                ; Error.txt " does not fit the inductive's sort "
                ; tm ctx_cur (Type.Sort spec.Inductive.sort)
                ];
            (bind a.aname (Value.eval ctx_cur.env a.aty) ctx_cur, j + 1))
          (ctx_p, 0) c.fields
      in
      (* the constructor's result [Ind params result_indices] must be well-typed
         (so the index instances match the index telescope) *)
      let _ =
        infer_univ ctx_after (applied_to_indices spec (m + nf) c.result_indices)
      in
      ())
    spec.Inductive.ctors
