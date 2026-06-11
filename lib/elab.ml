(* Bidirectional elaboration. [go ctx mode s] produces a core term for the
   surface term [s]; [mode] is the elaboration direction — [Infer] for a
   synthesizing position, [Check ty] when [s] is expected to have type [ty]. The
   expected type drives the inference the surface syntax leaves implicit, e.g.:
   constructor applications may drop the leading parameters (recovered from the
   expected inductive type, or solved as metavariables from the fields); a
   surface hole [_] becomes a metavariable, solved by unifying argument types
   during application (see {!Meta}); implicit binders [{x : A}] are inserted as
   fresh metavariables before an explicit argument and to coerce a
   fully-implicit term against a non-implicit goal ([@f] suppresses both); [x =
   y] infers the equality's type from the left side; [e.field] is a named
   projection; and a hole motive on a (non-indexed) recursor is synthesized by
   abstracting the scrutinee out of the expected goal. (The full account is in
   [elab.mli].)

   The elaborator is untrusted: whatever it produces is re-checked by {!Check}
   (on meta-free, zonked core), so a bug here is a usability bug, not a
   soundness one. It reuses the kernel's NbE ({!Value}) for the types it needs,
   plus its own meta-aware synthesis ([elab_infer]) for terms still carrying
   metavariables, which the kernel no longer knows. It is the sole surface →
   core pass — every surface form, down to the leaves ([()], numerals), is
   handled here. *)

type mode =
  | Infer
  | Check of Value.t

(* the surface application [s] peeled into its head and argument list, outermost
   function first *)
let peel s =
  let rec go acc (s : Ast.t) =
    match s.desc with
    | Ast.App (f, a) -> go (a :: acc) f
    | _ -> (s, acc)
  in
  go [] s

(* what the head of an application resolves to, for the spine rules below *)
type head =
  | Rec of Type.rec_head
  | Ctor of Inductive.spec * Type.ctor_head
  | Other

let classify_head sg (s : Ast.t) =
  match s.desc with
  | Ast.Field ({ desc = Ast.Var tname; _ }, field) -> (
      match Signature.find sg tname with
      | None -> Other
      | Some spec -> (
          if String.equal field "rec" then
            Rec (Inductive.rec_head spec)
          else
            match
              List.find_index
                (fun (c : Inductive.ctor) -> String.equal c.cname field)
                spec.Inductive.ctors
            with
            | Some i -> Ctor (spec, Inductive.ctor_head spec i)
            | None -> Other))
  | _ -> Other

let imax = Level.imax

(* if context slot [i] holds a universe-polymorphic def, its level-parameter
   count together with the pieces ([denv], type-[body] core) needed to build its
   type at any level instantiation [ls] (as [eval denv (subst_levels ls body)])
   — else [None] *)
let poly_def_info (ctx : Check.ctx) i =
  match List.nth_opt ctx.Check.types i with
  | Some (Value.VPoly { nlevels; denv; body }) -> Some (nlevels, denv, body)
  | _ -> None

(* peel a core application into its head and argument list (outermost first) *)
let core_spine t =
  let rec go acc = function
    | Type.App (f, a) -> go (a :: acc) f
    | h -> (h, acc)
  in
  go [] t

(* shift every free de Bruijn index of [t] (those [>= c]) up by [d] *)
let rec lift d c (t : Type.t) : Type.t =
  match t with
  | Type.Var i ->
      Type.Var
        (if i >= c then
           i + d
         else
           i)
  | Type.Def (i, ls) ->
      Type.Def
        ( (if i >= c then
             i + d
           else
             i)
        , ls )
  | Type.Pi (ic, x, a, b) -> Type.Pi (ic, x, lift d c a, lift d (c + 1) b)
  | Type.Lam (ic, x, a, b) -> Type.Lam (ic, x, lift d c a, lift d (c + 1) b)
  | Type.Let (x, a, v, b) ->
      Type.Let (x, lift d c a, lift d c v, lift d (c + 1) b)
  | Type.App (f, a) -> Type.App (lift d c f, lift d c a)
  | Type.Proj (i, e) -> Type.Proj (i, lift d c e)
  | Type.Sort _
  | Type.Ind _
  | Type.Ctor _
  | Type.Rec _
  | Type.Meta _ ->
      t

(* [abstract needle t] is the body of [λ _ ⇒ t] with every subterm equal to
   [needle] replaced by the fresh outermost binder (de Bruijn 0); [t]'s other
   free indices shift up by one to make room. [needle] and [t] are core terms in
   the same context, in normal form (so the match is up to βδη). This is the
   motive-synthesis primitive: it generalizes a goal over a chosen subterm. *)
let abstract needle t =
  let rec go k t =
    (* at depth [k] within [t], the new binder is index [k] and [needle]'s free
       indices have shifted up by [k] *)
    if t = lift k 0 needle then
      Type.Var k
    else
      match t with
      | Type.Var i ->
          Type.Var
            (if i >= k then
               i + 1
             else
               i)
      | Type.Def (i, ls) ->
          Type.Def
            ( (if i >= k then
                 i + 1
               else
                 i)
            , ls )
      | Type.Pi (ic, x, a, b) -> Type.Pi (ic, x, go k a, go (k + 1) b)
      | Type.Lam (ic, x, a, b) -> Type.Lam (ic, x, go k a, go (k + 1) b)
      | Type.Let (x, a, v, b) -> Type.Let (x, go k a, go k v, go (k + 1) b)
      | Type.App (f, a) -> Type.App (go k f, go k a)
      | Type.Proj (i, e) -> Type.Proj (i, go k e)
      | Type.Sort _
      | Type.Ind _
      | Type.Ctor _
      | Type.Rec _
      | Type.Meta _ ->
          t
  in
  go 0 t

(* resolve a surface level against the level parameters [lvls] in scope (their
   position is the level variable's de Bruijn index) *)
let rec resolve_level lvls = function
  | Ast.LNat n -> Level.of_int n
  | Ast.LVar x -> (
      match List.find_index (String.equal x) lvls with
      | Some i -> Level.Var i
      | None -> Error.type_error [ Error.txtf "unknown universe variable %s" x ]
      )
  | Ast.LMax (a, b) -> Level.max (resolve_level lvls a) (resolve_level lvls b)
  | Ast.LIMax (a, b) -> Level.imax (resolve_level lvls a) (resolve_level lvls b)

let elaborate ?(levels = []) notation (ctx0 : Check.ctx) mode0 s0 =
  let sg = ctx0.Check.signature in
  let fresh (ctx : Check.ctx) = Value.Neutral (Value.Var ctx.Check.lvl) in
  (* the metacontext for this elaboration: a functional value threaded through a
     local ref, so unification and hole creation can update it without any
     global state — the metacontext itself stays pure *)
  let ms = ref Meta.empty in
  (* a fresh metavariable of (use-site) type [ty], born at the current level;
     non-contextual (no spine), so a solution may mention variables already in
     scope at its birth, which {!Meta.unify}'s scope check enforces *)
  let fresh_meta_core (ctx : Check.ctx) (ty : Value.t) : Type.t =
    let ms', id = Meta.fresh !ms ~blvl:ctx.Check.lvl ty in
    ms := ms';
    Type.Meta id
  in
  (* the elaborator's own meta-aware type synthesis: it must not lean on the
     kernel's [Check.infer] for a term containing metavariables (the kernel no
     longer knows them). A term-meta-free subterm is still handed to
     [Check.infer] — but a solved {e level} meta may still sit unforced in its
     sorts/head levels (the kernel would treat it as a rigid atom and
     mis-check), so resolve those first. Only the term-meta-carrying spine is
     walked here, forcing solutions via [Meta]. *)
  let rec elab_infer ctx (t : Type.t) : Value.t =
    if not (Type.has_meta t) then
      Check.infer ctx
        (if Type.has_level_meta t then
           Meta.zonk !ms ctx.Check.lvl t
         else
           t)
    else
      match t with
      | Type.Meta i -> Meta.typ !ms i
      | Type.App (f, a) -> (
          match core_spine t with
          (* a saturated recursor application has type [P major] *)
          | Type.Rec rh, args ->
              Value.apply
                (Value.eval ctx.Check.env (List.nth args rh.Type.nparams))
                (Value.eval ctx.Check.env
                   (List.nth args (List.length args - 1)))
          | _ -> (
              match Meta.force !ms (elab_infer ctx f) with
              | Value.Pi (_, _, _, c) ->
                  Value.apply_closure c (Value.eval ctx.Check.env a)
              | _ -> assert false))
      | Type.Lam (vis, x, a, b) ->
          let va = Value.eval ctx.Check.env a in
          let vb = elab_infer (Check.bind x va ctx) b in
          Value.Pi
            ( vis
            , x
            , va
            , { Value.env = ctx.Check.env
              ; body = Value.quote (ctx.Check.lvl + 1) vb
              } )
      | Type.Pi (_, x, a, b) ->
          let i = sort_of_ty ctx a in
          let j =
            sort_of_ty (Check.bind x (Value.eval ctx.Check.env a) ctx) b
          in
          Value.Sort (imax i j)
      | Type.Proj (i, e) -> (
          match Meta.force !ms (elab_infer ctx e) with
          | Value.VInd (name, _, params) ->
              Check.field_type
                (Check.lookup_ind ctx name)
                params
                (Value.eval ctx.Check.env e)
                i
          | _ -> assert false)
      | _ -> Check.infer ctx t
  and sort_of_ty ctx a =
    match Meta.force !ms (elab_infer ctx a) with
    | Value.Sort i -> i
    | _ -> Level.zero
  in
  (* the inductive registered for the [sigma] role, that [Σ]/[×] desugar to *)
  let sigma_form () =
    match notation.Notation.sigma with
    | Some mk -> mk.Type.ind
    | None ->
        Error.type_error
          [ Error.txt "Σ/× requires the sigma notation to be registered" ]
  in
  (* the inductive registered for the [eq] role, that the infix [x = y] desugars
     to (its applied former; [rfl] is now an ordinary prelude def over
     [Eq.refl], and the recursor [Eq.rec] an ordinary qualified name) *)
  let eq_spec () =
    match notation.Notation.eq with
    | Some name -> (
        match Signature.find sg name with
        | Some spec -> spec
        | None ->
            Error.type_error
              [ Error.txt "the eq notation names an unknown inductive" ])
    | None ->
        Error.type_error
          [ Error.txt "= requires the eq notation to be registered" ]
  in
  (* expected-type-driven implicit insertion. [core] has (use-site) type [ty];
     in checking position, if [ty] begins with implicit binders [{a : A} -> …]
     and the goal does *not* itself expect an implicit binder, insert a fresh
     metavariable for each leading implicit and unify the instantiated type
     against the goal (which solves them). This lets a fully-implicit term be
     used bare — [rfl : {A}{x} -> x = x] checked against [a = a] — where the
     spine rule (which only inserts before an explicit argument) cannot. The
     unify is gated on having inserted at least one meta, so a meta-free term is
     left untouched for the kernel's own conversion. *)
  let coerce (ctx : Check.ctx) mode core ty : Type.t =
    match mode with
    | Infer -> core
    | Check g ->
        let goal_implicit =
          match Meta.force !ms g with
          | Value.Pi (Type.Implicit, _, _, _) -> true
          | _ -> false
        in
        if goal_implicit then
          core
        else
          let rec walk core ty inserted =
            match Meta.force !ms ty with
            | Value.Pi (Type.Implicit, _, dom, c) ->
                let m = fresh_meta_core ctx dom in
                walk
                  (Type.App (core, m))
                  (Value.apply_closure c (Value.eval ctx.Check.env m))
                  true
            | _ ->
                (* unify the result type against the goal when we inserted an
                   implicit (to solve it), or when either side still carries an
                   unsolved level metavariable — solving it from the goal (an
                   explicit argument of a polymorphic def checked against a
                   [Sort ?u] domain, or a saturated head like [cong f p] whose
                   codomain universe is fixed only by the goal's level).
                   Otherwise leave conversion to the kernel. *)
                let has_lmeta v =
                  Type.has_level_meta
                    (Value.quote ctx.Check.lvl (Meta.force !ms v))
                in
                if inserted || has_lmeta ty || has_lmeta g then
                  ms := Meta.unify !ms ctx ty g;
                core
          in
          walk core ty false
  in
  (* coerce a head leaf (a bare variable or projection) in checking position:
     synthesize its type and insert leading implicits as above. A no-op in
     inference position. *)
  let coerce_leaf ctx mode core : Type.t =
    match mode with
    | Infer -> core
    | Check _ -> coerce ctx mode core (Meta.force !ms (elab_infer ctx core))
  in
  let rec go (ctx : Check.ctx) mode (s : Ast.t) : Type.t =
    match s.desc with
    (* a bare name is a local binder (de Bruijn) first, otherwise a global
       inductive former *)
    | Ast.Var x ->
        let core =
          match List.find_index (String.equal x) ctx.Check.names with
          | Some i -> (
              match poly_def_info ctx i with
              (* a polymorphic def used bare. Checking position: level
                 metavariables, solved by coercing its type against the goal
                 ([rfl] against [a = a]) — also what stops it from capturing the
                 enclosing def's level parameters. Inference position: no goal,
                 so the identity levels [Var 0 … Var (k-1)], which print as its
                 universe parameters. An application re-solves them
                 ([Other]). *)
              | Some (nlevels, _, _) ->
                  let ls =
                    match mode with
                    | Check _ ->
                        List.init nlevels (fun _ ->
                            let ms', id = Meta.fresh_level !ms in
                            ms := ms';
                            Level.LMeta id)
                    | Infer -> List.init nlevels (fun j -> Level.Var j)
                  in
                  Type.Def (i, ls)
              | None -> Type.Var i)
          | None -> (
              match Signature.find sg x with
              | Some spec -> Type.Ind (spec.Inductive.name, [])
              | None -> raise (Ast.Unbound_variable (s.loc, x)))
        in
        coerce_leaf ctx mode core
    | Ast.Field (e, field) -> (
        (* qualified access on an inductive *name* [T] (not shadowed by a
           local): [T.rec] is its recursor, [T.c] one of its constructors.
           Otherwise [e.f] is a named field projection on the record value
           [e]. *)
        let qualified =
          match e.Ast.desc with
          | Ast.Var t when not (List.mem t ctx.Check.names) ->
              Signature.find sg t
          | _ -> None
        in
        match qualified with
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
              | None ->
                  raise
                    (Ast.Unbound_variable
                       (s.loc, spec.Inductive.name ^ "." ^ field)))
        | None -> (
            (* a named field projection: [field] is one of [e]'s single
               constructor's field names, resolving to the positional [Proj] *)
            let e' = go ctx Infer e in
            match Meta.force !ms (elab_infer ctx e') with
            | Value.VInd (name, _, _) -> (
                let spec = Check.lookup_ind ctx name in
                if not (Inductive.is_record spec) then
                  Error.type_error
                    [ Error.txtf
                        "%s is not a record (single-constructor) type, so it \
                         has no named field .%s"
                        name field
                    ];
                let ctor = List.hd spec.Inductive.ctors in
                match
                  List.find_index
                    (fun (a : Inductive.arg) ->
                      String.equal a.Inductive.aname field)
                    ctor.Inductive.fields
                with
                | Some i -> coerce_leaf ctx mode (Type.Proj (i, e'))
                | None ->
                    Error.type_error
                      [ Error.txtf "%s has no field .%s" name field ])
            | _ ->
                Error.type_error
                  [ Error.txtf "the projection .%s expects a record value" field
                  ]))
    | Ast.Sort l -> Type.Sort (resolve_level levels l)
    | Ast.Pi (i, x, a, b) ->
        let a' = go ctx Infer a in
        let b' = go (Check.bind x (Value.eval ctx.Check.env a') ctx) Infer b in
        Type.Pi (i, x, a', b')
    | Ast.Arrow (a, b) ->
        let a' = go ctx Infer a in
        let b' = go (Check.bind "" (Value.eval ctx.Check.env a') ctx) Infer b in
        Type.Pi (Type.Explicit, "", a', b')
    | Ast.Lam (i, x, a, b) ->
        let a' = go ctx Infer a in
        let va = Value.eval ctx.Check.env a' in
        (* in checking position, the expected codomain flows into the body so a
           constructor there can drop its parameters *)
        let body_mode =
          match mode with
          | Check e -> (
              match Meta.force !ms e with
              | Value.Pi (_, _, _, c) ->
                  Check (Value.apply_closure c (fresh ctx))
              | _ -> Infer)
          | Infer -> Infer
        in
        Type.Lam (i, x, a', go (Check.bind x va ctx) body_mode b)
    | Ast.App _
    | Ast.At _ ->
        elab_app ctx mode s
    | Ast.Match (scrut, arms) -> elab_match ctx mode scrut arms
    (* the generic record projections; handled here (not delegated) so a literal
       pair underneath — [(a, b).1] — still reaches the elaborator *)
    | Ast.Fst t -> Type.Proj (0, go ctx Infer t)
    | Ast.Snd t -> Type.Proj (1, go ctx Infer t)
    (* [x = y] is the registered equality former [Eq A x y] with [A] inferred
       from [x]: synthesize [x]'s type, then apply the former to it, [x], and
       [y] (checked at that type) *)
    | Ast.EqInfix (x, y) ->
        let spec = eq_spec () in
        let x' = go ctx Infer x in
        let tx = Meta.force !ms (elab_infer ctx x') in
        (* when the equality former is universe-polymorphic, its level argument
           is the sort of the operands' type *)
        let levels =
          if spec.Inductive.nlevels = 0 then
            []
          else
            [ Check.sort_of ctx tx ]
        in
        List.fold_left
          (fun f a -> Type.App (f, a))
          (Type.Ind (spec.Inductive.name, levels))
          [ Value.quote ctx.Check.lvl tx; x'; go ctx (Check tx) y ]
    (* a hole becomes a fresh metavariable; in checking position its type is the
       expected one, and unification (at the surrounding application) solves it.
       In inference position there is nothing to determine it. *)
    | Ast.Hole -> (
        match mode with
        | Check e -> fresh_meta_core ctx (Meta.force !ms e)
        | Infer ->
            Error.type_error
              [ Error.txt
                  "cannot infer the type of a hole _; use it where its type is \
                   determined"
              ])
    (* ascription is the typed identity: it forces a checking judgment for [t],
       and the redex evaporates under evaluation *)
    | Ast.Ascribe (t, a) ->
        let a' = go ctx Infer a in
        let va = Value.eval ctx.Check.env a' in
        let t' = go ctx (Check va) t in
        Type.App (Type.Lam (Type.Explicit, "x", a', Type.Var 0), t')
    (* TODO(let): elaboration in Stage 3 *)
    | Ast.Let _ -> Error.type_error [ Error.txt "let is not yet supported" ]
    (* a pair is sugar for the dependent-pair record's constructor [mk]: checked
       against the Σ it recovers the parameters and elaborates only the
       components; inferred (no expected Σ) it falls back to a constant second
       component family *)
    | Ast.Pair (a, b) -> (
        match notation.Notation.sigma with
        | None ->
            Error.type_error
              [ Error.txt "a pair requires the sigma notation to be registered"
              ]
        | Some mk -> (
            let recovered =
              match mode with
              | Check e -> (
                  match Meta.force !ms e with
                  | Value.VInd (name, levels, [ pa; pb ])
                    when String.equal name mk.Type.ind ->
                      Some (levels, [ pa; pb ])
                  | _ -> None)
              | Infer -> None
            in
            match recovered with
            | Some (levels, pvals) ->
                checked_ctor ctx
                  { mk with Type.clevels = levels }
                  pvals [ a; b ]
            | None ->
                let a' = go ctx Infer a and b' = go ctx Infer b in
                let ta = Meta.force !ms (elab_infer ctx a')
                and tb = Meta.force !ms (elab_infer ctx b') in
                (* a polymorphic pair lands at the sorts of its components *)
                let levels =
                  if (Check.lookup_ind ctx mk.Type.ind).Inductive.nlevels = 0
                  then
                    []
                  else
                    [ Check.sort_of ctx ta; Check.sort_of ctx tb ]
                in
                let bfun =
                  Type.Lam
                    ( Type.Explicit
                    , ""
                    , Value.quote ctx.Check.lvl ta
                    , Value.quote (ctx.Check.lvl + 1) tb )
                in
                List.fold_left
                  (fun core x -> Type.App (core, x))
                  (Type.Ctor { mk with Type.clevels = levels })
                  [ Value.quote ctx.Check.lvl ta; bfun; a'; b' ]))
    | Ast.Sum (a, b) -> (
        match notation.Notation.sum with
        | Some name ->
            let a' = go ctx Infer a in
            let b' = go ctx Infer b in
            (* a polymorphic sum lands at the max of its summands' levels: its
               level arguments are their sorts *)
            let levels =
              if (Check.lookup_ind ctx name).Inductive.nlevels = 0 then
                []
              else
                [ Check.sort_of ctx (Value.eval ctx.Check.env a')
                ; Check.sort_of ctx (Value.eval ctx.Check.env b')
                ]
            in
            Type.App (Type.App (Type.Ind (name, levels), a'), b')
        | None ->
            Error.type_error
              [ Error.txt "+ requires the sum notation to be registered" ])
    | Ast.Sigma (x, a, b) -> sigma_core ctx x a b
    | Ast.Prod (a, b) -> sigma_core ctx "" a b
    (* [()] is the constructor registered for the [unit] notation (the prelude's
       [Unit.unit]); the unit type itself is an ordinary inductive, resolved as
       a [Var] above *)
    | Ast.MkUnit -> (
        match notation.Notation.unit_ctor with
        | Some h -> Type.Ctor h
        | None ->
            Error.type_error
              [ Error.txt "() requires the unit notation to be registered" ])
    (* a numeral expands to succ-applications of the registered nat zero/succ *)
    | Ast.Numeral k -> (
        match notation.Notation.nat with
        | Some (zero, succ) ->
            let rec build k =
              if k = 0 then
                Type.Ctor zero
              else
                Type.App (Type.Ctor succ, build (k - 1))
            in
            build k
        | None ->
            Error.type_error
              [ Error.txt "a numeral requires the nat notation to be registered"
              ])
  (* an application spine [head arg…] *)
  and elab_app ctx mode s : Type.t =
    let head, args = peel s in
    (* [@f …]: the head is wrapped in [At], and every binder of [f]'s type —
       implicit included — consumes a written argument (no insertion) *)
    let explicit, head =
      match head.Ast.desc with
      | Ast.At h -> (true, h)
      | _ -> (false, head)
    in
    match classify_head sg head with
    (* a recursor application. The minors and major are elaborated in *checking*
       position (against their derived types), so check-only forms — a [rfl]
       base case, a constructor major — work; a hole motive on a non-indexed
       recursor is inferred by abstracting the major out of the goal. *)
    | Rec rh ->
        let spec = Check.lookup_ind ctx rh.Type.rind in
        let m = rh.Type.nparams and nidx = rh.Type.nindices in
        let nmin = List.length rh.Type.recs in
        let n = List.length args in
        if n <> m + 1 + nmin + nidx + 1 then
          (* not saturated: produce structurally and let the kernel report it *)
          List.fold_left
            (fun core a -> Type.App (core, go ctx Infer a))
            (Type.Rec rh) args
        else
          let param_asts = List.filteri (fun i _ -> i < m) args in
          let motive_ast = List.nth args m in
          let minor_asts =
            List.filteri (fun i _ -> i > m && i <= m + nmin) args
          in
          let index_asts =
            List.filteri (fun i _ -> i > m + nmin && i < n - 1) args
          in
          let major_ast = List.nth args (n - 1) in
          let is_hole (a : Ast.t) =
            match a.desc with
            | Ast.Hole -> true
            | _ -> false
          in
          (* the parameters and indices may be left as [_] and recovered from
             the major's type [T params indices]: infer the major, read its
             arguments off, and fill each hole (an explicit argument is
             elaborated as written and re-checked by the kernel). Otherwise the
             parameters and indices are explicit and the major is checked
             against the type they determine (so a check-only major works). *)
          let param_cores, index_cores, major_core, levels =
            if List.exists is_hole (param_asts @ index_asts) then
              let major_core = go ctx Infer major_ast in
              match Meta.force !ms (elab_infer ctx major_core) with
              | Value.VInd (nm, levels, margs)
                when String.equal nm rh.Type.rind
                     && List.length margs = m + nidx ->
                  let recover i (a : Ast.t) =
                    if is_hole a then
                      Value.quote ctx.Check.lvl (List.nth margs i)
                    else
                      go ctx Infer a
                  in
                  ( List.mapi recover param_asts
                  , List.mapi (fun j a -> recover (m + j) a) index_asts
                  , major_core
                  , levels )
              | _ ->
                  Error.type_error
                    [ Error.txtf
                        "cannot recover %s's parameters and indices: the major \
                         premise "
                        rh.Type.rind
                    ; Error.txt "is not "
                    ; Error.txtf "%s applied to arguments" rh.Type.rind
                    ]
            else
              (* the explicit parameters and indices are checked against the
                 former's telescope, instantiated at fresh level metas: checking
                 each against its (possibly [Sort]-typed) domain solves the
                 recursor's level arguments — the same level-meta mechanism a
                 former/constructor application uses, resolved by the final
                 zonk *)
              let metas =
                List.init spec.Inductive.nlevels (fun _ ->
                    let ms', id = Meta.fresh_level !ms in
                    ms := ms';
                    Level.LMeta id)
              in
              let rec walk fty cores = function
                | [] -> List.rev cores
                | a :: rest -> (
                    match Meta.force !ms fty with
                    | Value.Pi (_, _, dom, cl) ->
                        let c = go ctx (Check dom) a in
                        walk
                          (Value.apply_closure cl (Value.eval ctx.Check.env c))
                          (c :: cores) rest
                    | _ -> List.rev cores)
              in
              let pi_cores =
                walk
                  (Value.eval []
                     (Type.subst_levels metas (Inductive.former_type spec)))
                  [] (param_asts @ index_asts)
              in
              let param_cores = List.filteri (fun i _ -> i < m) pi_cores in
              let index_cores = List.filteri (fun i _ -> i >= m) pi_cores in
              let pvals = List.map (Value.eval ctx.Check.env) param_cores in
              let ivals = List.map (Value.eval ctx.Check.env) index_cores in
              let major_core =
                go ctx
                  (Check
                     (List.fold_left Value.apply
                        (Value.VInd (rh.Type.rind, metas, []))
                        (pvals @ ivals)))
                  major_ast
              in
              (param_cores, index_cores, major_core, metas)
          in
          (* a polymorphic recursor's level arguments: recovered from the
             major's type above, or solved as level metas from the explicit
             parameters/indices *)
          let rh = { rh with Type.rlevels = levels } in
          let pvals = List.map (Value.eval ctx.Check.env) param_cores in
          let motive_core =
            match (motive_ast.Ast.desc, mode) with
            (* infer a non-indexed recursor's hole motive by abstracting the
               major out of the goal: [P := λ (x : T params) ⇒ goal[major ↦ x]].
               An indexed motive abstracts the indices too (not done here), so
               an indexed recursor's motive must be written out. *)
            | Ast.Hole, Check g when nidx = 0 ->
                let lvl = ctx.Check.lvl in
                let t_c =
                  List.fold_left
                    (fun c p -> Type.App (c, p))
                    (Type.Ind (rh.Type.rind, []))
                    param_cores
                in
                let major_nf =
                  Value.quote lvl (Value.eval ctx.Check.env major_core)
                in
                Type.Lam
                  ( Type.Explicit
                  , "x"
                  , t_c
                  , abstract major_nf (Value.quote lvl (Meta.force !ms g)) )
            | _ -> go ctx Infer motive_ast
          in
          let pmot = Value.eval ctx.Check.env motive_core in
          let minor_cores =
            List.mapi
              (fun i ma ->
                go ctx
                  (Check
                     (Check.minor_type ~levels:rh.Type.rlevels ctx spec pvals
                        pmot i))
                  ma)
              minor_asts
          in
          List.fold_left
            (fun core a -> Type.App (core, a))
            (Type.Rec rh)
            (param_cores
            @ (motive_core :: minor_cores)
            @ index_cores
            @ [ major_core ])
    | Ctor (spec, h) -> (
        let nfields = h.Type.carity - h.Type.nparams in
        (* checked against its own inductive with the parameters omitted:
           recover them from the expected type and elaborate only the fields *)
        let recovered =
          match mode with
          | Check e -> (
              match Meta.force !ms e with
              | Value.VInd (name, levels, pvals)
                when String.equal name h.Type.ind && List.length args = nfields
                ->
                  Some (levels, pvals)
              | _ -> None)
          | Infer -> None
        in
        let cty = Value.eval [] (Inductive.ctor_type spec h.Type.cindex) in
        match recovered with
        (* the expected inductive type also supplies the level arguments *)
        | Some (levels, pvals) ->
            checked_ctor ctx { h with Type.clevels = levels } pvals args
        (* the parameters are omitted but no expected inductive type pins them
           (inference position, or a non-matching goal): insert a fresh
           metavariable per parameter and let unifying the field arguments solve
           the ones they determine ([Box.wrap a] fixes [A] from [a]; a genuinely
           undetermined parameter — [Sum.inl a] leaving [B] free — surfaces as
           an unsolved-hole error). Gated off under [@f], which forces the
           parameters explicit. *)
        | None
          when (not explicit)
               && h.Type.nparams > 0
               && List.length args = nfields ->
            let rec params core ty k =
              if k = 0 then
                (core, ty)
              else
                match Meta.force !ms ty with
                | Value.Pi (_, _, dom, c) ->
                    let m = fresh_meta_core ctx dom in
                    params
                      (Type.App (core, m))
                      (Value.apply_closure c (Value.eval ctx.Check.env m))
                      (k - 1)
                | _ -> (core, ty)
            in
            let head_core, field_ty = params (Type.Ctor h) cty h.Type.nparams in
            elab_spine ctx head_core field_ty args
        (* otherwise the parameters are explicit (or we are inferring): walk the
           constructor's full type. For a polymorphic inductive, infer the level
           arguments from the explicit arguments as for a former. *)
        | None when spec.Inductive.nlevels > 0 ->
            elab_poly_head ctx ~explicit ~mode ~nlv:spec.Inductive.nlevels
              ~tenv:[]
              ~tycore:(Inductive.ctor_type spec h.Type.cindex)
              ~mk_head:(fun ls -> Type.Ctor { h with Type.clevels = ls })
              args
        | None -> elab_spine ctx (Type.Ctor h) cty args)
    | Other -> (
        let head_core = go ctx Infer head in
        match head_core with
        (* a polymorphic inductive former: infer its level arguments from the
           argument types, then build the applied former *)
        | Type.Ind (name, _)
          when (Check.lookup_ind ctx name).Inductive.nlevels > 0 ->
            let spec = Check.lookup_ind ctx name in
            elab_poly_head ctx ~explicit ~mode ~nlv:spec.Inductive.nlevels
              ~tenv:[]
              ~tycore:(Inductive.former_type spec)
              ~mk_head:(fun ls -> Type.Ind (name, ls))
              args
        (* a polymorphic def applied to arguments: instantiate its type at fresh
           level metas and elaborate the spine. Unification solves the metas
           through the head type's sorts and inductive level arguments — so even
           a def with implicit level-bearing parameters ([subst]/[cong]'s [{A :
           Sort u}]) infers its levels. *)
        | Type.Def (i, _) -> (
            match poly_def_info ctx i with
            | Some (nlevels, denv, tybody) ->
                elab_poly_head ctx ~explicit ~mode ~nlv:nlevels ~tenv:denv
                  ~tycore:tybody
                  ~mk_head:(fun ls -> Type.Def (i, ls))
                  args
            | None ->
                elab_spine ~explicit ~mode ctx head_core
                  (elab_infer ctx head_core) args)
        | _ ->
            elab_spine ~explicit ~mode ctx head_core (elab_infer ctx head_core)
              args)
  (* a level-polymorphic head ([T], a constructor, or a def) applied to [args]:
     mint a fresh level meta per level parameter, instantiate the head's type
     [tycore] (which mentions those parameters, evaluated in environment [tenv])
     at them, and run the ordinary spine elaboration. Implicit insertion and
     unification then solve the level metas through the argument types (and any
     leftover against the goal, via [coerce]) — exactly as for the term
     arguments. This is the single mechanism for every polymorphic use; the
     [mk_head levels] node carries the solved levels after zonking. *)
  and elab_poly_head ctx ~explicit ~mode ~nlv ~tenv ~tycore ~mk_head args :
      Type.t =
    let metas =
      List.init nlv (fun _ ->
          let ms', id = Meta.fresh_level !ms in
          ms := ms';
          Level.LMeta id)
    in
    let head_ty = Value.eval tenv (Type.subst_levels metas tycore) in
    elab_spine ~explicit ~mode ctx (mk_head metas) head_ty args
  (* elaborate each argument against the domain read off the head's (function)
     type, advancing that type as arguments are consumed so each argument is in
     checking position. [~explicit] (set under an [@f] head) makes an implicit
     binder consume the next written argument instead of inserting a meta; once
     the arguments run out, [~mode] drives expected-type implicit insertion on
     the result (suppressed under [@f]). *)
  and elab_spine ?(explicit = false) ?(mode = Infer) ctx head_core head_ty args
      : Type.t =
    let rec walk core ty = function
      | [] ->
          if explicit then
            core
          else
            coerce ctx mode core ty
      | a :: rest -> (
          match Meta.force !ms ty with
          (* an implicit binder while an explicit argument is still to come:
             insert a fresh metavariable for it (solved by unification when the
             explicit argument lands below) and retry against the next binder.
             Insertion is gated on a remaining argument, so a partially-applied
             head keeps its trailing implicit binders rather than spawning
             unsolvable metas. Under [@f] ([explicit]) the binder instead
             consumes the written argument, like an explicit one. *)
          | Value.Pi (Type.Implicit, _, dom, c) when not explicit ->
              let m = fresh_meta_core ctx dom in
              walk
                (Type.App (core, m))
                (Value.apply_closure c (Value.eval ctx.Check.env m))
                (a :: rest)
          | Value.Pi (_, _, dom, c) ->
              let a' = go ctx (Check dom) a in
              (* only when the domain still has an unsolved metavariable is
                 there anything to solve; otherwise skip — inferring [a']'s type
                 could fail on a check-only form like [rfl], and is needless
                 work *)
              if Type.has_meta (Value.quote ctx.Check.lvl dom) then
                ms := Meta.unify !ms ctx dom (elab_infer ctx a');
              walk
                (Type.App (core, a'))
                (Value.apply_closure c (Value.eval ctx.Check.env a'))
                rest
          (* not a function (an ill-typed spine, or one whose head type we did
             not track): produce core and let the kernel report it *)
          | _ -> walk (Type.App (core, go ctx Infer a)) ty rest)
    in
    walk head_core head_ty args
  (* a constructor [h] whose [pvals] parameters are recovered (from an expected
     inductive type, or inferred for a pair) and prepended, then its remaining
     fields [args] elaborated against the instantiated field telescope *)
  and checked_ctor ctx (h : Type.ctor_head) pvals args : Type.t =
    let spec =
      match Signature.find sg h.Type.ind with
      | Some s -> s
      | None -> assert false
    in
    let head_core =
      List.fold_left
        (fun core p -> Type.App (core, Value.quote ctx.Check.lvl p))
        (Type.Ctor h) pvals
    in
    (* a Pi is a type, so instantiate its parameter binders by walking the
       closures, not by [Value.apply]; the constructor's level arguments
       instantiate the type's level variables first *)
    let cty =
      Value.eval []
        (Type.subst_levels h.Type.clevels
           (Inductive.ctor_type spec h.Type.cindex))
    in
    let rec instantiate ty = function
      | [] -> ty
      | p :: rest -> (
          match ty with
          | Value.Pi (_, _, _, c) -> instantiate (Value.apply_closure c p) rest
          | _ -> ty)
    in
    elab_spine ctx head_core (instantiate cty pvals) args
  (* [match e with | Cᵢ x̄ᵢ ⇒ bᵢ … end]: flat case analysis desugared to the
     recursor [T.rec params motive minors… indices e]. The motive is recovered
     from the expected goal (checking mode, non-indexed only). Each branch
     becomes the constructor's minor premise — a λ binding the constructor's
     fields to the pattern variables, with each recursive field's induction
     hypothesis bound to [_] (case analysis ignores it; recursion uses the
     recursor directly). A trailing [| _ ⇒ b] is a catch-all covering every
     unlisted constructor (its fields bound to [_], so [b] cannot inspect
     them). *)
  and elab_match ctx mode scrut arms : Type.t =
    let scrut_core = go ctx Infer scrut in
    match Meta.force !ms (elab_infer ctx scrut_core) with
    | Value.VInd (tname, levels, margs) ->
        let spec = Check.lookup_ind ctx tname in
        let rh = Inductive.rec_head ~levels spec in
        let m = rh.Type.nparams in
        if rh.Type.nindices > 0 then
          Error.type_error
            [ Error.txtf
                "match on the indexed family %s is not yet supported; use \
                 %s.rec"
                tname tname
            ];
        (* a trailing [| _ ⇒ b] is a catch-all; it must be last, singular, and
           bind no variables. Everything else is an explicit constructor arm. *)
        let is_wild (cn, _, _) = String.equal cn "_" in
        let nargs = List.length arms in
        List.iteri
          (fun i ((_, xs, _) as arm) ->
            if is_wild arm then (
              if i <> nargs - 1 then
                Error.type_error
                  [ Error.txt "a catch-all branch | _ => … must come last" ];
              if xs <> [] then
                Error.type_error
                  [ Error.txt
                      "a catch-all branch | _ => … cannot bind variables"
                  ]
            ))
          arms;
        let catchall =
          match List.rev arms with
          | last :: _ when is_wild last ->
              let _, _, b = last in
              Some b
          | _ -> None
        in
        let explicit = List.filter (fun a -> not (is_wild a)) arms in
        (* every explicit arm names an actual constructor *)
        List.iter
          (fun (cn, _, _) ->
            if
              not
                (List.exists
                   (fun (c : Inductive.ctor) -> String.equal c.cname cn)
                   spec.Inductive.ctors)
            then
              Error.type_error
                [ Error.txtf "%s is not a constructor of %s" cn tname ])
          explicit;
        (* the (binder names, body) for constructor [c]: its explicit arm if any
           (variables checked for arity), else the catch-all (all fields bound
           to [_]), else a missing-branch error *)
        let arm_for (c : Inductive.ctor) =
          match
            List.filter
              (fun (cn, _, _) -> String.equal cn c.Inductive.cname)
              explicit
          with
          | [ (_, xs, b) ] ->
              let nfields = List.length c.Inductive.fields in
              if List.length xs <> nfields then
                Error.type_error
                  [ Error.txtf
                      "the pattern for %s.%s binds %d variable(s) but the \
                       constructor has %d field(s)"
                      tname c.Inductive.cname (List.length xs) nfields
                  ];
              (xs, b)
          | [] -> (
              match catchall with
              | Some b -> (List.map (fun _ -> "_") c.Inductive.fields, b)
              | None ->
                  Error.type_error
                    [ Error.txtf "match is missing a branch for %s.%s" tname
                        c.Inductive.cname
                    ])
          | _ ->
              Error.type_error
                [ Error.txtf "match has more than one branch for %s.%s" tname
                    c.Inductive.cname
                ]
        in
        let goal =
          match mode with
          | Check g -> Meta.force !ms g
          | Infer ->
              Error.type_error
                [ Error.txt
                    "cannot infer the result type of a match; annotate it \
                     (e.g. (match … end : T))"
                ]
        in
        let lvl = ctx.Check.lvl in
        let pvals = List.filteri (fun i _ -> i < m) margs in
        let param_cores = List.map (Value.quote lvl) pvals in
        (* motive [P := λ (x : T params) ⇒ goal[e ↦ x]] (non-indexed, so no
           index binders to abstract) *)
        let t_c =
          List.fold_left
            (fun c p -> Type.App (c, p))
            (Type.Ind (tname, levels))
            param_cores
        in
        let scrut_nf = Value.quote lvl (Value.eval ctx.Check.env scrut_core) in
        let motive_core =
          Type.Lam
            (Type.Explicit, "x", t_c, abstract scrut_nf (Value.quote lvl goal))
        in
        let pmot = Value.eval ctx.Check.env motive_core in
        let minor_cores =
          List.mapi
            (fun i (c : Inductive.ctor) ->
              let xs, body = arm_for c in
              (* the minor's binders: a field's pattern variable, and [_] for
                 the induction hypothesis that follows each recursive field *)
              let names =
                List.concat
                  (List.map2
                     (fun x (a : Inductive.arg) ->
                       match a.Inductive.recursive with
                       | Some _ -> [ x; "_" ]
                       | None -> [ x ])
                     xs c.Inductive.fields)
              in
              build_minor ctx names body
                (Check.minor_type ~levels ctx spec pvals pmot i))
            spec.Inductive.ctors
        in
        List.fold_left
          (fun c a -> Type.App (c, a))
          (Type.Rec rh)
          (param_cores @ (motive_core :: minor_cores) @ [ scrut_core ])
    | _ ->
        Error.type_error
          [ Error.txt "the scrutinee of a match must have an inductive type" ]
  (* build a minor premise: wrap [body] in λs over the minor type's telescope,
     naming each binder from [names] (pattern variables and [_] for ignored
     induction hypotheses); the body is checked against the telescope's tail *)
  and build_minor ctx names body minor_ty : Type.t =
    match (names, Meta.force !ms minor_ty) with
    | name :: rest, Value.Pi (ic, _, dom, cod) ->
        let v = Value.Neutral (Value.Var ctx.Check.lvl) in
        Type.Lam
          ( ic
          , name
          , Value.quote ctx.Check.lvl dom
          , build_minor (Check.bind name dom ctx) rest body
              (Value.apply_closure cod v) )
    | [], final -> go ctx (Check final) body
    | _ -> assert false
  (* the [Σ]/[×] sugar: the registered dependent-pair former applied to [A] and
     the family [λ x ⇒ B]. When that inductive is universe-polymorphic its level
     arguments are the sorts of the two components ([Sort u] of [A], [Sort v] of
     [B]); monomorphic, they are empty. *)
  and sigma_core ctx x a b : Type.t =
    let name = sigma_form () in
    let a' = go ctx Infer a in
    let av = Value.eval ctx.Check.env a' in
    let ctx' = Check.bind x av ctx in
    let body = go ctx' Infer b in
    let levels =
      if (Check.lookup_ind ctx name).Inductive.nlevels = 0 then
        []
      else
        [ Check.sort_of ctx av
        ; Check.sort_of ctx' (Value.eval ctx'.Check.env body)
        ]
    in
    Type.App
      ( Type.App (Type.Ind (name, levels), a')
      , Type.Lam (Type.Explicit, x, a', body) )
  in
  let core = go ctx0 mode0 s0 in
  (* replace solved metavariables with their solutions; an unsolved one left
     behind is an unfillable hole, which the kernel must never see *)
  let core = Meta.zonk !ms ctx0.Check.lvl core in
  if Type.has_meta core then
    Error.type_error
      [ Error.txt "could not infer a hole (_); add a type annotation" ];
  if Type.has_level_meta core then
    Error.type_error
      [ Error.txt "could not infer a universe level; annotate it (e.g. Sort u)"
      ];
  core

let infer ?(levels = []) notation ctx s = elaborate ~levels notation ctx Infer s

let check ?(levels = []) notation ctx s expected =
  elaborate ~levels notation ctx (Check expected) s
