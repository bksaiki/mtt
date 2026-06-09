(* Bidirectional elaboration. [go ctx mode s] produces a core term for the
   surface term [s]; [mode] is the elaboration direction — [Infer] for a
   synthesizing position, [Check ty] when [s] is expected to have type [ty]. The
   mode is consulted only where it lets us drop an argument: at a constructor
   application (to recover omitted parameters) and through a lambda body.
   Elsewhere the core is produced purely structurally, exactly as {!Ast.to_term}
   would, and the kernel's later re-check supplies the typing.

   Types are computed (reusing {!Value} and {!Check}) only where they drive a
   decision: a function application needs its head's Pi type to know each
   argument's domain, and constructor inference needs the expected inductive's
   parameters. *)

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

let imax i j =
  if j = 0 then
    0
  else
    max i j

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
  | Type.Pi (ic, x, a, b) -> Type.Pi (ic, x, lift d c a, lift d (c + 1) b)
  | Type.Lam (ic, x, a, b) -> Type.Lam (ic, x, lift d c a, lift d (c + 1) b)
  | Type.App (f, a) -> Type.App (lift d c f, lift d c a)
  | Type.Proj (i, e) -> Type.Proj (i, lift d c e)
  | Type.Eq (a, x, y) -> Type.Eq (lift d c a, lift d c x, lift d c y)
  | Type.J (p, dd, pr) -> Type.J (lift d c p, lift d c dd, lift d c pr)
  | Type.Sort _
  | Type.Refl
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
      | Type.Pi (ic, x, a, b) -> Type.Pi (ic, x, go k a, go (k + 1) b)
      | Type.Lam (ic, x, a, b) -> Type.Lam (ic, x, go k a, go (k + 1) b)
      | Type.App (f, a) -> Type.App (go k f, go k a)
      | Type.Proj (i, e) -> Type.Proj (i, go k e)
      | Type.Eq (a, x, y) -> Type.Eq (go k a, go k x, go k y)
      | Type.J (p, d, pr) -> Type.J (go k p, go k d, go k pr)
      | Type.Sort _
      | Type.Refl
      | Type.Ind _
      | Type.Ctor _
      | Type.Rec _
      | Type.Meta _ ->
          t
  in
  go 0 t

let elaborate notation (ctx0 : Check.ctx) mode0 s0 =
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
     longer knows them). A meta-free subterm is still handed to [Check.infer];
     only the meta-carrying spine is walked here, forcing solutions via
     [Meta]. *)
  let rec elab_infer ctx (t : Type.t) : Value.t =
    if not (Type.has_meta t) then
      Check.infer ctx t
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
          | Value.VInd (name, params) ->
              Check.field_type
                (Check.lookup_ind ctx name)
                params
                (Value.eval ctx.Check.env e)
                i
          | _ -> assert false)
      | Type.J (p, _, pr) -> (
          match Meta.force !ms (elab_infer ctx pr) with
          | Value.Eq (_, _, vy) ->
              Value.apply
                (Value.apply (Value.eval ctx.Check.env p) vy)
                (Value.eval ctx.Check.env pr)
          | _ -> assert false)
      | _ -> Check.infer ctx t
  and sort_of_ty ctx a =
    match Meta.force !ms (elab_infer ctx a) with
    | Value.Sort i -> i
    | _ -> 0
  in
  (* the inductive registered for the [sigma] role, that [Σ]/[×] desugar to *)
  let sigma_form () =
    match notation.Notation.sigma with
    | Some mk -> mk.Type.ind
    | None ->
        Error.type_error
          [ Error.txt "Σ/× requires the sigma notation to be registered" ]
  in
  let rec go (ctx : Check.ctx) mode (s : Ast.t) : Type.t =
    match s.desc with
    (* a bare name is a local binder (de Bruijn) first, otherwise a global
       inductive former — matching {!Ast.to_term} *)
    | Ast.Var x -> (
        match List.find_index (String.equal x) ctx.Check.names with
        | Some i -> Type.Var i
        | None -> (
            match Signature.find sg x with
            | Some spec -> Type.Ind spec.Inductive.name
            | None -> raise (Ast.Unbound_variable (s.loc, x))))
    | Ast.Field ({ desc = Ast.Var tname; _ }, field) -> (
        match Signature.find sg tname with
        | None -> raise (Ast.Unbound_variable (s.loc, tname))
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
                  raise (Ast.Unbound_variable (s.loc, tname ^ "." ^ field))))
    | Ast.Field (_, f) -> raise (Ast.Unbound_variable (s.loc, "_." ^ f))
    | Ast.Sort i -> Type.Sort i
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
    | Ast.App _ -> elab_app ctx mode s
    (* the generic record projections; handled here (not delegated) so a literal
       pair underneath — [(a, b).1] — still reaches the elaborator *)
    | Ast.Fst t -> Type.Proj (0, go ctx Infer t)
    | Ast.Snd t -> Type.Proj (1, go ctx Infer t)
    (* [x = y] is [Eq A x y] with [A] inferred from [x]: synthesize [x]'s type,
       use it as the equality's type, and check [y] against it *)
    | Ast.EqInfix (x, y) ->
        let x' = go ctx Infer x in
        let tx = Meta.force !ms (elab_infer ctx x') in
        Type.Eq (Value.quote ctx.Check.lvl tx, x', go ctx (Check tx) y)
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
       and the redex evaporates under evaluation (as in {!Ast.to_term}) *)
    | Ast.Ascribe (t, a) ->
        let a' = go ctx Infer a in
        let va = Value.eval ctx.Check.env a' in
        let t' = go ctx (Check va) t in
        Type.App (Type.Lam (Type.Explicit, "x", a', Type.Var 0), t')
    (* a pair is sugar for the dependent-pair record's constructor [mk]: checked
       against the Σ it recovers the parameters (Phase-1 omission); inferred it
       defaults to the constant family, as the old (Pair-infer) rule did *)
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
                  | Value.VInd (name, [ pa; pb ])
                    when String.equal name mk.Type.ind ->
                      Some [ pa; pb ]
                  | _ -> None)
              | Infer -> None
            in
            match recovered with
            | Some pvals -> checked_ctor ctx mk pvals [ a; b ]
            | None ->
                let a' = go ctx Infer a and b' = go ctx Infer b in
                let ta = elab_infer ctx a' and tb = elab_infer ctx b' in
                let bfun =
                  Type.Lam
                    ( Type.Explicit
                    , ""
                    , Value.quote ctx.Check.lvl ta
                    , Value.quote (ctx.Check.lvl + 1) tb )
                in
                List.fold_left
                  (fun core x -> Type.App (core, x))
                  (Type.Ctor mk)
                  [ Value.quote ctx.Check.lvl ta; bfun; a'; b' ]))
    (* the equality/J/Σ/×/+ formers contain arbitrary subterms (a J motive, a Σ
       body) that may themselves use surface sugar like [x = y]; those subterms
       must elaborate through [go], not {!Ast.to_term} (which is type-free and
       chokes on an inferred form). We assemble the same core [to_term]
       would. *)
    | Ast.Eq (a, x, y) ->
        Type.Eq (go ctx Infer a, go ctx Infer x, go ctx Infer y)
    (* a hole motive in checking position is inferred by abstracting the proof's
       (second) endpoint out of the goal — based path induction's motive [P : Π
       (z : A) ⇒ Eq A x z → Sort] with [P y p ≡ goal] *)
    | Ast.J ({ desc = Ast.Hole; _ }, d, pr) when mode <> Infer -> (
        let g =
          match mode with
          | Check g -> Meta.force !ms g
          | Infer -> assert false
        in
        let pr_core = go ctx Infer pr in
        match Meta.force !ms (elab_infer ctx pr_core) with
        | Value.Eq (a, x, y) ->
            let lvl = ctx.Check.lvl in
            let a_c = Value.quote lvl a
            and x_c = Value.quote lvl x
            and y_c = Value.quote lvl y
            and g_c = Value.quote lvl g in
            (* [λ z ⇒ λ q ⇒ goal[y ↦ z]]: abstract [y] (one binder, [z]), then
               lift over the unused proof binder [q] *)
            let body = lift 1 0 (abstract y_c g_c) in
            let qty = Type.Eq (lift 1 0 a_c, lift 1 0 x_c, Type.Var 0) in
            let motive =
              Type.Lam
                ( Type.Explicit
                , "z"
                , a_c
                , Type.Lam (Type.Explicit, "q", qty, body) )
            in
            (* the diagonal proves [P x refl]; check [d] against it *)
            let pmot = Value.eval ctx.Check.env motive in
            let d_ty = Value.apply (Value.apply pmot x) Value.Refl in
            Type.J (motive, go ctx (Check d_ty) d, pr_core)
        | _ ->
            Error.type_error
              [ Error.txt
                  "cannot infer the J motive: the proof's type is not an \
                   equality"
              ])
    | Ast.J (p, d, pr) ->
        Type.J (go ctx Infer p, go ctx Infer d, go ctx Infer pr)
    | Ast.Sum (a, b) -> (
        match notation.Notation.sum with
        | Some name ->
            Type.App (Type.App (Type.Ind name, go ctx Infer a), go ctx Infer b)
        | None ->
            Error.type_error
              [ Error.txt "+ requires the sum notation to be registered" ])
    | Ast.Sigma (x, a, b) ->
        let a' = go ctx Infer a in
        let body =
          go (Check.bind x (Value.eval ctx.Check.env a') ctx) Infer b
        in
        Type.App
          ( Type.App (Type.Ind (sigma_form ()), a')
          , Type.Lam (Type.Explicit, x, a', body) )
    | Ast.Prod (a, b) ->
        let a' = go ctx Infer a in
        let body =
          go (Check.bind "" (Value.eval ctx.Check.env a') ctx) Infer b
        in
        Type.App
          ( Type.App (Type.Ind (sigma_form ()), a')
          , Type.Lam (Type.Explicit, "", a', body) )
    (* the remaining leaf forms ([()], numerals, refl) carry no elaborable
       subterm, so the type-free {!Ast.to_term} (with its notation) suffices *)
    | _ -> Ast.to_term sg ~notation ctx.Check.names s
  (* an application spine [head arg…] *)
  and elab_app ctx mode s : Type.t =
    let head, args = peel s in
    match classify_head sg head with
    (* a recursor is motive-polymorphic; produce its core structurally and let
       the kernel's bespoke rule type the saturated spine *)
    | Rec rh -> (
        let m = rh.Type.nparams in
        let n = List.length args in
        let saturated = n = m + 1 + List.length rh.Type.recs + 1 in
        let motive_is_hole =
          match List.nth_opt args m with
          | Some { desc = Ast.Hole; _ } -> true
          | _ -> false
        in
        match mode with
        (* a hole motive on a saturated recursor in checking position is
           inferred by abstracting the major premise out of the goal: [P := λ (x
           : T params) ⇒ goal[major ↦ x]] *)
        | Check g when saturated && motive_is_hole ->
            let g = Meta.force !ms g in
            let param_asts = List.filteri (fun i _ -> i < m) args in
            let minor_asts =
              List.filteri (fun i _ -> i > m && i < n - 1) args
            in
            let major_ast = List.nth args (n - 1) in
            let param_cores = List.map (go ctx Infer) param_asts in
            let param_vals = List.map (Value.eval ctx.Check.env) param_cores in
            let t_val =
              List.fold_left Value.apply
                (Value.VInd (rh.Type.rind, []))
                param_vals
            in
            let t_c =
              List.fold_left
                (fun c p -> Type.App (c, p))
                (Type.Ind rh.Type.rind) param_cores
            in
            let major_core = go ctx (Check t_val) major_ast in
            let lvl = ctx.Check.lvl in
            let major_nf =
              Value.quote lvl (Value.eval ctx.Check.env major_core)
            in
            let motive =
              Type.Lam
                (Type.Explicit, "x", t_c, abstract major_nf (Value.quote lvl g))
            in
            let minor_cores = List.map (go ctx Infer) minor_asts in
            List.fold_left
              (fun core a -> Type.App (core, a))
              (Type.Rec rh)
              (param_cores @ [ motive ] @ minor_cores @ [ major_core ])
        | _ ->
            List.fold_left
              (fun core a -> Type.App (core, go ctx Infer a))
              (Type.Rec rh) args)
    | Ctor (spec, h) -> (
        let nfields = h.Type.carity - h.Type.nparams in
        (* checked against its own inductive with the parameters omitted:
           recover them from the expected type and elaborate only the fields *)
        let recovered =
          match mode with
          | Check e -> (
              match Meta.force !ms e with
              | Value.VInd (name, pvals)
                when String.equal name h.Type.ind && List.length args = nfields
                ->
                  Some pvals
              | _ -> None)
          | Infer -> None
        in
        match recovered with
        | Some pvals -> checked_ctor ctx h pvals args
        (* otherwise the parameters are explicit (or we are inferring): walk the
           constructor's full type *)
        | None ->
            let cty = Value.eval [] (Inductive.ctor_type spec h.Type.cindex) in
            elab_spine ctx (Type.Ctor h) cty args)
    | Other ->
        let head_core = go ctx Infer head in
        elab_spine ctx head_core (elab_infer ctx head_core) args
  (* elaborate each argument against the domain read off the head's (function)
     type, advancing that type as arguments are consumed so each argument is in
     checking position *)
  and elab_spine ctx head_core head_ty args : Type.t =
    let rec walk core ty = function
      | [] -> core
      | a :: rest -> (
          match Meta.force !ms ty with
          (* an implicit binder while an explicit argument is still to come:
             insert a fresh metavariable for it (solved by unification when the
             explicit argument lands below) and retry against the next binder.
             Insertion is gated on a remaining argument, so a partially-applied
             head keeps its trailing implicit binders rather than spawning
             unsolvable metas. *)
          | Value.Pi (Type.Implicit, _, dom, c) ->
              let m = fresh_meta_core ctx dom in
              walk
                (Type.App (core, m))
                (Value.apply_closure c (Value.eval ctx.Check.env m))
                (a :: rest)
          | Value.Pi (_, _, dom, c) ->
              let a' = go ctx (Check dom) a in
              (* only when the domain still has an unsolved metavariable is
                 there anything to solve; otherwise skip — inferring [a']'s type
                 could fail on a check-only form like [refl], and is needless
                 work *)
              if Type.has_meta (Value.quote ctx.Check.lvl dom) then
                ms := Meta.unify !ms ctx.Check.lvl dom (elab_infer ctx a');
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
       closures, not by [Value.apply] *)
    let cty = Value.eval [] (Inductive.ctor_type spec h.Type.cindex) in
    let rec instantiate ty = function
      | [] -> ty
      | p :: rest -> (
          match ty with
          | Value.Pi (_, _, _, c) -> instantiate (Value.apply_closure c p) rest
          | _ -> ty)
    in
    elab_spine ctx head_core (instantiate cty pvals) args
  in
  let core = go ctx0 mode0 s0 in
  (* replace solved metavariables with their solutions; an unsolved one left
     behind is an unfillable hole, which the kernel must never see *)
  let core = Meta.zonk !ms ctx0.Check.lvl core in
  if Type.has_meta core then
    Error.type_error
      [ Error.txt "could not infer a hole (_); add a type annotation" ];
  core

let infer notation ctx s = elaborate notation ctx Infer s

let check notation ctx s expected = elaborate notation ctx (Check expected) s
