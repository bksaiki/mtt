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
    (* the remaining builtin formers and their intro/elim forms (and the
       [()]/numeral/Σ/×/+ sugar) carry no constructor inference yet; translate
       them syntactically, exactly as {!Ast.to_term} does, against the binder
       names. [Sum]'s constructors and recursor are ordinary qualified names
       ([Sum.inl], [Sum.rec]), so they ride the application spine above. *)
    | _ -> Ast.to_term sg ~notation ctx.Check.names s
  (* an application spine [head arg…] *)
  and elab_app ctx mode s : Type.t =
    let head, args = peel s in
    match classify_head sg head with
    (* a recursor is motive-polymorphic; produce its core structurally and let
       the kernel's bespoke rule type the saturated spine *)
    | Rec rh ->
        List.fold_left
          (fun core a -> Type.App (core, go ctx Infer a))
          (Type.Rec rh) args
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
