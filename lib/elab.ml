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

let elaborate notation (ctx0 : Check.ctx) mode0 s0 =
  let sg = ctx0.Check.signature in
  let fresh (ctx : Check.ctx) = Value.Neutral (Value.Var ctx.Check.lvl) in
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
    | Ast.Pi (x, a, b) ->
        let a' = go ctx Infer a in
        let b' = go (Check.bind x (Value.eval ctx.Check.env a') ctx) Infer b in
        Type.Pi (x, a', b')
    | Ast.Arrow (a, b) ->
        let a' = go ctx Infer a in
        let b' = go (Check.bind "" (Value.eval ctx.Check.env a') ctx) Infer b in
        Type.Pi ("", a', b')
    | Ast.Lam (x, a, b) ->
        let a' = go ctx Infer a in
        let va = Value.eval ctx.Check.env a' in
        (* in checking position, the expected codomain flows into the body so a
           constructor there can drop its parameters *)
        let body_mode =
          match mode with
          | Check (Value.Pi (_, _, c)) ->
              Check (Value.apply_closure c (fresh ctx))
          | _ -> Infer
        in
        Type.Lam (x, a', go (Check.bind x va ctx) body_mode b)
    | Ast.App _ -> elab_app ctx mode s
    (* the generic record projections; handled here (not delegated) so a literal
       pair underneath — [(a, b).1] — still reaches the elaborator *)
    | Ast.Fst t -> Type.Proj (0, go ctx Infer t)
    | Ast.Snd t -> Type.Proj (1, go ctx Infer t)
    (* ascription is the typed identity: it forces a checking judgment for [t],
       and the redex evaporates under evaluation (as in {!Ast.to_term}) *)
    | Ast.Ascribe (t, a) ->
        let a' = go ctx Infer a in
        let va = Value.eval ctx.Check.env a' in
        let t' = go ctx (Check va) t in
        Type.App (Type.Lam ("x", a', Type.Var 0), t')
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
            match mode with
            | Check (Value.VInd (name, [ pa; pb ]))
              when String.equal name mk.Type.ind ->
                checked_ctor ctx mk [ pa; pb ] [ a; b ]
            | _ ->
                let a' = go ctx Infer a and b' = go ctx Infer b in
                let ta = Check.infer ctx a' and tb = Check.infer ctx b' in
                let bfun =
                  Type.Lam
                    ( ""
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
        match mode with
        (* checked against its own inductive with the parameters omitted:
           recover them from the expected type and elaborate only the fields *)
        | Check (Value.VInd (name, pvals))
          when String.equal name h.Type.ind && List.length args = nfields ->
            checked_ctor ctx h pvals args
        (* otherwise the parameters are explicit (or we are inferring): walk the
           constructor's full type *)
        | _ ->
            let cty = Value.eval [] (Inductive.ctor_type spec h.Type.cindex) in
            elab_spine ctx (Type.Ctor h) cty args)
    | Other ->
        let head_core = go ctx Infer head in
        elab_spine ctx head_core (Check.infer ctx head_core) args
  (* elaborate each argument against the domain read off the head's (function)
     type, advancing that type as arguments are consumed so each argument is in
     checking position *)
  and elab_spine ctx head_core head_ty args : Type.t =
    let rec walk core ty = function
      | [] -> core
      | a :: rest -> (
          match ty with
          | Value.Pi (_, dom, c) ->
              let a' = go ctx (Check dom) a in
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
          | Value.Pi (_, _, c) -> instantiate (Value.apply_closure c p) rest
          | _ -> ty)
    in
    elab_spine ctx head_core (instantiate cty pvals) args
  in
  go ctx0 mode0 s0

let infer notation ctx s = elaborate notation ctx Infer s

let check notation ctx s expected = elaborate notation ctx (Check expected) s
