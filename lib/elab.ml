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
    (* ascription is the typed identity: it forces a checking judgment for [t],
       and the redex evaporates under evaluation (as in {!Ast.to_term}) *)
    | Ast.Ascribe (t, a) ->
        let a' = go ctx Infer a in
        let va = Value.eval ctx.Check.env a' in
        let t' = go ctx (Check va) t in
        Type.App (Type.Lam ("x", a', Type.Var 0), t')
    (* the builtin formers and their intro/elim forms (and the [()]/numeral
       sugar) carry no constructor inference yet; translate them syntactically,
       exactly as {!Ast.to_term} does, against the current binder names *)
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
            let head_core =
              List.fold_left
                (fun core p -> Type.App (core, Value.quote ctx.Check.lvl p))
                (Type.Ctor h) pvals
            in
            (* the field telescope: the constructor's type with its parameter
               binders instantiated by the recovered parameter values (a Pi is a
               type, so we walk its closures rather than [Value.apply]) *)
            let cty = Value.eval [] (Inductive.ctor_type spec h.Type.cindex) in
            let rec instantiate ty = function
              | [] -> ty
              | p :: rest -> (
                  match ty with
                  | Value.Pi (_, _, c) ->
                      instantiate (Value.apply_closure c p) rest
                  | _ -> ty)
            in
            elab_spine ctx head_core (instantiate cty pvals) args
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
  in
  go ctx0 mode0 s0

let infer notation ctx s = elaborate notation ctx Infer s

let check notation ctx s expected = elaborate notation ctx (Check expected) s
