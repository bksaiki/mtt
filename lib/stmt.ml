(* the surface form of an inductive declaration, before elaboration into an
   {!Inductive.spec}: names and types are still parameters/terms *)
type ind_decl =
  { iname : string (* the inductive's name *)
  ; iparams : (string * Ast.t) list (* the parameter telescope (flattened) *)
  ; isort : Ast.t (* the result sort *)
  ; ictors :
      (string * Ast.t) list (* each constructor's name and declared type *)
  ; iattr : (string * string) option (* an attribute, e.g. @[notation unit] *)
  }

type desc =
  | Check of Ast.t (* #check t: reports the normal form and type *)
  | Eval of Ast.t (* #eval t: reports the normal form *)
  | Axiom of string * Ast.t (* axiom x : A *)
  | Def of string * Ast.t option * Ast.t (* def x [: A] = t, transparent *)
  | Theorem of string * Ast.t * Ast.t (* theorem x : A = t, opaque *)
  | CheckEqual of Ast.t * Ast.t (* #check_equal t u *)
  | Inductive of ind_decl (* inductive T params : sort := | c : ty | ... *)
  | Prelude (* opt out of the auto-loaded prelude (handled by the driver) *)

type t =
  { loc : Loc.t
  ; desc : desc
  }

(* the evolving frontend state as statements are processed: the kernel checking
   context plus the notation registry (which the kernel no longer holds) *)
type session =
  { ctx : Check.ctx
  ; notation : Notation.t
  }

let initial = { ctx = Check.empty; notation = Notation.empty }

(* Elaborates a surface inductive declaration into an {!Inductive.spec}:
   scope-checks the parameter telescope, then the result — an index telescope
   ending in a sort, [(i : I) -> … -> Sort] — then each constructor's declared
   type. A constructor type is a Π-spine [(f₀ : F₀) -> … -> T params idxs]: the
   arguments become fields (a field is recursive when its type is [T] applied to
   the parameters and some indices), and the result must be [T] applied to its
   parameters and the constructor's index instances. The former is registered
   provisionally so constructor types can mention it. *)
let elaborate_inductive (sess : session) (d : ind_decl) : Inductive.spec =
  let sg = sess.ctx.Check.signature in
  let notation = sess.notation in
  (* universe level parameters are auto-bound (Lean-style): the free level
     variables occurring in [Sort u] across the declaration's types, in order of
     first appearance, become its level parameters — in scope for every type *)
  let levels =
    let terms = List.map snd d.iparams @ (d.isort :: List.map snd d.ictors) in
    List.fold_left
      (fun acc t ->
        acc @ List.filter (fun x -> not (List.mem x acc)) (Ast.level_vars t))
      [] terms
  in
  let nlevels = List.length levels in
  (* the spec's parameter/index/field types use de Bruijn relative to the
     parameter telescope alone, with only the parameters and other inductives in
     scope (not the ambient definitions). They are therefore elaborated in a
     bare context carrying just the inductive signature. [Elab] in inference
     position resolves names the right way for this: a bare name is a parameter
     binder, else an inductive former — never an ambient definition. *)
  let base sg = { Check.empty with Check.signature = sg } in
  (* parameter telescope: each type is elaborated under the earlier params *)
  let params, pctx =
    List.fold_left
      (fun (params, ctx) (x, aty) ->
        let a = Elab.infer ~levels notation ctx aty in
        (params @ [ (x, a) ], Check.bind x (Value.eval ctx.Check.env a) ctx))
      ([], base sg)
      d.iparams
  in
  (* the result is an index telescope ending in a sort; the Π binders the
     surface arrow introduces are the indices, elaborated under the
     parameters *)
  let indices, sort =
    let rec decompose = function
      | Type.Pi (_, x, a, b) ->
          let idxs, k = decompose b in
          ((x, a) :: idxs, k)
      | Type.Sort k -> ([], k)
      | _ ->
          Error.type_error
            [ Error.txt
                "an inductive's result must be a sort (Type, Prop, Type n), \
                 optionally after an index telescope (e.g. Nat -> Type)"
            ]
    in
    decompose (Elab.infer ~levels notation pctx d.isort)
  in
  let provisional =
    { Inductive.name = d.iname; nlevels; params; indices; sort; ctors = [] }
  in
  let sg = Signature.add provisional sg in
  (* constructor types may mention the inductive being defined, so they see the
     provisional former; the parameter binders are unchanged *)
  let cctx = { pctx with Check.signature = sg } in
  let m = List.length params in
  (* [as_self depth ty]: if [ty] is this inductive applied to the parameter
     variables (read at [depth]) and then index instances, those instances; else
     [None]. Used both to flag a recursive field and to read a constructor's
     result indices. (A field that mentions the inductive but not in this shape
     is left non-recursive and rejected later by the kernel's positivity
     gate.) *)
  let as_self depth ty =
    let rec peel acc = function
      | Type.App (f, a) -> peel (a :: acc) f
      | Type.Ind (n, _) when String.equal n d.iname -> Some acc
      | _ -> None
    in
    match peel [] ty with
    | Some args when List.length args >= m ->
        let pvars = List.filteri (fun i _ -> i < m) args in
        let expected = List.init m (fun j -> Type.Var (depth - 1 - j)) in
        if pvars = expected then
          Some (List.filteri (fun i _ -> i >= m) args)
        else
          None
    | _ -> None
  in
  let ctors =
    List.map
      (fun (cname, cty) ->
        if String.equal cname "rec" then
          Error.type_error
            [ Error.txt
                "a constructor may not be named 'rec' (reserved for the \
                 recursor T.rec)"
            ];
        let rec decompose j ty =
          match (ty : Type.t) with
          | Pi (_, x, a, b) ->
              let fields, result = decompose (j + 1) b in
              ( { Inductive.aname = x; aty = a; recursive = as_self (m + j) a }
                :: fields
              , result )
          | result -> ([], result)
        in
        let fields, result =
          decompose 0 (Elab.infer ~levels notation cctx cty)
        in
        match as_self (m + List.length fields) result with
        | Some result_indices -> { Inductive.cname; fields; result_indices }
        | None ->
            Error.type_error
              [ Error.txtf
                  "constructor %s must construct %s applied to its parameters \
                   and indices"
                  cname d.iname
              ])
      d.ictors
  in
  { Inductive.name = d.iname; nlevels; params; indices; sort; ctors }

let run (sess : session) stmt =
  let ctx = sess.ctx in
  let notation = sess.notation in
  (* elaborate (surface → explicit core) then have the kernel re-check: the
     elaborator is untrusted, so [Check] stays the sole authority. [Elab] solves
     and zonks metavariables internally, so the core handed to the kernel is
     meta-free (an unsolvable hole is reported there). *)
  let infer s = Elab.infer notation ctx s in
  let check_against s va =
    let t = Elab.check notation ctx s va in
    Check.check ctx t va;
    t
  in
  (* elaborate and evaluate an annotation, requiring it to be a type *)
  let eval_ann sa =
    let a = infer sa in
    let _ = Check.infer_univ ctx a in
    Value.eval ctx.env a
  in
  match stmt.desc with
  | Check s ->
      let t = infer s in
      let ty = Check.infer ctx t in
      let nf = Value.quote ctx.lvl (Value.eval ctx.env t) in
      ( sess
      , Some
          (Printf.sprintf "%s : %s"
             (Notation.show_term notation ctx.names nf)
             (Notation.show notation ctx.names ctx.lvl ty)) )
  | Eval s ->
      let t = infer s in
      (* still type-checked first: evaluation of ill-typed terms can get stuck
         on a non-function *)
      let _ = Check.infer ctx t in
      let nf = Value.quote ctx.lvl (Value.eval ctx.env t) in
      (sess, Some (Notation.show_term notation ctx.names nf))
  | Axiom (x, sa) ->
      let va = eval_ann sa in
      ({ sess with ctx = Check.bind x va ctx }, None)
  | Def (x, sa, st) ->
      (* universe level parameters are auto-bound (as for inductives): the free
         level variables in the def's annotation and body, in first-appearance
         order, become its level parameters *)
      let levels =
        List.fold_left
          (fun acc t ->
            acc @ List.filter (fun y -> not (List.mem y acc)) (Ast.level_vars t))
          []
          (Option.to_list sa @ [ st ])
      in
      let nlevels = List.length levels in
      if nlevels = 0 then begin
        let t, va =
          match sa with
          | Some sa ->
              let va = eval_ann sa in
              (check_against st va, va)
          | None ->
              let t = infer st in
              (t, Check.infer ctx t)
        in
        let v = Value.eval ctx.env t in
        ({ sess with ctx = Check.extend x v va ctx }, None)
      end else begin
        (* universe-polymorphic def: elaborate the type and body with the level
           parameters in scope (so [Sort u] becomes [Sort (Var i)]) and store
           them level-abstracted; each use instantiates them
           ([Check.extend_poly] / the [Type.Def] reference) *)
          let body, ty =
            match sa with
            | Some sa ->
                let a = Elab.infer ~levels notation ctx sa in
                let _ = Check.infer_univ ctx a in
                let va = Value.eval ctx.env a in
                let t = Elab.check ~levels notation ctx st va in
                Check.check ctx t va;
                (t, a)
            | None ->
                let t = Elab.infer ~levels notation ctx st in
                (t, Value.quote ctx.lvl (Check.infer ctx t))
          in
          ({ sess with ctx = Check.extend_poly x ~nlevels ~body ~ty ctx }, None)
      end
  | Theorem (x, sa, st) ->
      let va = eval_ann sa in
      let _ = check_against st va in
      (* opaque: the proof is checked, then forgotten *)
      ({ sess with ctx = Check.bind x va ctx }, None)
  | CheckEqual (st, su) ->
      let t = infer st in
      (* definitional equality is typed: both sides at the same type *)
      let ty = Check.infer ctx t in
      let u = check_against su ty in
      let vt = Value.eval ctx.env t in
      let vu = Value.eval ctx.env u in
      if not (Check.conv ctx ty vt vu) then
        Error.type_error
          [ Error.txt "#check_equal failed: "
          ; Check.vl ctx vt
          ; Error.txt " is not convertible with "
          ; Check.vl ctx vu
          ];
      (sess, None)
  | Inductive d ->
      let spec = elaborate_inductive sess d in
      Check.check_inductive ctx spec;
      let ctx = Check.add_ind spec ctx in
      let notation =
        match d.iattr with
        | None -> notation
        | Some ("notation", role) -> Notation.register role spec notation
        | Some (name, _) ->
            Error.type_error [ Error.txtf "unknown attribute @@[%s ...]" name ]
      in
      ({ ctx; notation }, None)
  (* the prelude directive only controls the driver's choice of starting context
     (auto-load vs. bare); it is handled there, so by the time a statement
     reaches [run] it is a no-op *)
  | Prelude -> (sess, None)
