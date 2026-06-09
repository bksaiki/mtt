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
   scope-checks the parameter telescope and the result sort, then each
   constructor's declared type. A constructor type is decomposed as a Π-spine
   [(f₀ : F₀) -> ... -> T params]: the arguments become fields (a field is
   recursive when its type is exactly the inductive applied to the parameters),
   and the result must be the inductive applied to its parameters (no indices).
   The former is registered provisionally so constructor types can mention
   it. *)
let elaborate_inductive (sess : session) (d : ind_decl) : Inductive.spec =
  let sg = sess.ctx.Check.signature in
  let notation = sess.notation in
  (* parameter telescope: each type is scope-checked under the earlier params *)
  let params, param_names =
    List.fold_left
      (fun (params, names) (x, aty) ->
        (params @ [ (x, Ast.to_term sg ~notation names aty) ], x :: names))
      ([], []) d.iparams
  in
  let sort =
    match Ast.to_term sg ~notation param_names d.isort with
    | Type.Sort k -> k
    | _ ->
        Error.type_error
          [ Error.txt
              "the result of an inductive must be a sort (Type, Prop, or Type \
               n)"
          ]
  in
  (* the surface still declares only non-indexed types ([indices = []]); the
     kernel supports indexed families, but parsing an index telescope and the
     constructors' result indices is a later phase *)
  let provisional =
    { Inductive.name = d.iname; params; indices = []; sort; ctors = [] }
  in
  let sg = Signature.add provisional sg in
  let m = List.length params in
  (* a field/result at depth [d] is recursive iff it is the inductive applied to
     its parameters there *)
  let is_self depth ty = ty = Inductive.apply provisional depth in
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
              ( { Inductive.aname = x
                ; aty = a
                ; recursive =
                    (if is_self (m + j) a then
                       Some []
                     else
                       None)
                }
                :: fields
              , result )
          | result -> ([], result)
        in
        let fields, result =
          decompose 0 (Ast.to_term sg ~notation param_names cty)
        in
        if not (is_self (m + List.length fields) result) then
          Error.type_error
            [ Error.txtf
                "constructor %s must construct %s applied to its parameters"
                cname d.iname
            ];
        { Inductive.cname; fields; result_indices = [] })
      d.ictors
  in
  { Inductive.name = d.iname; params; indices = []; sort; ctors }

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
