type desc =
  | Expr of Ast.t (* a bare term: type-checked, no output *)
  | Check of Ast.t (* #check t: reports the normal form and type *)
  | Eval of Ast.t (* #eval t: reports the normal form *)
  | Axiom of string * Ast.t (* axiom x : A *)
  | Def of string * Ast.t option * Ast.t (* def x [: A] = t, transparent *)
  | Theorem of string * Ast.t * Ast.t (* theorem x : A = t, opaque *)
  | CheckEqual of Ast.t * Ast.t (* #check_equal t u *)
  | Prelude (* opt out of the auto-loaded prelude (handled by the driver) *)

type t =
  { loc : Loc.t
  ; desc : desc
  }

let run (ctx : Check.ctx) stmt =
  (* scope-check and evaluate an annotation, requiring it to be a type *)
  let eval_ann sa =
    let a = Ast.to_term ctx.names sa in
    let _ = Check.infer_univ ctx a in
    Value.eval ctx.env a
  in
  match stmt.desc with
  | Expr s ->
      let t = Ast.to_term ctx.names s in
      let _ = Check.infer ctx t in
      (ctx, None)
  | Check s ->
      let t = Ast.to_term ctx.names s in
      let ty = Check.infer ctx t in
      let nf = Value.quote ctx.lvl (Value.eval ctx.env t) in
      ( ctx
      , Some
          (Printf.sprintf "%s : %s" (Check.show_term ctx nf) (Check.show ctx ty))
      )
  | Eval s ->
      let t = Ast.to_term ctx.names s in
      (* still type-checked first: evaluation of ill-typed terms can get stuck
         on a non-function *)
      let _ = Check.infer ctx t in
      let nf = Value.quote ctx.lvl (Value.eval ctx.env t) in
      (ctx, Some (Check.show_term ctx nf))
  | Axiom (x, sa) ->
      let va = eval_ann sa in
      (Check.bind x va ctx, None)
  | Def (x, sa, st) ->
      let t = Ast.to_term ctx.names st in
      let va =
        match sa with
        | Some sa ->
            let va = eval_ann sa in
            Check.check ctx t va;
            va
        | None -> Check.infer ctx t
      in
      let v = Value.eval ctx.env t in
      (Check.define x v va ctx, None)
  | Theorem (x, sa, st) ->
      let va = eval_ann sa in
      Check.check ctx (Ast.to_term ctx.names st) va;
      (* opaque: the proof is checked, then forgotten *)
      (Check.bind x va ctx, None)
  | CheckEqual (st, su) ->
      let t = Ast.to_term ctx.names st in
      let u = Ast.to_term ctx.names su in
      (* definitional equality is typed: both sides at the same type *)
      let ty = Check.infer ctx t in
      Check.check ctx u ty;
      let vt = Value.eval ctx.env t in
      let vu = Value.eval ctx.env u in
      if not (Check.conv ctx ty vt vu) then
        Check.type_error "#check_equal failed: %s is not convertible with %s"
          (Check.show ctx vt) (Check.show ctx vu);
      (ctx, None)
  (* the prelude directive only controls the driver's choice of starting context
     (auto-load vs. bare); it is handled there, so by the time a statement
     reaches [run] it is a no-op *)
  | Prelude -> (ctx, None)
