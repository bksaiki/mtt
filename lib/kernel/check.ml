(* An error message as renderable fragments: literal [Text], or a core [Term] to
   be rendered (with the binder names it is read against) by the frontend, which
   owns notation. The kernel formats no notation itself — it quotes the
   offending values to terms and lets the frontend delaborate them. *)
type frag =
  | Text of string
  | Term of string list * Type.t

exception Type_error of frag list

let type_error frags = raise (Type_error frags)

(* literal text; [txtf] is the printf-style variant for non-term parts (names,
   counts, sorts) that never carry notation *)
let txt s = Text s

let txtf fmt = Format.kasprintf (fun s -> Text s) fmt

type ctx =
  { env : Value.env (* values of bound variables, for evaluation *)
  ; types : Value.t list (* their types, index-aligned with [env] *)
  ; names : string list (* binder names, for error messages *)
  ; lvl : int (* binders in scope = next fresh de Bruijn level *)
  ; signature : Signature.t (* the inductive types declared so far *)
  ; notation : Type.notation (* display sugar, from @[notation ...] decls *)
  }

let empty =
  { env = []
  ; types = []
  ; names = []
  ; lvl = 0
  ; signature = Signature.empty
  ; notation = Type.no_notation
  }

(* extends the context with [x : ty] whose value is [v] *)
let extend x v ty ctx =
  { ctx with
    env = v :: ctx.env
  ; types = ty :: ctx.types
  ; names = x :: ctx.names
  ; lvl = ctx.lvl + 1
  }

(* a variable bound to a fresh neutral, so under the binder it blocks reduction
   instead of disappearing *)
let bind x ty ctx = extend x (Value.Neutral (Value.Var ctx.lvl)) ty ctx

(* a defined variable bound to its value, so occurrences unfold (δ-reduction) *)
let define = extend

(* registers an inductive declaration in the context's signature *)
let add_ind spec ctx = { ctx with signature = Signature.add spec ctx.signature }

(* Registers an inductive under a notation [role], after shape-checking that it
   can actually play that role. Notation is the frontend's, but the printer (and
   so the config) lives in the kernel, so this sets the context's display config
   from a [@[notation role]] declaration. One-shot: re-registering a role is an
   error. *)
let register_notation role spec ctx =
  match role with
  | "unit" ->
      if ctx.notation.Type.unit_ctor <> None then
        type_error [ txt "the unit notation is already registered" ];
      (match spec.Inductive.ctors with
      | [ { Inductive.fields = []; _ } ] when Inductive.nparams spec = 0 -> ()
      | _ ->
          type_error
            [ txt
                "@[notation unit] needs a parameterless inductive with a \
                 single nullary constructor"
            ]);
      { ctx with
        notation =
          { ctx.notation with
            Type.unit_ctor = Some (Inductive.ctor_head spec 0)
          }
      }
  | "nat" ->
      if ctx.notation.Type.nat <> None then
        type_error [ txt "the nat notation is already registered" ];
      (match spec.Inductive.ctors with
      | [ { Inductive.fields = []; _ }; { Inductive.fields = [ f ]; _ } ]
        when Inductive.nparams spec = 0 && f.Inductive.recursive ->
          ()
      | _ ->
          type_error
            [ txt
                "@[notation nat] needs a parameterless inductive with a \
                 nullary constructor then a single-recursive-field constructor"
            ]);
      { ctx with
        notation =
          { ctx.notation with
            Type.nat =
              Some (Inductive.ctor_head spec 0, Inductive.ctor_head spec 1)
          }
      }
  | _ ->
      type_error [ txtf "unknown notation role %s (expected: unit, nat)" role ]

(* the declared inductive [name], or a type error if it is unknown *)
let lookup_ind ctx name =
  match Signature.find ctx.signature name with
  | Some spec -> spec
  | None -> type_error [ txtf "unknown inductive type %s" name ]

(* renders values and terms with the context's binder names and notation; used
   by the frontend for [#check]/[#eval] output (error messages instead carry
   their terms, via [tm]/[vl], and are rendered by the frontend) *)
let show ctx v =
  Type.to_string_in ~notation:ctx.notation ctx.names (Value.quote ctx.lvl v)

let show_term ctx t = Type.to_string_in ~notation:ctx.notation ctx.names t

(* error fragments for a term and a value, capturing the binder names they are
   read against (the value is quoted now, with no notation; rendering is the
   frontend's, later) *)
let tm ctx (t : Type.t) = Term (ctx.names, t)

let vl ctx (v : Value.t) = Term (ctx.names, Value.quote ctx.lvl v)

(* imax i 0 = 0: a product into a proposition is a proposition *)
let imax i j =
  if j = 0 then
    0
  else
    max i j

(* the fresh variable for going under a binder *)
let fresh ctx = Value.Neutral (Value.Var ctx.lvl)

(* the type of a case branch, Π (x : comp) ⇒ P (inj x): the motive [p] is
   weakened by quoting one level up so it can sit under the branch's binder *)
let branch_ty ctx p x inj comp =
  let pq = Value.quote (ctx.lvl + 1) p in
  Value.Pi (x, comp, { env = ctx.env; body = Type.App (pq, inj (Type.Var 0)) })

(* a J motive [p] applied to an endpoint [y] and a proof [pr], i.e. [P y pr] *)
let motive_at p y pr = Value.apply (Value.apply p y) pr

(* builds a dependent function type [Π (name : aval) ⇒ B] as a value, where the
   codomain is computed by [k] given the extended context and the bound
   variable's value. The quote/eval round-trip handles the de Bruijn
   bookkeeping: applying the closure to an argument re-runs [k]'s result with
   the bound variable replaced by that argument. *)
let pi_val ctx name aval k =
  let ctx' = bind name aval ctx in
  let bval = k ctx' (fresh ctx) in
  Value.Pi (name, aval, { env = ctx.env; body = Value.quote ctx'.lvl bval })

(* The minor-premise type for the [i]-th constructor of [spec], given the
   recursor's parameter values [pvals] and motive value [pmot]:

   Π (f₀ : F₀) ⇒ [P f₀ ⇒] … Π (fₙ : Fₙ) ⇒ [P fₙ ⇒] P (c params fields)

   i.e. a binder per field, an induction hypothesis [P fⱼ] after each recursive
   field, concluding in the motive applied to the constructor. Field types come
   from the spec (in the context [params, earlier fields]) and are evaluated
   with the parameters and earlier fields substituted. *)
let minor_type ctx spec pvals pmot i =
  let c = List.nth spec.Inductive.ctors i in
  let chead = Inductive.ctor_head spec i in
  (* fieldvals is innermost-first; the spec field type is read in the context
     [params, earlier fields], so its env is [earlier fields (newest first)] ++
     [params (reverse)] *)
  let rec go ctx fieldvals = function
    | [] ->
        let ctor =
          List.fold_left Value.apply
            (Value.VCtor (chead, []))
            (pvals @ List.rev fieldvals)
        in
        Value.apply pmot ctor
    | (a : Inductive.arg) :: rest ->
        let aval = Value.eval (fieldvals @ List.rev pvals) a.aty in
        pi_val ctx a.aname aval (fun ctx' fv ->
            if a.recursive then
              pi_val ctx' "_ih" (Value.apply pmot fv) (fun ctx'' _ ->
                  go ctx'' (fv :: fieldvals) rest)
            else
              go ctx' (fv :: fieldvals) rest)
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
  | Value.App (m, a) -> (
      match infer_neutral ctx m with
      | Value.Pi (_, _, c) -> Value.apply_closure c a
      | _ -> assert false (* values are well-typed by invariant *))
  | Value.Fst n -> (
      match infer_neutral ctx n with
      | Value.Sigma (_, a, _) -> a
      | _ -> assert false)
  | Value.Snd n -> (
      match infer_neutral ctx n with
      | Value.Sigma (_, _, c) ->
          Value.apply_closure c (Value.Neutral (Value.Fst n))
      | _ -> assert false)
  | Value.Proj (i, n) -> (
      match infer_neutral ctx n with
      | Value.VInd (name, params) ->
          field_type (lookup_ind ctx name) params (Value.Neutral n) i
      | _ -> assert false)
  | Value.Case (p, n, _, _) -> Value.apply p (Value.Neutral n)
  (* J P d p : P y p; recover y from the stuck proof's type Eq A x y *)
  | Value.J (p, _, n) -> (
      match infer_neutral ctx n with
      | Value.Eq (_, _, y) -> motive_at p y (Value.Neutral n)
      | _ -> assert false)
  (* T.rec params P minors major : P major; the motive sits after the params in
     the recorded pre-major spine *)
  | Value.Rec (h, pre, n) ->
      let motive = List.nth pre h.Type.nparams in
      Value.apply motive (Value.Neutral n)

(* [sort_of ctx ty] is the i such that [ty : Sort i] *)
let rec sort_of ctx (ty : Value.t) : int =
  match ty with
  | Value.Sort i -> i + 1
  | Value.Pi (x, a, c) ->
      let j = sort_of (bind x a ctx) (Value.apply_closure c (fresh ctx)) in
      imax (sort_of ctx a) j
  (* plain max, no imax: a Σ is a proposition only when both components are, so
     data can never hide inside a Prop *)
  | Value.Sigma (x, a, c) ->
      let j = sort_of (bind x a ctx) (Value.apply_closure c (fresh ctx)) in
      max (sort_of ctx a) j
  (* plain max, like sigma: a sum is a proposition only when both sides are *)
  | Value.Sum (a, b) -> max (sort_of ctx a) (sort_of ctx b)
  | Value.Eq _ -> 0 (* Eq : Prop *)
  | Value.Neutral n -> (
      match infer_neutral ctx n with
      | Value.Sort i -> i
      | _ -> assert false)
  (* an inductive type lives at its declared sort *)
  | Value.VInd (name, _) -> (lookup_ind ctx name).Inductive.sort
  (* not types *)
  | Value.VCtor _
  | Value.VRec _
  | Value.Lam _
  | Value.Pair _
  | Value.Inl _
  | Value.Inr _
  | Value.Refl ->
      assert false

(* type-directed conversion: [conv] compares terms at a type, [conv_ty] compares
   types themselves (with optional cumulativity). β/δ have already happened
   during evaluation, so this is structural comparison of weak-head forms, going
   under binders with fresh variables. *)
let rec conv ctx ty v1 v2 =
  (* proof irrelevance *)
  sort_of ctx ty = 0
  ||
  match ty with
  (* η *)
  | Value.Pi (x, a, c) ->
      let v = fresh ctx in
      conv (bind x a ctx) (Value.apply_closure c v) (Value.apply v1 v)
        (Value.apply v2 v)
  (* at a sort, the values are types: compare strictly *)
  | Value.Sort _ -> conv_ty ~cumul:false ctx v1 v2
  (* η for pairs (surjective pairing): compare the projections, the second at
     the instantiated component type *)
  | Value.Sigma (_, a, c) ->
      let f1 = Value.vfst v1 in
      conv ctx a f1 (Value.vfst v2)
      && conv ctx (Value.apply_closure c f1) (Value.vsnd v1) (Value.vsnd v2)
  (* at a sum type there is no η: injections compare componentwise, and a stuck
     value equals nothing but another stuck value *)
  | Value.Sum (a, b) -> (
      match (v1, v2) with
      | Value.Inl x1, Value.Inl x2 -> conv ctx a x1 x2
      | Value.Inr y1, Value.Inr y2 -> conv ctx b y1 y2
      | Value.Neutral n1, Value.Neutral n2 ->
          Option.is_some (conv_neutral ctx n1 n2)
      | _ -> false)
  | Value.VInd (name, params) -> (
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

and conv_ty ~cumul ctx (t1 : Value.t) (t2 : Value.t) =
  match (t1, t2) with
  (* sorts: equal, or upward-included under cumulativity *)
  | Value.Sort i, Value.Sort j ->
      if cumul then
        i <= j
      else
        i = j
  (* pi: domains are invariant, codomains covariant *)
  | Value.Pi (x, a1, c1), Value.Pi (_, a2, c2) ->
      conv_ty ~cumul:false ctx a1 a2
      &&
      let v = fresh ctx in
      conv_ty ~cumul (bind x a1 ctx) (Value.apply_closure c1 v)
        (Value.apply_closure c2 v)
  (* sigma: unlike pi there is no contravariant position, so both components are
     covariant under cumulativity *)
  | Value.Sigma (x, a1, c1), Value.Sigma (_, a2, c2) ->
      conv_ty ~cumul ctx a1 a2
      &&
      let v = fresh ctx in
      conv_ty ~cumul (bind x a1 ctx) (Value.apply_closure c1 v)
        (Value.apply_closure c2 v)
  (* sum: covariant in both sides, like sigma *)
  | Value.Sum (a1, b1), Value.Sum (a2, b2) ->
      conv_ty ~cumul ctx a1 a2 && conv_ty ~cumul ctx b1 b2
  (* equality: invariant in the type, and the endpoints are compared at it.
     (Both are Prop, so cumulativity adds nothing.) *)
  | Value.Eq (a1, x1, y1), Value.Eq (a2, x2, y2) ->
      conv_ty ~cumul:false ctx a1 a2 && conv ctx a1 x1 x2 && conv ctx a1 y1 y2
  (* an inductive type former is invariant in its parameters: same name, and
     parameters convertible at their (instantiated) telescope types *)
  | Value.VInd (n1, ps1), Value.VInd (n2, ps2) ->
      String.equal n1 n2
      && conv_params ctx [] (lookup_ind ctx n1).Inductive.params ps1 ps2
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
      | Value.Pi (_, dom, c) ->
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
      | Some (Value.Pi (_, dom, c)) ->
          if conv ctx dom a1 a2 then
            Some (Value.apply_closure c a1)
          else
            None
      | _ -> None)
  | Value.Fst n1, Value.Fst n2 -> (
      match conv_neutral ctx n1 n2 with
      | Some (Value.Sigma (_, a, _)) -> Some a
      | _ -> None)
  | Value.Snd n1, Value.Snd n2 -> (
      match conv_neutral ctx n1 n2 with
      | Some (Value.Sigma (_, _, c)) ->
          Some (Value.apply_closure c (Value.Neutral (Value.Fst n1)))
      | _ -> None)
  | Value.Proj (i1, m1), Value.Proj (i2, m2) when i1 = i2 -> (
      match conv_neutral ctx m1 m2 with
      | Some (Value.VInd (name, params)) ->
          Some (field_type (lookup_ind ctx name) params (Value.Neutral m1) i1)
      | _ -> None)
  (* stuck cases: scrutinees, then motives (as type families at a fresh
     variable), then both branches at their Pi types built from the motive *)
  | Value.Case (p1, n1, u1, v1), Value.Case (p2, n2, u2, v2) -> (
      match conv_neutral ctx n1 n2 with
      | Some (Value.Sum (a, b) as sty) ->
          let motives_ok =
            conv_ty ~cumul:false (bind "s" sty ctx)
              (Value.apply p1 (fresh ctx))
              (Value.apply p2 (fresh ctx))
          in
          if
            motives_ok
            && conv ctx (branch_ty ctx p1 "x" (fun t -> Type.Inl t) a) u1 u2
            && conv ctx (branch_ty ctx p1 "y" (fun t -> Type.Inr t) b) v1 v2
          then
            Some (Value.apply p1 (Value.Neutral n1))
          else
            None
      | _ -> None)
  (* stuck J: the proofs are equality proofs (a Prop), so by irrelevance only
     their *types* must agree (giving equal endpoints); then compare motives
     extensionally and the diagonal cases *)
  | Value.J (p1, d1, n1), Value.J (p2, d2, n2) -> (
      match (infer_neutral ctx n1, infer_neutral ctx n2) with
      | (Value.Eq (a, x, y) as t1), t2 ->
          let yv = fresh ctx in
          let ctx1 = bind "y" a ctx in
          let pv = fresh ctx1 in
          let ctx2 = bind "p" (Value.Eq (a, x, yv)) ctx1 in
          if
            conv_ty ~cumul:false ctx t1 t2
            && conv_ty ~cumul:false ctx2 (motive_at p1 yv pv)
                 (motive_at p2 yv pv)
            && conv ctx (motive_at p1 x Value.Refl) d1 d2
          then
            Some (motive_at p1 y (Value.Neutral n1))
          else
            None
      | _ -> assert false)
  (* stuck inductive recursion: the recorded pre-major spine is [params @ motive
     :: minors], and each minor is compared at its derived minor-premise type *)
  | Value.Rec (h, pre1, n1), Value.Rec (h2, pre2, n2)
    when String.equal h.Type.rind h2.Type.rind ->
      let spec = lookup_ind ctx h.Type.rind in
      let m = h.Type.nparams in
      let params1 = List.take m pre1 and params2 = List.take m pre2 in
      let motive1 = List.nth pre1 m and motive2 = List.nth pre2 m in
      let minors1 = List.drop (m + 1) pre1
      and minors2 = List.drop (m + 1) pre2 in
      let ind_ty =
        List.fold_left Value.apply (Value.VInd (h.Type.rind, [])) params1
      in
      (* the major is compared *at the inductive type*, not structurally: a Prop
         scrutinee is a proof, so by irrelevance two stuck recursions on
         different proofs are equal (this is what subsumes [absurd]) *)
      let majors_ok = conv ctx ind_ty (Value.Neutral n1) (Value.Neutral n2) in
      let motives_ok =
        conv_ty ~cumul:false (bind "x" ind_ty ctx)
          (Value.apply motive1 (fresh ctx))
          (Value.apply motive2 (fresh ctx))
      in
      let minors_ok =
        List.for_all2
          (fun (i, mn1) mn2 ->
            conv ctx (minor_type ctx spec params1 motive1 i) mn1 mn2)
          (List.mapi (fun i mn -> (i, mn)) minors1)
          minors2
      in
      if
        conv_params ctx [] spec.Inductive.params params1 params2
        && majors_ok
        && motives_ok
        && minors_ok
      then
        Some (Value.apply motive1 (Value.Neutral n1))
      else
        None
  | _ -> None

(* the cumulativity relation t1 ≤ t2 on types, used by subsumption *)
let sub ctx t1 t2 = conv_ty ~cumul:true ctx t1 t2

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
            sort_of ctx (Value.eval env a.aty) = 0
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
  | Type.Sort i -> Value.Sort (i + 1) (* (Sort) *)
  (* (Pi) *)
  | Type.Pi (x, a, b) ->
      let i = infer_univ ctx a in
      let j = infer_univ (bind x (Value.eval ctx.env a) ctx) b in
      Value.Sort (imax i j)
  (* (Lam) *)
  | Type.Lam (x, a, b) ->
      let _ = infer_univ ctx a in
      let va = Value.eval ctx.env a in
      let vb = infer (bind x va ctx) b in
      (* [vb] is a value one binder deep; quote it back to syntax to form the
         codomain closure *)
      Value.Pi (x, va, { env = ctx.env; body = Value.quote (ctx.lvl + 1) vb })
  (* (App) — but a recursor is motive-polymorphic, so it has no type as a
     constant: a fully-applied recursor spine gets a bespoke rule (like NatRec),
     detected by peeling the application head *)
  | Type.App (f, a) -> (
      match spine t with
      | Type.Rec rh, args -> infer_rec ctx rh args
      | _ -> (
          match infer ctx f with
          | Value.Pi (_, dom, c) ->
              check ctx a dom;
              Value.apply_closure c (Value.eval ctx.env a)
          | ty ->
              type_error
                [ txt "expected a function, but "
                ; tm ctx f
                ; txt " has type "
                ; vl ctx ty
                ]))
  (* (Sum): plain max, like sigma *)
  | Type.Sum (a, b) ->
      let i = infer_univ ctx a in
      let j = infer_univ ctx b in
      Value.Sort (max i j)
  (* an injection does not determine the other side of its sum: inl/inr are
     checked, not inferred *)
  | Type.Inl _
  | Type.Inr _ ->
      type_error
        [ txt
            "cannot infer the type of an injection: ascribe it, e.g. (inl a : \
             A + B)"
        ]
  (* (Case): the recursor. The motive is a function from the scrutinee's type
     into a sort; each branch covers one injection. When the scrutinee is a
     proposition the motive must land in Prop: by proof irrelevance inl h ≡ inr
     h', so a Type-valued case could distinguish equal proofs — the
     large-elimination restriction. *)
  | Type.Case (p, s, u, v) -> (
      match infer ctx s with
      | Value.Sum (va, vb) as sty ->
          let j =
            match infer ctx p with
            | Value.Pi (_, dom, c) -> (
                if not (conv_ty ~cumul:false ctx dom sty) then
                  type_error
                    [ txt "the motive's domain "
                    ; vl ctx dom
                    ; txt " does not match the scrutinee's type "
                    ; vl ctx sty
                    ];
                match Value.apply_closure c (fresh ctx) with
                | Value.Sort j -> j
                | cod ->
                    type_error
                      [ txt "the motive must land in a sort, not "
                      ; vl (bind "s" sty ctx) cod
                      ])
            | ty ->
                type_error
                  [ txt "expected a motive from "
                  ; vl ctx sty
                  ; txt " into a sort, but "
                  ; tm ctx p
                  ; txt " has type "
                  ; vl ctx ty
                  ]
          in
          if sort_of ctx sty = 0 && j <> 0 then
            type_error
              [ txt "cannot eliminate a proof of "
              ; vl ctx sty
              ; txt " into "
              ; tm ctx (Type.Sort j)
              ; txt ": a case on a proposition must target Prop"
              ];
          let vp = Value.eval ctx.env p in
          check ctx u (branch_ty ctx vp "x" (fun t -> Type.Inl t) va);
          check ctx v (branch_ty ctx vp "y" (fun t -> Type.Inr t) vb);
          Value.apply vp (Value.eval ctx.env s)
      | ty ->
          type_error
            [ txt "expected a sum, but "
            ; tm ctx s
            ; txt " has type "
            ; vl ctx ty
            ])
  (* (Sigma): plain max — no imax, see sort_of *)
  | Type.Sigma (x, a, b) ->
      let i = infer_univ ctx a in
      let j = infer_univ (bind x (Value.eval ctx.env a) ctx) b in
      Value.Sort (max i j)
  (* (Pair-infer): a bare pair infers at the constant family — the components
     cannot determine a dependent one, so like Lean we default to (type of a) ×
     (type of b); dependent pairs arrive via checking. Quoting [tb] one level up
     weakens it across the closure's binder. *)
  | Type.Pair (a, b) ->
      let ta = infer ctx a in
      let tb = infer ctx b in
      Value.Sigma
        ("", ta, { env = ctx.env; body = Value.quote (ctx.lvl + 1) tb })
  (* (Fst) *)
  | Type.Fst p -> (
      match infer ctx p with
      | Value.Sigma (_, a, _) -> a
      | ty ->
          type_error
            [ txt "expected a pair, but "
            ; tm ctx p
            ; txt " has type "
            ; vl ctx ty
            ])
  (* (Snd): the result type instantiates the family at the first projection *)
  | Type.Snd p -> (
      match infer ctx p with
      | Value.Sigma (_, _, c) ->
          Value.apply_closure c (Value.vfst (Value.eval ctx.env p))
      | ty ->
          type_error
            [ txt "expected a pair, but "
            ; tm ctx p
            ; txt " has type "
            ; vl ctx ty
            ])
  (* (Proj): the i-th field of a record, at its dependent field type *)
  | Type.Proj (i, e) -> (
      match infer ctx e with
      | Value.VInd (name, params) ->
          let spec = lookup_ind ctx name in
          if not (Inductive.is_record spec) then
            type_error
              [ txtf "%s is not a record, so it has no field projections" name ];
          let nfields = List.length (List.nth spec.Inductive.ctors 0).fields in
          if i >= nfields then
            type_error [ txtf "%s has no field .%d" name (i + 1) ];
          field_type spec params (Value.eval ctx.env e) i
      | ty ->
          type_error
            [ txt "expected a record, but "
            ; tm ctx e
            ; txt " has type "
            ; vl ctx ty
            ])
  (* (Eq): propositional equality is a proposition *)
  | Type.Eq (a, x, y) ->
      let _ = infer_univ ctx a in
      let va = Value.eval ctx.env a in
      check ctx x va;
      check ctx y va;
      Value.Sort 0
  (* refl does not determine its endpoints: it is checked, not inferred *)
  | Type.Refl ->
      type_error
        [ txt
            "cannot infer the type of refl: ascribe it, e.g. (refl : Eq A x x)"
        ]
  (* (J): based path induction. The motive abstracts over the endpoint and the
     proof; the diagonal proves it for [refl]. No large-elimination restriction
     — Eq is a single-constructor subsingleton (like Empty), so eliminating into
     any sort is sound. *)
  | Type.J (p, d, pr) -> (
      match infer ctx pr with
      | Value.Eq (va, vx, vy) ->
          (* validate the motive P : Π (y : A) ⇒ Eq A x y → Sort *)
          (match infer ctx p with
          | Value.Pi (_, dom1, c1) -> (
              if not (conv_ty ~cumul:false ctx dom1 va) then
                type_error
                  [ txt "the motive should take an endpoint of type "
                  ; vl ctx va
                  ; txt ", but takes "
                  ; vl ctx dom1
                  ];
              let yv = fresh ctx in
              let ctx1 = bind "y" va ctx in
              match Value.apply_closure c1 yv with
              | Value.Pi (_, dom2, c2) -> (
                  let expected = Value.Eq (va, vx, yv) in
                  if not (conv_ty ~cumul:false ctx1 dom2 expected) then
                    type_error
                      [ txt "the motive should take a proof of "
                      ; vl ctx1 expected
                      ; txt ", but takes "
                      ; vl ctx1 dom2
                      ];
                  match Value.apply_closure c2 (fresh ctx1) with
                  | Value.Sort _ -> ()
                  | cod ->
                      type_error
                        [ txt "the motive must land in a sort, not "
                        ; vl ctx1 cod
                        ])
              | cod ->
                  type_error
                    [ txt
                        "the motive must also take the equality proof, but its \
                         body is "
                    ; vl ctx1 cod
                    ])
          | ty ->
              type_error
                [ txt "expected a motive, but "
                ; tm ctx p
                ; txt " has type "
                ; vl ctx ty
                ]);
          let vp = Value.eval ctx.env p in
          (* the diagonal proves P x refl *)
          check ctx d (motive_at vp vx Value.Refl);
          (* result: P y p *)
          motive_at vp vy (Value.eval ctx.env pr)
      | ty ->
          type_error
            [ txt "expected an equality proof, but "
            ; tm ctx pr
            ; txt " has type "
            ; vl ctx ty
            ])
  (* an inductive type former and its constructors have fixed (non-polymorphic)
     types derived from the declaration; they ride the normal (App) machinery *)
  | Type.Ind name -> Value.eval [] (Inductive.former_type (lookup_ind ctx name))
  | Type.Ctor h ->
      Value.eval [] (Inductive.ctor_type (lookup_ind ctx h.ind) h.cindex)
  (* a bare recursor is motive-polymorphic; only a saturated application (caught
     in (App)) can be typed *)
  | Type.Rec _ ->
      type_error
        [ txt
            "cannot infer the type of a bare recursor; apply it to its \
             parameters, motive, minor premises and target"
        ]

(* infers and requires a sort: used where the rules demand "a type" *)
and infer_univ ctx t =
  match infer ctx t with
  | Value.Sort i -> i
  | ty ->
      type_error
        [ txt "expected a type, but "; tm ctx t; txt " has type "; vl ctx ty ]

(* checks a parameter spine against the parameter telescope, returning the
   parameter values (so later parameter types and the motive can be
   instantiated) *)
and check_telescope ctx params tms =
  let rec go env params tms =
    match (params, tms) with
    | [], [] -> []
    | (_, pty) :: ps, tm :: rest ->
        check ctx tm (Value.eval env pty);
        let v = Value.eval ctx.env tm in
        v :: go (v :: env) ps rest
    | _ -> type_error [ txt "wrong number of parameters for the inductive" ]
  in
  go [] params tms

(* (Rec): the generic recursor. Generalizes (NatRec): the motive is [P : Ind
   params → Sort j]; each constructor contributes a minor premise (see
   {!minor_type}); the result is [P major]. Prop inductives that are not
   subsingletons are restricted to Prop-valued elimination (large-elimination
   restriction, generalizing the one on (Case)). *)
and infer_rec ctx rh args =
  let spec = lookup_ind ctx rh.Type.rind in
  let m = rh.Type.nparams in
  let nctors = List.length rh.Type.recs in
  let expected = m + 1 + nctors + 1 in
  if List.length args <> expected then
    type_error
      [ txtf "%s.rec expects %d arguments but got %d" rh.Type.rind expected
          (List.length args)
      ];
  let param_tms = List.take m args in
  let motive_tm = List.nth args m in
  let minor_tms = List.take nctors (List.drop (m + 1) args) in
  let major_tm = List.nth args (m + 1 + nctors) in
  (* parameters, then the target type they determine *)
  let pvals = check_telescope ctx spec.Inductive.params param_tms in
  let ind_ty =
    List.fold_left Value.apply (Value.VInd (rh.Type.rind, [])) pvals
  in
  (* the motive P : ind_ty → Sort j *)
  let pmot = Value.eval ctx.env motive_tm in
  let j =
    match infer ctx motive_tm with
    | Value.Pi (_, dom, c) -> (
        if not (conv_ty ~cumul:false ctx dom ind_ty) then
          type_error
            [ txt "the motive's domain "
            ; vl ctx dom
            ; txt " does not match the target type "
            ; vl ctx ind_ty
            ];
        match Value.apply_closure c (fresh ctx) with
        | Value.Sort j -> j
        | cod ->
            type_error
              [ txt "the motive must land in a sort, not "
              ; vl (bind "x" ind_ty ctx) cod
              ])
    | ty ->
        type_error
          [ txt "expected a motive from "
          ; vl ctx ind_ty
          ; txt " into a sort, but "
          ; tm ctx motive_tm
          ; txt " has type "
          ; vl ctx ty
          ]
  in
  if spec.Inductive.sort = 0 && j <> 0 && not (subsingleton ctx spec) then
    type_error
      [ txtf "cannot eliminate the proposition %s into " rh.Type.rind
      ; tm ctx (Type.Sort j)
      ; txt
          ": only a subsingleton (at most one constructor, all fields proofs) \
           may eliminate large"
      ];
  (* each minor premise against its derived type, then the target *)
  List.iteri
    (fun i mn -> check ctx mn (minor_type ctx spec pvals pmot i))
    minor_tms;
  check ctx major_tm ind_ty;
  Value.apply pmot (Value.eval ctx.env major_tm)

and check ctx t expected =
  match (t, expected) with
  (* a lambda against a Pi: the annotation must match the domain, then the body
     is checked against the codomain at a fresh variable *)
  | Type.Lam (x, a, b), Value.Pi (_, dom, c) ->
      let _ = infer_univ ctx a in
      let va = Value.eval ctx.env a in
      if not (conv_ty ~cumul:false ctx va dom) then
        type_error
          [ txt "the annotation "
          ; vl ctx va
          ; txt " does not match the expected domain "
          ; vl ctx dom
          ];
      check (bind x va ctx) b
        (Value.apply_closure c (Value.Neutral (Value.Var ctx.lvl)))
  (* (Inl)/(Inr): an injection checks against a sum *)
  | Type.Inl a, Value.Sum (va, _) -> check ctx a va
  | Type.Inr b, Value.Sum (_, vb) -> check ctx b vb
  (* (Pair): check the components, the second against the family instantiated at
     the first *)
  | Type.Pair (a, b), Value.Sigma (_, dom, c) ->
      check ctx a dom;
      check ctx b (Value.apply_closure c (Value.eval ctx.env a))
  (* (Refl): reflexivity proves x = y exactly when x ≡ y *)
  | Type.Refl, Value.Eq (va, vx, vy) ->
      if not (conv ctx va vx vy) then
        type_error
          [ txt "refl requires the sides to be equal, but "
          ; vl ctx vx
          ; txt " is not "
          ; vl ctx vy
          ]
  (* subsumption: infer and compare up to definitional equality (βδη plus proof
     irrelevance) and cumulativity *)
  | _ ->
      let ty = infer ctx t in
      if not (sub ctx ty expected) then
        type_error
          [ txt "this term has type "
          ; vl ctx ty
          ; txt " but "
          ; vl ctx expected
          ; txt " was expected"
          ]

(* Validates an inductive declaration: kind-checks the parameter telescope, then
   each constructor's field types in context. Enforces strict positivity (the
   inductive may appear only as a direct recursive field [Ind params], never
   elsewhere — under an arrow or nested) and predicativity (each field's sort
   fits the inductive's, unless it is a Prop, which is impredicative). The
   inductive is registered before checking constructors so their recursive
   occurrences resolve. *)
let check_inductive ctx spec =
  let name = spec.Inductive.name in
  let ctx = add_ind spec ctx in
  let ctx_p =
    List.fold_left
      (fun ctx (x, pty) ->
        let _ = infer_univ ctx pty in
        bind x (Value.eval ctx.env pty) ctx)
      ctx spec.Inductive.params
  in
  let m = Inductive.nparams spec in
  List.iter
    (fun (c : Inductive.ctor) ->
      ignore
        (List.fold_left
           (fun (ctx_cur, j) (a : Inductive.arg) ->
             let s = infer_univ ctx_cur a.aty in
             if a.recursive then
               begin if a.aty <> Inductive.apply spec (m + j) then
                 type_error
                   [ txtf "constructor %s: a recursive field must have type "
                       c.cname
                   ; tm ctx_cur (Inductive.apply spec (m + j))
                   ]
             end
             else if Inductive.occurs name a.aty then
               type_error
                 [ txtf
                     "constructor %s: %s may occur only as a direct recursive \
                      field, not inside "
                     c.cname name
                 ; tm ctx_cur a.aty
                 ; txt " (strict positivity)"
                 ];
             if spec.Inductive.sort <> 0 && s > spec.Inductive.sort then
               type_error
                 [ txtf "constructor %s: a field of sort " c.cname
                 ; tm ctx_cur (Type.Sort s)
                 ; txt " does not fit the inductive's sort "
                 ; tm ctx_cur (Type.Sort spec.Inductive.sort)
                 ];
             (bind a.aname (Value.eval ctx_cur.env a.aty) ctx_cur, j + 1))
           (ctx_p, 0) c.fields))
    spec.Inductive.ctors
