exception Type_error of string

let type_error fmt = Format.kasprintf (fun s -> raise (Type_error s)) fmt

type ctx =
  { env : Value.env (* values of bound variables, for evaluation *)
  ; types : Value.t list (* their types, index-aligned with [env] *)
  ; names : string list (* binder names, for error messages *)
  ; lvl : int (* binders in scope = next fresh de Bruijn level *)
  }

let empty = { env = []; types = []; names = []; lvl = 0 }

(* extends the context with a variable [x] of type [ty]; the variable is bound
   to a fresh neutral, so under the binder it blocks reduction instead of
   disappearing *)
let bind x ty ctx =
  { env = Value.Neutral (Value.Var ctx.lvl) :: ctx.env
  ; types = ty :: ctx.types
  ; names = x :: ctx.names
  ; lvl = ctx.lvl + 1
  }

(* extends the context with a *defined* variable [x] of type [ty]: bound to its
   value [v] rather than a neutral, so occurrences unfold during evaluation
   (δ-reduction) *)
let define x v ty ctx =
  { env = v :: ctx.env
  ; types = ty :: ctx.types
  ; names = x :: ctx.names
  ; lvl = ctx.lvl + 1
  }

(* renders values and terms with the context's binder names *)
let show ctx v = Type.to_string_in ctx.names (Value.quote ctx.lvl v)

let show_term ctx t = Type.to_string_in ctx.names t

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

(* the type of a NatRec step, Π (k : Nat) ⇒ P k → P (succ k): the motive [p] is
   quoted one binder deep for [P k] and two deep for [P (succ k)] (the weakening
   trick, as in branch_ty). The inner [P k] is the induction hypothesis. *)
let step_ty ctx p =
  let body =
    Type.Pi
      ( "_ih"
      , Type.App (Value.quote (ctx.lvl + 1) p, Type.Var 0)
      , Type.App (Value.quote (ctx.lvl + 2) p, Type.Succ (Type.Var 1)) )
  in
  Value.Pi ("k", Value.Nat, { env = ctx.env; body })

(* the type of a stuck neutral, reconstructed by walking the spine *)
let rec infer_neutral ctx (n : Value.neutral) : Value.t =
  match n with
  | Value.Var k -> List.nth ctx.types (ctx.lvl - k - 1)
  | Value.App (m, a) -> (
      match infer_neutral ctx m with
      | Value.Pi (_, _, c) -> Value.apply_closure c a
      | _ -> assert false (* values are well-typed by invariant *))
  | Value.Absurd (a, _) -> a (* the motive is the type *)
  | Value.Fst n -> (
      match infer_neutral ctx n with
      | Value.Sigma (_, a, _) -> a
      | _ -> assert false)
  | Value.Snd n -> (
      match infer_neutral ctx n with
      | Value.Sigma (_, _, c) ->
          Value.apply_closure c (Value.Neutral (Value.Fst n))
      | _ -> assert false)
  | Value.Case (p, n, _, _) -> Value.apply p (Value.Neutral n)
  (* J P d p : P y p; recover y from the stuck proof's type Eq A x y *)
  | Value.J (p, _, n) -> (
      match infer_neutral ctx n with
      | Value.Eq (_, _, y) -> motive_at p y (Value.Neutral n)
      | _ -> assert false)
  (* natrec P pz ps n : P n *)
  | Value.NatRec (p, _, _, n) -> Value.apply p (Value.Neutral n)

(* [sort_of ctx ty] is the i such that [ty : Sort i] *)
let rec sort_of ctx (ty : Value.t) : int =
  match ty with
  | Value.Sort i -> i + 1
  | Value.Pi (x, a, c) ->
      let j = sort_of (bind x a ctx) (Value.apply_closure c (fresh ctx)) in
      imax (sort_of ctx a) j
  | Value.Unit -> 1 (* Unit : Type *)
  | Value.Empty -> 0 (* Empty : Prop *)
  (* plain max, no imax: a Σ is a proposition only when both components are, so
     data can never hide inside a Prop *)
  | Value.Sigma (x, a, c) ->
      let j = sort_of (bind x a ctx) (Value.apply_closure c (fresh ctx)) in
      max (sort_of ctx a) j
  (* plain max, like sigma: a sum is a proposition only when both sides are *)
  | Value.Sum (a, b) -> max (sort_of ctx a) (sort_of ctx b)
  | Value.Eq _ -> 0 (* Eq : Prop *)
  | Value.Nat -> 1 (* Nat : Type *)
  | Value.Neutral n -> (
      match infer_neutral ctx n with
      | Value.Sort i -> i
      | _ -> assert false)
  | Value.Lam _
  | Value.MkUnit
  | Value.Pair _
  | Value.Inl _
  | Value.Inr _
  | Value.Refl
  | Value.Zero
  | Value.Succ _ ->
      assert false (* not types *)

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
  (* η for Unit: every element is (), so any two are equal *)
  | Value.Unit -> true
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
  (* Nat is positive: compare constructors structurally, no η *)
  | Value.Nat -> (
      match (v1, v2) with
      | Value.Zero, Value.Zero -> true
      | Value.Succ a, Value.Succ b -> conv ctx Value.Nat a b
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
  | Value.Unit, Value.Unit -> true
  | Value.Empty, Value.Empty -> true
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
  | Value.Nat, Value.Nat -> true
  | Value.Neutral n1, Value.Neutral n2 ->
      Option.is_some (conv_neutral ctx n1 n2)
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
  (* stuck recursion: scrutinees, then motives (extensionally), the base at P
     zero, and the step at its Π type *)
  | Value.NatRec (p1, z1, s1, n1), Value.NatRec (p2, z2, s2, n2) -> (
      match conv_neutral ctx n1 n2 with
      | Some Value.Nat ->
          if
            conv_ty ~cumul:false (bind "n" Value.Nat ctx)
              (Value.apply p1 (fresh ctx))
              (Value.apply p2 (fresh ctx))
            && conv ctx (Value.apply p1 Value.Zero) z1 z2
            && conv ctx (step_ty ctx p1) s1 s2
          then
            Some (Value.apply p1 (Value.Neutral n1))
          else
            None
      | _ -> None)
  (* stuck ex falso: the motives must agree; the proofs are of type Empty, a
     Prop, so by irrelevance they need not be compared at all *)
  | Value.Absurd (a1, _), Value.Absurd (a2, _) ->
      if conv_ty ~cumul:false ctx a1 a2 then
        Some a1
      else
        None
  | _ -> None

(* the cumulativity relation t1 ≤ t2 on types, used by subsumption *)
let sub ctx t1 t2 = conv_ty ~cumul:true ctx t1 t2

(* the rule markers below refer to the typing rules in check.mli's header *)
let rec infer ctx t =
  match t with
  | Type.Unit -> Value.Sort 1 (* (Unit): Unit : Type *)
  | Type.MkUnit -> Value.Unit (* (MkUnit) *)
  | Type.Empty -> Value.Sort 0 (* (Empty): Empty : Prop *)
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
  (* (App) *)
  | Type.App (f, a) -> (
      match infer ctx f with
      | Value.Pi (_, dom, c) ->
          check ctx a dom;
          Value.apply_closure c (Value.eval ctx.env a)
      | ty ->
          type_error "expected a function, but %s has type %s" (show_term ctx f)
            (show ctx ty))
  (* (Absurd): subsingleton elimination — the motive may live in any sort, even
     though Empty is a Prop, because Empty has no introduction forms *)
  | Type.Absurd (a, h) ->
      let _ = infer_univ ctx a in
      check ctx h Value.Empty;
      Value.eval ctx.env a
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
        "cannot infer the type of an injection: ascribe it, e.g. (inl a : A + \
         B)"
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
                    "the motive's domain %s does not match the scrutinee's \
                     type %s"
                    (show ctx dom) (show ctx sty);
                match Value.apply_closure c (fresh ctx) with
                | Value.Sort j -> j
                | cod ->
                    type_error "the motive must land in a sort, not %s"
                      (show (bind "s" sty ctx) cod))
            | ty ->
                type_error
                  "expected a motive from %s into a sort, but %s has type %s"
                  (show ctx sty) (show_term ctx p) (show ctx ty)
          in
          if sort_of ctx sty = 0 && j <> 0 then
            type_error
              "cannot eliminate a proof of %s into %s: a case on a proposition \
               must target Prop"
              (show ctx sty)
              (Type.to_string (Type.Sort j));
          let vp = Value.eval ctx.env p in
          check ctx u (branch_ty ctx vp "x" (fun t -> Type.Inl t) va);
          check ctx v (branch_ty ctx vp "y" (fun t -> Type.Inr t) vb);
          Value.apply vp (Value.eval ctx.env s)
      | ty ->
          type_error "expected a sum, but %s has type %s" (show_term ctx s)
            (show ctx ty))
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
          type_error "expected a pair, but %s has type %s" (show_term ctx p)
            (show ctx ty))
  (* (Snd): the result type instantiates the family at the first projection *)
  | Type.Snd p -> (
      match infer ctx p with
      | Value.Sigma (_, _, c) ->
          Value.apply_closure c (Value.vfst (Value.eval ctx.env p))
      | ty ->
          type_error "expected a pair, but %s has type %s" (show_term ctx p)
            (show ctx ty))
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
        "cannot infer the type of refl: ascribe it, e.g. (refl : Eq A x x)"
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
                  "the motive should take an endpoint of type %s, but takes %s"
                  (show ctx va) (show ctx dom1);
              let yv = fresh ctx in
              let ctx1 = bind "y" va ctx in
              match Value.apply_closure c1 yv with
              | Value.Pi (_, dom2, c2) -> (
                  let expected = Value.Eq (va, vx, yv) in
                  if not (conv_ty ~cumul:false ctx1 dom2 expected) then
                    type_error
                      "the motive should take a proof of %s, but takes %s"
                      (show ctx1 expected) (show ctx1 dom2);
                  match Value.apply_closure c2 (fresh ctx1) with
                  | Value.Sort _ -> ()
                  | cod ->
                      type_error "the motive must land in a sort, not %s"
                        (show ctx1 cod))
              | cod ->
                  type_error
                    "the motive must also take the equality proof, but its \
                     body is %s"
                    (show ctx1 cod))
          | ty ->
              type_error "expected a motive, but %s has type %s"
                (show_term ctx p) (show ctx ty));
          let vp = Value.eval ctx.env p in
          (* the diagonal proves P x refl *)
          check ctx d (motive_at vp vx Value.Refl);
          (* result: P y p *)
          motive_at vp vy (Value.eval ctx.env pr)
      | ty ->
          type_error "expected an equality proof, but %s has type %s"
            (show_term ctx pr) (show ctx ty))
  (* (Nat) *)
  | Type.Nat -> Value.Sort 1
  (* (Zero) / (Succ): the constructors; succ infers (its argument is Nat) *)
  | Type.Zero -> Value.Nat
  | Type.Succ n ->
      check ctx n Value.Nat;
      Value.Nat
  (* (NatRec): recursion. No large-elimination restriction — Nat is in Type, so
     there are no irrelevant proofs to protect; the motive may land in any
     sort. *)
  | Type.NatRec (p, z, s, n) ->
      check ctx n Value.Nat;
      (* validate the motive P : Nat → Sort *)
      (match infer ctx p with
      | Value.Pi (_, dom, c) -> (
          if not (conv_ty ~cumul:false ctx dom Value.Nat) then
            type_error "the motive should take a Nat, but takes %s"
              (show ctx dom);
          match Value.apply_closure c (fresh ctx) with
          | Value.Sort _ -> ()
          | cod ->
              type_error "the motive must land in a sort, not %s"
                (show (bind "n" Value.Nat ctx) cod))
      | ty ->
          type_error "expected a motive Nat → Sort, but %s has type %s"
            (show_term ctx p) (show ctx ty));
      let vp = Value.eval ctx.env p in
      (* base case proves P zero; step proves P k → P (succ k) *)
      check ctx z (Value.apply vp Value.Zero);
      check ctx s (step_ty ctx vp);
      Value.apply vp (Value.eval ctx.env n)

(* infers and requires a sort: used where the rules demand "a type" *)
and infer_univ ctx t =
  match infer ctx t with
  | Value.Sort i -> i
  | ty ->
      type_error "expected a type, but %s has type %s" (show_term ctx t)
        (show ctx ty)

and check ctx t expected =
  match (t, expected) with
  (* a lambda against a Pi: the annotation must match the domain, then the body
     is checked against the codomain at a fresh variable *)
  | Type.Lam (x, a, b), Value.Pi (_, dom, c) ->
      let _ = infer_univ ctx a in
      let va = Value.eval ctx.env a in
      if not (conv_ty ~cumul:false ctx va dom) then
        type_error "the annotation %s does not match the expected domain %s"
          (show ctx va) (show ctx dom);
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
        type_error "refl requires the sides to be equal, but %s is not %s"
          (show ctx vx) (show ctx vy)
  (* subsumption: infer and compare up to definitional equality (βδη plus proof
     irrelevance) and cumulativity *)
  | _ ->
      let ty = infer ctx t in
      if not (sub ctx ty expected) then
        type_error "this term has type %s but %s was expected" (show ctx ty)
          (show ctx expected)
