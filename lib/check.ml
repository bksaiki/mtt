(** Bidirectional type checking: [infer] synthesizes a type, [check] verifies a
    term against one.

    Definitional equality (decided by [conv], on values) is βη-conversion:

    - β: (fun (x : A) => b) a ≡ b[a/x] Performed implicitly: terms are evaluated
      with {!Value.eval} before comparison, and β-redexes never survive
      evaluation (application of a closure extends its environment).
    - η: f ≡ fun (x : A) => f x (for f of Pi type) Performed in [conv] when a
      lambda meets a neutral: both sides are applied to a fresh variable and
      compared.

    - δ: a [def]ined name unfolds to its body. Performed eagerly: [define] binds
      the name directly to its evaluated value, so occurrences are replaced
      during evaluation. Axioms and theorems are [bind]ed to fresh neutrals
      instead — theorems are opaque: the proof is checked, then forgotten.

    Not included (yet): universe cumulativity (Type i is NOT a subtype of Type
    (i+1); universes are Russell-style and compared for exact equality). Pi is
    predicative: (x : A) -> B lands in Type (max i j). *)

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

(** [conv l v1 v2] decides definitional equality at level [l]. β has already
    happened during evaluation, so this is structural comparison of weak-head
    forms, going under binders with fresh variables, plus the η rule. *)
let rec conv l (v1 : Value.t) (v2 : Value.t) =
  match (v1, v2) with
  (* universes: exact equality (no cumulativity) *)
  | Value.Univ i, Value.Univ j -> i = j
  (* binders: compare domains, then compare codomains/bodies applied to the same
     fresh variable (names are display hints, ignored: α-equivalence) *)
  | Value.Pi (_, a1, c1), Value.Pi (_, a2, c2)
  | Value.Lam (_, a1, c1), Value.Lam (_, a2, c2) ->
      let x = Value.Neutral (Value.Var l) in
      conv l a1 a2
      && conv (l + 1) (Value.apply_closure c1 x) (Value.apply_closure c2 x)
  (* η: a lambda equals a neutral f if its body equals f x *)
  | Value.Lam (_, _, c), Value.Neutral n
  | Value.Neutral n, Value.Lam (_, _, c) ->
      let x = Value.Neutral (Value.Var l) in
      conv (l + 1) (Value.apply_closure c x) (Value.Neutral (Value.App (n, x)))
  | Value.Neutral n1, Value.Neutral n2 -> conv_neutral l n1 n2
  | _ -> false

and conv_neutral l n1 n2 =
  match (n1, n2) with
  | Value.Var k1, Value.Var k2 -> k1 = k2
  | Value.App (n1, a1), Value.App (n2, a2) ->
      conv_neutral l n1 n2 && conv l a1 a2
  | _ -> false

(** [infer ctx t] synthesizes the type of [t] as a value *)
let rec infer ctx (t : Type.term) : Value.t =
  match t with
  (* (x : A) ∈ Γ ──────────── (Var) Γ ⊢ x : A *)
  | Type.Var i -> List.nth ctx.types i
  (* ─────────────────────── (Univ) Γ ⊢ Type i : Type (i+1) *)
  | Type.Univ i -> Value.Univ (i + 1)
  (* Γ ⊢ A : Type i Γ, x : A ⊢ B : Type j
     ──────────────────────────────────────── (Pi, predicative) Γ ⊢ (x : A) -> B
     : Type (max i j) *)
  | Type.Pi (x, a, b) ->
      let i = infer_univ ctx a in
      let j = infer_univ (bind x (Value.eval ctx.env a) ctx) b in
      Value.Univ (max i j)
  (* Γ ⊢ A : Type i Γ, x : A ⊢ b : B ─────────────────────────────────── (Lam) Γ
     ⊢ fun (x : A) => b : (x : A) -> B *)
  | Type.Lam (x, a, b) ->
      let _ = infer_univ ctx a in
      let va = Value.eval ctx.env a in
      let vb = infer (bind x va ctx) b in
      (* [vb] is a value one binder deep; quote it back to syntax to form the
         codomain closure *)
      Value.Pi (x, va, { env = ctx.env; body = Value.quote (ctx.lvl + 1) vb })
  (* Γ ⊢ f : (x : A) -> B Γ ⊢ a : A ────────────────────────────────── (App) Γ ⊢
     f a : B[a/x] the substitution is closure application *)
  | Type.App (f, a) -> (
      match infer ctx f with
      | Value.Pi (_, dom, c) ->
          check ctx a dom;
          Value.apply_closure c (Value.eval ctx.env a)
      | ty ->
          type_error "expected a function, but %s has type %s" (show_term ctx f)
            (show ctx ty))

(* infers and requires a universe: used where the rules demand "a type" *)
and infer_univ ctx t =
  match infer ctx t with
  | Value.Univ i -> i
  | ty ->
      type_error "expected a type, but %s has type %s" (show_term ctx t)
        (show ctx ty)

(** [check ctx t expected] verifies that [t] has type [expected] *)
and check ctx (t : Type.term) (expected : Value.t) =
  match (t, expected) with
  (* a lambda against a Pi: the annotation must match the domain, then the body
     is checked against the codomain at a fresh variable *)
  | Type.Lam (x, a, b), Value.Pi (_, dom, c) ->
      let _ = infer_univ ctx a in
      let va = Value.eval ctx.env a in
      if not (conv ctx.lvl va dom) then
        type_error "the annotation %s does not match the expected domain %s"
          (show ctx va) (show ctx dom);
      check (bind x va ctx) b
        (Value.apply_closure c (Value.Neutral (Value.Var ctx.lvl)))
  (* subsumption: infer and compare up to βη-conversion *)
  | _ ->
      let ty = infer ctx t in
      if not (conv ctx.lvl ty expected) then
        type_error "this term has type %s but %s was expected" (show ctx ty)
          (show ctx expected)
