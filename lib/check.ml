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
    - proof irrelevance: any two proofs of the same proposition (a type in Prop)
      are definitionally equal. This is why conversion is type-directed: [conv]
      compares values at a type and short-circuits when that type is a Prop,
      including for arguments inside neutral spines.

    Universes form a CoC-style Sort hierarchy: Prop = Sort 0 is impredicative,
    Type i = Sort (i+1) is the predicative tower above it. Pi formation lands in
    Sort (imax i j), where imax i 0 = 0: a product whose codomain is a
    proposition is itself a proposition, no matter how large the domain. Sorts
    are Russell-style and cumulative (Rocq-flavored, so Prop ≤ Type): in the
    subsumption rule the inferred type is compared with [sub] rather than
    [conv], where Sort i ≤ Sort j when i ≤ j and products are invariant in their
    domains and covariant in their codomains. [infer] still returns principal
    types: Sort i : Sort (i+1) exactly. *)

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

(* the type of a stuck neutral, reconstructed by walking the spine *)
let rec infer_neutral ctx (n : Value.neutral) : Value.t =
  match n with
  | Value.Var k -> List.nth ctx.types (ctx.lvl - k - 1)
  | Value.App (m, a) -> (
      match infer_neutral ctx m with
      | Value.Pi (_, _, c) -> Value.apply_closure c a
      | _ -> assert false (* values are well-typed by invariant *))

(* [sort_of ctx ty] is the i such that [ty : Sort i] *)
let rec sort_of ctx (ty : Value.t) : int =
  match ty with
  | Value.Sort i -> i + 1
  | Value.Pi (x, a, c) ->
      let j = sort_of (bind x a ctx) (Value.apply_closure c (fresh ctx)) in
      imax (sort_of ctx a) j
  | Value.Neutral n -> (
      match infer_neutral ctx n with
      | Value.Sort i -> i
      | _ -> assert false)
  | Value.Lam _ -> assert false (* a lambda is never a type *)

(** Type-directed conversion. [conv ctx ty v1 v2] decides definitional equality
    of the values [v1] and [v2] at the type [ty]; [conv_ty ~cumul] compares
    types themselves, up to cumulativity when [cumul] is set. β/δ have already
    happened during evaluation, so this is structural comparison of weak-head
    forms, going under binders with fresh variables, plus:

    - proof irrelevance: at a type in Prop, any two values are equal
    - η: at a Pi type, values are equal iff their applications to a fresh
      variable are (lambda annotations are never compared) *)
let rec conv ctx (ty : Value.t) v1 v2 =
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
  | _ -> None

(** [sub ctx t1 t2] is the cumulativity relation [t1] ≤ [t2] on types *)
let sub ctx t1 t2 = conv_ty ~cumul:true ctx t1 t2

(** [infer ctx t] synthesizes the type of [t] as a value, by the rules:

    {v
      (x : A) ∈ Γ
      ─────────── (Var)
       Γ ⊢ x : A

      ──────────────────────── (Sort)
      Γ ⊢ Sort i : Sort (i+1)

      Γ ⊢ A : Sort i    Γ, x : A ⊢ B : Sort j
      ──────────────────────────────────────── (Pi)
          Γ ⊢ (x : A) -> B : Sort (imax i j)

        where imax i 0 = 0 (Prop is impredicative)
        and   imax i j = max i j otherwise (the Type tower is predicative)

      Γ ⊢ A : Sort i    Γ, x : A ⊢ b : B
      ─────────────────────────────────── (Lam)
      Γ ⊢ fun (x : A) => b : (x : A) -> B

      Γ ⊢ f : (x : A) -> B    Γ ⊢ a : A
      ────────────────────────────────── (App)
              Γ ⊢ f a : B[a/x]
    v}

    In (App), the substitution [B[a/x]] is closure application. *)
let rec infer ctx (t : Type.t) : Value.t =
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
  (* (App) *)
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
  | Value.Sort i -> i
  | ty ->
      type_error "expected a type, but %s has type %s" (show_term ctx t)
        (show ctx ty)

(** [check ctx t expected] verifies that [t] has type [expected] *)
and check ctx (t : Type.t) (expected : Value.t) =
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
  (* subsumption: infer and compare up to βη-conversion and cumulativity *)
  | _ ->
      let ty = infer ctx t in
      if not (sub ctx ty expected) then
        type_error "this term has type %s but %s was expected" (show ctx ty)
          (show ctx expected)
