(** Bidirectional type checking: {!infer} synthesizes a type, {!check} verifies
    a term against one.

    Definitional equality (decided by {!conv}, on values) is βδη-conversion plus
    proof irrelevance:

    - β: [(fun (x : A) => b) a ≡ b[a/x]]. Performed implicitly: terms are
      evaluated with {!Value.eval} before comparison, and β-redexes never
      survive evaluation (application of a closure extends its environment).
    - η: [f ≡ fun (x : A) => f x] for [f] of Pi type. At a Pi type, {!conv}
      compares both sides applied to a fresh variable.
    - δ: a [def]ined name unfolds to its body. Performed eagerly: {!extend}
      binds the name directly to its evaluated value, so occurrences are
      replaced during evaluation. Axioms and theorems are {!bind}ed to fresh
      neutrals instead — theorems are opaque: the proof is checked, then
      forgotten.
    - proof irrelevance: any two proofs of the same proposition (a type in Prop)
      are definitionally equal. This is why conversion is type-directed: {!conv}
      compares values at a type and short-circuits when that type is a Prop,
      including for arguments inside neutral spines.

    Universes form a CoC-style Sort hierarchy: Prop = Sort 0 is impredicative,
    Type i = Sort (i+1) is the predicative tower above it. Pi formation lands in
    Sort (imax i j), where imax i 0 = 0: a product whose codomain is a
    proposition is itself a proposition, no matter how large the domain. There
    is {e no} cumulativity (Lean's model, not Rocq's): a smaller universe is not
    a subtype of a larger one, and {!conv} compares sorts by level equality —
    code that needs to span universes is universe-polymorphic instead (a
    declaration may take level parameters; see {!Inductive.spec}'s [nlevels]).

    The typing rules ({!infer} synthesizes; {!check} adds subsumption, which —
    with no cumulativity — is just type conversion). Every datatype is a prelude
    inductive — the dependent pair (Σ/(a,b)/.1/.2), the binary sum, and
    propositional equality (Eq/refl/Eq.rec) included — reached through the
    generic inductive rules (former/constructor/ recursor) and, for records, the
    projection (Proj) shown here:

    {v
      (x : A) ∈ Γ
      ─────────── (Var)
       Γ ⊢ x : A

      ──────────────────────── (Sort)
      Γ ⊢ Sort i : Sort (i+1)

      Γ ⊢ e : T p̄    T a single-constructor inductive with fields F₀ … Fₙ
      ──────────────────────────────────────────────────────────────────── (Proj)
        Γ ⊢ e.(i+1) : Fᵢ[p̄, e.1 … e.i]   (earlier projections substituted)

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

(** the typing context: the local binders (index-aligned), plus the global
    inductive signature *)
type ctx =
  { env : Value.env  (** values of bound variables, for evaluation *)
  ; types : Value.t list  (** their types *)
  ; names : string list  (** binder names, for error messages *)
  ; lvl : int  (** binders in scope = next fresh de Bruijn level *)
  ; signature : Signature.t  (** the inductive types declared so far *)
  }

val empty : ctx

(** [bind x ty ctx] extends the context with a variable [x] of type [ty], bound
    to a fresh neutral so that under the binder it blocks reduction instead of
    disappearing *)
val bind : string -> Value.t -> ctx -> ctx

(** [extend x v ty ctx] extends the context with a variable [x] of type [ty]
    bound to the value [v] rather than a neutral, so occurrences unfold during
    evaluation (δ-reduction). This is how a [def] is added; {!bind} is the
    fresh-neutral counterpart. *)
val extend : string -> Value.t -> Value.t -> ctx -> ctx

(** [show ctx v] renders a value against the context's binder names, {e without}
    notation — the kernel's faithful/debug view. User-facing output and error
    messages are rendered by the frontend, which owns notation. *)
val show : ctx -> Value.t -> string

(** [vl ctx v] is an {!Error} fragment for a value, capturing the binder names
    it is read against (the value is quoted now, notation applied later by the
    frontend). Used by the driver to build [#check_equal] errors; the term
    counterpart [tm] stays internal to the checker. *)
val vl : ctx -> Value.t -> Error.frag

(** [conv ctx ty v1 v2] decides definitional equality of the values [v1] and
    [v2] at the type [ty], which both must inhabit. Type-directed: at a Prop,
    true by proof irrelevance; at a Pi, both sides are applied to a fresh
    variable (η, so lambda annotations are never compared); at a record
    (single-constructor) inductive by comparing field projections (η, surjective
    pairing — the dependent pair is one such record, and the 0-field case makes
    any two values equal); at a positive inductive (multi-constructor or
    recursive, like the sum or [Nat]), constructors compare componentwise and
    there is no η; at a sort, the values are types and are compared
    structurally. *)
val conv : ctx -> Value.t -> Value.t -> Value.t -> bool

(** [infer ctx t] synthesizes the type of [t] as a value, by the typing rules in
    the module header. *)
val infer : ctx -> Type.t -> Value.t

(** [infer_univ ctx t] infers and requires a sort, returning its level: used
    where the rules demand "a type" *)
val infer_univ : ctx -> Type.t -> Level.t

(** [check ctx t expected] verifies that [t] has type [expected]: a lambda
    against a Pi checks the annotation and descends into the body; anything else
    is inferred and compared to [expected] by conversion (subsumption — no
    cumulativity) *)
val check : ctx -> Type.t -> Value.t -> unit

(** [add_ind spec ctx] registers an inductive declaration in the context's
    signature, so its former, constructors and recursor can be referenced *)
val add_ind : Inductive.spec -> ctx -> ctx

(** [lookup_ind ctx name] is the inductive [name] declared in [ctx], or a type
    error if unknown. (Exposed for the elaborator's own type synthesis.) *)
val lookup_ind : ctx -> string -> Inductive.spec

(** [sort_of ctx ty] is the level [i] such that [ty : Sort i], for a [ty] known
    to be a type. (Exposed so the elaborator can compute the level arguments of
    a polymorphic inductive from its components' sorts.) *)
val sort_of : ctx -> Value.t -> Level.t

(** [field_type spec params v i] is the type of the [i]-th field of a record
    value [v : Ind params]: the field's declared type, instantiated by the
    parameters and by [v]'s earlier projections. (Exposed for the elaborator.)
*)
val field_type : Inductive.spec -> Value.t list -> Value.t -> int -> Value.t

(** [minor_type ctx spec pvals pmot i] is the type of the [i]-th constructor's
    minor premise in a recursor on [spec], given the parameter values [pvals]
    and motive value [pmot]. (Exposed so the elaborator can check a recursor's
    minor premises — e.g. a [refl] base case — in checking position.) *)
val minor_type :
     ?levels:Level.t list
  -> ctx
  -> Inductive.spec
  -> Value.t list
  -> Value.t
  -> int
  -> Value.t

(** [check_inductive ctx spec] validates an inductive declaration: kind-checks
    the parameter telescope and each constructor's field types, and enforces
    strict positivity (the inductive may appear only as a direct recursive
    field) and predicativity. Raises {!Error.Type_error} on an ill-formed
    declaration. Does not modify [ctx] — register the spec with {!add_ind}. *)
val check_inductive : ctx -> Inductive.spec -> unit
