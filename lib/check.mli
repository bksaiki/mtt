(** Bidirectional type checking: {!infer} synthesizes a type, {!check} verifies
    a term against one.

    Definitional equality (decided by {!conv}, on values) is βδη-conversion plus
    proof irrelevance:

    - β: [(fun (x : A) => b) a ≡ b[a/x]]. Performed implicitly: terms are
      evaluated with {!Value.eval} before comparison, and β-redexes never
      survive evaluation (application of a closure extends its environment).
    - η: [f ≡ fun (x : A) => f x] for [f] of Pi type. At a Pi type, {!conv}
      compares both sides applied to a fresh variable.
    - δ: a [def]ined name unfolds to its body. Performed eagerly: {!define}
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
    proposition is itself a proposition, no matter how large the domain. Sorts
    are Russell-style and cumulative (Rocq-flavored, so Prop ≤ Type): in the
    subsumption rule the inferred type is compared up to Sort i ≤ Sort j when i
    ≤ j, with products invariant in their domains and covariant in their
    codomains. {!infer} still returns principal types: Sort i : Sort (i+1)
    exactly. *)

exception Type_error of string

(** [type_error fmt ...] raises {!Type_error} with a formatted message *)
val type_error : ('a, Format.formatter, unit, 'b) format4 -> 'a

(** the typing context: one entry per binder in scope, all index-aligned *)
type ctx =
  { env : Value.env  (** values of bound variables, for evaluation *)
  ; types : Value.t list  (** their types *)
  ; names : string list  (** binder names, for error messages *)
  ; lvl : int  (** binders in scope = next fresh de Bruijn level *)
  }

val empty : ctx

(** [bind x ty ctx] extends the context with a variable [x] of type [ty], bound
    to a fresh neutral so that under the binder it blocks reduction instead of
    disappearing *)
val bind : string -> Value.t -> ctx -> ctx

(** [define x v ty ctx] extends the context with a {e defined} variable [x] of
    type [ty]: bound to its value [v] rather than a neutral, so occurrences
    unfold during evaluation (δ-reduction) *)
val define : string -> Value.t -> Value.t -> ctx -> ctx

(** [show ctx v] renders a value with the context's binder names *)
val show : ctx -> Value.t -> string

(** [show_term ctx t] renders a term with the context's binder names *)
val show_term : ctx -> Type.t -> string

(** [conv ctx ty v1 v2] decides definitional equality of the values [v1] and
    [v2] at the type [ty], which both must inhabit. Type-directed: at a Prop,
    true by proof irrelevance; at a Pi, both sides are applied to a fresh
    variable (η, so lambda annotations are never compared); at [Unit], true (η:
    every element is [tt]); at a sort, the values are types and are compared
    structurally. *)
val conv : ctx -> Value.t -> Value.t -> Value.t -> bool

(** [infer ctx t] synthesizes the type of [t] as a value, by the rules:

    {v
      (x : A) ∈ Γ
      ─────────── (Var)
       Γ ⊢ x : A

      ──────────────────────── (Sort)
      Γ ⊢ Sort i : Sort (i+1)

      ─────────────── (Unit)      ───────────── (MkUnit)
      Γ ⊢ Unit : Type             Γ ⊢ () : Unit

      ──────────────── (Empty)
      Γ ⊢ Empty : Prop

      Γ ⊢ A : Sort i    Γ ⊢ h : Empty
      ───────────────────────────────── (Absurd)
            Γ ⊢ absurd A h : A

        ex falso at any sort: subsingleton elimination, sound because
        Empty has no introduction forms

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
val infer : ctx -> Type.t -> Value.t

(** [infer_univ ctx t] infers and requires a sort, returning its index: used
    where the rules demand "a type" *)
val infer_univ : ctx -> Type.t -> int

(** [check ctx t expected] verifies that [t] has type [expected]: a lambda
    against a Pi checks the annotation and descends into the body; anything else
    is inferred and compared up to cumulativity (subsumption) *)
val check : ctx -> Type.t -> Value.t -> unit
