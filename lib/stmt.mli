(** Top-level statements: declarations, or a bare term to evaluate. A program is
    a telescope of declarations, each scoping over the rest, so processing a
    statement just extends the checking context:

    - [axiom x : A] — binds [x] to a fresh neutral (a stuck constant)
    - [def x [: A] = t] — binds [x] to the value of [t]; occurrences unfold
      (δ-reduction). The annotation may be omitted and inferred.
    - [theorem x : A = t] — checks the proof [t], then binds [x] like an axiom:
      theorems are opaque and never unfold.
    - [#check t] — type checks and normalizes [t], reporting [nf : type]; with
      an ascription, [#check (t : A)] asserts that [t] checks against [A]
    - [#eval t] — type checks and normalizes [t], reporting just [nf]
    - [#check_equal t u] — asserts that [t] and [u] are definitionally equal

    Only [#check] and [#eval] produce output; a bare term is checked silently,
    and [#check_equal] succeeds silently or fails with a type error. *)

type desc =
  | Expr of Ast.t  (** a bare term: type-checked, no output *)
  | Check of Ast.t  (** [#check t]: reports the normal form and type *)
  | Eval of Ast.t  (** [#eval t]: reports the normal form *)
  | Axiom of string * Ast.t  (** [axiom x : A] *)
  | Def of string * Ast.t option * Ast.t  (** [def x [: A] = t], transparent *)
  | Theorem of string * Ast.t * Ast.t  (** [theorem x : A = t], opaque *)
  | CheckEqual of Ast.t * Ast.t  (** [#check_equal t u] *)
  | Prelude
      (** the [prelude] directive: opt out of the auto-loaded standard prelude
          (the file is prelude-level / wants a bare environment). Must be the
          first statement. The driver acts on it when choosing the starting
          context — [Stmt] cannot reach {!Prelude} without a cycle — so {!run}
          treats it as a no-op. *)

(** a statement with the source location of the whole declaration, for
    statement-level error reporting (type errors carry no finer position: the
    core language is location-free) *)
type t =
  { loc : Loc.t
  ; desc : desc
  }

(** [run ctx stmt] processes one statement, returning the extended context and
    an output message, if the statement produces one. Raises
    {!Ast.Unbound_variable} or {!Check.Type_error}. *)
val run : Check.ctx -> t -> Check.ctx * string option
