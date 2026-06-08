(** Entry points tying the lexer and parser together. All syntax failures —
    lexical or grammatical — are reported as {!Error} carrying the location of
    the offending token. *)

exception Error of Loc.t * string

(** [term_of_string s] parses and scope-checks the closed term [s]. Raises
    {!Error} or {!Ast.Unbound_variable}. *)
val term_of_string : string -> Type.t

(** [stmt_of_string s] parses [s] as a top-level statement (one REPL line).
    Scope checking happens later, against the names of the declarations already
    in scope. Raises {!Error}. *)
val stmt_of_string : string -> Stmt.t

(** [file_of_string ?fname s] parses [s] as a whole file: a sequence of
    declarations. [fname] is recorded in locations for error reporting. Raises
    {!Error}. *)
val file_of_string : ?fname:string -> string -> Stmt.t list
