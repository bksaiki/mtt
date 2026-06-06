(** Entry points tying the lexer and parser together. *)

(** [term_of_string s] parses and scope-checks the closed term [s]. Raises
    {!Lexer.Error}, [Parser.Error], or {!Ast.Unbound_variable}. *)
val term_of_string : string -> Type.t

(** [stmt_of_string s] parses [s] as a top-level statement (one REPL line).
    Scope checking happens later, against the names of the declarations already
    in scope. Raises {!Lexer.Error} or [Parser.Error]. *)
val stmt_of_string : string -> Stmt.t

(** [file_of_string s] parses [s] as a whole file: a sequence of declarations
    (bare terms are REPL-only). Raises {!Lexer.Error} or [Parser.Error]. *)
val file_of_string : string -> Stmt.t list
