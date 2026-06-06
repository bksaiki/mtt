(** [term_of_string s] parses and scope-checks the closed term [s]. Raises
    {!Lexer.Error}, {!Parser.Error}, or {!Ast.Unbound_variable}. *)
let term_of_string s =
  let lexbuf = Lexing.from_string s in
  Ast.to_term [] (Parser.main Lexer.token lexbuf)

(** [stmt_of_string s] parses [s] as a top-level statement. Scope checking
    happens later, against the names of the declarations already in scope.
    Raises {!Lexer.Error} or {!Parser.Error}. *)
let stmt_of_string s =
  let lexbuf = Lexing.from_string s in
  Parser.stmt Lexer.token lexbuf

(** [file_of_string s] parses [s] as a whole file: a sequence of declarations
    (bare terms are REPL-only). Raises {!Lexer.Error} or {!Parser.Error}. *)
let file_of_string s =
  let lexbuf = Lexing.from_string s in
  Parser.file Lexer.token lexbuf
