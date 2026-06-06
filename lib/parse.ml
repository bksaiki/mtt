(** [term_of_string s] parses and scope-checks [s] into a term. Raises
    {!Lexer.Error}, {!Parser.Error}, or {!Ast.Unbound_variable}. *)
let term_of_string s =
  let lexbuf = Lexing.from_string s in
  Ast.to_term (Parser.main Lexer.token lexbuf)
