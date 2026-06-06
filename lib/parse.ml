let term_of_string s =
  let lexbuf = Lexing.from_string s in
  Ast.to_term [] (Parser.main Lexer.token lexbuf)

let stmt_of_string s =
  let lexbuf = Lexing.from_string s in
  Parser.stmt Lexer.token lexbuf

let file_of_string s =
  let lexbuf = Lexing.from_string s in
  Parser.file Lexer.token lexbuf
