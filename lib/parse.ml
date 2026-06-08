exception Error of Loc.t * string

(* run [k] on a fresh lexbuf for [s], converting lexer/parser failures into
   [Error] at the offending token's location *)
let with_lexbuf ?(fname = "") s k =
  let lexbuf = Lexing.from_string s in
  Lexing.set_filename lexbuf fname;
  let loc () = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
  try k lexbuf with
  | Lexer.Error msg -> raise (Error (loc (), msg))
  | Parser.Error -> raise (Error (loc (), "unexpected token"))

let term_of_string s =
  with_lexbuf s (fun lexbuf ->
      Ast.to_term Signature.empty [] (Parser.main Lexer.token lexbuf))

let stmt_of_string s = with_lexbuf s (Parser.stmt Lexer.token)

let file_of_string ?fname s = with_lexbuf ?fname s (Parser.file Lexer.token)
