{
open Parser

exception Error of string
}

let whitespace = [' ' '\t' '\r' '\n']+
let digits = ['0'-'9']+
let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

(* unicode alternatives are matched as literal UTF-8 byte sequences *)
rule token = parse
  | whitespace { token lexbuf }
  | "--" [^ '\n']* { token lexbuf }
  | "fun" { FUN }
  | "λ" { FUN }
  | "Π" { PI }
  | "∏" { PI }
  | "Type" { TYPE }
  | "#check" { CHECK }
  | "#check_equal" { CHECK_EQUAL }
  | "#eval" { EVAL }
  | "axiom" { AXIOM }
  | "def" { DEF }
  | "theorem" { THEOREM }
  | "lemma" { THEOREM }
  | "->" { ARROW }
  | "→" { ARROW }
  | "=>" { DARROW }
  | "⇒" { DARROW }
  | "=" { EQUALS }
  | ":=" { EQUALS }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | ":" { COLON }
  | digits as n { INT (int_of_string n) }
  | ident as x { ID x }
  | eof { EOF }
  | _ as c { raise (Error (Printf.sprintf "unexpected character '%c'" c)) }
