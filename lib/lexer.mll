(* The lexer (ocamllex). Whitespace and [--] line comments are skipped;
   keywords win over identifiers by rule order, and longest-match keeps the
   multi-character operators ([->], [=>], [:=], [#check_equal]) unambiguous. *)

{
open Parser

(* raised on a character no rule matches, with a human-readable message *)
exception Error of string
}

let whitespace = [' ' '\t' '\r']+
let digits = ['0'-'9']+
let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

(* unicode alternatives are matched as literal UTF-8 byte sequences *)
rule token = parse
  (* newlines must be reported so positions stay accurate *)
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | whitespace { token lexbuf }
  | "--" [^ '\n']* { token lexbuf }
  | "fun" { FUN }
  | "λ" { FUN }
  | "Π" { PI }
  | "∏" { PI }
  | "Σ" { SIGMA }
  | "Type" { TYPE }
  | "Prop" { PROP }
  | "Unit" { UNIT }
  | "Empty" { EMPTY }
  | "absurd" { ABSURD }
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
  | "×" { TIMES }
  | "*" { TIMES }
  | "," { COMMA }
  | ".1" { FST }
  | ".2" { SND }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | ":" { COLON }
  | digits as n { INT (int_of_string n) }
  | ident as x { ID x }
  | eof { EOF }
  | _ as c { raise (Error (Printf.sprintf "unexpected character '%c'" c)) }
