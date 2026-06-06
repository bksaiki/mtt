{
open Parser

exception Error of string
}

let whitespace = [' ' '\t' '\r' '\n']+
let digits = ['0'-'9']+
let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*

rule token = parse
  | whitespace { token lexbuf }
  | "fun" { FUN }
  | "Type" { TYPE }
  | "->" { ARROW }
  | "=>" { DARROW }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | ":" { COLON }
  | digits as n { INT (int_of_string n) }
  | ident as x { ID x }
  | eof { EOF }
  | _ as c { raise (Error (Printf.sprintf "unexpected character '%c'" c)) }
