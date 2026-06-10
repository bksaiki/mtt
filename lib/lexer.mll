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
  (* a universe literal is one lexeme: "Type" and its level, so the level can
     never be mistaken for a separate numeral argument *)
  | "Type" [' ' '\t']+ (digits as n) { TYPELEVEL (int_of_string n) }
  | "Type" { TYPE }
  | "Prop" { PROP }
  (* explicit universe levels: [Sort u], with [max]/[imax] on level expressions *)
  | "Sort" { SORT }
  | "max" { MAX }
  | "imax" { IMAX }
  | "prelude" { PRELUDE }
  | "#check" { CHECK }
  | "#check_equal" { CHECK_EQUAL }
  | "#eval" { EVAL }
  | "axiom" { AXIOM }
  | "def" { DEF }
  | "theorem" { THEOREM }
  | "lemma" { THEOREM }
  | "inductive" { INDUCTIVE }
  (* [match e with | C x => … | … end]: case-analysis sugar for the recursor *)
  | "match" { MATCH }
  | "with" { WITH }
  | "end" { END }
  | "->" { ARROW }
  | "→" { ARROW }
  | "=>" { DARROW }
  | "⇒" { DARROW }
  (* [:=] separates a definition/inductive from its body; [=] is equality infix
     (sugar for [Eq], with the type inferred) *)
  | ":=" { EQUALS }
  | "=" { EQOP }
  | "+" { PLUS }
  | "×" { TIMES }
  | "*" { TIMES }
  | "," { COMMA }
  | "|" { BAR }
  | "@[" { ATTR_OPEN }
  | "]" { ATTR_CLOSE }
  (* [@f] makes every argument explicit (suppresses implicit insertion); the
     longer [@[] above wins by maximal munch, so a lone [@] is unambiguous *)
  | "@" { AT }
  | ".1" { FST }
  | ".2" { SND }
  | "." digits as s
    { raise
        (Error
           (Printf.sprintf
              "no projection %s: tuples are right-nested pairs, so e.g. the \
               third component of a triple is .2.2"
              s)) }
  (* a named projection, currently only [.rec] (an inductive's recursor) *)
  | "." (ident as f) { DOTID f }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | ":" { COLON }
  | digits as n { INT (int_of_string n) }
  | ident as x { ID x }
  | eof { EOF }
  | _ as c { raise (Error (Printf.sprintf "unexpected character '%c'" c)) }
