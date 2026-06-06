open Mtt

(* only prompt when interactive, so piped input produces clean output *)
let interactive = Unix.isatty Unix.stdin

let process line =
  match Parse.term_of_string line with
  | t -> Format.printf "%a@." Type.pp t
  | exception Lexer.Error msg -> Printf.printf "lex error: %s\n" msg
  | exception Parser.Error -> print_endline "parse error"
  | exception Ast.Unbound_variable x ->
      Printf.printf "unbound variable: %s\n" x

let rec repl () =
  if interactive then (
    print_string "mtt> ";
    flush stdout);
  match In_channel.input_line In_channel.stdin with
  | None -> if interactive then print_newline ()
  | Some "" -> repl ()
  | Some line ->
      process line;
      repl ()

let () = repl ()
