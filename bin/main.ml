open Mtt

(* only prompt when interactive, so piped input produces clean output *)
let interactive = Unix.isatty Unix.stdin

let process line =
  match Parse.term_of_string line with
  | exception Lexer.Error msg -> Printf.printf "lex error: %s\n" msg
  | exception Parser.Error -> print_endline "parse error"
  | exception Ast.Unbound_variable x -> Printf.printf "unbound variable: %s\n" x
  | t -> (
      (* type checking precedes evaluation, so normalization cannot get stuck on
         a non-function *)
      match Check.infer Check.empty t with
      | exception Check.Type_error msg -> Printf.printf "type error: %s\n" msg
      | ty ->
          Format.printf "@[%a@ : %a@]@." Type.pp (Value.normalize t) Type.pp
            (Value.quote 0 ty))

let rec repl () =
  if interactive then (
    print_string "mtt> ";
    flush stdout
  );
  match In_channel.input_line In_channel.stdin with
  | None -> if interactive then print_newline ()
  | Some "" -> repl ()
  | Some line ->
      process line;
      repl ()

let () = repl ()
