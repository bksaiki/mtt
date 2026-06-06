open Mtt

(* only prompt when interactive, so piped input produces clean output *)
let interactive = Unix.isatty Unix.stdin

(* processes one line, returning the (possibly extended) context *)
let process ctx line =
  match Stmt.run ctx (Parse.stmt_of_string line) with
  | ctx, message ->
      Option.iter print_endline message;
      ctx
  | exception Lexer.Error msg ->
      Printf.printf "lex error: %s\n" msg;
      ctx
  | exception Parser.Error ->
      print_endline "parse error";
      ctx
  | exception Ast.Unbound_variable x ->
      Printf.printf "unbound variable: %s\n" x;
      ctx
  | exception Check.Type_error msg ->
      Printf.printf "type error: %s\n" msg;
      ctx

let rec repl ctx =
  if interactive then (
    print_string "mtt> ";
    flush stdout
  );
  match In_channel.input_line In_channel.stdin with
  | None -> if interactive then print_newline ()
  | Some "" -> repl ctx
  | Some line -> repl (process ctx line)

(* checks a whole file, stopping at the first error with a nonzero exit *)
let run_file path =
  let die fmt = Format.kasprintf (fun s -> prerr_endline s; exit 1) fmt in
  let contents = In_channel.with_open_text path In_channel.input_all in
  match Parse.file_of_string contents with
  | exception Lexer.Error msg -> die "lex error: %s" msg
  | exception Parser.Error -> die "parse error"
  | stmts ->
      let step ctx stmt =
        match Stmt.run ctx stmt with
        | ctx, message ->
            Option.iter print_endline message;
            ctx
        | exception Ast.Unbound_variable x -> die "unbound variable: %s" x
        | exception Check.Type_error msg -> die "type error: %s" msg
      in
      ignore (List.fold_left step Check.empty stmts)

let () =
  match Sys.argv with
  | [| _ |] -> repl Check.empty
  | [| _; path |] -> run_file path
  | _ ->
      prerr_endline "usage: mtt [file]";
      exit 2
