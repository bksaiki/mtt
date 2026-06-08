open Mtt

(* only prompt when interactive, so piped input produces clean output *)
let interactive = Unix.isatty Unix.stdin

(* runs one statement, expanding the prelude directive (which [Stmt.run] cannot
   — only the driver can reach the [Prelude] module) *)
let run_stmt ctx (stmt : Stmt.t) =
  match stmt.desc with
  | Stmt.Prelude -> (Prelude.load ctx, None)
  | _ -> Stmt.run ctx stmt

(* processes one line, returning the (possibly extended) context *)
let process ctx line =
  match Parse.stmt_of_string line with
  | exception Parse.Error (loc, msg) ->
      Printf.printf "%s: syntax error: %s\n" (Loc.to_string loc) msg;
      ctx
  | stmt -> (
      match run_stmt ctx stmt with
      | ctx, message ->
          Option.iter print_endline message;
          ctx
      | exception Ast.Unbound_variable (loc, x) ->
          Printf.printf "%s: unbound variable: %s\n" (Loc.to_string loc) x;
          ctx
      | exception Check.Type_error msg ->
          (* the statement is the whole REPL line: a position adds nothing *)
          Printf.printf "type error: %s\n" msg;
          ctx)

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
  let die fmt =
    Format.kasprintf
      (fun s ->
        prerr_endline s;
        exit 1)
      fmt
  in
  let contents = In_channel.with_open_text path In_channel.input_all in
  match Parse.file_of_string ~fname:path contents with
  | exception Parse.Error (loc, msg) ->
      die "%s: syntax error: %s" (Loc.to_string loc) msg
  | stmts ->
      let step ctx (stmt : Stmt.t) =
        match run_stmt ctx stmt with
        | ctx, message ->
            Option.iter print_endline message;
            ctx
        | exception Ast.Unbound_variable (loc, x) ->
            die "%s: unbound variable: %s" (Loc.to_string loc) x
        | exception Check.Type_error msg ->
            (* type errors are located at the failing statement *)
            die "%s: type error: %s" (Loc.to_string stmt.loc) msg
      in
      ignore (List.fold_left step Check.empty stmts)

let () =
  match Sys.argv with
  | [| _ |] -> repl Check.empty
  | [| _; path |] -> run_file path
  | _ ->
      prerr_endline "usage: mtt [file]";
      exit 2
