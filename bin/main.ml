open Mtt

(* only prompt when interactive, so piped input produces clean output *)
let interactive = Unix.isatty Unix.stdin

(* The standard prelude is loaded automatically unless the program opens with
   the `prelude` directive (which asks for a bare environment, e.g. to define
   the prelude itself or a from-scratch encoding). Loading is lazy — decided by
   the first statement — so an opted-out file never pays for it. A `prelude`
   directive anywhere but first is an error. *)

let help =
  String.concat "\n"
    [ "mtt REPL — enter one statement per line. Commands:"
    ; "  :help, :h        show this help"
    ; "  :env             list the bindings in scope"
    ; "  :quit, :q        exit (or Ctrl-D)"
    ; ""
    ; "  #check t         report the normal form and type of t"
    ; "  #eval t          report just the normal form of t"
    ; "  #check_equal t u assert t and u are definitionally equal"
    ; "  axiom x : A      postulate x of type A"
    ; "  def x [: A] := t define x (annotation optional)"
    ; "  theorem x : A := t  prove A with t (opaque)"
    ; "  prelude          start without the standard prelude (only valid for \
       first line)"
    ]

(* print the bindings in scope, oldest first (the context lists are
   most-recent-first). Neutral levels are absolute, so every type renders
   correctly against the full set of names. *)
let print_env (ctx : Check.ctx) =
  match List.rev (List.combine ctx.names ctx.types) with
  | [] -> print_endline "(empty context)"
  | binds ->
      List.iter
        (fun (x, ty) -> Printf.printf "%s : %s\n" x (Check.show ctx ty))
        binds

(* REPL: run one statement, printing its message or error, returning the ctx *)
let run_repl ctx (stmt : Stmt.t) =
  match Stmt.run ctx stmt with
  | ctx, message ->
      Option.iter print_endline message;
      ctx
  | exception Ast.Unbound_variable (loc, x) ->
      Printf.printf "%s: unbound variable: %s\n" (Loc.to_string loc) x;
      ctx
  | exception Check.Type_error msg ->
      (* the statement is the whole REPL line: a position adds nothing *)
      Printf.printf "type error: %s\n" msg;
      ctx

let rec repl ctx initialized =
  if interactive then (
    print_string "mtt> ";
    flush stdout
  );
  match In_channel.input_line In_channel.stdin with
  | None -> if interactive then print_newline ()
  | Some "" -> repl ctx initialized
  (* REPL meta-commands: handled here, not in the grammar; they leave the
     context (and the prelude-init decision) untouched *)
  | Some (":quit" | ":q") -> ()
  | Some (":help" | ":h") ->
      print_endline help;
      repl ctx initialized
  | Some ":env" ->
      (* before the first statement the prelude has not loaded yet (it loads
         lazily, so a leading `prelude` can still opt out): say so rather than
         report a misleading empty context *)
      if initialized then
        print_env ctx
      else
        print_endline
          "no bindings yet (the prelude loads on the first statement; \
           `prelude` opts out)";
      repl ctx initialized
  | Some line -> (
      match Parse.stmt_of_string line with
      | exception Parse.Error (loc, msg) ->
          Printf.printf "%s: syntax error: %s\n" (Loc.to_string loc) msg;
          repl ctx initialized
      | { desc = Stmt.Prelude; _ } when not initialized ->
          (* opt out: start from a bare environment *)
          repl Check.empty true
      | { desc = Stmt.Prelude; _ } ->
          print_endline "prelude must be the first statement";
          repl ctx initialized
      | stmt when not initialized ->
          (* first real statement: auto-load the prelude, then run it *)
          repl (run_repl (Prelude.load Check.empty) stmt) true
      | stmt -> repl (run_repl ctx stmt) true)

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
      (* auto-load the prelude unless the file opens with `prelude` *)
      let init, stmts =
        match stmts with
        | { Stmt.desc = Stmt.Prelude; _ } :: rest -> (Check.empty, rest)
        | _ -> (Prelude.load Check.empty, stmts)
      in
      let step ctx (stmt : Stmt.t) =
        match stmt.desc with
        | Stmt.Prelude ->
            die "%s: prelude must be the first statement"
              (Loc.to_string stmt.loc)
        | _ -> (
            match Stmt.run ctx stmt with
            | ctx, message ->
                Option.iter print_endline message;
                ctx
            | exception Ast.Unbound_variable (loc, x) ->
                die "%s: unbound variable: %s" (Loc.to_string loc) x
            | exception Check.Type_error msg ->
                die "%s: type error: %s" (Loc.to_string stmt.loc) msg)
      in
      ignore (List.fold_left step init stmts)

let () =
  match Sys.argv with
  | [| _ |] -> repl Check.empty false
  | [| _; path |] -> run_file path
  | _ ->
      prerr_endline "usage: mtt [file]";
      exit 2
