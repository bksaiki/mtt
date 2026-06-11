let source = Prelude_data.contents

exception Load_error of string

(* run the prelude's statements, turning any failure into a [Load_error] with a
   rendered, [<prelude>:line:col]-located message. The prelude ships with the
   tool, so a failure here is a build-time bug — but it must not escape as a raw
   exception: the auto-load callers invoke [load] outside their own
   per-statement error handlers, so without this it would surface as an
   unlocated [Fatal error: exception]. *)
let load sess =
  let stmts =
    match Parse.file_of_string ~fname:"<prelude>" source with
    | stmts -> stmts
    | exception Parse.Error (loc, msg) ->
        raise
          (Load_error
             (Printf.sprintf "%s: syntax error: %s" (Loc.to_string loc) msg))
  in
  List.fold_left
    (fun (sess : Stmt.session) (stmt : Stmt.t) ->
      match Stmt.run sess stmt with
      | sess, _ -> sess
      | exception Error.Type_error frags ->
          raise
            (Load_error
               (Printf.sprintf "%s: type error: %s" (Loc.to_string stmt.loc)
                  (Notation.render_error sess.notation frags)))
      | exception Ast.Unbound_variable (loc, x) ->
          raise
            (Load_error
               (Printf.sprintf "%s: unbound variable: %s" (Loc.to_string loc) x)))
    sess stmts
