let source = Prelude_data.contents

let load ctx =
  let stmts = Parse.file_of_string ~fname:"<prelude>" source in
  List.fold_left (fun ctx stmt -> fst (Stmt.run ctx stmt)) ctx stmts
