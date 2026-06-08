let source = Prelude_data.contents

let load sess =
  let stmts = Parse.file_of_string ~fname:"<prelude>" source in
  List.fold_left (fun sess stmt -> fst (Stmt.run sess stmt)) sess stmts
