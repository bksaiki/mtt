type t = Lexing.position * Lexing.position

let pp fmt ((s, _) : t) =
  (* 1-based column, gcc/editor style *)
  let col = s.Lexing.pos_cnum - s.Lexing.pos_bol + 1 in
  if s.Lexing.pos_fname <> "" then Format.fprintf fmt "%s:" s.Lexing.pos_fname;
  Format.fprintf fmt "%d:%d" s.Lexing.pos_lnum col

let to_string l = Format.asprintf "%a" pp l
