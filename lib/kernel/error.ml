type frag =
  | Text of string
  | Term of string list * Type.t

exception Type_error of frag list

let type_error frags = raise (Type_error frags)

let txt s = Text s

let txtf fmt = Format.kasprintf (fun s -> Text s) fmt
