(** Kernel error messages, carried as renderable fragments rather than
    pre-rendered strings.

    A message is a list of fragments: literal [Text], or a core [Term] paired
    with the binder names it is read against. The kernel formats no notation
    itself — it carries the offending terms (built with {!Check.tm}/{!Check.vl})
    and the frontend, which owns the notation registry, renders them. *)

type frag =
  | Text of string
  | Term of string list * Type.t

exception Type_error of frag list

(** [type_error frags] raises {!Type_error} with the given message fragments *)
val type_error : frag list -> 'a

(** [txt s] is a literal-text fragment. *)
val txt : string -> frag

(** [txtf fmt] is a printf-style literal-text fragment. *)
val txtf : ('a, Format.formatter, unit, frag) format4 -> 'a
