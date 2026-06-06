(** Source locations: the span of a token or phrase, as reported by the lexer.
    Attached to surface syntax and statements for error reporting; the core
    language carries no locations (the kernel doesn't care where a term came
    from). *)

type t = Lexing.position * Lexing.position

(** [pp fmt loc] prints the start of [loc] as [file:line:col] (1-based column),
    omitting the file when unknown (e.g. REPL input) *)
val pp : Format.formatter -> t -> unit

(** [to_string loc] is [loc] rendered via {!pp} *)
val to_string : t -> string
