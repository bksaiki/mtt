(** The global signature [Σ]: the inductive types declared so far, keyed by
    name. This is mtt's first global (non-de-Bruijn) namespace; it sits beside
    the local context and is consulted only at the boundary — the scope-checker
    (resolving a surface name to an {!Type.Ind}/{!Type.Ctor}/{!Type.Rec} node)
    and the checker (which holds it in its context). The NbE core never needs
    it: the computational skeleton it requires is baked into the syntax nodes.
*)

type t

(** the empty signature *)
val empty : t

(** [add spec t] registers an inductive declaration *)
val add : Inductive.spec -> t -> t

(** [find t name] is the inductive declared under [name], if any *)
val find : t -> string -> Inductive.spec option

(** [find_ctor t cname] finds the inductive and constructor index of the
    (globally unique) constructor name [cname], if any *)
val find_ctor : t -> string -> (Inductive.spec * int) option
