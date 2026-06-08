module M = Map.Make (String)

type t = { inds : Inductive.spec M.t }

let empty = { inds = M.empty }

let add spec t = { inds = M.add spec.Inductive.name spec t.inds }

let find t name = M.find_opt name t.inds
