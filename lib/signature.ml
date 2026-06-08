module M = Map.Make (String)

type t = { inds : Inductive.spec M.t }

let empty = { inds = M.empty }

let add spec t = { inds = M.add spec.Inductive.name spec t.inds }

let find t name = M.find_opt name t.inds

(* the (spec, constructor index) of a constructor by its globally unique name *)
let find_ctor t cname =
  M.fold
    (fun _ spec acc ->
      match acc with
      | Some _ -> acc
      | None -> (
          match
            List.find_index
              (fun (c : Inductive.ctor) -> String.equal c.cname cname)
              spec.Inductive.ctors
          with
          | Some i -> Some (spec, i)
          | None -> None))
    t.inds None
