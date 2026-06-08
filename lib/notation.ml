type t =
  { unit_ctor : Type.ctor_head option
  ; nat : (Type.ctor_head * Type.ctor_head) option
  }

let empty = { unit_ctor = None; nat = None }

(* renders a subterm as a surface atom if it matches a registered role: the unit
   constructor as [()], the nat zero as [0], a closed succ-chain as a decimal;
   otherwise None, so the kernel prints it plainly. This is the hook the kernel
   printer ({!Type.pp_in}) consults — all notation knowledge lives here. *)
let sugar n term =
  let nat_lit term =
    match n.nat with
    | None -> None
    | Some (zero, succ) ->
        let rec count acc = function
          | Type.Ctor h when h = zero -> Some acc
          | Type.App (Type.Ctor h, m) when h = succ -> count (acc + 1) m
          | _ -> None
        in
        count 0 term
  in
  match term with
  | Type.Ctor h when n.unit_ctor = Some h -> Some "()"
  | _ -> Option.map string_of_int (nat_lit term)

let render_error n frags =
  String.concat ""
    (List.map
       (function
         | Error.Text s -> s
         | Error.Term (names, t) -> Type.to_string_in ~sugar:(sugar n) names t)
       frags)

let show n ctx v =
  Type.to_string_in ~sugar:(sugar n) ctx.Check.names
    (Value.quote ctx.Check.lvl v)

let show_term n ctx t = Type.to_string_in ~sugar:(sugar n) ctx.Check.names t

let register role spec n =
  match role with
  | "unit" ->
      if n.unit_ctor <> None then
        Error.type_error [ Error.txt "the unit notation is already registered" ];
      (match spec.Inductive.ctors with
      | [ { Inductive.fields = []; _ } ] when Inductive.nparams spec = 0 -> ()
      | _ ->
          Error.type_error
            [ Error.txt
                "@[notation unit] needs a parameterless inductive with a \
                 single nullary constructor"
            ]);
      { n with unit_ctor = Some (Inductive.ctor_head spec 0) }
  | "nat" ->
      if n.nat <> None then
        Error.type_error [ Error.txt "the nat notation is already registered" ];
      (match spec.Inductive.ctors with
      | [ { Inductive.fields = []; _ }; { Inductive.fields = [ f ]; _ } ]
        when Inductive.nparams spec = 0 && f.Inductive.recursive ->
          ()
      | _ ->
          Error.type_error
            [ Error.txt
                "@[notation nat] needs a parameterless inductive with a \
                 nullary constructor then a single-recursive-field constructor"
            ]);
      { n with
        nat = Some (Inductive.ctor_head spec 0, Inductive.ctor_head spec 1)
      }
  | _ ->
      Error.type_error
        [ Error.txtf "unknown notation role %s (expected: unit, nat)" role ]
