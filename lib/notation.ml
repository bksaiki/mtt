let render_error notation frags =
  String.concat ""
    (List.map
       (function
         | Check.Text s -> s
         | Check.Term (names, t) -> Type.to_string_in ~notation names t)
       frags)

let show notation ctx v =
  Type.to_string_in ~notation ctx.Check.names (Value.quote ctx.Check.lvl v)

let show_term notation ctx t = Type.to_string_in ~notation ctx.Check.names t

let register role spec notation =
  match role with
  | "unit" ->
      if notation.Type.unit_ctor <> None then
        Check.type_error [ Check.txt "the unit notation is already registered" ];
      (match spec.Inductive.ctors with
      | [ { Inductive.fields = []; _ } ] when Inductive.nparams spec = 0 -> ()
      | _ ->
          Check.type_error
            [ Check.txt
                "@[notation unit] needs a parameterless inductive with a \
                 single nullary constructor"
            ]);
      { notation with Type.unit_ctor = Some (Inductive.ctor_head spec 0) }
  | "nat" ->
      if notation.Type.nat <> None then
        Check.type_error [ Check.txt "the nat notation is already registered" ];
      (match spec.Inductive.ctors with
      | [ { Inductive.fields = []; _ }; { Inductive.fields = [ f ]; _ } ]
        when Inductive.nparams spec = 0 && f.Inductive.recursive ->
          ()
      | _ ->
          Check.type_error
            [ Check.txt
                "@[notation nat] needs a parameterless inductive with a \
                 nullary constructor then a single-recursive-field constructor"
            ]);
      { notation with
        Type.nat = Some (Inductive.ctor_head spec 0, Inductive.ctor_head spec 1)
      }
  | _ ->
      Check.type_error
        [ Check.txtf "unknown notation role %s (expected: unit, nat)" role ]
