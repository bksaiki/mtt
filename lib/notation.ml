type t =
  { unit_ctor : Type.ctor_head option
  ; nat : (Type.ctor_head * Type.ctor_head) option
  ; sigma : Type.ctor_head option
  ; sum : string option
  ; eq : string option (* the inductive registered for [x = y] / [rfl] *)
  }

let empty =
  { unit_ctor = None; nat = None; sigma = None; sum = None; eq = None }

(* renders a subterm as surface notation, or None to let the kernel print it
   plainly: the unit constructor as [()], a succ-chain as a decimal, an applied
   Σ/Sum former as [×]/[Σ]/[+], a tuple, and native equality [Eq A x y] as infix
   [x = y]. This is the hook the kernel printer ({!Type.pp_in}) consults — all
   notation knowledge lives here. Returns [(prec, text)] so the printer can
   parenthesize (atoms use precedence 11); [recurse] renders a subterm at a
   given precedence for the infix forms. *)
let sugar n ~recurse names term =
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
  let peel term =
    let rec go acc = function
      | Type.App (f, a) -> go (a :: acc) f
      | h -> (h, acc)
    in
    go [] term
  in
  (* a saturated [Sigma.mk A B a b] peeled into its two components [(a, b)] *)
  let pair_components term =
    match (n.sigma, peel term) with
    | Some mk, (Type.Ctor h, [ _A; _B; a; b ]) when h = mk -> Some (a, b)
    | _ -> None
  in
  match term with
  | Type.Ctor h when n.unit_ctor = Some h -> Some (11, "()")
  | _ -> (
      match peel term with
      (* the registered equality former [Eq A x y] prints infix, dropping its
         type argument: [x = y] (non-associative, looser than + and ×, tighter
         than ->) *)
      | Type.Ind (name, _), [ _A; x; y ] when n.eq = Some name ->
          Some
            (2, Printf.sprintf "%s = %s" (recurse 3 names x) (recurse 3 names y))
      (* the equality's constructor [Eq.refl A x] prints as the bare [rfl],
         dropping its recovered parameters *)
      | Type.Ctor h, [ _A; _x ] when n.eq = Some h.Type.ind -> Some (11, "rfl")
      (* an applied [Sigma] former: dependent → [Σ (x : A) ⇒ B], else → [A ×
         B] *)
      | Type.Ind (name, _), [ a; Type.Lam (_, x, _, b) ]
        when match n.sigma with
             | Some mk -> String.equal name mk.Type.ind
             | None -> false ->
          if Type.occurs 0 b then
            let x = Type.freshen names x in
            Some
              ( 0
              , Printf.sprintf "Σ (%s : %s) ⇒ %s" x (recurse 0 names a)
                  (recurse 0 (x :: names) b) )
          else
            Some
              ( 4
              , Printf.sprintf "%s × %s" (recurse 5 names a)
                  (recurse 4 ("" :: names) b) )
      (* an applied [Sum] former → [A + B] (right-associative) *)
      | Type.Ind (name, _), [ a; b ] when n.sum = Some name ->
          Some
            (3, Printf.sprintf "%s + %s" (recurse 4 names a) (recurse 3 names b))
      | _ -> (
          match pair_components term with
          (* tuples right-nest: flatten the right spine to [(a, b, c)] *)
          | Some _ ->
              let rec comps t =
                match pair_components t with
                | Some (a, b) -> recurse 0 names a :: comps b
                | None -> [ recurse 0 names t ]
              in
              Some (11, "(" ^ String.concat ", " (comps term) ^ ")")
          | None -> Option.map (fun k -> (11, string_of_int k)) (nat_lit term)))

let render_error n frags =
  String.concat ""
    (List.map
       (function
         | Error.Text s -> s
         | Error.Term (names, t) -> Type.to_string_in ~sugar:(sugar n) names t)
       frags)

let show n names lvl v =
  Type.to_string_in ~sugar:(sugar n) names (Value.quote lvl v)

let show_term n names t = Type.to_string_in ~sugar:(sugar n) names t

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
        when Inductive.nparams spec = 0 && Option.is_some f.Inductive.recursive
        ->
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
  | "sigma" ->
      if n.sigma <> None then
        Error.type_error
          [ Error.txt "the sigma notation is already registered" ];
      (match spec.Inductive.ctors with
      | [ { Inductive.fields = [ _; _ ]; _ } ]
        when Inductive.nparams spec = 2 && Inductive.is_record spec ->
          ()
      | _ ->
          Error.type_error
            [ Error.txt
                "@[notation sigma] needs a two-parameter record with a single \
                 two-field constructor"
            ]);
      { n with sigma = Some (Inductive.ctor_head spec 0) }
  | "sum" ->
      if n.sum <> None then
        Error.type_error [ Error.txt "the sum notation is already registered" ];
      (match spec.Inductive.ctors with
      | [ { Inductive.fields = [ _ ]; _ }; { Inductive.fields = [ _ ]; _ } ]
        when Inductive.nparams spec = 2 ->
          ()
      | _ ->
          Error.type_error
            [ Error.txt
                "@[notation sum] needs a two-parameter inductive with two \
                 single-field constructors"
            ]);
      { n with sum = Some spec.Inductive.name }
  | "eq" ->
      if n.eq <> None then
        Error.type_error [ Error.txt "the eq notation is already registered" ];
      (match spec.Inductive.ctors with
      | [ { Inductive.fields = []; _ } ]
        when Inductive.nparams spec = 2 && Inductive.nindices spec = 1 ->
          ()
      | _ ->
          Error.type_error
            [ Error.txt
                "@[notation eq] needs a two-parameter, one-index inductive \
                 with a single nullary constructor (refl)"
            ]);
      { n with eq = Some spec.Inductive.name }
  | _ ->
      Error.type_error
        [ Error.txtf
            "unknown notation role %s (expected: unit, nat, sigma, sum, eq)"
            role
        ]
