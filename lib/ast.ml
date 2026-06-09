type t =
  { loc : Loc.t
  ; desc : desc
  }

and desc =
  | Var of string
  | Field of t * string (* a named projection, e.g. [Nat.rec] *)
  | Sort of int
  | Pi of Type.icit * string * t * t (* (x : A) -> B / {x : A} -> B *)
  | Arrow of t * t (* A -> B *)
  | Lam of Type.icit * string * t * t (* fun (x : A) => b / fun {x : A} => b *)
  | App of t * t
  | Ascribe of t * t (* (t : A) *)
  | MkUnit (* (), sugar for the prelude's Unit.unit *)
  | Sigma of string * t * t (* Σ (x : A) ⇒ B *)
  | Prod of t * t (* A × B *)
  | Pair of t * t (* (a, b) *)
  | Fst of t (* p.1 *)
  | Snd of t (* p.2 *)
  | Sum of t * t (* A + B *)
  | EqInfix of t * t (* x = y: the equality former, with the type inferred *)
  | Refl (* rfl: the equality's constructor Eq.refl, parameters recovered *)
  | Numeral of int (* a decimal literal, e.g. 0, 5; sugar for succ … zero *)
  | Hole (* _, an elaboration hole (a fresh metavariable) *)

let mk loc desc = { loc; desc }

(* telescopes: a binder group [(x y : A)] (or implicit [{x y : A}]) is a
   visibility, a name list, and an annotation; [telescope] folds groups into
   nested binders built by [node], stamping each synthetic node with the span of
   the whole construct *)
let telescope node loc groups body =
  List.fold_right
    (fun (i, xs, a) acc ->
      List.fold_right (fun x acc -> mk loc (node i x a acc)) xs acc)
    groups body

let lams = telescope (fun i x a b -> Lam (i, x, a, b))

let pis = telescope (fun i x a b -> Pi (i, x, a, b))

(* Σ binders carry no visibility (the parser only forms explicit ones) *)
let sigmas = telescope (fun _ x a b -> Sigma (x, a, b))

let var_spine t =
  let rec go acc t =
    match t.desc with
    | Var x -> Some (x :: acc)
    | App (f, { desc = Var x; _ }) -> go (x :: acc) f
    | _ -> None
  in
  go [] t

exception Unbound_variable of Loc.t * string

let to_term sg ?(notation = Notation.empty) names s =
  (* the inductive registered for the [sigma] role, that [Σ]/[×] desugar to *)
  let sigma_former loc =
    match notation.Notation.sigma with
    | Some mk -> mk.Type.ind
    | None ->
        raise (Unbound_variable (loc, "Σ/× (no sigma notation registered)"))
  in
  let sigma_app loc a bfun =
    Type.App (Type.App (Type.Ind (sigma_former loc), a), bfun)
  in
  (* the inductive registered for the [sum] role, that [+] desugars to *)
  let sum_former loc =
    match notation.Notation.sum with
    | Some name -> name
    | None -> raise (Unbound_variable (loc, "+ (no sum notation registered)"))
  in
  let rec go env s =
    match s.desc with
    (* a bare name is a local binder (de Bruijn) first, otherwise a global
       inductive former. Constructors are not bare: they are qualified [T.c]
       (handled below), so their names need only be unique within their type. *)
    | Var x -> (
        match List.find_index (String.equal x) env with
        | Some i -> Type.Var i
        | None -> (
            match Signature.find sg x with
            | Some spec -> Type.Ind spec.Inductive.name
            | None -> raise (Unbound_variable (s.loc, x))))
    (* qualified access on an inductive [T]: [T.rec] is its recursor, [T.c] one
       of its constructors *)
    | Field ({ desc = Var tname; _ }, field) -> (
        match Signature.find sg tname with
        | None -> raise (Unbound_variable (s.loc, tname))
        | Some spec -> (
            if String.equal field "rec" then
              Type.Rec (Inductive.rec_head spec)
            else
              match
                List.find_index
                  (fun (c : Inductive.ctor) -> String.equal c.cname field)
                  spec.Inductive.ctors
              with
              | Some i -> Type.Ctor (Inductive.ctor_head spec i)
              | None -> raise (Unbound_variable (s.loc, tname ^ "." ^ field))))
    | Field (_, f) -> raise (Unbound_variable (s.loc, "_." ^ f))
    | Sort i -> Type.Sort i
    | Pi (i, x, a, b) -> Type.Pi (i, x, go env a, go (x :: env) b)
    (* non-dependent: extend the env with a dummy no identifier can equal, so
       indices in [b] still shift across the binder *)
    | Arrow (a, b) -> Type.Pi (Type.Explicit, "", go env a, go ("" :: env) b)
    | Lam (i, x, a, b) -> Type.Lam (i, x, go env a, go (x :: env) b)
    | App (f, a) -> Type.App (go env f, go env a)
    (* () is sugar for whichever constructor is registered for the [unit]
       notation (the prelude's [Unit.unit]); the unit type itself is an ordinary
       inductive, resolved as a [Var] above *)
    | MkUnit -> (
        match notation.Notation.unit_ctor with
        | Some h -> Type.Ctor h
        | None ->
            raise (Unbound_variable (s.loc, "() (no unit notation registered)"))
        )
    (* Σ/× desugar to the registered dependent-pair former applied to [A] and
       the family [λ x : A ⇒ B] (a dummy binder when non-dependent), so the
       kernel needs no Σ of its own *)
    | Sigma (x, a, b) ->
        let a' = go env a in
        sigma_app s.loc a' (Type.Lam (Type.Explicit, x, a', go (x :: env) b))
    | Prod (a, b) ->
        let a' = go env a in
        sigma_app s.loc a' (Type.Lam (Type.Explicit, "", a', go ("" :: env) b))
    (* projections are the generic record projections *)
    | Fst t -> Type.Proj (0, go env t)
    | Snd t -> Type.Proj (1, go env t)
    (* a pair needs the expected Σ type to recover its parameters, so it is the
       elaborator's job ({!Elab}); this type-free pass cannot build it *)
    | Pair _ ->
        Error.type_error
          [ Error.txt "a pair requires a known type (elaborate it in context)" ]
    (* + desugars to the registered sum former applied to its two sides *)
    | Sum (a, b) ->
        Type.App (Type.App (Type.Ind (sum_former s.loc), go env a), go env b)
    (* the equality forms ([x = y], rfl) desugar to the registered [Eq]
       inductive with arguments the type-free pass cannot infer (the equality's
       type, rfl's parameters), so they are the elaborator's job ({!Elab}) *)
    | EqInfix _
    | Refl ->
        Error.type_error
          [ Error.txt
              "= / rfl require the elaborator (the type or parameters are \
               inferred)"
          ]
    (* a numeral expands to succ-applications of the registered nat zero/succ *)
    | Numeral n -> (
        match notation.Notation.nat with
        | Some (zero, succ) ->
            let rec build k =
              if k = 0 then
                Type.Ctor zero
              else
                Type.App (Type.Ctor succ, build (k - 1))
            in
            build n
        | None ->
            raise
              (Unbound_variable (s.loc, "numeral (no nat notation registered)"))
        )
    (* ascription is the typed identity: applying (fun (x : A) => x) to [t]
       forces the checking judgment t ⇐ A, and the redex evaporates under
       evaluation. No core constructor needed. *)
    | Ascribe (t, a) ->
        Type.App (Type.Lam (Type.Explicit, "x", go env a, Type.Var 0), go env t)
    (* a hole needs a type to become a metavariable, so it is the elaborator's
       job ({!Elab}); this type-free pass cannot produce one *)
    | Hole ->
        Error.type_error
          [ Error.txt "a hole _ requires the elaborator (use it in a term)" ]
  in
  go names s
