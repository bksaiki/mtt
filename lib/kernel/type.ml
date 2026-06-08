(* The computational skeleton of an inductive constructor, baked into the syntax
   node so that the NbE core can fire ι without consulting the global signature
   (which holds the full types, for the checker only). *)
type ctor_head =
  { ind : string (* the inductive this constructs *)
  ; cname : string (* the constructor's (globally unique) name *)
  ; cindex : int (* its position in the inductive's constructor list *)
  ; carity : int (* total arguments: leading parameters + fields *)
  ; nparams : int (* leading parameters, so a projection can skip them *)
  }

(* The skeleton of a recursor, enough to drive ι. [recs] has one entry per
   constructor (in order); each entry flags, for that constructor's *fields*
   (its non-parameter arguments), which are recursive (of the inductive's own
   type). Parameters are shared and never recursive, so they are excluded. *)
type rec_head =
  { rind : string (* the inductive being eliminated; prints as "rind.rec" *)
  ; nparams : int (* leading parameter arguments, shared and fixed *)
  ; recs : bool list list
  }

type t =
  | Var of int (* de Bruijn index *)
  | Sort of int (* the Sort hierarchy: Prop = Sort 0, Type i = Sort (i+1) *)
  | Pi of string * t * t (* Π (x : A). B, B binds index 0 *)
  | Lam of string * t * t (* λ (x : A). b *)
  | App of t * t
  | Proj of int * t (* x.(i+1): the i-th field projection of a record *)
  | Sum of t * t (* A + B *)
  | Inl of t (* left injection *)
  | Inr of t (* right injection *)
  | Case of t * t * t * t (* case P s u v: eliminates s : A + B at motive P *)
  | Eq of t * t * t (* Eq A x y: propositional equality of x, y : A *)
  | Refl (* the reflexivity proof; check-only *)
  | J of t * t * t (* J P d p: eliminates p : Eq A x y at motive P *)
  | Ind of string (* an inductive type former, applied to params via App *)
  | Ctor of ctor_head (* a constructor, applied to args via App *)
  | Rec of rec_head (* an inductive's recursor, applied to args via App *)

let rec occurs k = function
  | Var i -> i = k
  | Sort _ -> false
  | Pi (_, a, b)
  | Lam (_, a, b) ->
      occurs k a || occurs (k + 1) b
  | App (f, a) -> occurs k f || occurs k a
  | Proj (_, t) -> occurs k t
  | Sum (a, b) -> occurs k a || occurs k b
  | Inl t
  | Inr t ->
      occurs k t
  | Case (p, s, u, v) -> occurs k p || occurs k s || occurs k u || occurs k v
  | Eq (a, x, y) -> occurs k a || occurs k x || occurs k y
  | Refl -> false
  | J (p, d, pr) -> occurs k p || occurs k d || occurs k pr
  (* inductive heads are closed: they carry no de Bruijn indices, only the
     skeleton; any arguments ride along as App nodes *)
  | Ind _
  | Ctor _
  | Rec _ ->
      false

(* makes the hint [x] distinct from every name in scope *)
let freshen names x =
  let rec prime x =
    if List.mem x names then
      prime (x ^ "'")
    else
      x
  in
  prime
    (if x = "" then
       "x"
     else
       x)

(* [sugar ~recurse names t] optionally renders the subterm [t] as surface
   notation, returning [(prec, text)] so the printer can parenthesize it; the
   kernel knows no notation itself, so the frontend supplies the hook (see
   [Notation.sugar]). [recurse prec names sub] renders a subterm, letting the
   hook build infix/mixfix forms out of rendered pieces. *)
let pp_in ?(sugar = fun ~recurse:_ _ _ -> None) names fmt t =
  (* adds parentheses around [body] (written to [fmt]) if [cond] is true. Takes
     the formatter explicitly: [recurse] renders subterms to their own buffers,
     so this must not close over [pp_in]'s outermost [fmt]. *)
  let paren_if fmt cond body =
    if cond then
      Format.fprintf fmt "(%t)" body
    else
      body fmt
  in
  (* precedence: 0 = binders, 1 = arrow, 2 = sum, 3 = product, 10 = application,
     11 = atom *)
  (* renders a subterm to its own isolated buffer — [Format.asprintf] is not safe
     to nest here (the hook may call [recurse] while the printer is mid-format),
     so an explicit formatter avoids any shared-buffer corruption *)
  let rec recurse p ns s =
    let buf = Buffer.create 32 in
    let f = Format.formatter_of_buffer buf in
    go p ns f s;
    Format.pp_print_flush f ();
    Buffer.contents buf
  and go prec names fmt t =
    match sugar ~recurse names t with
    | Some (p, s) ->
        paren_if fmt (prec > p) (fun fmt -> Format.pp_print_string fmt s)
    | None -> go_struct prec names fmt t
  and go_struct prec names fmt t =
    match t with
    | Var i -> (
        match List.nth_opt names i with
        | Some x -> Format.pp_print_string fmt x
        | None -> Format.fprintf fmt "!%d" i)
    (* surface names for sorts: Sort 0 is Prop, Sort (i+1) is Type i *)
    | Sort 0 -> Format.pp_print_string fmt "Prop"
    | Sort 1 -> Format.pp_print_string fmt "Type"
    | Sort u ->
        paren_if fmt (prec > 10) (fun fmt ->
            Format.fprintf fmt "Type %d" (u - 1))
    | Pi (x, a, b) ->
        paren_if fmt (prec > 1) (fun fmt ->
            if occurs 0 b then
              let x = freshen names x in
              Format.fprintf fmt "@[(%s : %a) ->@ %a@]" x (go 0 names) a
                (go 1 (x :: names))
                b
            else
              (* the binder is unused: print an arrow and push an empty name (no
                 identifier can collide with it) to keep depths aligned *)
              Format.fprintf fmt "@[%a ->@ %a@]" (go 2 names) a
                (go 1 ("" :: names))
                b)
    | Lam (x, a, b) ->
        let x = freshen names x in
        paren_if fmt (prec > 0) (fun fmt ->
            Format.fprintf fmt "@[fun (%s : %a) =>@ %a@]" x (go 0 names) a
              (go 0 (x :: names))
              b)
    | App (f, a) ->
        paren_if fmt (prec > 10) (fun fmt ->
            Format.fprintf fmt "@[%a@ %a@]" (go 10 names) f (go 11 names) a)
    | Proj (i, t) -> Format.fprintf fmt "%a.%d" (go 11 names) t (i + 1)
    (* + is right-associative, between arrows and products *)
    | Sum (a, b) ->
        paren_if fmt (prec > 2) (fun fmt ->
            Format.fprintf fmt "@[%a +@ %a@]" (go 3 names) a (go 2 names) b)
    | Inl t ->
        paren_if fmt (prec > 10) (fun fmt ->
            Format.fprintf fmt "@[inl@ %a@]" (go 11 names) t)
    | Inr t ->
        paren_if fmt (prec > 10) (fun fmt ->
            Format.fprintf fmt "@[inr@ %a@]" (go 11 names) t)
    | Case (p, s, u, v) ->
        paren_if fmt (prec > 10) (fun fmt ->
            Format.fprintf fmt "@[case@ %a@ %a@ %a@ %a@]" (go 11 names) p
              (go 11 names) s (go 11 names) u (go 11 names) v)
    | Eq (a, x, y) ->
        paren_if fmt (prec > 10) (fun fmt ->
            Format.fprintf fmt "@[Eq@ %a@ %a@ %a@]" (go 11 names) a
              (go 11 names) x (go 11 names) y)
    | Refl -> Format.pp_print_string fmt "refl"
    | J (p, d, pr) ->
        paren_if fmt (prec > 10) (fun fmt ->
            Format.fprintf fmt "@[J@ %a@ %a@ %a@]" (go 11 names) p (go 11 names)
              d (go 11 names) pr)
    (* inductive heads are atoms; their arguments print via the enclosing App
       nodes (so [Nat.rec P z s n] renders through application). Constructors
       and the recursor print qualified by their type; surface sugar like [()]
       or decimals is applied by [sugar] above, not here. *)
    | Ind name -> Format.pp_print_string fmt name
    | Ctor h -> Format.fprintf fmt "%s.%s" h.ind h.cname
    | Rec h -> Format.fprintf fmt "%s.rec" h.rind
  in
  go 0 names fmt t

let pp fmt t = pp_in [] fmt t

let to_string_in ?(sugar = fun ~recurse:_ _ _ -> None) names t =
  Format.asprintf "%a" (pp_in ~sugar names) t

let to_string t = to_string_in [] t
