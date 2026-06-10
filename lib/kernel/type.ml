(* The computational skeleton of an inductive constructor, baked into the syntax
   node so that the NbE core can fire ι without consulting the global signature
   (which holds the full types, for the checker only). *)
type ctor_head =
  { ind : string (* the inductive this constructs *)
  ; cname : string (* the constructor's (globally unique) name *)
  ; cindex : int (* its position in the inductive's constructor list *)
  ; carity : int (* total arguments: leading parameters + fields *)
  ; nparams : int (* leading parameters, so a projection can skip them *)
  ; clevels : Level.t list (* use-site level arguments (empty if monomorphic) *)
  }

(* a binder's visibility: an explicit [(x : A)] argument is written at every
   application; an implicit [{x : A}] one is inserted by the elaborator. The
   kernel carries this on Π/λ but ignores it entirely in conversion and typing
   (like the binder-name hint) — it is metadata read only by the frontend
   (elaboration's argument insertion and the printer). *)
type icit =
  | Explicit
  | Implicit

type t =
  | Var of int (* de Bruijn index *)
  | Sort of Level.t (* the Sort hierarchy: Prop = Sort 0, Type i = Sort (i+1) *)
  | Pi of icit * string * t * t (* Π (x : A). B, B binds index 0 *)
  | Lam of icit * string * t * t (* λ (x : A). b *)
  | App of t * t
  | Proj of int * t (* x.(i+1): the i-th field projection of a record *)
  | Meta of
      int (* a metavariable, by id; elaboration-only, never in final core *)
  | Ind of string * Level.t list
    (* an inductive type former (with use-site level arguments), applied to
       params/indices via App *)
  | Ctor of ctor_head (* a constructor, applied to args via App *)
  | Rec of rec_head (* an inductive's recursor, applied to args via App *)

(* The skeleton of a recursor, enough to drive ι without the signature. [recs]
   has one entry per constructor (in order), each listing that constructor's
   *fields* (its non-parameter arguments) and which are recursive. Parameters
   are shared and never recursive, so they are excluded. For an indexed family
   the recursor's argument spine is [params @ motive :: minors @ indices @
   [major]]: [nindices] index arguments sit just before the major, and a
   recursive field carries the index instances it sits at (so ι can form the
   induction hypothesis at the right indices — see [vrec]). *)
and rec_head =
  { rind : string (* the inductive being eliminated; prints as "rind.rec" *)
  ; nparams : int (* leading parameter arguments, shared and fixed *)
  ; nindices : int (* index arguments, between the minors and the major *)
  ; recs : field_rec list list
  ; rlevels : Level.t list (* use-site level arguments (empty if monomorphic) *)
  }

(* whether a constructor field is recursive, and if so the index instances of
   its inductive type [Ind params indices] — terms in the context [params,
   earlier fields], evaluated by ι against the constructor's actual arguments *)
and field_rec =
  | Nonrec
  | Recursive of t list

(* substitute the level arguments [args] for the level variables in every [Sort]
   and inductive-head level list of [t] (instantiating a level-polymorphic term
   at a use site); identity on a monomorphic term *)
let rec subst_levels args t =
  match t with
  | Sort l -> Sort (Level.subst args l)
  | Var _
  | Meta _ ->
      t
  | Pi (i, x, a, b) -> Pi (i, x, subst_levels args a, subst_levels args b)
  | Lam (i, x, a, b) -> Lam (i, x, subst_levels args a, subst_levels args b)
  | App (f, a) -> App (subst_levels args f, subst_levels args a)
  | Proj (i, e) -> Proj (i, subst_levels args e)
  | Ind (n, ls) -> Ind (n, List.map (Level.subst args) ls)
  | Ctor h -> Ctor { h with clevels = List.map (Level.subst args) h.clevels }
  | Rec h -> Rec { h with rlevels = List.map (Level.subst args) h.rlevels }

let rec occurs k = function
  | Var i -> i = k
  | Sort _ -> false
  | Pi (_, _, a, b)
  | Lam (_, _, a, b) ->
      occurs k a || occurs (k + 1) b
  | App (f, a) -> occurs k f || occurs k a
  | Proj (_, t) -> occurs k t
  (* a metavariable carries no de Bruijn index of its own; its dependencies ride
     the enclosing [App] spine *)
  | Meta _ -> false
  (* inductive heads are closed: they carry no de Bruijn indices, only the
     skeleton; any arguments ride along as App nodes *)
  | Ind _
  | Ctor _
  | Rec _ ->
      false

(* whether any metavariable occurs in [t]; the frontend uses it to reject a term
   with an unsolved hole before the trusted check ever sees it *)
let rec has_meta = function
  | Meta _ -> true
  | Var _
  | Sort _
  | Ind _
  | Ctor _
  | Rec _ ->
      false
  | Proj (_, a) -> has_meta a
  | Pi (_, _, a, b)
  | Lam (_, _, a, b) ->
      has_meta a || has_meta b
  | App (a, b) -> has_meta a || has_meta b

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
  (* precedence: 0 = binders, 1 = arrow, 2 = equality, 3 = sum, 4 = product,
     10 = application, 11 = atom. (The kernel printer itself uses only 0/1/10/11;
     the sugar hook uses 2–4 for the =/+/× infix notations.) *)
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
    | Sort l -> (
        match Level.to_int l with
        | Some 0 -> Format.pp_print_string fmt "Prop"
        | Some 1 -> Format.pp_print_string fmt "Type"
        | Some u ->
            paren_if fmt (prec > 10) (fun fmt ->
                Format.fprintf fmt "Type %d" (u - 1))
        | None ->
            (* a level variable (universe polymorphism); no surface form yet *)
            paren_if fmt (prec > 10) (fun fmt ->
                Format.fprintf fmt "Sort %s" (Level.to_string l)))
    | Pi (Implicit, x, a, b) ->
        (* an implicit binder always shows its braces and name (dropping the
           name would lose the marker), even when unused *)
        let x = freshen names x in
        paren_if fmt (prec > 1) (fun fmt ->
            Format.fprintf fmt "@[{%s : %a} ->@ %a@]" x (go 0 names) a
              (go 1 (x :: names))
              b)
    | Pi (Explicit, x, a, b) ->
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
    | Lam (i, x, a, b) ->
        let x = freshen names x in
        let l, r =
          match i with
          | Implicit -> ("{", "}")
          | Explicit -> ("(", ")")
        in
        paren_if fmt (prec > 0) (fun fmt ->
            Format.fprintf fmt "@[fun %s%s : %a%s =>@ %a@]" l x (go 0 names) a r
              (go 0 (x :: names))
              b)
    | App (f, a) ->
        paren_if fmt (prec > 10) (fun fmt ->
            Format.fprintf fmt "@[%a@ %a@]" (go 10 names) f (go 11 names) a)
    | Proj (i, t) -> Format.fprintf fmt "%a.%d" (go 11 names) t (i + 1)
    | Meta n -> Format.fprintf fmt "?%d" n
    (* inductive heads are atoms; their arguments print via the enclosing App
       nodes (so [Nat.rec P z s n] renders through application). Constructors
       and the recursor print qualified by their type; surface sugar like [()]
       or decimals is applied by [sugar] above, not here. *)
    | Ind (name, _) -> Format.pp_print_string fmt name
    | Ctor h -> Format.fprintf fmt "%s.%s" h.ind h.cname
    | Rec h -> Format.fprintf fmt "%s.rec" h.rind
  in
  go 0 names fmt t

let pp fmt t = pp_in [] fmt t

let to_string_in ?(sugar = fun ~recurse:_ _ _ -> None) names t =
  Format.asprintf "%a" (pp_in ~sugar names) t

let to_string t = to_string_in [] t
