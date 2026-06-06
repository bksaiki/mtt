type t =
  | Var of int (* de Bruijn index *)
  | Sort of int (* the Sort hierarchy: Prop = Sort 0, Type i = Sort (i+1) *)
  | Pi of string * t * t (* Π (x : A). B, B binds index 0 *)
  | Lam of string * t * t (* λ (x : A). b *)
  | App of t * t
  | Unit (* the unit type *)
  | MkUnit (* the element of Unit *)
  | Empty (* the empty type: falsity *)
  | Absurd of
      t * t (* absurd A h: ex falso, eliminating h : Empty at motive A *)
  | Sigma of string * t * t (* Σ (x : A) ⇒ B, B binds index 0 *)
  | Pair of t * t (* (a, b) *)
  | Fst of t (* p.1 *)
  | Snd of t (* p.2 *)

let rec occurs k = function
  | Var i -> i = k
  | Sort _ -> false
  | Pi (_, a, b)
  | Lam (_, a, b) ->
      occurs k a || occurs (k + 1) b
  | App (f, a) -> occurs k f || occurs k a
  | Unit
  | MkUnit
  | Empty ->
      false
  | Absurd (a, h) -> occurs k a || occurs k h
  | Sigma (_, a, b) -> occurs k a || occurs (k + 1) b
  | Pair (a, b) -> occurs k a || occurs k b
  | Fst t
  | Snd t ->
      occurs k t

let pp_in names fmt t =
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
  in
  (* adds parentheses if [cond] is true *)
  let paren_if cond body =
    if cond then
      Format.fprintf fmt "(%t)" body
    else
      body fmt
  in
  (* precedence: 0 = binders, 1 = arrow, 3 = product, 10 = application, 11 =
     atom *)
  let rec go prec names fmt t =
    match t with
    | Var i -> (
        match List.nth_opt names i with
        | Some x -> Format.pp_print_string fmt x
        | None -> Format.fprintf fmt "!%d" i)
    (* surface names for sorts: Sort 0 is Prop, Sort (i+1) is Type i *)
    | Sort 0 -> Format.pp_print_string fmt "Prop"
    | Sort 1 -> Format.pp_print_string fmt "Type"
    | Sort u ->
        paren_if (prec > 10) (fun fmt -> Format.fprintf fmt "Type %d" (u - 1))
    | Pi (x, a, b) ->
        paren_if (prec > 1) (fun fmt ->
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
        paren_if (prec > 0) (fun fmt ->
            Format.fprintf fmt "@[fun (%s : %a) =>@ %a@]" x (go 0 names) a
              (go 0 (x :: names))
              b)
    | App (f, a) ->
        paren_if (prec > 10) (fun fmt ->
            Format.fprintf fmt "@[%a@ %a@]" (go 10 names) f (go 11 names) a)
    | Unit -> Format.pp_print_string fmt "Unit"
    | MkUnit -> Format.pp_print_string fmt "()"
    | Empty -> Format.pp_print_string fmt "Empty"
    | Sigma (x, a, b) ->
        if occurs 0 b then
          let x = freshen names x in
          paren_if (prec > 0) (fun fmt ->
              Format.fprintf fmt "@[Σ (%s : %a) ⇒@ %a@]" x (go 0 names) a
                (go 0 (x :: names))
                b)
        else
          (* non-dependent: print a product; × is right-associative and sits
             between arrows and application *)
            paren_if (prec > 3) (fun fmt ->
              Format.fprintf fmt "@[%a ×@ %a@]" (go 4 names) a
                (go 3 ("" :: names))
                b)
    | Pair (a, b) ->
        Format.fprintf fmt "@[(%a,@ %a)@]" (go 0 names) a (go 0 names) b
    | Fst t -> Format.fprintf fmt "%a.1" (go 11 names) t
    | Snd t -> Format.fprintf fmt "%a.2" (go 11 names) t
    | Absurd (a, h) ->
        paren_if (prec > 10) (fun fmt ->
            Format.fprintf fmt "@[absurd@ %a@ %a@]" (go 11 names) a
              (go 11 names) h)
  in
  go 0 names fmt t

let pp fmt t = pp_in [] fmt t

let to_string_in names t = Format.asprintf "%a" (pp_in names) t

let to_string t = to_string_in [] t
