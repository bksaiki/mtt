(** type of both terms and types; binder names are display hints only and are
    ignored by all algorithms (variables are de Bruijn indices) *)
type term =
  | Var of int (* de Bruijn index *)
  | Univ of int (* Type 0, Type 1, ... *)
  | Pi of string * term * term (* Π (x : A). B, B binds index 0 *)
  | Lam of string * term * term (* λ (x : A). b *)
  | App of term * term

(** [occurs k t] is true if de Bruijn index [k] appears free in [t] *)
let rec occurs k = function
  | Var i -> i = k
  | Univ _ -> false
  | Pi (_, a, b)
  | Lam (_, a, b) ->
      occurs k a || occurs (k + 1) b
  | App (f, a) -> occurs k f || occurs k a

(** [pp_in names fmt t] pretty-prints [t] using binder name hints, priming names
    that would shadow an enclosing binder; [names] supplies the names of
    enclosing binders for [t]'s free indices. Unbound indices print as [!i]. *)
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
  (* precedence: 0 = fun, 1 = arrow, 10 = application, 11 = atom *)
  let rec go prec names fmt t =
    match t with
    | Var i -> (
        match List.nth_opt names i with
        | Some x -> Format.pp_print_string fmt x
        | None -> Format.fprintf fmt "!%d" i)
    | Univ 0 -> Format.pp_print_string fmt "Type"
    | Univ i -> paren_if (prec > 10) (fun fmt -> Format.fprintf fmt "Type %d" i)
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
  in
  go 0 names fmt t

(** [pp fmt t] pretty-prints the closed term [t] *)
let pp fmt t = pp_in [] fmt t

(** [to_string_in names t] is [t] rendered via {!pp_in} *)
let to_string_in names t = Format.asprintf "%a" (pp_in names) t

(** [to_string t] is the closed term [t] rendered via {!pp} *)
let to_string t = to_string_in [] t
