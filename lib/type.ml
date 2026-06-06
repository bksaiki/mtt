(** type of both terms and types *)
type term =
  | Var of int (* de Bruijn index *)
  | Univ of int (* Type 0, Type 1, ... *)
  | Pi of term * term (* Π (_ : A). B, B binds index 0 *)
  | Lam of term * term (* λ (_ : A). b *)
  | App of term * term

(** [occurs k t] is true if de Bruijn index [k] appears free in [t] *)
let rec occurs k = function
  | Var i -> i = k
  | Univ _ -> false
  | Pi (a, b)
  | Lam (a, b) ->
      occurs k a || occurs (k + 1) b
  | App (f, a) -> occurs k f || occurs k a

(** [pp fmt t] pretty-prints [t], inventing names [x0], [x1], ... for binders.
    Unbound indices print as [!i]. *)
let pp fmt t =
  (* generates a fresh identifier *)
  let fresh names = "x" ^ string_of_int (List.length names) in
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
    | Pi (a, b) ->
        let x = fresh names in
        paren_if (prec > 1) (fun fmt ->
            if occurs 0 b then
              Format.fprintf fmt "@[(%s : %a) ->@ %a@]" x (go 0 names) a
                (go 1 (x :: names))
                b
            else
              Format.fprintf fmt "@[%a ->@ %a@]" (go 2 names) a
                (go 1 (x :: names))
                b)
    | Lam (a, b) ->
        let x = fresh names in
        paren_if (prec > 0) (fun fmt ->
            Format.fprintf fmt "@[fun (%s : %a) =>@ %a@]" x (go 0 names) a
              (go 0 (x :: names))
              b)
    | App (f, a) ->
        paren_if (prec > 10) (fun fmt ->
            Format.fprintf fmt "@[%a@ %a@]" (go 10 names) f (go 11 names) a)
  in
  go 0 [] fmt t

(** [to_string t] is [t] rendered via {!pp} *)
let to_string t = Format.asprintf "%a" pp t
