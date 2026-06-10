(* Universe levels. Today every level in a checked term is *closed* — a [Succ^n
   Zero], i.e. a concrete [Prop]/[Type n]; the [Var]/[Max]/[IMax] cases exist so
   the representation is ready for universe polymorphism without another change
   to [Type.t]/[Value.t]. [equal]/[leq] are exact on closed levels (all the
   kernel produces today); the open-level normalizer is completeness-tested when
   level variables actually land. *)
type t =
  | Zero
  | Succ of t
  | Max of t * t
  | IMax of t * t
  | Var of int  (** a level parameter, by de Bruijn index *)

let zero = Zero

let succ l = Succ l

let of_int n =
  let rec go n acc =
    if n <= 0 then
      acc
    else
      go (n - 1) (Succ acc)
  in
  go n Zero

(* the value of a closed level, or [None] if it mentions a variable *)
let rec to_int = function
  | Zero -> Some 0
  | Succ a -> Option.map (fun n -> n + 1) (to_int a)
  | Max (a, b) -> (
      match (to_int a, to_int b) with
      | Some x, Some y -> Some (Stdlib.max x y)
      | _ -> None)
  (* [imax _ 0 = 0]: a product into a proposition is a proposition *)
  | IMax (a, b) -> (
      match to_int b with
      | Some 0 -> Some 0
      | _ -> (
          match (to_int a, to_int b) with
          | Some x, Some y -> Some (Stdlib.max x y)
          | _ -> None))
  | Var _ -> None

(* smart constructors: fully evaluate the closed case, apply the defining
   identities otherwise *)
let max a b =
  match (to_int a, to_int b) with
  | Some x, Some y -> of_int (Stdlib.max x y)
  | _ ->
      if a = b then
        a
      else
        Max (a, b)

let imax a b =
  match to_int b with
  | Some 0 -> Zero
  | Some _ -> max a b
  | None -> IMax (a, b)

let rec normalize = function
  | Zero -> Zero
  | Var _ as l -> l
  | Succ a -> Succ (normalize a)
  | Max (a, b) -> max (normalize a) (normalize b)
  | IMax (a, b) -> imax (normalize a) (normalize b)

let equal a b =
  match (to_int a, to_int b) with
  | Some x, Some y -> x = y
  | _ -> normalize a = normalize b

let leq a b =
  match (to_int a, to_int b) with
  | Some x, Some y -> x <= y
  (* best-effort on open levels (refined with level variables): u ≤ v iff max u
     v ≡ v *)
  | _ -> equal (max a b) b

let rec to_string = function
  | Zero -> "0"
  | Succ a -> (
      match to_int (Succ a) with
      | Some n -> string_of_int n
      | None -> "(" ^ to_string a ^ "+1)")
  | Max (a, b) -> Printf.sprintf "max %s %s" (to_string a) (to_string b)
  | IMax (a, b) -> Printf.sprintf "imax %s %s" (to_string a) (to_string b)
  | Var i -> "u" ^ string_of_int i
