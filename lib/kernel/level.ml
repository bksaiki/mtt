(* Universe levels. Until universe polymorphism wires level variables into
   checked terms, every level the kernel produces is *closed* — a [Succ^n Zero],
   i.e. a concrete [Prop]/[Type n]. The full algebra ([Var]/[Max]/[IMax] with a
   canonicalizing [normalize], [equal], [leq], and [subst]) is implemented and
   unit-tested now (see [test/test_level.ml]) so the polymorphism stage builds
   on a settled foundation; [equal]/[leq] are sound on open levels and complete
   on the {Zero,Succ,Var,Max} fragment, with [imax] reduced wherever its second
   argument's zero-ness is decidable. *)
type t =
  | Zero
  | Succ of t
  | Max of t * t
  | IMax of t * t
  | Var of int  (** a level parameter, by de Bruijn index *)
  | LMeta of int
      (** a level metavariable, by id: an elaboration-only placeholder for an
          as-yet-unknown level argument, solved by unification and zonked away
          (the {!Meta} analogue of {!Type.Meta}). Treated as an opaque atom by
          the algebra here; it never reaches a checked term. *)

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
  | Var _
  | LMeta _ ->
      None

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

(* Canonical form, for deciding equality and [≤] of open levels. A level over
   {Zero, Succ, Var, Max} is a max of summands [atom + offset]; we read it into
   [(const, atoms)] where [const] is the constant floor (from [Zero] summands)
   and [atoms] maps each atom (a [Var], or an irreducible [IMax]) to its largest
   offset, then rebuild a deterministic [Max]-chain so structural equality
   decides level equality. [IMax] is reduced where its second argument's
   zero-ness is known ([imax _ 0 = 0], [imax a b = max a b] when [b] is nonzero
   or distributes over a [Max]); an [IMax] over a bare variable stays an opaque
   atom (compared structurally — sound, and complete enough in practice). *)
let rec normalize l =
  let const, atoms = summands l in
  let atoms = List.sort compare atoms in
  (* fold the constant floor and each [atom + offset] back into a Max chain *)
  List.fold_left
    (fun acc (atom, off) ->
      let s = succ_n off atom in
      if acc = Zero then
        s
      else
        Max (acc, s))
    (of_int const) atoms

(* [summands l] reads [l] into its constant floor and a list of [(atom, offset)]
   summands of the outer max, each atom appearing once (largest offset kept) *)
and summands l =
  (* record an atom (already normal) at [off], keeping the largest offset
     seen *)
  let add (const, atoms) atom off =
    let here, others = List.partition (fun (x, _) -> x = atom) atoms in
    let prev = List.fold_left (fun m (_, o) -> Stdlib.max m o) 0 here in
    (const, (atom, Stdlib.max prev off) :: others)
  in
  let rec go acc off = function
    | Zero -> (Stdlib.max (fst acc) off, snd acc)
    | Succ a -> go acc (off + 1) a
    | Max (a, b) -> go (go acc off a) off b
    | (Var _ | LMeta _) as a -> add acc a off
    | IMax (x, y) as a -> (
        match reduce_imax a with
        | Some a' -> go acc off a'
        (* irreducible: an atom, with its components normalized *)
        | None -> add acc (IMax (normalize x, normalize y)) off)
  in
  go (0, []) 0 l

(* reduce an [IMax a b] by the zero-ness of its second argument: [imax a 0 = 0],
   [imax a b = max a b] when [b] is definitely nonzero, and the distribution
   [imax a (max b c) = max (imax a b) (imax a c)] otherwise; [None] leaves an
   [imax a v] over a bare variable as an opaque atom. *)
and reduce_imax = function
  | IMax (a, b) -> (
      let b = normalize b in
      match to_int b with
      | Some 0 -> Some Zero
      | Some _ -> Some (max a b)
      | None -> (
          if min_value b >= 1 then
            Some (max a b)
          else
            match b with
            | Max (b1, b2) -> Some (max (imax a b1) (imax a b2))
            | _ -> None))
  | _ -> None

(* the value of [l] when every level variable is [0] — its minimum over all
   instantiations (levels are monotone in their variables), so [min_value l ≥ 1]
   certifies [l] is nonzero under every instantiation *)
and min_value = function
  | Zero -> 0
  | Succ a -> 1 + min_value a
  | Max (a, b) -> Stdlib.max (min_value a) (min_value b)
  | IMax (a, b) ->
      let mb = min_value b in
      if mb = 0 then
        0
      else
        Stdlib.max (min_value a) mb
  | Var _
  | LMeta _ ->
      0

and succ_n n l =
  if n <= 0 then
    l
  else
    Succ (succ_n (n - 1) l)

let equal a b = normalize a = normalize b

(* [a ≤ b] iff [max a b ≡ b] *)
let leq a b = equal (max a b) b

(* substitute the level arguments [args] for the level variables [Var 0…] *)
let rec subst args = function
  | Zero -> Zero
  | Succ a -> succ (subst args a)
  | Max (a, b) -> max (subst args a) (subst args b)
  | IMax (a, b) -> imax (subst args a) (subst args b)
  | Var i -> (
      match List.nth_opt args i with
      | Some l -> l
      | None -> Var i)
  (* a level meta is solved separately (by the elaborator), not by level-param
     instantiation *)
  | LMeta _ as l -> l

(* whether [l] mentions any level metavariable (used to keep an unsolved one out
   of a checked term) *)
let rec has_meta = function
  | Zero -> false
  | Succ a -> has_meta a
  | Max (a, b)
  | IMax (a, b) ->
      has_meta a || has_meta b
  | Var _ -> false
  | LMeta _ -> true

let rec to_string = function
  | Zero -> "0"
  | Succ a -> (
      match to_int (Succ a) with
      | Some n -> string_of_int n
      | None -> "(" ^ to_string a ^ "+1)")
  | Max (a, b) -> Printf.sprintf "max %s %s" (to_string a) (to_string b)
  | IMax (a, b) -> Printf.sprintf "imax %s %s" (to_string a) (to_string b)
  | Var i -> "u" ^ string_of_int i
  | LMeta i -> "?u" ^ string_of_int i
