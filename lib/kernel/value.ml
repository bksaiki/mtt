type t =
  | Sort of int
  | Pi of Type.icit * string * t * closure
  | Lam of Type.icit * string * t * closure
  | Eq of t * t * t
  | Refl
  (* an inductive type former applied to its parameters (a type once the
     parameters are complete; a type-returning function while partial) *)
  | VInd of string * t list
  (* a constructor applied to a spine of arguments (canonical data once
     saturated; a constructor function while partial) *)
  | VCtor of Type.ctor_head * t list
  (* a recursor accumulating its arguments [params @ motive :: minors @ [major]]
     until saturated, when it fires ι (see [vrec]) *)
  | VRec of Type.rec_head * t list
  | Neutral of neutral

and neutral =
  | Var of int (* de Bruijn level *)
  | Meta of int (* a metavariable head, by id; flexible until solved *)
  | App of neutral * t
  | Proj of int * neutral (* a stuck record field projection *)
  | J of t * t * neutral (* a stuck J: motive, diagonal, stuck proof *)
  | Rec of Type.rec_head * t list * neutral
(* a stuck inductive recursion: the recursor skeleton, the arguments before the
   major ([params @ motive :: minors]), and the stuck major *)

and closure =
  { env : env
  ; body : Type.t
  }

and env = t list

exception Not_a_function

let rec eval env t =
  match t with
  | Type.Var i -> List.nth env i
  (* a metavariable is inert in the kernel: it evaluates to a stuck head and is
     never solved here. The frontend ({!Meta}) owns solutions and zonks them
     away, so a meta never reaches a final {!Check}. *)
  | Type.Meta i -> Neutral (Meta i)
  | Type.Sort i -> Sort i
  | Type.Pi (i, x, a, b) -> Pi (i, x, eval env a, { env; body = b })
  | Type.Lam (i, x, a, b) -> Lam (i, x, eval env a, { env; body = b })
  | Type.App (f, a) -> apply (eval env f) (eval env a)
  | Type.Proj (i, t) -> vproj i (eval env t)
  | Type.Eq (a, x, y) -> Eq (eval env a, eval env x, eval env y)
  | Type.Refl -> Refl
  | Type.J (p, d, pr) -> vj (eval env p) (eval env d) (eval env pr)
  (* inductive heads start empty and accumulate their arguments via [apply] *)
  | Type.Ind name -> VInd (name, [])
  | Type.Ctor h -> VCtor (h, [])
  | Type.Rec h -> VRec (h, [])

(* β-reduction: (fun (x : A) => b) a ≡ b[a/x]. The substitution is just
   evaluating the closure body in an extended environment: no term-level
   substitution, no index shifting. Stuck applications (head is a variable)
   accumulate as neutral spines instead. *)
and apply f a =
  match f with
  | Lam (_, _, _, c) -> apply_closure c a
  | Neutral n -> Neutral (App (n, a))
  (* inductive heads accumulate arguments; a saturated recursor fires ι *)
  | VInd (name, args) -> VInd (name, args @ [ a ])
  | VCtor (h, args) -> VCtor (h, args @ [ a ])
  | VRec (h, args) ->
      let args = args @ [ a ] in
      (* params, then the motive, one minor premise per constructor, the
         major *)
      let needed = h.Type.nparams + 1 + List.length h.Type.recs + 1 in
      if List.length args < needed then
        VRec (h, args)
      else
        vrec h args
  | _ -> raise Not_a_function

and apply_closure { env; body } a = eval (a :: env) body

(* split [l] into its first [n] elements and the rest *)
and split_at n l = (List.take n l, List.drop n l)

(* ι-reduction for the generic recursor, on the saturated argument list [params
   @ motive :: minors @ [major]]. On a constructor it applies that constructor's
   minor premise to the constructor's fields, inserting after each recursive
   field its induction hypothesis (the recursor called on that field); a stuck
   major freezes the whole recursion as a neutral frame. Terminates by
   descending on the structurally smaller recursive fields. *)
and vrec h args =
  let params, rest = split_at h.Type.nparams args in
  let motive, rest =
    match rest with
    | m :: r -> (m, r)
    | [] -> assert false
  in
  let minors, rest = split_at (List.length h.Type.recs) rest in
  let major =
    match rest with
    | [ m ] -> m
    | _ -> assert false
  in
  match major with
  | VCtor (ch, cargs) ->
      let minor = List.nth minors ch.Type.cindex in
      let recs = List.nth h.Type.recs ch.Type.cindex in
      (* drop the leading parameters: the minor premise abstracts only fields *)
      let _, fields = split_at h.Type.nparams cargs in
      let rec go acc fields recs =
        match (fields, recs) with
        | [], [] -> acc
        | f :: fs, r :: rs ->
            let acc = apply acc f in
            let acc =
              if r then
                (* the induction hypothesis: the recursor on the recursive
                   field *)
                apply acc (vrec h (params @ (motive :: minors) @ [ f ]))
              else
                acc
            in
            go acc fs rs
        | _ -> assert false
      in
      go minor fields recs
  | Neutral n -> Neutral (Rec (h, params @ (motive :: minors), n))
  | _ -> assert false

(* the [i]-th field projection of a record: on a constructor, the matching
   argument (skipping the [nparams] leading parameters); a stuck frame on a
   neutral *)
and vproj i = function
  | VCtor (h, args) -> List.nth args (h.nparams + i)
  | Neutral n -> Neutral (Proj (i, n))
  | _ -> assert false

(* ι-reduction: J on refl picks the diagonal case; a stuck proof freezes the
   whole elimination as a neutral frame *)
and vj p d pr =
  match pr with
  | Refl -> d
  | Neutral n -> Neutral (J (p, d, n))
  | _ -> assert false

let rec quote l v =
  match v with
  | Sort i -> Type.Sort i
  | Eq (a, x, y) -> Type.Eq (quote l a, quote l x, quote l y)
  | Refl -> Type.Refl
  | Pi (i, x, a, c) -> Type.Pi (i, x, quote l a, quote_closure l c)
  | Lam (i, x, a, c) -> Type.Lam (i, x, quote l a, quote_closure l c)
  | VInd (name, args) -> quote_spine l (Type.Ind name) args
  | VCtor (h, args) -> quote_spine l (Type.Ctor h) args
  | VRec (h, args) -> quote_spine l (Type.Rec h) args
  | Neutral n -> quote_neutral l n

(* to go under a binder, apply the closure to a fresh stuck variable *)
and quote_closure l c = quote (l + 1) (apply_closure c (Neutral (Var l)))

(* read back a head applied to a spine of value arguments *)
and quote_spine l head args =
  List.fold_left (fun t a -> Type.App (t, quote l a)) head args

and quote_neutral l = function
  (* level → index: the variable bound under k other binders, seen from under l
     binders, is index l - k - 1 *)
  | Var k -> Type.Var (l - k - 1)
  (* an unsolved meta (a solved one is unfolded by [force] in [quote]) *)
  | Meta i -> Type.Meta i
  | App (n, a) -> Type.App (quote_neutral l n, quote l a)
  | Proj (i, n) -> Type.Proj (i, quote_neutral l n)
  | J (p, d, n) -> Type.J (quote l p, quote l d, quote_neutral l n)
  | Rec (h, pre, n) ->
      (* pre = params @ motive :: minors; the stuck major closes the spine *)
      Type.App (quote_spine l (Type.Rec h) pre, quote_neutral l n)

let normalize t = quote 0 (eval [] t)
