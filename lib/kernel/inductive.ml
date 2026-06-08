(* A parameterized inductive type declaration. Parameters are shared across the
   whole definition and appear as explicit leading arguments to the former,
   every constructor, and the recursor. There are no indices yet (see the
   Inductive types section of docs/design.md). *)

type arg =
  { aname : string (* the field's binder name (display only) *)
  ; aty : Type.t (* its type, in the context [params, earlier fields] *)
  ; recursive : bool (* whether [aty] is the inductive's own type [T params] *)
  }

(* a constructor records only its *fields* (the parameters are shared and live
   on the spec); its result is always [T params] *)
type ctor =
  { cname : string
  ; fields : arg list
  }

type spec =
  { name : string
  ; params :
      (string * Type.t) list (* the parameter telescope (x1:P1)...(xm:Pm) *)
  ; sort : int (* the result sort: [T params : Sort sort] *)
  ; ctors : ctor list
  }

let nparams spec = List.length spec.params

(* the skeleton (see {!Type.ctor_head}) of the [i]-th constructor *)
let ctor_head spec i =
  let c = List.nth spec.ctors i in
  { Type.ind = spec.name
  ; cname = c.cname
  ; cindex = i
  ; carity = nparams spec + List.length c.fields
  ; nparams = nparams spec
  }

(* a record is a single-constructor inductive with no recursive fields; it gets
   field projections and definitional η *)
let is_record spec =
  match spec.ctors with
  | [ c ] -> List.for_all (fun a -> not a.recursive) c.fields
  | _ -> false

(* the skeleton (see {!Type.rec_head}) of the recursor *)
let rec_head spec =
  { Type.rind = spec.name
  ; nparams = nparams spec
  ; recs =
      List.map (fun c -> List.map (fun a -> a.recursive) c.fields) spec.ctors
  }

(* [apply spec depth] is the inductive applied to its parameters as variables,
   read in a context of [depth] binders whose outermost [nparams] are the
   parameters (p_0 outermost). This is the type the constructors return, and the
   shape a direct recursive field must have. *)
let apply spec depth =
  let m = nparams spec in
  let rec go acc j =
    if j = m then
      acc
    else
      go (Type.App (acc, Type.Var (depth - 1 - j))) (j + 1)
  in
  go (Type.Ind spec.name) 0

(* wrap [body] in the parameter telescope as Π binders *)
let pi_params spec body =
  List.fold_right (fun (x, pty) acc -> Type.Pi (x, pty, acc)) spec.params body

(* the type former's type: [(params) -> Sort sort] *)
let former_type spec = pi_params spec (Type.Sort spec.sort)

(* the [i]-th constructor's type: [(params) -> (fields) -> Ind params]. Field
   types are stored in the context [params, earlier fields], which is exactly
   where their Π binders sit, so no shifting is needed. *)
let ctor_type spec i =
  let c = List.nth spec.ctors i in
  let result = apply spec (nparams spec + List.length c.fields) in
  pi_params spec
    (List.fold_right
       (fun a acc -> Type.Pi (a.aname, a.aty, acc))
       c.fields result)

(* whether the inductive [name] occurs anywhere in [t]; the positivity check
   uses it to reject the inductive appearing in a non-recursive field *)
let rec occurs name (t : Type.t) =
  match t with
  | Ind n -> String.equal n name
  | Ctor h -> String.equal h.ind name
  | Rec h -> String.equal h.rind name
  | Var _
  | Sort _
  | Refl ->
      false
  | Fst a
  | Snd a
  | Proj (_, a)
  | Inl a
  | Inr a ->
      occurs name a
  | Pi (_, a, b)
  | Lam (_, a, b)
  | Sigma (_, a, b)
  | App (a, b)
  | Pair (a, b)
  | Sum (a, b) ->
      occurs name a || occurs name b
  | Eq (a, b, c)
  | J (a, b, c) ->
      occurs name a || occurs name b || occurs name c
  | Case (a, b, c, d) ->
      occurs name a || occurs name b || occurs name c || occurs name d
