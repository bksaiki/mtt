(* A parameterized inductive type declaration. Parameters are shared across the
   whole definition and appear as explicit leading arguments to the former,
   every constructor, and the recursor. There are no indices yet (see the
   Inductive types section of docs/design.md). *)

type arg =
  { aname : string (* the field's binder name (display only) *)
  ; aty : Type.t (* its type, in the context [params, earlier fields] *)
  ; recursive : Type.t list option
        (* [None] if not recursive; [Some idxs] if [aty] is the inductive's own
           type [Ind params idxs], recording the index instances [idxs] (in the
           context [params, earlier fields]) *)
  }

(* a constructor records its *fields* (the parameters are shared and live on the
   spec) and the index instances of its result [Ind params result_indices] (in
   the context [params, fields]); for a non-indexed type [result_indices] is
   empty and the result is just [Ind params] *)
type ctor =
  { cname : string
  ; fields : arg list
  ; result_indices : Type.t list
  }

type spec =
  { name : string
  ; params :
      (string * Type.t) list (* the parameter telescope (x1:P1)...(xm:Pm) *)
  ; indices : (string * Type.t) list
        (* the index telescope (i1:I1)...(ik:Ik), in the context [params]; empty
           for a non-indexed type *)
  ; sort : Level.t (* the result sort: [T params indices : Sort sort] *)
  ; ctors : ctor list
  }

let nparams spec = List.length spec.params

let nindices spec = List.length spec.indices

(* the skeleton (see {!Type.ctor_head}) of the [i]-th constructor; [levels] are
   the use-site level arguments (empty for a monomorphic inductive) *)
let ctor_head ?(levels = []) spec i =
  let c = List.nth spec.ctors i in
  { Type.ind = spec.name
  ; cname = c.cname
  ; cindex = i
  ; carity = nparams spec + List.length c.fields
  ; nparams = nparams spec
  ; clevels = levels
  }

(* a record is a single-constructor, non-recursive, *non-indexed* inductive; it
   gets field projections and definitional η. Indexed families (e.g. [Eq]) are
   excluded: their [VInd] spine carries indices, which the record-η path would
   mistake for parameters. *)
let is_record spec =
  match spec.ctors with
  | [ c ] ->
      spec.indices = []
      && List.for_all (fun a -> Option.is_none a.recursive) c.fields
  | _ -> false

(* the skeleton (see {!Type.rec_head}) of the recursor; [levels] are the
   use-site level arguments (empty for a monomorphic inductive) *)
let rec_head ?(levels = []) spec =
  { Type.rind = spec.name
  ; nparams = nparams spec
  ; nindices = nindices spec
  ; recs =
      List.map
        (fun c ->
          List.map
            (fun a ->
              match a.recursive with
              | None -> Type.Nonrec
              | Some idxs -> Type.Recursive idxs)
            c.fields)
        spec.ctors
  ; rlevels = levels
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
  go (Type.Ind (spec.name, [])) 0

(* wrap [body] in a telescope of explicit Π binders *)
let pi_telescope tele body =
  List.fold_right
    (fun (x, ty) acc -> Type.Pi (Type.Explicit, x, ty, acc))
    tele body

(* wrap [body] in the parameter telescope (parameters are always explicit) *)
let pi_params spec body = pi_telescope spec.params body

(* the type former's type: [(params) -> (indices) -> Sort sort] *)
let former_type spec =
  pi_params spec (pi_telescope spec.indices (Type.Sort spec.sort))

(* the [i]-th constructor's type: [(params) -> (fields) -> Ind params
   result_indices]. Field types are stored in the context [params, earlier
   fields], which is exactly where their Π binders sit, so no shifting is
   needed; the result's index instances live in [params, fields]. *)
let ctor_type spec i =
  let c = List.nth spec.ctors i in
  let result =
    List.fold_left
      (fun acc idx -> Type.App (acc, idx))
      (apply spec (nparams spec + List.length c.fields))
      c.result_indices
  in
  pi_params spec
    (List.fold_right
       (fun a acc -> Type.Pi (Type.Explicit, a.aname, a.aty, acc))
       c.fields result)

(* whether the inductive [name] occurs anywhere in [t]; the positivity check
   uses it to reject the inductive appearing in a non-recursive field *)
let rec occurs name (t : Type.t) =
  match t with
  | Ind (n, _) -> String.equal n name
  | Ctor h -> String.equal h.ind name
  | Rec h -> String.equal h.rind name
  | Var _
  | Sort _
  | Meta _ ->
      false
  | Proj (_, a) -> occurs name a
  | Pi (_, _, a, b)
  | Lam (_, _, a, b) ->
      occurs name a || occurs name b
  | App (a, b) -> occurs name a || occurs name b
