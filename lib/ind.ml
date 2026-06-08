(* A parameterized inductive type declaration. Parameters are shared across the
   whole definition and appear as explicit leading arguments to the former,
   every constructor, and the recursor. There are no indices yet (see
   docs/inductive-plan.md). *)

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
  }

(* the skeleton (see {!Type.rec_head}) of the recursor *)
let rec_head spec =
  { Type.rind = spec.name
  ; nparams = nparams spec
  ; recs =
      List.map (fun c -> List.map (fun a -> a.recursive) c.fields) spec.ctors
  }
