(* the inductive machinery lives in the kernel, so this suite uses the top-level
   kernel modules (Type, Value, Check, Inductive) directly *)

(* These first tests exercise the kernel's *computation* for inductives
   (eval/quote and the generic ι-rule) by building core terms directly, with no
   surface syntax or type checking involved. Two specs serve as fixtures: a
   parameterless Nat and a parameterized List. *)

let norm t = print_endline (Type.to_string (Value.normalize t))

(* inductive Nat := zero | succ (n : Nat) *)
let nat_spec =
  { Inductive.name = "Nat"
  ; params = []
  ; indices = []
  ; sort = 1
  ; ctors =
      [ { Inductive.cname = "zero"; fields = []; result_indices = [] }
      ; { Inductive.cname = "succ"
        ; fields =
            [ { Inductive.aname = "n"
              ; aty = Type.Ind "Nat"
              ; recursive = Some []
              }
            ]
        ; result_indices = []
        }
      ]
  }

let nat = Type.Ind "Nat"

let zero = Type.Ctor (Inductive.ctor_head nat_spec 0)

let succ n = Type.App (Type.Ctor (Inductive.ctor_head nat_spec 1), n)

let nat_rec = Type.Rec (Inductive.rec_head nat_spec)

(* a numeral as [succ (succ ... zero)] *)
let rec numeral k =
  if k = 0 then
    zero
  else
    succ (numeral (k - 1))

(* inductive List (A : Type) := nil | cons (head : A) (tail : List A) *)
let list_spec =
  { Inductive.name = "List"
  ; params = [ ("A", Type.Sort 1) ]
  ; indices = []
  ; sort = 1
  ; ctors =
      [ { Inductive.cname = "nil"; fields = []; result_indices = [] }
      ; { Inductive.cname = "cons"
        ; fields =
            [ { Inductive.aname = "head"
              ; aty = Type.Var 0 (* A *)
              ; recursive = None
              }
            ; { Inductive.aname = "tail"
              ; aty = Type.App (Type.Ind "List", Type.Var 1 (* A *))
              ; recursive = Some []
              }
            ]
        ; result_indices = []
        }
      ]
  }

let nil a = Type.App (Type.Ctor (Inductive.ctor_head list_spec 0), a)

let cons a h t =
  Type.App
    (Type.App (Type.App (Type.Ctor (Inductive.ctor_head list_spec 1), a), h), t)

let list_rec = Type.Rec (Inductive.rec_head list_spec)

let%expect_test "constructors are canonical and print by name" =
  norm zero;
  [%expect {| Nat.zero |}];
  norm (numeral 3);
  [%expect {| Nat.succ (Nat.succ (Nat.succ Nat.zero)) |}]

let%expect_test "recursor reduces on a constructor (double via Nat.rec)" =
  (* double n = natrec (fun _ => Nat) zero (fun k ih => succ (succ ih)) n *)
  let motive = Type.Lam (Type.Explicit, "_", nat, nat) in
  let step =
    Type.Lam
      ( Type.Explicit
      , "k"
      , nat
      , Type.Lam (Type.Explicit, "ih", nat, succ (succ (Type.Var 0))) )
  in
  let double n =
    Type.App (Type.App (Type.App (Type.App (nat_rec, motive), zero), step), n)
  in
  norm (double (numeral 2));
  [%expect {| Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))) |}];
  norm (double zero);
  [%expect {| Nat.zero |}]

let%expect_test "a recursor on a stuck variable stays neutral" =
  (* fun (x : Nat) => natrec (fun _ => Nat) zero (fun k ih => ih) x *)
  let motive = Type.Lam (Type.Explicit, "_", nat, nat) in
  let step =
    Type.Lam
      (Type.Explicit, "k", nat, Type.Lam (Type.Explicit, "ih", nat, Type.Var 0))
  in
  let body =
    Type.App
      (Type.App (Type.App (Type.App (nat_rec, motive), zero), step), Type.Var 0)
  in
  norm (Type.Lam (Type.Explicit, "x", nat, body));
  [%expect
    {|
    fun (x : Nat) =>
    Nat.rec (fun (_ : Nat) => Nat) Nat.zero
    (fun (k : Nat) => fun (ih : Nat) => ih) x
    |}]

let%expect_test "parameterized recursor: length of a two-element list" =
  (* length A xs = List.rec A (fun _ => Nat) zero (fun h t ih => succ ih) xs,
     with the parameter A and elements stripped/recursed correctly *)
  let motive =
    Type.Lam (Type.Explicit, "_", Type.App (Type.Ind "List", Type.Var 0), nat)
  in
  let step =
    (* fun (h : A) (t : List A) (ih : Nat) => succ ih *)
    Type.Lam
      ( Type.Explicit
      , "h"
      , Type.Var 0
      , Type.Lam
          ( Type.Explicit
          , "t"
          , Type.App (Type.Ind "List", Type.Var 1)
          , Type.Lam (Type.Explicit, "ih", nat, succ (Type.Var 0)) ) )
  in
  let length a xs =
    Type.App (Type.App (Type.App (Type.App (list_rec, a), motive), zero), step)
    |> fun f -> Type.App (f, xs)
  in
  (* fun (A : Type) (a b : A) => length A (cons A a (cons A b (nil A))) *)
  let a = Type.Var 2 and x = Type.Var 1 and y = Type.Var 0 in
  let two_elts = cons a x (cons a y (nil a)) in
  let term =
    Type.Lam
      ( Type.Explicit
      , "A"
      , Type.Sort 1
      , Type.Lam
          ( Type.Explicit
          , "a"
          , Type.Var 0
          , Type.Lam
              (Type.Explicit, "b", Type.Var 1, length (Type.Var 2) two_elts) )
      )
  in
  norm term;
  [%expect
    {| fun (A : Type) => fun (a : A) => fun (b : A) => Nat.succ (Nat.succ Nat.zero) |}]

(* --- type checking --- *)

let sig_ctx = Check.add_ind list_spec (Check.add_ind nat_spec Check.empty)

let infers ctx t = print_endline (Check.show ctx (Check.infer ctx t))

let%expect_test "former and constructors infer their derived types" =
  infers sig_ctx nat;
  [%expect {| Type |}];
  infers sig_ctx zero;
  [%expect {| Nat |}];
  infers sig_ctx (succ zero);
  [%expect {| Nat |}];
  (* a bare constructor is a function *)
  infers sig_ctx (Type.Ctor (Inductive.ctor_head nat_spec 1));
  [%expect {| Nat -> Nat |}];
  (* the parameterized former and a constructor *)
  infers sig_ctx (Type.Ind "List");
  [%expect {| Type -> Type |}];
  infers sig_ctx (Type.Ctor (Inductive.ctor_head list_spec 1));
  [%expect {| (A : Type) -> A -> List A -> List A |}]

let%expect_test "well-formed declarations pass check_inductive" =
  Check.check_inductive Check.empty nat_spec;
  Check.check_inductive Check.empty list_spec;
  print_endline "ok";
  [%expect {| ok |}]

let%expect_test "a recursor application infers P major" =
  let motive = Type.Lam (Type.Explicit, "_", nat, nat) in
  let step =
    Type.Lam
      ( Type.Explicit
      , "k"
      , nat
      , Type.Lam (Type.Explicit, "ih", nat, succ (succ (Type.Var 0))) )
  in
  let double n =
    Type.App (Type.App (Type.App (Type.App (nat_rec, motive), zero), step), n)
  in
  infers sig_ctx (double (numeral 2));
  [%expect {| Nat |}]

let%expect_test "strict positivity rejects a non-recursive occurrence" =
  (* inductive Bad := mk : (Bad -> Bad) -> Bad — Bad left of an arrow *)
  let bad =
    { Inductive.name = "Bad"
    ; params = []
    ; indices = []
    ; sort = 1
    ; ctors =
        [ { Inductive.cname = "mk"
          ; fields =
              [ { Inductive.aname = "f"
                ; aty =
                    Type.Pi (Type.Explicit, "_", Type.Ind "Bad", Type.Ind "Bad")
                ; recursive = None
                }
              ]
          ; result_indices = []
          }
        ]
    }
  in
  (try Check.check_inductive Check.empty bad with
  | Error.Type_error frags ->
      print_endline (Mtt.Notation.render_error Mtt.Notation.empty frags));
  [%expect
    {| constructor mk: Bad may occur only as a direct recursive field, not inside Bad -> Bad (strict positivity) |}]

(* inductive PBool : Prop := pt | pf — a Prop with two constructors, so not a
   subsingleton: it may eliminate only into Prop *)
let pbool_spec =
  { Inductive.name = "PBool"
  ; params = []
  ; indices = []
  ; sort = 0
  ; ctors =
      [ { Inductive.cname = "pt"; fields = []; result_indices = [] }
      ; { Inductive.cname = "pf"; fields = []; result_indices = [] }
      ]
  }

let pbool_ctx = Check.add_ind pbool_spec Check.empty

let pbool = Type.Ind "PBool"

let pt = Type.Ctor (Inductive.ctor_head pbool_spec 0)

let pbool_rec = Type.Rec (Inductive.rec_head pbool_spec)

(* inductive PUnit : Prop := pstar — one constructor, no fields: a subsingleton,
   so (like Empty/Eq) it may eliminate into any sort *)
let punit_spec =
  { Inductive.name = "PUnit"
  ; params = []
  ; indices = []
  ; sort = 0
  ; ctors = [ { Inductive.cname = "pstar"; fields = []; result_indices = [] } ]
  }

let punit_ctx = Check.add_ind punit_spec Check.empty

let pstar = Type.Ctor (Inductive.ctor_head punit_spec 0)

let punit_rec = Type.Rec (Inductive.rec_head punit_spec)

let%expect_test "Prop large-elimination restriction" =
  (* a non-subsingleton Prop (two constructors) cannot eliminate into Type *)
  let into_type =
    Type.App
      ( Type.App
          ( Type.App
              ( Type.App
                  (pbool_rec, Type.Lam (Type.Explicit, "_", pbool, Type.Sort 1))
              , pt )
          , pt )
      , pt )
  in
  (try ignore (Check.infer pbool_ctx into_type) with
  | Error.Type_error frags ->
      print_endline (Mtt.Notation.render_error Mtt.Notation.empty frags));
  [%expect
    {| cannot eliminate the proposition PBool into Type 1: only a subsingleton (at most one constructor, all fields proofs) may eliminate large |}];
  (* but a subsingleton Prop may: PUnit.rec (fun _ => Type) Prop pstar : Type *)
  let big =
    Type.App
      ( Type.App
          ( Type.App
              ( punit_rec
              , Type.Lam (Type.Explicit, "_", Type.Ind "PUnit", Type.Sort 1) )
          , Type.Sort 0 )
      , pstar )
  in
  infers punit_ctx big;
  [%expect {| Type |}]

let conv_str ctx ty v1 v2 =
  if Check.conv ctx ty v1 v2 then
    "equal"
  else
    "not equal"

let%expect_test "a stuck recursor on a Prop scrutinee ignores the proof" =
  (* Bot : Prop with no constructors (an Empty); Bot.rec is ex falso. Two stuck
     eliminations of distinct proofs h1, h2 : Bot into a *Type* motive A are
     definitionally equal — the proofs are irrelevant, even though A is not a
     Prop so result-level irrelevance does not apply. This is what subsumes the
     hardcoded `absurd`. *)
  let bot_spec =
    { Inductive.name = "Bot"; params = []; indices = []; sort = 0; ctors = [] }
  in
  let ctx = Check.add_ind bot_spec Check.empty in
  let ctx = Check.bind "A" (Value.Sort 1) ctx in
  let ctx = Check.bind "h1" (Value.VInd ("Bot", [])) ctx in
  let ctx = Check.bind "h2" (Value.VInd ("Bot", [])) ctx in
  let bot_rec = Type.Rec (Inductive.rec_head bot_spec) in
  (* motive (fun _ => A); A is Var 2, shifted to Var 3 under the binder *)
  let motive = Type.Lam (Type.Explicit, "_", Type.Ind "Bot", Type.Var 3) in
  let elim major = Type.App (Type.App (bot_rec, motive), major) in
  let v1 =
    Value.eval ctx.Check.env (elim (Type.Var 1))
    (* h1 *)
  in
  let v2 =
    Value.eval ctx.Check.env (elim (Type.Var 0))
    (* h2 *)
  in
  let a = Value.eval ctx.Check.env (Type.Var 2) in
  print_endline (conv_str ctx a v1 v2);
  [%expect {| equal |}]

let%expect_test "a stuck recursor on a non-Prop scrutinee compares it" =
  (* the same shape on Nat (a Type): distinct scrutinees x, y are relevant, so
     the eliminations are not equal *)
  let ctx = Check.add_ind nat_spec Check.empty in
  let ctx = Check.bind "x" (Value.VInd ("Nat", [])) ctx in
  let ctx = Check.bind "y" (Value.VInd ("Nat", [])) ctx in
  let motive = Type.Lam (Type.Explicit, "_", nat, nat) in
  let step =
    Type.Lam
      (Type.Explicit, "k", nat, Type.Lam (Type.Explicit, "ih", nat, Type.Var 0))
  in
  let elim major =
    Type.App
      (Type.App (Type.App (Type.App (nat_rec, motive), zero), step), major)
  in
  let v1 =
    Value.eval ctx.Check.env (elim (Type.Var 1))
    (* x *)
  in
  let v2 =
    Value.eval ctx.Check.env (elim (Type.Var 0))
    (* y *)
  in
  print_endline (conv_str ctx (Value.eval ctx.Check.env nat) v1 v2);
  [%expect {| not equal |}]

(* --- records: projections + definitional η --- *)

(* inductive DPair (A : Type) (B : A -> Type) : Type := mk : (a : A) -> B a ->
   DPair A B a single-constructor non-recursive inductive, i.e. a (dependent)
   record *)
let dpair_spec =
  { Inductive.name = "DPair"
  ; params =
      [ ("A", Type.Sort 1)
      ; ("B", Type.Pi (Type.Explicit, "_", Type.Var 0, Type.Sort 1))
      ]
  ; indices = []
  ; sort = 1
  ; ctors =
      [ { Inductive.cname = "mk"
        ; fields =
            [ { Inductive.aname = "a"
              ; aty = Type.Var 1 (* A *)
              ; recursive = None
              }
            ; { Inductive.aname = "b"
              ; aty = Type.App (Type.Var 1 (* B *), Type.Var 0 (* a *))
              ; recursive = None
              }
            ]
        ; result_indices = []
        }
      ]
  }

let dmk = Type.Ctor (Inductive.ctor_head dpair_spec 0)

(* the components are types: fun _ : Type => Type, with Prop and Type as two
   distinct elements (an arbitrary type-with-elements; the builtin Nat once
   played this role) *)
let ty_fam = Type.Lam (Type.Explicit, "_", Type.Sort 1, Type.Sort 1)

(* mk Type (fun _ => Type) a b : DPair Type (fun _ => Type) *)
let dmk_ty a b =
  Type.App (Type.App (Type.App (Type.App (dmk, Type.Sort 1), ty_fam), a), b)

let%expect_test "record projection computes (ι)" =
  norm (Type.Proj (0, dmk_ty (Type.Sort 0) (Type.Sort 1)));
  [%expect {| Prop |}];
  norm (Type.Proj (1, dmk_ty (Type.Sort 0) (Type.Sort 1)));
  [%expect {| Type |}]

let%expect_test "record η: a value equals the tuple of its projections" =
  let ctx = Check.add_ind dpair_spec Check.empty in
  let dty =
    Value.eval [] (Type.App (Type.App (Type.Ind "DPair", Type.Sort 1), ty_fam))
  in
  let ctx = Check.bind "x" dty ctx in
  let xv = Value.eval ctx.Check.env (Type.Var 0) in
  (* mk Type (fun _ => Type) x.1 x.2 *)
  let expanded =
    Value.eval ctx.Check.env
      (Type.App
         ( Type.App
             ( Type.App (Type.App (dmk, Type.Sort 1), ty_fam)
             , Type.Proj (0, Type.Var 0) )
         , Type.Proj (1, Type.Var 0) ))
  in
  print_endline (conv_str ctx dty xv expanded);
  [%expect {| equal |}];
  (* but a neutral is not equal to an arbitrary pair *)
  let other = Value.eval ctx.Check.env (dmk_ty (Type.Sort 0) (Type.Sort 0)) in
  print_endline (conv_str ctx dty xv other);
  [%expect {| not equal |}]

(* a 0-field record (Unit-like): η makes any two values equal *)
let urec_spec =
  { Inductive.name = "URec"
  ; params = []
  ; indices = []
  ; sort = 1
  ; ctors = [ { Inductive.cname = "u"; fields = []; result_indices = [] } ]
  }

let%expect_test "0-field record: any two values are equal (Unit-η)" =
  let ctx = Check.add_ind urec_spec Check.empty in
  let ctx = Check.bind "r1" (Value.VInd ("URec", [])) ctx in
  let ctx = Check.bind "r2" (Value.VInd ("URec", [])) ctx in
  let r1 = Value.eval ctx.Check.env (Type.Var 1) in
  let r2 = Value.eval ctx.Check.env (Type.Var 0) in
  print_endline (conv_str ctx (Value.VInd ("URec", [])) r1 r2);
  [%expect {| equal |}]

(* === Indexed families ===

   [Vec], the canonical indexed family, exercises what parameters cannot: a
   per-constructor result index, and a recursive field ([v : Vec A k]) sitting
   at a *different* index than the result ([Vec A (succ k)]). The recursor's ι
   rule must recover that field index [k] to form the induction hypothesis, so
   computing a vector's length is the real test of the index machinery.

   inductive Vec (A : Type) : Nat -> Type := | vnil : Vec A 0 | vcons : (k :
   Nat) -> A -> Vec A k -> Vec A (succ k) *)
let vec_spec =
  { Inductive.name = "Vec"
  ; params = [ ("A", Type.Sort 1) ]
  ; indices = [ ("n", nat) ]
  ; sort = 1
  ; ctors =
      [ { Inductive.cname = "vnil"; fields = []; result_indices = [ zero ] }
      ; { Inductive.cname = "vcons"
        ; fields =
            [ { Inductive.aname = "k"; aty = nat; recursive = None }
            ; { Inductive.aname = "a"
              ; aty = Type.Var 1 (* A *)
              ; recursive = None
              }
            ; { Inductive.aname = "v"
              ; aty =
                  Type.App
                    ( Type.App (Type.Ind "Vec", Type.Var 2 (* A *))
                    , Type.Var 1 (* k *) )
              ; recursive = Some [ Type.Var 1 (* k *) ]
              }
            ]
        ; result_indices = [ succ (Type.Var 2 (* k *)) ]
        }
      ]
  }

let vec_ctx = Check.add_ind vec_spec sig_ctx

let vnil a = Type.App (Type.Ctor (Inductive.ctor_head vec_spec 0), a)

(* vcons A k x v *)
let vcons a k x v =
  let c = Type.Ctor (Inductive.ctor_head vec_spec 1) in
  Type.App (Type.App (Type.App (Type.App (c, a), k), x), v)

let vec_rec = Type.Rec (Inductive.rec_head vec_spec)

(* a length recursor at the constant motive [fun n v => Nat]: vnil ↦ 0, vcons k
   a v ih ↦ succ ih (the IH [ih] is the recursor on the tail [v : Vec A k]) *)
let vec_length n vec =
  let vec_ty m = Type.App (Type.App (Type.Ind "Vec", nat), m) in
  let motive =
    Type.Lam
      ( Type.Explicit
      , "n"
      , nat
      , Type.Lam (Type.Explicit, "v", vec_ty (Type.Var 0), nat) )
  in
  let vcons_case =
    Type.Lam
      ( Type.Explicit
      , "k"
      , nat
      , Type.Lam
          ( Type.Explicit
          , "a"
          , nat
          , Type.Lam
              ( Type.Explicit
              , "v"
              , vec_ty (Type.Var 1 (* k *))
              , Type.Lam (Type.Explicit, "ih", nat, succ (Type.Var 0 (* ih *)))
              ) ) )
  in
  List.fold_left
    (fun f a -> Type.App (f, a))
    vec_rec
    [ nat; motive; zero (* vnil case *); vcons_case; n; vec ]

(* a Vec Nat 2: vcons 1 7 (vcons 0 5 vnil) *)
let vec2 =
  vcons nat (numeral 1) (numeral 7) (vcons nat zero (numeral 5) (vnil nat))

let%expect_test "indexed Vec: declaration is well-formed" =
  Check.check_inductive sig_ctx vec_spec;
  print_endline "ok";
  [%expect {| ok |}]

let%expect_test
    "indexed Vec: the recursor computes a length (ι passes the field index)" =
  norm (vec_length (numeral 2) vec2);
  [%expect {| Nat.succ (Nat.succ Nat.zero) |}]

let%expect_test "indexed Vec: a recursor application is typed at P index major"
    =
  infers vec_ctx (vec_length (numeral 2) vec2);
  [%expect {| Nat |}]
