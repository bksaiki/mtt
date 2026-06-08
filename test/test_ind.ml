open Mtt

(* Phase 1 exercises the kernel's *computation* for inductives (eval/quote and
   the generic ι-rule) by building terms directly, before any surface syntax or
   type checking exists. Two specs serve as fixtures: a parameterless Nat and a
   parameterized List. *)

let norm t = print_endline (Type.to_string (Value.normalize t))

(* inductive Nat := zero | succ (n : Nat) *)
let nat_spec =
  { Inductive.name = "Nat"
  ; params = []
  ; sort = 1
  ; ctors =
      [ { Inductive.cname = "zero"; fields = [] }
      ; { Inductive.cname = "succ"
        ; fields =
            [ { Inductive.aname = "n"; aty = Type.Ind "Nat"; recursive = true }
            ]
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
  ; sort = 1
  ; ctors =
      [ { Inductive.cname = "nil"; fields = [] }
      ; { Inductive.cname = "cons"
        ; fields =
            [ { Inductive.aname = "head"
              ; aty = Type.Var 0 (* A *)
              ; recursive = false
              }
            ; { Inductive.aname = "tail"
              ; aty = Type.App (Type.Ind "List", Type.Var 1 (* A *))
              ; recursive = true
              }
            ]
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
  let motive = Type.Lam ("_", nat, nat) in
  let step =
    Type.Lam ("k", nat, Type.Lam ("ih", nat, succ (succ (Type.Var 0))))
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
  let motive = Type.Lam ("_", nat, nat) in
  let step = Type.Lam ("k", nat, Type.Lam ("ih", nat, Type.Var 0)) in
  let body =
    Type.App
      (Type.App (Type.App (Type.App (nat_rec, motive), zero), step), Type.Var 0)
  in
  norm (Type.Lam ("x", nat, body));
  [%expect
    {|
    fun (x : Nat) =>
    Nat.rec (fun (_ : Nat) => Nat) Nat.zero
    (fun (k : Nat) => fun (ih : Nat) => ih) x
    |}]

let%expect_test "parameterized recursor: length of a two-element list" =
  (* length A xs = List.rec A (fun _ => Nat) zero (fun h t ih => succ ih) xs,
     with the parameter A and elements stripped/recursed correctly *)
  let motive = Type.Lam ("_", Type.App (Type.Ind "List", Type.Var 0), nat) in
  let step =
    (* fun (h : A) (t : List A) (ih : Nat) => succ ih *)
    Type.Lam
      ( "h"
      , Type.Var 0
      , Type.Lam
          ( "t"
          , Type.App (Type.Ind "List", Type.Var 1)
          , Type.Lam ("ih", nat, succ (Type.Var 0)) ) )
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
      ( "A"
      , Type.Sort 1
      , Type.Lam
          ( "a"
          , Type.Var 0
          , Type.Lam ("b", Type.Var 1, length (Type.Var 2) two_elts) ) )
  in
  norm term;
  [%expect
    {| fun (A : Type) => fun (a : A) => fun (b : A) => Nat.succ (Nat.succ Nat.zero) |}]

(* --- Phase 2: type checking --- *)

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
  let motive = Type.Lam ("_", nat, nat) in
  let step =
    Type.Lam ("k", nat, Type.Lam ("ih", nat, succ (succ (Type.Var 0))))
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
    ; sort = 1
    ; ctors =
        [ { Inductive.cname = "mk"
          ; fields =
              [ { Inductive.aname = "f"
                ; aty = Type.Pi ("_", Type.Ind "Bad", Type.Ind "Bad")
                ; recursive = false
                }
              ]
          }
        ]
    }
  in
  (try Check.check_inductive Check.empty bad with
  | Check.Type_error msg -> print_endline msg);
  [%expect
    {| constructor mk: Bad may occur only as a direct recursive field, not inside Bad -> Bad (strict positivity) |}]

(* inductive PBool : Prop := pt | pf — a Prop with two constructors, so not a
   subsingleton: it may eliminate only into Prop *)
let pbool_spec =
  { Inductive.name = "PBool"
  ; params = []
  ; sort = 0
  ; ctors =
      [ { Inductive.cname = "pt"; fields = [] }
      ; { Inductive.cname = "pf"; fields = [] }
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
  ; sort = 0
  ; ctors = [ { Inductive.cname = "pstar"; fields = [] } ]
  }

let punit_ctx = Check.add_ind punit_spec Check.empty

let pstar = Type.Ctor (Inductive.ctor_head punit_spec 0)

let punit_rec = Type.Rec (Inductive.rec_head punit_spec)

let%expect_test "Prop large-elimination restriction" =
  (* a non-subsingleton Prop (two constructors) cannot eliminate into Type *)
  let into_type =
    Type.App
      ( Type.App
          ( Type.App (Type.App (pbool_rec, Type.Lam ("_", pbool, Type.Nat)), pt)
          , pt )
      , pt )
  in
  (try ignore (Check.infer pbool_ctx into_type) with
  | Check.Type_error msg -> print_endline msg);
  [%expect
    {| cannot eliminate the proposition PBool into Type: only a subsingleton (at most one constructor, all fields proofs) may eliminate large |}];
  (* but a subsingleton Prop may: PUnit.rec (fun _ => Nat) 0 pstar : Nat *)
  let big =
    Type.App
      ( Type.App
          ( Type.App (punit_rec, Type.Lam ("_", Type.Ind "PUnit", Type.Nat))
          , Type.Zero )
      , pstar )
  in
  infers punit_ctx big;
  [%expect {| Nat |}]

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
    { Inductive.name = "Bot"; params = []; sort = 0; ctors = [] }
  in
  let ctx = Check.add_ind bot_spec Check.empty in
  let ctx = Check.bind "A" (Value.Sort 1) ctx in
  let ctx = Check.bind "h1" (Value.VInd ("Bot", [])) ctx in
  let ctx = Check.bind "h2" (Value.VInd ("Bot", [])) ctx in
  let bot_rec = Type.Rec (Inductive.rec_head bot_spec) in
  (* motive (fun _ => A); A is Var 2, shifted to Var 3 under the binder *)
  let motive = Type.Lam ("_", Type.Ind "Bot", Type.Var 3) in
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
  let motive = Type.Lam ("_", nat, nat) in
  let step = Type.Lam ("k", nat, Type.Lam ("ih", nat, Type.Var 0)) in
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
