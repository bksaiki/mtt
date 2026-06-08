open Mtt

(* Phase 1 exercises the kernel's *computation* for inductives (eval/quote and
   the generic ι-rule) by building terms directly, before any surface syntax or
   type checking exists. Two specs serve as fixtures: a parameterless Nat and a
   parameterized List. *)

let norm t = print_endline (Type.to_string (Value.normalize t))

(* inductive Nat := zero | succ (n : Nat) *)
let nat_spec =
  { Ind.name = "Nat"
  ; params = []
  ; sort = 1
  ; ctors =
      [ { Ind.cname = "zero"; fields = [] }
      ; { Ind.cname = "succ"
        ; fields =
            [ { Ind.aname = "n"; aty = Type.Ind "Nat"; recursive = true } ]
        }
      ]
  }

let nat = Type.Ind "Nat"

let zero = Type.Ctor (Ind.ctor_head nat_spec 0)

let succ n = Type.App (Type.Ctor (Ind.ctor_head nat_spec 1), n)

let nat_rec = Type.Rec (Ind.rec_head nat_spec)

(* a numeral as [succ (succ ... zero)] *)
let rec numeral k =
  if k = 0 then
    zero
  else
    succ (numeral (k - 1))

(* inductive List (A : Type) := nil | cons (head : A) (tail : List A) *)
let list_spec =
  { Ind.name = "List"
  ; params = [ ("A", Type.Sort 1) ]
  ; sort = 1
  ; ctors =
      [ { Ind.cname = "nil"; fields = [] }
      ; { Ind.cname = "cons"
        ; fields =
            [ { Ind.aname = "head"
              ; aty = Type.Var 0 (* A *)
              ; recursive = false
              }
            ; { Ind.aname = "tail"
              ; aty = Type.App (Type.Ind "List", Type.Var 1 (* A *))
              ; recursive = true
              }
            ]
        }
      ]
  }

let nil a = Type.App (Type.Ctor (Ind.ctor_head list_spec 0), a)

let cons a h t =
  Type.App (Type.App (Type.App (Type.Ctor (Ind.ctor_head list_spec 1), a), h), t)

let list_rec = Type.Rec (Ind.rec_head list_spec)

let%expect_test "constructors are canonical and print by name" =
  norm zero;
  [%expect {| zero |}];
  norm (numeral 3);
  [%expect {| succ (succ (succ zero)) |}]

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
  [%expect {| succ (succ (succ (succ zero))) |}];
  norm (double zero);
  [%expect {| zero |}]

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
    Nat.rec (fun (_ : Nat) => Nat) zero (fun (k : Nat) => fun (ih : Nat) => ih) x
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
    {| fun (A : Type) => fun (a : A) => fun (b : A) => succ (succ zero) |}]
