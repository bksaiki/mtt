open Level

let b x = print_string (string_of_bool x)

(* a few level variables *)
let u = Var 0

let v = Var 1

let%expect_test "closed levels: equality and ≤ are integer compare" =
  b (equal (of_int 3) (of_int 3));
  b (equal (of_int 3) (of_int 2));
  b (leq (of_int 2) (of_int 3));
  b (leq (of_int 3) (of_int 2));
  b (equal (max (of_int 2) (of_int 5)) (of_int 5));
  b (equal (imax (of_int 4) Zero) Zero);
  [%expect {| truefalsetruefalsetruetrue |}]

let%expect_test "max is commutative, idempotent, absorbing" =
  b (equal (max u v) (max v u));
  b (equal (max u u) u);
  (* a summand absorbs a lower-offset copy of the same atom *)
  b (equal (max u (succ u)) (succ u));
  b (equal (max u (succ v)) (max (succ v) u));
  (* distinct atoms are both kept *)
  b (equal (max u v) u);
  [%expect {| truetruetruetruefalse |}]

let%expect_test "≤ on open levels" =
  b (leq u (max u v));
  b (leq u (succ u));
  b (leq u v);
  b (leq (max u v) (max v u));
  [%expect {| truetruefalsetrue |}]

let%expect_test "imax reduces when the second argument's zero-ness is known" =
  (* imax _ 0 = 0; imax a (succ b) = max a (succ b) *)
  b (equal (imax u Zero) Zero);
  b (equal (imax u (succ v)) (max u (succ v)));
  (* a known-nonzero second argument (floor ≥ 1) collapses imax to max *)
  b (equal (imax u (max v (succ Zero))) (max (max u v) (succ Zero)));
  (* over two bare variables it distributes into irreducible imax atoms *)
  b (equal (imax u (max v v)) (imax u v));
  (* imax over a bare variable stays irreducible but compares structurally *)
  b (equal (imax u v) (imax u v));
  b (equal (imax u v) (imax v u));
  [%expect {| truetruetruetruetruefalse |}]

let%expect_test "subst instantiates level variables" =
  (* [u ↦ 2]: max u 1 ⇒ max 2 1 = 2 *)
  b (equal (subst [ of_int 2 ] (max u (succ Zero))) (of_int 2));
  (* [u ↦ v]: max u u ⇒ v *)
  b (equal (subst [ v ] (max u u)) v);
  (* a variable beyond the argument list is left in place *)
  b (equal (subst [ of_int 0 ] v) v);
  [%expect {| truetruetrue |}]
