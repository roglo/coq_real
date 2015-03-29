(* second version of adding reals in interval [0..1[ *)

Require Import Utf8 QArith NPeano.
Require Import Summation.
Require Import Digit Real01.

Open Scope nat_scope.

Fixpoint int_pow a b :=
  match b with
  | 0 => 1
  | S b1 => a * int_pow a b1
  end.

Definition I_add_algo x y i := d2n (x.[i]) + d2n (y.[i]).
Arguments I_add_algo x%I y%I i%nat.

Definition z_of_u b n u i :=
  n2d (Σ (k = 0, n), u (i + k) * int_pow b (n - k) / int_pow b n mod b).

Definition I_add2_i x y := z_of_u base 2 (I_add_algo x y).
Definition I_add2 x y := {| rm := I_add2_i x y |}.
