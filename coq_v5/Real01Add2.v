(* second version of adding reals in interval [0..1[ *)

Require Import Utf8 QArith NPeano.
Require Import Digit Real01.

Open Scope nat_scope.

Definition I_add_algo x y i := d2n (x.[i]) + d2n (y.[i]).
Arguments I_add_algo x%I y%I i%nat.

(*
Definition I_add2_i x y := z_of_u base (I_add_algo x y).
Definition I_add2 x y := {| rm := I_add2_i x y |}.
*)
