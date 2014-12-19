Require Import Utf8.
Require Import RealAdd.

Definition rm_shift_l n x := {| rm i := x.[i+n] |}.

(* mmm... should adjust x and y before *)
Fixpoint rm_div_si x y i :=
  match i with
  | O => if rm_lt_dec x y then false else true
  | S j =>
      let x := if rm_lt_dec x y then x else rm_sub x y in
      rm_div_si (rm_shift_l 1 x) y j
  end.

Definition rm_div x y = {| rm i := rm_div_si x y (i + 1) |}.
