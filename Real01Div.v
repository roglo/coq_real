Require Import Utf8.
Require Import Real01Add.

Theorem rm_lt_dec : ∀ x y, {(x < y)%rm} + {(x ≥ y)%rm}.
Proof.
intros x y.
unfold rm_lt, rm_ge.
remember (rm_compare x y) as cmp eqn:Hcmp .
symmetry in Hcmp.
destruct cmp; [ right | left; reflexivity | right ]; intros H; discriminate H.
Qed.

Definition rm_shift_l n x := {| rm i := x.[i+n] |}.

Fixpoint rm_div_si x y i :=
  match i with
  | O => if rm_lt_dec x y then false else true
  | S j =>
      let x := if rm_lt_dec x y then x else rm_sub x y in
      rm_div_si (rm_shift_l 1 x) y j
  end.

Definition rm_div x y = {| rm i := rm_div_si x y (i + 1) |}.
