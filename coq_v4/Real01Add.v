(* addition modulo 1 in I = [0..1] ⊂ ℝ *)

Require Import Utf8 QArith NPeano.
Require Import Real01.

Open Scope nat_scope.

Definition I_add_algo x y := {| sn i := d2n (x.[i]) + d2n (y.[i]) |}.
Definition I_add_i x y i := n2d (sn (I_propag_carry 1 (I_add_algo x y)) i).
Definition I_add x y := {| rm := I_add_i x y |}.

Arguments I_add_algo x%I y%I.
Arguments I_add_i x%I y%I i%nat.
Arguments I_add x%I y%I.

Notation "x + y" := (I_add x y) : I_scope.

(* commutativity *)

Theorem I_add_i_comm : ∀ x y i, I_add_i x y i = I_add_i y x i.
Proof.
intros x y i.
unfold I_add_i; f_equal.
unfold I_propag_carry, propag_carry_once.
remember modulo as f.
remember div as g; simpl; subst f g.
f_equal; rewrite Nat.add_comm; reflexivity.
Qed.

Theorem I_add_comm : ∀ x y, I_eq_ext (x + y) (y + x).
Proof.
intros x y.
unfold I_eq_ext; simpl; intros i.
apply I_add_i_comm.
Qed.
