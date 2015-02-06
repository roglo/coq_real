(* addition modulo 1 in I = [0..1] ⊂ ℝ *)

Require Import Utf8 QArith NPeano.
Require Import Real01.

Open Scope nat_scope.

Definition I_add_algo x y := {| sn i := d2n (x.[i]) + d2n (y.[i]) |}.
Definition I_add_i x y i := n2d (sn (propag_carry_once (I_add_algo x y)) i).
Definition I_add x y := {| rm := I_add_i x y |}.

Arguments I_add_algo x%I y%I.
Arguments I_add_i x%I y%I i%nat.
Arguments I_add x%I y%I.

Notation "x + y" := (I_add x y) : I_scope.

(* commutativity *)

Theorem I_add_i_comm : ∀ x y i, I_add_i x y i = I_add_i y x i.
Proof.
intros x y i.
unfold I_add_i; simpl; f_equal.
f_equal; rewrite Nat.add_comm; reflexivity.
Qed.

Theorem I_add_comm : ∀ x y, I_eq_ext (x + y) (y + x).
Proof.
intros x y.
unfold I_eq_ext; simpl; intros i.
apply I_add_i_comm.
Qed.

(* neutral element *)

Theorem I_add_0_r : ∀ x, I_eq_ext (x + 0) x.
Proof.
intros x.
unfold I_eq_ext; simpl; intros i.
unfold I_add_i; simpl.
destruct (x.[i]), (x.[S i]); reflexivity.
Qed.

(* compatibility *)

Theorem I_add_compat_r : ∀ x y z, I_eq_ext x y → I_eq_ext (x + z) (y + z).
Proof.
intros x y z Hxy.
unfold I_eq_ext in Hxy.
unfold I_eq_ext; simpl; intros i.
unfold I_add_i; simpl.
do 2 rewrite Hxy; reflexivity.
Qed.

(* associativity *)

Theorem I_add_assoc : ∀ x y z, I_eq_ext (x + (y + z)) ((x + y) + z).
Proof.
intros x y z.
unfold I_eq_ext; simpl; intros i.
unfold I_add_i; simpl.
unfold I_add_i; simpl.
bbb.
