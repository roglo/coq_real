Require Import Utf8 NPeano QArith.

Theorem nat_archimedean : ∀ a b, (0 < a → ∃ n, n * a > b)%nat.
Proof.
intros * Ha.
exists (S b); simpl.
induction b; [ now rewrite Nat.add_0_r | ].
simpl; rewrite <- Nat.add_1_l.
now apply Nat.add_le_lt_mono.
Qed.

Theorem Pos2Nat_neq_0 : ∀ a, Pos.to_nat a ≠ 0%nat.
Proof.
intros.
specialize (Pos2Nat.is_pos a) as Ha.
now intros H; rewrite H in Ha.
Qed.

Theorem Pos_archimedean : ∀ a b, (∃ n, Pos.of_nat n * a > b)%positive.
Proof.
intros.
specialize (Pos2Nat.is_pos a) as Ha.
specialize (nat_archimedean (Pos.to_nat a) (Pos.to_nat b) Ha) as (m, Hm).
exists m.
replace a with (Pos.of_nat (Pos.to_nat a)) by apply Pos2Nat.id.
rewrite <- Pos2Nat.id.
rewrite <- Nat2Pos.inj_mul.
 unfold Pos.gt.
 rewrite <- Nat2Pos.inj_compare; [ now apply Nat.compare_gt_iff | | ].
  destruct m; [ easy | ].
  apply Nat.neq_mul_0.
  split; [ apply Nat.neq_succ_0 | ].
  apply Pos2Nat_neq_0.

  apply Pos2Nat_neq_0.

 intros H; rewrite H in Hm; simpl in Hm.
 apply gt_not_le in Hm; apply Hm.
 apply Nat.lt_le_incl.
 apply Pos2Nat.is_pos.

 apply Pos2Nat_neq_0.
Qed.

Theorem Z_archimedean : ∀ a b, (0 < a → ∃ n, Z.of_nat n * a > b)%Z.
Proof.
intros * Ha.
destruct b as [| b| b].
 exists 1%nat.
 rewrite Z.mul_1_l.
 now apply Z.lt_gt.

 destruct a as [| a| a]; [ easy | | ].
  specialize (Pos_archimedean a b) as (m, Hm).
  destruct m; [ now exists 1%nat | ].
  exists (S m).
  apply Pos2Nat.inj_gt in Hm.
  rewrite Pos2Nat.inj_mul in Hm.
  rewrite Nat2Pos.id in Hm; [ | apply Nat.neq_succ_0 ].
  rewrite <- positive_nat_Z.
  rewrite <- Nat2Z.inj_mul.
  rewrite <- positive_nat_Z.
  now apply Nat2Z.inj_gt.

  apply Z.nle_gt in Ha.
  exfalso; apply Ha.
  apply Pos2Z.neg_is_nonpos.

 exists 1%nat.
 rewrite Z.mul_1_l.
 apply Z.lt_gt.
 eapply Z.lt_trans; [ | eassumption ].
 apply Pos2Z.neg_is_neg.
Qed.

Theorem Q_archimedean : ∀ a b, 0 < a → ∃ n, (Z.of_nat n # 1) * a > b.
Proof.
intros (an, ad) (bn, bd) Ha.
unfold Qlt in Ha; simpl in Ha.
rewrite Z.mul_1_r in Ha.
assert (Hab : (0 < an * ' bd)%Z) by now apply Z.mul_pos_pos.
specialize (Z_archimedean (an * ' bd) (bn * ' ad) Hab) as (m, Hm).
exists m; simpl.
unfold Qmult; simpl.
unfold Qlt; simpl.
apply Zgt_lt.
now rewrite Z.mul_assoc in Hm.
Qed.
