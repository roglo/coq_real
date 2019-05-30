(* Reals between 0 and 1; associativity of addition *)

Require Import Utf8 Arith NPeano Psatz PeanoNat.
Require Import Misc Summation Rational Ureal UrealNorm UrealAddAssoc1.
Import Q.Notations.

Set Nested Proofs Allowed.

Theorem pred_rad_lt_rad {r : radix} : rad - 1 < rad.
Proof.
specialize radix_ge_2 as H; lia.
Qed.

Definition digit_9 {r : radix} := mkdig _ (rad - 1) pred_rad_lt_rad.
Definition ureal_999 {r : radix} := {| ureal i := digit_9 |}.

Definition ureal_shift {r : radix} k x := {| ureal i := ureal x (k + i) |}.
Arguments ureal_shift _ _ x%F.

Theorem all_9_fA_ge_1_ε {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) = rad - 1)
  → ∀ k, fA_ge_1_ε u i k = true.
Proof.
intros * Hur *.
specialize radix_ge_2 as Hr.
apply A_ge_1_true_iff.
rewrite A_all_9; [ | intros j Hj; apply Hur ].
rewrite Q.frac_small. 2: {
  split.
  -apply Q.le_add_le_sub_l.
   rewrite Q.add_0_l.
   replace 1%Q with (1 // 1)%Q by easy.
   apply Q.le_pair_mono_l; split; [ pauto | now apply Nat_pow_ge_1 ].
  -apply Q.sub_lt, Q.lt_0_pair; pauto.
}
apply Q.sub_le_mono; [ easy | ].
apply Q.le_pair_mono_l; split; [ apply Nat.neq_0_lt_0; pauto | ].
apply Nat.pow_le_mono_r; [ easy | min_n_ge ].
Qed.

Theorem all_fA_ge_1_ε_carry {r : radix} : ∀ u i,
  (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k, carry u (i + k) = Q.intg (A (i + k) (min_n (i + k)) u).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Haut *.
clear - Haut.
unfold carry, carry_cases.
destruct (LPO_fst (fA_ge_1_ε u (i + k))) as [H1| H1]. {
  now rewrite Nat.add_0_r.
}
destruct H1 as (j & Hjj & Hj).
specialize (Haut (k + j)) as H1.
apply A_ge_1_add_r_true_if in H1.
now rewrite Hj in H1.
Qed.

Theorem all_fA_ge_1_ε_carry_carry {r : radix} : ∀ u i,
  (∀ k, u (i + k) ≤ 3 * (rad - 1))
  → (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k,
    carry u (i + k) =
    Q.intg
      ((u (i + k + 1) + carry u (i + k + 1))%nat // rad +
       Q.frac (A (i + k + 1) (min_n (i + k + 1)) u) * 1 // rad)%Q.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hmr Haut *.
rewrite all_fA_ge_1_ε_carry; [ | easy ].
assert (Hmr' : ∀ l, u (i + k + l) ≤ 3 * (rad - 1)). {
  intros; rewrite <- Nat.add_assoc; apply Hmr.
}
assert (Haut' : ∀ l, fA_ge_1_ε u (i + k) l = true). {
  intros l; apply A_ge_1_add_r_true_if, Haut.
}
specialize (three_lt_rad_pow (i + k)) as H.
replace (i + k) with (i + k + 0) at 2 by easy.
rewrite <- (all_fA_ge_1_ε_NQintg_A 3 (i + k) u H Hmr' Haut' 0 rad).
clear H.
unfold carry, carry_cases.
destruct (LPO_fst (fA_ge_1_ε u (i + k + 1))) as [H1| H1]. 2: {
  destruct H1 as (j & Hjj & Hj).
  specialize (Haut (k + 1 + j)) as H1.
  apply A_ge_1_add_r_true_if in H1.
  now rewrite Nat.add_assoc, Hj in H1.
}
clear H1.
rewrite A_split_first; [ | min_n_ge ].
replace (S (i + k)) with (i + k + 1) by flia.
rewrite Q.pair_add_l, <- Q.add_assoc.
rewrite <- (Q.mul_pair_den_num (Q.intg _) 1); [ | easy ].
rewrite <- Q.mul_add_distr_r.
rewrite (min_n_add _ 1), Nat.mul_1_r.
f_equal; f_equal; f_equal.
rewrite Q.intg_frac at 1; [ | easy ].
do 2 rewrite Nat.add_0_r.
f_equal; symmetry.
now rewrite min_n_add, Nat.mul_1_r.
Qed.

Theorem P_999_after_7_ge_17 {r : radix} : ∀ m u i,
  m ≤ rad
  → (∀ k, u (i + k) ≤ m * (rad - 1))
  → (∀ k, fA_ge_1_ε u i k = true)
  → ∀ j, 1 ≤ j ≤ m
  → u (i + 1) = j * rad - m
  → u (i + 2) ≥ (m - 1) * rad - m ∧ carry u (i + 1) = m - 1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hmr Hur Hau * Hj Hu1 *.
destruct (zerop m) as [Hmz| Hmz]. {
  rewrite Hmz, Nat.sub_0_r in Hu1.
  specialize (Hur 1) as H1.
  rewrite Hmz, Nat.mul_0_l, Hu1 in H1.
  apply Nat.le_0_r in H1.
  apply Nat.eq_mul_0 in H1.
  destruct H1 as [H1| H1]; [ flia Hj H1 | flia Hr H1  ].
}
apply Nat.neq_0_lt_0 in Hmz.
specialize (all_fA_ge_1_ε_P_999 u i Hau 0) as H1.
rewrite Nat.add_0_r in H1.
unfold P, d2n, prop_carr, dig in H1.
rewrite Hu1 in H1.
replace j with (j - 1 + 1) in H1 by flia Hj.
rewrite Nat.mul_add_distr_r, Nat.mul_1_l in H1.
rewrite <- Nat.add_sub_assoc in H1; [ | easy ].
rewrite <- Nat.add_assoc in H1.
rewrite Nat.add_comm in H1.
rewrite Nat.mod_add in H1; [ | easy ].
rewrite Nat.add_comm in H1.
specialize (carry_upper_bound_for_adds m u i Hmz) as Hcm.
assert (H : ∀ k, u (i + k + 1) ≤ m * (rad - 1)). {
  now intros; rewrite <- Nat.add_assoc.
}
specialize (Hcm H); clear H.
rewrite Nat.mod_small in H1. 2: {
  specialize (Hcm 1) as H2.
  flia Hmr H2.
}
assert (H2 : carry u (i + 1) = m - 1) by flia H1 Hmz Hmr.
split; [ | easy ].
unfold carry in H2.
apply Q.intg_interv in H2; [ | easy ].
rewrite A_split_first in H2; [ | min_n_ge ].
replace (S (i + 1)) with (i + 2) in H2 by easy.
destruct H2 as (H2, H3).
apply Nat.nlt_ge; intros H4.
apply Q.nlt_ge in H2; apply H2; clear H2.
remember (min_n (i + 1 + carry_cases u (i + 1))) as n eqn:Hn.
eapply Q.lt_le_trans. {
  apply (Q.lt_pair_mono_r _ _ rad) in H4.
  apply Q.add_lt_le_mono; [ apply H4 | ].
  apply Q.mul_le_mono_pos_r; [ apply Q.lt_0_pair; pauto | ].
  apply (A_upper_bound_for_adds m).
  now intros; do 2 rewrite <- Nat.add_assoc.
}
rewrite <- (Q.mul_pair_den_num _ 1); [ | easy ].
rewrite <- Q.mul_add_distr_r.
apply (Q.mul_le_mono_pos_r (rad // 1)%Q); [ now apply Q.lt_0_pair | ].
rewrite <- Q.mul_assoc.
rewrite Q.mul_inv_pair; [ | easy | easy ].
rewrite Q.mul_1_r.
rewrite <- Q.pair_mul_r.
rewrite Q.mul_sub_distr_l, Q.mul_1_r.
rewrite Q.add_sub_assoc.
eapply Q.le_trans. {
  apply Q.le_sub_l.
  apply Q.le_0_mul_r; [ easy | ].
  apply Q.le_0_pair.
}
rewrite Q.pair_sub_l; [ | flia H4 ].
now rewrite Q.sub_add.
Qed.

Theorem A_mul_inv_rad_interv {r : radix} : ∀ m u i j n,
  m ≤ rad
  → (∀ k, u (i + k) ≤ m * (rad - 1))
  → i ≤ j + 1
  → (0 ≤ A j n u * 1 // rad < 1)%Q.
Proof.
intros * Hm Hur Hj.
split; [ now apply Q.le_0_mul_r | ].
apply (Q.mul_lt_mono_pos_r (rad // 1)%Q). {
  now apply Q.lt_0_pair.
}
rewrite <- Q.mul_assoc.
rewrite Q.mul_pair_den_num; [ | easy ].
rewrite Q.mul_1_r, Q.mul_1_l.
eapply Q.le_lt_trans. {
  apply A_upper_bound_for_adds.
  intros p.
  replace (j + p + 1) with (i + (j + p + 1 - i)).
  apply Hur.
  intros; rewrite <- Nat.add_assoc; flia Hj.
}
rewrite Q.mul_sub_distr_l, Q.mul_1_r.
destruct (zerop m) as [Hmz| Hmz]. {
  subst m; cbn.
  specialize radix_ge_2 as Hr.
  now destruct rad.
}
apply (Q.lt_le_trans _ (m // 1)). {
  apply Q.sub_lt.
  apply Q.mul_pos_cancel_l; [ | easy ].
  now apply Q.lt_0_pair.
}
apply Q.le_pair; [ easy | easy | ].
now rewrite Nat.mul_1_r, Nat.mul_1_l.
Qed.

Theorem carry_succ_lemma1 {r : radix} : ∀ u a,
  (0 ≤ a)%Q
  → (Q.frac (u // rad) + Q.frac (a * 1 // rad) < 1)%Q
  → u / rad + Q.intg (a * (1 // rad)%Q) = (u + Q.intg a) / rad.
Proof.
intros * Haz H3.
specialize radix_ge_2 as Hr.
rewrite Q.frac_pair in H3.
rewrite <- (Q.mul_pair_den_num _ 1) in H3; [ | easy ].
apply (Q.mul_lt_mono_pos_r (rad // 1)%Q) in H3. 2: {
  now apply Q.lt_0_pair.
}
rewrite Q.mul_add_distr_r in H3.
rewrite <- Q.mul_assoc, Q.mul_1_l in H3.
rewrite Q.mul_pair_den_num in H3; [ | easy ].
rewrite Q.mul_1_r in H3.
specialize (Nat.div_mod u rad radix_ne_0) as H5.
symmetry; rewrite H5 at 1.
rewrite Nat.mul_comm, <- Nat.add_assoc, Nat.add_comm.
rewrite Nat.div_add; [ | easy ].
rewrite Nat.add_comm; f_equal.
specialize (Nat.div_mod (u mod rad + Q.intg a) rad radix_ne_0) as H7.
remember ((u mod rad + Q.intg a) / rad) as m eqn:Hm.
symmetry.
apply Q.intg_interv; [ now apply Q.le_0_mul_r | ].
split. {
  apply (Q.mul_le_mono_pos_r (rad // 1)); [ now apply Q.lt_0_pair | ].
  rewrite <- Q.mul_assoc.
  rewrite Q.mul_pair_den_num; [ | easy ].
  rewrite Q.mul_1_r, <- Q.pair_mul_r.
  apply Q.nlt_ge; intros H10.
  rewrite (Q.frac_less_small (m - 1)) in H3. 2: {
    split. 2: {
      rewrite <- (Q.pair_add_l _ 1).
      rewrite Nat.sub_add. 2: {
        apply Nat.nlt_ge; intros Hnz.
        apply Nat.lt_1_r in Hnz; rewrite Hnz in H10.
        cbn in H10.
        now apply Q.nle_gt in H10; apply H10.
      }
      apply (Q.mul_lt_mono_pos_r (rad // 1)); [ now apply Q.lt_0_pair | ].
      rewrite <- Q.mul_assoc.
      rewrite Q.mul_pair_den_num; [ | easy ].
      rewrite Q.mul_1_r.
      now rewrite <- Q.pair_mul_l.
    }
    apply (Q.mul_le_mono_pos_r (rad // 1)); [ now apply Q.lt_0_pair | ].
    rewrite <- Q.mul_assoc.
    rewrite Q.mul_pair_den_num; [ | easy ].
    rewrite Q.mul_1_r.
    rewrite <- Q.pair_mul_l.
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
    rewrite Q.pair_sub_l. 2: {
      destruct m; [ | cbn; flia ].
      cbn in H10; exfalso.
      now apply Q.nle_gt in H10; apply H10.
    }
    apply Q.le_sub_le_add_r.
    rewrite Hm.
    rewrite (Q.num_den a) at 2; [ | easy ].
    rewrite Q.add_pair; [ | easy | easy ].
    do 2 rewrite Nat.mul_1_r.
    apply Q.le_pair; [ easy | easy | ].
    rewrite Nat.mul_1_l.
    remember (u mod rad + Q.intg a) as x eqn:Hx.
    apply (le_trans _ (x * Q.den a)). {
      apply Nat.mul_le_mono_r.
      rewrite Nat.mul_comm.
      now apply Nat.mul_div_le.
    }
    subst x.
    rewrite Nat.mul_add_distr_r, Nat.add_comm.
    apply Nat.add_le_mono. {
      rewrite (Q.num_den a) at 1; [ | easy ].
      rewrite Q.intg_pair; [ | easy ].
      rewrite Nat.mul_comm.
      now apply Nat.mul_div_le.
    }
    rewrite Nat.mul_comm.
    apply Nat.mul_le_mono_l.
    now apply Nat.lt_le_incl, Nat.mod_upper_bound.
  }
  rewrite Q.mul_sub_distr_r in H3.
  rewrite <- Q.mul_assoc in H3.
  rewrite Q.mul_pair_den_num in H3; [ | easy ].
  rewrite Q.mul_1_r in H3.
  rewrite <- Q.pair_mul_l in H3.
  rewrite Q.add_sub_assoc in H3.
  apply Q.lt_sub_lt_add_l in H3.
  rewrite <- Q.pair_add_l in H3.
  replace rad with (1 * rad) in H3 at 3 by flia.
  rewrite <- Nat.mul_add_distr_r in H3.
  rewrite Nat.sub_add in H3. 2: {
    apply Nat.nlt_ge; intros Hnz.
    apply Nat.lt_1_r in Hnz; rewrite Hnz in H10.
    cbn in H10.
    now apply Q.nle_gt in H10; apply H10.
  }
  apply Q.nle_gt in H3; apply H3; clear H3.
  rewrite Hm.
  rewrite (Q.num_den a) at 2; [ | easy ].
  rewrite Q.add_pair; [ | easy | easy ].
  do 2 rewrite Nat.mul_1_l.
  apply Q.le_pair; [ easy | easy | ].
  rewrite Nat.mul_1_l.
  remember (u mod rad + Q.intg a) as x eqn:Hx.
  apply (le_trans _ (x * Q.den a)). {
    apply Nat.mul_le_mono_r.
    rewrite Nat.mul_comm.
    now apply Nat.mul_div_le.
  }
  subst x.
  rewrite Nat.mul_add_distr_r.
  apply Nat.add_le_mono_l.
  rewrite (Q.num_den a) at 1; [ | easy ].
  rewrite Q.intg_pair; [ | easy ].
  rewrite Nat.mul_comm.
  now apply Nat.mul_div_le.
}
apply (Q.mul_lt_mono_pos_r (rad // 1)); [ now apply Q.lt_0_pair | ].
rewrite <- Q.mul_assoc.
rewrite Q.mul_pair_den_num; [ | easy ].
rewrite Q.mul_1_r.
rewrite <- (Q.pair_add_l _ 1).
rewrite <- Q.pair_mul_r.
specialize (Q.intg_interv (Q.intg a) a) as H10.
specialize (proj2 (H10 Haz) eq_refl) as (H11, H12); clear H10.
eapply Q.lt_le_trans; [ apply H12 | ].
apply Q.le_add_le_sub_l.
rewrite <- (Q.pair_sub_l _ 1). 2: {
  rewrite Nat.mul_add_distr_r; flia Hr.
}
apply Q.le_pair_mono_r.
apply Nat.le_add_le_sub_r.
rewrite Hm, Nat.mul_add_distr_r, Nat.mul_1_l.
apply (le_trans _ (Q.intg a / rad * rad + rad)). 2: {
  apply Nat.add_le_mono_r.
  apply Nat.mul_le_mono_r.
  apply Nat.div_le_mono; [ easy | flia ].
}
specialize (Nat.div_mod (Q.intg a) rad radix_ne_0) as H10.
rewrite Nat.mul_comm in H10.
rewrite H10 at 1.
rewrite <- Nat.add_assoc.
apply Nat.add_le_mono_l.
rewrite Nat.add_comm.
now apply Nat.mod_upper_bound.
Qed.

Theorem carry_succ_lemma2 {r : radix} : ∀ u a,
  (0 ≤ a)%Q
  → (1 ≤ Q.frac (u // rad) + Q.frac (a * 1 // rad))%Q
  → u / rad + Q.intg (a * (1 // rad)%Q) + 1 = (u + Q.intg a) / rad.
Proof.
intros * Haz H3.
rewrite Q.frac_pair in H3.
rewrite <- (Q.mul_pair_den_num _ 1) in H3; [ | easy ].
apply (Q.mul_le_mono_pos_r (rad // 1)%Q) in H3. 2: {
  now apply Q.lt_0_pair.
}
rewrite Q.mul_add_distr_r in H3.
rewrite <- Q.mul_assoc, Q.mul_1_l in H3.
rewrite Q.mul_pair_den_num in H3; [ | easy ].
rewrite Q.mul_1_r in H3.
specialize (Nat.div_mod u rad radix_ne_0) as H5.
symmetry; rewrite H5 at 1.
rewrite Nat.mul_comm, <- Nat.add_assoc, Nat.add_comm.
rewrite Nat.div_add; [ | easy ].
rewrite Nat.add_comm, <- Nat.add_assoc; f_equal.
specialize (Nat.div_mod (u mod rad + Q.intg a) rad radix_ne_0) as H7.
remember ((u mod rad + Q.intg a) / rad) as m eqn:Hm.
destruct m. {
  exfalso.
  symmetry in Hm.
  apply Nat.div_small_iff in Hm; [ | easy ].
  clear H7.
  rewrite Q.frac_small in H3. 2: {
    split; [ now apply Q.le_0_mul_r | ].
    apply (Q.mul_lt_mono_pos_r (rad // 1)); [ now apply Q.lt_0_pair | ].
    rewrite <- Q.mul_assoc.
    rewrite Q.mul_pair_den_num; [ | easy ].
    rewrite Q.mul_1_r, Q.mul_1_l.
    apply Q.intg_lt_lt; [ easy | flia Hm ].
  }
  rewrite <- Q.mul_assoc in H3.
  rewrite Q.mul_pair_den_num in H3; [ | easy ].
  rewrite Q.mul_1_r in H3.
  apply Q.nlt_ge in H3; apply H3; clear H3.
  apply Q.intg_lt_lt. {
    apply Q.le_0_add; [ apply Q.le_0_pair | easy ].
  }
  rewrite Q.intg_add_cond; [ | apply Q.le_0_pair | easy ].
  rewrite Q.intg_pair; [ | easy ].
  rewrite Nat.div_1_r, Q.frac_pair, Nat.mod_1_r.
  rewrite Q.add_0_l.
  destruct (Q.lt_le_dec (Q.frac a) 1) as [H3| H3]. {
    now rewrite Nat.add_0_r.
  }
  exfalso; apply Q.nlt_ge in H3; apply H3.
  apply Q.frac_lt_1.
}
rewrite <- Nat.add_1_r in Hm.
rewrite Nat.add_1_r; f_equal; symmetry.
apply Q.intg_interv; [ now apply Q.le_0_mul_r | ].
assert (Hma : (m // 1 ≤ a * 1 // rad)%Q). {
  apply (Q.mul_le_mono_pos_r (rad // 1)); [ now apply Q.lt_0_pair | ].
  rewrite <- Q.mul_assoc.
  rewrite Q.mul_pair_den_num; [ | easy ].
  rewrite Q.mul_1_r, <- Q.pair_mul_r.
  apply (Q.add_le_mono_r _ _ (rad // 1)).
  rewrite Q.add_pair; [ | easy | easy ].
  do 2 rewrite Nat.mul_1_r.
  rewrite <- Nat.mul_add_distr_r, Hm.
  remember (u mod rad + Q.intg a) as x eqn:Hx.
  apply (Q.le_trans _ (x // 1)). {
    apply Q.le_pair_mono_r; rewrite Nat.mul_comm.
    now apply Nat.mul_div_le.
  }
  rewrite Hx, Nat.add_comm.
  rewrite Q.pair_add_l.
  apply Q.add_le_mono. {
    rewrite Q.intg_to_frac; [ | easy ].
    now apply Q.le_sub_l.
  }
  apply Q.le_pair; [ easy | easy | ].
  rewrite Nat.mul_1_r, Nat.mul_1_l.
  now apply Nat.lt_le_incl, Nat.mod_upper_bound.
}
split; [ easy | ].
apply (Q.mul_lt_mono_pos_r (rad // 1)); [ now apply Q.lt_0_pair | ].
rewrite <- Q.mul_assoc.
rewrite Q.mul_pair_den_num; [ | easy ].
rewrite Q.mul_1_r.
rewrite <- (Q.pair_add_l _ 1).
rewrite <- Q.pair_mul_r.
apply (Q.mul_le_mono_pos_r (rad // 1)) in Hma; [ | now apply Q.lt_0_pair ].
rewrite <- Q.mul_assoc in Hma.
rewrite Q.mul_pair_den_num in Hma; [ | easy ].
rewrite Q.mul_1_r in Hma.
rewrite <- Q.pair_mul_r in Hma.
clear - Hm Hma H3 Haz.
move H3 at bottom.
assert (H8 : rad ≤  Q.intg a mod rad + u mod rad). {
  apply Nat.nlt_ge; intros H8.
  apply Nat.lt_add_lt_sub_r in H8.
  apply Q.nlt_ge in H3; apply H3; clear H3.
  rewrite (Q.num_den a); [ | easy ].
  rewrite Q.mul_pair; [ | easy | easy ].
  rewrite Nat.mul_1_r, Q.frac_pair, <- Q.pair_mul_l.
  rewrite Q.mul_pair_mono_r; [ | easy | easy ].
  rewrite Q.add_pair; [ | easy | easy ].
  do 2 rewrite Nat.mul_1_l.
  apply Q.lt_pair; [ easy | easy | ].
  rewrite Nat.mul_1_r.
  rewrite Nat.mod_mul_r; [ | easy | easy ].
  rewrite (Nat.mul_comm (Q.den a)).
  rewrite Nat.add_assoc, Nat.add_shuffle0, <- Nat.mul_add_distr_r.
  apply Nat.lt_add_lt_sub_l.
  rewrite Nat.mul_comm.
  rewrite <- Nat.mul_sub_distr_r.
  eapply Nat.lt_le_trans; [ now apply Nat.mod_upper_bound | ].
  replace (Q.den a) with (1 * Q.den a) at 1 by flia.
  apply Nat.mul_le_mono_r.
  unfold Q.intg in H8; flia H8.
}
specialize (proj2 (Q.intg_interv (Q.intg a) a Haz) eq_refl) as H.
eapply Q.lt_le_trans; [ apply H | ].
rewrite <- (Q.pair_add_l _ 1).
apply Q.le_pair; [ easy | easy | ].
rewrite Nat.mul_1_r, Nat.mul_1_l.
eapply Q.le_lt_trans in Hma; [ clear H | apply H ].
remember (Q.intg a) as b eqn:Hb.
rewrite <- (Q.pair_add_l _ 1) in Hma.
apply Q.lt_pair in Hma; [ | easy | easy ].
rewrite Nat.mul_1_r, Nat.mul_1_l in Hma.
clear a Haz Hb H3.
specialize (Nat.mod_upper_bound u rad radix_ne_0) as Hu.
remember (u mod rad) as a eqn:Ha.
rewrite Nat.add_comm in H8.
clear u Ha.
symmetry in Hm.
specialize (Nat.div_mod (a + b) rad radix_ne_0) as H1.
rewrite Hm in H1.
apply (Nat.add_le_mono_l _ _ a).
rewrite Nat.add_assoc.
rewrite H1.
rewrite Nat.mul_comm, <- Nat.add_assoc, (Nat.add_comm).
apply Nat.add_le_mono_r.
rewrite <- Nat.add_mod_idemp_r; [ | easy ].
rewrite (Nat_mod_less_small 1). 2: {
  rewrite Nat.mul_1_l; split; [ easy | ].
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  apply Nat.add_lt_mono; [ easy | ].
  now apply Nat.mod_upper_bound.
}
rewrite Nat.mul_1_l.
rewrite <- Nat.add_sub_swap; [ | easy ].
apply Nat.le_sub_le_add_r.
rewrite <- Nat.add_assoc.
apply Nat.add_le_mono_l.
rewrite Nat.add_comm.
now apply Nat.mod_upper_bound.
Qed.

Theorem carry_succ_lemma3 {r : radix} : ∀ u a,
  (0 ≤ a)%Q
  → Q.intg ((u // rad)%Q + (a * 1 // rad)%Q) = (u + Q.intg a) / rad.
Proof.
intros * Ha.
rewrite Q.intg_add_cond; [ | apply Q.le_0_pair | now apply Q.le_0_mul_r ].
rewrite Q.intg_pair; [ | easy ].
destruct
  (Q.lt_le_dec (Q.frac (u // rad) + Q.frac (a * (1 // rad)%Q)) 1)
  as [H3| H3]. {
  rewrite Nat.add_0_r.
  now apply carry_succ_lemma1.
}
now apply carry_succ_lemma2.
Qed.

Theorem carry_succ {r : radix} : ∀ m u i,
  m < rad ^ (rad * (i + 3) - (i + 2))
  → (∀ k, u (i + k) ≤ m * (rad - 1))
  → carry u i = (u (i + 1) + carry u (i + 1)) / rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hmrr Hur.
assert (Hmrj : ∀ j, m < rad ^ (rad * (i + j + 3) - i - j - 2)). {
  intros j.
  eapply lt_le_trans; [ apply Hmrr | ].
  apply Nat.pow_le_mono_r; [ easy | ].
  rewrite Nat.sub_add_distr.
  apply Nat.sub_le_mono_r.
  rewrite Nat_sub_sub_swap.
  apply Nat.sub_le_mono_r.
  rewrite Nat.add_shuffle0.
  rewrite (Nat.mul_add_distr_l _ (i + 3)).
  rewrite <- Nat.add_sub_assoc; [ flia | ].
  destruct rad as [| rr]; [ easy | cbn; flia ].
}
unfold carry, carry_cases.
destruct (LPO_fst (fA_ge_1_ε u i)) as [H1| H1]. {
  specialize (all_fA_ge_1_ε_P_999 u i H1 0) as H6.
  rewrite Nat.add_0_r in H6.
  unfold P, d2n, prop_carr, dig in H6.
  unfold carry, carry_cases in H6.
  destruct (LPO_fst (fA_ge_1_ε u (i + 1))) as [H2| H2]. {
    do 2 rewrite Nat.add_0_r.
    rewrite <- (all_fA_ge_1_ε_NQintg_A' m i) with (k := 1); try easy.
    rewrite A_split_first; [ | min_n_ge ].
    replace (S i) with (i + 1) by flia.
    remember (A (i + 1) (min_n (i + 1)) u) as a eqn:Ha.
    rewrite <- (Q.mul_pair_den_num _ 1); [ | easy ].
    rewrite <- Q.mul_add_distr_r.
    remember ((u (i + 1) + Q.intg a) / rad) as n eqn:Hn.
    symmetry in Hn.
    apply (Q.intg_less_small n).
    split. {
      rewrite <- Hn.
      apply (Q.mul_le_mono_pos_r (rad // 1)); [ now apply Q.lt_0_pair | ].
      rewrite <- Q.mul_assoc, Q.mul_pair_den_num; [ | easy ].
      rewrite Q.mul_1_r, <- Q.pair_mul_r.
      rewrite (Q.num_den a); [ | now rewrite Ha ].
      rewrite Q.add_pair; [ | easy | easy ].
      do 2 rewrite Nat.mul_1_l.
      apply Q.le_pair; [ easy | easy | ].
      rewrite Nat.mul_1_l.
      rewrite Q.intg_pair; [ | easy ].
      eapply le_trans. {
        apply Nat.mul_le_mono_r.
        rewrite Nat.mul_comm.
        now apply Nat.mul_div_le.
      }
      rewrite Nat.mul_add_distr_r.
      apply Nat.add_le_mono_l.
      rewrite Nat.mul_comm.
      now apply Nat.mul_div_le.
    }
    specialize (Nat.div_mod (u (i + 1) + Q.intg a) rad radix_ne_0) as H3.
    rewrite Nat.add_0_r, <- Ha in H6.
    rewrite Hn, H6 in H3.
    apply (Q.mul_lt_mono_pos_r (rad // 1)); [ now apply Q.lt_0_pair | ].
    rewrite <- Q.mul_assoc, Q.mul_pair_den_num; [ | easy ].
    rewrite Q.mul_1_r.
    rewrite Q.mul_add_distr_r, Q.mul_1_l.
    rewrite <- Q.pair_mul_r, <- Q.pair_add_l.
    replace rad with ((rad - 1) + 1) at 2 by flia Hr.
    rewrite Nat.mul_comm, Nat.add_assoc, <- H3.
    rewrite <- Nat.add_assoc, Q.pair_add_l.
    apply Q.add_lt_mono_l.
    rewrite Q.pair_add_l.
    specialize (Q.intg_interv (Q.intg a) a) as H4.
    assert (H : (0 ≤ a)%Q) by now rewrite Ha.
    specialize (proj2 (H4 H) eq_refl) as H5; clear H H4.
    now destruct H5 as (H4, H5).
  }
  destruct H2 as (j & Hjj & Hj).
  now rewrite A_ge_1_add_r_true_if in Hj.
}
destruct H1 as (j & Hjj & Hj).
assert
  (H3 :
     ∀ k, j ≤ k →
     Q.intg (A i (min_n (i + k)) u) = Q.intg (A i (min_n (i + j)) u)). {
  intros k Hk.
  apply (fA_lt_1_ε_NQintg_A m); try easy.
  now unfold min_n.
}
rewrite <- (H3 (j + 1)); [ | flia ].
destruct (LPO_fst (fA_ge_1_ε u (i + 1))) as [H2| H2]. {
  specialize (all_fA_ge_1_ε_P_999 u (i + 1) H2 0) as H6.
  rewrite Nat.add_0_r in H6.
  unfold P, d2n, prop_carr, dig in H6.
  unfold carry, carry_cases in H6.
  destruct (LPO_fst (fA_ge_1_ε u (i + 1 + 1))) as [H1| H1]. 2: {
    destruct H1 as (k & Hjk & Hk).
    now rewrite A_ge_1_add_r_true_if in Hk.
  }
  symmetry.
  rewrite Nat.add_0_r.
  rewrite <- (all_fA_ge_1_ε_NQintg_A' m) with (k := j); try easy; cycle 1. {
    do 2 rewrite Nat.sub_add_distr; apply Hmrj.
  } {
    now intros; rewrite <- Nat.add_assoc.
  }
  symmetry.
  rewrite A_split_first; [ | min_n_ge ].
  replace (S i) with (i + 1) by flia.
  rewrite Nat.add_assoc, Nat.add_shuffle0.
  now apply carry_succ_lemma3.
}
destruct H2 as (k & Hjk & Hk).
assert
  (H4 :
     ∀ p, k ≤ p →
     Q.intg (A (i + 1) (min_n (i + 1 + p)) u) =
     Q.intg (A (i + 1) (min_n (i + 1 + k)) u)). {
  intros p Hp.
  apply (fA_lt_1_ε_NQintg_A m); try easy. {
    unfold min_n.
    replace (i + 1 + k + 3) with (i + (1 + k) + 3) by flia.
    rewrite Nat.sub_add_distr.
    now rewrite <- (Nat.sub_add_distr _ 1).
  }
  now intros q; rewrite <- Nat.add_assoc.
}
rewrite H3; [ | flia ].
rewrite <- (H3 (j + k + 1)); [ | flia ].
rewrite <- (H4 (j + k)); [ | flia ].
rewrite A_split_first; [ | min_n_ge ].
replace (S i) with (i + 1) by flia.
replace (i + (j + k + 1)) with (i + 1 + (j + k)) by flia.
now apply carry_succ_lemma3.
Qed.

Theorem carry_succ_m_le_rad {r : radix} : ∀ m u i,
  m ≤ rad
  → (∀ k, u (i + k) ≤ m * (rad - 1))
  → carry u i = (u (i + 1) + carry u (i + 1)) / rad.
Proof.
intros * Hmr Hur.
apply (carry_succ m); [ | easy ].
apply (le_lt_trans _ rad); [ easy | ].
specialize radix_ge_2 as Hr.
replace rad with (rad ^ 1) at 1 by apply Nat.pow_1_r.
apply Nat.pow_lt_mono_r; [ easy | ].
destruct rad as [| rr]; [ easy | ].
destruct rr; [ flia Hr | cbn; flia ].
Qed.

Theorem P_999_after_7_gt {r : radix} : ∀ m u i,
  m ≤ rad
  → (∀ k, u (i + k) ≤ m * (rad - 1))
  → (∀ k, fA_ge_1_ε u i k = true)
  → ∀ j, 1 ≤ j ≤ m
  → u (i + 1) = j * rad - m
  → u (i + 2) ≥ (m - 1) * rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hmr Hur Hau * Hj Hu1 *.
destruct (zerop m) as [Hmz| Hmz]; [ flia Hmz Hj | ].
move Hmz before Hmr.
specialize (P_999_after_7_ge_17 m u i Hmr Hur Hau _ Hj Hu1) as (Hu2lb, Hc1).
destruct (Nat.eq_dec m 1) as [Hm| Hm]; [ rewrite Hm; cbn; flia | ].
assert (Hmg : m ≥ 2) by flia Hmz Hm.
move Hmg before Hmr; clear Hmz Hm.
destruct (Nat.eq_dec (u (i + 2)) ((m - 1) * rad - m)) as [Hu2| Hu2]. {
  exfalso; clear Hu2lb.
  specialize (P_999_after_7_ge_17 m u (i + 1) Hmr) as H2.
  replace (i + 1 + 1) with (i + 2) in H2 by flia.
  replace (i + 1 + 2) with (i + 3) in H2 by flia.
  assert (H : ∀ k, u (i + 1 + k) ≤ m * (rad - 1)). {
    now intros; rewrite <- Nat.add_assoc.
  }
  specialize (H2 H); clear H.
  assert (H : ∀ k, fA_ge_1_ε u (i + 1) k = true). {
    now intros; apply A_ge_1_add_r_true_if.
  }
  specialize (H2 H (m - 1)); clear H.
  assert (H : 1 ≤ m - 1 ≤ m) by flia Hmg.
  specialize (H2 H Hu2); clear H.
  destruct H2 as (Hu3, Hc2).
  specialize (carry_succ_m_le_rad m u (i + 1) Hmr) as H1.
  replace (i + 1 + 1) with (i + 2) in H1 by flia.
  assert (H : ∀ k, u (i + 1 + k) ≤ m * (rad - 1)). {
    now intros; rewrite <- Nat.add_assoc.
  }
  specialize (H1 H); clear H.
  rewrite Hc1, Hc2, Hu2 in H1.
  apply (Nat.add_cancel_r _ _ 1) in H1.
  rewrite Nat.sub_add in H1; [ | flia Hmg ].
  rewrite <- Nat.div_add in H1; [ | easy ].
  rewrite Nat.mul_1_l, <- Nat.add_assoc in H1.
  rewrite <- Nat.add_sub_swap in H1. 2: {
    rewrite Nat.mul_comm.
    destruct rad as [| rr]; [ easy | ].
    destruct rr; [ flia Hr | cbn; flia Hmg ].
  }
  rewrite <- Nat.add_sub_assoc in H1; [ | flia Hmr ].
  rewrite Nat.add_comm in H1.
  rewrite Nat.div_add in H1; [ | easy ].
  replace (m - 1 + rad - m) with (rad - 1) in H1 by flia Hmg.
  rewrite Nat.div_small in H1; [ flia H1 Hmg | flia Hr ].
}
assert (H : u (i + 2) ≥ (m - 1) * rad - m + 1) by flia Hu2lb Hu2.
move H before Hu2lb; clear Hu2lb Hu2; rename H into Hu2lb.
specialize (carry_succ_m_le_rad m u (i + 1) Hmr) as H1.
assert (H : ∀ k, u (i + 1 + k) ≤ m * (rad - 1)). {
  now intros; rewrite <- Nat.add_assoc.
}
specialize (H1 H); clear H.
replace (i + 1 + 1) with (i + 2) in H1 by flia.
specialize (all_fA_ge_1_ε_P_999 u i Hau 1) as H2.
replace (i + 1 + 1) with (i + 2) in H2 by flia.
unfold P, d2n, prop_carr, dig in H2.
specialize (Nat.div_mod (u (i + 2) + carry u (i + 2)) rad) as H3.
specialize (H3 radix_ne_0).
rewrite <- H1, H2, Hc1 in H3; clear H1 H2.
specialize (carry_upper_bound_for_adds m u i) as Hc2.
assert (H : m ≠ 0) by flia Hmg.
specialize (Hc2 H); clear H.
assert (H : ∀ k, u (i + k + 1) ≤ m * (rad - 1)). {
  now intros; rewrite <- Nat.add_assoc.
}
specialize (Hc2 H 2); clear H.
clear - Hmr H3 Hc2 Hmg Hu2lb.
flia Hmr H3 Hc2 Hmg Hu2lb.
Qed.

Theorem P_999_once_after_7 {r : radix} : ∀ m u i,
  m ≤ rad
  → (∀ k, u (i + k) ≤ m * (rad - 1))
  → (∀ k, fA_ge_1_ε u i k = true)
  → ∀ j, 1 ≤ j ≤ m
  → u (i + 1) = j * rad - m
  → u (i + 2) = m * (rad - 1).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hmr Hur Hau * Hj Hu1 *.
specialize (P_999_after_7_gt m u i Hmr Hur Hau j Hj Hu1) as H1.
specialize (P_999_start u (i + 2) m) as H2.
assert (H : ∀ k, u (i + 2 + k) ≤ m * (rad - 1)). {
  now intros; rewrite <- Nat.add_assoc.
}
specialize (H2 H); clear H.
assert (H : ∀ k, P u (i + 2 + k) = rad - 1). {
  intros.
  replace (i + 2 + k) with (i + (k + 1) + 1) by flia.
  now apply all_fA_ge_1_ε_P_999.
}
specialize (H2 H); clear H.
destruct (lt_dec rad m) as [H| H]; [ flia Hmr H | clear H ].
destruct (Nat.eq_dec (u (i + 2)) (m * (rad - 1))) as [Hu| Hu]; [ easy | ].
destruct H2 as (H2 & H3 & H4).
remember (u (i + 2) / rad + 1) as j1 eqn:Hj1.
remember (carry u (i + 2) + 1) as k1 eqn:Hk1.
move k1 before j1; move Hk1 before Hj1.
exfalso.
apply Nat.nlt_ge in H1; apply H1; clear H1.
rewrite H4.
apply (lt_le_trans _ (j1 * rad)). {
  apply Nat.sub_lt; [ | flia H3 ].
  replace k1 with (1 * k1) by flia.
  apply Nat.mul_le_mono; [ easy | flia H3 Hmr ].
}
apply Nat.mul_le_mono_r.
flia H2.
Qed.

Theorem P_999_after_7 {r : radix} : ∀ m u i,
  m ≤ rad
  → (∀ k, u (i + k) ≤ m * (rad - 1))
  → (∀ k, fA_ge_1_ε u i k = true)
  → ∀ j, 1 ≤ j ≤ m
  → u (i + 1) = j * rad - m
  → ∀ k, u (i + k + 2) = m * (rad - 1).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hmr Hur Hau * Hj Hu1 *.
induction k. {
  rewrite Nat.add_0_r.
  now eapply P_999_once_after_7.
}
replace (i + k + 2) with (i + S k + 1) in IHk by flia.
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in IHk.
apply P_999_once_after_7 with (j0 := m); [ easy | | | flia Hj | easy ]. {
  now intros p; rewrite <- Nat.add_assoc.
} {
  now intros p; apply A_ge_1_add_r_true_if.
}
Qed.

Theorem rad_2_sum_2_half_A_lt_1 {r : radix} : ∀ i n u,
  rad = 2
  → (∀ k, u (i + k) ≤ 2)
  → (A i n u * 1 // 2 < 1)%Q.
Proof.
intros * Hr2 Hu.
specialize (A_mul_inv_rad_interv 2 u i i n radix_ge_2) as H1.
rewrite Hr2 in H1.
specialize (H1 Hu).
assert (H : i ≤ i + 1) by flia.
specialize (H1 H); clear H.
now destruct H1.
Qed.

(* ça serait achement plus cool si au lieu de l'hypothèse
   (∀ k, fA_ge_1_ε u i k = true), j'avais
   (∀ k, P u (i + k) = rad - 1), mais c'est compliqué
   du fait que c'est une somme de 3 *)
Theorem sum_3_all_fA_true_8_not_8 {r : radix} : ∀ u i,
  (∀ k, u (i + k) ≤ 3 * (rad - 1))
  → (∀ k, fA_ge_1_ε u i k = true)
  → u (i + 1) = rad - 2
  → u (i + 2) ≠ rad - 2.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu3 Hau Hu1 Hu2.
specialize (all_fA_ge_1_ε_P_999 _ _ Hau) as Hpu.
assert (Hc3 : ∀ k, carry u (i + k) < 3). {
  specialize (carry_upper_bound_for_adds 3 u i) as H6.
  assert (H : 3 ≠ 0) by easy.
  specialize (H6 H); clear H.
  assert (H : ∀ k, u (i + k + 1) ≤ 3 * (rad - 1)). {
    intros p; rewrite <- Nat.add_assoc; apply Hu3.
  }
  now specialize (H6 H).
}
assert (Hci1 : carry u (i + 1) mod rad = 1). {
  specialize (Hpu 0) as H1.
  rewrite Nat.add_0_r in H1.
  unfold P, d2n, prop_carr, dig in H1.
  rewrite Hu1 in H1.
  rewrite <- Nat.add_mod_idemp_r in H1; [ | easy ].
  remember (carry u (i + 1) mod rad) as c eqn:Hc.
  symmetry in Hc.
  destruct c; [ rewrite Nat.add_0_r, Nat.mod_small in H1; flia Hr H1 | ].
  destruct c; [ easy | exfalso ].
  replace (rad - 2 + S (S c)) with (rad + c) in H1 by flia Hr.
  rewrite Nat_mod_add_same_l in H1; [ | easy ].
  destruct c. {
    rewrite Nat.mod_0_l in H1; [ flia Hr H1 | easy ].
  }
  specialize (Hc3 1) as H2.
  apply Nat.nle_gt in H2; apply H2; clear H2.
  specialize (Nat.div_mod (carry u (i + 1)) rad radix_ne_0) as H2.
  rewrite H2, Hc; flia.
}
assert (Hci2 : carry u (i + 2) = 1). {
  specialize (Hpu 1) as H1.
  unfold P, d2n, prop_carr in H1; cbn in H1.
  rewrite <- Nat.add_assoc in H1; replace (1 + 1) with 2 in H1 by easy.
  rewrite Hu2 in H1.
  destruct (Nat.eq_dec (carry u (i + 2)) 0) as [Hc20| Hc20]. {
    rewrite Hc20, Nat.add_0_r in H1.
    rewrite Nat.mod_small in H1; [ flia Hr H1 | flia Hr ].
  }
  destruct (Nat.eq_dec (carry u (i + 2)) 2) as [Hc22| Hc22]. {
    rewrite Hc22, Nat.sub_add in H1; [ | easy ].
    rewrite Nat.mod_same in H1; [ flia Hr H1 | easy ].
  }
  specialize (Hc3 2) as H7.
  flia Hc20 Hc22 H7.
}
unfold carry, carry_cases in Hci1.
destruct (LPO_fst (fA_ge_1_ε u (i + 1))) as [HA| HA]. 2: {
  destruct HA as (p & Hjp & Hp).
  specialize (Hau (1 + p)).
  now rewrite A_ge_1_add_r_true_if in Hp.
}
clear HA.
unfold carry, carry_cases in Hci2.
destruct (LPO_fst (fA_ge_1_ε u (i + 2))) as [HA| HA]. 2: {
  destruct HA as (p & Hjp & Hp).
  specialize (Hau (2 + p)).
  now rewrite A_ge_1_add_r_true_if in Hp.
}
clear HA.
rewrite <- (all_fA_ge_1_ε_NQintg_A 3) with (l := rad) in Hci1; cycle 1. {
  apply three_lt_rad_pow.
} {
  intros; rewrite <- Nat.add_assoc; apply Hu3.
} {
  now intros; apply A_ge_1_add_r_true_if.
}
replace (i + 2) with (i + 1 + 1) in Hci2 at 2 by flia.
rewrite A_split_first in Hci1; [ | min_n_ge ].
replace (S (i + 1)) with (i + 2) in Hci1 by easy.
rewrite Hu2 in Hci1.
rewrite Q.intg_add_cond in Hci1; [ | apply Q.le_0_pair | ]. 2: {
  now apply Q.le_0_mul_r.
}
rewrite Q.intg_small in Hci1. 2: {
  split; [ apply Q.le_0_pair | ].
  replace 1%Q with (1 // 1)%Q by easy.
  apply Q.lt_pair; [ easy | easy | flia Hr ].
}
rewrite Q.frac_small in Hci1. 2: {
  split; [ apply Q.le_0_pair | ].
  replace 1%Q with (1 // 1)%Q by easy.
  apply Q.lt_pair; [ easy | easy | flia Hr ].
}
rewrite Nat.add_0_l in Hci1.
rewrite Q.frac_small in Hci1. 2: {
  apply Q.intg_interv in Hci2; [ | easy ].
  split; [ now apply Q.le_0_mul_r | ].
  apply (Q.mul_lt_mono_pos_r (rad // 1)%Q); [ now apply Q.lt_0_pair | ].
  rewrite <- Q.mul_assoc, Q.mul_pair_den_num; [ | easy ].
  rewrite Q.mul_1_r, Q.mul_1_l.
  rewrite Nat.add_0_r.
  rewrite Nat.add_0_r, min_n_add, Nat.mul_1_r in Hci2.
  eapply Q.lt_le_trans; [ apply Hci2 | ].
  replace 1%Q with (1 // 1)%Q by easy.
  rewrite <- Q.pair_add_l.
  apply Q.le_pair; [ easy | easy | flia Hr ].
}
remember (A (i + 2) (min_n (i + 1) + rad) u) as a eqn:Ha.
rewrite Nat.add_0_r, min_n_add, Nat.mul_1_r in Hci2.
rewrite Nat.add_0_r, <- Ha in Hci1.
rewrite <- Ha in Hci2.
destruct (Q.lt_le_dec (((rad - 2) // rad)%Q + (a * 1 // rad)%Q) 1)
  as [H1| H1]. {
  rewrite Nat.add_0_r in Hci1.
  rewrite Q.intg_small in Hci1; [ now rewrite Nat.mod_0_l in Hci1 | ].
  apply Q.intg_interv in Hci2; [ | now rewrite Ha ].
  rewrite Ha.
  split; [ now apply Q.le_0_mul_r | ].
  rewrite <- Ha.
  apply (Q.mul_lt_mono_pos_r (rad // 1)%Q); [ now apply Q.lt_0_pair | ].
  rewrite <- Q.mul_assoc, Q.mul_pair_den_num; [ | easy ].
  rewrite Q.mul_1_r, Q.mul_1_l.
  eapply Q.lt_le_trans; [ apply Hci2 | ].
  replace 1%Q with (1 // 1)%Q by easy.
  rewrite <- Q.pair_add_l.
  apply Q.le_pair; [ easy | easy | flia Hr ].
}
apply Q.intg_interv in Hci2; [ | now rewrite Ha ].
apply Q.nlt_ge in H1; apply H1; clear H1.
apply (Q.lt_le_trans _ ((rad - 2) // rad + 2 // rad)%Q). {
  apply Q.add_lt_mono_l.
  apply (Q.mul_lt_mono_pos_r (rad // 1)%Q); [ now apply Q.lt_0_pair | ].
  rewrite <- Q.mul_assoc, Q.mul_pair_den_num; [ | easy ].
  rewrite Q.mul_1_r, Q.mul_pair_den_num; [ now destruct Hci2 | easy ].
}
rewrite <- Q.pair_add_l.
rewrite Nat.sub_add; [ | easy ].
now rewrite Q.pair_diag.
Qed.

(* special case of sum_3_all_fA_true_8_not_8 *)
Theorem rad_2_sum_3_all_9_not_0_0 {r : radix} : ∀ u i,
  rad = 2
  → (∀ k, u (i + k) ≤ 3 * (rad - 1))
  → (∀ k, fA_ge_1_ε u i k = true)
  → u (i + 1) = 0
  → u (i + 2) ≠ 0.
Proof.
intros * Hr2 Hu3 Hau Hu1.
replace 0 with (rad - 2) in Hu1 at 2 |-* at 2 by flia Hr2.
now apply sum_3_all_fA_true_8_not_8.
Qed.

Theorem rad_2_sum_3_all_9_02_1_3 {r : radix} : ∀ u i,
  rad = 2
  → (∀ k, u (i + k) ≤ 3)
  → (∀ k, fA_ge_1_ε u i k = true)
  → u (i + 1) = 0 ∨ u (i + 1) = 2
  → u (i + 2) = 1
  → u (i + 3) = 3 ∧ carry u (i + 2) = 2.
Proof.
intros * Hr2 Hu3r Hau Hu10 Hu21.
assert (Hcu : ∀ k, carry u (i + k) < 3). {
  intros p.
  apply carry_upper_bound_for_adds; [ easy | ].
  intros q; rewrite <- Nat.add_assoc, Hr2; apply Hu3r.
}
assert (Hcu1 : carry u (i + 1) = 1). {
  specialize (all_fA_ge_1_ε_P_999 _ _ Hau 0) as Hpu1.
  rewrite Nat.add_0_r in Hpu1.
  unfold P, d2n, prop_carr, dig in Hpu1.
  assert (H : carry u (i + 1) mod 2 = 1). {
    destruct Hu10 as [Hu10| Hu12].
    -now rewrite Hu10, Hr2, Nat.add_0_l in Hpu1.
    -now rewrite Hu12, Hr2, Nat_mod_add_same_l in Hpu1.
  }
  clear Hpu1; rename H into Hpu1.
  specialize (Nat.div_mod (carry u (i + 1)) 2) as H1.
  assert (H : 2 ≠ 0) by easy.
  specialize (H1 H); clear H; rewrite Hpu1 in H1.
  rewrite H1, <- Nat.add_0_l; f_equal.
  specialize (Hcu 1).
  remember (carry u (i + 1)) as c eqn:Hc.
  destruct c; [ easy | ].
  destruct c; [ easy | exfalso ].
  destruct c; [ flia H1 | flia Hcu ].
}
assert (Hcu2 : carry u (i + 2) = 2 * ((carry u (i + 2) + 1) / 2)). {
  specialize (all_fA_ge_1_ε_P_999 _ _ Hau 1) as Hpu2.
  replace (i + 1 + 1) with (i + 2) in Hpu2 by flia.
  unfold P, d2n, prop_carr, dig in Hpu2.
  rewrite Hu21, Hr2 in Hpu2.
  specialize (Nat.div_mod (1 + carry u (i + 2)) 2) as H1.
  assert (H : 2 ≠ 0) by easy.
  specialize (H1 H); clear H; rewrite Hpu2, Nat.add_comm in H1.
  now apply Nat.add_cancel_r in H1.
}
remember (carry u (i + 2)) as c2 eqn:Hc2.
symmetry in Hc2.
destruct (Nat.eq_dec c2 0) as [Hc20| Hc20]. {
  exfalso.
  move Hc20 at top; subst c2; clear Hcu2.
  rename Hc2 into Hcu2.
  replace 3 with (3 * (rad - 1)) in Hu3r by flia Hr2.
  specialize (all_fA_ge_1_ε_carry_carry u i Hu3r Hau 1) as H1.
  replace (i + 1 + 1) with (i + 2) in H1 by flia.
  rewrite Hcu1, Hu21, Hcu2, Nat.add_0_r in H1.
  symmetry in H1.
  rewrite Q.intg_add_cond in H1; [ | easy | ]. 2: {
    now apply Q.le_0_mul_r.
  }
  rewrite Q.intg_small in H1. 2: {
    split; [ easy | ].
    replace 1%Q with (1 // 1)%Q by easy.
    apply Q.lt_pair_mono_l; [ flia Hr2 | pauto ].
  }
  rewrite (Q.frac_small (_ // _)%Q) in H1. 2: {
    replace 1%Q with (1 // 1)%Q by easy.
    split; [ easy | apply Q.lt_pair_mono_l; flia Hr2 ].
  }
  rewrite Nat.add_0_l in H1.
  assert
    (HF : (0 ≤ Q.frac (A (i + 2) (min_n (i + 2)) u) * 1 // rad < 1)%Q). {
    split; [ now apply Q.le_0_mul_r | ].
    apply (Q.mul_lt_mono_pos_r (rad // 1)%Q). {
      now apply Q.lt_0_pair.
    }
    rewrite <- Q.mul_assoc, Q.mul_pair_den_num; [ | easy ].
    rewrite Q.mul_1_r, Q.mul_1_l.
    eapply Q.lt_trans; [ apply Q.frac_lt_1 | ].
    replace 1%Q with (1 // 1)%Q by easy.
    apply Q.lt_pair_mono_r; flia Hr2.
  }
  rewrite Q.intg_small in H1; [ | easy ].
  rewrite Q.frac_small in H1; [ | easy ].
  rewrite Nat.add_0_l in H1.
  destruct
    (Q.lt_le_dec
       (1 // rad +
        Q.frac (A (i + 2) (min_n (i + 2)) u) *
        1 // rad)%Q 1) as [H6| H6]; [ easy | clear H1 ].
  apply Q.nlt_ge in H6; apply H6; clear H6.
  apply Q.lt_add_lt_sub_l.
  replace 1%Q with (1 // 1)%Q by easy.
  rewrite Q.sub_pair_pos; [ | easy | easy | flia Hr2 ].
  do 2 rewrite Nat.mul_1_l.
  rewrite <- (Q.mul_pair_den_num (rad - 1) 1); [ | easy ].
  apply Q.mul_lt_mono_pos_r; [ easy | ].
  eapply Q.lt_le_trans; [ apply Q.frac_lt_1 | ].
  replace 1%Q with (1 // 1)%Q by easy.
  apply Q.le_pair_mono_r; flia Hr2.
}
destruct (Nat.eq_dec c2 2) as [Hc22| Hc22]. {
  move Hc22 at top; subst c2; clear Hc20 Hcu2.
  rename Hc2 into Hcu2.
  specialize (all_fA_ge_1_ε_carry u i Hau 2) as H6.
  rewrite Hcu2 in H6; symmetry in H6.
  rewrite <- (all_fA_ge_1_ε_NQintg_A' 3) with (k := 0 + 1) in H6;
    cycle 1. {
    apply three_lt_rad_pow.
  } {
    intros p; rewrite Hr2.
    rewrite <- Nat.add_assoc; apply Hu3r.
  } {
    intros p.
    apply A_ge_1_add_r_true_if, Hau.
  }
  rewrite min_n_add, Nat.mul_1_r in H6.
  apply Q.intg_interv in H6; [ | easy ].
  rewrite A_split_first in H6; [ | min_n_ge ].
  replace (S (i + 2)) with (i + 3) in H6 by easy.
  remember (u (i + 3)) as u3 eqn:Hu3.
  symmetry in Hu3.
  destruct (Nat.eq_dec u3 0) as [Hu30| Hu30]. {
    exfalso; move Hu30 at top; subst u3.
    rewrite Q.add_0_l in H6.
    destruct H6 as (H6, _).
    apply Q.nlt_ge in H6; apply H6; clear H6.
    apply (Q.mul_lt_mono_pos_r (rad // 1)%Q); [ now apply Q.lt_0_pair | ].
    rewrite <- Q.mul_assoc, Q.mul_pair_den_num; [ | easy ].
    rewrite Q.mul_1_r.
    eapply Q.le_lt_trans. {
      apply (A_upper_bound_for_adds 3); rewrite Hr2.
      intros p; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
    }
    rewrite Q.mul_sub_distr_l, Q.mul_1_r.
    eapply Q.lt_le_trans; [ now apply Q.sub_lt | ].
    rewrite <- Q.pair_mul_l, Hr2.
    apply Q.le_pair_mono_r; cbn; pauto.
  }
  destruct (Nat.eq_dec u3 1) as [Hu31| Hu31]. {
    exfalso; move Hu31 at top; subst u3.
    clear Hu30.
    destruct H6 as (H6, _).
    apply Q.nlt_ge in H6; apply H6; clear H6.
    apply (Q.mul_lt_mono_pos_r (rad // 1)%Q). {
      now apply Q.lt_0_pair.
    }
    rewrite Q.mul_add_distr_r.
    apply Q.lt_add_lt_sub_l.
    rewrite <- Q.mul_assoc, Q.mul_pair_den_num; [ | easy ].
    rewrite Q.mul_1_r.
    eapply Q.le_lt_trans. {
      apply (A_upper_bound_for_adds 3); rewrite Hr2.
      intros p; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
    }
    rewrite Q.mul_sub_distr_l, Q.mul_1_r.
    eapply Q.lt_le_trans; [ now apply Q.sub_lt | ].
    now rewrite <- Q.pair_mul_l, Hr2.
  }
  destruct (Nat.eq_dec u3 2) as [Hu32| Hu32]. {
    exfalso; move Hu32 at top; subst u3.
    clear Hu30 Hu31.
    specialize (all_fA_ge_1_ε_P_999 _ _ Hau 2) as Hpu3.
    replace (i + 2 + 1) with (i + 3) in Hpu3 by flia.
    unfold P, d2n, prop_carr, dig in Hpu3.
    rewrite Hu3, Hr2 in Hpu3.
    rewrite Nat_mod_add_same_l in Hpu3; [ | easy ].
    replace (2 - 1) with 1 in Hpu3 by easy.
    rewrite Nat.mod_small in Hpu3. 2: {
      remember (carry u (i + 3)) as c eqn:Hc.
      destruct c; [ easy | ].
      destruct c; [ pauto | exfalso ].
      replace (S (S c)) with (2 + c) in Hpu3 by easy.
      rewrite Nat_mod_add_same_l in Hpu3; [ | easy ].
      destruct c; [ easy | ].
      specialize (Hcu 3) as H7.
      rewrite <- Hc in H7; flia H7.
    }
    unfold carry in Hpu3.
    rewrite (all_fA_ge_1_ε_NQintg_A' 3) in Hpu3; cycle 1. {
      apply three_lt_rad_pow.
    } {
      intros p; rewrite <- Nat.add_assoc, Hr2; apply Hu3r.
    } {
      intros p; apply A_ge_1_add_r_true_if, Hau.
    }
    replace (i + 3) with (i + 2 + 1) in Hpu3 at 2 by flia.
    rewrite min_n_add, Nat.mul_1_r in Hpu3.
    apply Q.intg_interv in Hpu3; [ | easy ].
    rewrite Hr2, Q.pair_diag in H6; [ | easy ].
    destruct H6 as (H6, _).
    replace (2 // 1)%Q with (1 + 1)%Q in H6 by easy.
    apply Q.add_le_mono_l in H6.
    destruct Hpu3 as (_, H).
    apply Q.nle_gt in H; apply H; clear H.
    apply (Q.mul_le_mono_pos_r 2%Q) in H6; [ | easy ].
    replace 2%Q with (2 // 1)%Q in H6 by easy.
    rewrite <- Q.mul_assoc in H6.
    rewrite Q.mul_pair_den_num in H6; [ | easy ].
    rewrite Q.mul_1_l, Q.mul_1_r in H6.
    now rewrite Hr2.
  }
  specialize (Hu3r 3) as H.
  rewrite Hu3 in H.
  flia Hu30 Hu31 Hu32 H.
}
exfalso.
specialize (Hcu 2) as H.
rewrite Hc2 in H.
destruct (Nat.eq_dec c2 1) as [Hc21| Hc21]; [ now rewrite Hc21 in Hcu2 | ].
flia H Hc20 Hc21 Hc22.
Qed.

Theorem rad_2_sum_3_all_9_3r2_3r2 {r : radix} : ∀ u i,
  rad = 2
  → (∀ k, u (i + k) ≤ 3 * (rad - 1))
  → (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k, u (i + k + 1) = 3 ∧ carry u (i + k) = 2
  → u (i + k + 2) = 3 ∧ carry u (i + k + 1) = 2.
Proof.
intros * Hr2 Hu3r Hau p IHp.
assert (Hc3 : ∀ k, carry u (i + k) < 3). {
  intros q.
  apply carry_upper_bound_for_adds; [ easy | ].
  intros s; rewrite <- Nat.add_assoc; apply Hu3r.
}
generalize IHp; intros H1.
destruct H1 as (Huv33, Hcw).
generalize Hcw; intros Hcuv2.
move Hcuv2 before Huv33.
unfold carry, d2n, prop_carr, dig in Hcw.
rewrite (all_fA_ge_1_ε_NQintg_A' 3) in Hcw; cycle 1. {
  apply three_lt_rad_pow.
} {
  intros; rewrite <- Nat.add_assoc; apply Hu3r.
} {
  intros; apply A_ge_1_add_r_true_if, Hau.
}
replace (i + p) with (i + p + 0) in Hcw at 2 by easy.
rewrite <- (all_fA_ge_1_ε_NQintg_A 3) with (l := rad) in Hcw; cycle 1. {
  apply three_lt_rad_pow.
} {
  intros; rewrite <- Nat.add_assoc; apply Hu3r.
} {
  intros; apply A_ge_1_add_r_true_if, Hau.
}
rewrite A_split_first in Hcw; [ | min_n_ge ].
rewrite Nat.add_0_r in Hcw.
remember (min_n (i + p) + rad) as nr eqn:Hnr.
replace (S (i + p)) with (i + p + 1) in Hcw by flia.
rewrite Huv33 in Hcw.
rewrite Q.intg_add_cond in Hcw; [ | easy | ]. 2: {
  now apply Q.le_0_mul_r.
}
rewrite Hr2 in Hcw.
rewrite Q.intg_pair in Hcw; [ | easy ].
symmetry in Hcw; rewrite <- Nat.add_assoc in Hcw.
replace 2 with (1 + 1) in Hcw at 1 by easy.
apply Nat.add_cancel_l in Hcw; symmetry in Hcw.
rewrite Q.frac_pair in Hcw.
replace (3 mod 2) with 1 in Hcw by easy.
destruct
  (Q.lt_le_dec
     ((1 // 2)%Q + Q.frac (A (i + p + 1) nr u * (1 // 2)%Q)) 1)
  as [H1| H1]. {
  rewrite Nat.add_0_r in Hcw.
  apply Q.intg_interv in Hcw; [ | now apply Q.le_0_mul_r ].
  assert (HA : Q.intg (A (i + p + 1) nr u) = 2). {
    apply Q.intg_interv; [ easy | ].
    split. {
      apply (Q.mul_le_mono_pos_r (1 // 2)%Q); [ easy | ].
      now destruct Hcw.
    }
    rewrite <- (Q.pair_add_l _ 1).
    replace (2 + 1) with 3 by easy.
    eapply Q.le_lt_trans. {
      apply (A_upper_bound_for_adds 3).
      intros; do 3 rewrite <- Nat.add_assoc; apply Hu3r.
    }
    rewrite Q.mul_sub_distr_l, Q.mul_1_r.
    now apply Q.sub_lt.
  }
  assert (Hcuv3 : carry u (i + p + 1) = 2). {
    unfold carry.
    rewrite (all_fA_ge_1_ε_NQintg_A' 3); cycle 1. {
      apply three_lt_rad_pow.
    } {
      intros; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
    } {
      intros; rewrite <- Nat.add_assoc; apply A_ge_1_add_r_true_if, Hau.
    }
    now rewrite min_n_add, Nat.mul_1_r, <- Hnr.
  }
  move Hcuv3 before Hcuv2.
  unfold carry, d2n, prop_carr, dig.
  rewrite (all_fA_ge_1_ε_NQintg_A' 3); cycle 1. {
    apply three_lt_rad_pow.
  } {
    intros; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
  } {
    intros; rewrite <- Nat.add_assoc; apply A_ge_1_add_r_true_if, Hau.
  }
  rewrite min_n_add, Nat.mul_1_r, <- Hnr.
  split; [ | easy ].
  rewrite A_split_first in HA; [ | rewrite Hnr; min_n_ge ].
  rewrite Q.intg_add_cond in HA; [ | apply Q.le_0_pair | ]. 2: {
    now apply Q.le_0_mul_r.
  }
  replace (S (i + p + 1)) with (i + p + 2) in HA by flia.
  rewrite A_split_first in Hcw; [ | rewrite Hnr; min_n_ge ].
  replace (S (i + p + 1)) with (i + p + 2) in Hcw by flia.
  rewrite Hr2 in Hcw, HA.
  remember (u (i + p + 2)) as x eqn:Hx; symmetry in Hx.
  destruct (Nat.eq_dec x 0) as [Hx0| Hx0]. {
    exfalso.
    move Hx0 at top; subst x.
    rewrite Q.add_0_l in Hcw.
    destruct Hcw as (H, _).
    apply Q.nlt_ge in H; apply H; clear H.
    apply (Q.mul_lt_mono_pos_r (4 // 1)%Q); [ easy | ].
    do 2 rewrite <- Q.mul_assoc.
    rewrite Q.mul_pair; [ | easy | easy ].
    rewrite Q.mul_pair; [ | easy | easy ].
    rewrite Q.pair_diag; [ | easy ].
    rewrite Q.mul_1_r, Q.mul_1_l.
    eapply Q.le_lt_trans. {
      apply (A_upper_bound_for_adds 3).
      intros; do 3 rewrite <- Nat.add_assoc; apply Hu3r.
    }
    rewrite Q.mul_sub_distr_l, Q.mul_1_r.
    eapply Q.lt_trans; [ now apply Q.sub_lt | ].
    apply Q.lt_pair_mono_r; pauto.
  }
  destruct
  (Q.lt_le_dec
     (Q.frac (x // 2) + Q.frac (A (i + p + 2) nr u * (1 // 2)%Q)) 1)
    as [H6| H6]. {
    rewrite Nat.add_0_r in HA.
    destruct (Nat.eq_dec x 1) as [Hx1| Hx1]. {
      exfalso; clear Hx0.
      move Hx1 at top; subst x.
      rewrite Q.intg_small in HA. 2: {
        split; [ easy | ].
        apply (Q.lt_pair_mono_l 1); pauto.
      }
      rewrite Nat.add_0_l in HA.
      apply Q.intg_interv in HA; [ | now apply Q.le_0_mul_r ].
      destruct HA as (H, _).
      apply Q.nlt_ge in H; apply H; clear H.
      apply (Q.mul_lt_mono_pos_r 2%Q); [ easy | ].
      rewrite <- Q.mul_assoc.
      rewrite (Q.mul_pair _ _ 2 1); [ | easy | easy ].
      rewrite Q.pair_diag; [ | easy ].
      rewrite Q.mul_1_r.
      eapply Q.le_lt_trans. {
        apply (A_upper_bound_for_adds 3).
        intros; do 3 rewrite <- Nat.add_assoc; apply Hu3r.
      }
      rewrite Q.mul_sub_distr_l, Q.mul_1_r.
      eapply Q.lt_trans; [ now apply Q.sub_lt | ].
      rewrite <- (Q.pair_mul_r _ 2 1).
      apply Q.lt_pair_mono_r; pauto.
    }
    destruct (Nat.eq_dec x 2) as [Hx2| Hx2]. {
      exfalso; clear Hx0 Hx1 H6 Hcw.
      move Hx2 at top; subst x.
      rename Hx into Huv42; move Huv42 before Huv33.
      rewrite Q.pair_diag, Q.intg_1 in HA; [ | easy ].
      replace 2 with (1 + 1) in HA at 3 by easy.
      apply Nat.add_cancel_l in HA.
      apply Q.intg_interv in HA; [ | now apply Q.le_0_mul_r ].
      specialize (all_fA_ge_1_ε_P_999 _ _ Hau (p + 1)) as H7.
      unfold P, d2n, prop_carr, dig in H7.
      replace (i + (p + 1) + 1) with (i + p + 2) in H7 by flia.
      rewrite Huv42 in H7.
      rewrite Hr2 in H7.
      rewrite Nat_mod_add_same_l in H7; [ | easy ].
      rewrite Nat.mod_small in H7. 2: {
        remember (carry u (i + p + 2)) as x eqn:Hx.
        symmetry in Hx.
        destruct x; [ now rewrite Nat.mod_0_l in H7 | ].
        destruct x; [ pauto | exfalso ].
        replace (S (S x)) with (2 + x) in H7 by easy.
        rewrite Nat_mod_add_same_l in H7; [ | easy ].
        destruct x; [ now rewrite Nat.mod_0_l in H7 | ].
        specialize (Hc3 (p + 2)) as H.
        rewrite Nat.add_assoc in H.
        flia Hx H.
      }
      cbn in H7.
      rename H7 into Hcuv4.
      move Hcuv4 before Hcuv3.
      generalize Hcuv3; intros H7.
      generalize Hcuv4; intros H8.
      unfold carry in H7, H8.
      rewrite (all_fA_ge_1_ε_NQintg_A' 3) in H7; cycle 1. {
        apply three_lt_rad_pow.
      } {
        intros; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
      } {
        intros; rewrite <- Nat.add_assoc.
        apply A_ge_1_add_r_true_if, Hau.
      }
      rewrite (all_fA_ge_1_ε_NQintg_A' 3) in H8; cycle 1. {
        apply three_lt_rad_pow.
      } {
        intros; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
      } {
        intros; rewrite <- Nat.add_assoc.
        apply A_ge_1_add_r_true_if, Hau.
      }
      rewrite <- (Nat.add_0_r (i + p + 1)) in H7 at 2 by easy.
      rewrite <- (all_fA_ge_1_ε_NQintg_A 3) with (l := rad) in H7; cycle 1. {
        apply three_lt_rad_pow.
      } {
        intros; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
      } {
        intros; rewrite <- Nat.add_assoc.
        apply A_ge_1_add_r_true_if, Hau.
      }
      rewrite Nat.add_0_r in H7.
      replace (i + p + 2) with (i + p + 1 + 1) in H8 at 2 by flia.
      rewrite min_n_add, Nat.mul_1_r in H8.
      rewrite A_split_first in H7; [ | min_n_ge ].
      replace (S (i + p + 1)) with (i + p + 2) in H7 by flia.
      rewrite Huv42 in H7.
      rewrite Hr2 in H7 at 1.
      rewrite Q.pair_diag in H7; [ | easy ].
      rewrite (Q.intg_add_nat_l 1) in H7; [ | now apply Q.le_0_mul_r ].
      replace 2 with (1 + 1) in H7 at 3 by easy.
      apply Nat.add_cancel_l in H7.
      remember (A (i + p + 2) (min_n (i + p + 2) + rad) u) as x eqn:Hx.
      apply Q.intg_interv in H7; [ | now apply Q.le_0_mul_r; subst x ].
      apply Q.intg_interv in H8; [ | now subst x ].
      destruct H7 as (H7, _).
      destruct H8 as (_, H8).
      apply (Q.mul_le_mono_pos_r 2%Q) in H7; [ | easy ].
      rewrite <- Q.mul_assoc in H7.
      rewrite (Q.mul_pair _ _ 2 1) in H7; [ | easy | easy ].
      do 2 rewrite Nat.mul_1_l in H7.
      replace (1 + 1)%Q with 2%Q in H8 by easy.
      rewrite Hr2 in H7, H8.
      rewrite (Q.mul_pair_den_num _ 2 1) in H7; [ | easy ].
      rewrite Q.mul_1_r in H7.
      now apply Q.nlt_ge in H7.
    }
    specialize (Hu3r (p + 2)) as H.
    rewrite Nat.add_assoc, Hx, Hr2 in H.
    flia Hx0 Hx1 Hx2 H.
  }
  replace (i + S p + 1) with (i + p + 2) in Hx, Hcw, H6, HA by flia.
  destruct (Nat.eq_dec x 1) as [Hx1| Hx1]. {
    exfalso; clear Hx0.
    move Hx1 at top; subst x.
    rename Hx into Huv41; move Huv41 before Huv33.
    rewrite Q.intg_small in HA. 2: {
      split; [ easy | ].
      apply (Q.lt_pair_mono_l 1); pauto.
    }
    rewrite Nat.add_0_l in HA.
    replace 2 with (1 + 1) in HA at 3 by easy.
    apply Nat.add_cancel_r in HA.
    apply Q.intg_interv in HA; [ | now apply Q.le_0_mul_r ].
    generalize Hcuv3; intros Hc3'.
    unfold carry in Hc3'.
    rewrite (all_fA_ge_1_ε_NQintg_A' 3) in Hc3'; cycle 1. {
      apply three_lt_rad_pow.
    } {
      intros; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
    } {
      intros; rewrite <- Nat.add_assoc.
      apply A_ge_1_add_r_true_if, Hau.
    }
    rewrite A_split_first in Hc3'; [ | min_n_ge ].
    replace (S (i + p + 1)) with (i + p + 2) in Hc3' by flia.
    rewrite Huv41 in Hc3'.
    apply Q.intg_interv in Hc3'. 2: {
      apply Q.le_0_add; [ easy | now apply Q.le_0_mul_r ].
    }
    destruct Hc3' as (H, _).
    apply Q.nlt_ge in H; apply H; clear H.
    apply Q.lt_add_lt_sub_l; rewrite Hr2.
    apply (Q.mul_lt_mono_pos_r 2%Q); [ easy | ].
    rewrite <- Q.mul_assoc.
    rewrite (Q.mul_pair_den_num _ 2 1); [ | easy ].
    rewrite Q.mul_1_r.
    eapply Q.le_lt_trans. {
      apply (A_upper_bound_for_adds 3).
      intros; do 3 rewrite <- Nat.add_assoc; apply Hu3r.
    }
    rewrite Q.mul_sub_distr_l, Q.mul_1_r.
    eapply Q.lt_le_trans; [ now apply Q.sub_lt | ].
    rewrite Q.sub_pair_pos; [ | easy | easy | flia ].
    do 2 rewrite Nat.mul_1_l.
    replace (2 * 2 - 1) with 3 by easy.
    now rewrite (Q.mul_pair_den_num _ 2 1).
  }
  destruct (Nat.eq_dec x 2) as [Hx2| Hx2]. {
    exfalso; clear Hx0 Hx1.
    move Hx2 at top; subst x.
    rename Hx into Huv42; move Huv42 before Huv33.
    rewrite Q.pair_diag, Q.intg_1 in HA; [ | easy ].
    replace 2 with (1 + 0 + 1) in HA at 3 by easy.
    apply Nat.add_cancel_r in HA.
    apply Nat.add_cancel_l in HA.
    apply Q.eq_intg_0 in HA; [ | now apply Q.le_0_mul_r ].
    specialize (all_fA_ge_1_ε_P_999 _ _ Hau (p + 1)) as H7.
    unfold P, d2n, prop_carr, dig in H7.
    replace (i + (p + 1) + 1) with (i + p + 2) in H7 by flia.
    rewrite Huv42 in H7.
    rewrite Hr2 in H7.
    rewrite Nat_mod_add_same_l in H7; [ | easy ].
    rewrite Nat.mod_small in H7. 2: {
      remember (carry u (i + p + 2)) as x eqn:Hx.
      symmetry in Hx.
      destruct x; [ now rewrite Nat.mod_0_l in H7 | ].
      destruct x; [ pauto | exfalso ].
      replace (S (S x)) with (2 + x) in H7 by easy.
      rewrite Nat_mod_add_same_l in H7; [ | easy ].
      destruct x; [ now rewrite Nat.mod_0_l in H7 | ].
      specialize (Hc3 (p + 2)) as H.
      rewrite Nat.add_assoc in H.
      flia Hx H.
    }
    cbn in H7.
    rename H7 into Hcuv4.
    move Hcuv4 before Hcuv3.
    generalize Hcuv3; intros H7.
    generalize Hcuv4; intros H8.
    unfold carry in H7, H8.
    rewrite (all_fA_ge_1_ε_NQintg_A' 3) in H7; cycle 1. {
      apply three_lt_rad_pow.
    } {
      intros; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
    } {
      intros; rewrite <- Nat.add_assoc.
      apply A_ge_1_add_r_true_if, Hau.
    }
    rewrite (all_fA_ge_1_ε_NQintg_A' 3) in H8; cycle 1. {
      apply three_lt_rad_pow.
    } {
      intros; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
    } {
      intros; rewrite <- Nat.add_assoc.
      apply A_ge_1_add_r_true_if, Hau.
    }
    rewrite <- (Nat.add_0_r (i + p + 1)) in H7 at 2 by easy.
    rewrite <- (all_fA_ge_1_ε_NQintg_A 3) with (l := rad) in H7; cycle 1. {
      apply three_lt_rad_pow.
    } {
      intros; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
    } {
      intros; rewrite <- Nat.add_assoc.
      apply A_ge_1_add_r_true_if, Hau.
    }
    rewrite Nat.add_0_r in H7.
    replace (i + p + 2) with (i + p + 1 + 1) in H8 at 2 by flia.
    rewrite min_n_add, Nat.mul_1_r in H8.
    rewrite A_split_first in H7; [ | min_n_ge ].
    replace (S (i + p + 1)) with (i + p + 2) in H7 by flia.
    rewrite Huv42 in H7.
    rewrite Hr2 in H7 at 1.
    rewrite Q.pair_diag in H7; [ | easy ].
    rewrite (Q.intg_add_nat_l 1) in H7; [ | now apply Q.le_0_mul_r ].
    replace 2 with (1 + 1) in H7 at 3 by easy.
    apply Nat.add_cancel_l in H7.
    remember (A (i + p + 2) (min_n (i + p + 1) + rad) u) as x eqn:Hx.
    rewrite Hr2 in H7.
    apply Q.intg_interv in H7; [ | now apply Q.le_0_mul_r; subst x ].
    apply Q.intg_interv in H8; [ | now subst x ].
    destruct H7 as (H7, _).
    destruct H8 as (_, H8).
    apply (Q.mul_le_mono_pos_r 2%Q) in H7; [ | easy ].
    rewrite <- Q.mul_assoc in H7.
    rewrite (Q.mul_pair _ _ 2 1) in H7; [ | easy | easy ].
    do 2 rewrite Nat.mul_1_l in H7.
    replace (1 + 1)%Q with 2%Q in H8 by easy.
    rewrite (Q.mul_pair_den_num _ 2 1) in H7; [ | easy ].
    rewrite Q.mul_1_r in H7.
    now apply Q.nlt_ge in H7.
  }
  specialize (Hu3r (p + 2)) as H.
  rewrite Nat.add_assoc, Hx, Hr2 in H.
  flia Hx0 Hx1 Hx2 H.
}
exfalso.
replace 1 with (0 + 1) in Hcw at 5 by easy.
apply Nat.add_cancel_r in Hcw.
apply Q.eq_intg_0 in Hcw; [ | now apply Q.le_0_mul_r ].
apply (Q.mul_lt_mono_pos_r 2%Q) in Hcw; [ | easy ].
rewrite <- Q.mul_assoc in Hcw.
rewrite (Q.mul_pair_den_num _ 2 1) in Hcw; [ | easy ].
rewrite Q.mul_1_r, Q.mul_1_l in Hcw.
apply Q.le_sub_le_add_l in H1.
rewrite (Q.sub_pair_pos 1 1) in H1; [ | easy | easy | cbn; pauto ].
do 2 rewrite Nat.mul_1_l in H1.
replace (2 - 1) with 1 in H1 by easy.
assert (Hcuv3x : carry u (i + p + 1) < 2). {
  unfold carry.
  rewrite (all_fA_ge_1_ε_NQintg_A' 3); cycle 1. {
    apply three_lt_rad_pow.
  } {
    intros; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
  } {
    intros; rewrite <- Nat.add_assoc.
    apply A_ge_1_add_r_true_if, Hau.
  }
  rewrite min_n_add, Nat.mul_1_r, <- Hnr.
  apply Nat.lt_succ_r.
  rewrite (Q.intg_frac (A _ _ _)) in Hcw; [ | easy ].
  eapply Q.le_lt_trans in Hcw; [ | now apply Q.le_add_r ].
  apply (Q.lt_pair _ _ 2 1) in Hcw; [ flia Hcw | easy | easy ].
}
remember (carry u (i + p + 1)) as ci eqn:Hcuv3.
symmetry in Hcuv3; move Hcuv3 before Hcuv2.
move ci before p.
destruct (Nat.eq_dec ci 0) as [Hci0| Hci0]. {
  move Hci0 at top; subst ci; clear Hcuv3x.
  generalize Hcuv2; intros H6.
  generalize Hcuv3; intros H7.
  unfold carry in H6, H7.
  rewrite (all_fA_ge_1_ε_NQintg_A' 3) in H6; cycle 1. {
    apply three_lt_rad_pow.
  } {
    intros; rewrite <- Nat.add_assoc; apply Hu3r.
  } {
    intros; apply A_ge_1_add_r_true_if, Hau.
  }
  rewrite (all_fA_ge_1_ε_NQintg_A' 3) in H7; cycle 1. {
    apply three_lt_rad_pow.
  } {
    intros; do 2 rewrite <- Nat.add_assoc; apply Hu3r.
  } {
    intros; rewrite <- Nat.add_assoc.
    apply A_ge_1_add_r_true_if, Hau.
  }
  rewrite <- (Nat.add_0_r (i + p)) in H6 at 2 by easy.
  rewrite <- (all_fA_ge_1_ε_NQintg_A 3) with (l := rad) in H6; cycle 1. {
    apply three_lt_rad_pow.
  } {
    intros; rewrite <- Nat.add_assoc; apply Hu3r.
  } {
    intros; apply A_ge_1_add_r_true_if, Hau.
  }
  rewrite Nat.add_0_r in H6.
  rewrite min_n_add, Nat.mul_1_r in H7.
  rewrite A_split_first in H6; [ | min_n_ge ].
  replace (S (i + p)) with (i + p + 1) in H6 by flia.
  rewrite Huv33 in H6.
  remember (A (i + p + 1) (min_n (i + p) + rad) u) as x eqn:Hx.
  apply Q.intg_interv in H6. 2: {
    rewrite Hr2, Hx.
    apply Q.le_0_add; [ easy | ].
    now apply Q.le_0_mul_r.
  }
  apply Q.eq_intg_0 in H7; [ | now rewrite Hx ].
  destruct H6 as (H6, _).
  apply Q.nlt_ge in H6; apply H6; clear H6.
  rewrite Hr2.
  apply Q.lt_add_lt_sub_l.
  rewrite Q.sub_pair_pos; [ | easy | easy | cbn; pauto ].
  do 2 rewrite Nat.mul_1_l.
  replace (2 * 2 - 3) with 1 by easy.
  replace (1 // 2)%Q with (1 * (1 // 2))%Q at 2 by easy.
  now apply Q.mul_lt_mono_pos_r.
}
destruct (Nat.eq_dec ci 1) as [Hci1| Hci1]. {
  move Hci1 at top; subst ci; clear Hci0 Hcuv3x.
  specialize (all_fA_ge_1_ε_P_999 _ _ Hau p) as H6.
  unfold P, d2n, prop_carr, dig in H6.
  now rewrite Huv33, Hcuv3, Hr2 in H6.
}
flia Hcuv3x Hci0 Hci1.
Qed.

Theorem rad_2_sum_3_all_9_02_222_123 {r : radix} : ∀ j u i,
  rad = 2
  → (∀ k, u (i + k + 1) ≤ 3)
  → (∀ k, fA_ge_1_ε u i k = true)
  → u (i + 1) = 0 ∨ u (i + 1) = 2
  → (∀ k, k < j → u (i + k + 2) = 2)
  → u (i + j + 2) = 1 ∨ u (i + j + 2) = 2 ∨ u (i + j + 2) = 3.
Proof.
intros * Hr2 Hu3r Hau Hu1 Huk.
assert (Hcu : ∀ k, carry u (i + k) < 3). {
  apply carry_upper_bound_for_adds; [ easy | now rewrite Hr2 ].
}
assert (Hcu2 :  ∀ k, k ≤ j → carry u (i + k + 1) = 1). {
  intros k Hk.
  specialize (all_fA_ge_1_ε_P_999 _ _ Hau k) as Hpu2.
  unfold P, d2n, prop_carr, dig in Hpu2.
  rewrite Hr2 in Hpu2.
  destruct (Nat.eq_dec (carry u (i + k + 1)) 2) as [Hc2| Hc2]. {
    exfalso.
    rewrite Hc2, Nat_mod_add_same_r in Hpu2; [ | easy ].
    destruct k. {
      rewrite Nat.add_0_r in Hpu2.
      now destruct Hu1 as [H| H]; rewrite H in Hpu2.
    }
    assert (H : k < j) by flia Hk.
    specialize (Huk _ H) as H1.
    replace (i + k + 2) with (i + S k + 1) in H1 by flia.
    now rewrite H1 in Hpu2.
  }
  specialize (Hcu (k + 1)) as H1.
  rewrite Nat.add_assoc in H1.
  destruct k. {
    rewrite Nat.add_0_r in Hpu2, Hc2, H1 |-*.
    destruct Hu1 as [Hu1| Hu1]. {
      rewrite Hu1, Nat.add_0_l in Hpu2.
      rewrite Nat.mod_small in Hpu2; [ easy | flia Hc2 H1 ].
    }
    rewrite Hu1, Nat_mod_add_same_l in Hpu2; [ | easy ].
    rewrite Nat.mod_small in Hpu2; [ easy | flia Hc2 H1 ].
  }
  assert (H : k < j) by flia Hk.
  specialize (Huk _ H) as H2; clear H.
  replace (i + k + 2) with (i + S k + 1) in H2 by flia.
  rewrite H2, Nat_mod_add_same_l in Hpu2; [ | easy ].
  rewrite Nat.mod_small in Hpu2; [ easy | flia Hc2 H1 ].
}
assert (H : u (i + j + 2) ≠ 0). {
  intros Hu30; move Hu30 before Huk.
  specialize (all_fA_ge_1_ε_P_999 _ _ Hau (j + 1)) as Hpu2.
  replace (i + (j + 1) + 1) with (i + j + 2) in Hpu2 by flia.
  unfold P, d2n, prop_carr, dig in Hpu2.
  rewrite Hu30, Nat.add_0_l, Hr2 in Hpu2.
  specialize (Hcu (j + 2)) as H1.
  rewrite Nat.add_assoc in H1.
  remember (carry u (i + j + 2)) as c eqn:Hc.
  symmetry in Hc.
  destruct c; [ easy | ].
  destruct c. {
    clear Hpu2 H1.
    unfold carry in Hc.
    rewrite (all_fA_ge_1_ε_NQintg_A' 3) in Hc; cycle 1. {
      apply three_lt_rad_pow.
    } {
      intros p; rewrite Hr2.
      now replace (i + j + 2 + p) with (i + (j + p + 1) + 1) by flia.
    } {
      intros p; rewrite <- Nat.add_assoc.
      now apply A_ge_1_add_r_true_if.
    }
    specialize (Hcu2 _ (le_refl _)) as H1.
    unfold carry in H1.
    rewrite (all_fA_ge_1_ε_NQintg_A' 3) in H1; cycle 1. {
      apply three_lt_rad_pow.
    } {
      intros p; rewrite Hr2.
      now replace (i + j + 1 + p) with (i + (j + p) + 1) by flia.
    } {
      intros p; rewrite <- Nat.add_assoc.
      now apply A_ge_1_add_r_true_if.
    }
    rewrite <- (Nat.add_0_r (i + j + 1)) in H1 at 2.
    rewrite <- (all_fA_ge_1_ε_NQintg_A 3) with (l := rad) in H1; cycle 1. {
      apply three_lt_rad_pow.
    } {
      intros p; rewrite Hr2.
      now replace (i + j + 1 + p) with (i + (j + p) + 1) by flia.
    } {
      intros p; rewrite <- Nat.add_assoc.
      now apply A_ge_1_add_r_true_if.
    }
    rewrite Nat.add_0_r in H1.
    rewrite A_split_first in H1; [ | min_n_ge ].
    replace (S (i + j + 1)) with (i + j + 2) in H1 by easy.
    rewrite Hu30, Q.add_0_l in H1.
    replace (i + j + 2) with (i + j + 1 + 1) in Hc at 2 by flia.
    rewrite min_n_add, Nat.mul_1_r in Hc.
    apply Q.intg_interv in H1; [ | now apply Q.le_0_mul_r ].
    apply Q.intg_interv in Hc; [ | easy ].
    destruct Hc as (_, Hc); rewrite Hr2 in Hc.
    apply Q.nle_gt in Hc; apply Hc; clear Hc.
    destruct H1 as (H1, _).
    apply (Q.mul_le_mono_pos_r 2%Q) in H1; [ | easy ].
    rewrite <- Q.mul_assoc, Hr2 in H1.
    rewrite (Q.mul_pair_den_num _ 2 1) in H1; [ | easy ].
    rewrite Q.mul_1_l, Q.mul_1_r in H1.
    now replace (1 // 1 + 1)%Q with 2%Q.
  }
  destruct c; [ easy | flia H1 ].
}
specialize (Hu3r (j + 1)) as H1.
replace (i + (j + 1) + 1) with (i + j + 2) in H1 by flia.
flia H H1.
Qed.

Theorem rad_2_sum_3_all_9_02_123 {r : radix} : ∀ u i,
  rad = 2
  → (∀ k, u (i + k + 1) ≤ 3)
  → (∀ k, fA_ge_1_ε u i k = true)
  → u (i + 1) = 0 ∨ u (i + 1) = 2
  → u (i + 2) = 1 ∨ u (i + 2) = 2 ∨ u (i + 2) = 3.
Proof.
intros * Hr2 Hu3r Hau Hu1.
rewrite <- (Nat.add_0_r i).
now apply rad_2_sum_3_all_9_02_222_123.
Qed.

Theorem rad_2_sum_3_all_9_02_222_13 {r : radix} : ∀ j u i,
  rad = 2
  → (∀ k, u (i + k + 1) ≤ 3)
  → (∀ k, fA_ge_1_ε u i k = true)
  → u (i + 1) = 0 ∨ u (i + 1) = 2
  → (∀ k, k < j → u (i + k + 2) = 2)
  → (∀ k, u (i + k + 2) = 2) ∨
    ∃ k, (∀ p, p < k → u (i + p + 2) = 2) ∧
     (u (i + k + 2) = 1 ∨ u (i + k + 2) = 3).
Proof.
intros * Hr2 Hu3r Hau Hu1 Huk.
destruct (LPO_fst (λ k, Nat.eqb (u (i + k + 2)) 2)) as [H1| H1]. {
  now left; intros; apply Nat.eqb_eq.
}
destruct H1 as (k & Hjk & Hk).
right; exists k.
apply Nat.eqb_neq in Hk.
specialize (rad_2_sum_3_all_9_02_222_123 k u i Hr2 Hu3r Hau Hu1) as H1.
assert (H : ∀ p, p < k → u (i + p + 2) = 2). {
  now intros; apply Nat.eqb_eq; apply Hjk.
}
split; [ easy | ].
specialize (H1 H); clear H.
destruct H1 as [H1| H1]; [ now left | ].
destruct H1 as [H1| H1]; [ easy | now right ].
Qed.

Theorem rad_2_sum_3_all_9_02_1_333 {r : radix} : ∀ u i,
  rad = 2
  → (∀ k, u (i + k) ≤ 3)
  → (∀ k, fA_ge_1_ε u i k = true)
  → u (i + 1) = 0 ∨ u (i + 1) = 2
  → u (i + 2) = 1
  → ∀ k, u (i + k + 3) = 3 ∧ carry u (i + k + 2) = 2.
Proof.
intros * Hr2 Hu3r Hau Hu10 Hu21 p.
induction p. {
  rewrite Nat.add_0_r.
  now apply rad_2_sum_3_all_9_02_1_3.
}
clear - Hr2 Hu3r IHp Hau.
replace (i + S p + 3) with (i + (p + 2) + 2) by flia.
replace (i + S p + 2) with (i + (p + 2) + 1) by flia.
replace (i + p + 3) with (i + (p + 2) + 1) in IHp by flia.
replace (i + p + 2) with (i + (p + 2)) in IHp by flia.
apply rad_2_sum_3_all_9_3r2_3r2; try easy; now rewrite Hr2.
Qed.

Theorem rad_2_sum_3_all_9_02_222_1_333 {r : radix} : ∀ u i j,
  rad = 2
  → (∀ k, u (i + k) ≤ 3)
  → (∀ k, fA_ge_1_ε u i k = true)
  → u (i + 1) = 0 ∨ u (i + 1) = 2
  → (∀ k, k < j → u (i + k + 2) = 2)
  → u (i + j + 2) = 1
  → ∀ k, u (i + j + k + 3) = 3 ∧ carry u (i + j + k + 2) = 2.
Proof.
intros * Hr2 Hur3 Hau Hu1 Hu2 Huj2 k.
revert i Hur3 Hau Hu1 Hu2 Huj2.
induction j; intros. {
  rewrite Nat.add_0_r in Huj2 |-*.
  now apply rad_2_sum_3_all_9_02_1_333.
}
specialize (IHj (i + 1)).
assert (H : ∀ k, u (i + 1 + k) ≤ 3) by now intros; rewrite <- Nat.add_assoc.
specialize (IHj H); clear H.
assert (H : ∀ k, fA_ge_1_ε u (i + 1) k = true). {
  now intros; apply A_ge_1_add_r_true_if.
}
specialize (IHj H); clear H.
assert (H : u (i + 1 + 1) = 0 ∨ u (i + 1 + 1) = 2). {
  right.
  replace (i + 1 + 1) with (i + 0 + 2) by flia.
  apply Hu2, Nat.lt_0_succ.
}
specialize (IHj H); clear H.
assert (H : ∀ k, k < j → u (i + 1 + k + 2) = 2). {
  intros p Hp.
  replace (i + 1 + p + 2) with (i + (p + 1) + 2) by flia.
  apply Hu2; flia Hp.
}
specialize (IHj H); clear H.
replace (i + 1 + j + 2) with (i + S j + 2) in IHj by flia.
specialize (IHj Huj2).
replace (i + S j + k + 3) with (i + 1 + j + k + 3) by flia.
replace (i + S j + k + 2) with (i + 1 + j + k + 2) by flia.
easy.
Qed.

Theorem rad_2_sum_3_all_9_0_1_A_lt_1 {r : radix} : ∀ u v i n,
  rad = 2
  → (∀ k, u (i + k) ≤ 1)
  → (∀ k, v (i + k) ≤ 2)
  → (∀ k, fA_ge_1_ε (u ⊕ v) i k = true)
  → (u ⊕ v) (i + 1) = 0
  → (u ⊕ v) (i + 2) = 1
  → (A i n (u ⊕ P v) < 1)%Q.
Proof.
intros * Hr2 Hu Hv Hauv Huv10 Huv21 *.
assert (Huv3 : ∀ k, (u ⊕ v) (i + k) ≤ 3). {
  intros p.
  unfold "⊕"; replace 3 with (1 + 2) by easy.
  apply Nat.add_le_mono; [ apply Hu | apply Hv ].
}
remember (u ⊕ v) as w eqn:Hw.
assert (Huv33 : ∀ k, w (i + k + 3) = 3 ∧ carry w (i + k + 2) = 2). {
  intros p.
  apply rad_2_sum_3_all_9_02_1_333; try easy; now left.
}
move Huv3 before Hv; move w before v; move Hw after Hu.
clear - Hr2 Hw Huv10 Hu Huv21 Huv33 Hv.
destruct (lt_dec (n - 1) (i + 1)) as [Hin| Hin]. {
  now unfold A; rewrite summation_empty.
}
apply Nat.nlt_ge in Hin.
rewrite A_additive.
rewrite A_split_first; [ | easy ].
rewrite <- Nat.add_1_r.
replace (u (i + 1)) with 0. 2: {
  rewrite Hw in Huv10.
  now apply Nat.eq_add_0 in Huv10.
}
rewrite Q.add_0_l.
rewrite (A_split_first _ _ (P _)); [ | easy ].
rewrite <- (Nat.add_1_r i).
rewrite Q.add_assoc, Q.add_add_swap, <- Q.mul_add_distr_r.
rewrite <- A_additive.
remember (P v (i + 1)) as pv eqn:Hpv.
destruct pv. {
  rewrite Q.add_0_r; rewrite Hr2.
  apply rad_2_sum_2_half_A_lt_1; [ easy | ].
  intros p; rewrite <- Nat.add_assoc; unfold "⊕".
  replace 2 with (1 + 1) by easy.
  apply Nat.add_le_mono; [ apply Hu | ].
  replace 1 with (rad - 1) by flia Hr2.
  apply P_le.
}
destruct pv. {
  apply Q.lt_add_lt_sub_r.
  rewrite Hr2.
  replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
  apply Q.mul_lt_mono_pos_r; [ easy | ].
  destruct (lt_dec (n - 1) (i + 1 + 1)) as [Hin2| Hin2]. {
    now unfold A; rewrite summation_empty.
  }
  apply Nat.nlt_ge in Hin2.
  rewrite A_split_first; [ | easy ].
  replace (S (i + 1)) with (i + 2) by flia.
  generalize Huv21; intros H1.
  rewrite Hw in H1; unfold "⊕" in H1.
  apply Nat.eq_add_1 in H1.
  destruct H1 as [H1| H1]. {
    unfold "⊕" at 1; rewrite (proj1 H1).
    remember (P v (i + 2)) as x eqn:Hx.
    destruct x. {
      specialize (Huv33 0) as H6.
      rewrite Nat.add_0_r in H6.
      destruct H6 as (H6, _).
      rewrite Hw in H6.
      rewrite Nat.add_0_r, Hr2.
      apply Q.lt_add_lt_sub_l.
      replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
      apply Q.mul_lt_mono_pos_r; [ easy | ].
      symmetry in Hx.
      clear - Hr2 Hx H1 H6 Hu Hv.
      unfold P, d2n, prop_carr, dig in Hx.
      rewrite (proj2 H1), Nat.add_0_l in Hx.
      unfold carry in Hx.
      unfold "⊕" in H6.
      rewrite A_split_first in Hx; [ | min_n_ge ].
      replace (S (i + 2)) with (i + 3) in Hx by easy.
      replace (v (i + 3)) with 2 in Hx. 2: {
        specialize (Hu 3) as H7.
        specialize (Hv 3) as H8.
        flia H6 H7 H8.
      }
      rewrite Hr2, Q.pair_diag in Hx; [ | easy ].
      rewrite Q.intg_add_cond in Hx; [ | easy | now apply Q.le_0_mul_r ].
      rewrite Q.intg_1 in Hx.
      rewrite Q.frac_1, Q.add_0_l in Hx.
      destruct
        (Q.lt_le_dec
           (Q.frac
              (A (i + 3) (min_n (i + 2 + carry_cases v (i + 2))) v *
               (1 // 2)%Q)) 1) as [H7| H7]. 2: {
        exfalso.
        apply Q.nlt_ge in H7; apply H7; clear H7.
        apply Q.frac_lt_1.
      }
      rewrite Nat.add_0_r in Hx.
      rewrite Q.intg_small in Hx; [ easy | ].
      split; [ now apply Q.le_0_mul_r | ].
      apply rad_2_sum_2_half_A_lt_1; [ easy | ].
      now intros; rewrite <- Nat.add_assoc.
    }
    destruct x. {
      exfalso.
      specialize (Huv33 0) as H6.
      destruct H6 as (H6, _).
      rewrite Nat.add_0_r in H6.
      symmetry in Hpv, Hx.
      clear - Hx H1 Hw Hu Hv Hr2 Hpv Huv10 H6.
      unfold P, d2n, prop_carr, dig in Hx.
      rewrite (proj2 H1), Nat.add_0_l in Hx.
      unfold carry in Hx.
      rewrite Hw in H6.
      unfold "⊕" in H6.
      rewrite A_split_first in Hx; [ | min_n_ge ].
      replace (S (i + 2)) with (i + 3) in Hx by easy.
      replace (v (i + 3)) with 2 in Hx. 2: {
        specialize (Hu 3) as H7.
        specialize (Hv 3) as H8.
        flia H6 H7 H8.
      }
      rewrite Hr2, Q.pair_diag in Hx; [ | easy ].
      rewrite Q.intg_add_cond in Hx; [ | easy | now apply Q.le_0_mul_r ].
      rewrite Q.intg_1 in Hx.
      rewrite Q.frac_1, Q.add_0_l in Hx.
      destruct
        (Q.lt_le_dec
           (Q.frac
              (A (i + 3) (min_n (i + 2 + carry_cases v (i + 2))) v *
               (1 // 2)%Q)) 1) as [H7| H7]. 2: {
        exfalso.
        apply Q.nlt_ge in H7; apply H7; clear H7.
        apply Q.frac_lt_1.
      }
      clear H7.
      rewrite Nat.add_0_r in Hx.
      clear Hx.
      unfold P, d2n, prop_carr, dig in Hpv.
      replace (v (i + 1)) with 0 in Hpv. 2: {
        rewrite Hw in Huv10.
        unfold "⊕" in Huv10.
        now apply Nat.eq_add_0 in Huv10.
      }
      rewrite Nat.add_0_l in Hpv.
      unfold carry in Hpv.
      rewrite A_split_first in Hpv; [ | min_n_ge ].
      replace (S (i + 1)) with (i + 2) in Hpv by easy.
      rewrite (proj2 H1), Q.add_0_l in Hpv.
      rewrite Q.intg_small in Hpv; [ now rewrite Nat.mod_0_l in Hpv | ].
      split; [ now apply Q.le_0_mul_r | ].
      rewrite Hr2.
      apply rad_2_sum_2_half_A_lt_1; [ easy | ].
      now intros; rewrite <- Nat.add_assoc.
    }
    specialize (P_le v (i + 2)) as H.
    rewrite <- Hx, Hr2 in H.
    flia H.
  }
  unfold "⊕" at 1; rewrite (proj1 H1).
  rewrite Nat.add_0_l.
  remember (P v (i + 2)) as x eqn:Hx.
  destruct x. {
    rewrite Q.add_0_l.
    clear - Hr2 Hu.
    rewrite Hr2.
    apply rad_2_sum_2_half_A_lt_1; [ easy | ].
    intros p; rewrite <- Nat.add_assoc; unfold "⊕".
    replace 2 with (1 + 1) at 3 by easy.
    apply Nat.add_le_mono; [ apply Hu | ].
    replace 1 with (rad - 1) by flia Hr2.
    apply P_le.
  }
  destruct x. {
    apply Q.lt_add_lt_sub_l; rewrite Hr2.
    replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
    apply Q.mul_lt_mono_pos_r; [ easy | ].
    clear - Hr2 Hx H1 Huv33 Hw Hu Hv.
    unfold P, d2n, prop_carr, dig in Hx.
    rewrite (proj2 H1) in Hx.
    unfold carry in Hx.
    specialize (Huv33 0) as H6.
    destruct H6 as (H6, _).
    rewrite Nat.add_0_r in H6.
    rewrite Hw in H6.
    unfold "⊕" in H6.
    rewrite A_split_first in Hx; [ | min_n_ge ].
    replace (S (i + 2)) with (i + 3) in Hx by easy.
    replace (v (i + 3)) with 2 in Hx. 2: {
      specialize (Hu 3) as H7.
      specialize (Hv 3) as H8.
      flia H6 H7 H8.
    }
    rewrite Hr2, Q.pair_diag in Hx; [ | easy ].
    rewrite (Q.intg_add_nat_l 1) in Hx; [ | now apply Q.le_0_mul_r ].
    rewrite Nat.add_assoc in Hx.
    rewrite Nat_mod_add_same_l in Hx; [ | easy ].
    rewrite Q.intg_small in Hx; [ easy | ].
    split; [ now apply Q.le_0_mul_r | ].
    apply rad_2_sum_2_half_A_lt_1; [ easy | ].
    now intros; rewrite <- Nat.add_assoc.
  }
  specialize (P_le v (i + 2)) as H.
  rewrite <- Hx, Hr2 in H.
  flia H.
}
specialize (P_le v (i + 1)) as H.
rewrite <- Hpv, Hr2 in H.
flia H.
Qed.

Theorem rad_2_sum_3_213c1_A_lt_1 {r : radix} : ∀ u v i n,
  rad = 2
  → (∀ k, u (i + k) ≤ 1)
  → (∀ k, v (i + k) ≤ 2)
  → (u ⊕ v) (i + 2) = 2
  → (u ⊕ v) (i + 3) = 1
  → (u ⊕ v) (i + 4) = 3
  → carry v (i + 1) ≠ 0
  → (A (i + 1) n (u ⊕ P v) < 1)%Q.
Proof.
intros * Hr2 Hu Hv Huv2 Huv3 Huv4 Hc1z.
remember (carry v (i + 1)) as c1 eqn:Hc1.
symmetry in Hc1.
destruct c1; [ easy | clear Hc1z ].
destruct c1. 2: {
  destruct c1. 2: {
    specialize (carry_upper_bound_for_adds 2 v i) as H1.
    assert (H : 2 ≠ 0) by easy.
    specialize (H1 H); clear H.
    assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
      now intros; rewrite <- Nat.add_assoc, Hr2.
    }
    specialize (H1 H 1); clear H.
    rewrite Hc1 in H1; flia H1.
  }
  unfold carry in Hc1.
  apply Q.intg_interv in Hc1; [ | easy ].
  destruct Hc1 as (Hc1, _).
  apply Q.nlt_ge in Hc1.
  exfalso; apply Hc1; clear Hc1.
  eapply Q.le_lt_trans. {
    apply (A_upper_bound_for_adds 2).
    now intros; do 2 rewrite <- Nat.add_assoc; rewrite Hr2.
  }
  rewrite Q.mul_sub_distr_l, Q.mul_1_r.
  now apply Q.sub_lt.
}
apply Nat_eq_add_2 in Huv2.
destruct Huv2 as [Huv2| Huv2]; [ specialize (Hu 2); flia Hu Huv2 | ].
destruct Huv2 as [(Hu2, Hv2)| (Hu2, Hv2)]. {
  unfold "⊕" in Huv3.
  apply Nat.eq_add_1 in Huv3.
  destruct Huv3 as [(Hu3, Hv3)| (Hu3, Hv3)]. {
    unfold carry in Hc1.
    apply Q.intg_interv in Hc1; [ | easy ].
    destruct Hc1 as (Hc1, _).
    exfalso; apply Q.nlt_ge in Hc1; apply Hc1; clear Hc1.
    rewrite A_split_first; [ | min_n_ge ].
    replace (S (i + 1)) with (i + 2) by easy.
    replace (v (i + 2)) with 1 by flia Huv2.
    apply Q.lt_add_lt_sub_l; rewrite Hr2.
    replace (1 // 1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
    apply Q.mul_lt_mono_pos_r; [ easy | ].
    rewrite A_split_first; [ | min_n_ge ].
    replace (S (i + 2)) with (i + 3) by easy.
    rewrite Hv3, Q.add_0_l, Hr2.
    apply rad_2_sum_2_half_A_lt_1; [ easy | ].
    now intros; rewrite <- Nat.add_assoc.
  }
  destruct (lt_dec (n - 1) (i + 1 + 1)) as [Hin| Hin]. {
    now unfold A; rewrite summation_empty.
  }
  apply Nat.nlt_ge in Hin.
  rewrite A_split_first; [ | easy ].
  replace (S (i + 1)) with (i + 2) by flia.
  unfold "⊕" at 1; rewrite Hu2.
  replace (P v (i + 2)) with 0. 2: {
    symmetry; unfold P, d2n, prop_carr, dig.
    rewrite Hv2, Hr2.
    replace (carry v (i + 2)) with 1; [ easy | ].
    symmetry; unfold carry.
    remember (carry_cases v (i + 2)) as c eqn:Hc.
    rewrite A_split_first; [ | min_n_ge ].
    replace (S (i + 2)) with (i + 3) by easy.
    rewrite Hv3, Hr2.
    rewrite A_split_first; [ | min_n_ge ].
    replace (S (i + 3)) with (i + 4) by easy.
    unfold "⊕" in Huv4.
    assert (H : u (i + 4) = 1 ∧ v (i + 4) = 2). {
      specialize (Hu 4); specialize (Hv 4); flia Hu Hv Huv4.
    }
    destruct H as (Hu4, Hv4).
    move Hu4 before Hv3; move Hv4 before Hu4.
    rewrite Hv4, Hr2, Q.pair_diag; [ | easy ].
    rewrite Q.mul_add_distr_r, Q.mul_1_l, Q.add_assoc.
    rewrite Q.add_pair; [ | easy | easy ].
    rewrite Q.pair_diag; [ | easy ].
    assert (HA : (0 ≤ A (i + 4) (min_n (i + 2 + c)) v * 1 // 2 * 1 // 2)%Q). {
      apply Q.le_0_mul_r; [ easy | ].
      now apply Q.le_0_mul_r.
    }
    rewrite (Q.intg_add_nat_l 1); [ | easy ].
    replace 1 with (1 + 0) at 8 by easy; f_equal.
    apply Q.intg_small.
    split; [ easy | ].
    apply (Q.mul_lt_mono_pos_r 2%Q); [ easy | ].
    rewrite <- Q.mul_assoc.
    rewrite (Q.mul_pair_den_num _ 2 1); [ | easy ].
    rewrite Q.pair_diag; [ | easy ].
    rewrite Q.mul_1_r, Q.mul_1_l.
    apply (Q.lt_le_trans _ 1). 2: {
      apply (Q.le_pair_mono_r 1 2 1); pauto.
    }
    apply rad_2_sum_2_half_A_lt_1; [ easy | ].
    now intros; rewrite <- Nat.add_assoc.
  }
  rewrite Nat.add_0_r.
  apply Q.lt_add_lt_sub_l; rewrite Hr2.
  replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
  apply Q.mul_lt_mono_pos_r; [ easy | ].
  destruct (lt_dec (n - 1) (i + 2 + 1)) as [Hin2| Hin2]. {
    now unfold A; rewrite summation_empty.
  }
  apply Nat.nlt_ge in Hin2.
  rewrite A_split_first; [ | easy ].
  replace (S (i + 2)) with (i + 3) by easy.
  unfold "⊕" at 1.
  rewrite Hu3, Nat.add_0_l.
  replace (P v (i + 3)) with 0. 2: {
    symmetry; unfold P, d2n, prop_carr, dig.
    rewrite Hv3, Hr2.
    replace (carry v (i + 3)) with 1; [ easy | ].
    symmetry; unfold carry.
    remember (carry_cases v (i + 3)) as c eqn:Hc.
    rewrite A_split_first; [ | min_n_ge ].
    replace (S (i + 3)) with (i + 4) by easy.
    unfold "⊕" in Huv4.
    assert (H : u (i + 4) = 1 ∧ v (i + 4) = 2). {
      specialize (Hu 4); specialize (Hv 4); flia Hu Hv Huv4.
    }
    destruct H as (Hu4, Hv4).
    move Hu4 before Hv3; move Hv4 before Hu4.
    rewrite Hv4, Hr2, Q.pair_diag; [ | easy ].
    rewrite (Q.intg_add_nat_l 1); [ | now apply Q.le_0_mul_r ].
    replace 1 with (1 + 0) at 6 by easy; f_equal.
    apply Q.intg_small.
    split; [ now apply Q.le_0_mul_r | ].
    apply rad_2_sum_2_half_A_lt_1; [ easy | ].
    now intros; rewrite <- Nat.add_assoc.
  }
  rewrite Q.add_0_l, Hr2.
  apply rad_2_sum_2_half_A_lt_1; [ easy | ].
  intros p; rewrite <- Nat.add_assoc; unfold "⊕".
  replace 2 with (1 + 1) at 3 by easy.
  apply Nat.add_le_mono; [ easy | ].
  replace 1 with (rad - 1) by flia Hr2; apply P_le.
}
destruct (lt_dec (n - 1) (i + 1 + 1)) as [Hin| Hin]. {
  now unfold A; rewrite summation_empty.
}
apply Nat.nlt_ge in Hin.
rewrite A_split_first; [ | easy ].
replace (S (i + 1)) with (i + 2) by flia.
unfold "⊕" at 1; rewrite Hu2, Nat.add_0_l.
apply Nat.eq_add_1 in Huv3.
destruct Huv3 as [(Hu3, Hv3)| (Hu3, Hv3)]. {
  replace (P v (i + 2)) with 0. 2: {
    symmetry; unfold P, d2n, prop_carr, dig.
    rewrite Hv2, Hr2, Nat_mod_add_same_l; [ | easy ].
    replace (carry v (i + 2)) with 0; [ easy | ].
    symmetry; unfold carry.
    apply Q.intg_small; split; [ easy | ].
    rewrite A_split_first; [ | min_n_ge ].
    replace (S (i + 2)) with (i + 3) by easy.
    rewrite Hv3, Q.add_0_l, Hr2.
    apply rad_2_sum_2_half_A_lt_1; [ easy | ].
    now intros p; rewrite <- Nat.add_assoc.
  }
  rewrite Q.add_0_l, Hr2.
  apply rad_2_sum_2_half_A_lt_1; [ easy | ].
  intros; rewrite <- Nat.add_assoc; unfold "⊕".
  replace 2 with (1 + 1) at 3 by easy.
  apply Nat.add_le_mono; [ easy | ].
  replace 1 with (rad - 1) by flia Hr2; apply P_le.
}
apply Q.lt_add_lt_sub_l.
apply (Q.lt_le_trans _ (1 * 1 // 2)%Q). 2: {
  rewrite Q.mul_1_l, Hr2.
  remember (P v (i + 2)) as p2 eqn:Hp2.
  destruct p2; [ rewrite Q.sub_0_r; apply (Q.le_pair_mono_l 1); flia | ].
  destruct p2; [ easy | ].
  specialize (P_le v (i + 2)) as H3.
  flia Hr2 Hp2 H3.
}
rewrite Hr2.
apply Q.mul_lt_mono_pos_r; [ easy | ].
destruct (lt_dec (n - 1) (i + 2 + 1)) as [Hin2| Hin2]. {
  now unfold A; rewrite summation_empty.
}
apply Nat.nlt_ge in Hin2.
rewrite A_split_first; [ | easy ].
replace (S (i + 2)) with (i + 3) by easy.
unfold "⊕" at 1.
rewrite Hu3, Nat.add_0_l.
apply Q.lt_add_lt_sub_l.
replace (P v (i + 3)) with 0. 2: {
  symmetry; unfold P, d2n, prop_carr, dig.
  rewrite Hv3; unfold carry.
  rewrite A_split_first; [ | min_n_ge ].
  replace (S (i + 3)) with (i + 4) by easy.
  replace (v (i + 4)) with 2. 2: {
    symmetry; unfold "⊕" in Huv4.
    specialize (Hu 4); specialize (Hv 4); flia Hu Hv Huv4.
  }
  rewrite Hr2, Q.pair_diag; [ | easy ].
  rewrite (Q.intg_add_nat_l 1); [ | now apply Q.le_0_mul_r ].
  rewrite Nat.add_assoc, Nat_mod_add_same_l; [ | easy ].
  rewrite Q.intg_small; [ easy | ].
  split; [ now apply Q.le_0_mul_r | ].
  apply rad_2_sum_2_half_A_lt_1; [ easy | ].
  now intros; rewrite <- Nat.add_assoc.
}
rewrite Q.sub_0_r, Hr2.
apply rad_2_sum_2_half_A_lt_1; [ easy | ].
intros p; rewrite <- Nat.add_assoc; unfold "⊕".
replace 2 with (1 + 1) at 3 by easy.
apply Nat.add_le_mono; [ easy | ].
replace 1 with (rad - 1) by flia Hr2; apply P_le.
Qed.

Theorem rad_2_sum_3_0213_A_lt_1 {r : radix} : ∀ u v i n,
  rad = 2
  → (∀ k, u (i + k) ≤ 1)
  → (∀ k, v (i + k) ≤ 2)
  → (u ⊕ v) (i + 1) = 0
  → (u ⊕ v) (i + 2) = 2
  → (u ⊕ v) (i + 3) = 1
  → (u ⊕ v) (i + 4) = 3
  → (A i n (u ⊕ P v) < 1)%Q.
Proof.
intros * Hr2 Hu Hv Huv1 Huv2 Huv3 Huv4.
unfold "⊕" in Huv1; apply Nat.eq_add_0 in Huv1.
destruct Huv1 as (Hu1, Hv1).
destruct (lt_dec (n - 1) (i + 1)) as [Hin| Hin]. {
  now unfold A; rewrite summation_empty.
}
apply Nat.nlt_ge in Hin.
rewrite A_split_first; [ | easy ].
replace (S i) with (i + 1) by flia.
unfold "⊕" at 1; rewrite Hu1, Nat.add_0_l, Hr2.
clear Hu1.
apply Q.lt_add_lt_sub_l.
destruct (zerop (P v (i + 1))) as [Hp1| Hzp1]. {
  rewrite Hp1, Q.sub_0_r.
  apply rad_2_sum_2_half_A_lt_1; [ easy | ].
  intros p; rewrite <- Nat.add_assoc; unfold "⊕".
  replace 2 with (1 + 1) by easy.
  apply Nat.add_le_mono; [ easy | ].
  replace 1 with (rad - 1) by flia Hr2.
  apply P_le.
}
assert (Hp1 : P v (i + 1) = 1). {
  specialize (P_le v (i + 1)) as H.
  rewrite Hr2 in H; flia Hzp1 H.
}
clear Hzp1.
rename Hp1 into Hc1.
rewrite Hc1.
replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
apply Q.mul_lt_mono_pos_r; [ easy | ].
unfold P, d2n, prop_carr, dig in Hc1.
rewrite Hv1, Nat.add_0_l in Hc1.
clear Hv1.
rewrite Nat.mod_small in Hc1. 2: {
  specialize (carry_upper_bound_for_adds 2 v i) as H3.
  assert (H : 2 ≠ 0) by easy.
  specialize (H3 H); clear H.
  assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
    intros; rewrite <- Nat.add_assoc, Hr2; apply Hv.
  }
  specialize (H3 H); clear H.
  now rewrite Hr2.
}
apply rad_2_sum_3_213c1_A_lt_1; try easy.
now intros H; rewrite H in Hc1.
Qed.

Theorem rad_2_sum_3_22_1_lt_2 {r : radix} : ∀ u v i j n p,
  rad = 2
  → (∀ k, u (i + k) ≤ 1)
  → (∀ k, v (i + k) ≤ 2)
  → (∀ k, k < j + n → (u ⊕ v) (i + k + 2) = 2)
  → (u ⊕ v) (i + j + n + 2) = 1
  → (A (i + n + 1) p (u ⊕ v) < 2)%Q.
Proof.
intros * Hr2 Hu Hv Huvbef Huvj.
revert n Huvbef Huvj.
induction j; intros. {
  rewrite Nat.add_0_r in Huvj.
  destruct (lt_dec (p - 1) (i + n + 2)) as [H2| H2]. {
    unfold A; rewrite summation_empty; [ easy | flia H2 ].
  }
  apply Nat.nlt_ge in H2.
  rewrite A_split_first; [ | flia H2 ].
  replace (S (i + n + 1)) with (i + n + 2) by easy.
  rewrite Huvj, Hr2.
  apply Q.lt_add_lt_sub_l.
  replace (2 - 1 // 2)%Q with (3 * 1 // 2)%Q by easy.
  apply Q.mul_lt_mono_pos_r; [ easy | ].
  eapply Q.le_lt_trans. {
    apply (A_upper_bound_for_adds 3).
    intros j; cbn; rewrite Hr2.
    do 3 rewrite <- Nat.add_assoc.
    now apply Nat.add_le_mono.
  }
  rewrite Q.mul_sub_distr_l, Q.mul_1_r.
  now apply Q.sub_lt.
}
replace (S j + n) with (j + S n) in Huvbef by flia.
replace (i + S j + n) with (i + j + S n) in Huvj by flia.
specialize (IHj (S n) Huvbef Huvj) as H2.
destruct (lt_dec (p - 1) (i + n + 2)) as [H3| H3]. {
  unfold A; rewrite summation_empty; [ easy | flia H3 ].
}
apply Nat.nlt_ge in H3.
rewrite A_split_first; [ | flia H3 ].
replace (i + S n + 1) with (i + n + 2) in H2 by flia.
replace (S (i + n + 1)) with (i + n + 2) by flia.
specialize (Huvbef n) as H4.
assert (H : n < j + S n) by flia.
specialize (H4 H); clear H.
rewrite H4, Hr2, Q.pair_diag; [ | easy ].
apply Q.lt_add_lt_sub_l.
replace (2 - 1)%Q with 1%Q by easy.
rewrite <- (Q.mul_inv_pair 2 1); [ | easy | easy ].
now apply Q.mul_lt_mono_pos_r.
Qed.

Theorem P_999_after_9 {r : radix} : ∀ u i m,
  m ≤ rad
  → (∀ k, u (i + k) ≤ m * (rad - 1))
  → (∀ k, P u (i + k) = rad - 1)
  → ∀ j, u (i + j) = rad - 1
  → rad - m ≤ u (i + j + 1) < rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hmr Hur Hpu * Hum.
enough
  (H : let k := rad - u (i + j + 1) in
       1 ≤ k ≤ m ∧ u (i + j + 1) = rad - k) by flia H.
specialize (P_999_start u (i + j) m) as H1.
assert (H : ∀ k, u (i + j + k) ≤ m * (rad - 1)). {
  intros k; rewrite <- Nat.add_assoc; apply Hur.
}
specialize (H1 H); clear H.
assert (H : ∀ k, P u (i + j + k) = rad - 1). {
  intros k; rewrite <- Nat.add_assoc; apply Hpu.
}
specialize (H1 H); clear H.
destruct (Nat.eq_dec (u (i + j)) (m * (rad - 1))) as [H2| H2].
-clear H1.
 assert (Hm : m = 1). {
   rewrite H2 in Hum.
   destruct m; [ cbn in Hum; flia Hum Hr | ].
   destruct m; [ easy | ].
   cbn in Hum; flia Hum Hr.
 }
 subst m; clear H2; rewrite Nat.mul_1_l in Hur.
 specialize (Hpu (j + 1)) as H1.
 rewrite Nat.add_assoc in H1.
 unfold P, d2n, prop_carr in H1; cbn in H1.
 specialize (carry_upper_bound_for_adds 1 u i) as H2.
 assert (H : 1 ≠ 0) by easy.
 specialize (H2 H); clear H.
 assert (H : ∀ k, u (i + k + 1) ≤ 1 * (rad - 1)). {
   intros; rewrite <- Nat.add_assoc, Nat.mul_1_l; apply Hur.
 }
 specialize (H2 H (j + 1)); clear H.
 rewrite Nat.add_assoc in H2.
 apply Nat.lt_1_r in H2.
 rewrite H2, Nat.add_0_r in H1.
 rewrite Nat.mod_small in H1. 2: {
   specialize (Hur (j + 1)) as H3.
   rewrite Nat.add_assoc in H3.
   flia H3 Hr.
 }
 rewrite H1; flia Hr.
-rewrite Hum in H1.
 rewrite Nat.div_small in H1; [ | flia Hr ].
 rewrite Nat.add_0_l in H1.
 destruct (lt_dec rad m) as [H3| H3]; [ now apply Nat.nle_gt in H3 | ].
 clear H3.
 destruct H1 as ((_, Hm) & (_, Hc) & H1).
 rewrite Nat.mul_1_l in H1.
 destruct (Nat.eq_dec m 1) as [H4| H4]; [ flia Hm H4 | clear H4 ].
 assert (Hcu : carry u (i + j) = 0) by flia Hr H1.
 clear Hc H1.
 assert (Hur1 : u (i + j + 1) < rad). {
   apply Nat.nle_gt; intros Hur1.
   unfold carry in Hcu.
   apply Q.eq_intg_0 in Hcu; [ | easy ].
   apply Q.nle_gt in Hcu; apply Hcu; clear Hcu.
   rewrite A_split_first; [ | min_n_ge ].
   rewrite <- (Nat.add_1_r (i + j)).
   eapply Q.le_trans; [ | now apply Q.le_add_r, Q.le_0_mul_r ].
   apply (Q.le_pair 1 1); [ easy | easy | ].
   now do 2 rewrite Nat.mul_1_l.
 }
 split; [ | flia Hur1 ].
 split; [ flia Hur1 | ].
 specialize (P_999_start u (i + j + 1) m) as H1.
 assert (H : ∀ k, u (i + j + 1 + k) ≤ m * (rad - 1)). {
   intros k; do 2 rewrite <- Nat.add_assoc; apply Hur.
 }
 specialize (H1 H); clear H.
 assert (H : ∀ k, P u (i + j + 1 + k) = rad - 1). {
   intros k; do 2 rewrite <- Nat.add_assoc; apply Hpu.
 }
 specialize (H1 H); clear H.
 destruct (lt_dec rad m) as [H3| H3]; [ now apply Nat.nle_gt in H3 | ].
 clear H3.
 destruct (Nat.eq_dec (u (i + j + 1)) (m * (rad - 1))) as [H4| H4].
 +clear H1.
  rewrite H4, Nat.mul_sub_distr_l, Nat.mul_1_r.
  destruct m; [ easy | cbn; flia ].
 +rewrite Nat.div_small in H1; [ | easy ].
  rewrite Nat.add_0_l in H1.
  destruct H1 as (H1 & H3 & H5); rewrite H5, Nat.mul_1_l.
  rewrite Nat_sub_sub_distr; [ now rewrite Nat.sub_diag | ].
  split; [ flia H3 Hmr | easy ].
Qed.

(* generalizes A_all_9 and A_all_18 *)
Theorem A_all_nth_pred_rad {r : radix} : ∀ u i m n,
  (∀ k : nat, i + k + 1 < n → u (i + k + 1) = m * (rad - 1))
  → A i n u = (m // 1 - m // rad ^ (n - i - 1))%Q.
Proof.
intros * Hmr.
specialize radix_ge_2 as Hr.
unfold A.
destruct (le_dec (i + 1) (n - 1)) as [Hin| Hin]; cycle 1. {
  replace (n - i - 1) with 0 by flia Hin.
  rewrite Nat.pow_0_r, Q.sub_diag.
  now rewrite summation_empty; [ | flia Hin ].
}
rewrite summation_shift; [ | easy ].
rewrite summation_eq_compat with
    (h := λ j, ((m * (rad - 1)) // rad ^ (j + 1))%Q). 2: {
  intros j Hj.
  replace (i + 1 + j - i) with (j + 1) by flia.
  rewrite Nat.add_shuffle0, Hmr; [ easy | flia Hin Hj ].
}
rewrite summation_eq_compat with
    (h := λ j, ((m * (rad - 1)) // rad * 1 // rad ^ j)%Q). 2: {
  intros j Hj.
  rewrite Q.mul_pair; [ | easy | pauto ].
  rewrite Nat.mul_1_r; f_equal.
  now rewrite Nat.add_comm.
}
rewrite <- summation_mul_distr_l.
remember Q.of_pair as f; simpl; subst f.
rewrite Q.power_summation; [ | flia Hr ].
replace (n - 1 - (i + 1)) with (n - i - 1 - 1) by flia Hin.
remember (n - i - 1) as s eqn:Hs.
replace (S (s - 1)) with s by flia Hs Hin.
rewrite Q.sub_pair_pos; [ | easy | pauto | ]; cycle 1. {
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_l.
  now apply Nat_pow_ge_1.
}
do 2 rewrite Nat.mul_1_l.
rewrite Q.mul_pair; [ | easy | ]. 2: {
  apply Nat.neq_mul_0.
  split; [ pauto | flia Hr ].
}
rewrite Nat.mul_shuffle0, Nat.mul_assoc.
rewrite <- Q.mul_pair; [ | | flia Hr ]; cycle 1. {
  apply Nat.neq_mul_0.
  split; [ easy | pauto ].
}
rewrite Q.pair_diag; [ | flia Hr ].
rewrite Q.mul_1_r.
replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
rewrite <- Nat.pow_add_r.
replace (1 + (s - 1)) with s by flia Hs Hin.
now rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
Qed.

Theorem NQintg_A_for_dig {r : radix} : ∀ i n u,
  (∀ k, i + 1 ≤ k ≤ n - 1 → u k ≤ rad - 1)
  → Q.intg (A i n u) = 0.
Proof.
intros * Hur.
apply Q.intg_small.
split; [ easy | ].
now apply A_upper_bound_for_dig.
Qed.

Theorem fold_carry {r : radix} : ∀ u i,
  Q.intg (A i (min_n (i + carry_cases u i)) u) = carry u i.
Proof. easy. Qed.

Fixpoint carry_nth {r : radix} n u i :=
  match n with
  | 0 => carry u i
  | S n' => (u (i + 1) + carry_nth n' u (i + 1)) / rad
  end.

Theorem carry_nth_carry {r : radix} : ∀ m n u i,
  m < rad ^ (rad * (i + 3) - (i + 2))
  → (∀ k, u (i + k) ≤ m * (rad - 1))
  → carry_nth n u i = carry u i.
Proof.
intros * Hmr Hur.
specialize radix_ne_0 as Hr.
revert i Hmr Hur.
induction n; intros; [ easy | cbn ].
rewrite (carry_succ m); [ | easy | easy ].
rewrite IHn; [ easy | | now intros; rewrite <- Nat.add_assoc ].
eapply lt_le_trans; [ apply Hmr | ].
apply Nat.pow_le_mono_r; [ easy | ].
setoid_rewrite Nat.add_shuffle0.
rewrite (Nat.sub_add_distr _ (i + 2)).
rewrite Nat_sub_sub_swap.
apply Nat.sub_le_mono_r.
rewrite (Nat.mul_add_distr_l _ (i + 3)), Nat.mul_1_r.
flia Hr.
Qed.

Theorem rad_2_all_12_2_carry_1 {r : radix} : ∀ j u i,
  rad = 2
  → (∀ p, u (i + p) ≤ 2)
  → (∀ p, p < j → u (i + p + 2) = 1 ∨ u (i + p + 2) = 2)
  → u (i + j + 2) = 2
  → ∀ k, k ≤ j → carry u (i + k + 1) = 1.
Proof.
intros * Hr2 Hu Huj1 Huj2 k Hkj.
revert i k Hu Huj1 Huj2 Hkj.
induction j; intros. {
  apply Nat.le_0_r in Hkj; subst k.
  rewrite Nat.add_0_r in Huj2 |-*.
  rewrite (carry_succ 2); cycle 1. {
    rewrite Hr2.
    replace 2 with (2 ^ 1) at 1 by easy.
    apply Nat.pow_lt_mono_r; [ pauto | flia ].
  } {
    intros; rewrite Hr2.
    now rewrite <- Nat.add_assoc.
  }
  replace (i + 1 + 1) with (i + 2) by flia.
  rewrite Hr2, Huj2, Nat_div_add_same_l; [ | easy ].
  specialize (carry_upper_bound_for_adds 2 u i (Nat.neq_succ_0 _)) as H1.
  assert (H : ∀ k, u (i + k + 1) ≤ 2 * (rad - 1)). {
    now intros; rewrite Hr2, <- Nat.add_assoc.
  }
  specialize (H1 H 2).
  remember (carry u (i + 2)) as c eqn:Hc.
  destruct c; [ easy | ].
  destruct c; [ easy | flia H1 ].
}
destruct (Nat.eq_dec k (S j)) as [Hksj| Hksj]. {
  rewrite Hksj.
  replace (i + S j + 1) with (S i + j + 1) by flia.
  rewrite <- (Nat.add_succ_comm i) in Huj2.
  apply IHj; [ | | easy | easy ]. {
    now intros; rewrite Nat.add_succ_comm.
  }
  intros p Hp.
  rewrite Nat.add_succ_comm.
  apply Huj1; flia Hp.
}
rewrite (carry_succ 2); cycle 1. {
  rewrite Hr2.
  replace 2 with (2 ^ 1) at 1 by easy.
  apply Nat.pow_lt_mono_r; [ pauto | flia ].
} {
  intros; rewrite Hr2.
  now do 2 rewrite <- Nat.add_assoc.
}
rewrite (Nat.add_shuffle0 i).
rewrite IHj; [ | | | | flia Hkj Hksj ]; cycle 1. {
  now intros; rewrite <- Nat.add_assoc.
} {
  intros p Hp.
  rewrite <- (Nat.add_assoc i).
  apply Huj1; flia Hp.
} {
  now rewrite <- (Nat.add_assoc i).
}
specialize (Huj1 k) as H1.
assert (H : k < S j) by flia Hkj Hksj.
specialize (H1 H); clear H.
replace (i + 1 + k + 1) with (i + k + 2) by flia.
remember (u (i + k + 2)) as c eqn:Hc.
rewrite Hr2.
now destruct H1 as [H1| H1]; rewrite H1.
Qed.

Theorem rad_2_sum_3_0_222_1_A_lt_1 {r : radix} : ∀ q u v i n,
  rad = 2
  → (∀ k, u (i + k) ≤ 1)
  → (∀ k, v (i + k) ≤ 2)
  → (∀ k, fA_ge_1_ε (u ⊕ v) i k = true)
  → (u ⊕ v) (i + 1) = 0
  → (∀ p, p < q → (u ⊕ v) (i + p + 2) = 2)
  → (u ⊕ v) (i + q + 2) = 1
  → (A i n (u ⊕ P v) < 1)%Q.
Proof.
intros * Hr2 Hu Hv Hauv Huv1 Hjq Huv2.
assert (Huvl3 : ∀ k, (u ⊕ v) (i + k) ≤ 3). {
  intros p.
  unfold "⊕"; replace 3 with (1 + 2) by easy.
  apply Nat.add_le_mono; [ apply Hu | apply Hv ].
}
specialize (rad_2_sum_3_all_9_02_222_1_333 _ i q Hr2 Huvl3 Hauv) as Huvqc3.
specialize (Huvqc3 (or_introl Huv1) Hjq Huv2).
assert (Huvq3 : ∀ k, u (i + q + k + 3) = 1 ∧ v (i + q + k + 3) = 2). {
  intros p.
  specialize (Huvqc3 p) as (H1, _).
  unfold "⊕" in H1.
  specialize (Hu (q + p + 3)) as H2.
  specialize (Hv (q + p + 3)) as H3.
  do 2 rewrite Nat.add_assoc in H2, H3.
  flia H1 H2 H3.
}
destruct (lt_dec (n - 1) (i + 1)) as [Hin| Hin]. {
  now unfold A; rewrite summation_empty.
}
apply Nat.nlt_ge in Hin.
rewrite A_split_first; [ | easy ].
replace (S i) with (i + 1) by flia.
unfold "⊕" at 1, P at 1, d2n, prop_carr, dig.
apply Nat.eq_add_0 in Huv1.
rewrite (proj1 Huv1), (proj2 Huv1), Hr2.
do 2 rewrite Nat.add_0_l.
remember (carry v (i + 1)) as c eqn:Hc.
destruct c. {
  rewrite Q.add_0_l.
  apply rad_2_sum_2_half_A_lt_1; [ easy | ].
  intros p; unfold "⊕"; rewrite <- Nat.add_assoc.
  replace 2 with (1 + 1) by easy.
  apply Nat.add_le_mono; [ apply Hu | ].
  replace 1 with (rad - 1) by flia Hr2.
  apply P_le.
}
specialize (carry_upper_bound_for_adds 2 v i) as Hcv.
specialize (Hcv (Nat.neq_succ_0 _)).
assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
  now intros; rewrite Hr2, <- Nat.add_assoc.
}
specialize (Hcv H); clear H.
specialize (Hcv 1) as H1.
rewrite <- Hc in H1.
destruct c; [ | flia H1 ].
clear H1; symmetry in Hc.
rewrite Nat.mod_small; [ | pauto ].
apply Q.lt_add_lt_sub_l.
replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
apply Q.mul_lt_mono_pos_r; [ easy | ].
(*
     u 0 . . . . . 1 1 1 1 ...
     v 0 . . . . . 2 2 2 2 ...
   u+v 0 2 2 2 2 1 3 3 3 3 ...
    Pv . . . . . . 1 1 1 1 ...
  u+Pv . . . . . . 2 2 2 2 ...
 *)
assert (Hvq1 : ∀ j, j < q → v (i + j + 2) = 1 ∨ v (i + j + 2) = 2). {
  intros s Hs.
  specialize (Hjq _ Hs) as H3.
  apply Nat_eq_add_2 in H3.
  destruct H3 as [H3| H3]. {
    specialize (Hu (s + 2)); rewrite Nat.add_assoc in Hu; flia Hu H3.
  }
  destruct H3 as [H3| H3]; [ now left | now right ].
}
set (T := λ t, negb (Nat.eqb (v (i + q + 1 - t)) 1)).
remember (first_such_that T q 0) as t eqn:Ht.
specialize (first_such_that_has_prop T q 0 t) as H1.
assert (H : T (q + 0) = true). {
  unfold T.
  replace (i + q + 1 - (q + 0)) with (i + 1) by flia.
  apply Bool.negb_true_iff, Nat.eqb_neq.
  now intros H; rewrite H in Huv1.
}
specialize (H1 H Ht); clear H.
unfold T in H1; clear T Ht.
destruct H1 as (Hvt, Hvjt).
apply Bool.negb_true_iff, Nat.eqb_neq in Hvt.
assert (H : ∀ j, j < t → v (i + q + 1 - j) = 1). {
  intros s Hs.
  specialize (Hvjt _ (Nat.le_0_l s) Hs) as H1.
  now apply Bool.negb_false_iff, Nat.eqb_eq in H1.
}
clear Hvjt; rename H into Hvjt; move Hvt after Hvjt.
destruct (Nat.eq_dec t q) as [Htq| Htq]. {
  rewrite Htq in Hvt, Hvjt.
  clear t Htq Hvt.
  apply Nat.eq_add_1 in Huv2.
  destruct Huv2 as [Huv2| Huv2]. {
    replace (carry v (i + 1)) with 0 in Hc; [ easy | symmetry ].
    clear Hc; unfold carry.
    rewrite (A_9_8_all_18 q); cycle 1. {
      intros t Ht1.
      specialize (Hvjt (q - t - 1)) as H1.
      assert (H : q - t - 1 < q) by flia Ht1.
      specialize (H1 H); clear H.
      replace (i + q + 1 - (q - t - 1)) with (i + 1 + t + 1) in H1
        by flia Ht1.
      now rewrite Hr2.
    } {
      replace (i + 1 + q + 1) with (i + q + 2) by flia.
      now rewrite Hr2.
    } {
      intros t.
      replace (i + 1 + q + t + 2) with (i + q + t + 3) by flia.
      specialize (Huvq3 t) as H1.
      now rewrite Hr2.
    }
    apply Q.intg_small.
    remember (min_n (i + 1 + carry_cases v (i + 1))) as x eqn:Hx.
    remember (i + 1 + q + 1) as y eqn:Hy.
    split. {
      apply Q.le_0_sub.
      apply (Q.le_pair _ _ 1 1); [ pauto | easy | ].
      apply Nat.mul_le_mono_r.
      destruct (le_dec y (x - 1)) as [H2| H2]. {
        rewrite Hr2.
        replace 2 with (2 ^ 1) at 1 by easy.
        apply Nat.pow_le_mono_r; [ easy | rewrite Hx; min_n_ge ].
      }
      apply Nat.neq_0_lt_0; pauto.
    }
    apply Q.sub_lt, Q.lt_0_pair.
    destruct (le_dec y (x - 1)); pauto.
  }
  rewrite (A_9_8_all_18 q); cycle 1. {
    intros t Ht1.
    specialize (Hvjt (q - t - 1)) as H1.
    assert (H : q - t - 1 < q) by flia Ht1.
    specialize (H1 H); clear H.
    replace (i + q + 1 - (q - t - 1)) with (i + t + 2) in H1
      by flia Ht1.
    replace (i + 1 + t + 1) with (i + t + 2) by flia.
    specialize (Hjq _ Ht1) as H2.
    unfold "⊕" in H2.
    unfold "⊕", P, d2n, prop_carr, dig.
    replace (u (i + t + 2)) with 1 by flia H1 H2.
    rewrite H1, Hr2.
    replace (carry v (i + t + 2)) with 1; [ easy | symmetry ].
    replace (i + t + 2) with (i + (t + 1) + 1) by flia.
    apply (rad_2_all_12_2_carry_1 (q + 1)); try easy. {
      intros p Hp.
      destruct (lt_dec p q) as [Hpq| Hpq]; [ now apply Hvq1 | ].
      replace p with q by flia Hp Hpq.
      now left.
    } {
      replace (i + (q + 1) + 2) with (i + q + 0 + 3) by flia.
      apply Huvq3.
    }
    flia Ht1.
  } {
    replace (i + 1 + q + 1) with (i + q + 2) by flia.
    unfold "⊕", P, d2n, prop_carr, dig.
    rewrite (proj1 Huv2), (proj2 Huv2), Nat.add_0_l, Hr2.
    replace (carry v (i + q + 2)) with 1; [ easy | symmetry ].
    rewrite (carry_succ 2); cycle 1. {
      rewrite Hr2.
      replace 2 with (2 ^ 1) at 1 by easy.
      apply Nat.pow_lt_mono_r; [ pauto | flia ].
    } {
      now intros; rewrite Hr2; do 2 rewrite <- Nat.add_assoc.
    }
    replace (i + q + 2 + 1) with (i + q + 0 + 3) at 1 by flia.
    replace (i + q + 2 + 1) with (i + (q + 3)) by flia.
    rewrite (proj2 (Huvq3 _)), Hr2, Nat_div_add_same_l; [ | easy ].
    specialize (Hcv (q + 3)).
    remember (carry v (i + (q + 3))) as c eqn:Hc1.
    destruct c; [ easy | ].
    destruct c; [ easy | flia Hcv ].
  } {
    intros t.
    replace (i + 1 + q + t + 2) with (i + q + t + 3) by flia.
    specialize (Huvq3 t) as H1.
    unfold "⊕", P, d2n, prop_carr, dig.
    rewrite (proj1 H1), (proj2 H1), Hr2, Nat_mod_add_same_l; [ | easy ].
    replace (carry v (i + q + t + 3)) with 1; [ easy | symmetry ].
    rewrite (carry_succ 2); cycle 1. {
      rewrite Hr2.
      replace 2 with (2 ^ 1) at 1 by easy.
      apply Nat.pow_lt_mono_r; [ pauto | flia ].
    } {
      now intros; rewrite Hr2; do 3 rewrite <- Nat.add_assoc.
    }
    replace (i + q + t + 3 + 1) with (i + q + (t + 1) + 3) at 1 by flia.
    rewrite (proj2 (Huvq3 _)), Hr2, Nat_div_add_same_l; [ | easy ].
    specialize (Hcv (q + t + 3 + 1)) as H2.
    do 3 rewrite Nat.add_assoc in H2.
    remember (carry v (i + q + t + 3 + 1)) as c eqn:Hc1.
    destruct c; [ easy | ].
    destruct c; [ easy | flia H2 ].
  }
  apply Q.sub_lt, Q.lt_0_pair.
  destruct (le_dec (i + 1 + q + 1) (n - 1)); pauto.
}
assert (Htlq : t < q). {
  apply Nat_le_neq_lt; [ | easy ].
  apply Nat.nlt_ge; intros H.
  specialize (Hvjt _ H) as H1.
  replace (i + q + 1 - q) with (i + 1) in H1 by flia.
  now rewrite H1 in Huv1.
}
clear Htq.
specialize (Hjq (q - t - 1)) as Huvqt.
assert (H : q - t - 1 < q) by flia Htlq.
specialize (Huvqt H); clear H.
replace (i + (q - t - 1) + 2) with (i + q + 1 - t) in Huvqt by flia Htlq.
unfold "⊕" in Huvqt.
assert (H : v (i + q + 1 - t) = 2). {
  specialize (Hu (q + 1 - t)) as H2.
  replace (i + (q + 1 - t)) with (i + q + 1 - t) in H2 by flia Htlq.
  flia Hvt Huvqt H2.
}
move H before Hvt; clear Hvt; rename H into Hvt.
assert (Hut : u (i + q + 1 - t) = 0) by flia Hvt Huvqt.
move Hut after Hvt; clear Huvqt.
apply Nat.eq_add_1 in Huv2.
destruct Huv2 as [Huv2| Huv2]. {
  assert (Hqts : ∀ s, q - t < s → P v (i + s + 1) = 1). {
    intros s Hqs.
    destruct (le_dec (q + 2) s) as [Hq2s| Hq2s]. {
      specialize (Huvq3 (s - q - 2)) as H1.
      replace (i + q + (s - q - 2) + 3) with (i + s + 1) in H1 by flia Hq2s.
      unfold P, d2n, prop_carr, dig.
      rewrite (proj2 H1), Hr2, Nat_mod_add_same_l; [ | easy ].
      replace (carry v (i + s + 1)) with 1; [ easy | symmetry ].
      unfold carry.
      rewrite A_all_18. 2: {
        intros t1.
        replace (i + s + 1 + t1 + 1) with (i + q + (s + t1 - q - 1) + 3)
          by flia Hq2s.
        rewrite Hr2; apply Huvq3.
      }
      apply Q.intg_interv. 2: {
        split. {
          apply Q.le_add_le_sub_r.
          apply Q.le_add_le_sub_l.
          replace (2 - 1 // 1)%Q with (1 // 1)%Q by easy.
          apply Q.le_pair; [ pauto | easy | ].
          apply Nat.mul_le_mono_r.
          rewrite Hr2.
          replace 2 with (2 ^ 1) at 1 by easy.
          apply Nat.pow_le_mono_r; [ easy | min_n_ge ].
        }
        apply Q.sub_lt, Q.lt_0_pair; pauto.
      }
      apply Q.le_0_sub, (Q.le_pair_mono_l 1).
      split; [ pauto | ].
      apply Nat.neq_0_lt_0; pauto.
    }
    apply Nat.nle_gt in Hq2s.
    unfold P, d2n, prop_carr, dig.
    destruct (Nat.eq_dec (q + 1) s) as [H| H]. {
      rewrite <- H.
      replace (i + (q + 1) + 1) with (i + q + 2) by flia.
      rewrite (proj2 Huv2), Nat.add_0_l, Hr2.
      replace (carry v (i + q + 2)) with 1; [ easy | symmetry ].
      unfold carry.
      rewrite A_all_18. 2: {
        intros t1.
        replace (i + q + 2 + t1 + 1) with (i + q + t1 + 3) by flia.
        rewrite Hr2; apply Huvq3.
      }
      apply Q.intg_interv. 2: {
        split. {
          apply Q.le_add_le_sub_r.
          apply Q.le_add_le_sub_l.
          replace (2 - 1 // 1)%Q with (1 // 1)%Q by easy.
          apply Q.le_pair; [ pauto | easy | ].
          apply Nat.mul_le_mono_r.
          rewrite Hr2.
          replace 2 with (2 ^ 1) at 1 by easy.
          apply Nat.pow_le_mono_r; [ easy | min_n_ge ].
        }
        apply Q.sub_lt, Q.lt_0_pair; pauto.
      }
      apply Q.le_0_sub, (Q.le_pair_mono_l 1).
      split; [ pauto | ].
      apply Nat.neq_0_lt_0; pauto.
    }
    assert (Hq1s : s < q + 1) by flia Hq2s H; clear Hq2s H.
    specialize (Hvjt (q - s)) as H1.
    assert (H : q - s < t) by flia Hqs Hq1s.
    specialize (H1 H); clear H.
    replace (i + q + 1 - (q - s)) with (i + s + 1) in H1 by flia Hq1s.
    rewrite H1, Hr2.
    replace (carry v (i + s + 1)) with 0; [ easy | symmetry ].
    unfold carry.
    rewrite (A_9_8_all_18 (q - s)); cycle 1. {
      intros t1 Ht1.
      specialize (Hvjt (q - s - t1 - 1)) as H2.
      assert (H : q - s - t1 - 1 < t) by flia Hqs Ht1.
      specialize (H2 H); clear H.
      replace (i + q + 1 - (q - s - t1 - 1)) with (i + s + 1 + t1 + 1) in H2
        by flia Ht1.
      now rewrite Hr2.
    } {
      replace (i + s + 1 + (q - s) + 1) with (i + q + 2) by flia Hq1s.
      now rewrite Hr2.
    } {
      intros t1.
      replace (i + s + 1 + (q - s) + t1 + 2) with (i + q + t1 + 3)
        by flia Hq1s.
      specialize (Huvq3 t1) as H2.
      now rewrite Hr2.
    }
    apply Q.intg_small.
    remember (min_n (i + s + 1 + carry_cases v (i + s + 1))) as x eqn:Hx.
    remember (i + s + 1 + (q - s) + 1) as y eqn:Hy.
    split. {
      apply Q.le_0_sub.
      apply (Q.le_pair _ _ 1 1); [ pauto | easy | ].
      apply Nat.mul_le_mono_r.
      destruct (le_dec y (x - 1)) as [H2| H2]. {
        rewrite Hr2.
        replace 2 with (2 ^ 1) at 1 by easy.
        apply Nat.pow_le_mono_r; [ easy | rewrite Hx; min_n_ge ].
      }
      apply Nat.neq_0_lt_0; pauto.
    }
    apply Q.sub_lt, Q.lt_0_pair.
    destruct (le_dec y (x - 1)); pauto.
  }
  rewrite (A_9_8_all_18 (q - t - 1)); cycle 1. {
    intros s Hs.
    replace (i + 1 + s + 1) with (i + s + 2) by flia.
    unfold "⊕", P, d2n, prop_carr, dig.
    specialize (Hjq s) as H1.
    assert (H : s < q) by flia Hs.
    specialize (H1 H); clear H.
    unfold "⊕" in H1.
    apply Nat_eq_add_2 in H1.
    destruct H1 as [H1| H1]. {
      specialize (Hu (s + 2)); rewrite Nat.add_assoc in Hu; flia Hu H1.
    }
    assert (Hc1 : carry v (i + s + 2) = 1). {
      replace (i + s + 2) with (i + (s + 1) + 1) by flia.
      apply (rad_2_all_12_2_carry_1 (q - t - 1)); try easy. {
        intros p Hp; apply Hvq1; flia Hp.
      } {
        now replace (i + (q - t - 1) + 2) with (i + q + 1 - t) by flia Hs.
      }
      flia Hs.
    }
    now destruct H1 as [H1| H1]; rewrite (proj1 H1), (proj2 H1), Hr2, Hc1.
  } {
    replace (i + 1 + (q - t - 1) + 1) with (i + q + 1 - t) by flia Htlq.
    unfold "⊕", P, d2n, prop_carr, dig.
    rewrite Hut, Hvt, Nat.add_0_l, Hr2, Nat_mod_add_same_l; [ | easy ].
    replace (carry v (i + q + 1 - t)) with 0; [ easy | symmetry ].
    unfold carry.
    rewrite (A_9_8_all_18 t); cycle 1. {
      intros s Hst.
      replace (i + q + 1 - t + s + 1) with (i + q + 1 - (t - s - 1))
        by flia Htlq Hst.
      rewrite Hr2; apply Hvjt.
      flia Hst.
    } {
      rewrite Nat.sub_add; [ | flia Htlq ].
      now rewrite <- Nat.add_assoc, Hr2.
    } {
      intros s; rewrite Nat.sub_add; [ | flia Htlq ].
      replace (i + q + 1 + s + 2) with (i + q + s + 3) by flia.
      now rewrite Hr2, (proj2 (Huvq3 _)).
    }
    rewrite Nat.sub_add; [ | flia Htlq ].
    apply Q.intg_small.
    remember (i + q + 1 - t) as z eqn:Hz.
    remember (min_n (z + carry_cases v z)) as x eqn:Hx.
    remember (i + q + 1 + 1) as y eqn:Hy.
    split. {
      apply Q.le_0_sub.
      apply (Q.le_pair _ _ 1 1); [ pauto | easy | ].
      apply Nat.mul_le_mono_r.
      destruct (le_dec y (x - 1)) as [H2| H2]. {
        rewrite Hr2.
        replace 2 with (2 ^ 1) at 1 by easy.
        apply Nat.pow_le_mono_r; [ easy | rewrite Hx; min_n_ge ].
      }
      apply Nat.neq_0_lt_0; pauto.
    }
    apply Q.sub_lt, Q.lt_0_pair.
    destruct (le_dec y (x - 1)); pauto.
  } {
    intros s.
    replace (i + 1 + (q - t - 1) + s + 2) with (i + (q - t + s + 1) + 1)
      by flia Htlq.
    specialize (Hqts (q - t + s + 1)) as H1.
    assert (H : q - t < q - t + s + 1) by flia Htlq.
    specialize (H1 H); clear H.
    unfold "⊕"; rewrite H1, Hr2.
    destruct (le_dec (s + 1) t) as [Hst| Hst]. {
      specialize (Hvjt (t - s - 1)) as H2.
      assert (H : t - s - 1 < t) by flia Hst.
      specialize (H2 H); clear H.
      specialize (Hjq (q + s - t)) as H3.
      assert (H : q + s - t < q) by flia Hst Htlq.
      specialize (H3 H); clear H.
      remember (i + q + s - t + 2) as x eqn:Hx.
      replace (i + q + 1 - (t - s - 1)) with x in H2 by flia Hst Htlq Hx.
      replace (i + (q + s - t) + 2) with x in H3 by flia Htlq Hx.
      replace (i + (q - t + s + 1) + 1) with x by flia Htlq Hx.
      unfold "⊕" in H3.
      flia H2 H3.
    }
    apply Nat.nle_gt in Hst.
    destruct (Nat.eq_dec t s) as [Hts| Hts]. {
      replace (i + (q - t + s + 1) + 1) with (i + q + 2) by flia Htlq Hts.
      now rewrite (proj1 Huv2).
    }
    replace (i + (q - t + s + 1) + 1) with (i + q + (s - t - 1) + 3)
      by flia Htlq Hst Hts.
    now rewrite (proj1 (Huvq3 _)).
  }
  apply Q.sub_lt, Q.lt_0_pair.
  destruct (le_dec (i + 1 + (q - t - 1) + 1) (n - 1)); pauto.
}
rewrite (A_9_8_all_18 q); cycle 1. {
  intros s Hs.
  replace (i + 1 + s + 1) with (i + s + 2) by flia.
  destruct (lt_dec (q - t) (s + 1)) as [Hqts| Hqts]. {
    unfold "⊕", P, d2n, prop_carr, dig.
    specialize (Hvjt (q - s - 1)) as H1.
    assert (q - s - 1 < t) by flia Hs Hqts.
    specialize (H1 H); clear H.
    replace (i + q + 1 - (q - s - 1)) with (i + s + 2) in H1 by flia Hs Hqts.
    specialize (Hjq _ Hs) as H2.
    unfold "⊕" in H2.
    replace (u (i + s + 2)) with 1 by flia H1 H2.
    rewrite H1, Hr2.
    replace (carry v (i + s + 2)) with 1; [ easy | symmetry ].
    replace (i + s + 2) with (i + (s + 1) + 1) by flia.
    apply (rad_2_all_12_2_carry_1 (q + 1)); try easy. {
      intros p Hp.
      destruct (lt_dec p q) as [Hpq| Hpq]; [ now apply Hvq1 | ].
      replace p with q by flia Hp Hpq.
      now left.
    } {
      replace (i + (q + 1) + 2) with (i + q + 0 + 3) by flia.
      apply (proj2 (Huvq3 _)).
    }
    flia Hs.
  }
  apply Nat.nlt_ge in Hqts.
  destruct (Nat.eq_dec (q - t) (s + 1)) as [Hqs| Hqs]. {
    replace (i + s + 2) with (i + q + 1 - t) by flia Hqs.
    unfold "⊕", P, d2n, prop_carr, dig.
    rewrite Hut, Hvt, Nat.add_0_l, Hr2, Nat_mod_add_same_l; [ | easy ].
    replace (carry v (i + q + 1 - t)) with 1; [ easy | symmetry ].
    replace (i + q + 1 - t) with (i + (q - t) + 1) by flia Hqs.
    apply (rad_2_all_12_2_carry_1 (q + 1)); try easy. {
      intros p Hp.
      destruct (lt_dec p q) as [Hpq| Hpq]; [ now apply Hvq1 | ].
      replace p with q by flia Hp Hpq.
      now left.
    } {
      replace (i + (q + 1) + 2) with (i + q + 0 + 3) by flia.
      apply (proj2 (Huvq3 _)).
    }
    flia Hs.
  }
  assert (Hsqt : s + 1 < q - t) by flia Hqts Hqs; clear Hqts Hqs.
  unfold "⊕", P, d2n, prop_carr, dig.
  specialize (Hjq _ Hs) as H1.
  replace (carry v (i + s + 2)) with 1. 2: {
    symmetry.
    replace (i + s + 2) with (i + (s + 1) + 1) by flia.
    apply (rad_2_all_12_2_carry_1 (q - t - 1)); try easy. {
      intros p Hp.
      destruct (lt_dec p q) as [Hpq| Hpq]; [ now apply Hvq1 | ].
      replace p with q by flia Hp Hpq.
      now left.
    } {
      now replace (i + (q - t - 1) + 2) with (i + q + 1 - t) by flia Hsqt.
    }
    flia Hsqt.
  }
  apply Nat_eq_add_2 in H1.
  destruct H1 as [H1| H1]. {
    specialize (Hu (s + 2)); rewrite Nat.add_assoc in Hu; flia Hu H1.
  }
  now destruct H1 as [H1| H1]; rewrite (proj1 H1), (proj2 H1), Hr2.
} {
  replace (i + 1 + q + 1) with (i + q + 2) by flia.
  unfold "⊕", P, d2n, prop_carr, dig.
  rewrite (proj1 Huv2), (proj2 Huv2), Nat.add_0_l, Hr2.
  replace (carry v (i + q + 2)) with 1; [ easy | symmetry ].
  rewrite (carry_succ 2); cycle 1. {
    rewrite Hr2.
    replace 2 with (2 ^ 1) at 1 by easy.
    apply Nat.pow_lt_mono_r; [ pauto | flia ].
  } {
    now intros; rewrite Hr2; do 2 rewrite <- Nat.add_assoc.
  }
  replace (i + q + 2 + 1) with (i + q + 0 + 3) at 1 by flia.
  replace (i + q + 2 + 1) with (i + (q + 3)) by flia.
  rewrite (proj2 (Huvq3 _)), Hr2, Nat_div_add_same_l; [ | easy ].
  specialize (Hcv (q + 3)).
  remember (carry v (i + (q + 3))) as c eqn:Hc1.
  destruct c; [ easy | ].
  destruct c; [ easy | flia Hcv ].
} {
  intros s.
  replace (i + 1 + q + s + 2) with (i + q + s + 3) by flia.
  specialize (Huvq3 s) as H1.
  unfold "⊕", P, d2n, prop_carr, dig.
  rewrite (proj1 H1), (proj2 H1), Hr2, Nat_mod_add_same_l; [ | easy ].
  replace (carry v (i + q + s + 3)) with 1; [ easy | symmetry ].
  rewrite (carry_succ 2); cycle 1. {
    rewrite Hr2.
    replace 2 with (2 ^ 1) at 1 by easy.
    apply Nat.pow_lt_mono_r; [ pauto | flia ].
  } {
    now intros; rewrite Hr2; do 3 rewrite <- Nat.add_assoc.
  }
  replace (i + q + s + 3 + 1) with (i + q + (s + 1) + 3) at 1 by flia.
  rewrite (proj2 (Huvq3 _)), Hr2, Nat_div_add_same_l; [ | easy ].
  specialize (Hcv (q + s + 3 + 1)) as H2.
  do 3 rewrite Nat.add_assoc in H2.
  remember (carry v (i + q + s + 3 + 1)) as c eqn:Hc1.
  destruct c; [ easy | ].
  destruct c; [ easy | flia H2 ].
}
apply Q.sub_lt, Q.lt_0_pair.
destruct (le_dec (i + 1 + q + 1) (n - 1)); pauto.
Qed.

Theorem rad_2_sum_3_all_9_uv_0_1_uPv_0_222 {r : radix} : ∀ u v i,
  rad = 2
  → (∀ k, u (i + k) ≤ 1)
  → (∀ k, v (i + k) ≤ 2)
  → (∀ k, fA_ge_1_ε (u ⊕ v) i k = true)
  → (u ⊕ v) (i + 1) = 0
  → (u ⊕ v) (i + 2) = 1
  → ∀ p, (u ⊕ P v) (i + p + 1) = 0
  → ∀ q, (u ⊕ P v) (i + p + q + 2) = 2.
Proof.
intros * Hr2 Hu Hv Hauv Huv1 Huv2 p Hp q.
assert (Huvl3 : ∀ k, (u ⊕ v) (i + k) ≤ 3). {
  intros j.
  unfold "⊕"; replace 3 with (1 + 2) by easy.
  apply Nat.add_le_mono; [ apply Hu | apply Hv ].
}
specialize (rad_2_sum_3_all_9_02_1_333 _ _ Hr2 Huvl3 Hauv) as Huvc3.
specialize (Huvc3 (or_introl Huv1) Huv2).
assert (Huv3 : ∀ k, u (i + k + 3) = 1 ∧ v (i + k + 3) = 2). {
  intros s.
  specialize (Huvc3 s) as H2.
  destruct H2 as (H2, _).
  unfold "⊕" in H2.
  specialize (Hu (s + 3)) as H3.
  specialize (Hv (s + 3)) as H4.
  rewrite Nat.add_assoc in H3, H4.
  flia H2 H3 H4.
}
move Huv3 before Huv2.
move Huvc3 before Huv3.
destruct p. 2: {
  destruct p. 2: {
    (* state (p > 1)
     i+1       i+p+1
   u 0 . . . . 0/1 ← contrad
   v 0 . . . . .
 u+v 0 1 3 3 3 3
  Pv 1 . . . . 0
u+Pv 1 1 1 1 1 0
     *)
    specialize (Huv3 p) as H2.
    replace (i + S (S p) + 1) with (i + p + 3) in Hp by flia.
    apply Nat.eq_add_0 in Hp.
    now rewrite (proj1 Hp) in H2.
  }
  (* state (p = 1)
     i+1
   u 0 0 1 1 1 1
   v 0 1 2 2 2 2
 u+v 0 1 3 3 3 3
  Pv 1 0 1 1 1 1
u+Pv 1 0 2 2 2 2
   *)
  replace (i + 1 + q + 2) with (i + q + 3) by flia.
  specialize (Huv3 q) as H1.
  unfold "⊕", P, d2n, prop_carr, dig.
  rewrite (proj1 H1), (proj2 H1), Hr2.
  rewrite Nat_mod_add_same_l; [ | easy ].
  replace (carry v (i + q + 3)) with 1; [ easy | symmetry ].
  unfold carry.
  rewrite A_split_first; [ | min_n_ge ].
  replace (S (i + q + 3)) with (i + S q + 3) at 1 by flia.
  rewrite (proj2 (Huv3 _)), Hr2, Q.pair_diag; [ | easy ].
  rewrite (Q.intg_add_nat_l 1); [ | now apply Q.le_0_mul_r ].
  symmetry; replace 1 with (1 + 0) at 1 by flia; symmetry; f_equal.
  apply Q.intg_small.
  split; [ now apply Q.le_0_mul_r | ].
  apply rad_2_sum_2_half_A_lt_1; [ easy | ].
  intros p.
  now replace (S (i + q + 3) + p) with (i + (p + q + 4)) by flia.
}
(* state (p = 0)
     i+1
   u 0 . 1 1 1 1
   v 0 . 2 2 2 2
 u+v 0 1 3 3 3 3
  Pv 0 . 1 1 1 1
u+Pv 0 . 2 2 2 2
 *)
(*clear Hjp;*) rewrite Nat.add_0_r in Hp |-*.
(* seems true for q > 0 *)
destruct q. 2: {
  replace (i + S q + 2) with (i + q + 3) by flia.
  unfold "⊕", P, d2n, prop_carr, dig.
  specialize (Huv3 q) as H1.
  rewrite (proj1 H1), (proj2 H1), Hr2.
  rewrite Nat_mod_add_same_l; [ | easy ].
  replace (carry v (i + q + 3)) with 1; [ easy | symmetry ].
  unfold carry.
  rewrite A_split_first; [ | min_n_ge ].
  replace (S (i + q + 3)) with (i + S q + 3) at 1 by flia.
  rewrite (proj2 (Huv3 _)), Hr2, Q.pair_diag; [ | easy ].
  rewrite (Q.intg_add_nat_l 1); [ | now apply Q.le_0_mul_r ].
  symmetry; replace 1 with (1 + 0) at 1 by flia; symmetry; f_equal.
  apply Q.intg_small.
  split; [ now apply Q.le_0_mul_r | ].
  apply rad_2_sum_2_half_A_lt_1; [ easy | ].
  intros p.
  now replace (S (i + q + 3) + p) with (i + (p + q + 4)) by flia.
}
(* state (p = 0 & q = 0)
     i+1
   u 0
   v 0
 u+v 0 1
  Pv 0
u+Pv 0
 *)
rewrite Nat.add_0_r.
unfold "⊕", P, d2n, prop_carr, dig.
apply Nat.eq_add_1 in Huv2.
destruct Huv2 as [Huv2| Huv2]. {
  rewrite (proj1 Huv2), (proj2 Huv2), Nat.add_0_l, Hr2.
  (* state (p = 0 & q = 0 & u2 = 1, v2 = 0)
     i+1
   u 0 1 1 1 1 1
   v 0 0 2 2 2 2
 u+v 0 1 3 3 3 3
  Pv 0 1 1 1 1 1
u+Pv 0 2 2 2 2 2
   *)
  replace (carry v (i + 2)) with 1; [ easy | symmetry ].
  unfold carry.
  rewrite A_split_first; [ | min_n_ge ].
  replace (S (i + 2)) with (i + 0 + 3) at 1 by flia.
  rewrite (proj2 (Huv3 _)), Hr2, Q.pair_diag; [ | easy ].
  rewrite (Q.intg_add_nat_l 1); [ | now apply Q.le_0_mul_r ].
  symmetry; replace 1 with (1 + 0) at 1 by flia; symmetry; f_equal.
  apply Q.intg_small.
  split; [ now apply Q.le_0_mul_r | ].
  apply rad_2_sum_2_half_A_lt_1; [ easy | ].
  intros p.
  now replace (S (i + 2) + p) with (i + (p + 3)) by flia.
}
(* state (p = 0 & q = 0 & u2 = 0, v2 = 1)
     i+1
   u 0 0 1 1 1 1
   v 0 1 2 2 2 2
 u+v 0 . 3 3 3 3
  Pv 0/1 0 1 1 1 1 <- contrad
u+Pv 0 . 2 2 2 2
 *)
exfalso.
unfold "⊕", P, d2n, prop_carr, dig in Hp.
apply Nat.eq_add_0 in Huv1.
rewrite (proj1 Huv1), (proj2 Huv1), Nat.add_0_l, Hr2 in Hp.
replace (carry v (i + 1)) with 1 in Hp; [ easy | symmetry ].
replace (i + 1) with (i + 0 + 1) by flia.
apply (rad_2_all_12_2_carry_1 1); try easy; try pauto. {
  intros p Hp1.
  apply Nat.lt_1_r in Hp1.
  rewrite Hp1, Nat.add_0_r.
  now rewrite (proj2 Huv2); left.
} {
  replace (i + 1 + 2) with (i + 0 + 3) by flia.
  now rewrite (proj2 (Huv3 _)).
}
Qed.

Theorem pre_Hugo_Herbelin_82_rad_2_lemma_1 {r : radix} : ∀ u v i j k,
  rad = 2
  → (∀ k, u (i + k) ≤ 1)
  → (∀ k, v (i + k) ≤ 2)
  → (∀ p, p < j → fA_ge_1_ε v i p = true)
  → fA_ge_1_ε v i j = false
  → (∀ p, p < k → fA_ge_1_ε (u ⊕ P v) i p = true)
  → fA_ge_1_ε (u ⊕ P v) i k = false
  → (∀ k, fA_ge_1_ε (u ⊕ v) i k = true)
  → (u ⊕ v) (i + 1) = 0
  → (A i (min_n (i + k)) (u ⊕ P v) < 1)%Q.
Proof.
intros * Hr2 Hu Hv Hjj Hj Hjk Hk Hauv Huv1.
remember (min_n i) as n eqn:Hn.
remember (min_n (i + j)) as nj eqn:Hnj.
remember (min_n (i + k)) as nk eqn:Hnk.
move nj before n; move nk before nj.
(**)
assert (Huvl3 : ∀ k, (u ⊕ v) (i + k) ≤ 3). {
  intros p.
  unfold "⊕"; replace 3 with (1 + 2) by easy.
  apply Nat.add_le_mono; [ apply Hu | apply Hv ].
}
destruct (zerop (carry (u ⊕ P v) (i + 1))) as [Hcuv| Hcuv]. {
  destruct (LPO_fst (λ j, negb ((u ⊕ P v) (i + j + 1) =? 0))) as [H| Hupv0]. {
    assert (Hupv0 : ∀ k, (u ⊕ P v) (i + k + 1) ≠ 0). {
      intros p; specialize (H p).
      apply Bool.negb_true_iff in H.
      now apply Nat.eqb_neq in H.
    }
    clear H.
    rewrite A_all_9; [ now apply Q.sub_lt | ].
    intros p Hp; rewrite Hr2; replace (2 - 1) with 1 by easy.
(* u+v
  02*∞
  02*13*∞
  02*31*∞
  02*31*02*∞
  02*31*02*13*∞
  02*31*02*31*∞
  02*31*02*31*02*13*∞
  02*31*02*31*02*31*∞
  02*31*02*31*02*31*02*∞
  02*31*02*31*02*31*02*13*∞
  02*31*02*31*02*31*02*31*∞
  02*31*02*31*02*31*02*31*02*∞
  02*31*02*31*02*31*02*31*02*13∞
  02*31*02*31*02*31*02*31*02*31*∞
  02*31*02*31*02*31*02*31*02*31*0
  02*31*1
*)
...
(**)
    specialize (Hupv0 p) as Hupvp.
    remember ((u ⊕ P v) (i + p + 1)) as x eqn:Hx; symmetry in Hx.
    destruct x; [ easy | clear Hupvp ].
    destruct x; [ easy | exfalso ].
    destruct x. 2: {
      unfold "⊕" in Hx.
      rewrite <- Nat.add_assoc in Hx.
      specialize (Hu (p + 1)) as H1.
      specialize (P_le v (i + (p + 1))) as H2.
      flia Hr2 Hx H1 H2.
    }
    apply Nat_eq_add_2 in Hx.
    destruct Hx as [Hx| Hx]. {
      specialize (Hu (p + 1)) as H1.
      rewrite Nat.add_assoc in H1; flia Hx H1.
    }
    destruct Hx as [Hx| Hx]. 2: {
      specialize (P_le v (i + (p + 1))) as H1.
      rewrite Nat.add_assoc, Hr2 in H1; flia Hx H1.
    }
    assert (Hupvle : ∀ k, (u ⊕ P v) (i + k) ≤ 2). {
      intros q; unfold "⊕".
      specialize (Hu q) as H1.
      specialize (P_le v (i + q)) as H2.
      rewrite Hr2 in H2; flia H1 H2.
    }
    assert (Hcupv : carry (u ⊕ P v) (i + 1) = 1). {
      replace i with (i + 0) by easy.
      destruct p. {
        apply Nat.eq_add_0 in Huv1.
        unfold "⊕" in Hx.
        rewrite Nat.add_0_r, (proj1 Huv1) in Hx.
        flia Hx.
      }
      apply (rad_2_all_12_2_carry_1 p); [ easy | easy | | | flia ].
      -intros q Hq.
       specialize (Hupv0 (q + 1)) as H1.
       replace (i + (q + 1) + 1) with (i + q + 2) in H1 by flia.
       specialize (Hupvle (q + 2)) as H2.
       rewrite Nat.add_assoc in H2.
       flia H1 H2.
      -replace (i + S p + 1) with (i + p + 2) in Hx by flia.
       now unfold "⊕"; rewrite (proj1 Hx), (proj2 Hx).
    }
    move Hcuv before Hcupv.
    now rewrite Hcuv in Hcupv.
  }
  destruct Hupv0 as (p & H1 & H2).
  assert (Hjp : ∀ q, q < p → (u ⊕ P v) (i + q + 1) ≠ 0). {
    intros q Hq.
    specialize (H1 _ Hq).
    apply Bool.negb_true_iff in H1.
    now apply Nat.eqb_neq in H1.
  }
  move Hjp before H1; clear H1.
  assert (Hp : (u ⊕ P v) (i + p + 1) = 0). {
    apply Bool.negb_false_iff in H2.
    now apply Nat.eqb_eq in H2.
  }
  clear H2.
  assert (H : ∀ q, q < p → (u ⊕ P v) (i + q + 1) = 1). {
    intros q Hq.
    specialize (Hjp _ Hq) as H1.
    destruct (Nat.eq_dec ((u ⊕ P v) (i + q + 1)) 2) as [H2| H2]. {
      destruct (zerop q) as [Hzq| Hzq]. {
        subst q.
        apply Nat.eq_add_0 in Huv1.
        rewrite Nat.add_0_r in H2.
        unfold "⊕" in H2.
        rewrite (proj1 Huv1), Nat.add_0_l in H2.
        specialize (P_le v (i + 1)) as H3.
        rewrite H2, Hr2 in H3; flia H3.
      }
      rewrite <- (Nat.add_0_r i) in Hcuv.
      rewrite (rad_2_all_12_2_carry_1 (q - 1)) in Hcuv; try easy. {
        intros s.
        unfold "⊕".
        specialize (Hu s) as H3.
        specialize (P_le v (i + s)) as H4.
        rewrite Hr2 in H4.
        flia H3 H4.
      } {
        intros s Hs.
        specialize (Hjp (s + 1)) as H3.
        replace (i + (s + 1) + 1) with (i + s + 2) in H3 by flia.
        assert (H : s + 1 < p) by flia Hq Hs.
        specialize (H3 H); clear H.
        remember ((u ⊕ P v) (i + s + 2)) as x eqn:Hx.
        destruct x; [ easy | ].
        destruct x; [ now left | ].
        destruct x; [ now right | ].
        exfalso; clear H3.
        specialize (Hu (s + 2)) as H3.
        specialize (P_le v (i + s + 2)) as H4.
        rewrite Nat.add_assoc in H3.
        rewrite Hr2 in H4.
        unfold "⊕" in Hx.
        flia Hx H3 H4.
      } {
        now replace (i + (q - 1) + 2) with (i + q + 1) by flia Hzq.
      }
      flia.
    }
    remember ((u ⊕ P v) (i + q + 1)) as x eqn:Hx.
    destruct x; [ easy | ].
    destruct x; [ easy | exfalso ].
    destruct x; [ easy | ].
    specialize (Hu (q + 1)) as H3.
    specialize (P_le v (i + q + 1)) as H4.
    rewrite Nat.add_assoc in H3.
    rewrite Hr2 in H4.
    unfold "⊕" in Hx.
    flia Hx H3 H4.
  }
  move H before Hjp; clear Hjp; rename H into Hjp.
  specialize (all_fA_ge_1_ε_P_999 _ _ Hauv) as Hpuv.
  rewrite Hr2 in Hpuv.
  replace (2 - 1) with 1 in Hpuv by easy.
  specialize (rad_2_sum_3_all_9_02_123 (u ⊕ v) i Hr2) as Huv2.
  assert (H : ∀ k, (u ⊕ v) (i + k + 1) ≤ 3). {
    now intros; rewrite <- Nat.add_assoc.
  }
  specialize (Huv2 H Hauv (or_introl Huv1)); clear H.
  move Huv2 before Huv1.
  rewrite (A_9_8_all_18 p); rewrite Hr2; [ | easy | easy | ]; cycle 1. {
    intros q.
    move q before p.
    replace (2 * (2 - 1)) with 2 by easy.
    destruct Huv2 as [Huv2| Huv2]. {
      now apply rad_2_sum_3_all_9_uv_0_1_uPv_0_222.
    }
    destruct Huv2 as [Huv2| Huv2]. {
(* state
     i+1       i+p+1
   u 0 . . . . .
   v 0 . . . . .
 u+v 0 2 . . . .
  Pv 1 . . . . .
u+Pv 1 1 1 1 1 0
*)
      specialize (rad_2_sum_3_all_9_02_222_123 1 (u ⊕ v) i Hr2) as Huv3.
      replace (i + 1 + 2) with (i + 3) in Huv3 by flia.
      assert (H : ∀ k, (u ⊕ v) (i + k + 1) ≤ 3). {
        now intros; rewrite <- Nat.add_assoc.
      }
      specialize (Huv3 H Hauv (or_introl Huv1)); clear H.
      assert (H : ∀ k, k < 1 → (u ⊕ v) (i + k + 2) = 2). {
        intros s Hs.
        now apply Nat.lt_1_r in Hs; rewrite Hs, Nat.add_0_r.
      }
      specialize (Huv3 H); clear H.
      move Huv3 before Huv2.
      destruct Huv3 as [Huv3| Huv3]. {
(* state
     i+1       i+p+1
   u 0 . . . . .
   v 0 . . . . .
 u+v 0 2 1 . . .
  Pv 1 . . . . .
u+Pv 1 1 1 1 1 0
*)
...
... suite ok
  }
  apply Q.sub_lt, Q.lt_0_pair.
  destruct (le_dec (i + p + 1) (nk - 1)); pauto.
}
...
... (* code quand je testais (zerop (carry (u ⊕ v) (i + 1)))
       au lieu de u ⊕ P v *)
    unfold carry in Hcuv, Hcupv.
    rewrite (all_fA_ge_1_ε_NQintg_A' 3) in Hcuv; cycle 1. {
      apply three_lt_rad_pow.
    } {
      intros s; rewrite Hr2.
      now replace (i + 1 + s) with (i + (s + 1)) by flia.
    } {
      intros s.
      now apply A_ge_1_add_r_true_if.
    }
    remember (carry_cases (u ⊕ P v) (i + 1)) as n1 eqn:Hn1.
    rewrite <- (all_fA_ge_1_ε_NQintg_A' 3) with (k0 := n1) in Hcuv; cycle 1. {
      apply three_lt_rad_pow.
    } {
      intros s; rewrite Hr2.
      now replace (i + 1 + s) with (i + (s + 1)) by flia.
    } {
      intros s.
      now apply A_ge_1_add_r_true_if.
    }
    rewrite A_additive in Hcuv, Hcupv.
    rewrite Q.intg_add_cond in Hcuv; [ | easy | easy ].
    rewrite Q.intg_add_cond in Hcupv; [ | easy | easy ].
    rewrite Q.intg_small, Nat.add_0_l in Hcuv. 2: {
      split; [ easy | ].
      apply A_upper_bound_for_dig; intros s Hs; rewrite Hr2.
      now replace s with (i + (s - i)) by flia Hs.
    }
    rewrite Q.intg_small, Nat.add_0_l in Hcupv. 2: {
      split; [ easy | ].
      apply A_upper_bound_for_dig; intros s Hs; rewrite Hr2.
      now replace s with (i + (s - i)) by flia Hs.
    }
    rewrite Q.intg_small, Nat.add_0_l in Hcupv. 2: {
      split; [ easy | ].
      apply A_upper_bound_for_dig; intros s Hs; rewrite Hr2.
      replace (2 - 1) with (rad - 1) by flia Hr2.
      apply P_le.
    }
    rewrite Q.frac_small in Hcuv. 2: {
      split; [ easy | ].
      apply A_upper_bound_for_dig; intros s Hs; rewrite Hr2.
      now replace s with (i + (s - i)) by flia Hs.
    }
    rewrite Q.frac_small in Hcupv. 2: {
      split; [ easy | ].
      apply A_upper_bound_for_dig; intros s Hs; rewrite Hr2.
      now replace s with (i + (s - i)) by flia Hs.
    }
    rewrite Q.frac_small in Hcupv. 2: {
      split; [ easy | ].
      apply A_upper_bound_for_dig; intros s Hs; rewrite Hr2.
      replace (2 - 1) with (rad - 1) by flia Hr2.
      apply P_le.
    }
    rewrite Nat.add_comm in Hcuv.
    destruct
      (Q.lt_le_dec
         (A (i + 1) (min_n (i + 1 + n1)) u +
          Q.frac (A (i + 1) (min_n (i + 1 + n1)) v)) 1) as [H1| H1];
      [ | easy ].
    rewrite Nat.add_0_l in Hcuv.
    destruct
      (Q.lt_le_dec
         (A (i + 1) (min_n (i + 1 + n1)) u +
          A (i + 1) (min_n (i + 1 + n1)) (P v)) 1) as [H2| H2]; [ easy | ].
    clear Hcupv.
    apply Q.eq_intg_0 in Hcuv; [ | easy ].
    rewrite Q.frac_small in H1; [ | easy ].
    apply Q.nlt_ge in H2.
    apply H2; clear H2.
    remember (min_n (i + 1 + n1)) as n2 eqn:Hn2; subst n1.
    clear Hcuv.
    assert (Hpv1 : P v (i + 1) = 1). {
      specialize (Hupv0 0) as H3.
      apply Nat.eq_add_0 in Huv1.
      unfold "⊕" in H3.
      rewrite Nat.add_0_r, (proj1 Huv1), Nat.add_0_l in H3.
      specialize (P_le v (i + 1)) as H4.
      rewrite Hr2 in H4; flia H3 H4.
    }
    move Hpv1 after Hx.
(* situation

     i+1     i+p+1
     ↓       ↓
   u 0 . . . 1
   v 0 . . . .
 u+v 0 . . . .
  Pv 1 . . . 1
u+Pv 1 . . . 2

*)
(* contre-exemple ?
   u 0 1 1 1 1
   v 0 2 0 0 0 2
 u+v 0 3 1 1 1 .
  Pv 1 0 0 0 1
u+Pv 1 1 1 1 2
  non, car en . ci-dessus, il ne peut y avoir que 0 ou 1, d'après
  l'automate, ce qui est incompatible avec la valeur en v
*)
Search (A _ _ _ ≤ A _ _ _)%Q.
(* est-ce qu'on peut prouver que A i n (P u) ≤ A i n u ? Est-ce toujours
vrai, d'ailleurs ? *)
(* bin non, je pense que soit ils sont égaux, soit A (P u) = A u + ε, où
ε = 1/r^(n-i-1), ce 2e cas arrivant si c(n-1)=1 et que A u = 1-ε; du coup
c(i)=1 aussi, la retenue se propageant partout *)
rename H1 into HAA1.
rename p into p1.
...
(* ancienne preuve, non finie, pas sûr qu'elle soit finissable, faut
voir, mais ne prenant pas les choses à bras le corps ; je me lance,
ci-dessus, dans une preuve qui part de u+Pv avec deux considérations :
soit la retenue en i de u+v vaut 0 et alors u+Pv serait un
999...8/18/18/18... ou un 999... ; soit la retenue de u+v en i vaut 1
et alors u+Pv serait forcément un 18/18/18... *)
assert (Huvl3 : ∀ k, (u ⊕ v) (i + k) ≤ 3). {
  intros p.
  unfold "⊕"; replace 3 with (1 + 2) by easy.
  apply Nat.add_le_mono; [ apply Hu | apply Hv ].
}
specialize (rad_2_sum_3_all_9_02_222_13 0 (u ⊕ v) i Hr2) as H1.
assert (H : ∀ k, (u ⊕ v) (i + k + 1) ≤ 3). {
  now intros; rewrite <- Nat.add_assoc.
}
specialize (H1 H Hauv (or_introl Huv1)); clear H.
assert (H : ∀ k, k < 0 → (u ⊕ v) (i + k + 2) = 2) by (intros p H; flia H).
specialize (H1 H); clear H.
destruct H1 as [Huvn| H1]. {
  destruct (LPO_fst (λ p, Nat.eqb (v (i + p + 2)) 1)) as [H1| H1]. {
    assert (H : ∀ p, v (i + p + 2) = 1). {
      intros p; specialize (H1 p).
      now apply Nat.eqb_eq in H1.
    }
    clear H1; rename H into Hv2.
    (* v=01111..., then u=01111... and Pv=01111..., then u+Pv=02222...
       then resolved by A_split_first and A_all_18 *)
    rewrite A_split_first; [ | rewrite Hnk; min_n_ge ].
    replace (S i) with (i + 1) by flia.
    apply Nat.eq_add_0 in Huv1.
    unfold "⊕" at 1.
    rewrite (proj1 Huv1), Nat.add_0_l, Hr2.
    replace (P v (i + 1)) with 0. 2: {
      symmetry.
      unfold P, d2n, prop_carr, dig.
      rewrite (proj2 Huv1), Nat.add_0_l, Hr2.
      replace (carry v (i + 1)) with 0; [ easy | ].
      symmetry; unfold carry.
      apply Q.intg_small.
      split; [ easy | ].
      rewrite A_all_9. 2: {
        intros p Hp.
        replace (i + 1 + p + 1) with (i + p + 2) by flia.
        now rewrite Hr2.
      }
      apply Q.sub_lt, Q.lt_0_pair; pauto.
    }
    rewrite Q.add_0_l.
    apply rad_2_sum_2_half_A_lt_1; [ easy | ].
    intros p; unfold "⊕"; rewrite <- Nat.add_assoc.
    replace 2 with (1 + 1) by easy.
    apply Nat.add_le_mono; [ apply Hu | ].
    replace 1 with (rad - 1) by flia Hr2.
    apply P_le.
  }
  destruct H1 as (p & Hjp & Hp).
  assert (H : v (i + p + 2) = 2). {
    apply Nat.eqb_neq in Hp.
    specialize (Huvn p) as H1.
    specialize (Hu (p + 2)) as H2.
    rewrite Nat.add_assoc in H2.
    unfold "⊕" in H1.
    flia Hp H1 H2.
  }
  clear Hp; rename H into Hp.
  destruct
    (LPO_fst
       (λ q,
        match LPO_fst (λ s, Nat.eqb (v (i + q + s + 2)) 1) with
        | inl _ => false
        | inr _ _ => true
        end)) as [Hv2| Hv2]. {
    assert
      (H : ∀ q, ∃ s,
      (∀ j, j < s → v (i + q + j + 2) = 1) ∧ v (i + q + s + 2) = 2). {
      intros q.
      specialize (Hv2 q).
      destruct (LPO_fst (λ s, v (i + q + s + 2) =? 1)) as [H| H]; [ easy | ].
      destruct H as (s & Hjs & Hs); clear Hv2.
      exists s.
      apply Nat.eqb_neq in Hs.
      specialize (Huvn (q + s)) as H1.
      specialize (Hu (q + s + 2)) as H2.
      rewrite Nat.add_assoc in H1.
      do 2 rewrite Nat.add_assoc in H2.
      unfold "⊕" in H1.
      split; [ | flia Hs H1 H2 ].
      intros t Ht.
      specialize (Hjs _ Ht) as H3.
      now apply Nat.eqb_eq in H3.
    }
    clear Hv2; rename H into Hv2.
    assert (H : ∀ j, j < p → v (i + j + 2) = 1). {
      intros q Hq; specialize (Hjp q Hq) as H1.
      now apply Nat.eqb_eq in H1.
    }
    move H before Hjp; clear Hjp; rename H into Hjp.
    (* v=0111211211112..., then u=0111011011110... and Pv=10000100100000...,
       then u+Pv=111111..., then resolved by A_all_9 *)
    rewrite A_split_first; [ | rewrite Hnk; min_n_ge ].
    replace (S i) with (i + 1) by flia.
    apply Nat.eq_add_0 in Huv1.
    unfold "⊕" at 1.
    rewrite (proj1 Huv1), Nat.add_0_l, Hr2.
    eapply Q.le_lt_trans. {
      apply Q.add_le_mono_r with (y := (1 // 2)%Q).
      apply Q.le_pair_mono_r.
      replace 1 with (rad - 1) at 2 by flia Hr2.
      apply P_le.
    }
    apply Q.lt_add_lt_sub_l.
    replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
    apply Q.mul_lt_mono_pos_r; [ easy | ].
    rewrite A_all_9; [ now apply Q.sub_lt | ].
    intros s Hs; rewrite Hr2.
    replace (i + 1 + s + 1) with (i + s + 2) in Hs |-* by flia.
    unfold "⊕".
    specialize (Huvn s) as Huv2.
    apply Nat_eq_add_2 in Huv2.
    destruct Huv2 as [Huv2| Huv2]. {
      specialize (Hu (s + 2)) as H1.
      rewrite Nat.add_assoc in H1; flia Huv2 H1.
    }
    assert
      (Hcs : ∀ s t,
        (∀ j, j < t → v (i + S s + j + 2) = 1)
        → v (i + s + t + 3) = 2
        → carry v (i + s + 2) = 1). {
      clear s Hs Huv2.
      intros * Hjt Ht.
      clear - Hr2 Hu Hv Hjt Ht Huvn.
      revert s Hjt Ht.
      induction t; intros. {
        rewrite Nat.add_0_r in Ht.
        rewrite (carry_succ 2); cycle 1. {
          rewrite Hr2.
          replace 2 with (2 ^ 1) at 1 by easy.
          apply Nat.pow_lt_mono_r; [ pauto | flia ].
        } {
          intros; rewrite Hr2.
          specialize (Huvn (s + k)) as H1.
          replace (i + (s + k) + 2) with (i + s + 2 + k) in H1 by flia.
          unfold "⊕" in H1; flia H1.
        }
        replace (i + s + 2 + 1) with (i + s + 3) by flia.
        rewrite Ht, Hr2, Nat_div_add_same_l; [ | easy ].
        specialize (carry_upper_bound_for_adds 2 v i) as H1.
        specialize (H1 (Nat.neq_succ_0 _)).
        assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
          now intros; rewrite Hr2, <- Nat.add_assoc.
        }
        specialize (H1 H (s + 3)); clear H.
        rewrite Nat.add_assoc in H1.
        remember (carry v (i + s + 3)) as c eqn:Hc.
        destruct c; [ easy | ].
        destruct c; [ easy | flia H1 ].
      }
      specialize (IHt (S s)).
      assert (H : ∀ j, j < t → v (i + S (S s) + j + 2) = 1). {
        intros q Hq.
        replace (i + S (S s) + q) with (i + S s + S q) by flia.
        apply Hjt; flia Hq.
      }
      replace (i + s + S t) with (i + S s + t) in Ht by flia.
      specialize (IHt H Ht); clear H.
      rewrite (carry_succ 2); cycle 1. {
        rewrite Hr2.
        replace 2 with (2 ^ 1) at 1 by easy.
        apply Nat.pow_lt_mono_r; [ pauto | flia ].
      } {
        now intros; rewrite Hr2; do 2 rewrite <- Nat.add_assoc.
      }
      replace (i + s + 2 + 1) with (i + S s + 2) by flia.
      rewrite IHt, Hr2.
      specialize (Huvn (S s)) as H1.
      apply Nat_eq_add_2 in H1.
      destruct H1 as [H1| H1]. {
        specialize (Hu (S s + 2)) as H2.
        rewrite Nat.add_assoc in H2; flia H1 H2.
      }
      now destruct H1 as [H1| H1]; rewrite (proj2 H1).
    }
    destruct Huv2 as [Huv2| Huv2]. {
      rewrite (proj1 Huv2).
      replace (2 - 1) with (1 + 0) by easy; f_equal.
      unfold P, d2n, prop_carr, dig.
      rewrite (proj2 Huv2), Hr2.
      replace (carry v (i + s + 2)) with 1; [ easy | symmetry ].
      specialize (Hv2 (S s)) as H1.
      destruct H1 as (t & Hjt & Ht).
      replace (i + S s + t + 2) with (i + s + t + 3) in Ht by flia.
      now apply (Hcs _ t).
    }
    rewrite (proj1 Huv2), Nat.add_0_l.
    unfold P, d2n, prop_carr, dig.
    rewrite (proj2 Huv2), Hr2, Nat_mod_add_same_l; [ | easy ].
    replace (carry v (i + s + 2)) with 1; [ easy | symmetry ].
    specialize (Hv2 (S s)) as H1.
    destruct H1 as (t & Hjt & Ht).
    replace (i + S s + t + 2) with (i + s + t + 3) in Ht by flia.
    now apply (Hcs _ t).
  }
  destruct Hv2 as (q & Hjq & Hq).
  assert (H : ∀ j, j < p → v (i + j + 2) = 1). {
    intros s Hs.
    specialize (Hjp _ Hs).
    now apply Nat.eqb_eq in Hjp.
  }
  move H before Hjp; clear Hjp; rename H into Hjp.
  destruct (LPO_fst (λ s, v (i + q + s + 2) =? 1)) as [H1| H1]; [ | easy ].
  clear Hq.
  assert (H : ∀ k, v (i + q + k + 2) = 1). {
    intros s; specialize (H1 s).
    now apply Nat.eqb_eq in H1.
  }
  clear H1; rename H into Hq.
  assert (H : ∀ j, j < q → ∃ s, v (i + j + s + 2) = 2). {
    intros t Htq.
    specialize (Hjq t Htq) as H1.
    destruct (LPO_fst (λ s, v (i + t + s + 2) =? 1)) as [H2| H2]; [ easy | ].
    clear H1.
    destruct H2 as (s & Hjs & Hs).
    exists s.
    apply Nat.eqb_neq in Hs.
    specialize (Huvn (t + s)) as H1.
    specialize (Hu (t + s + 2)) as H2.
    rewrite Nat.add_assoc in H1.
    do 2 rewrite Nat.add_assoc in H2.
    unfold "⊕" in H1.
    flia Hs H1 H2.
  }
  move H before Hjq; clear Hjq; rename H into Hjq.
  (*         p+2  q+2
             |    |
     v=0111112...21111..., then u=0111110...01111... and
    Pv=0000001...01111... then u+Pv=0111111...02222...,
    then resolved by A_9_8_all_18 *)
  destruct q. {
    rewrite Nat.add_0_r in Hq; clear Hjq.
    now rewrite Hq in Hp.
  }
  specialize (Hjq q (Nat.lt_succ_diag_r _)) as H1.
  destruct H1 as (s, Hs).
  destruct s. 2: {
    replace (i + q + S s + 2) with (i + S q + s + 2) in Hs by flia.
    now rewrite Hq in Hs.
  }
  rewrite Nat.add_0_r in Hs.
  rename Hs into Hvq2.
  assert (Hvq1 : ∀ j, j < q → v (i + j + 2) = 1 ∨ v (i + j + 2) = 2). {
    intros s Hs.
    specialize (Huvn s) as H1.
    apply Nat_eq_add_2 in H1.
    destruct H1 as [H1| H1]. {
      specialize (Hu (s + 2)); rewrite Nat.add_assoc in Hu; flia Hu H1.
    }
    destruct H1 as [H1| H1]; [ now left | now right ].
  }
  move Hvq2 after Hvq1.
  rewrite (A_9_8_all_18 (q + 1)); cycle 1. {
    intros t Ht; rewrite Hr2.
    destruct t. {
      clear Ht.
      rewrite Nat.add_0_r.
      apply Nat.eq_add_0 in Huv1.
      unfold "⊕", P, d2n, prop_carr, dig.
      rewrite (proj1 Huv1), (proj2 Huv1), Hr2.
      replace (carry v (i + 1)) with 1; [ easy | symmetry ].
      clear - Hr2 Hv Hvq1 Hvq2.
      specialize (rad_2_all_12_2_carry_1 q v i Hr2 Hv Hvq1 Hvq2 0) as H1.
      specialize (H1 (Nat.le_0_l _)) as H1.
      now rewrite Nat.add_0_r in H1.
    }
    replace (i + S t + 1) with (i + t + 2) by flia.
    unfold "⊕", P, d2n, prop_carr, dig.
    specialize (Huvn t) as H1.
    apply Nat_eq_add_2 in H1.
    destruct H1 as [H1| H1]. {
      specialize (Hu (t + 2)); rewrite Nat.add_assoc in Hu; flia Hu H1.
    }
    replace (carry v (i + t + 2)) with 1. 2: {
      symmetry.
      assert (Htq : t < q) by flia Ht; clear Ht.
      specialize (rad_2_all_12_2_carry_1 q v i Hr2 Hv Hvq1 Hvq2 (S t)) as H2.
      assert (H : S t ≤ q) by flia Htq.
      specialize (H2 H); clear H.
      now replace (i + S t + 1) with (i + t + 2) in H2 by flia.
    }
    now destruct H1 as [H1| H1]; rewrite (proj1 H1), (proj2 H1); rewrite Hr2.
  } {
    rewrite Hr2.
    specialize (Huvn q) as H1.
    replace (i + (q + 1) + 1) with (i + q + 2) by flia.
    unfold "⊕" in H1 |-*.
    replace (u (i + q + 2)) with 0 by flia Hvq2 H1.
    rewrite Nat.add_0_l.
    unfold P, d2n, prop_carr, dig.
    rewrite Hvq2, Hr2, Nat_mod_add_same_l; [ | easy ].
    replace (carry v (i + q + 2)) with 0; [ easy | symmetry ].
    unfold carry.
    apply Q.intg_small.
    split; [ easy | ].
    rewrite A_all_9. 2: {
      intros t Ht.
      replace (i + q + 2 + t + 1) with (i + S q + t + 2) by flia.
      now rewrite Hr2.
    }
    apply Q.sub_lt, Q.lt_0_pair; pauto.
  } {
    intros s; rewrite Hr2.
    specialize (Hq s) as H1.
    specialize (Huvn (q + s + 1)) as H2.
    remember (i + q + s + 3) as t eqn:Ht.
    replace (i + S q + s + 2) with t in H1 by flia Ht.
    replace (i + (q + s + 1) + 2) with t in H2 by flia Ht.
    replace (i + (q + 1) + s + 2) with t by flia Ht.
    unfold "⊕" in H2 |-*.
    unfold P, d2n, prop_carr, dig.
    rewrite H1, Hr2; replace (u t) with 1 by flia H1 H2.
    replace (2 * (2 - 1)) with (1 + 1) by easy; f_equal.
    replace (carry v t) with 0; [ easy | symmetry ].
    unfold carry.
    apply Q.intg_small; split; [ easy | ].
    rewrite A_all_9. 2: {
      intros x Hx.
      rewrite Ht, Hr2.
      replace (i + q + s + 3 + x + 1) with (i + S q + S (x + s) + 2) by flia.
      apply Hq.
    }
    apply Q.sub_lt, Q.lt_0_pair; pauto.
  }
  apply Q.sub_lt, Q.lt_0_pair.
  destruct (le_dec (i + (q + 1) + 1) (nk - 1)); pauto.
}
destruct H1 as (q & Hjq & Huv2).
destruct Huv2 as [Huv2| Huv2]; [ now apply (rad_2_sum_3_0_222_1_A_lt_1 q) | ].
(*
     u 0 . . . . 1 . . . .
     v 0 . . . . 2 . . . .
   u+v 0 2 2 2 2 3 . . . .
    Pv . . . . . . . . . .
  u+Pv . . . . . . . . . .
*)
assert (Hcq2 : carry (u ⊕ v) (i + q + 2) = 0). {
  specialize (all_fA_ge_1_ε_P_999 _ i Hauv (q + 1)) as H1.
  replace (i + (q + 1) + 1) with (i + q + 2) in H1 by flia.
  unfold P, d2n, prop_carr, dig in H1.
  rewrite Huv2, Hr2 in H1.
  remember (carry (u ⊕ v) (i + q + 2)) as c eqn:Hc; symmetry in Hc.
  destruct c; [ easy | exfalso ].
  destruct c; [ easy | ].
  destruct c. 2: {
    specialize (carry_upper_bound_for_adds 3 (u ⊕ v) i) as H2.
    specialize (H2 (Nat.neq_succ_0 _)) as H2.
    assert (H : ∀ k, (u ⊕ v) (i + k + 1) ≤ 3 * (rad - 1)). {
      now intros; rewrite Hr2, <- Nat.add_assoc.
    }
    specialize (H2 H (q + 2)); clear H.
    rewrite Nat.add_assoc in H2; flia Hc H2.
  }
  clear H1.
  assert (Hc1 : carry (u ⊕ v) (i + q + 1) = 2). {
    rewrite (carry_succ 3); cycle 1. {
      rewrite Hr2.
      apply (Nat.lt_le_trans _ (2 ^ 2)); [ pauto | ].
      apply Nat.pow_le_mono_r; [ easy | ].
      destruct (i + q); cbn; [ pauto | flia ].
    } {
      now intros; do 2 rewrite <- Nat.add_assoc; rewrite Hr2.
    }
    replace (i + q + 1 + 1) with (i + q + 2) by flia.
    now rewrite Huv2, Hc, Hr2.
  }
  specialize (all_fA_ge_1_ε_P_999 _ i Hauv q) as H1.
  unfold P, d2n, prop_carr, dig in H1.
  rewrite Hc1, Hr2, Nat_mod_add_same_r in H1; [ | easy ].
  destruct q; [ now rewrite Nat.add_0_r, Huv1 in H1 | ].
  replace (i + S q + 1) with (i + q + 2) in H1 by flia.
  rewrite Hjq in H1; [ easy | pauto ].
}
assert (Hcuv3_lt_2 : (u ⊕ v) (i + q + 3) < 2). {
  apply Nat.nle_gt; intros H.
  rewrite (carry_succ 3) in Hcq2; cycle 1. {
    rewrite Hr2.
    apply (Nat.lt_le_trans _ (2 ^ 2)); [ pauto | ].
    apply Nat.pow_le_mono_r; [ easy | ].
    destruct (i + q); cbn; [ pauto | flia ].
  } {
    now intros; do 2 rewrite <- Nat.add_assoc; rewrite Hr2.
  }
  replace (i + q + 2 + 1) with (i + q + 3) in Hcq2 by flia.
  remember ((u ⊕ v) (i + q + 3)) as uv eqn:Huv.
  replace uv with (2 + (uv - 2)) in Hcq2 by flia H.
  now rewrite Hr2, <- Nat.add_assoc, Nat_div_add_same_l in Hcq2.
}
assert (Hpv1 : P v (i + 1) = 1). {
  unfold P, d2n, prop_carr, dig.
  apply Nat.eq_add_0 in Huv1.
  rewrite (proj2 Huv1), Nat.add_0_l, Hr2.
  replace (carry v (i + 1)) with 1; [ easy | symmetry ].
  replace (i + 1) with (i + 0 + 1) by flia.
  apply (rad_2_all_12_2_carry_1 q); try easy; [ | | flia ]. {
    intros p Hp.
    specialize (Hjq _ Hp) as H1.
    apply Nat_eq_add_2 in H1.
    destruct H1 as [H1| H1]. {
      specialize (Hu (p + 2)); rewrite Nat.add_assoc in Hu; flia Hu H1.
    }
    destruct H1; [ now left | now right ].
  }
  unfold "⊕" in Huv2.
  specialize (Hu (q + 2)) as H1.
  specialize (Hv (q + 2)) as H2.
  rewrite Nat.add_assoc in H1, H2.
  flia H1 H2 Huv2.
}
move Hpv1 before Huv1.
rewrite A_split_first; [ | rewrite Hnk; min_n_ge ].
replace (S i) with (i + 1) by flia.
unfold "⊕" at 1.
apply Nat.eq_add_0 in Huv1.
rewrite (proj1 Huv1), Hpv1, Hr2, Nat.add_0_l.
apply Q.lt_add_lt_sub_l.
replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
apply Q.mul_lt_mono_pos_r; [ easy | ].
assert (Huvq2 : u (i + q + 2) = 1 ∧ v (i + q + 2) = 2). {
  unfold "⊕" in Huv2.
  specialize (Hu (q + 2)) as H1.
  specialize (Hv (q + 2)) as H2.
  rewrite Nat.add_assoc in H1, H2.
  flia Huv2 H1 H2.
}
move Huvq2 before Huv2.
assert (Hc2 : ∀ p, p < q → carry v (i + p + 2) = 1). {
  intros p Hp.
  replace (i + p + 2) with (i + (p + 1) + 1) by flia.
  apply (rad_2_all_12_2_carry_1 q); try easy; [ | flia Hp ].
  intros s Hs.
  specialize (Hjq _ Hs) as H1.
  apply Nat_eq_add_2 in H1.
  destruct H1 as [H1| H1]. {
    specialize (Hu (s + 2)); rewrite Nat.add_assoc in Hu; flia Hu H1.
  }
  destruct H1 as [H1| H1]; [ now left | now right ].
}
move Hc2 after Hcq2.
assert (Hupv : ∀ p, p < q → (u ⊕ P v) (i + p + 2) = 1). {
  intros p Hp.
  specialize (Hjq _ Hp) as H1.
  unfold "⊕", P, d2n, prop_carr, dig; rewrite Hr2.
  rewrite Hc2; [ | easy ].
  apply Nat_eq_add_2 in H1.
  destruct H1 as [H1| H1]. {
    specialize (Hu (p + 2)); rewrite Nat.add_assoc in Hu; flia Hu H1.
  }
  now destruct H1 as [H1| H1]; rewrite (proj1 H1), (proj2 H1).
}
assert (Hcvq2 : carry v (i + q + 2) = 0). {
  unfold carry in Hcq2 |-*.
  apply Q.intg_small.
  split; [ easy | ].
  rewrite (all_fA_ge_1_ε_NQintg_A' 3) in Hcq2; cycle 1. {
    rewrite Hr2.
    apply (Nat.lt_le_trans _ (2 ^ 2)); [ pauto | ].
    apply Nat.pow_le_mono_r; [ easy | ].
    destruct (i + q); cbn; [ pauto | flia ].
  } {
    now intros; do 2 rewrite <- Nat.add_assoc; rewrite Hr2.
  } {
    intros; rewrite <- Nat.add_assoc.
    apply A_ge_1_add_r_true_if, Hauv.
  }
  replace (i + q + 2) with (i + q + 2 + 0) in Hcq2 at 2 by easy.
  remember (carry_cases v (i + q + 2)) as ccv eqn:Hccv.
  rewrite <- (all_fA_ge_1_ε_NQintg_A 3) with (l := rad * ccv)
    in Hcq2; cycle 1. {
    rewrite Hr2.
    apply (Nat.lt_le_trans _ (2 ^ 2)); [ pauto | ].
    apply Nat.pow_le_mono_r; [ easy | ].
    destruct (i + q); cbn; [ pauto | flia ].
  } {
    now intros; do 2 rewrite <- Nat.add_assoc; rewrite Hr2.
  } {
    intros; rewrite <- Nat.add_assoc.
    apply A_ge_1_add_r_true_if, Hauv.
  }
  rewrite Nat.add_0_r in Hcq2.
  rewrite <- min_n_add in Hcq2.
  apply Q.eq_intg_0 in Hcq2; [ | easy ].
  rewrite A_split_first, Hr2; [ | min_n_ge ].
  rewrite A_split_first, Hr2 in Hcq2; [ | min_n_ge ].
  replace (S (i + q + 2)) with (i + q + 3) in Hcq2 |-* by easy.
  remember ((u ⊕ v) (i + q + 3)) as uv eqn:Huv; symmetry in Huv.
  destruct uv. {
    apply Nat.eq_add_0 in Huv.
    rewrite (proj2 Huv), Q.add_0_l.
    apply rad_2_sum_2_half_A_lt_1; [ easy | ].
    now intros p; do 2 rewrite <- Nat.add_assoc.
  }
  destruct uv; [ | flia Hcuv3_lt_2 ].
  apply Nat.eq_add_1 in Huv.
  destruct Huv as [Huv| Huv]; rewrite (proj2 Huv). {
    rewrite Q.add_0_l.
    apply rad_2_sum_2_half_A_lt_1; [ easy | ].
    now intros p; do 2 rewrite <- Nat.add_assoc.
  }
  move Hcq2 at bottom.
  apply Q.lt_add_lt_sub_l in Hcq2.
  apply Q.lt_add_lt_sub_l.
  replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q in Hcq2 |-* by easy.
  apply Q.mul_lt_mono_pos_r in Hcq2; [ | easy ].
  apply Q.mul_lt_mono_pos_r; [ easy | ].
  rewrite A_additive in Hcq2.
  eapply Q.le_lt_trans; [ | apply Hcq2 ].
  now apply Q.le_add_l.
}
assert (Hpvq2 : P v (i + q + 2) = 0). {
  unfold P, d2n, prop_carr, dig.
  now rewrite (proj2 Huvq2), Hcvq2, Hr2, Nat_mod_add_same_l.
}
enough (H : (A (i + q + 2) nk (u ⊕ P v) < 1)%Q). {
  assert (H1 : ∀ p, p ≤ q → (u ⊕ P v) (i + p + 2) = 1). {
    intros p Hp.
    destruct (Nat.eq_dec p q) as [Hpq| Hpq]. {
      rewrite Hpq.
      now unfold "⊕"; rewrite (proj1 Huvq2), Hpvq2.
    }
    apply Hupv; flia Hp Hpq.
  }
  clear - q H Hr2 H1.
  revert i H1 H.
  induction q; intros. {
    specialize (H1 0 (Nat.le_refl _)) as H2.
    rewrite Nat.add_0_r in H, H2.
    destruct (lt_dec (nk - 1) (i + 1 + 1)) as [Hin| Hin]. {
      now unfold A; rewrite summation_empty.
    }
    apply Nat.nlt_ge in Hin.
    rewrite A_split_first, Hr2; [ | easy ].
    replace (S (i + 1)) with (i + 2) by easy.
    rewrite H2.
    apply Q.lt_add_lt_sub_l.
    replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
    now apply Q.mul_lt_mono_pos_r.
  }
  destruct (lt_dec (nk - 1) (i + 1 + 1)) as [Hin| Hin]. {
    now unfold A; rewrite summation_empty.
  }
  apply Nat.nlt_ge in Hin.
  rewrite A_split_first, Hr2; [ | easy ].
  replace (S (i + 1)) with (i + 0 + 2) at 1 by flia.
  rewrite H1; [ | flia ].
  apply Q.lt_add_lt_sub_l.
  replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
  apply Q.mul_lt_mono_pos_r; [ easy | ].
  replace (S (i + 1)) with (i + 1 + 1) by flia.
  replace (i + S q + 2) with (i + 1 + q + 2) in H by flia.
  apply IHq; [ | easy ].
  intros p Hp.
  rewrite <- (Nat.add_assoc i).
  apply H1; flia Hp.
}
remember (i + q + 3) as p eqn:Hp.
assert (Huvq3 : (u ⊕ v) p = 0 ∨ (u ⊕ v) p = 1) by flia Hcuv3_lt_2.
subst p; clear Hcuv3_lt_2.
remember (i + q + 1) as ii.
replace (i + q + 2) with (ii + 1) in * by flia Heqii.
replace (i + q + 3) with (ii + 2) in * by flia Heqii.
assert (H : ∀ k, u (ii + k) ≤ 1). {
  now intros; rewrite Heqii; do 2 rewrite <- Nat.add_assoc.
}
move H before Hu; clear Hu; rename H into Hu.
assert (H : ∀ k, v (ii + k) ≤ 2). {
  now intros; rewrite Heqii; do 2 rewrite <- Nat.add_assoc.
}
move H before Hv; clear Hv; rename H into Hv.
assert (H : ∀ k, fA_ge_1_ε (u ⊕ v) ii k = true). {
  intros; rewrite Heqii, <- Nat.add_assoc.
  now apply A_ge_1_add_r_true_if.
}
move H before Hauv; clear Hauv; rename H into Hauv.
clear n Hn.
clear i j k Hjj Hj Hjk Hk Huv1 Hpv1 Hnj Hnk Huvl3 Hjq Heqii Hc2 Hupv.
rename ii into i.
move Huvq3 before Huvq2.
rename Huv2 into Huv1.
rename Huvq3 into Huv2.
move Huv2 before Huv1.
rename Hcq2 into Hcuv1.
rename Hcvq2 into Hcv1.
rename Hpvq2 into Hpv1.
rename Huvq2 into Huv11.
clear nj q; rename nk into n.
...

Theorem pre_Hugo_Herbelin_82 {r : radix} : ∀ u v i j k,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → (∀ j0, j0 < j → fA_ge_1_ε v i j0 = true)
  → fA_ge_1_ε v i j = false
  → (∀ j, j < k → fA_ge_1_ε (u ⊕ P v) i j = true)
  → fA_ge_1_ε (u ⊕ P v) i k = false
  → (∀ k, fA_ge_1_ε (u ⊕ v) i k = true)
  → Q.intg (A i (min_n (i + j)) v) ≤ 1
  → Q.intg (A i (min_n i) v) ≤ 1
  → (A i (min_n i) u + Q.frac (A i (min_n i) v) < 1)%Q
  → (1 ≤ A i (min_n (i + k)) u + A i (min_n (i + k)) (P v))%Q
  → Q.intg (A i (min_n i) v) = (Q.intg (A i (min_n (i + j)) v) + 1) mod rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hjj Hj Hjk Hk Hauv Haj Ha0 Huv Hup.
remember (min_n i) as n eqn:Hn.
remember (min_n (i + j)) as nj eqn:Hnj.
remember (min_n (i + k)) as nk eqn:Hnk.
move n before k; move nj before n; move nk before nj.
move nk before nj; move Hnk before Hnj; move Hn after Hnj.
assert
  (Hiv : ∀ p, j ≤ p → Q.intg (A i (min_n (i + p)) v) = Q.intg (A i nj v)). {
  specialize (fA_lt_1_ε_NQintg_A 2 i v j) as H1.
  assert (H : 2 < rad ^ (min_n (i + j) - i - j - 2)). {
    apply (le_lt_trans _ 3); [ pauto | ].
    unfold min_n; do 2 rewrite <- Nat.sub_add_distr.
    rewrite Nat.add_assoc.
    apply three_lt_rad_pow.
  }
  specialize (H1 H Hv Hjj Hj); clear H.
  now rewrite Hnj.
}
generalize Hk; intros HHHHHHk.
assert
  (Hiup : ∀ p, k ≤ p
   → Q.intg (A i (min_n (i + p)) (u ⊕ P v)) = Q.intg (A i nk (u ⊕ P v))). {
  specialize (fA_lt_1_ε_NQintg_A 2 i (u ⊕ P v) k) as H1.
  assert (H : 2 < rad ^ (min_n (i + k) - i - k - 2)). {
    apply (le_lt_trans _ 3); [ pauto | ].
    unfold min_n; do 2 rewrite <- Nat.sub_add_distr.
    rewrite Nat.add_assoc.
    apply three_lt_rad_pow.
  }
  specialize (H1 H); clear H.
  assert (H : ∀ k, (u ⊕ P v) (i + k) ≤ 2 * (rad - 1)). {
    intros p; unfold "⊕".
    replace 2 with (1 + 1) by easy.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
    apply Nat.add_le_mono; [ easy | ].
    apply P_le.
  }
  specialize (H1 H Hjk Hk); clear H.
  now rewrite Hnk.
}
assert
  (Hiuv :
  ∀ p, Q.intg (A i (min_n (i + p)) (u ⊕ v)) = Q.intg (A i n (u ⊕ v))). {
  specialize (all_fA_ge_1_ε_NQintg_A' 3 i (u ⊕ v)) as Hiuv.
  specialize (Hiuv (three_lt_rad_pow _)).
  assert (H : ∀ k, (u ⊕ v) (i + k) ≤ 3 * (rad - 1)). {
    intros p.
    unfold "⊕"; replace 3 with (1 + 2) by easy.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
    apply Nat.add_le_mono; [ apply Hu | apply Hv ].
  }
  specialize (Hiuv H Hauv); clear H.
  now rewrite <- Hn in Hiuv.
}
assert (HAu : ∀ n, (0 ≤ A i n u < 1)%Q). {
  intros m.
  split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros p Hp; replace p with (i + (p - i)) by flia Hp; apply Hu.
}
apply A_ge_1_false_iff in Hk; rewrite <- Hnk in Hk.
rewrite A_additive in Hk.
rewrite Q.frac_add_cond in Hk; [ | easy | easy ].
rewrite (Q.frac_small (A _ _ u)) in Hk; [ | easy ].
rewrite NQfrac_P_M in Hk.
destruct (Q.lt_le_dec (A i nk u + A i nk (P v)) 1) as [H1| H1]. {
  exfalso; rewrite Q.sub_0_r in Hk.
  apply Q.nle_gt in Hk; apply Hk; clear Hk.
  eapply Q.le_trans; [ | apply Hup ].
  now apply Q.le_sub_l.
}
clear H1.
move Hk after Hup.
specialize (Hiuv k) as H2; rewrite <- Hnk in H2.
do 2 rewrite A_additive in H2.
rewrite Q.intg_add_cond in H2; [ | easy | easy ].
rewrite Q.intg_add_cond in H2; [ | easy | easy ].
rewrite (Q.intg_small (A _ _ u)) in H2; [ | easy ].
rewrite (Q.intg_small (A _ _ u)) in H2; [ | easy ].
rewrite (Q.frac_small (A _ _ u)) in H2; [ | easy ].
rewrite (Q.frac_small (A _ _ u)) in H2; [ | easy ].
do 2 rewrite Nat.add_0_l in H2.
apply Q.nle_gt in Huv.
destruct (Q.lt_le_dec (A i n u + Q.frac (A i n v)) 1) as [H3| ]; [ | easy ].
apply Q.nle_gt in Huv; clear H3; rewrite Nat.add_0_r in H2.
specialize (Hiuv j) as H3; rewrite <- Hnj in H3.
do 2 rewrite A_additive in H3.
rewrite Q.intg_add_cond in H3; [ | easy | easy ].
rewrite Q.intg_add_cond in H3; [ | easy | easy ].
rewrite (Q.intg_small (A _ _ u)) in H3; [ | easy ].
rewrite (Q.intg_small (A _ _ u)) in H3; [ | easy ].
rewrite (Q.frac_small (A _ _ u)) in H3; [ | easy ].
rewrite (Q.frac_small (A _ _ u)) in H3; [ | easy ].
do 2 rewrite Nat.add_0_l in H3.
apply Q.nle_gt in Huv.
destruct (Q.lt_le_dec (A i n u + Q.frac (A i n v)) 1) as [H4| ]; [ | easy ].
apply Q.nle_gt in Huv; clear H4; rewrite Nat.add_0_r in H3.
destruct (Q.lt_le_dec (A i nj u + Q.frac (A i nj v)) 1) as [H4| H4]. 2: {
  rewrite H3, Nat.mod_small; [ easy | ].
  destruct (zerop (Q.intg (A i n v))) as [Hiv0| Hiv0].
  -now rewrite Hiv0.
  -now replace (Q.intg (A i n v)) with 1 by flia Ha0 Hiv0.
}
exfalso; rewrite Nat.add_0_r in H3.
clear Haj; move H4 after Huv.
destruct (Q.lt_le_dec (A i nk u + Q.frac (A i nk v)) 1) as [H5| H5].
-rewrite Nat.add_0_r in H2; move H5 before H4.
 destruct (zerop (Q.intg (A i n v))) as [Hzn| Hzn]. {
   rewrite Hzn in H2, H3; clear Ha0.
   rewrite Q.frac_small in H4; [ | split; [ easy | now apply Q.eq_intg_0 ] ].
   rewrite Q.frac_small in H5; [ | split; [ easy | now apply Q.eq_intg_0 ] ].
   rewrite Q.frac_small in Huv; [ | split; [ easy | now apply Q.eq_intg_0 ] ].
   assert (Huvl3 : ∀ k, (u ⊕ v) (i + k) ≤ 3 * (rad - 1)). {
     intros p.
     unfold "⊕"; replace 3 with (1 + 2) by easy.
     rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
     apply Nat.add_le_mono; [ apply Hu | apply Hv ].
   }
   assert (Hianuv : Q.intg (A i n (u ⊕ v)) = 0). {
     apply Q.intg_small.
     split; [ easy | ].
     now rewrite A_additive.
   }
   assert (Hiauv : ∀ p, Q.intg (A i (min_n (i + p)) (u ⊕ v)) = 0). {
     now intros; rewrite Hiuv.
   }
   clear Hiuv.
   assert (Hiau : ∀ p, Q.intg (A i (min_n (i + p)) u) = 0). {
     intros.
     specialize (Hiauv p); rewrite A_additive in Hiauv.
     rewrite Q.intg_add in Hiauv; [ | easy | easy ].
     apply Nat.eq_add_0 in Hiauv.
     destruct Hiauv as (H, _).
     now apply Nat.eq_add_0 in H.
   }
   assert (Hiav : ∀ p, Q.intg (A i (min_n (i + p)) v) = 0). {
     intros.
     specialize (Hiauv p); rewrite A_additive in Hiauv.
     rewrite Q.intg_add in Hiauv; [ | easy | easy ].
     apply Nat.eq_add_0 in Hiauv.
     destruct Hiauv as (H, _).
     now apply Nat.eq_add_0 in H.
   }
   clear H2 H3 Hzn Hianuv H4 H5 Huv Hiv.
   assert
     (Huv789 :
        (u ⊕ v) (i + 1) = rad - 3 ∨ (u ⊕ v) (i + 1) = rad - 2 ∨
        (u ⊕ v) (i + 1) = rad - 1). {
     specialize (Hiauv 0) as H1.
     apply Q.eq_intg_0 in H1; [ | easy ].
     rewrite A_split_first in H1; [ | min_n_ge ].
     replace (S i) with (i + 1) in H1 by flia.
     remember ((u ⊕ v) (i + 1)) as uvi1 eqn:Huvi1.
     symmetry in Huvi1.
     assert (H2 : uvi1 < rad). {
       apply Nat.nle_gt; intros H.
       apply Q.nle_gt in H1; apply H1; clear H1.
       eapply Q.le_trans; [ | now apply Q.le_add_r, Q.le_0_mul_r ].
       apply (Q.le_pair 1 1); [ easy | pauto | flia H ].
     }
     specialize (P_999_start (u ⊕ v) (i + 1) 3) as H3.
     assert (H : ∀ k, (u ⊕ v) (i + 1 + k) ≤ 3 * (rad - 1)). {
       intros; rewrite <- Nat.add_assoc; apply Huvl3.
     }
     specialize (H3 H); clear H.
     assert (H : ∀ k, P (u ⊕ v) (i + 1 + k) = rad - 1). {
       specialize (all_fA_ge_1_ε_P_999 _ _ Hauv) as H.
       intros; rewrite Nat.add_shuffle0; apply H.
     }
     specialize (H3 H); clear H.
     rewrite Huvi1 in H3.
     destruct (lt_dec rad 3) as [H| Hr3]; [ flia H2 H | ].
     apply Nat.nlt_ge in Hr3.
     destruct (Nat.eq_dec uvi1 (3 * (rad - 1))) as [H4| H4]; [ flia H2 H4 | ].
     remember (uvi1 / rad + 1) as j1 eqn:Hj1.
     remember (carry (u ⊕ v) (i + 1) + 1) as c1 eqn:Hc1.
     cbn in H3.
     destruct H3 as (H3 & H5 & H6).
     destruct (Nat.eq_dec j1 1) as [H7| H7]. {
       move H7 at top; subst j1; clear H3.
       rewrite Nat.mul_1_l in H6.
       destruct (Nat.eq_dec c1 1) as [H3| H3]. {
         now rewrite H3 in H6; right; right.
       }
       destruct (Nat.eq_dec c1 2) as [H7| H7]. {
         now rewrite H7 in H6; right; left.
       }
       destruct (Nat.eq_dec c1 3) as [H8| H8]. {
         now rewrite H8 in H6; left.
       }
       flia H5 H3 H7 H8.
     }
     destruct (Nat.eq_dec j1 2) as [H8| H8]. {
       now rewrite H8, Nat.div_small in Hj1.
     }
     flia H3 H7 H8.
   }
   destruct Huv789 as [Huv1| Huv1]. {
     destruct (Nat.eq_dec rad 2) as [Hr2| Hr2]. {
       apply Q.nlt_ge in Hup; apply Hup; clear Hup.
       rewrite <- A_additive, Hnk.
       rewrite Hr2 in Hu, Hv, Huv1.
...
       now apply (pre_Hugo_Herbelin_82_rad_2_lemma_1 _ _ _ j).
     }
     (* ce qui suit est correct, mais faut le finir *)
     assert (Huv2 : ∀ p, (u ⊕ v) (i + p + 2) = 3 * (rad - 1)). {
       intros p.
       replace rad with (1 * rad) in Huv7 by flia.
       apply P_999_after_7 with (j0 := 1); try easy; [ | pauto ].
       flia Hr Hr2.
     }
     assert (Hv2 : ∀ p, v (i + p + 2) = 2 * (rad - 1)). {
       intros p; specialize (Huv2 p) as H1.
       unfold "⊕" in H1.
       replace 3 with (1 + 2) in H1 by easy.
       rewrite Nat.mul_add_distr_r, Nat.mul_1_l in H1.
...
       specialize (Hu (p + 2)) as H2; rewrite Nat.add_assoc in H2.
       specialize (Hv (p + 2)) as H3; rewrite Nat.add_assoc in H3.
       flia H1 H2 H3.
     }
...
   destruct (lt_dec rad 3) as [H| Hr3]. {
     assert (Hr2 : rad = 2) by flia H Hr; clear H H1.
     rewrite Hr2 in Hu, Hv, Hk; cbn in Hu, Hv.
     destruct (Nat.eq_dec ((u ⊕ v) (i + 1)) 0) as [Huv0| Huv0]. {
       destruct (Nat.eq_dec ((u ⊕ v) (i + 2)) 0) as [Huv20| Huv20]. {
         revert Huv20.
         now apply rad_2_sum_3_all_9_not_0_0.
       }
       destruct (Nat.eq_dec ((u ⊕ v) (i + 2)) 1) as [Huv21| Huv21]. {
         apply Q.nlt_ge in Hup; apply Hup; clear Hup.
         rewrite <- A_additive; subst nk.
         now apply rad_2_sum_3_all_9_0_1_A_lt_1.
       }
       destruct (Nat.eq_dec ((u ⊕ v) (i + 2)) 2) as [Huv22| Huv22]. {
         clear Huv20 Huv21.
         remember (u ⊕ v) as w eqn:Hw.
         specialize (rad_2_sum_3_all_9_2_123 w (i + 1) Hr2) as H.
         replace (i + 1 + 1) with (i + 2) in H by flia.
         replace (i + 1 + 2) with (i + 3) in H by flia.
         assert (H' : ∀ k, w (i + 1 + k + 1) ≤ 3 * (rad - 1)). {
           now intros; do 2 rewrite <- Nat.add_assoc.
         }
         specialize (H H'); clear H'.
         assert (H' : ∀ k, fA_ge_1_ε w (i + 1) k = true). {
           now intros; apply A_ge_1_add_r_true_if.
         }
         specialize (H H' Huv22); clear H'.
         destruct H as [Huv31| [Huv32| Huv33]].
         -apply Q.nlt_ge in Hup; apply Hup; clear Hup.
          rewrite <- A_additive; subst nk.
          rewrite Hw in Huv0, Huv22, Huv31.
          apply rad_2_sum_3_0213_A_lt_1; try easy.
          specialize (rad_2_sum_3_all_9_02_1_3 (u ⊕ v) (i + 1) Hr2) as H1.
          replace (i + 1 + 1) with (i + 2) in H1 by flia.
          replace (i + 1 + 2) with (i + 3) in H1 by flia.
          replace (i + 1 + 3) with (i + 4) in H1 by flia.
          apply H1; [ | | now right | easy ]. {
            now intros; rewrite <- Nat.add_assoc, <- Hw.
          }
          intros p; rewrite <- Hw.
          now apply A_ge_1_add_r_true_if.
         -specialize (rad_2_sum_3_all_9_2_123 w (i + 2) Hr2) as H1.
          replace (i + 2 + 1) with (i + 3) in H1 by flia.
          replace (i + 2 + 2) with (i + 4) in H1 by flia.
          assert (H : ∀ k, w (i + 2 + k + 1) ≤ 3 * (rad - 1)). {
            now intros; do 2 rewrite <- Nat.add_assoc.
          }
          specialize (H1 H); clear H.
          assert (H : ∀ k, fA_ge_1_ε w (i + 2) k = true). {
            now intros; apply A_ge_1_add_r_true_if.
          }
          specialize (H1 H Huv32); clear H.
          destruct H1 as [Huv4| Huv4]. {
            apply Q.nlt_ge in Hup; apply Hup; clear Hup.
            rewrite <- A_additive; subst nk.
            rewrite Hw in Huv0, Huv22, Huv32, Huv4.
            rewrite A_split_first; [ | min_n_ge ].
            replace (S i) with (i + 1) by flia.
            apply Nat.eq_add_0 in Huv0.
            unfold "⊕" at 1; rewrite (proj1 Huv0), Nat.add_0_l.
            apply Q.lt_add_lt_sub_l.
            remember (P v (i + 1)) as p1 eqn:Hp1; symmetry in Hp1.
            destruct p1. {
              rewrite Q.sub_0_r, Hr2.
              apply rad_2_sum_2_half_A_lt_1; [ easy | ].
              intros p; rewrite <- Nat.add_assoc; unfold "⊕".
              replace 2 with (1 + 1) by easy.
              apply Nat.add_le_mono; [ apply Hu | ].
              replace 1 with (rad - 1) by flia Hr2.
              apply P_le.
            }
            destruct p1. {
              rewrite Hr2.
              replace (1 - 1 // 2)%Q with (1 * 1 // 2)%Q by easy.
              apply Q.mul_lt_mono_pos_r; [ easy | ].
              unfold P, d2n, prop_carr, dig in Hp1.
              rewrite (proj2 Huv0), Nat.add_0_l in Hp1.
              rewrite Nat.mod_small in Hp1. 2: {
                specialize (carry_upper_bound_for_add v (i + 1)) as H1.
                assert (H : ∀ k, v (i + 1 + k + 1) ≤ 2 * (rad - 1)). {
                  now intros; rewrite Hr2; do 2 rewrite <- Nat.add_assoc.
                }
                specialize (H1 H); clear H.
                flia H1 Hr2.
              }
              unfold carry in Hp1.
              apply Q.intg_interv in Hp1; [ | easy ].
              apply Nat_eq_add_2 in Huv22.
              destruct Huv22 as [Huv22| Huv22]. {
                rewrite A_split_first in Hp1; [ | min_n_ge ].
                replace (S (i + 1)) with (i + 2) in Hp1 by flia.
                rewrite (proj2 Huv22), Q.add_0_l in Hp1.
                destruct Hp1 as (Hp1, _).
                apply Q.nlt_ge in Hp1.
                exfalso; apply Hp1; clear Hp1.
                rewrite Hr2.
                apply rad_2_sum_2_half_A_lt_1; [ easy | ].
                now intros; rewrite <- Nat.add_assoc.
              }
              destruct Huv22 as [Huv22| Huv22]. {
                rewrite A_split_first; [ | min_n_ge ].
                replace (S (i + 1)) with (i + 2) by flia.
                unfold "⊕" at 1.
                rewrite (proj1 Huv22).
...
induction p. {
  rewrite Nat.add_0_r.
  apply rad_2_sum_3_all_9_02_1_3; try easy; now left.
}
clear - Hr2 Hu3r IHp Hau.
replace (i + S p + 3) with (i + (p + 2) + 2) by flia.
replace (i + S p + 2) with (i + (p + 2) + 1) by flia.
replace (i + p + 3) with (i + (p + 2) + 1) in IHp by flia.
replace (i + p + 2) with (i + (p + 2)) in IHp by flia.
now apply rad_2_sum_3_all_9_3r2_3r2.
...
Check rad_2_sum_3_all_9_02_1_3.
Check rad_2_sum_3_all_9_0_123.
Check rad_2_sum_3_all_9_not_0_0.
Check rad_2_sum_3_all_9_0_1_333.
Check rad_2_sum_3_all_9_3r2_3r2.
Check rad_2_sum_3_all_9_0_1_A_lt_1.
...
rewrite (proj2 H1), Nat.add_0_l in Hpv.
unfold carry in Hx.
specialize (Huv33 0) as H6.
rewrite Nat.add_0_r in H6.
...
rewrite Q.intg_small in Hx; [ easy | ].
split; [ now apply Q.le_0_mul_r | ].
apply (Q.mul_lt_mono_pos_r 2%Q); [ easy | ].
rewrite <- Q.mul_assoc.
rewrite Q.mul_pair_den_num; [ | easy ].
rewrite Q.mul_1_r, Q.mul_1_l.
eapply Q.le_lt_trans. {
  apply (A_upper_bound_for_adds 2).
  rewrite Hr2.
  intros; do 2 rewrite <- Nat.add_assoc; apply Hv.
}
rewrite Q.mul_sub_distr_l, Q.mul_1_r.
now apply Q.sub_lt.
}
destruct x. {
...
      rewrite <- Q.pair_add_l.
      replace (2 + 1) with 3 by easy.
      eapply Q.le_lt_trans. {
...
         apply Q.nlt_ge in Hup; apply Hup; clear Hup.
         rewrite A_split_first; [ | rewrite Hnk; min_n_ge ].
         rewrite <-  Nat.add_1_r.
         replace (u (i + 1)) with 0. 2: {
           rewrite Hw in Huv0.
           unfold "⊕" in Huv0.
           now apply Nat.eq_add_0 in Huv0.
         }
         rewrite Q.add_0_l.
...
         rewrite (A_split_first _ _ (P _)); [ | rewrite Hnk; min_n_ge ].
         rewrite <- (Nat.add_1_r i).
         replace (P v (i + 1)) with 0. 2: {
           unfold P, d2n, prop_carr, dig.
           replace (v (i + 1)) with 0. 2: {
             rewrite Hw in Huv0.
             unfold "⊕" in Huv0.
             apply Nat.eq_add_0 in Huv0.
             now rewrite <-  Nat.add_1_r.
           }
           rewrite Nat.add_0_l.
unfold carry.
    rewrite (fA_lt_1_ε_NQintg_A _ _ j).
      intros p; rewrite <- Nat.add_assoc.
eapply Nat.le_trans; [ apply Hv | ].
rewrite Hr2; flia.
    } {
      intros.
      apply A_ge_1_add_r_true_if.
    }
...
         move Hj at bottom.
         apply A_ge_1_false_iff in Hj.
         (* ah bin non, chuis con, c'est faux ce que je dis plus haut *)
         (* enfin je crois *)
         (* t'façons, c'est l'heure de la sieste *)
         (* voir avec Hup, plutôt ? *)
...
         rewrite A_split_first in Hj; [ | min_n_ge ].
         replace (S i) with (i + 1) in Hj by flia.
... suite
 assert (H1 : Q.intg (A i n v) = 1) by flia Ha0 Hzn; clear Ha0 Hzn.
 rewrite H1 in H2, H3.
...
destruct (Q.lt_le_dec (A i n u + Q.frac (A i n v))) as [H| ]; [ | easy ].
clear H; rewrite Nat.add_0_r in H2.
apply Q.nle_gt in Huv.
destruct (Q.lt_le_dec (A i nj u + Q.frac (A i nj v)) 1) as [H3| H3].
-rewrite Nat.add_0_r in H2; exfalso.
 apply A_ge_1_false_iff in Hk.
 rewrite <- Hnk in Hk.
...
destruct (le_dec j k) as [Hljk| Hlkj].
-specialize (Hiv _ Hljk) as H1.
 rewrite <- Hnk in H1.
...
specialize (P_999_start (u ⊕ v) (i + 1) 3) as H1.
assert (H : ∀ k, (u ⊕ v) (i + 1 + k) ≤ 3 * (rad - 1)). {
  intros p.
  unfold "⊕"; replace 3 with (1 + 2) by easy.
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  rewrite <- Nat.add_assoc.
  apply Nat.add_le_mono; [ apply Hu | apply Hv ].
}
specialize (H1 H); clear H.
assert (H : ∀ k, P (u ⊕ v) (i + 1 + k) = rad - 1). {
  specialize (all_fA_ge_1_ε_P_999 _ _ Hauv) as H.
  intros; rewrite Nat.add_shuffle0; apply H.
}
specialize (H1 H); clear H.
...
*)

Theorem pre_Hugo_Herbelin {r : radix} : ∀ u v i,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → carry (u ⊕ v) i mod rad = (carry (u ⊕ P v) i + carry v i) mod rad.
Proof.
intros * Hu Hv.
specialize radix_ge_2 as Hr.
rewrite Nat.add_comm.
unfold carry, carry_cases.
remember
  (match LPO_fst (fA_ge_1_ε v i) with
   | inl _ => 0
   | inr (exist _ k _) => k
   end) as kv eqn:Hkv.
remember
  (match LPO_fst (fA_ge_1_ε (u ⊕ P v) i) with
   | inl _ => 0
   | inr (exist _ k _) => k
   end) as kup eqn:Hkup.
remember
  (match LPO_fst (fA_ge_1_ε (u ⊕ v) i) with
   | inl _ => 0
   | inr (exist _ k _) => k
   end) as kuv eqn:Hkuv.
move kuv before kv; move kup before kv.
remember (min_n (i + k)v) as nv eqn:Hnv.
remember (min_n (i + k)up) as nup eqn:Hnup.
remember (min_n (i + k)uv) as nuv eqn:Hnuv.
move nuv before kuv; move nup before kuv; move nv before kuv.
(*
destruct (LPO_fst (fA_ge_1_ε v i)) as [H3| H3].
-subst kv.
 assert (Hii : ∀ p, Q.intg (A i (min_n i p) v) = Q.intg (A i nv v)). {
   specialize (all_fA_ge_1_ε_NQintg_A' i v) as Hii.
   assert (H : ∀ k, v (i + k) ≤ 3 * (rad - 1)). {
     intros p.
     eapply Nat.le_trans; [ apply Hv | ].
     apply Nat.mul_le_mono_r; pauto.
   }
   specialize (Hii H H3); clear H.
   now rewrite <- Hnv in Hii.
 }
 rewrite <- (Hii kuv), <- Hnuv.
 destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [Hupv| Hupv].
 *subst kup; rewrite <- Hnv in Hnup; subst nup.
  assert (Hik : ∀ p,
    Q.intg (A i (min_n i p) (u ⊕ P v)) = Q.intg (A i nv (u ⊕ P v))). {
    specialize (all_fA_ge_1_ε_NQintg_A' i (u ⊕ P v)) as Hik.
    assert (H : ∀ k, (u ⊕ P v) (i + k) ≤ 3 * (rad - 1)). {
      intros p.
      unfold "⊕"; replace 3 with (1 + 2) by easy.
      rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
      apply Nat.add_le_mono; [ apply Hu | ].
      eapply Nat.le_trans; [ apply P_le | flia Hr ].
    }
    specialize (Hik H Hupv); clear H.
    now rewrite <- Hnv in Hik.
  }
  rewrite <- (Hik kuv), <- Hnuv.
  do 2 rewrite A_additive.
  rewrite Q.intg_add; [ symmetry | easy | easy ].
  rewrite Q.intg_add; [ symmetry | easy | easy ].
  do 2 rewrite Nat.add_assoc.
  rewrite (Nat.add_comm (Q.intg (A i nuv v))).
  do 3 rewrite <- Nat.add_assoc.
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  f_equal; f_equal.
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  f_equal; f_equal.
  assert (HA : (0 ≤ A i nuv u < 1)%Q). {
    split; [ easy | ].
    apply A_upper_bound_for_dig; intros p Hp.
    replace p with (i + (p - i)) by flia Hp.
    apply Hu.
  }
  assert (HAP : (0 ≤ A i nuv (P v) < 1)%Q). {
    split; [ easy | ].
    apply A_upper_bound_for_dig; intros p Hp.
    apply P_le.
  }
  rewrite Q.frac_small; [ | easy ].
  rewrite (Q.frac_small (A _ _ (P _))); [ | easy ].
  rewrite (Q.intg_small (A _ _ (P _))); [ | easy ].
  rewrite Nat.add_0_l.
  rewrite Q.intg_add_cond; [ symmetry | easy | easy ].
  rewrite Q.intg_add_cond; [ symmetry | easy | easy ].
  rewrite Q.intg_NQfrac, Q.frac_idemp; [ | easy ].
  rewrite (Q.intg_small (A _ _ (P _))); [ | easy ].
  rewrite (Q.frac_small (A _ _ (P _))); [ | easy ].
  rewrite Q.frac_small; [ | easy ].
  rewrite Nat.add_0_r.
  f_equal; f_equal.
  destruct (Q.lt_le_dec (A i nuv u + Q.frac (A i nuv v)) 1) as [H1| H1].
 --destruct (Q.lt_le_dec (A i nuv u + A i nuv (P v)) 1) as [| H2]; [ easy | ].
   exfalso.
   apply Q.nlt_ge in H2; apply H2; clear H2.
   rewrite (A_all_9 (P _)); [ | now intros; apply all_fA_ge_1_ε_P_999 ].
   specialize (A_ge_1_add_all_true_if v i) as H2.
   assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
     intros k; rewrite <- Nat.add_assoc; apply Hv.
   }
   specialize (H2 H H3); clear H.
   destruct H2 as [H2| [H2| H2]].
  ++rewrite (A_all_9 v) in H1; [ | intros; apply H2 ].
    rewrite Q.frac_small in H1; [ easy | ].
    split; [ | now apply Q.sub_lt ].
    apply Q.le_0_sub, Q.le_pair_mono_l.
    split; [ pauto | now apply Nat_pow_ge_1 ].
  ++rewrite (A_all_18 v) in H1; [ | intros; apply H2 ].
    rewrite Q.frac_less_small in H1. 2: {
      split; [ | now apply Q.sub_lt ].
      apply Q.le_add_le_sub_l.
      replace 2%Q with (1 + 1)%Q by easy.
      apply Q.add_le_mono_l.
      apply Q.le_pair; [ pauto | easy | ].
      apply Nat.mul_le_mono_pos_r; [ pauto | ].
      remember (nuv - i - 1) as s eqn:Hs.
      destruct s.
      -rewrite Hnuv in Hs; unfold min_n in Hs.
       destruct rad; [ easy | cbn in Hs; flia Hs ].
      -cbn.
       replace 2 with (2 * 1) by easy.
       apply Nat.mul_le_mono; [ easy | ].
       now apply Nat_pow_ge_1.
    }
    rewrite <- Q.sub_sub_swap in H1.
    replace (2 - 1)%Q with 1%Q in H1 by easy.
    remember (nuv - i - 1) as s eqn:Hs.
    destruct (Q.lt_le_dec (A i nuv u) (1 // rad ^ s)) as [H4| H4]. {
      rewrite Q.add_comm.
      rewrite <- Q.sub_sub_distr.
      now apply Q.sub_lt, Q.lt_0_sub.
    }
    exfalso.
    apply Q.nle_gt in H1; apply H1; clear H1.
    destruct (Q.le_lt_dec (2 // rad ^ s) (A i nuv u)) as [H5| H5]. {
      rewrite Q.add_comm, <- Q.add_sub_swap, <- Q.add_sub_assoc.
      now apply Q.le_add_r, Q.le_0_sub.
    }
    exfalso.
    destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [Huv| Huv].
   **subst kuv; rewrite <- Hnv in Hnuv; subst nuv.
...
     specialize (proj1 (frac_ge_if_all_fA_ge_1_ε (u ⊕ v) i) Huv 0) as H6.
     rewrite <- Hnv, Nat.pow_1_r, A_additive in H6.
     apply Q.nlt_ge in H6; apply H6; clear H6.
     rewrite <- Hnv, Nat.pow_1_r, A_additive.
     rewrite Q.frac_add_cond; [ | easy | easy ].
     rewrite Q.frac_small; [ | easy ].
     rewrite Q.frac_less_small. 2: {
       rewrite A_all_18, <- Hs; [ | easy ].
       split; [ | now apply Q.sub_lt ].
       apply Q.le_add_le_sub_r.
       replace 2%Q with (1 + 1)%Q by easy.
       apply Q.add_le_mono_r.
       apply Q.le_pair; [ pauto | easy | ].
       apply Nat.mul_le_mono_pos_r; [ pauto | ].
       destruct s.
       -rewrite Hnv in Hs; unfold min_n in Hs.
        destruct rad; [ easy | cbn in Hs; flia Hs ].
       -cbn.
        replace 2 with (2 * 1) by easy.
        apply Nat.mul_le_mono; [ easy | ].
        now apply Nat_pow_ge_1.
     }
...
     rewrite Q.add_sub_assoc.
     destruct (Q.lt_le_dec (A i nv u + A i nv v - 1)%Q 1) as [H6| H6].
   ---rewrite Q.sub_0_r.
      rewrite <- Q.add_sub_assoc.
      eapply Q.lt_le_trans; [ apply Q.add_lt_mono_r, H5 | ].
      rewrite (A_all_18 v), <- Hs; [ | easy ].
...
    destruct (Q.lt_le_dec (A i nuv u) (1 // rad ^ s)) as [H4| H4]. {
      rewrite Q.add_comm.
      rewrite <- Q.sub_sub_distr.
      now apply Q.sub_lt, Q.lt_0_sub.
    }
    exfalso.
    apply Q.nle_gt in H1; apply H1; clear H1.
    destruct (Q.le_lt_dec (2 // rad ^ s) (A i nuv u)) as [H5| H5]. {
      rewrite Q.add_comm, <- Q.add_sub_swap, <- Q.add_sub_assoc.
      now apply Q.le_add_r, Q.le_0_sub.
    }
    exfalso.
ah ouais, faut regarder en nj+1, un truc comme ça...
Search (∀ _, fA_ge_1_ε _ _ _ = true).
...
...
     assert (Hauv : ∀ p,
       Q.intg (A i (min_n i p) (u ⊕ v)) = Q.intg (A i nv (u ⊕ v))). {
       specialize (all_fA_ge_1_ε_NQintg_A' i (u ⊕ v)) as Hauv.
       assert (H : ∀ k, (u ⊕ v) (i + k) ≤ 3 * (rad - 1)). {
         intros p.
         unfold "⊕"; replace 3 with (1 + 2) by easy.
         rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
         apply Nat.add_le_mono; [ apply Hu | apply Hv ].
       }
       specialize (Hauv H Huv); clear H.
       now rewrite <- Hnv in Hauv.
     }
...
*)
do 2 rewrite A_additive.
rewrite Q.intg_add; [ symmetry | easy | easy ].
rewrite Q.intg_add; [ symmetry | easy | easy ].
do 2 rewrite Nat.add_assoc.
remember (Q.intg (A i nv v) + Q.intg (A i nup u)) as x eqn:Hx.
rewrite Nat.add_comm in Hx; subst x.
rewrite NQintg_P_M, Nat.add_0_r.
rewrite (NQintg_A_for_dig _ _ u), Nat.add_0_l. 2: {
  intros k Hk; replace k with (i + (k - i)) by flia Hk; apply Hu.
}
rewrite (NQintg_A_for_dig _ _ u), Nat.add_0_l. 2: {
  intros k Hk; replace k with (i + (k - i)) by flia Hk; apply Hu.
}
specialize (NQintg_A_le_1_for_add v i kv) as H1.
rewrite <- Hnv in H1.
specialize (NQintg_A_le_1_for_add v i kuv) as H2.
rewrite <- Hnuv in H2.
assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
  intros k; rewrite <- Nat.add_assoc; apply Hv.
}
specialize (H1 H); specialize (H2 H); clear H.
do 2 rewrite Q.intg_add_frac.
rewrite (Q.frac_small (A i nup u)). 2: {
  split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros k Hk; replace k with (i + (k - i)) by flia Hk; apply Hu.
}
rewrite (Q.frac_small (A i nuv u)). 2: {
  split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros k Hk; replace k with (i + (k - i)) by flia Hk; apply Hu.
}
rewrite NQfrac_P_M.
assert (Hv3 : ∀ k, v (i + k) ≤ 3 * (rad - 1)). {
  intros.
  intros; eapply le_trans; [ apply Hv | ].
  apply Nat.mul_le_mono_r; pauto.
}
destruct (LPO_fst (fA_ge_1_ε v i)) as [H3| H3].
specialize (proj1 (frac_ge_if_all_fA_ge_1_ε v i) H3) as H.
-rewrite Hnv, Hnuv at 1.
 rewrite (all_fA_ge_1_ε_NQintg_A' 3); [ symmetry | | easy | easy ].
...
 rewrite (all_fA_ge_1_ε_NQintg_A' 3); [ symmetry | easy | easy ].
 rewrite all_fA_ge_1_ε_NQintg_A'; [ symmetry | easy | easy ].
 rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
 rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
 f_equal; f_equal; f_equal.
 subst kv.
 remember (Q.intg (A i nuv v)) as m eqn:Hm.
 symmetry in Hm.
 destruct m.
 +clear H2.
  rewrite Q.frac_small. 2: {
    split; [ easy | ].
    now apply Q.eq_intg_0 in Hm.
  }
  destruct (Q.lt_le_dec (A i nup u + A i nup (P v)) 1) as [H4| H4].
  *destruct (Q.lt_le_dec (A i nuv u + A i nuv v) 1) as [H5| H5]; [ easy | ].
   exfalso.
   apply Q.nlt_ge in H5; apply H5; clear H5.
   subst nv nup nuv.
   now apply (pre_Hugo_Herbelin_1 u v i kup kuv).
  *destruct (Q.lt_le_dec (A i nuv u + A i nuv v) 1) as [H5| H5]; [ | easy ].
   exfalso.
   apply Q.nlt_ge in H4; apply H4; clear H4.
   destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [H2| H2].
  --subst kup; rewrite <- Hnv in Hnup; subst nup.
    destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [Hauv| Hauv].
   ++subst kuv; rewrite <- Hnv in Hnuv; subst nuv; clear H1.
     subst nv.
     now apply pre_Hugo_Herbelin_21.
   ++destruct Hauv as (j & Hjj & Hj).
     subst kuv nv nuv.
     now apply (pre_Hugo_Herbelin_22 _ _ _ j).
  --destruct H2 as (j & Hjj & Hj).
    subst kup.
    rename H3 into Hvt.
    specialize (all_fA_ge_1_ε_P_999 v i Hvt) as H2.
    enough (H : A i nup u = 0%Q). {
      rewrite H, Q.add_0_l.
      rewrite A_all_9; [ | intros k Hk; apply H2 ].
      now apply Q.sub_lt.
    }
    destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [Hauv| Hauv].
   ++subst kuv; rewrite <- Hnv in Hnuv; subst nuv; clear H1.
     clear Hm; subst nv nup.
     now apply (pre_Hugo_Herbelin_31 u v).
   ++destruct Hauv as (k & Hjk & Hk); subst kuv.
     move j before i; move k before j.
     subst nv nup nuv; clear Hr; move Hm before H1.
     now apply (pre_Hugo_Herbelin_32 u v _ _ k).
 +destruct m; [ clear H2 | flia H2 ].
  rewrite (Q.frac_less_small 1). 2: {
    split.
    -specialize (Q.intg_to_frac (A i nuv v) (A_ge_0 _ _ _)) as H2.
     rewrite Hm in H2; rewrite H2.
     now apply Q.le_sub_l.
    -eapply Q.le_lt_trans; [ apply A_upper_bound_for_add | ].
     intros k; rewrite <- Nat.add_assoc; apply Hv.
     rewrite Q.mul_sub_distr_l, Q.mul_1_r.
     now apply Q.sub_lt.
  }
  replace (1 // 1)%Q with 1%Q by easy.
  rewrite Q.add_sub_assoc.
  destruct (Q.lt_le_dec (A i nup u + A i nup (P v))%Q 1) as [H4| H4].
  *destruct (Q.lt_le_dec (A i nuv u + A i nuv v - 1)%Q 1)
      as [H5| H5]; [ easy | exfalso ].
   apply Q.nlt_ge in H5; apply H5; clear H5.
   apply Q.lt_sub_lt_add_r; replace (1 + 1)%Q with 2%Q by easy.
   specialize (all_fA_ge_1_ε_P_999 v i H3) as Hap.
   rewrite (A_all_9 (P v)) in H4; [ | easy ].
   rewrite Q.add_comm, <- Q.add_sub_swap in H4.
   apply Q.lt_sub_lt_add_r, Q.add_lt_mono_l in H4.
   apply A_lt_le_pred in H4.
   apply Q.le_antisymm in H4; [ | easy ].
   symmetry in H4; rewrite Nat.sub_diag in H4.
   rewrite Hnup in H4 at 1.
   replace kup with (0 + kup) in H4 by easy.
   rewrite min_n_add, <- Hnv in H4.
   rewrite <- ApB_A in H4. 2: {
     rewrite Hnv; unfold min_n.
     destruct rad; [ easy | cbn; flia ].
   }
   apply Q.eq_add_0 in H4; [ | easy | easy ].
   clear H1; destruct H4 as (H1, H4).
   destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [H6| H6].
  --subst kuv; rewrite <- Hnv in Hnuv; subst nuv.
    rewrite H1, Q.add_0_l.
    eapply Q.le_lt_trans.
   ++apply A_upper_bound_for_add.
     intros k; rewrite <- Nat.add_assoc; apply Hv.
   ++rewrite Q.mul_sub_distr_l, Q.mul_1_r.
     now apply Q.sub_lt.
  --destruct H6 as (j & Hjj & Hj); subst kuv; move j before i.
    destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [H2| H2].
   ++subst kup; rewrite <- Hnv in Hnup; subst nup nv nuv.
     now apply pre_Hugo_Herbelin_41.
   ++destruct H2 as (k & Hjk & Hk); subst kup; move k before j.
     subst nv nup nuv.
     now apply (pre_Hugo_Herbelin_42 _ _ _ _ k).
  *destruct (Q.lt_le_dec (A i nuv u + A i nuv v - 1)%Q 1)
      as [H5| H5]; [ exfalso | easy ].
   apply Q.nlt_ge in H4; apply H4; clear H4.
   apply Q.lt_sub_lt_add_r in H5.
   replace (1 + 1)%Q with 2%Q in H5 by easy.
   destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [H6| H6].
  --subst kuv; rewrite <- Hnv in Hnuv; subst nuv.
    clear H1.
    destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [H2| H2].
   ++subst kup; rewrite <- Hnv in Hnup; subst nup nv.
     now apply pre_Hugo_Herbelin_51.
   ++destruct H2 as (j & Hjj & Hj); move j before i; subst kup nup nv.
     now apply pre_Hugo_Herbelin_52.
  --destruct H6 as (j & Hjj & Hj); subst kuv; move j before i.
    destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [H2| H2].
   ++subst kup; rewrite <- Hnv in Hnup; subst nup nuv nv.
     now apply (pre_Hugo_Herbelin_61 _ _ _ j).
   ++destruct H2 as (k & Hjk & Hk); subst kup nv nuv nup; move k before j.
     now apply (pre_Hugo_Herbelin_62 _ _ _ j).
-destruct H3 as (j & Hjj & Hj); subst kv.
 destruct (Q.lt_le_dec (A i nuv u + Q.frac (A i nuv v))%Q 1) as [Huv| Huv].
 +rewrite Nat.add_0_r.
  rewrite (Nat.mod_small (Q.intg (A i nuv v))). 2: {
    eapply Nat.le_lt_trans; [ apply H2 | easy ].
  }
  destruct (Q.lt_le_dec (A i nup u + A i nup (P v))%Q 1) as [Hup| Hup].
  *rewrite Nat.add_0_r.
   rewrite Nat.mod_small. 2: {
     eapply Nat.le_lt_trans; [ apply H1 | easy ].
   }
   clear kup Hv3 Hkup Hnup.
   subst kuv nv nuv.
   destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [Hauv| Hauv].
  --now apply (pre_Hugo_Herbelin_71 u).
  --destruct Hauv.
    now apply (pre_Hugo_Herbelin_72 u).
  *subst kuv.
   destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [Hauv| Hauv].
  --destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [Haup| Haup].
   ++now subst; apply (pre_Hugo_Herbelin_81 u).
   ++destruct Haup as (k & Hjk & Hk); subst kup nv nup nuv.
...
     now apply (pre_Hugo_Herbelin_82 u _ _ _ k).
  --destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [Haup| Haup].
   ++idtac.
     ...
   ++idtac.
     ...
 +destruct (Q.lt_le_dec (A i nup u + A i nup (P v))%Q 1) as [Hup| Hup].
  *destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [Hauv| Hauv].
  --destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [Haup| Haup].
   ++...
   ++...
  --destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [Haup| Haup].
   ++...
   ++...
  *destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [Hauv| Hauv].
  --destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [Haup| Haup].
   ++...
   ++...
  --destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [Haup| Haup].
   ++...
   ++...
...

Theorem Hugo_Herbelin {r : radix} : ∀ u v i,
  (∀ k : nat, u (i + k) ≤ rad - 1)
  → (∀ k : nat, v (i + k) ≤ 2 * (rad - 1))
  → P (u ⊕ P v) i = P (u ⊕ v) i.
Proof.
intros * Hu Hv.
specialize radix_ge_2 as Hr.
remember (P v) as v' eqn:Hv'; cbn.
unfold P, add_series.
replace (λ i, u i + v i) with (u ⊕ v) by easy.
replace (λ i, u i + v' i) with (u ⊕ v') by easy.
do 2 rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
remember (v' i) as x eqn:Hx.
rewrite Hv' in Hx; subst x; cbn.
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
subst v'; rewrite Nat.add_comm; symmetry.
now apply pre_Hugo_Herbelin.
Qed.

Theorem truc {r : radix} : ∀ x u,
  ({| ureal := prop_carr (x ⊕ {| ureal := prop_carr u |}) |} =
   {| ureal := prop_carr (add_series (d2n (ureal x)) (d2n (prop_carr u))) |})%F.
Proof. easy. Qed.

Theorem fold_P {r : radix} : ∀ x, d2n (prop_carr x) = P x.
Proof. easy. Qed.

Theorem d2n_eq_compat {r : radix} : ∀ u v,
  (∀ i, u i = v i)
  → ∀ i, d2n u i = d2n v i.
Proof.
intros * Huv *.
unfold d2n.
f_equal.
apply Huv.
Qed.

Theorem is_9_strict_after_eq_compat {r : radix} : ∀ u v,
  (∀ i, u i = v i)
  → ∀ i j, is_9_strict_after u i j = is_9_strict_after v i j.
Proof.
intros * Huv *.
unfold is_9_strict_after.
now rewrite (d2n_eq_compat u v).
Qed.

Theorem normalize_eq_compat {r : radix} : ∀ u v,
  (∀ i, u i = v i)
  → ∀ i, normalize u i = normalize v i.
Proof.
intros * Huv *.
unfold normalize.
destruct (LPO_fst (is_9_strict_after u i)) as [H1| H1].
-destruct (LPO_fst (is_9_strict_after v i)) as [H2| H2].
 +now rewrite (d2n_eq_compat u v).
 +destruct H2 as (j & Hj & Hjj).
  specialize (H1 j).
  rewrite (is_9_strict_after_eq_compat u v) in H1; [ | easy ].
  now rewrite H1 in Hjj.
-destruct (LPO_fst (is_9_strict_after v i)) as [H2| H2].
 +destruct H1 as (j & Hj & Hjj).
  specialize (H2 j).
  rewrite (is_9_strict_after_eq_compat u v) in Hjj; [ | easy ].
  now rewrite Hjj in H2.
 +apply Huv.
Qed.

Theorem add_series_assoc {r : radix} : ∀ x y z i,
  add_series (fd2n x) (y ⊕ z)%F i = add_series (fd2n z) (y ⊕ x)%F i.
Proof.
intros.
unfold add_series, "⊕", fd2n.
unfold "⊕"%F.
rewrite Nat.add_assoc, Nat.add_comm.
do 2 rewrite Nat.add_assoc.
now rewrite Nat.add_shuffle0.
Qed.

Theorem ureal_add_assoc {r : radix} : ∀ x y z, (x + (y + z) = z + (y + x))%F.
Proof.
intros.
unfold "+"%F.
intros i.
Print P.
assert (H1 : ∀ x z i,
  prop_carr (d2n (ureal x) ⊕ P (y ⊕ z)%F) i =
  prop_carr (d2n (ureal x) ⊕ (y ⊕ z)%F) i). {
  clear x z i.
  intros x z i.
  apply digit_eq_eq.
  apply Hugo_Herbelin.
  -intros k.
   apply digit_le_pred_radix.
  -intros k.
   apply ureal_add_series_le_twice_pred.
}
do 2 rewrite truc.
do 2 rewrite fold_P.
unfold ureal_normalize, fd2n; cbn.
apply digit_eq_eq.
apply normalize_eq_compat.
intros j.
do 2 rewrite H1.
apply prop_carr_eq_compat.
clear j; intros j.
apply add_series_assoc.
Qed.

...

Theorem add_assoc_case_11 {r : radix} : ∀ x y z i,
  (∀ k, (x ⊕ (y + z)) (i + k + 1) = rad - 1)
  → (∀ k, (z ⊕ (y + x)) (i + k + 1) = rad - 1)
  → ((x ⊕ (y + z)) i) mod rad = ((z ⊕ (y + x)) i) mod rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros H1 H2.
unfold ureal_add_series.
unfold ureal_add, fd2n; simpl.
unfold carry.
destruct (LPO_fst (A_ge_1 (y ⊕ z) i)) as [H3| H3].
-simpl.
 destruct (LPO_fst (A_ge_1 (y ⊕ x) i)) as [H4| H4].
 +now simpl; apply add_assoc_case_11_11.
 +destruct H4 as (j2 & Hjj2 & Hj2); simpl.
  apply (add_assoc_case_11_12 j2); try easy.
  intros k.
  specialize (H1 k) as H5.
  unfold ureal_add_series in H5.
  rewrite A_ge_1_ureal_add_series_all_true in H5; [ | easy ].
  now rewrite Nat.add_0_r in H5.
-destruct H3 as (j1 & Hjj1 & Hj1); simpl.
 destruct (LPO_fst (A_ge_1 (y ⊕ x) i)) as [H4| H4].
 +simpl; symmetry.
  apply (add_assoc_case_11_12 j1); try easy.
  intros k.
  specialize (H2 k) as H5.
  unfold ureal_add_series in H5.
  rewrite A_ge_1_ureal_add_series_all_true in H5; [ | easy ].
  now rewrite Nat.add_0_r in H5.
 +destruct H4 as (j2 & Hjj2 & Hj2); simpl.
  rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
  rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
  unfold ureal_add_series at 1 3.
  do 4 rewrite Nat.add_assoc.
  do 2 rewrite fold_fd2n.
  replace (fd2n z i + fd2n y i + fd2n x i) with
      (fd2n x i + fd2n y i + fd2n z i) by flia.
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  f_equal; f_equal.
  move j2 before j1.
  apply A_ge_1_false_iff in Hj1.
  apply A_ge_1_false_iff in Hj2.
  unfold min_n in Hj1, Hj2 |-*.
  remember (rad * (i + j1 + 3)) as n1 eqn:Hn1.
  remember (n1 - i - 1) as s1 eqn:Hs1.
  move n1 before j2.
  move s1 before n1.
  remember (rad * (i + j2 + 3)) as n2 eqn:Hn2.
  remember (n2 - i - 1) as s2 eqn:Hs2.
  move n2 before s1.
  move s2 before n2.
  assert (Hr2s1 : 2 ≤ rad ^ s1). {
    destruct s1.
    -rewrite Hn1 in Hs1.
     destruct rad; [ easy | simpl in Hs1; flia Hs1 ].
    -simpl.
     replace 2 with (2 * 1) by flia.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  assert (Hr2s2 : 2 ≤ rad ^ s2). {
    destruct s2.
    -rewrite Hn2 in Hs2.
     destruct rad; [ easy | simpl in Hs2; flia Hs2 ].
    -simpl.
     replace 2 with (2 * 1) by flia.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  destruct (lt_dec (nA i n1 (y ⊕ z)) (rad ^ s1)) as [H3| H3].
  *rewrite Nat.mod_small in Hj1; [ | easy ].
   rewrite Nat.div_small; [ | easy ].
   destruct (lt_dec (nA i n2 (y ⊕ x)) (rad ^ s2)) as [H4| H4].
  --rewrite Nat.mod_small in Hj2; [ | easy ].
    now rewrite Nat.div_small.
  --exfalso.
    apply Nat.nlt_ge in H4.
    rewrite Nat_mod_less_small in Hj2; cycle 1.
   ++split; [ easy | rewrite Hs2; apply nA_ureal_add_series_lt ].
   ++move Hn1 before s2; move Hs1 before Hn1.
     move Hn2 before Hs1; move Hs2 before Hn2.
     move Hr2s1 before Hs2; move Hr2s2 before Hr2s1.
     move Hjj2 before Hjj1.
     apply Nat.lt_sub_lt_add_r in Hj2.
     (* y ≠ 0, otherwise would contradict H4
        x ≠ 0, otherwise would contradict H1
        z ≠ 0, otherwise would contradict H2
        x cannot end with and infinity of 0s, or would contradict H1
        z cannot end with and infinity of 0s, or would contradict H2 *)
     assert
       (H5 : fd2n x (i + 1) + fd2n y (i + 1) + fd2n z (i + 1) = rad - 3
           ∨ fd2n x (i + 1) + fd2n y (i + 1) + fd2n z (i + 1) = rad - 2
           ∨ fd2n x (i + 1) + fd2n y (i + 1) + fd2n z (i + 1) = rad - 1
           ∨ fd2n x (i + 1) + fd2n y (i + 1) + fd2n z (i + 1) =
               2 * rad - 3
           ∨ fd2n x (i + 1) + fd2n y (i + 1) + fd2n z (i + 1) =
               2 * rad - 2
           ∨ fd2n x (i + 1) + fd2n y (i + 1) + fd2n z (i + 1) =
               2 * rad - 1). {
       specialize (H1 0); rewrite Nat.add_0_r in H1.
       unfold "+"%F, fd2n in H1; simpl in H1.
       unfold "⊕", fd2n in H1; simpl in H1.
       do 3 rewrite fold_fd2n in H1.
       specialize carry_le_2 as H5.
       specialize (H5 (λ i, dig (ureal y i) + dig (ureal z i)) (i + 1)).
       assert
         (H :
          ∀ k, (λ i, dig (ureal y i) + dig (ureal z i)) (i + 1 + k + 1) ≤
                 2 * (rad - 1)). {
         intros k.
         specialize (digit_lt_radix (ureal y (i + 1 + k + 1))) as H6.
         specialize (digit_lt_radix (ureal z (i + 1 + k + 1))) as H7.
         flia H6 H7.
       }
       specialize (H5 H); clear H.
       remember
         (carry (λ i, dig (ureal y i) + dig (ureal z i)) (i + 1))
         as c eqn:Hc.
       destruct c.
       -rewrite Nat.add_0_r in H1.
        destruct (lt_dec (fd2n y (i + 1) + fd2n z (i + 1)) rad) as [H6| H6].
        +rewrite Nat.mod_small in H1; [ | easy ].
         rewrite Nat.add_assoc in H1.
         now right; right; left.
        +apply Nat.nlt_ge in H6.
         rewrite Nat_mod_less_small in H1.
         *rewrite Nat.add_sub_assoc in H1; [ | easy ].
          right; right; right; right; right.
          flia Hr H1.
         *split; [ easy | ].
          specialize (digit_lt_radix (ureal y (i + 1))) as Hy.
          specialize (digit_lt_radix (ureal z (i + 1))) as Hz.
          unfold fd2n; flia Hy Hz.
       -destruct c.
        +destruct (lt_dec (fd2n y (i + 1) + fd2n z (i + 1) + 1) rad) as [H6| H6].
         *rewrite Nat.mod_small in H1; [ | easy ].
          rewrite Nat.add_assoc in H1.
          right; left; flia Hr H1.
         *apply Nat.nlt_ge in H6.
          rewrite Nat_mod_less_small in H1.
         --rewrite Nat.add_sub_assoc in H1; [ | easy ].
           right; right; right; right; left; flia Hr H1.
         --split; [ easy | ].
           specialize (digit_lt_radix (ureal y (i + 1))) as Hy.
           specialize (digit_lt_radix (ureal z (i + 1))) as Hz.
           unfold fd2n; flia Hy Hz.
        +destruct c; [ clear H5 | flia H5 ].
         destruct (lt_dec (fd2n y (i + 1) + fd2n z (i + 1) + 2) rad) as [H6| H6].
         *rewrite Nat.mod_small in H1; [ | easy ].
          rewrite Nat.add_assoc in H1.
          left; flia Hr H1.
         *apply Nat.nlt_ge in H6.
          destruct (lt_dec (fd2n y (i + 1) + fd2n z (i + 1) + 2) (2 * rad))
            as [H7| H7].
         --rewrite Nat_mod_less_small in H1; [ | easy ].
           rewrite Nat.add_sub_assoc in H1; [ | easy ].
           right; right; right; left; flia Hr H1.
         --apply Nat.nlt_ge in H7.
(* case 3r-3 to be added! *)
...
     }
     remember (ureal_shift (i + 1) x) as xs eqn:Hxs.
     remember (ureal_shift (i + 1) y) as ys eqn:Hys.
     move ys before xs.
     assert (Hlex : (xs + ys ≤ xs)%F). {
       unfold "≤"%F.
       rewrite ureal_normalize_add.
       remember (ureal_normalize xs) as xsn eqn:Hxsn.
       move xsn before ys.
       unfold ureal_norm_le.
       destruct (LPO_fst (has_same_digits (xs + ys)%F xsn)) as [H5| H5];
         [ easy | ].
       destruct H5 as (j & Hjj & Hj).
       apply has_same_digits_false_iff in Hj.
       destruct (lt_dec (fd2n (xs + ys) j) (fd2n xsn j)) as [H5| H5];
         [ easy | ].
       assert (H6 : fd2n xsn j < fd2n (xs + ys) j) by flia Hj H5.
       clear Hj H5.
       apply Nat.nle_gt in H6; apply H6; clear H6.
(**)
       subst xsn.
       unfold ureal_normalize, fd2n at 2; simpl.
       unfold normalize.
       destruct (LPO_fst (is_9_strict_after (ureal xs) j)) as [H5| H5].
       -specialize (is_9_strict_after_all_9 _ _ H5) as H6; clear H5.
        assert (H5 : ∀ k, fd2n x (i + j + k + 2) = rad - 1). {
          intros k.
          specialize (H6 k).
          rewrite Hxs in H6.
          unfold d2n in H6; simpl in H6.
          unfold fd2n.
          now replace (i + 1 + (j + k + 1)) with (i + j + k + 2) in H6 by flia.
        }
        destruct (lt_dec (S (d2n (ureal xs) j)) rad) as [H7| H7].
        +simpl.
         unfold d2n, fd2n.
Theorem glop {r : radix} : ∀ x y i, ureal_norm_eq (ureal_shift i (x + y)) (ureal_shift i x + ureal_shift i y)%F.
Proof.
intros * j.
unfold ureal_shift, fd2n.
unfold "+"%F, "⊕", fd2n; simpl.
f_equal; f_equal.
unfold carry.
...
ADMITTED.
rewrite Hxs, Hys.
Search ureal_norm_eq.
...
rewrite <- glop.
unfold ureal_shift; simpl.
...
       rewrite Hxsn, Hxs, Hys.
       unfold ureal_shift, fd2n; simpl.
       unfold "⊕", fd2n; simpl.
       unfold normalize.
...
       destruct (ureal_eq_dec xs ureal_999) as [Hx| Hx].
...
     remember (max n1 n2) as n3 eqn:Hn3.
     remember (n3 - i - 1) as s3 eqn:Hs3.
     move s3 before n3.
     assert
       (Hj1' : nA i n3 (y ⊕ z) < (rad ^ S j1 - 1) * rad ^ (s3 - S j1) +
          2 * rad ^ (s3 - s1)). {
       replace (s3 - S j1) with (s1 - S j1 + (s3 - s1)); cycle 1.
       -destruct (le_dec n1 n2) as [Hnn| Hnn].
        +rewrite Nat.max_r in Hn3; [ | easy ].
         subst n3; rewrite <- Hs2 in Hs3; subst s3.
         assert (Hss : s1 ≤ s2) by (rewrite Hs1, Hs2; flia Hnn).
         assert (Hsj : j1 < s1). {
           rewrite Hs1, Hn1; destruct rad; [ easy | simpl; flia ].
         }
         flia Hsj Hss.
        +apply Nat.nle_gt, Nat.lt_le_incl in Hnn.
         rewrite Nat.max_l in Hn3; [ | easy ].
         subst n3; rewrite <- Hs1 in Hs3; subst s3.
         now rewrite Nat.sub_diag, Nat.add_0_r.
       -rewrite Nat.pow_add_r, Nat.mul_assoc.
        destruct (le_dec n1 n2) as [Hnn| Hnn].
        +rewrite Nat.max_r in Hn3; [ | easy ].
         subst n3; rewrite <- Hs2 in Hs3; subst s3.
         rewrite (nA_split n1); cycle 1.
         *split; [ | flia Hnn ].
          rewrite Hn1; destruct rad; [ easy | simpl; flia ].
         *apply Nat.add_lt_mono.
         --replace (n2 - n1) with (s2 - s1); cycle 1.
          ++rewrite Hs1, Hs2, Hn1, Hn2.
            destruct rad; [ easy | simpl; flia ].
          ++apply Nat.mul_lt_mono_pos_r; [ | easy ].
            now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
         --rewrite Hs2, Hs1.
           enough (n1 > i).
          ++replace (n2 - i - 1 - (n1 - i - 1)) with (n2 - (n1 - 1) - 1)
             by flia H.
            eapply le_lt_trans.
           **apply nA_upper_bound_for_add.
             intros; apply ureal_add_series_le_twice_pred.
           **rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
             apply Nat.sub_lt; [ | apply Nat.lt_0_2 ].
             replace 2 with (2 * 1) at 1 by flia.
             apply Nat.mul_le_mono_l.
             now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
          ++rewrite Hn1.
            destruct rad; [ easy | simpl; flia ].
        +rewrite Nat.max_l in Hn3; [ | flia Hnn ].
         subst n3; rewrite <- Hs1 in Hs3; subst s3.
         rewrite Nat.sub_diag, Nat.pow_0_r.
         do 2 rewrite Nat.mul_1_r.
         eapply lt_trans; [ apply Hj1 | flia ].
     }
     assert
       (Hj2' : nA i n3 (y ⊕ x) <
          (rad ^ S j2 - 1) * rad ^ (s3 - S j2) + rad ^ s3 +
           2 * rad ^ (s3 - s2)). {
       replace (s3 - S j2) with (s2 - S j2 + (s3 - s2)); cycle 1.
       -destruct (le_dec n1 n2) as [Hnn| Hnn].
        +rewrite Nat.max_r in Hn3; [ | easy ].
         subst n3; rewrite <- Hs2 in Hs3; subst s3.
         now rewrite Nat.sub_diag, Nat.add_0_r.
        +apply Nat.nle_gt, Nat.lt_le_incl in Hnn.
         rewrite Nat.max_l in Hn3; [ | easy ].
         subst n3; rewrite <- Hs1 in Hs3; subst s3.
         assert (Hss : s2 ≤ s1) by (rewrite Hs1, Hs2; flia Hnn).
         assert (Hsj : j2 < s2). {
           rewrite Hs2, Hn2; destruct rad; [ easy | simpl; flia ].
         }
         flia Hsj Hss.
       -rewrite Nat.pow_add_r, Nat.mul_assoc.
        destruct (le_dec n1 n2) as [Hnn| Hnn].
        +rewrite Nat.max_r in Hn3; [ | easy ].
         subst n3; rewrite <- Hs2 in Hs3; subst s3.
         rewrite Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r.
         eapply lt_trans; [ apply Hj2 | ].
         apply Nat.lt_add_pos_r, Nat.lt_0_2.
        +apply Nat.nle_gt, Nat.lt_le_incl in Hnn.
         rewrite Nat.max_l in Hn3; [ | easy ].
         subst n3; rewrite <- Hs1 in Hs3; subst s3.
         rewrite (nA_split n2); cycle 1.
         *split; [ | flia Hnn ].
          rewrite Hn2; destruct rad; [ easy | simpl; flia ].
         *apply Nat.add_lt_mono.
          assert (Hss : s2 ≤ s1) by (rewrite Hs1, Hs2; flia Hnn).
          replace s1 with (s2 + (s1 - s2)) at 2 by flia Hss.
         --rewrite Nat.pow_add_r, <- Nat.mul_add_distr_r.
           replace (s1 - s2) with (n1 - n2); cycle 1.
          ++rewrite Hs1, Hs2, Hn1, Hn2.
            destruct rad; [ easy | simpl; flia ].
          ++apply Nat.mul_lt_mono_pos_r; [ | easy ].
            now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
         --rewrite Hs2, Hs1.
           enough (n2 > i).
          ++replace (n1 - i - 1 - (n2 - i - 1)) with (n1 - (n2 - 1) - 1)
             by flia H.
            eapply le_lt_trans.
           **apply nA_upper_bound_for_add.
             intros; apply ureal_add_series_le_twice_pred.
           **rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
             apply Nat.sub_lt; [ | apply Nat.lt_0_2 ].
             replace 2 with (2 * 1) at 1 by flia.
             apply Nat.mul_le_mono_l.
             now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
          ++rewrite Hn2.
            destruct rad; [ easy | simpl; flia ].
     }
     assert (H3' : nA i n3 (y ⊕ z) < rad ^ s3 + 2 * rad ^ (s2 - s1)). {
       destruct (le_dec n1 n2) as [Hnn| Hnn].
       -rewrite Nat.max_r in Hn3; [ | easy ].
        subst n3; rewrite <- Hs2 in Hs3; subst s3.
        rewrite (nA_split n1); cycle 1.
        +split; [ | flia Hnn ].
         rewrite Hn1; destruct rad; [ easy | simpl; flia ].
        +assert (Hss : s1 ≤ s2) by (rewrite Hs1, Hs2; flia Hnn).
         apply Nat.add_lt_mono.
         *replace s2 with (s2 - s1 + s1) by flia Hss.
          rewrite Nat.pow_add_r.
          replace (n2 - n1) with (s2 - s1); cycle 1.
         --rewrite Hs1, Hs2, Hn1, Hn2.
           destruct rad; [ easy | simpl; flia ].
         --rewrite Nat.mul_comm.
           apply Nat.mul_lt_mono_pos_l; [ | easy ].
           now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
         *eapply le_lt_trans.
         --apply nA_upper_bound_for_add.
           intros k; apply ureal_add_series_le_twice_pred.
         --apply Nat.mul_lt_mono_pos_l; [ apply Nat.lt_0_2 | ].
           replace (n2 - (n1 - 1) - 1) with (s2 - s1); cycle 1.
          ++rewrite Hs1, Hs2.
            enough (n1 > i) by flia H.
            rewrite Hn1.
            destruct rad; [ easy | simpl; flia ].
          ++apply Nat.sub_lt; [ | apply Nat.lt_0_1 ].
            now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
       -rewrite Nat.max_l in Hn3; [ | flia Hnn ].
        subst n3; rewrite <- Hs1 in Hs3; subst s3.
        now apply lt_plus_trans.
     }
     assert (H4' : rad ^ s3 ≤ nA i n3 (y ⊕ x)). {
       destruct (le_dec n1 n2) as [Hnn| Hnn].
       -rewrite Nat.max_r in Hn3; [ | easy ].
        now subst n3; rewrite <- Hs2 in Hs3; subst s3.
       -apply Nat.nle_gt, Nat.lt_le_incl in Hnn.
        rewrite Nat.max_l in Hn3; [ | easy ].
        subst n3; rewrite <- Hs1 in Hs3; subst s3.
        assert (Hss : s2 ≤ s1) by (rewrite Hs1, Hs2; flia Hnn).
        replace s1 with (s1 - s2 + s2) by flia Hss.
        rewrite Nat.pow_add_r.
        rewrite (nA_split n2); cycle 1.
        +split; [ | flia Hnn ].
         rewrite Hn2; destruct rad; [ easy | simpl; flia ].
        +apply le_plus_trans.
         rewrite Nat.mul_comm.
         apply Nat.mul_le_mono; [ easy | ].
         apply Nat.pow_le_mono_r; [ easy | ].
         rewrite Hs1, Hs2; flia.
     }
     assert (H1' : nA i n3 (x ⊕ (y + z)) = rad ^ s3 - 1). {
       unfold nA.
       erewrite summation_eq_compat; cycle 1.
       -intros j Hj.
        specialize (H1 (j - (i + 1))).
        replace (i + (j - (i + 1)) + 1) with j in H1 by flia Hj.
        now rewrite H1.
       -simpl; rewrite <- summation_mul_distr_l; simpl.
        rewrite summation_rtl.
        rewrite summation_shift.
        +erewrite summation_eq_compat; cycle 1.
         *intros j Hj.
          replace (n3 - 1 - (n3 - 1 + (i + 1) - (i + 1 + j))) with j.
         --easy.
         --flia Hj.
         *rewrite <- power_summation_sub_1; [ | easy ].
          f_equal; f_equal.
          rewrite <- Nat.sub_succ_l.
         --rewrite <- Nat.sub_succ_l.
          ++rewrite Nat.sub_succ, Nat.sub_0_r; flia Hs3.
          ++rewrite Hn3, Hn1; destruct rad; [ easy | simpl; flia ].
         --rewrite Hn3, Hn1; destruct rad; [ easy | simpl; flia ].
        +rewrite Hn3, Hn1; destruct rad; [ easy | simpl; flia ].
     }
     assert (H2' : nA i n3 (z ⊕ (y + x)) = rad ^ s3 - 1). {
       unfold nA.
       erewrite summation_eq_compat; cycle 1.
       -intros j Hj.
        specialize (H2 (j - (i + 1))).
        replace (i + (j - (i + 1)) + 1) with j in H2 by flia Hj.
        now rewrite H2.
       -simpl; rewrite <- summation_mul_distr_l; simpl.
        rewrite summation_rtl.
        rewrite summation_shift.
        +erewrite summation_eq_compat; cycle 1.
         *intros j Hj.
          replace (n3 - 1 - (n3 - 1 + (i + 1) - (i + 1 + j))) with j.
         --easy.
         --flia Hj.
         *rewrite <- power_summation_sub_1; [ | easy ].
          f_equal; f_equal.
          rewrite <- Nat.sub_succ_l.
         --rewrite <- Nat.sub_succ_l.
          ++rewrite Nat.sub_succ, Nat.sub_0_r; flia Hs3.
          ++rewrite Hn3, Hn1; destruct rad; [ easy | simpl; flia ].
         --rewrite Hn3, Hn1; destruct rad; [ easy | simpl; flia ].
        +rewrite Hn3, Hn1; destruct rad; [ easy | simpl; flia ].
     }
(*
0                                     1
---------------------------------------
<-------><---------------------------->  d'après H1
    x                y+z
<---><-------------------------------->  d'après H2
 x+y                 z

x+y est inférieur à x d'après Hj2 et H4
contradiction car z doit être inférieur à y+z d'après Hj1
...
1-z = x+y ≤ x
1-x = y+z ≥ z
...
x+y+z ≤ x+z
x+y+z ≥ x+z
...
Pas clair... tout dépend de ce qu'on entend par "≤".
*)
(* counterexample:
     x=0.999...
     y=0.5
     z=0.4999... ?
 H1: x ⊕ (y + z) = 0.999 ⊕ (0.5 + 0.4999) = 0.999 ⊕ P(0.999) = 0.999 ⊕ 0 = 0.999 ok
 H2: (x ⊕ y) + z = 0.4999 ⊕ (0.5 + 0.9999) = 0.4999 ⊕ P(0.4999) = 0.4999 ⊕ 0.5 = 0.999 ok
 Hj1: nA i n1 (y ⊕ z) = nA i n1 (0.5 ⊕ 0.4999) = nA i n1 0.9999: ah no
    2nd try:
     x=0.333..33999...    (j1+1 3s)
     y=0.333..325         (j1 3s and 2)
     z=0.333..334999...   (j1+1 3s)
 H1: x ⊕ (y + z) = 0.333..33999 ⊕ (0.333..325000 + 0.333..334999)
                 = 0.333..33999 ⊕ P(0.666..659999)
                 = 0.333..33999 ⊕ 0.666..660000
                 = 0.999.. ok
 Hj1: nA i n1 (y ⊕ z) = nA i n1 (0.333..325000... ⊕ 0.333..334999...)
                      = nA i n1 (0.666..659999...) < 0.999..99000 ok
 but H4 won't work
*)
...
     assert (Hxyx : nA i n3 (fd2n (y + x)) < nA i n3 (fd2n x)). {
       move Hj2' at bottom; move H4' at bottom.
...
     rewrite nA_ureal_add_series in Hj1', Hj2', H3', H4', H1', H2'.
     eapply Nat.add_le_mono_r in H4'.
     rewrite <- Nat.add_assoc, H1' in H4'.
     apply Nat.nlt_ge in H4'; apply H4'; clear H4'.
     rewrite Nat.add_sub_assoc; cycle 1.
    **now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    **rewrite Nat.add_comm.
      destruct (zerop (nA i n3 (fd2n y))) as [Hy| Hy].
    ---rewrite Hy, Nat.add_0_r.
       apply lt_plus_trans.
       apply Nat.sub_lt; [ | apply Nat.lt_0_1 ].
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    ---rewrite <- Nat.add_sub_assoc; [ | flia Hy ].
       apply Nat.add_lt_mono_l.
       apply (Nat.le_lt_add_lt 1 1); [ easy | ].
       rewrite Nat.sub_add; [ | easy ].
       rewrite Nat.add_1_r.
       apply Nat.lt_succ_r.
       apply (Nat.add_le_mono_l _ _ (nA i n3 (fd2n x))).
       rewrite H1'.
rewrite nA_ureal_add_series, Nat.add_comm in H4.
(* ça veut dire que ce que je cherche à démontrer est faux ? *)
...
       rewrite Nat.add_comm in Hj2'.
...
       eapply Nat.le_trans.
     +++apply Nat.lt_le_incl in Hj2'.
        apply Hj2'.
     +++idtac.
...
  *apply Nat.nlt_ge in H3.
   rewrite Nat_div_less_small; cycle 1.
  --split; [ easy | rewrite Hs1; apply nA_ureal_add_series_lt ].
  --destruct (lt_dec (nA i n2 (y ⊕ x)) (rad ^ s2)) as [H4| H4].
   ++exfalso.
     ... (* same as above, I guess, by symmetry between x and z *)
   ++apply Nat.nlt_ge in H4.
     rewrite Nat_div_less_small; [ easy | ].
     split; [ easy | rewrite Hs2; apply nA_ureal_add_series_lt ].
...

Theorem ureal_add_assoc {r : radix} : ∀ x y z,
  ureal_norm_eq (x + (y + z)) ((x + y) + z).
Proof.
intros.
specialize radix_ge_2 as Hr.
specialize (ureal_add_comm (x + y) z) as H.
rewrite H; clear H.
specialize (ureal_add_comm x y) as H.
rewrite H; clear H.
unfold ureal_norm_eq.
intros i.
unfold ureal_add at 1 3.
unfold fd2n; simpl.
unfold carry.
destruct (LPO_fst (A_ge_1 (x ⊕ (y + z)) i)) as [H1| H1].
-simpl.
 remember (rad * (i + 3)) as n1 eqn:Hn1.
 remember (n1 - i - 1) as s1 eqn:Hs1.
 move s1 before n1.
 assert (Hr2s1 : 2 ≤ rad ^ s1). {
   destruct s1.
   -rewrite Hn1 in Hs1.
    destruct rad; [ easy | simpl in Hs1; flia Hs1 ].
   -simpl.
    replace 2 with (2 * 1) by flia.
    apply Nat.mul_le_mono; [ easy | ].
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 }
 apply A_ge_1_add_all_true_if in H1.
 +destruct (LPO_fst (A_ge_1 (z ⊕ (y + x)) i)) as [H2| H2].
  *simpl.
   destruct H1 as [H1| [H1| H1]].
  --rewrite nA_all_9; [ | intros; apply H1 ].
    rewrite <- Hs1.
    rewrite Nat.div_small; [ | flia Hr2s1 ].
    rewrite Nat.add_0_r.
    rewrite Nat.add_shuffle0.
    rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
    rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
    f_equal; f_equal.
    apply A_ge_1_add_all_true_if in H2.
   ++destruct H2 as [H2| [H2| H2]].
    **rewrite nA_all_9; [ | easy ].
      rewrite <- Hs1, Nat.div_small; [ | flia Hr2s1 ].
      rewrite Nat.add_0_r.
      now apply add_assoc_case_11.
    **now apply not_all_18_x_yz in H2.
    **destruct H2 as (j2 & _ & _ & H2aft).
      remember (i + j2 + 1) as n eqn:Hn.
      assert (H2 : ∀ k, (z ⊕ (y + x)) (n + k + 1) = 2 * (rad - 1)). {
        intros k; subst n.
        replace (i + j2 + 1 + k + 1) with (i + j2 + k + 2) by flia.
        apply H2aft.
      }
      now apply not_all_18_x_yz in H2.
   ++intros k; apply ureal_add_series_le_twice_pred.
  --now apply not_all_18_x_yz in H1.
  --destruct H1 as (j1 & _ & _ & H1aft).
    remember (i + j1 + 1) as n eqn:Hn.
    assert (H3 : ∀ k, (x ⊕ (y + z)) (n + k + 1) = 2 * (rad - 1)). {
      intros k; subst n.
      replace (i + j1 + 1 + k + 1) with (i + j1 + k + 2) by flia.
      apply H1aft.
    }
    now apply not_all_18_x_yz in H3.
  *destruct H2 as (j2 & Hjj2 & Hj2); simpl.
   destruct H1 as [H1| [H1| H1]].
  --rewrite nA_all_9; [ | easy ].
    rewrite <- Hs1, Nat.div_small; [ | flia Hr2s1 ].
    rewrite Nat.add_0_r.
    clear n1 s1 Hn1 Hs1 Hr2s1.
    apply A_ge_1_false_iff in Hj2.
    remember (rad * (i + j2 + 3)) as n1 eqn:Hn1.
    remember (n1 - i - 1) as s1 eqn:Hs1.
    move s1 before n1.
    destruct (lt_dec (nA i n1 (z ⊕ (y + x))) (rad ^ s1)) as [H2| H2].
   ++rewrite Nat.mod_small in Hj2; [ | easy ].
     rewrite Nat.div_small; [ | easy ].
     rewrite Nat.add_0_r.
     ...
   ++apply Nat.nlt_ge in H2.
     assert (H : rad ^ s1 ≤ nA i n1 (z ⊕ (y + x)) < 2 * rad ^ s1). {
       split; [ easy | rewrite Hs1; apply nA_ureal_add_series_lt ].
     }
     rewrite Nat_mod_less_small in Hj2; [ | easy ].
     rewrite Nat_div_less_small; [ clear H | easy ].
     apply Nat.lt_sub_lt_add_l in Hj2.
     rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
     rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
     f_equal; f_equal.
     ...
  --now apply not_all_18_x_yz in H1.
  --destruct H1 as (j1 & _ & _ & H1aft).
    remember (i + j1 + 1) as n eqn:Hn.
    assert (H3 : ∀ k, (x ⊕ (y + z)) (n + k + 1) = 2 * (rad - 1)). {
      intros k; subst n.
      replace (i + j1 + 1 + k + 1) with (i + j1 + k + 2) by flia.
      apply H1aft.
    }
    now apply not_all_18_x_yz in H3.
 +intros k; apply ureal_add_series_le_twice_pred.
-destruct H1 as (j1 & Hjj1 & Hj1); simpl.
 destruct (LPO_fst (A_ge_1 (z ⊕ (y + x)) i)) as [H2| H2].
 +simpl.
  apply A_ge_1_add_all_true_if in H2; cycle 1.
  *intros k; apply ureal_add_series_le_twice_pred.
  *symmetry.
   destruct H2 as [H2| [H2| H2]].
  --rewrite nA_all_9; [ | intros; apply H2 ].
    rewrite Nat.div_small; cycle 1.
   ++apply Nat.sub_lt; [ | apply Nat.lt_0_1 ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   ++rewrite Nat.add_0_r.
     ...
  --rewrite nA_all_18; [ | easy ].
    ...
  --destruct H2 as (j2 & H2bef & H2whi & H2aft).
    rewrite (nA_9_8_all_18 j2); [ | easy | easy | easy ].
    ...
 +destruct H2 as (j2 & Hjj2 & Hj2); simpl.
  ...
Qed.
