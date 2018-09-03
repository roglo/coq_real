(* Reals between 0 and 1; associativity of addition *)

Require Import Utf8 Arith NPeano Psatz.
Require Import Misc Summation FracReal.
Set Nested Proofs Allowed.

Theorem nA_freal_add_series {r : radix} : ∀ x y i n,
   nA i n (x ⊕ y) = nA i n (fd2n x) + nA i n (fd2n y).
Proof.
intros.
rewrite nA_eq_compat with (v := λ j, fd2n x j + fd2n y j); [ | easy ].
unfold nA.
erewrite summation_eq_compat; cycle 1.
-intros j Hj; apply Nat.mul_add_distr_r.
-apply summation_add_distr.
Qed.

Theorem nA_freal_add_series_lt {r : radix} : ∀ i n x y,
  nA i n (x ⊕ y) < 2 * rad ^ (n - i - 1).
Proof.
intros.
eapply le_lt_trans.
-apply nA_upper_bound_for_add.
 intros k; apply freal_add_series_le_twice_pred.
-rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
 apply Nat.sub_lt; [ | apply Nat.lt_0_2 ].
 replace 2 with (2 * 1) at 1 by flia.
 apply Nat.mul_le_mono_l.
 now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

Theorem eq_add_series_18_eq_9 {r : radix} : ∀ x y n,
  (∀ k, (x ⊕ y) (n + k + 1) = 2 * (rad - 1))
  → (∀ k, fd2n x (n + k + 1) = rad - 1) ∧ (∀ k, fd2n y (n + k + 1) = rad - 1).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hxy.
split.
-intros.
 specialize (Hxy k).
 unfold freal_add_series in Hxy.
 specialize (digit_lt_radix (freal x (n + k + 1))) as H1.
 specialize (digit_lt_radix (freal y (n + k + 1))) as H2.
 unfold fd2n in Hxy |-*; lia.
-intros.
 specialize (Hxy k).
 unfold freal_add_series in Hxy.
 specialize (digit_lt_radix (freal x (n + k + 1))) as H1.
 specialize (digit_lt_radix (freal y (n + k + 1))) as H2.
 unfold fd2n in Hxy |-*; lia.
Qed.

Theorem eq_add_series_eq_l {r : radix} : ∀ x y n a,
  (∀ k, (x ⊕ y) (n + k + 1) = a)
  → (∀ k, fd2n x (n + k + 1) = a)
  → ∀ k, fd2n y (n + k + 1) = 0.
Proof.
intros * Hxy Hx *.
specialize (Hxy k).
specialize (Hx k).
unfold freal_add_series in Hxy; lia.
Qed.

Theorem eq_add_series_eq_r {r : radix} : ∀ x y n a,
  (∀ k, (x ⊕ y) (n + k + 1) = a)
  → (∀ k, fd2n y (n + k + 1) = a)
  → ∀ k, fd2n x (n + k + 1) = 0.
Proof.
intros * Hxy Hx *.
specialize (Hxy k).
specialize (Hx k).
unfold freal_add_series in Hxy; lia.
Qed.

Theorem le_90_198_mod_100 {r : radix} : ∀ j n s k,
  n = rad * (j + k + 3)
  → s = n - j - 1
  → (rad ^ S k - 1) * rad ^ (s - S k) ≤ (2 * (rad ^ s - 1)) mod rad ^ s.
Proof.
intros * Hn Hs.
specialize radix_ge_2 as Hr.
assert (Hr2s : 2 ≤ rad ^ s). {
  destruct s.
  -rewrite Hn in Hs.
   destruct rad; [ easy | simpl in Hs; flia Hs ].
  -simpl.
   replace 2 with (2 * 1) by flia.
   apply Nat.mul_le_mono; [ easy | ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
rewrite Nat_mod_less_small; [ | flia Hr2s ].
rewrite Nat_sub_sub_swap.
replace (2 * rad ^ s - rad ^ s) with (rad ^ s) by flia.
rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
rewrite <- Nat.pow_add_r.
replace (S k + (s - S k)) with s; cycle 1.
-rewrite Hs, Hn.
 destruct rad; [ easy | simpl; flia ].
-apply Nat.sub_le_mono_l.
 destruct (zerop (s - S k)) as [H4| H4].
 +rewrite Hs, Hn in H4.
  destruct rad; [ easy | simpl in H4; flia H4 ].
 +destruct (s - S k); [ easy | simpl ].
  replace 2 with (2 * 1) by flia.
  apply Nat.mul_le_mono; [ easy | ].
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

Theorem all_x_yz_9_all_yx_9_all_yz_18 {r : radix } : ∀ x y z i,
  (∀ k, (x ⊕ (y + z)) (i + k + 1) = rad - 1)
  → (∀ k, (y ⊕ x) (i + k + 1) = rad - 1)
  → (∀ k, (y ⊕ z) (i + k + 1) = 2 * (rad - 1))
  → False.
Proof.
intros * H2 H3 H4.
specialize (eq_add_series_18_eq_9 _ _ _ H4) as Hzy.
destruct Hzy as (Hy, Hz).
specialize (eq_add_series_eq_l _ _ _ _ H3 Hy) as Hx.
unfold freal_add in H2.
unfold freal_add_series at 1 in H2.
unfold fd2n at 2 in H2; simpl in H2.
remember (y ⊕ z) as yz eqn:Hyz.
assert (H5 : ∀ k, d2n (prop_carr yz) (i + 1 + k) = rad - 1). {
  intros k.
  specialize (H2 k).
  rewrite Hx in H2.
  now replace (i + k + 1) with (i + 1 + k) in H2 by flia.
}
apply not_prop_carr_all_9 in H5; [ easy | ].
intros k; subst yz; apply freal_add_series_le_twice_pred.
Qed.

Theorem all_x_yz_9_all_yz_9_all_x_9 {r : radix} : ∀ x y z i,
  (∀ k, (x ⊕ (y + z)) (i + k + 1) = rad - 1)
  → (∀ k, (y ⊕ z) (i + k + 1) = rad - 1)
  → ∀ k, fd2n x (i + k + 1) = rad - 1.
Proof.
intros * H1 H3.
specialize radix_ge_2 as Hr.
intros.
specialize (H1 k) as H5.
unfold freal_add_series in H5.
unfold freal_add in H5.
unfold fd2n at 2 in H5; simpl in H5.
unfold nat_prop_carr in H5.
remember (y ⊕ z) as yz eqn:Hyz.
rewrite H3 in H5.
rewrite Nat.sub_add in H5; [ | easy ].
destruct (LPO_fst (A_ge_1 yz (i + k + 1))) as [H6| H6].
-simpl in H5.
 rewrite nA_all_9 in H5; cycle 1.
 +intros j Hj.
  replace (i + k + 1 + j) with (i + (k + 1 + j)) by flia.
  apply H3.
 +rewrite Nat.div_small in H5; cycle 1.
  *apply Nat.sub_lt; [ | apply Nat.lt_0_1 ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *rewrite Nat.add_0_r in H5.
   rewrite Nat.mod_same in H5; [ | easy ].
   now rewrite Nat.add_0_r in H5.
-destruct H6 as (j3 & Hjj3 & Hj3); simpl in H5.
 apply A_ge_1_false_iff in Hj3.
 remember (rad * (i + k + 1 + j3 + 3)) as n3 eqn:Hn3.
 remember (n3 - (i + k + 1) - 1) as s3 eqn:Hs3.
 move s3 before n3.
 rewrite nA_all_9 in Hj3; cycle 1.
 +intros.
  replace (i + k + 1 + j) with (i + (k + 1 + j)) by flia.
  apply H3.
 +rewrite Nat.mod_small in Hj3; cycle 1.
  *rewrite <- Hs3.
   apply Nat.sub_lt; [ | apply Nat.lt_0_1 ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *exfalso.
   apply Nat.nle_gt in Hj3; apply Hj3; clear Hj3.
   rewrite <- Hs3.
   rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
   rewrite <- Nat.pow_add_r.
   replace (S j3 + (s3 - S j3)) with s3; cycle 1.
  --rewrite Hs3, Hn3.
    destruct rad; [ easy | simpl; flia ].
  --apply Nat.sub_le_mono_l.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

Theorem A_ge_1_freal_add_series_all_true {r : radix} : ∀ y z i,
  (∀ k, A_ge_1 (y ⊕ z) i k = true)
  → ∀ k, fd2n (y + z) (i + k + 1) = 0.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros H1 *.
(* à simplifier peut-être *)
apply A_ge_1_add_all_true_if in H1; cycle 1.
-intros; apply freal_add_series_le_twice_pred.
-destruct H1 as [H1| [H1| H1]].
 +unfold freal_add, fd2n; simpl.
  unfold nat_prop_carr.
  destruct (LPO_fst (A_ge_1 (y ⊕ z) (i + k + 1))) as
      [H4| H4].
  *simpl.
   rewrite H1, Nat.sub_add; [ | easy ].
   rewrite Nat_mod_add_same_l; [ | easy ].
   remember (rad * (i + k + 1 + 3)) as n2 eqn:Hn2.
   remember (n2 - (i + k + 1) - 1) as s2 eqn:Hs2.
   move s2 before n2.
   assert (Hr2s2 : 2 ≤ rad ^ s2). {
     destruct s2.
     -rewrite Hn2 in Hs2.
      destruct rad; [ easy | simpl in Hs2; flia Hs2 ].
     -simpl.
      replace 2 with (2 * 1) by flia.
      apply Nat.mul_le_mono; [ easy | ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   }
   rewrite nA_all_9; cycle 1.
  --intros j Hj.
    replace (i + k + 1 + j + 1) with (i + (k + j + 1) + 1) by flia.
    apply H1.
  --rewrite <- Hs2.
    rewrite Nat.div_small; [ | flia Hr2s2 ].
    now apply Nat.mod_0_l.
  *exfalso.
   destruct H4 as (j3 & Hjj3 & Hj3).
   apply A_ge_1_false_iff in Hj3.
   remember (rad * (i + k + 1 + j3 + 3)) as n3 eqn:Hn3.
   remember (n3 - (i + k + 1) - 1) as s3 eqn:Hs3.
   move s3 before n3.
   assert (Hr2s3 : 2 ≤ rad ^ s3). {
     destruct s3.
     -rewrite Hn3 in Hs3.
      destruct rad; [ easy | simpl in Hs3; flia Hs3 ].
     -simpl.
      replace 2 with (2 * 1) by flia.
      apply Nat.mul_le_mono; [ easy | ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   }
   apply Nat.nle_gt in Hj3; apply Hj3; clear Hj3.
   rewrite nA_all_9; cycle 1.
  --intros j Hj.
    replace (i + k + 1 + j) with (i + (k + j + 1)) by flia.
    apply H1.
  --rewrite <- Hs3.
    rewrite Nat.mod_small; [ | flia Hr2s3 ].
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
    rewrite <- Nat.pow_add_r.
    replace (S j3 + (s3 - S j3)) with s3; cycle 1.
   ++rewrite Hs3, Hn3.
     destruct rad; [ easy | simpl; flia ].
   ++apply Nat.sub_le_mono_l.
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +unfold freal_add, fd2n; simpl.
  unfold nat_prop_carr.
  destruct (LPO_fst (A_ge_1 (y ⊕ z) (i + k + 1))) as
      [H4| H4].
  *simpl.
   rewrite H1.
   replace (2 * (rad - 1) + 1) with (rad + (rad - 1)) by flia Hr.
   rewrite <- Nat.add_assoc.
   rewrite Nat_mod_add_same_l; [ | easy ].
   rewrite nA_all_18; cycle 1.
  --intros j.
    replace (i + k + 1 + j) with (i + (k + j + 1)) by flia.
    apply H1.
  --remember (rad * (i + k + 1 + 3)) as n3 eqn:Hn3.
    remember (n3 - (i + k + 1) - 1) as s3 eqn:Hs3.
    move s3 before n3.
    assert (Hr2s3 : 2 ≤ rad ^ s3). {
      destruct s3.
      -rewrite Hn3 in Hs3.
       destruct rad; [ easy | simpl in Hs3; flia Hs3 ].
      -simpl.
       replace 2 with (2 * 1) by flia.
       apply Nat.mul_le_mono; [ easy | ].
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    rewrite Nat_div_less_small; [ | flia Hr2s3 ].
    now rewrite Nat.sub_add, Nat.mod_same.
  *exfalso.
   destruct H4 as (j3 & Hjj3 & Hj3).
   apply A_ge_1_false_iff in Hj3.
   remember (rad * (i + k + 1 + j3 + 3)) as n3 eqn:Hn3.
   remember (n3 - (i + k + 1) - 1) as s3 eqn:Hs3.
   move s3 before n3.
   apply Nat.nle_gt in Hj3; apply Hj3; clear Hj3.
   rewrite nA_all_18; cycle 1.
  --intros j.
    replace (i + k + 1 + j) with (i + (k + j + 1)) by flia.
    apply H1.
  --rewrite <- Hs3; now apply (le_90_198_mod_100 (i + k + 1) n3).
 +unfold freal_add, fd2n; simpl.
  unfold nat_prop_carr.
  destruct H1 as (j1 & H1bef & H1whi & H1aft).
  destruct (LPO_fst (A_ge_1 (y ⊕ z) (i + k + 1))) as
      [H4| H4].
  *simpl.
   remember (rad * (i + k + 1 + 3)) as n3 eqn:Hn3.
   remember (n3 - (i + k + 1) - 1) as s3 eqn:Hs3.
   move s3 before n3.
   assert (Hr2s3 : 2 ≤ rad ^ s3). {
     destruct s3.
     -rewrite Hn3 in Hs3.
      destruct rad; [ easy | simpl in Hs3; flia Hs3 ].
     -simpl.
      replace 2 with (2 * 1) by flia.
      apply Nat.mul_le_mono; [ easy | ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   }
   destruct (lt_dec k j1) as [Hkj1| Hkj1].
  --rewrite H1bef; [ | easy ].
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat_mod_add_same_l; [ | easy ].
    rewrite (nA_9_8_all_18 (j1 - S k)); cycle 1.
   ++intros j Hj.
     replace (i + k + 1 + j) with (i + (k + j + 1)) by flia.
     apply H1bef; flia Hj.
   ++now replace (i + k + 1 + (j1 - S k)) with (i + j1) by flia Hkj1.
   ++intros j.
     replace (i + k + 1 + (j1 - S k)) with (i + j1) by flia Hkj1.
     apply H1aft.
   ++rewrite <- Hs3.
     rewrite Nat.div_small; [ now apply Nat.mod_0_l | ].
     destruct (le_dec (i + k + 1 + (j1 - S k) + 1) (n3 - 1)); flia Hr2s3.
  --apply Nat.nlt_ge in Hkj1.
    rewrite nA_all_18; cycle 1.
   ++intros j.
     replace (i + k + 1 + j + 1) with (i + j1 + (k + j - j1) + 2) by
         flia Hkj1.
     apply H1aft.
   ++rewrite <- Hs3.
     rewrite Nat_div_less_small; [ | flia Hr2s3 ].
     destruct (eq_nat_dec k j1) as [Hkj1e| Hkj1e].
    **subst k; clear Hkj1.
      rewrite H1whi.
      replace (rad - 2 + 1 + 1) with rad by flia Hr.
      now apply Nat.mod_same.
    **replace (i + k + 1) with (i + j1 + (k - S j1) + 2) by
          flia Hkj1 Hkj1e.
      rewrite H1aft.
      replace (2 * (rad - 1) + 1 + 1) with (2 * rad) by flia Hr.
      now rewrite Nat.mod_mul.
  *destruct H4 as (j3 & Hjj3 & Hj3); simpl.
   (* after i+j1+1, y=9, z=9 and x=9 *)
   exfalso; apply A_ge_1_false_iff in Hj3.
   apply Nat.nle_gt in Hj3; apply Hj3; clear Hj3.
   remember (rad * (i + k + 1 + j3 + 3)) as n3 eqn:Hn3.
   remember (n3 - (i + k + 1) - 1) as s3 eqn:Hs3.
   move s3 before n3.
   assert (Hr2s3 : 2 ≤ rad ^ s3). {
     destruct s3.
     -rewrite Hn3 in Hs3.
      destruct rad; [ easy | simpl in Hs3; flia Hs3 ].
     -simpl.
      replace 2 with (2 * 1) by flia.
      apply Nat.mul_le_mono; [ easy | ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   }
   assert (Hsj3 : s3 - S j3 ≠ 0). {
     rewrite Hs3, Hn3.
     destruct rad; [ easy | simpl; flia ].
   }
   rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
   rewrite <- Nat.pow_add_r.
   replace (S j3 + (s3 - S j3)) with s3; cycle 1.
  --rewrite Hs3, Hn3.
    destruct rad; [ easy | simpl; flia ].
  --destruct (lt_dec k j1) as [Hkj1| Hkj1].
   ++rewrite (nA_9_8_all_18 (j1 - S k)); cycle 1.
    **intros j Hj.
      replace (i + k + 1 + j) with (i + (k + j + 1)) by flia.
      apply H1bef; flia Hj.
    **now replace (i + k + 1 + (j1 - S k)) with (i + j1) by flia Hkj1.
    **intros j.
      replace (i + k + 1 + (j1 - S k)) with (i + j1) by flia Hkj1.
      apply H1aft.
    **rewrite <- Hs3.
      replace (i + k + 1 + (j1 - S k) + 1) with (i + j1 + 1) by flia Hkj1.
      rewrite Nat.mod_small; cycle 1.
    ---destruct (le_dec (i + j1 + 1) (n3 - 1)); flia Hr2s3.
    ---apply Nat.sub_le_mono_l.
       destruct (le_dec (i + j1 + 1) (n3 - 1)) as [H4| H4].
     +++destruct (s3 - S j3); [ easy | simpl ].
        replace 2 with (2 * 1) by flia.
        apply Nat.mul_le_mono; [ easy | ].
        now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
     +++now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   ++apply Nat.nlt_ge in Hkj1.
     rewrite nA_all_18; cycle 1.
    **intros j.
      replace (i + k + 1 + j + 1) with (i + j1 + (k + j - j1) + 2) by
          flia Hkj1.
      apply H1aft.
    **rewrite <- Hs3.
      replace (2 * (rad ^ s3 - 1)) with (rad ^ s3 + (rad ^ s3 - 2)) by
          flia Hr2s3.
      rewrite Nat_mod_add_same_l; [ | flia Hr2s3 ].
      rewrite Nat.mod_small; [ | flia Hr2s3 ].
      apply Nat.sub_le_mono_l.
      destruct (s3 - S j3); [ easy | simpl ].
      replace 2 with (2 * 1) by flia.
      apply Nat.mul_le_mono; [ easy | ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

Theorem add_assoc_case_11_11 {r : radix} : ∀ x y z i n1 s1,
  n1 = rad * (i + 3)
  → s1 = n1 - i - 1
  → (∀ k, (x ⊕ (y + z)) (i + k + 1) = rad - 1)
  → (∀ k, (z ⊕ (y + x)) (i + k + 1) = rad - 1)
  → (∀ k, A_ge_1 (y ⊕ z) i k = true)
  → (∀ k, A_ge_1 (y ⊕ x) i k = true)
  → (dig (freal x i) +
       ((y ⊕ z) i + 1 + nA i n1 (y ⊕ z) / rad ^ s1) mod rad) mod rad =
    (dig (freal z i) +
       ((y ⊕ x) i + 1 + nA i n1 (y ⊕ x) / rad ^ s1) mod rad) mod rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hn1 Hs1 H1 H2 H3 H4.
assert (Hr2s1 : 2 ≤ rad ^ s1). {
  destruct s1.
  -rewrite Hn1 in Hs1.
   destruct rad; [ easy | simpl in Hs1; flia Hs1 ].
  -simpl.
   replace 2 with (2 * 1) by flia.
   apply Nat.mul_le_mono; [ easy | ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
apply A_ge_1_add_all_true_if in H4; cycle 1.
-intros; apply freal_add_series_le_twice_pred.
-rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
 rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
 unfold freal_add_series at 1 3.
 do 6 rewrite Nat.add_assoc.
 do 2 rewrite fold_fd2n.
 replace (fd2n z i + fd2n y i + fd2n x i) with
     (fd2n x i + fd2n y i + fd2n z i) by flia.
 rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
 rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
 f_equal; f_equal.
 apply A_ge_1_add_all_true_if in H3; cycle 1.
 +intros; apply freal_add_series_le_twice_pred.
 +destruct H3 as [H3| [H3| H3]].
  *rewrite nA_all_9; [ | intros; apply H3 ].
   destruct H4 as [H4| [H4| H4]].
  --rewrite nA_all_9; [ easy | intros; apply H4 ].
  --exfalso; now apply (all_x_yz_9_all_yx_9_all_yz_18 z y x i).
  --destruct H4 as (j & Hjbef & Hjwhi & Hjaft).
    rewrite <- Hs1.
    rewrite Nat.div_small; [ | flia Hr2s1 ].
    rewrite (nA_9_8_all_18 j); [ | easy | easy | easy ].
    rewrite <- Hs1.
    destruct (le_dec (i + j + 1) (n1 - 1)) as [H4| H4].
   ++rewrite Nat.div_small; [ easy | flia Hr2s1 ].
   ++rewrite Nat.div_small; [ easy | flia Hr2s1 ].
  *rewrite nA_all_18; [ | apply H3 ].
   rewrite <- Hs1.
   rewrite Nat_div_less_small; [ | flia Hr2s1 ].
   destruct H4 as [H4| [H4| H4]].
  --exfalso; now apply (all_x_yz_9_all_yx_9_all_yz_18 x y z i).
  --rewrite nA_all_18; [ | apply H4 ].
    rewrite <- Hs1.
    rewrite Nat_div_less_small; [ easy | flia Hr2s1 ].
  --exfalso.
    destruct H4 as (j2 & H2bef & H2whi & H2aft).
    specialize (eq_add_series_18_eq_9 _ _ _ H3) as (Hy, _).
    unfold freal_add_series in H2whi.
    rewrite Hy in H2whi; flia Hr H2whi.
  *destruct H3 as (j1 & H1bef & H1whi & H1aft).
   rewrite (nA_9_8_all_18 j1); [ | easy | easy | easy ].
   rewrite <- Hs1.
   rewrite Nat.div_small.
  --destruct H4 as [H4| [H4| H4]].
   ++rewrite nA_all_9; [ | intros; apply H4 ].
     rewrite <- Hs1.
     rewrite Nat.div_small; [ easy | flia Hr2s1 ].
   ++exfalso.
     apply eq_add_series_18_eq_9 in H4.
     destruct H4 as (Hy & _).
     unfold freal_add_series in H1whi.
     rewrite Hy in H1whi; flia Hr H1whi.
   ++destruct H4 as (j2 & H2bef & H2whi & H2aft).
     rewrite (nA_9_8_all_18 j2); [ | easy | easy | easy ].
     rewrite <- Hs1.
     destruct (le_dec (i + j2 + 1) (n1 - 1)) as [H3| H3].
    **rewrite Nat.div_small; [ easy | flia Hr2s1 ].
    **rewrite Nat.div_small; [ easy | flia Hr2s1 ].
  --destruct (le_dec (i + j1 + 1) (n1 - 1)); flia Hr2s1.
Qed.

Theorem add_assoc_case_11_12 {r : radix} :  ∀ j2 x y z i n1 s1 n2 s2,
  n1 = rad * (i + 3)
  → s1 = n1 - i - 1
  → n2 = rad * (i + j2 + 3)
  → s2 = n2 - i - 1
  → (∀ k, fd2n x (i + k + 1) = rad - 1)
  → (∀ k, A_ge_1 (y ⊕ z) i k = true)
  → A_ge_1 (y ⊕ x) i j2 = false
  → (dig (freal x i) +
       ((y ⊕ z) i + 1 + nA i n1 (y ⊕ z) / rad ^ s1) mod rad) mod rad =
    (dig (freal z i) +
       ((y ⊕ x) i + nA i n2 (y ⊕ x) / rad ^ s2) mod rad) mod rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hn1 Hs1 Hn2 Hs2 Hx H3 Hj2.
assert (Hr2s1 : 2 ≤ rad ^ s1). {
  destruct s1.
  -rewrite Hn1 in Hs1.
   destruct rad; [ easy | simpl in Hs1; flia Hs1 ].
  -simpl.
   replace 2 with (2 * 1) by flia.
   apply Nat.mul_le_mono; [ easy | ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
apply A_ge_1_false_iff in Hj2.
rewrite <- Hn2, <- Hs2 in Hj2.
assert (Hr2s2 : 2 ≤ rad ^ s2). {
  destruct s2.
  -rewrite Hn2 in Hs2.
   destruct rad; [ easy | simpl in Hs2; flia Hs2 ].
  -simpl.
   replace 2 with (2 * 1) by flia.
   apply Nat.mul_le_mono; [ easy | ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
unfold freal_add_series at 1 3.
do 5 rewrite Nat.add_assoc.
do 2 rewrite fold_fd2n.
replace (fd2n z i + fd2n y i + fd2n x i) with
  (fd2n x i + fd2n y i + fd2n z i) by flia.
rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
apply A_ge_1_add_all_true_if in H3; cycle 1.
-intros; apply freal_add_series_le_twice_pred.
-destruct H3 as [H3| [H3| H3]].
 +rewrite nA_all_9; [ | intros; apply H3 ].
  rewrite <- Hs1.
  rewrite Nat.div_small; [ | flia Hr2s1 ].
  rewrite Nat.add_0_r.
  destruct (lt_dec (nA i n2 (y ⊕ x)) (rad ^ s2)) as [H4| H4].
  *exfalso.
   rewrite Nat.mod_small in Hj2; [ | easy ].
   apply Nat.nle_gt in Hj2; apply Hj2; clear Hj2.
   apply le_trans with (m := nA i n2 (fd2n x)).
  --rewrite nA_all_9; [ | intros j Hj; apply Hx ].
    rewrite <- Hs2.
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
    rewrite <- Nat.pow_add_r.
    replace (S j2 + (s2 - S j2)) with s2; cycle 1.
   ++rewrite Hs2, Hn2.
     destruct rad; [ easy | simpl; flia ].
   ++apply Nat.sub_le_mono_l.
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  --unfold nA.
    apply (@summation_le_compat _ nat_ord_ring).
    intros j Hj; simpl; unfold Nat.le.
    apply Nat.mul_le_mono_r.
    unfold freal_add_series.
    flia.
  *rewrite Nat_div_less_small; [ easy | ].
   apply Nat.nlt_ge in H4.
   split; [ easy | rewrite Hs2; apply nA_freal_add_series_lt ].
 +exfalso.
  specialize (eq_add_series_18_eq_9 _ _ _ H3) as (Hy, Hz).
  apply Nat.nle_gt in Hj2; apply Hj2; clear Hj2.
  rewrite nA_all_18; cycle 1.
  *intros; unfold freal_add_series; rewrite Hx, Hy; flia.
  *rewrite <- Hs2; now apply (le_90_198_mod_100 i n2).
 +destruct H3 as (j1 & H1bef & H1whi & H1aft).
  rewrite (nA_9_8_all_18 j1); [ | easy | easy | easy ].
  rewrite <- Hs1.
  rewrite Nat.div_small; cycle 1.
  *destruct (le_dec (i + j1 + 1) (n1 - 1)); flia Hr2s1.
  *rewrite Nat.add_0_r, Nat.mod_1_l; [ | easy ].
   destruct (lt_dec (nA i n2 (y ⊕ x)) (rad ^ s2)) as [H3| H3].
  --exfalso.
    rewrite Nat.mod_small in Hj2; [ | easy ].
    apply Nat.nle_gt in Hj2; apply Hj2; clear Hj2.
    apply (le_trans _ (nA i n2 (fd2n x))).
   ++rewrite nA_all_9; [ | easy ].
     rewrite <- Hs2.
     rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
     rewrite <- Nat.pow_add_r.
     replace (S j2 + (s2 - S j2)) with s2; cycle 1.
    **rewrite Hs2, Hn2.
      destruct rad; [ easy | simpl; flia ].
    **apply Nat.sub_le_mono_l.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   ++unfold nA.
     apply (@summation_le_compat _ nat_ord_ring).
     intros j Hj; simpl; unfold Nat.le.
     apply Nat.mul_le_mono_r.
     unfold freal_add_series; flia.
  --apply Nat.nlt_ge in H3.
    rewrite Nat_div_less_small; [ now rewrite Nat.mod_1_l | ].
    split; [ easy | rewrite Hs2; apply nA_freal_add_series_lt ].
Qed.

Theorem not_all_18_x_yz {r : radix} : ∀ x y z i,
  ¬ ∀ k, (x ⊕ (y + z)) (i + k + 1) = 2 * (rad - 1).
Proof.
intros * H1.
specialize (eq_add_series_18_eq_9 _ _ _ H1) as (_, H2).
unfold "+"%F, fd2n in H2; simpl in H2.
specialize (not_prop_carr_all_9 (y ⊕ z)) as H; unfold d2n in H.
apply H with (n := i + 1); intros k.
-apply freal_add_series_le_twice_pred.
-rewrite Nat.add_shuffle0; apply H2.
Qed.

(* faux: car prop_carr fabrique les chiffres, donc modulo rad
Theorem nA_series_add_le_add {r : radix} : ∀ x y i n,
  nA i n (x ⊕ y) ≤ nA i n (fd2n (x + y)).
Proof.
intros.
change (nA i n (x ⊕ y) ≤ nA i n (d2n (prop_carr (x ⊕ y)))).
*)

Theorem add_assoc_case_11 {r : radix} : ∀ x y z i,
  (∀ k, (x ⊕ (y + z)) (i + k + 1) = rad - 1)
  → (∀ k, (z ⊕ (y + x)) (i + k + 1) = rad - 1)
  → ((x ⊕ (y + z)) i) mod rad = ((z ⊕ (y + x)) i) mod rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros H1 H2.
unfold freal_add_series.
unfold freal_add, fd2n; simpl.
unfold nat_prop_carr.
destruct (LPO_fst (A_ge_1 (y ⊕ z) i)) as [H3| H3].
-simpl.
 destruct (LPO_fst (A_ge_1 (y ⊕ x) i)) as [H4| H4].
 +now simpl; apply add_assoc_case_11_11.
 +destruct H4 as (j2 & Hjj2 & Hj2); simpl.
  apply (add_assoc_case_11_12 j2); try easy.
  intros k.
  specialize (H1 k) as H5.
  unfold freal_add_series in H5.
  rewrite A_ge_1_freal_add_series_all_true in H5; [ | easy ].
  now rewrite Nat.add_0_r in H5.
-destruct H3 as (j1 & Hjj1 & Hj1); simpl.
 destruct (LPO_fst (A_ge_1 (y ⊕ x) i)) as [H4| H4].
 +simpl; symmetry.
  apply (add_assoc_case_11_12 j1); try easy.
  intros k.
  specialize (H2 k) as H5.
  unfold freal_add_series in H5.
  rewrite A_ge_1_freal_add_series_all_true in H5; [ | easy ].
  now rewrite Nat.add_0_r in H5.
 +destruct H4 as (j2 & Hjj2 & Hj2); simpl.
  rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
  rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
  unfold freal_add_series at 1 3.
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
   ++split; [ easy | rewrite Hs2; apply nA_freal_add_series_lt ].
   ++move Hn1 before s2; move Hs1 before Hn1.
     move Hn2 before Hs1; move Hs2 before Hn2.
     move Hr2s1 before Hs2; move Hr2s2 before Hr2s1.
     move Hjj2 before Hjj1.
     apply Nat.lt_sub_lt_add_r in Hj2.
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
             intros; apply freal_add_series_le_twice_pred.
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
             intros; apply freal_add_series_le_twice_pred.
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
           intros k; apply freal_add_series_le_twice_pred.
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
     rewrite nA_freal_add_series in Hj1', Hj2', H3', H4', H1', H2'.
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
rewrite nA_freal_add_series, Nat.add_comm in H4.
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
  --split; [ easy | rewrite Hs1; apply nA_freal_add_series_lt ].
  --destruct (lt_dec (nA i n2 (y ⊕ x)) (rad ^ s2)) as [H4| H4].
   ++exfalso.
     ... (* same as above, I guess, by symmetry between x and z *)
   ++apply Nat.nlt_ge in H4.
     rewrite Nat_div_less_small; [ easy | ].
     split; [ easy | rewrite Hs2; apply nA_freal_add_series_lt ].
...
*)

Theorem freal_add_assoc {r : radix} : ∀ x y z,
  freal_norm_eq (x + (y + z)) ((x + y) + z).
Proof.
intros.
specialize radix_ge_2 as Hr.
specialize (freal_add_comm (x + y) z) as H.
rewrite H; clear H.
specialize (freal_add_comm x y) as H.
rewrite H; clear H.
unfold freal_norm_eq.
intros i.
unfold freal_add at 1 3.
unfold fd2n; simpl.
unfold nat_prop_carr.
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
   ++intros k; apply freal_add_series_le_twice_pred.
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
       split; [ easy | rewrite Hs1; apply nA_freal_add_series_lt ].
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
 +intros k; apply freal_add_series_le_twice_pred.
-destruct H1 as (j1 & Hjj1 & Hj1); simpl.
 destruct (LPO_fst (A_ge_1 (z ⊕ (y + x)) i)) as [H2| H2].
 +simpl.
  apply A_ge_1_add_all_true_if in H2; cycle 1.
  *intros k; apply freal_add_series_le_twice_pred.
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
