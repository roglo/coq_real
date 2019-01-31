(* Reals between 0 and 1; associativity of addition *)

Require Import Utf8 Arith NPeano Psatz PeanoNat.
Require Import Misc Summation Ureal UrealNorm NQ.
Set Nested Proofs Allowed.

Theorem pred_rad_lt_rad {r : radix} : rad - 1 < rad.
Proof.
specialize radix_ge_2 as H; lia.
Qed.

Definition digit_9 {r : radix} := mkdig _ (rad - 1) pred_rad_lt_rad.
Definition ureal_999 {r : radix} := {| ureal i := digit_9 |}.

Definition ureal_shift {r : radix} k x := {| ureal i := ureal x (k + i) |}.
Arguments ureal_shift _ _ x%F.

(*
Require Import Morphisms.
Instance gr_add_morph {r : radix} :
  Proper (ureal_norm_eq ==> ureal_norm_eq ==> iff) ureal_norm_le.
Proof.
assert
  (H : ∀ x1 x2 y1 y2,
   ureal_norm_eq x1 y1
   → ureal_norm_eq x2 y2
   → ureal_norm_le x1 x2
   → ureal_norm_le y1 y2). {
  intros * H1 H2 Hxx.
  unfold ureal_norm_le in Hxx |-*.
  unfold ureal_norm_eq in H1, H2.
  destruct (LPO_fst (has_same_digits y1 y2)) as [Hs| Hs]; [ easy | ].
  destruct Hs as (j & Hjj & Hj).
  rewrite <- H1, <- H2.
  destruct (lt_dec (fd2n x1 j) (fd2n x2 j)) as [Hx12| Hx12]; [ easy | ].
  apply Nat.nlt_ge in Hx12.
  apply has_same_digits_false_iff in Hj; apply Hj; clear Hj.
  destruct (LPO_fst (has_same_digits x1 x2)) as [Hs| Hs].
  +specialize (all_eq_seq_all_eq _ _ Hs) as H3.
   rewrite <- H1, <- H2.
   apply digit_eq_eq; apply H3.
  +destruct Hs as (k & Hjk & Hk).
   destruct (lt_dec (fd2n x1 k) (fd2n x2 k)) as [H3| H3]; [ | easy ].
   destruct (eq_nat_dec j k) as [Hjke| Hjke].
   *subst k.
    now apply Nat.nle_gt in H3.
   *destruct (lt_dec j k) as [Hjk1| Hjk1].
   --specialize (Hjk _ Hjk1).
     apply has_same_digits_true_iff in Hjk.
     now rewrite <- H1, <- H2.
   --assert (Hjk2 : k < j) by flia Hjke Hjk1.
     specialize (Hjj _ Hjk2).
     apply has_same_digits_true_iff in Hjj.
     rewrite H1, H2, Hjj in H3.
     now apply Nat.lt_irrefl in H3.
}
intros x1 y1 H1 x2 y2 H2.
split; intros.
-now apply (H x1 x2).
-now apply (H y1 y2).
Qed.

Theorem nA_ureal_add_series {r : radix} : ∀ x y i n,
   nA i n (x ⊕ y) = nA i n (fd2n x) + nA i n (fd2n y).
Proof.
intros.
rewrite nA_eq_compat with (v := λ j, fd2n x j + fd2n y j); [ | easy ].
unfold nA.
erewrite summation_eq_compat; cycle 1.
-intros j Hj; apply Nat.mul_add_distr_r.
-apply summation_add_distr.
Qed.

Theorem nA_ureal_add_series_lt {r : radix} : ∀ i n x y,
  nA i n (x ⊕ y) < 2 * rad ^ (n - i - 1).
Proof.
intros.
eapply le_lt_trans.
-apply nA_upper_bound_for_add.
 intros k; apply ureal_add_series_le_twice_pred.
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
 unfold ureal_add_series in Hxy.
 specialize (digit_lt_radix (ureal x (n + k + 1))) as H1.
 specialize (digit_lt_radix (ureal y (n + k + 1))) as H2.
 unfold fd2n in Hxy |-*; lia.
-intros.
 specialize (Hxy k).
 unfold ureal_add_series in Hxy.
 specialize (digit_lt_radix (ureal x (n + k + 1))) as H1.
 specialize (digit_lt_radix (ureal y (n + k + 1))) as H2.
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
unfold ureal_add_series in Hxy; lia.
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
unfold ureal_add in H2.
unfold ureal_add_series at 1 in H2.
unfold fd2n at 2 in H2; simpl in H2.
remember (y ⊕ z) as yz eqn:Hyz.
assert (H5 : ∀ k, d2n (prop_carr yz) (i + 1 + k) = rad - 1). {
  intros k.
  specialize (H2 k).
  rewrite Hx in H2.
  now replace (i + k + 1) with (i + 1 + k) in H2 by flia.
}
apply not_prop_carr_all_9 in H5; [ easy | ].
intros k; subst yz; apply ureal_add_series_le_twice_pred.
Qed.

Theorem A_ge_1_ureal_add_series_all_true {r : radix} : ∀ y z i,
  (∀ k, A_ge_1 (y ⊕ z) i k = true)
  → ∀ k, fd2n (y + z) (i + k + 1) = 0.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros H1 *.
(* à simplifier peut-être *)
apply A_ge_1_add_all_true_if in H1; cycle 1.
-intros; apply ureal_add_series_le_twice_pred.
-destruct H1 as [H1| [H1| H1]].
 +unfold ureal_add, fd2n; simpl.
  unfold nat_prop_carr.
  destruct (LPO_fst (A_ge_1 (y ⊕ z) (i + k + 1))) as
      [H4| H4].
  *simpl.
   rewrite H1.
   rewrite Nat.add_assoc, Nat.add_shuffle0.
   rewrite Nat.sub_add; [ | easy ].
   rewrite Nat_mod_add_same_l; [ | easy ].
   unfold min_n; rewrite Nat.add_0_r.
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
   unfold min_n in Hj3.
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
 +unfold ureal_add, fd2n; simpl.
  unfold nat_prop_carr.
  destruct (LPO_fst (A_ge_1 (y ⊕ z) (i + k + 1))) as
      [H4| H4].
  *simpl.
   rewrite H1, Nat.add_assoc, Nat.add_shuffle0.
   replace (2 * (rad - 1) + 1) with (rad + (rad - 1)) by flia Hr.
   rewrite <- Nat.add_assoc.
   rewrite Nat_mod_add_same_l; [ | easy ].
   rewrite nA_all_18; cycle 1.
  --intros j.
    replace (i + k + 1 + j) with (i + (k + j + 1)) by flia.
    apply H1.
  --unfold min_n; rewrite Nat.add_0_r.
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
    rewrite Nat_div_less_small; [ | flia Hr2s3 ].
    now rewrite Nat.sub_add, Nat.mod_same.
  *exfalso.
   destruct H4 as (j3 & Hjj3 & Hj3).
   apply A_ge_1_false_iff in Hj3.
   unfold min_n in Hj3.
   remember (rad * (i + k + 1 + j3 + 3)) as n3 eqn:Hn3.
   remember (n3 - (i + k + 1) - 1) as s3 eqn:Hs3.
   move s3 before n3.
   apply Nat.nle_gt in Hj3; apply Hj3; clear Hj3.
   rewrite nA_all_18; cycle 1.
  --intros j.
    replace (i + k + 1 + j) with (i + (k + j + 1)) by flia.
    apply H1.
  --rewrite <- Hs3; now apply (le_90_198_mod_100 (i + k + 1) n3).
 +unfold ureal_add, fd2n; simpl.
  unfold nat_prop_carr.
  destruct H1 as (j1 & H1bef & H1whi & H1aft).
  destruct (LPO_fst (A_ge_1 (y ⊕ z) (i + k + 1))) as
      [H4| H4].
  *simpl.
   unfold min_n; rewrite Nat.add_0_r.
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
    rewrite Nat.add_assoc, Nat.add_shuffle0.
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
      replace (rad - 2 + (1 + 1)) with rad by flia Hr.
      now apply Nat.mod_same.
    **replace (i + k + 1) with (i + j1 + (k - S j1) + 2) by
          flia Hkj1 Hkj1e.
      rewrite H1aft.
      replace (2 * (rad - 1) + (1 + 1)) with (2 * rad) by flia Hr.
      now rewrite Nat.mod_mul.
  *destruct H4 as (j3 & Hjj3 & Hj3); simpl.
   (* after i+j1+1, y=9, z=9 and x=9 *)
   exfalso; apply A_ge_1_false_iff in Hj3.
   apply Nat.nle_gt in Hj3; apply Hj3; clear Hj3.
   unfold min_n.
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
  n1 = min_n i 0
  → s1 = n1 - i - 1
  → (∀ k, (x ⊕ (y + z)) (i + k + 1) = rad - 1)
  → (∀ k, (z ⊕ (y + x)) (i + k + 1) = rad - 1)
  → (∀ k, A_ge_1 (y ⊕ z) i k = true)
  → (∀ k, A_ge_1 (y ⊕ x) i k = true)
  → (dig (ureal x i) +
       ((y ⊕ z) i + (nA i n1 (y ⊕ z) / rad ^ s1 + 1)) mod rad) mod rad =
    (dig (ureal z i) +
       ((y ⊕ x) i + (nA i n1 (y ⊕ x) / rad ^ s1 + 1)) mod rad) mod rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hn1 Hs1 H1 H2 H3 H4.
assert (Hr2s1 : 2 ≤ rad ^ s1). {
  destruct s1.
  -rewrite Hn1 in Hs1; unfold min_n in Hs1.
   destruct rad; [ easy | simpl in Hs1; flia Hs1 ].
  -simpl.
   replace 2 with (2 * 1) by flia.
   apply Nat.mul_le_mono; [ easy | ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
apply A_ge_1_add_all_true_if in H4; cycle 1.
-intros; apply ureal_add_series_le_twice_pred.
-rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
 rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
 unfold ureal_add_series at 1 3.
 do 6 rewrite Nat.add_assoc.
 do 2 rewrite fold_fd2n.
 replace (fd2n z i + fd2n y i + fd2n x i) with
     (fd2n x i + fd2n y i + fd2n z i) by flia.
 rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
 rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
 f_equal; f_equal.
 apply A_ge_1_add_all_true_if in H3; cycle 1.
 +intros; apply ureal_add_series_le_twice_pred.
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
    unfold ureal_add_series in H2whi.
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
     unfold ureal_add_series in H1whi.
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
  n1 = min_n i 0
  → s1 = n1 - i - 1
  → n2 = min_n i j2
  → s2 = n2 - i - 1
  → (∀ k, fd2n x (i + k + 1) = rad - 1)
  → (∀ k, A_ge_1 (y ⊕ z) i k = true)
  → A_ge_1 (y ⊕ x) i j2 = false
  → (dig (ureal x i) +
       ((y ⊕ z) i + (nA i n1 (y ⊕ z) / rad ^ s1 + 1)) mod rad) mod rad =
    (dig (ureal z i) +
       ((y ⊕ x) i + nA i n2 (y ⊕ x) / rad ^ s2) mod rad) mod rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hn1 Hs1 Hn2 Hs2 Hx H3 Hj2.
assert (Hr2s1 : 2 ≤ rad ^ s1). {
  destruct s1.
  -rewrite Hn1 in Hs1.
   unfold min_n in Hs1.
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
   unfold min_n in Hs2.
   destruct rad; [ easy | simpl in Hs2; flia Hs2 ].
  -simpl.
   replace 2 with (2 * 1) by flia.
   apply Nat.mul_le_mono; [ easy | ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
unfold ureal_add_series at 1 3.
do 5 rewrite Nat.add_assoc.
do 2 rewrite fold_fd2n.
replace (fd2n z i + fd2n y i + fd2n x i) with
  (fd2n x i + fd2n y i + fd2n z i) by flia.
rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
apply A_ge_1_add_all_true_if in H3; cycle 1.
-intros; apply ureal_add_series_le_twice_pred.
-destruct H3 as [H3| [H3| H3]].
 +rewrite nA_all_9; [ | intros; apply H3 ].
  rewrite <- Hs1.
  rewrite Nat.div_small; [ | flia Hr2s1 ].
  rewrite Nat.add_0_l.
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
   ++rewrite Hs2, Hn2; unfold min_n.
     destruct rad; [ easy | simpl; flia ].
   ++apply Nat.sub_le_mono_l.
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  --unfold nA.
    apply (@summation_le_compat _ nat_ord_ring).
    intros j Hj; simpl; unfold Nat.le.
    apply Nat.mul_le_mono_r.
    unfold ureal_add_series.
    flia.
  *rewrite Nat_div_less_small; [ easy | ].
   apply Nat.nlt_ge in H4.
   split; [ easy | rewrite Hs2; apply nA_ureal_add_series_lt ].
 +exfalso.
  specialize (eq_add_series_18_eq_9 _ _ _ H3) as (Hy, Hz).
  apply Nat.nle_gt in Hj2; apply Hj2; clear Hj2.
  rewrite nA_all_18; cycle 1.
  *intros; unfold ureal_add_series; rewrite Hx, Hy; flia.
  *rewrite <- Hs2; now apply (le_90_198_mod_100 i n2).
 +destruct H3 as (j1 & H1bef & H1whi & H1aft).
  rewrite (nA_9_8_all_18 j1); [ | easy | easy | easy ].
  rewrite <- Hs1.
  rewrite Nat.div_small; cycle 1.
  *destruct (le_dec (i + j1 + 1) (n1 - 1)); flia Hr2s1.
  *rewrite Nat.add_0_l, Nat.mod_1_l; [ | easy ].
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
    **rewrite Hs2, Hn2; unfold min_n.
      destruct rad; [ easy | simpl; flia ].
    **apply Nat.sub_le_mono_l.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   ++unfold nA.
     apply (@summation_le_compat _ nat_ord_ring).
     intros j Hj; simpl; unfold Nat.le.
     apply Nat.mul_le_mono_r.
     unfold ureal_add_series; flia.
  --apply Nat.nlt_ge in H3.
    rewrite Nat_div_less_small; [ now rewrite Nat.mod_1_l | ].
    split; [ easy | rewrite Hs2; apply nA_ureal_add_series_lt ].
Qed.

Theorem not_all_18_x_yz {r : radix} : ∀ x y z i,
  ¬ ∀ k, (x ⊕ (y + z)) (i + k + 1) = 2 * (rad - 1).
Proof.
intros * H1.
specialize (eq_add_series_18_eq_9 _ _ _ H1) as (_, H2).
unfold "+"%F, fd2n in H2; simpl in H2.
specialize (not_prop_carr_all_9 (y ⊕ z)) as H; unfold d2n in H.
apply H with (i := i + 1); intros k.
-apply ureal_add_series_le_twice_pred.
-rewrite Nat.add_shuffle0; apply H2.
Qed.

Theorem nat_prop_carr_le_2 {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → nat_prop_carr u i ≤ 2.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur.
unfold nat_prop_carr.
destruct (LPO_fst (A_ge_1 u i)) as [H1| H1].
-specialize (A_ge_1_add_all_true_if u i Hur H1) as H.
 destruct H as [H| [H| H]].
 +rewrite Nat.div_small; [ flia | ].
  rewrite nA_all_9; [ | easy ].
  apply Nat.sub_lt; [ | apply Nat.lt_0_1 ].
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +rewrite nA_all_18; [ | easy ].
  rewrite Nat_div_less_small; [ easy | ].
  remember (min_n i 0 - i - 1) as s eqn:Hs.
  split.
  *rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   replace (2 * rad ^ s) with (rad ^ s + rad ^ s) by flia.
   rewrite <- Nat.add_sub_assoc; [ flia | ].
   destruct s.
  --unfold min_n in Hs.
    destruct rad; [ easy | simpl in Hs; flia Hs ].
  --simpl; replace 2 with (2 * 1) by flia.
    apply Nat.mul_le_mono; [ easy | ].
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   apply Nat.sub_lt; [ | apply Nat.lt_0_2 ].
   replace 2 with (2 * 1) at 1 by flia.
   apply Nat.mul_le_mono_l.
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +destruct H as (j & Hbef & Hwhi & Haft).
  rewrite (nA_9_8_all_18 j); [ | easy | easy | easy ].
  rewrite Nat.div_small; [ flia | ].
  apply Nat.sub_lt.
  *destruct (le_dec (i + j + 1) (min_n i 0 - 1)) as [H| H].
  --remember (min_n i 0 - i - 1) as s eqn:Hs.
    destruct s.
   ++unfold min_n in Hs.
     destruct rad; [ easy | simpl in Hs; flia Hs ].
   ++simpl; replace 2 with (2 * 1) by flia.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  --now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *destruct (le_dec (i + j + 1) (min_n i 0 - 1)); flia.
-destruct H1 as (j & Hjj & Hj).
 remember (min_n i j) as n eqn:Hs.
 destruct (lt_dec (nA i n u) (rad ^ (n - i - 1))) as [H1| H1].
 +rewrite Nat.div_small; [ apply Nat.le_0_2 | easy ].
 +rewrite Nat_div_less_small; [ now apply Nat.le_succ_r; left | ].
  apply Nat.nlt_ge in H1.
  split; [ easy | ].
  specialize (nA_upper_bound_for_add u i n Hur) as H.
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H.
  eapply Nat.le_lt_trans; [ apply H | ].
  apply Nat.sub_lt; [ | apply Nat.lt_0_2 ].
  replace 2 with (2 * 1) at 1 by flia.
  apply Nat.mul_le_mono_l.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.
*)

Definition P {r : radix} u := d2n (prop_carr u).
Definition add_series (u v : nat → nat) i := u i + v i.
Notation "u ⊕ v" := (add_series u v) (at level 50).
Definition M {r : radix} (u : nat → _) i := u i mod rad.

Theorem A_additive {r : radix} : ∀ i n u v,
  A i n (u ⊕ v) = (A i n u + A i n v)%NQ.
Proof.
intros.
unfold A, "⊕".
rewrite summation_eq_compat with
  (h := λ j, (u j // rad ^ (j - i) + v j // rad ^ (j - i))%NQ);
  cycle 1. {
  intros; apply NQpair_add_l.
}
now rewrite summation_add_distr.
Qed.

Definition num_A {r : radix} (rg := nat_ord_ring) i n u :=
  Σ (j = i + 1, n - 1), u j * rad ^ (n - j - 1).
Definition den_A {r : radix} i n := rad ^ (n - i - 1).

Theorem A_num_den {r : radix} : ∀ i n u,
  A i n u = (num_A i n u // den_A i n)%NQ.
Proof.
intros.
unfold A, num_A, den_A.
rewrite NQsum_pair.
apply summation_eq_compat.
intros j Hj.
rewrite NQpair_mul_r.
rewrite NQpow_pair_r; [ | easy | flia Hj ].
rewrite NQmul_pair_den_num; [ | easy ].
f_equal; f_equal.
flia Hj.
Qed.

Theorem fA_ge_1_ε_999 {r : radix} : ∀ u i,
  (∀ k, fA_ge_1_ε u i k = true)
  → P u (i + 1) = rad - 1.
Proof.
intros * Hu *.
specialize radix_ge_2 as Hr.
unfold P, prop_carr; cbn.
unfold carry.
destruct (LPO_fst (fA_ge_1_ε u (i + 1))) as [H1| H1]. 2: {
  destruct H1 as (j & Hj & H1).
  rewrite A_ge_1_add_r_true_if in H1; [ easy | apply Hu ].
}
remember (min_n (i + 1) 0) as n eqn:Hn.
apply Nat.le_antisymm. {
  rewrite Nat.sub_1_r.
  now apply Nat.lt_le_pred, Nat.mod_upper_bound.
}
apply Nat.nlt_ge; intros H2.
specialize (Hu 1) as H3.
apply A_ge_1_true_iff in H3.
remember (min_n i 1) as m eqn:Hm.
move m before n; move Hm before Hn.
assert (H : n = m) by (rewrite Hn, Hm; unfold min_n; ring).
clear Hm; subst m.
apply NQnlt_ge in H3; apply H3; clear H3.
rewrite A_split_first. 2: {
  subst n; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
}
replace (u (i + 1) + NQintg (A (i + 1) n u)) with
  (NQintg (u (i + 1)%nat // 1 + A (i + 1) n u))%NQ in H2. 2: {
  rewrite NQintg_add; [ | | easy ]. 2: {
    replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQle_pair; [ easy | easy | flia ].
  }
  rewrite NQintg_pair; [ | easy ].
  rewrite Nat.div_1_r, <- Nat.add_assoc; f_equal.
  rewrite NQfrac_of_nat, NQadd_0_l, NQintg_NQfrac, Nat.add_0_r.
  easy.
}
rewrite <- Nat.add_1_r.
remember (u (i + 1)%nat // rad)%NQ as x eqn:Hx.
rewrite <- NQmul_1_r in Hx.
rewrite NQmul_pair in Hx; [ | easy | easy ].
rewrite Nat.mul_comm in Hx.
rewrite <- NQmul_pair in Hx; [ | easy | easy ].
rewrite NQmul_comm in Hx; subst x.
rewrite <- NQmul_add_distr_r.
remember (u (i + 1)%nat // 1 + A (i + 1) n u)%NQ as x.
remember x as y eqn:Hy.
rewrite NQnum_den in Hy. 2: {
  subst x y.
  replace 0%NQ with (0 + 0)%NQ by easy.
  apply NQadd_le_mono; [ | easy ].
  replace 0%NQ with (0 // 1)%NQ by easy.
  apply NQle_pair; [ easy | easy | flia ].
}
subst y.
remember (NQnum x) as xn.
remember (NQden x) as xd.
move xd before xn.
assert (Hxd : xd ≠ 0) by (subst xd; apply NQden_neq_0).
move H2 at bottom.
rewrite NQintg_pair in H2; [ | easy ].
rewrite NQmul_pair; [ | easy | easy ].
rewrite Nat.mul_1_r, NQfrac_pair.
rewrite NQsub_pair_pos; [ | easy | pauto | ]. 2: {
  do 2 rewrite Nat.mul_1_l.
  now apply Nat_pow_ge_1.
}
do 2 rewrite Nat.mul_1_l.
apply NQlt_pair; [ now apply Nat.neq_mul_0 | pauto | ].
rewrite Nat.mul_shuffle0, Nat.pow_2_r, Nat.mul_assoc.
apply Nat.mul_lt_mono_pos_r; [ easy | ].
rewrite Nat.mod_mul_r; [ | easy | easy ].
(**)
apply (lt_le_trans _ ((xd + xd * (rad - 2)) * rad)).
-apply Nat.mul_lt_mono_pos_r; [ easy | ].
 apply Nat.add_lt_le_mono; [ now apply Nat.mod_upper_bound | ].
 apply Nat.mul_le_mono_pos_l; [ now apply Nat.neq_0_lt_0 | ].
 replace (rad - 2) with (pred (rad - 1)) by flia.
 now apply Nat.lt_le_pred.
-replace xd with (xd * 1) at 1 by flia.
 rewrite <- Nat.mul_add_distr_l.
 rewrite <- Nat.mul_assoc.
 apply Nat.mul_le_mono_pos_l; [ now apply Nat.neq_0_lt_0 | ].
 replace (1 + (rad - 2)) with (rad - 1) by flia Hr.
 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
 now apply Nat.sub_le_mono_l.
Qed.

Theorem all_9_fA_ge_1_ε {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) = rad - 1)
  → ∀ k, fA_ge_1_ε u i k = true.
Proof.
intros * Hur *.
specialize radix_ge_2 as Hr.
apply A_ge_1_true_iff.
rewrite A_all_9; [ | intros j Hj; apply Hur ].
rewrite NQfrac_small. 2: {
  split.
  -apply NQle_add_le_sub_l.
   rewrite NQadd_0_l.
   apply NQle_pair; [ pauto | easy | ].
   do 2 rewrite Nat.mul_1_r.
   now apply Nat_pow_ge_1.
  -apply NQsub_lt.
   replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | pauto | flia ].
}
apply NQsub_le_mono; [ apply NQle_refl | ].
apply NQle_pair; [ pauto | pauto | ].
rewrite Nat.mul_1_l, Nat.mul_1_r.
apply Nat.pow_le_mono_r; [ easy | ].
unfold min_n.
destruct rad; [ easy | cbn; flia ].
Qed.

Theorem all_fA_ge_1_ε_P_999 {r : radix} : ∀ u i,
  (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k, P u (i + k + 1) = rad - 1.
Proof.
intros * Hu *.
apply fA_ge_1_ε_999.
intros l.
apply A_ge_1_add_r_true_if, Hu.
Qed.

Theorem M_upper_bound {r : radix} : ∀ u i, M u i < rad.
Proof.
intros.
unfold M.
now apply Nat.mod_upper_bound.
Qed.

Theorem A_M_upper_bound {r : radix} : ∀ u i n, (A i n (M u) < 1)%NQ.
Proof.
intros.
destruct (le_dec (i + 1) (n - 1)) as [H1| H1].
-eapply NQle_lt_trans.
 +apply A_dig_seq_ub; [ | easy ].
  intros j Hj; apply M_upper_bound.
 +apply NQsub_lt.
  replace 0%NQ with (0 // 1)%NQ by easy.
  apply NQlt_pair; [ easy | pauto | pauto ].
-apply Nat.nle_gt in H1.
 unfold A.
 now rewrite summation_empty.
Qed.

Theorem NQintg_A_M {r : radix} : ∀ i n u, NQintg (A i n (M u)) = 0.
Proof.
intros.
apply NQintg_small.
split; [ easy | apply A_M_upper_bound ].
Qed.

Theorem NQintg_P_M {r : radix} : ∀ i n u, NQintg (A i n (P u)) = 0.
Proof.
intros.
apply NQintg_small.
split; [ easy | apply A_M_upper_bound ].
Qed.

Theorem NQfrac_A_M {r : radix} : ∀ i n u, NQfrac (A i n (M u)) = A i n (M u).
Proof.
intros.
apply NQfrac_small.
split; [ easy | ].
apply A_M_upper_bound.
Qed.

Theorem NQfrac_P_M {r : radix} : ∀ i n u, NQfrac (A i n (P u)) = A i n (P u).
Proof.
intros.
apply NQfrac_small.
split; [ easy | ].
apply A_M_upper_bound.
Qed.

(* faux
Theorem P_add_999 {r : radix} : ∀ i u v,
  (∀ k, v (i + k + 1) = rad - 1)
  → ∀ k, P (u ⊕ v) (i + k + 1) = P u (i + k + 1).
Proof.
intros * Hv *.
specialize radix_ge_2 as Hr.
unfold P, d2n, prop_carr; cbn.
unfold "⊕" at 1.
rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
rewrite Hv.
unfold carry.
remember (min_n (i + k + 1) 0) as n eqn:Hn.
assert (Hin : i + k + 2 ≤ n - 1). {
  rewrite Hn; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
}
set (s := n - (i + k + 1) - 1).
assert (HAv : (A (i + k + 1) n v = 1 - 1 // rad ^ s)%NQ). {
  unfold A.
  rewrite summation_shift; [ | flia Hin ].
  rewrite summation_eq_compat with
    (h := λ j, ((rad - 1) // rad * 1 // rad ^ j)%NQ). 2: {
    intros j Hj.
    rewrite NQmul_pair; [ | easy | pauto ].
    replace (i + k + 1 + 1 + j - (i + k + 1)) with (1 + j) by flia.
    rewrite Nat.pow_add_r, Nat.pow_1_r, Nat.mul_1_r; f_equal.
    replace (i + k + 1 + 1 + j) with (i + (k + j + 1) + 1) by flia.
    apply Hv.
  }
  rewrite <- summation_mul_distr_l.
  replace (n - 1 - (i + k + 1 + 1)) with (n - i - k - 3) by flia.
  rewrite NQpower_summation; [ | easy ].
  rewrite NQmul_pair; [ | easy | ]. 2: {
    apply Nat.neq_mul_0.
    split; [ pauto | flia Hr ].
  }
  rewrite Nat.mul_assoc, Nat.mul_comm.
  rewrite <- NQmul_pair; [ | | flia Hr ]. 2: {
    apply Nat.neq_mul_0; pauto.
  }
  rewrite NQpair_diag, NQmul_1_r; [ | flia Hr ].
  rewrite <- Nat.pow_succ_r; [ | flia Hin ].
  replace (S (n - i - k - 3)) with s by flia Hin.
  rewrite NQsub_pair_pos; [ | easy | pauto | ]. 2: {
    do 2 rewrite Nat.mul_1_l.
    now apply Nat_pow_ge_1.
  }
  now do 2 rewrite Nat.mul_1_l.
}
destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) (i + k + 1))) as [H1| H1].
-destruct (LPO_fst (fA_ge_1_ε u (i + k + 1))) as [H2| H2].
 +rewrite A_additive.
  rewrite NQintg_add; [ | easy | easy ].
  rewrite Nat.add_comm.
  remember (A (i + k + 1) n u) as x eqn:Hx.
  remember (A (i + k + 1) n v) as y eqn:Hy.
  move y before x.
  do 2 rewrite <- Nat.add_assoc.
  replace (NQintg x) with (NQintg x + 0) at 2 by apply Nat.add_0_r.
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  f_equal; f_equal.
  rewrite Nat.mod_0_l; [ | easy ].
  rewrite Nat.add_assoc.
  assert (H4 : NQintg y = 0). {
    apply NQintg_small.
    subst y; split; [ easy | ].
    rewrite HAv.
    apply NQsub_lt.
    replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQlt_pair; [ easy | pauto | flia ].
  }
  rewrite H4, Nat.add_0_l.
  rewrite NQintg_add_frac.
  destruct (NQlt_le_dec (NQfrac x + NQfrac y) 1) as [H5| H5]. 2: {
    rewrite Nat.add_comm, Nat.sub_add; [ | easy ].
    now apply Nat.mod_same.
  }
  exfalso.
  specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H2 0) as AA2.
  rewrite <- Hn, <- Hx, Nat.pow_1_r in AA2.
  apply NQnlt_ge in AA2; apply AA2; clear AA2.
  assert (H6 : (NQfrac y = 1 - 1 // rad ^ s)%NQ). {
    rewrite NQfrac_of_intg; [ | now rewrite Hy ].
    now rewrite H4, NQsub_0_r.
  }
  apply NQlt_add_lt_sub_r.
  eapply NQle_lt_trans; [ | apply H5 ].
  apply NQadd_le_mono_l.
  rewrite H6.
  apply NQle_add_le_sub_r.
  rewrite NQadd_pair; [ | pauto | easy ].
  rewrite Nat.mul_1_l, Nat.mul_1_r.
  apply NQle_pair; [ | easy | ].
  *apply Nat.neq_mul_0; pauto.
  *do 2 rewrite Nat.mul_1_r.
   destruct (zerop s) as [H7| H7].
  --exfalso; unfold s in H7.
    rewrite Hn in H7; unfold min_n in H7.
    destruct rad; [ easy | cbn in H7; flia H7 ].
  --destruct s; [ flia H7 | cbn ].
    replace rad with (rad * 1) at 1 by flia.
    rewrite <- Nat.mul_add_distr_l, Nat.mul_comm.
    apply Nat.mul_le_mono_r.
    destruct s; [ cbn; flia Hr | cbn ].
    apply Nat.mul_lt_mono_pos_l; [ easy | ].
    replace (rad ^ s) with (1 * rad ^ s) at 1 by flia.
    apply Nat.mul_lt_mono_pos_r; [ | easy ].
    now apply Nat_pow_ge_1.
 +destruct H2 as (j & Hj & Hjj).
...
-destruct H1 as (j & Hj & Hjj).
...
*)

Theorem pre_Hugo_Herbelin_lemma {r : radix} : ∀ i n u v,
  n = min_n i 0
  → (∀ k, fA_ge_1_ε (u ⊕ P v) i k = true)
  → (∀ k, fA_ge_1_ε v i k = true)
  → NQintg (NQfrac (A i n u) + (1 - 1 // rad ^ (n - i - 1))%NQ) =
     NQintg (NQfrac (A i n u) + (1 - 2 // rad ^ (n - i - 1))%NQ).
Proof.
intros * Hn H1 H3.
specialize radix_ge_2 as Hr.
specialize (all_fA_ge_1_ε_P_999 _ _ H3) as A3.
assert (H4 : (0 ≤ 1 - 2 // rad ^ (n - i - 1))%NQ). {
  rewrite NQsub_pair_pos; [ | easy | pauto | ]. 2: {
    do 2 rewrite Nat.mul_1_l.
    remember (n - i - 1) as s eqn:Hs.
    destruct s.
    -rewrite Hn in Hs; unfold min_n in Hs.
     rewrite Nat.add_0_r, Nat.mul_add_distr_l in Hs.
     destruct rad; [ easy | cbn in Hs; flia Hs ].
    -cbn.
     replace 2 with (2 * 1) by flia.
     apply Nat.mul_le_mono; [ easy | now apply Nat_pow_ge_1 ].
  }
  do 2 rewrite Nat.mul_1_l.
  replace 0%NQ with (0 // 1)%NQ by easy.
  apply NQle_pair; [ easy | pauto | ].
  rewrite Nat.mul_0_l, Nat.mul_1_l; flia.
}
set (s := n - i - 1) in H4 |-*.
remember (NQfrac (A i n u)) as x eqn:Hx.
destruct (NQlt_le_dec x (1 // rad ^ s)%NQ) as [H5| H5].
-rewrite NQintg_small. 2: {
   split.
   -replace 0%NQ with (0 + 0)%NQ by easy.
    subst x; apply NQadd_le_mono; [ easy | ].
    eapply NQle_trans; [ apply H4 | ].
    apply NQsub_le_mono; [ apply NQle_refl | ].
    apply NQle_pair; [ pauto | pauto | ].
    rewrite Nat.mul_comm; apply Nat.mul_le_mono_l; pauto.
   -rewrite NQadd_comm, <- NQsub_sub_distr.
    apply NQsub_lt, NQlt_add_lt_sub_l.
    now rewrite NQadd_0_r.
 }
 rewrite NQintg_small; [ easy | ]. {
   split.
   -replace 0%NQ with (0 + 0)%NQ by easy.
    now subst x; apply NQadd_le_mono.
   -rewrite NQadd_comm, <- NQsub_sub_distr.
    apply NQsub_lt, NQlt_add_lt_sub_l.
    rewrite NQadd_0_r.
    eapply NQlt_trans; [ apply H5 | ].
    apply NQlt_pair; [ pauto | pauto | ].
    rewrite Nat.mul_comm.
    apply Nat.mul_lt_mono_pos_l; [ | pauto ].
    now apply Nat_pow_ge_1.
 }
-destruct (NQle_lt_dec (2 // rad ^ s) x) as [H6| H6].
 +do 2 rewrite NQadd_sub_assoc.
  rewrite NQadd_comm.
  do 2 rewrite <- NQadd_sub_assoc.
  rewrite NQintg_add_nat_l; [ | now apply NQle_add_le_sub_l ].
  rewrite NQintg_add_nat_l; [ | now apply NQle_add_le_sub_l ].
  rewrite NQintg_small. 2: {
    split; [ now apply NQle_add_le_sub_l | ].
    apply (NQlt_trans _ x); [ | subst x; apply NQfrac_lt_1 ].
    apply NQsub_lt.
    replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQlt_pair; [ easy | pauto | cbn; flia ].
  }
  rewrite NQintg_small; [ easy | ]. {
    split; [ now apply NQle_add_le_sub_l | ].
    apply (NQlt_trans _ x); [ | subst x; apply NQfrac_lt_1 ].
    apply NQsub_lt.
    replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQlt_pair; [ easy | pauto | cbn; flia ].
  }
 +assert (H7 : x = (1 // rad ^ s)%NQ). {
    apply NQle_antisymm; [ | easy ].
    rewrite A_num_den, NQfrac_pair in Hx.
    unfold den_A in Hx.
    fold s in Hx; subst x.
    apply NQle_pair; [ pauto | pauto | ].
    rewrite Nat.mul_comm.
    apply Nat.mul_le_mono_l.
    apply NQlt_pair in H6; [ | pauto | pauto ].
    rewrite Nat.mul_comm in H6.
    apply Nat.mul_lt_mono_pos_l in H6; [ | now apply Nat_pow_ge_1 ].
    now apply Nat.lt_le_pred in H6.
  }
  exfalso; subst x.
  specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H1 0) as AA1.
  rewrite <- Hn, A_additive, Nat.pow_1_r in AA1.
  rewrite NQfrac_add in AA1; [ | pauto | pauto ].
  rewrite H7 in AA1.
  rewrite A_all_9 in AA1; [ | easy ].
  fold s in AA1.
  rewrite (NQfrac_small (1 - 1 // rad ^ s)%NQ) in AA1. 2: {
    split.
    -eapply NQle_trans; [ apply H4 | ].
     apply NQsub_le_mono; [ apply NQle_refl | ].
     apply NQle_pair; [ pauto | pauto | flia ].
    -apply NQsub_lt.
     replace 0%NQ with (0 // 1)%NQ by easy.
     apply NQlt_pair; [ easy | pauto | cbn; flia ].
  }
  rewrite NQadd_comm, NQsub_add, NQfrac_1 in AA1.
  apply NQnlt_ge in AA1; apply AA1.
  apply NQlt_add_lt_sub_r.
  rewrite NQadd_0_l.
  apply NQlt_pair; [ easy | pauto | flia Hr ].
Qed.

Theorem A_upper_bound_for_dig {r : radix} : ∀ u i n,
  (∀ k, i + 1 ≤ k ≤ n - 1 → u k ≤ rad - 1)
  → (A i n u < 1)%NQ.
Proof.
intros * Hur.
specialize radix_ge_2 as Hr.
destruct (le_dec (i + 1) (n - 1)) as [H1| H1].
-unfold A.
 rewrite summation_shift; [ | easy ].
 eapply NQle_lt_trans.
 +apply summation_le_compat with
      (g := λ j, ((rad - 1) // rad * 1 // rad ^ j)%NQ).
  intros k Hk.
  replace (i + 1 + k - i) with (1 + k) by flia.
  rewrite NQmul_pair; [ | easy | pauto ].
  rewrite Nat.mul_1_r.
  rewrite <- Nat.pow_succ_r'.
  apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_l, Hur.
  flia H1 Hk.
 +rewrite <- summation_mul_distr_l.
  rewrite NQpower_summation; [ | easy ].
  rewrite NQmul_pair; [ | easy | ]. 2: {
    apply Nat.neq_mul_0.
    split; [ pauto | flia Hr ].
  }
  rewrite Nat.mul_comm, Nat.mul_assoc.
  rewrite <- NQmul_pair; [ | | flia Hr ]. 2: {
    apply Nat.neq_mul_0; pauto.
  }
  rewrite NQpair_diag, NQmul_1_r; [ | flia Hr ].
  rewrite <- Nat.pow_succ_r'.
  apply NQlt_pair; [ pauto | easy | ].
  do 2 rewrite Nat.mul_1_r.
  apply Nat.sub_lt; [ | pauto ].
  now apply Nat_pow_ge_1.
-unfold A; rewrite summation_empty; [ easy | ].
 flia H1.
Qed.

Theorem NQintg_A_le_1_for_add {r : radix} : ∀ u i j,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → NQintg (A i (min_n i j) u) ≤ 1.
Proof.
intros * Hur.
specialize radix_ge_2 as Hr.
remember (min_n i j) as n eqn:Hn.
specialize (A_upper_bound_for_add u i n Hur) as H2.
apply NQintg_le_mono in H2; [ | easy ].
eapply le_trans; [ apply H2 | ].
rewrite NQmul_sub_distr_l.
replace (2 * 1)%NQ with (1 + 1)%NQ by easy.
rewrite <- NQadd_sub_assoc.
assert (H3 : (0 ≤ 1 - 2 * 1 // rad ^ (n - i - 1))%NQ). {
  apply NQle_add_le_sub_l.
  rewrite NQadd_0_l.
  rewrite NQmul_pair; [ | easy | pauto ].
  rewrite Nat.mul_1_r, Nat.mul_1_l.
  apply NQle_pair; [ pauto | easy | ].
  do 2 rewrite Nat.mul_1_r.
  remember (n - i - 1) as s eqn:Hs.
  destruct s.
  -rewrite Hn in Hs.
   unfold min_n in Hs.
   destruct rad; [ easy | cbn in Hs; flia Hs ].
  -cbn; replace 2 with (2 * 1) by flia.
   apply Nat.mul_le_mono; [ easy | ].
   now apply Nat_pow_ge_1.
}
rewrite NQintg_add_nat_l; [ | easy ].
rewrite NQintg_small; [ easy | ].
split; [ easy | ].
apply NQlt_sub_lt_add_r.
replace 1%NQ with (1 + 0)%NQ at 1 by easy.
apply NQadd_le_lt_mono; [ apply NQle_refl | ].
remember (1 // rad ^ (n - i - 1))%NQ as x eqn:Hx.
apply (NQlt_le_trans _ x).
+replace 0%NQ with (0 // 1)%NQ by easy.
 subst x.
 apply NQlt_pair; [ flia | pauto | pauto ].
+replace x with (1 * x)%NQ at 1 by apply NQmul_1_l.
 subst x.
 apply NQmul_le_mono_pos_r.
 *replace 0%NQ with (0 // 1)%NQ by easy.
  apply NQlt_pair; [ flia | pauto | ].
  rewrite Nat.mul_0_l; flia.
 *apply NQle_pair; flia.
Qed.

Theorem carry_upper_bound_for_add {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → carry u i ≤ 1.
Proof.
intros * Hur.
specialize radix_ge_2 as Hr.
unfold carry.
enough (∀ j, NQintg (A i (min_n i j) u) ≤ 1). {
  destruct (LPO_fst (fA_ge_1_ε u i)) as [H1| H1]; [ apply H | ].
  destruct H1 as (j & Hj & Hjj); apply H.
}
intros j.
now apply NQintg_A_le_1_for_add.
Qed.

(* pffff... chais pas... est-ce vrai, d'abord ? si oui, ça vaudrait quand
   même de voir à voir si ça se prouve
Theorem carry_of_succ {r : radix} : ∀ u i,
  carry u i = (u (i + 1) + carry u (i + 1)) / rad.
Proof.
intros.
specialize radix_ge_2 as Hr.
unfold carry.
destruct (LPO_fst (fA_ge_1_ε u i)) as [H1| H1].
-destruct (LPO_fst (fA_ge_1_ε u (i + 1))) as [H2| H2].
 +specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H1) as H3.
  specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H2) as H4.
  rewrite A_split_first, <- Nat.add_1_r. 2: {
    unfold min_n.
    destruct rad; [ easy | cbn; flia ].
  }
  rewrite <- (NQmul_pair_den_num _ 1); [ | easy ].
  rewrite <- NQmul_add_distr_r.
...
*)

(* chais pas
Theorem A_prop_carr {r : radix} : ∀ i n u,
  A i n (P u) = NQfrac (A i n u + carry u (n - 1) // rad ^ (n - i - 1))%NQ.
Proof.
intros.
specialize radix_ge_2 as Hr.
destruct (lt_dec n (i + 1)) as [H1| H1]. {
  unfold A.
  rewrite summation_empty; [ | flia H1 ].
  rewrite summation_empty; [ | flia H1 ].
  rewrite NQadd_0_l.
  replace (n - i - 1) with 0 by flia H1.
  rewrite Nat.pow_0_r.
  unfold carry; symmetry.
  destruct (LPO_fst (fA_ge_1_ε u 0));  apply NQfrac_of_nat.
}
apply Nat.nlt_ge in H1.
remember (n - i - 1) as m eqn:Hm.
replace (n - 1) with (m + i) by flia Hm H1.
replace n with (m + i + 1) by flia Hm H1.
clear n H1 Hm.
revert i.
induction m; intros i.
-rewrite Nat.add_0_l.
 unfold A.
 rewrite Nat.add_sub.
 rewrite summation_empty; [ | flia ].
 rewrite summation_empty; [ | flia ].
 rewrite NQadd_0_l.
 unfold carry; symmetry.
 destruct (LPO_fst (fA_ge_1_ε u 0));  apply NQfrac_of_nat.
(**)
-destruct m.
 +unfold A.
  rewrite Nat.add_sub, Nat.add_comm.
  do 2 rewrite summation_only_one.
  rewrite Nat.add_sub, Nat.pow_1_r.
  unfold P, d2n, prop_carr; cbn.
  rewrite <- NQpair_add_l.
  remember (u (S i) + carry u (S i)) as x eqn:Hx.
  now rewrite NQfrac_pair.
 +destruct m.
  *idtac.
...
*)

(* pffff... c'est trop la merde...
Theorem A_frac_P {r : radix} : ∀ i n u,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → (A i n (P u) = NQfrac (A i n u)) ∨
     (A i n (P u) = NQfrac (A i n u) + 1 // rad ^ (n - i - 1))%NQ ∨
     (∀ j, i + 1 ≤ j ≤ n - 1 → u j = rad - 1).
Proof.
intros * Hur.
specialize radix_ge_2 as Hr.
destruct (lt_dec (n - 1) (i + 1)) as [H1| H1]. {
  unfold A.
  rewrite summation_empty; [ | easy ].
  rewrite summation_empty; [ | easy ].
  now left.
}
apply Nat.nlt_ge in H1.
destruct (eq_nat_dec (i + 1) (n - 1)) as [H2| H2].
-replace (n - i - 1) with 1 by flia H2.
 unfold A.
 rewrite <- H2.
 do 2 rewrite summation_only_one.
 replace (i + 1 - i) with 1 by flia.
 rewrite Nat.pow_1_r.
 rewrite NQfrac_pair.
 unfold P, d2n, prop_carr.
 remember (1 // rad)%NQ as x eqn:Hx.
 cbn; subst x.
 specialize (carry_upper_bound_for_add u (i + 1)) as H3.
 assert (H : ∀ k, u (i + 1 + k) ≤ 2 * (rad - 1)). {
   intros; rewrite Nat.add_shuffle0; apply Hur.
 }
 specialize (H3 H); clear H.
 remember (carry u (i + 1)) as x eqn:Hx.
 symmetry in Hx.
 destruct x; [ now left; rewrite Nat.add_0_r | ].
 destruct x; [ right | flia H3 ].
 destruct (eq_nat_dec (u (i + 1)) rad) as [H4| H4].
 +rewrite H4.
  rewrite Nat_mod_add_same_l; [ | easy ].
  rewrite Nat.mod_same; [ | easy ].
  rewrite Nat.mod_1_l; [ | easy ].
  now left; rewrite NQadd_0_l.
 +destruct (lt_dec (u (i + 1)) (rad - 1)) as [H5| H5].
  *rewrite Nat.mod_small; [ | flia H5 ].
   rewrite Nat.mod_small; [ | flia H5 ].
   now left; rewrite <- NQpair_add_l.
  *apply Nat.nlt_ge in H5.
   destruct (eq_nat_dec (u (i + 1)) (rad - 1)) as [H6| H6].
  --rewrite H6, Nat.sub_add; [ | easy ].
    rewrite Nat.mod_same; [ | easy ].
    rewrite Nat.mod_small; [ | flia Hr ].
    right; intros j Hj.
    now replace j with (i + 1) by flia Hj.
  --left.
    specialize (Hur 0); rewrite Nat.mul_sub_distr_l in Hur.
    rewrite Nat.add_0_r in Hur.
    rewrite Nat_mod_less_small. 2: {
      split; [ flia H5 | flia Hur Hr ].
    }
    rewrite Nat_mod_less_small. 2: {
      split; [ | flia Hur Hr ].
      flia H5 H6.
    }
    rewrite <- NQpair_add_l.
    rewrite Nat.add_sub_swap; [ easy | flia H5 H6 ].
-assert (H : i + 1 < n - 1) by flia H1 H2.
 clear H1 H2; rename H into H1.
 destruct (eq_nat_dec (i + 1) (n - 2)) as [H2| H2].
 +setoid_rewrite A_split_first; [ | flia H2 | flia H2 | flia H2 | flia H2 ].
  setoid_rewrite A_split_first; [ | flia H2 | flia H2 | flia H2 | flia H2 ].
  unfold A.
  rewrite summation_empty; [ | flia H2 ].
  rewrite summation_empty; [ | flia H2 ].
  rewrite NQmul_0_l.
  do 2 rewrite NQadd_0_r.
  replace (S (S i)) with (i + 2) by flia.
  rewrite <- Nat.add_1_r.
  rewrite NQfrac_add_cond.
  destruct
    (NQlt_le_dec
       (NQfrac (u (i + 1)%nat // rad) +
        NQfrac (u (i + 2)%nat // rad * 1 // rad))%NQ
       1) as [H3| H3].
  *rewrite NQsub_0_r.
...
*)

(* bof...
Theorem A_P_upper_bound {r : radix} : ∀ i n u,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → (A i n (P u) ≤ NQfrac (A i n u) + 1 // rad)%NQ.
Proof.
intros * Hur.
specialize radix_ge_2 as Hr.
destruct (lt_dec (n - 1) (i + 1)) as [H1| H1]. {
  unfold A.
  rewrite summation_empty; [ | easy ].
  now rewrite summation_empty.
}
apply Nat.nlt_ge in H1.
destruct (eq_nat_dec (i + 1) (n - 1)) as [H2| H2].
-unfold A.
 rewrite <- H2.
 do 2 rewrite summation_only_one.
 replace (i + 1 - i) with 1 by flia.
 rewrite Nat.pow_1_r.
 rewrite NQfrac_pair.
 rewrite <- NQpair_add_l.
 apply NQle_pair; [ easy | easy | ].
 rewrite Nat.mul_comm.
 apply Nat.mul_le_mono_l.
 unfold P, d2n, prop_carr; cbn.
 destruct (lt_dec (u (i + 1)) rad) as [H3| H3].
 +replace (u (i + 1) mod rad) with (u (i + 1)) by now rewrite Nat.mod_small.
  destruct (le_dec (rad - 2) (u (i + 1))) as [H4| H4].
  *replace (rad - 2) with (rad - 1 - 1) in H4 by flia.
   apply Nat.le_sub_le_add_r in H4.
   eapply le_trans; [ | apply H4 ].
   rewrite Nat.sub_1_r.
   apply Nat.lt_le_pred.
   now apply Nat.mod_upper_bound.
  *apply Nat.nle_gt in H4.
   clear H3; rename H4 into H3.
   rewrite Nat.mod_small.
  --apply Nat.add_le_mono_l.
    apply carry_upper_bound_for_add.
    intros k.
    rewrite Nat.add_shuffle0.
    apply Hur.
  --apply (lt_le_trans _ (rad - 2 + carry u (i + 1))).
   ++now apply Nat.add_lt_mono_r.
   ++replace rad with (rad - 2 + 2) at 2 by now apply Nat.sub_add.
     apply Nat.add_le_mono_l.
     apply (le_trans _ 1); [ | flia ].
     apply carry_upper_bound_for_add.
     intros k.
     rewrite Nat.add_shuffle0.
     apply Hur.
 +apply Nat.nlt_ge in H3.
  specialize (carry_upper_bound_for_add u (i + 1)) as H4.
  assert (H : ∀ k, u (i + 1 + k) ≤ 2 * (rad - 1)). {
    intros k.
    rewrite Nat.add_shuffle0.
    apply Hur.
  }
  specialize (H4 H); clear H.
  remember (carry u (i + 1)) as c eqn:Hc; symmetry in Hc.
  destruct c; [ rewrite Nat.add_0_r; flia | ].
  destruct c; [ clear H4 | flia H4 ].
  rewrite Nat_mod_less_small. 2: {
    split; [ flia H3 | ].
    specialize (Hur 0); rewrite Nat.add_0_r in Hur.
    rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in Hur.
    flia Hur Hr.
  }
  rewrite Nat.add_sub_swap; [ | easy ].
  apply Nat.add_le_mono_r.
  rewrite Nat_mod_less_small; [ easy | ].
  split; [ easy | ].
  specialize (Hur 0); rewrite Nat.add_0_r in Hur.
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in Hur.
  flia Hur Hr.
-assert (H : i + 1 < n - 1) by flia H1 H2.
 clear H1 H2; rename H into H1.
 destruct (eq_nat_dec (i + 1) (n - 2)) as [H2| H2].
 +setoid_rewrite A_split_first; [ | flia H2 | flia H2 ].
  setoid_rewrite A_split_first; [ | flia H2 | flia H2 ].
  unfold A.
  rewrite summation_empty; [ | flia H2 ].
  rewrite summation_empty; [ | flia H2 ].
  rewrite NQmul_0_l.
  do 2 rewrite NQadd_0_r.
  replace (S (S i)) with (i + 2) by flia.
  rewrite <- Nat.add_1_r.
  rewrite NQfrac_add_cond.
...
*)

Definition is_num_9 {r : radix} u i j :=
  if eq_nat_dec (u (i + j)) (rad - 1) then true else false.

Theorem is_num_9_all_9 {r : radix} : ∀ u i,
  (∀ j, is_num_9 u i j = true)
  → (∀ k, u (i + k) = rad - 1).
Proof.
intros * Hm9 *.
specialize (Hm9 k); unfold is_num_9 in Hm9.
now destruct (Nat.eq_dec (u (i + k)) (rad - 1)).
Qed.

Theorem is_num_9_true_iff {r : radix} : ∀ i j u,
  is_num_9 u i j = true ↔ u (i + j) = rad - 1.
Proof.
intros.
unfold is_num_9.
now destruct (Nat.eq_dec (u (i + j)) (rad - 1)).
Qed.

Theorem is_num_9_false_iff {r : radix} : ∀ i j u,
  is_num_9 u i j = false ↔ u (i + j) ≠ rad - 1.
Proof.
intros.
unfold is_num_9.
now destruct (Nat.eq_dec (u (i + j)) (rad - 1)).
Qed.

Theorem all_P_9_all_8_9_18 {r : radix} : ∀ u i,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → (∀ k, P u (i + k) = rad - 1)
  → ∀ k,
     if zerop (carry u (i + k)) then
       u (i + k) = rad - 1
     else if lt_dec (u (i + k) + 1) rad then
       u (i + k) = rad - 2
     else
       u (i + k) = 2 * (rad - 1).
Proof.
intros * Hur Hpr k.
specialize radix_ge_2 as Hr.
specialize (Hpr k) as H1.
unfold P, d2n, prop_carr in H1; cbn in H1.
specialize (carry_upper_bound_for_add u (i + k)) as H2.
assert (H : ∀ j, u (i + k + j + 1) ≤ 2 * (rad - 1)). {
  intros j; do 2 rewrite <- Nat.add_assoc; apply Hur.
}
specialize (H2 H); clear H.
remember (carry u (i + k)) as c eqn:Hc.
symmetry in Hc.
destruct c; cbn.
-rewrite Nat.add_0_r in H1.
 destruct (lt_dec (u (i + k)) rad) as [H4| H4].
 +now rewrite Nat.mod_small in H1.
 +exfalso; apply Nat.nlt_ge in H4.
  rewrite Nat_mod_less_small in H1. 2: {
    split; [ easy | ].
    eapply le_lt_trans; [ apply Hur | ].
    rewrite Nat.mul_sub_distr_l.
    apply Nat.sub_lt; [ flia Hr | flia ].
  }
  apply Nat.add_sub_eq_nz in H1; [ | flia Hr ].
  specialize (Hur k) as H5.
  apply Nat.nlt_ge in H5; apply H5; clear H5.
  rewrite <- H1.
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
  cbn; rewrite Nat.add_0_r.
  rewrite Nat.add_sub_assoc; [ | easy ].
  apply Nat_sub_lt_mono_l.
  split; [ flia | flia Hr ].
-destruct c; [ | flia H2 ].
 destruct (lt_dec (u (i + k) + 1) rad) as [H3| H3].
 +rewrite Nat.mod_small in H1; [ flia H1 | easy ].
 +rewrite Nat.add_0_r.
  apply Nat.nlt_ge in H3.
  rewrite Nat_mod_less_small in H1; [ flia H1 | ].
  split; [ easy | ].
  specialize (Hur k) as H4.
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H4.
  apply (le_lt_trans _ (2 * rad - 1)); [ flia H4 Hr | flia Hr ].
Qed.

Theorem all_P_9_all_frac_mod {r : radix} : ∀ u i,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → (∀ k, P u (i + k) = rad - 1)
  → ∀ k, ∃ m,
  let n := rad * (i + k + m + 3) in
  (NQfrac (A (i + k) n u) < 1 - 1 // rad ^ S m)%NQ ∧
  (u (i + k) + NQintg (A (i + k) n u)) mod rad = rad - 1.
Proof.
(* eq_all_prop_carr_9_cond *)
intros * Hur Hi *.
specialize (Hi k) as Huni.
unfold P, prop_carr, d2n in Huni; simpl in Huni.
unfold carry in Huni.
destruct (LPO_fst (fA_ge_1_ε u (i + k))) as [H1| H1]; simpl in Huni.
-exists 0.
 split; [ | easy ].
 unfold min_n in Huni.
 remember (rad * (i + k + 0 + 3)) as m eqn:Hm.
 specialize (all_P_9_all_8_9_18 u i Hur Hi) as H2.
 assert (Hn' : ∀ l, P u ((i + k) + l) = rad - 1). {
   intros j.
   replace ((i + k) + j) with (i + (k + j)) by flia.
   apply Hi.
 }
Abort. (* à voir...
...
 exfalso; revert Hn'.
 unfold min_n in Huni; rewrite Nat.add_0_r in Huni.
...
 apply not_prop_carr_all_9_all_ge_1; [ | easy | easy ].
 intros l.
 replace (i + k + l + 1) with (i + (k + l) + 1) by flia.
 apply Hur.
...
-destruct H1 as (m & Hjm & Hm).
 apply A_ge_1_false_iff in Hm.
 exists m; easy.
Qed.
...
*)

Theorem eq_all_prop_carr_9_cond1 {r : radix} : ∀ u i n j,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → j < n - i - 1
  → (NQfrac (A i n u) < 1 - 1 // rad ^ S j)%NQ
  → (u i + NQintg (A i n u)) mod rad = rad - 1
  → if NQlt_le_dec (A i n u) 1 then
       u i = rad - 1 ∧ u (i + 1) ≠ 2 * (rad - 1)
     else if lt_dec (u i) (rad - 1) then
       u i = rad - 2 ∧ u (i + 1) ≥ rad - 1
     else
       u i = 2 * (rad - 1) ∧ u (i + 1) ≥ rad - 1.
Proof.
(* eq_all_prop_carr_9_cond1 *)
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hs1z Hj1 Hun1.
Abort. (* à voir *)
Theorem A_upper_bound_for_add_1st_lt_9 {r : radix} : ∀ u i k n,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → i + k + 1 ≤ n - 1
  → u (i + k + 1) < rad - 1
  → (A (i + k) n u < 1)%NQ.
Proof.
intros * Hur Hin H3.
 specialize radix_ge_2 as Hr.
  rewrite A_split_first; [ | easy ].
  replace (S (i + k)) with (i + k + 1) by flia.
  assert (H2 : u (i + k + 1) ≤ rad - 2) by flia Hr H3.
  eapply NQle_lt_trans.
  *apply NQadd_le_mono_r.
   apply NQle_pair; [ easy | easy | ].
   rewrite Nat.mul_comm.
   apply Nat.mul_le_mono_pos_l; [ easy | apply H2 ].
  *rewrite NQpair_sub_l; [ | easy ].
   rewrite NQpair_diag; [ | easy ].
   rewrite <- NQsub_sub_distr.
   apply NQsub_lt, NQlt_add_lt_sub_r.
   rewrite NQadd_0_l.
   replace (2 // rad)%NQ with (2 * (1 // rad))%NQ. 2: {
     now rewrite <- NQpair_mul_r.
   }
   apply NQmul_lt_mono_pos_r.
  --replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQlt_pair; [ easy | easy | flia ].
  --eapply NQle_lt_trans.
   ++apply A_upper_bound_for_add.
     intros l; do 3 rewrite <- Nat.add_assoc; apply Hur.
   ++rewrite NQmul_sub_distr_l, NQmul_1_r.
     apply NQsub_lt.
     remember (n - (i + k + 1) - 1) as l eqn:Hl.
     replace 0%NQ with (0 * 1 // rad ^ l)%NQ by easy.
     apply NQmul_lt_le_mono_pos; [ easy | easy | easy | ].
     apply NQle_refl.
Qed.

Theorem all_P_9_all_8g9_9n18_18g9 {r : radix} : ∀ u i,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → (∀ k, P u (i + k) = rad - 1)
  → ∀ k,
     if zerop (carry u (i + k)) then
       u (i + k) = rad - 1 ∧ u (i + k + 1) ≠ 2 * (rad - 1)
     else if lt_dec (u (i + k) + 1) rad then
       u (i + k) = rad - 2 ∧ u (i + k + 1) ≥ rad - 1
     else
       u (i + k) = 2 * (rad - 1) ∧ u (i + k + 1) ≥ rad - 1.
Proof.
intros * Hur Hpr k.
specialize radix_ge_2 as Hr.
specialize (all_P_9_all_8_9_18 u i Hur Hpr k) as H1.
assert (Hc : ∃ n, carry u (i + k) = NQintg (A (i + k) (min_n (i + k) n) u)). {
  unfold carry.
  destruct (LPO_fst (fA_ge_1_ε u (i + k))) as [H3| H3].
  -exists 0; easy.
  -destruct H3 as (j & Hjj & Hj).
   exists j; easy.
}
destruct Hc as (m & Hm).
remember (min_n (i + k) m) as n eqn:Hn.
assert (Hin : i + k + 1 ≤ n - 1). {
  rewrite Hn; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
}
destruct (zerop (carry u (i + k))) as [H2| H2].
-split; [ easy | ].
 rewrite Hm in H2.
 apply eq_NQintg_0 in H2; [ | easy ].
 apply NQnle_gt in H2.
 intros H3; apply H2; clear H2.
 rewrite A_split_first; [ | easy ].
 replace (S (i + k)) with (i + k + 1) by flia.
 rewrite H3.
 replace (2 * (rad - 1)) with (rad + (rad - 2)) by flia Hr.
 rewrite NQpair_add_l, (NQpair_diag rad); [ | easy ].
 rewrite <- NQadd_assoc.
 apply NQle_add_r.
 replace 0%NQ with (0 // 1 + 0 * 1 // rad)%NQ by easy.
 apply NQadd_le_mono.
 +apply NQle_pair; [ easy | easy | flia Hr ].
 +apply NQmul_le_mono_nonneg; [ easy | easy | easy | ].
  apply NQle_refl.
-assert (H3 : carry u (i + k) ≥ 1). {
   specialize (carry_upper_bound_for_add u (i + k)) as H3.
   assert (H : ∀ l, u (i + k + l + 1) ≤ 2 * (rad - 1)). {
     intros; do 2 rewrite <- Nat.add_assoc; apply Hur.
   }
   specialize (H3 H).
   flia H2 H3.
 }
 clear H2; rename H3 into H2.
 rewrite Hm in H2.
 apply Nat.nlt_ge in H2.
 destruct (lt_dec (u (i + k) + 1) rad) as [H3| H3]; clear H3.
 +split; [ easy | ].
  apply Nat.nlt_ge.
  intros H3; apply H2; clear H2.
  apply Nat.lt_1_r, NQintg_small.
  split; [ easy | ].
  now apply A_upper_bound_for_add_1st_lt_9.
 +split; [ easy | ].
  apply Nat.nlt_ge.
  intros H3; apply H2; clear H2.
  apply Nat.lt_1_r, NQintg_small.
  split; [ easy | ].
  now apply A_upper_bound_for_add_1st_lt_9.
Qed.

Theorem exists_9ge10 {r : radix} : ∀ u i n,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → (∀ k, P u (i + k) = rad - 1)
  → NQintg (A i n u) = 1
  → ∃ m, (∀ l, l < m → u (i + l + 1) = rad - 1) ∧ u (i + m + 1) ≥ rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hpu Hia.
destruct (LPO_fst (is_num_9 u (i + 1))) as [H1| H1]; cycle 1.
-destruct H1 as (j & Hjj & Hj).
 apply is_num_9_false_iff in Hj.
 exists j.
 split.
 +intros l Hl.
  specialize (Hjj _ Hl).
  apply is_num_9_true_iff in Hjj.
  now rewrite Nat.add_shuffle0.
 +rewrite Nat.add_shuffle0 in Hj.
  specialize (all_P_9_all_8g9_9n18_18g9 u i Hur Hpu (j + 1)) as H1.
  replace (i + (j + 1)) with (i + j + 1) in H1 by flia.
  destruct (zerop (carry u (i + j + 1))) as [H2| H2]; [ easy | ].
  destruct (lt_dec (u (i + j + 1) + 1) rad) as [H3| H3]. 2: {
    rewrite (proj1 H1); flia Hr.
  }
  exfalso.
  clear Hj H3.
  (* devrait être contradictoire avec Hia car j'ai 99998 et même avec
     la retenue 1, ça ne donnera que 99999 et ça ne débordera point *)
  revert i Hur Hpu Hjj H1 H2 Hia.
  induction j; intros.
  *rewrite Nat.add_0_r in H1, H2.
   destruct (lt_dec (n - 1) (i + 1)) as [H3| H3]. {
     unfold A in Hia.
     now rewrite summation_empty in Hia.
   }
   apply Nat.nlt_ge in H3.
   rewrite A_split_first in Hia; [ | easy ].
   rewrite <- Nat.add_1_r in Hia.
   rewrite (proj1 H1) in Hia.
   rewrite NQpair_sub_l in Hia; [ | easy ].
   rewrite NQpair_diag in Hia; [ | easy ].
   rewrite <- NQsub_sub_distr in Hia.
   rewrite NQintg_small in Hia; [ easy | ].
   split.
  --apply NQle_0_sub.
    replace (2 // rad)%NQ with (2 * 1 // rad)%NQ. 2: {
      now rewrite <- NQpair_mul_r.
    }
    rewrite <- NQmul_sub_distr_r.
    replace 1%NQ with (rad // 1 * 1 // rad)%NQ. 2: {
      rewrite <- NQpair_mul_r, Nat.mul_1_r.
      now apply NQpair_diag.
    }
    apply NQmul_le_mono_nonneg_r.
   ++replace 0%NQ with (0 // 1)%NQ by easy.
     apply NQle_pair; [ easy | easy | flia ].
   ++eapply NQle_trans; [ now apply NQle_sub_l | ].
     apply NQle_pair; [ easy | easy | flia Hr ].
  --apply NQsub_lt, NQlt_0_sub.
    replace (2 // rad)%NQ with (2 * 1 // rad)%NQ. 2: {
      now rewrite <- NQpair_mul_r.
    }
    apply NQmul_lt_mono_pos_r.
   **replace 0%NQ with (0 // 1)%NQ by easy.
     apply NQlt_pair; [ easy | easy | pauto ].
   **eapply NQle_lt_trans.
   ---apply A_upper_bound_for_add.
      intros k; do 2 rewrite <- Nat.add_assoc; apply Hur.
   ---replace 2%NQ with (2 * 1)%NQ at 2 by easy.
      apply NQmul_lt_mono_pos_l; [ easy | ].
      apply NQsub_lt.
      replace 0%NQ with (0 // 1)%NQ by easy.
      apply NQlt_pair; [ easy | pauto | flia ].
  *specialize (IHj (i + 1)) as H3.
   assert (H : ∀ k, u (i + 1 + k) ≤ 2 * (rad - 1)). {
     intros; rewrite <- Nat.add_assoc; apply Hur.
   }
   specialize (H3 H); clear H.
   assert (H : ∀ k, P u (i + 1 + k) = rad - 1). {
     intros; rewrite <- Nat.add_assoc; apply Hpu.
   }
   specialize (H3 H); clear H.
   assert (H : ∀ k : nat, k < j → is_num_9 u (i + 1 + 1) k = true). {
     intros k Hk.
     assert (H : S k < S j) by flia Hk.
     specialize (Hjj _ H).
     apply is_num_9_true_iff in Hjj.
     apply is_num_9_true_iff.
     now rewrite <- Nat.add_assoc.
   }
   specialize (H3 H); clear H.
   replace (i + 1 + j) with (i + S j) in H3 by flia.
   specialize (H3 H1 H2); apply H3; clear H3.
   destruct (lt_dec (n - 1) (i + 1)) as [H3| H3]. {
     unfold A in Hia.
     now rewrite summation_empty in Hia.
   }
   apply Nat.nlt_ge in H3.
   rewrite A_split_first in Hia; [ | easy ].
   specialize (Hjj 0 (Nat.lt_0_succ j)) as H4.
   apply is_num_9_true_iff in H4.
   rewrite <- Nat.add_1_r in Hia.
   rewrite Nat.add_0_r in H4.
   rewrite H4 in Hia.
   rewrite NQpair_sub_l in Hia; [ | easy ].
   rewrite NQpair_diag in Hia; [ | easy ].
   destruct (NQlt_le_dec (A (i + 1) n u) 1) as [H5| H5].
  --exfalso.
    rewrite NQintg_small in Hia; [ easy | ].
    split.
   ++rewrite <- NQadd_sub_swap.
     apply NQle_0_sub.
     apply (NQle_trans _ 1).
    **apply NQle_pair; [ easy | easy | flia Hr ].
    **apply NQle_add_r.
      replace 0%NQ with (0 * 1 // rad)%NQ by easy.
      apply NQmul_le_mono_nonneg_r; [ | easy ].
      replace 0%NQ with (0 // 1)%NQ by easy.
      apply NQle_pair; [ easy | easy | flia Hr ].
   ++rewrite <- NQsub_sub_distr.
     apply NQsub_lt.
     apply NQlt_0_sub.
     replace (1 // rad)%NQ with (1 * 1 // rad)%NQ at 2 by apply NQmul_1_l.
     apply NQmul_lt_mono_pos_r; [ | easy ].
     replace 0%NQ with (0 // 1)%NQ by easy.
     apply NQlt_pair; [ easy | easy | flia Hr ].
  --apply eq_nA_div_1.
   ++intros; do 2 rewrite <- Nat.add_assoc; apply Hur.
   ++now apply NQintg_le_mono in H5.
-exfalso.
 specialize (is_num_9_all_9 _ _ H1) as H2.
 (* contradictoire entre Hia et H2 *)
 rewrite NQintg_small in Hia; [ easy | ].
 split; [ easy | ].
 apply A_upper_bound_for_dig.
 intros k Hk.
 replace k with (i + 1 + (k - i - 1)) by flia Hk.
 now rewrite H2.
Qed.

Theorem all_P_9_all_9n18_8_18 {r : radix} : ∀ u i,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → (∀ k, P u (i + k) = rad - 1)
  → ∀ k,
     u (i + k) = rad - 1 ∧ u (i + k + 1) ≠ 2 * (rad - 1) ∨
     u (i + k) = rad - 2 ∧
       (∃ n,
          (∀ l, l < n → u (i + k + l + 1) = rad - 1) ∧
          u (i + k + n + 1) ≥ rad) ∨
     u (i + k) = 2 * (rad - 1) ∧
       (∃ n, (∀ l, l < n → u (i + k + l + 1) = rad - 1) ∧
       u (i + k + n + 1) ≥ rad).
Proof.
(* eq_all_prop_carr_9_cond2 *)
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hi j.
specialize (all_P_9_all_8_9_18 u i Hur Hi j) as H1.
assert (Hc : ∃ n, carry u (i + j) = NQintg (A (i + j) (min_n (i + j) n) u)). {
  unfold carry.
  destruct (LPO_fst (fA_ge_1_ε u (i + j))) as [H3| H3].
  -exists 0; easy.
  -destruct H3 as (k & Hjk & Hk).
   exists k; easy.
}
destruct Hc as (m & Hm).
destruct (zerop (carry u (i + j))) as [H2| H2].
-left; split; [ easy | ].
 rewrite H2 in Hm; symmetry in Hm.
 remember (min_n (i + j) m) as n eqn:Hn.
 assert (Hin : i + j + 1 ≤ n - 1). {
   rewrite Hn; unfold min_n.
   destruct rad; [ easy | cbn; flia ].
 }
 apply eq_NQintg_0 in Hm; [ | easy ].
 apply NQnle_gt in Hm.
 intros H4; apply Hm; clear Hm.
 rewrite A_split_first; [ | easy ].
 replace (S (i + j)) with (i + j + 1) by flia.
 rewrite H4.
 eapply NQle_trans; [ | apply NQle_add_r ].
 +apply NQle_pair; [ easy | easy | flia Hr ].
 +replace 0%NQ with (0 * 0)%NQ by easy.
  now apply NQmul_le_mono_nonneg.
-assert (H3 : carry u (i + j) = 1). {
   specialize (carry_upper_bound_for_add u (i + j)) as H3.
   assert (H : ∀ k, u (i + j + k + 1) ≤ 2 * (rad - 1)). {
     intros; do 2 rewrite <- Nat.add_assoc; apply Hur.
   }
   specialize (H3 H).
   flia H2 H3.
 }
 clear H2; rename H3 into H2.
 rewrite Hm in H2.
 destruct (lt_dec (u (i + j) + 1) rad) as [H3| H3].
 +right; left; clear H3.
  split; [ easy | ].
  eapply exists_9ge10; [ | | apply H2 ].
  *intros k; rewrite <- Nat.add_assoc; apply Hur.
  *intros k; rewrite <- Nat.add_assoc; apply Hi.
 +right; right; clear H3.
  split; [ easy | ].
  eapply exists_9ge10; [ | | apply H2 ].
  *intros k; rewrite <- Nat.add_assoc; apply Hur.
  *intros k; rewrite <- Nat.add_assoc; apply Hi.
Qed.

Theorem all_P_9_all_989_8_18 {r : radix} : ∀ u i,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → (∀ k, P u (i + k) = rad - 1)
  → ∀ k,
     u (i + k) = rad - 1 ∧
       (u (i + k + 1) = rad - 2 ∨ u (i + k + 1) = rad - 1) ∨
     u (i + k) = rad - 2 ∧
       (∃ n,
           (∀ l, l < n → u (i + k + l + 1) = rad - 1) ∧
           u (i + k + n + 1) = 2 * (rad - 1)) ∨
     u (i + k) = 2 * (rad - 1) ∧
       (∃ n,
           (∀ l, l < n → u (i + k + l + 1) = rad - 1) ∧
           u (i + k + n + 1) = 2 * (rad - 1)).
Proof.
(* eq_all_prop_carr_9_cond3 *)
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hn k.
rename i into n.
specialize (all_P_9_all_9n18_8_18 u n Hur Hn k) as H.
remember (n + k + 1) as i eqn:Hi.
replace (n + k + 2) with (i + 1) by flia Hi.
destruct H as [H| [H| H]]; destruct H as (H1, H2).
-left; split; [ easy | ].
 specialize (all_P_9_all_9n18_8_18 u n Hur Hn (k + 1)) as H.
 replace (n + (k + 1)) with i in H by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H3, H4).
 +now right.
 +now left.
 +easy.
-right; left; split; [ easy | ].
 destruct H2 as (j2 & Hlj2 & Hj2).
 exists j2.
 split; [ easy | ].
 specialize (all_P_9_all_9n18_8_18 u n Hur Hn (i + j2 - n)) as H.
 replace (n + (i + j2 - n)) with (i + j2) in H by flia Hi.
 replace (n + k + j2 + 1) with (i + j2) in Hj2 |-* by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H3, H4).
 +rewrite H3 in Hj2; flia Hr Hj2.
 +rewrite H3 in Hj2; flia Hr Hj2.
 +easy.
-right; right; split; [ easy | ].
 destruct H2 as (j2 & Hlj2 & Hj2).
 exists j2.
 specialize (all_P_9_all_9n18_8_18 u n Hur Hn (i + j2 - n)) as H.
 replace (n + (i + j2 - n)) with (i + j2) in H by flia Hi.
 replace (n + k + j2 + 1) with (i + j2) in Hj2 |-* by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H3, H4).
 +rewrite H3 in Hj2; flia Hr Hj2.
 +rewrite H3 in Hj2; flia Hr Hj2.
 +easy.
Qed.

Theorem all_P_9_all_989_818_1818 {r : radix} : ∀ u i,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → (∀ k, P u (i + k) = rad - 1)
  → ∀ k,
     u (i + k) = rad - 1 ∧
       (u (i + k + 1) = rad - 2 ∨ u (i + k + 1) = rad - 1) ∨
     u (i + k) = rad - 2 ∧
        u (i + k + 1) = 2 * (rad - 1) ∨
     u (i + k) = 2 * (rad - 1) ∧
        u (i + k + 1) = 2 * (rad - 1).
Proof.
(* eq_all_prop_carr_9_cond4 *)
intros * Hur Hpr k.
specialize radix_ge_2 as Hr.
specialize (all_P_9_all_989_8_18 u i Hur Hpr k) as H.
destruct H as [H| [H| H]]; [ now left | | ].
-right; left.
 destruct H as (Huk & n & Hln & Hn).
 split; [ easy | ].
 destruct n; [ now rewrite Nat.add_0_r in Hn | ].
 specialize (Hln n (Nat.lt_succ_diag_r n)) as H1.
 specialize (all_P_9_all_989_8_18 u i Hur Hpr (k + n + 1)) as H.
 replace (i + (k + n + 1)) with (i + k + n + 1) in H by flia.
 replace (i + k + n + 1 + 1) with (i + k + n + 2) in H by flia.
 replace (i + k + S n + 1) with (i + k + n + 2) in Hn by flia.
 destruct H as [H| [H| H]]; destruct H as (H2, H3).
 +exfalso.
  rewrite Hn in H3.
  destruct H3 as [H3| H3]; flia Hr H3.
 +rewrite H1 in H2; flia Hr H2.
 +rewrite H1 in H2; flia Hr H2.
-right; right.
 destruct H as (Huk & n & Hln & Hn).
 split; [ easy | ].
 destruct n; [ now rewrite Nat.add_0_r in Hn | ].
 specialize (Hln n (Nat.lt_succ_diag_r n)) as H1.
 specialize (all_P_9_all_989_8_18 u i Hur Hpr (k + n + 1)) as H.
 replace (i + (k + n + 1)) with (i + k + n + 1) in H by flia.
 replace (i + k + n + 1 + 1) with (i + k + n + 2) in H by flia.
 replace (i + k + S n + 1) with (i + k + n + 2) in Hn by flia.
 destruct H as [H| [H| H]]; destruct H as (H2, H3).
 +exfalso.
  rewrite Hn in H3.
  destruct H3 as [H3| H3]; flia Hr H3.
 +rewrite H1 in H2; flia Hr H2.
 +rewrite H1 in H2; flia Hr H2.
Qed.

Theorem all_P_9_999_9818_1818 {r : radix} : ∀ u i,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → (∀ k, P u (i + k) = rad - 1)
  → (∀ k, u (i + k) = rad - 1) ∨
     (∀ k, u (i + k) = 2 * (rad - 1)) ∨
     (∃ j,
       (∀ k, k < j → u (i + k) = rad - 1) ∧
       u (i + j) = rad - 2 ∧
       (∀ k, u (i + j + k + 1) = 2 * (rad - 1))).
Proof.
(* eq_all_prop_carr_9 *)
intros * Hur Hpr.
specialize radix_ge_2 as Hr.
specialize (all_P_9_all_989_818_1818 u i Hur Hpr) as HAF.
destruct (LPO_fst (is_num_9 u i)) as [H1| H1].
-specialize (is_num_9_all_9 u i H1) as H2.
 now left.
-destruct H1 as (j & Hjj & Hj).
 apply is_num_9_false_iff in Hj.
 destruct j.
 +specialize (HAF 0) as H1.
  rewrite Nat.add_0_r in Hj, H1.
  destruct H1 as [H1| [H1| H1]]; destruct H1 as (H1, H2).
  *easy.
  *right; right.
   exists 0.
   rewrite Nat.add_0_r.
   split; [ now intros | ].
   split; [ easy | ].
   replace (i + 1 + 1) with (i + 2) in H2 by flia.
   intros k.
   induction k; [ now rewrite Nat.add_0_r | ].
   specialize (HAF (k + 1)) as H3.
   replace (i + (k + 1)) with (i + k + 1) in H3 by flia.
   destruct H3 as [H3| [H3| H3]]; destruct H3 as (H3, H4).
  --rewrite H3 in IHk; flia Hr IHk.
  --rewrite H3 in IHk; flia Hr IHk.
  --now replace (i + k + 1 + 1) with (i + S k + 1) in H4 by flia.
  *right; left.
   intros k.
   induction k; [ now rewrite Nat.add_0_r | ].
   specialize (HAF k) as H3.
   destruct H3 as [H3| [H3| H3]]; destruct H3 as (H3, H4).
  --rewrite H3 in IHk; flia Hr IHk.
  --rewrite H3 in IHk; flia Hr IHk.
  --now replace (i + k + 1) with (i + S k) in H4 by flia.
 +specialize (Hjj j (Nat.lt_succ_diag_r j)) as H1.
  apply is_num_9_true_iff in H1.
  right; right.
  exists (S j).
  split.
  *intros k Hk.
   specialize (Hjj _ Hk).
   now apply is_num_9_true_iff in Hjj.
  *replace (i + S j) with (i + j + 1) in Hj |-* by flia.
   specialize (HAF j) as H2.
   destruct H2 as [H2| [H2| H2]]; destruct H2 as (H2, H3).
  --(*replace (i + j + 1 + 1) with (i + j + 2) in H3 by flia.*)
    destruct H3 as [H3| H3]; [ | easy ].
    split; [ easy | ].
    intros k.
    induction k.
   ++rewrite Nat.add_0_r.
     replace (i + j + 1 + 1) with (i + j + 2) by flia.
     specialize (HAF (j + 1)) as H4.
     destruct H4 as [H4| [H4| H4]]; destruct H4 as (H4, H5).
    **replace (i + (j + 1)) with (i + j + 1) in H4 by flia.
      rewrite H3 in H4; flia Hr H4.
    **now replace (i + (j + 1) + 1) with (i + j + 2) in H5 by flia.
    **now replace (i + (j + 1) + 1) with (i + j + 2) in H5 by flia.
   ++replace (i + j + 1 + k + 1) with (i + j + k + 2) in IHk by flia.
     replace (i + j + 1 + S k + 1) with (i + j + k + 3) by flia.
     specialize (HAF (j + k + 2)) as H4.
     replace (i + (j + k + 2)) with (i + j + k + 2) in H4 by flia.
     destruct H4 as [H4| [H4| H4]]; destruct H4 as (H4, H5).
    **rewrite H4 in IHk; flia Hr IHk.
    **rewrite H4 in IHk; flia Hr IHk.
    **now replace (i + j + k + 2 + 1) with (i + j + k + 3) in H5 by flia.
  --rewrite H1 in H2; flia Hr H2.
  --rewrite H1 in H2; flia Hr H2.
Qed.

Theorem all_P_9_all_fA_true {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, P u (i + k + 1) = rad - 1)
  → ∀ k, fA_ge_1_ε u i k = true.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hpr k.
apply A_ge_1_true_iff.
specialize (all_P_9_999_9818_1818 u (i + 1))  as H1.
assert (H : ∀ k, u (i + 1 + k) ≤ 2 * (rad - 1)). {
  intros; rewrite Nat.add_shuffle0; apply Hur.
}
specialize (H1 H); clear H.
assert (H : ∀ k, P u (i + 1 + k) = rad - 1). {
  intros; rewrite Nat.add_shuffle0; apply Hpr.
}
specialize (H1 H); clear H.
destruct H1 as [H1| [H1| H1]].
-rewrite A_all_9 by (intros j Hj; rewrite Nat.add_shuffle0; apply H1).
 rewrite NQfrac_small. 2: {
   split.
   -apply NQle_0_sub.
    apply NQle_pair; [ pauto | easy | ].
    now apply Nat.mul_le_mono_r, Nat_pow_ge_1.
   -apply NQsub_lt.
    replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQlt_pair; [ easy | pauto | flia ].
 }
 apply NQsub_le_mono; [ apply NQle_refl | ].
 apply NQle_pair; [ pauto | pauto | ].
 rewrite Nat.mul_1_l, Nat.mul_1_r.
 apply Nat.pow_le_mono_r; [ easy | ].
 unfold min_n.
 destruct rad; [ easy | cbn; flia ].
-rewrite A_all_18 by (intros j; rewrite Nat.add_shuffle0; apply H1).
 replace 2%NQ with (1 + 1)%NQ by easy.
 rewrite <- NQadd_sub_assoc.
 remember (min_n i k - i - 1) as s eqn:Hs.
 assert (H2 : 2 ≤ rad ^ s). {
   destruct s.
   +unfold min_n in Hs.
    destruct rad; [ easy | cbn in Hs; flia Hs ].
   +cbn.
    replace 2 with (2 * 1) by easy.
    apply Nat.mul_le_mono_nonneg; [ flia | easy | flia | ].
    now apply Nat_pow_ge_1.
 }
 rewrite NQfrac_add_nat_l.
 +rewrite NQfrac_small. 2: {
    split.
    -apply NQle_0_sub.
     apply NQle_pair; [ pauto | easy | ].
     now apply Nat.mul_le_mono_r.
    -apply NQsub_lt.
     replace 0%NQ with (0 // 1)%NQ by easy.
     apply NQlt_pair; [ easy | pauto | flia ].
  }
  apply NQsub_le_mono; [ apply NQle_refl | ].
  apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_1_r.
  apply (le_trans _ (rad ^ S (S k))).
  *rewrite (Nat.pow_succ_r' _ (S k)).
   now apply Nat.mul_le_mono.
  *apply Nat.pow_le_mono_r; [ easy | ].
   rewrite Hs.
   unfold min_n.
   destruct rad; [ easy | cbn; flia ].
 +apply NQle_0_sub.
  apply NQle_pair; [ pauto | easy | ].
  now apply Nat.mul_le_mono_r.
-destruct H1 as (j & Hjj & Hj).
 rewrite Nat.add_shuffle0 in Hj.
 remember (min_n i k - i - 1) as s eqn:Hs.
 assert (H2 : 2 ≤ rad ^ s). {
   destruct s.
   +unfold min_n in Hs.
    destruct rad; [ easy | cbn in Hs; flia Hs ].
   +cbn.
    replace 2 with (2 * 1) by easy.
    apply Nat.mul_le_mono_nonneg; [ flia | easy | flia | ].
    now apply Nat_pow_ge_1.
 }
 rewrite (A_9_8_all_18 j); [ | | easy | ].
 +rewrite <- Hs.
  rewrite NQfrac_small. 2: {
    split.
    -apply NQle_0_sub.
     apply NQle_pair; [ pauto | easy | ].
     do 2 rewrite Nat.mul_1_r.
     apply (le_trans _ 2); [ | easy ].
     destruct (le_dec (i + j + 1) (min_n i k - 1)); [ easy | pauto ].
    -apply NQsub_lt.
     replace 0%NQ with (0 // 1)%NQ by easy.
     apply NQlt_pair; [ easy | pauto | ].
     cbn; rewrite Nat.add_0_r.
     destruct (le_dec (i + j + 1) (min_n i k - 1)); pauto.
  }
  apply NQsub_le_mono; [ apply NQle_refl | ].
  apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_1_r.
  destruct (le_dec (i + j + 1) (min_n i k - 1)) as [H1| H1].
  *apply (le_trans _ (rad ^ S (S k))).
  --rewrite (Nat.pow_succ_r' _ (S k)).
    now apply Nat.mul_le_mono.
  --apply Nat.pow_le_mono_r; [ easy | ].
    rewrite Hs.
    unfold min_n.
    destruct rad; [ easy | cbn; flia ].
  *rewrite Nat.mul_1_l.
   apply Nat.pow_le_mono_r; [ easy | ].
   rewrite Hs; unfold min_n.
   destruct rad; [ easy | cbn; flia ].
 +intros l Hl.
  now rewrite Nat.add_shuffle0; apply Hjj.
 +intros l.
  replace (i + j + l + 2) with (i + j + 1 + l + 1) by flia.
  apply Hj.
Qed.

Theorem pre_Hugo_Herbelin_111 {r : radix} : ∀ u v i n,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → n = min_n i 0
  → (∀ k, fA_ge_1_ε (u ⊕ P v) i k = true)
  → (∀ k, fA_ge_1_ε (u ⊕ v) i k = true)
  → (∀ k, fA_ge_1_ε v i k = true)
  → (NQintg (A i n v) + NQintg (A i n (u ⊕ P v))) mod rad =
     NQintg (A i n (u ⊕ v)) mod rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hn H1 H2 H3.
rewrite Nat.add_comm.
do 2 rewrite A_additive.
rewrite NQintg_add; [ symmetry | easy | easy ].
rewrite NQintg_add; [ symmetry | easy | easy ].
do 3 rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
rewrite Nat.add_assoc, Nat.add_comm.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
rewrite Nat.add_comm.
rewrite NQintg_P_M, Nat.add_0_r.
specialize (all_fA_ge_1_ε_P_999 _ _ H3) as A3.
assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
  intros; rewrite <- Nat.add_assoc; apply Hv.
}
specialize (A_ge_1_add_all_true_if v i H H3) as H'3; clear H.
assert (H4 : (0 ≤ 1 - 2 // rad ^ (n - i - 1))%NQ). {
  rewrite NQsub_pair_pos; [ | easy | pauto | ]. 2: {
    do 2 rewrite Nat.mul_1_l.
    remember (n - i - 1) as s eqn:Hs.
    destruct s.
    -rewrite Hn in Hs; unfold min_n in Hs.
     rewrite Nat.add_0_r, Nat.mul_add_distr_l in Hs.
     destruct rad; [ easy | cbn in Hs; flia Hs ].
    -cbn.
     replace 2 with (2 * 1) by flia.
     apply Nat.mul_le_mono; [ easy | now apply Nat_pow_ge_1 ].
  }
  do 2 rewrite Nat.mul_1_l.
  replace 0%NQ with (0 // 1)%NQ by easy.
  apply NQle_pair; [ easy | pauto | ].
  rewrite Nat.mul_0_l, Nat.mul_1_l; flia.
}
destruct H'3 as [H'3| [H'3| H'3]].
-f_equal; f_equal; f_equal; f_equal.
 apply A_eq_compat.
 intros j Hj.
 replace j with (i + (j - i - 1) + 1) by flia Hj.
 now rewrite A3, H'3.
(* Here, NQfrac(A(P v))=0.999...999 and NQfrac(A(v))=0.999...998 with
     therefore a difference of 0.000...001. If NQfrac(A(u))≠0.000...001,
     then the two parts are equal (equal to 1) and it is ok. Otherwise,
     if NQfrac(A(u))=0.000...001, then the left hand part is 1 but the
     right hand part is 0. *)
-rewrite NQfrac_P_M.
 remember (NQfrac (A i n u)) as x eqn:Hx.
 rewrite A_all_9; [ | intros; apply A3 ].
 rewrite A_all_18; [ | easy ].
 replace 2%NQ with (1 + 1)%NQ by easy.
 rewrite <- NQadd_sub_assoc.
 rewrite NQfrac_add_nat_l; [ | easy ].
 set (s := n - i - 1) in H4 |-*.
 rewrite NQfrac_small. 2: {
   split; [ easy | ].
   apply NQsub_lt.
   replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | pauto | cbn; pauto ].
 }
 f_equal.
 subst s x.
 now eapply pre_Hugo_Herbelin_lemma.
-destruct H'3 as (j & Hbef & Hwhi & Haft).
 rewrite NQfrac_P_M.
 remember (NQfrac (A i n u)) as x eqn:Hx.
 rewrite A_all_9; [ | intros; apply A3 ].
 rewrite (A_9_8_all_18 j); [ | easy | easy | easy ].
 destruct (le_dec (i + j + 1) (n - 1)) as [H5| H5]. 2: {
   rewrite NQfrac_small; [ easy | ].
   split.
   -apply NQle_add_le_sub_l.
    rewrite NQadd_0_l.
    apply NQle_pair; [ pauto | easy | ].
    do 2 rewrite Nat.mul_1_r.
    now apply Nat_pow_ge_1.
   -apply NQsub_lt.
    replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQlt_pair; [ easy | pauto | flia ].
 }
 set (s := n - i - 1) in H4 |-*.
 rewrite NQfrac_small. 2: {
   split; [ easy | ].
   apply NQsub_lt.
   replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | pauto | flia ].
 }
 f_equal.
 subst x s.
 now eapply pre_Hugo_Herbelin_lemma.
Qed.

(* generalizes A_all_9 and A_all_18 *)
Theorem glop {r : radix} : ∀ u i m n,
  (∀ k : nat, i + k + 1 < n → u (i + k + 1) = m * (rad - 1))
  → A i n u = (m // 1 - m // rad ^ (n - i - 1))%NQ.
Proof.
intros * Hmr.
specialize radix_ge_2 as Hr.
Check A_all_9.
Check A_all_18.
unfold A.
destruct (le_dec (i + 1) (n - 1)) as [Hin| Hin]; cycle 1. {
  replace (n - i - 1) with 0 by flia Hin.
  rewrite Nat.pow_0_r, NQsub_diag.
  now rewrite summation_empty; [ | flia Hin ].
}
rewrite summation_shift; [ | easy ].
rewrite summation_eq_compat with
    (h := λ j, ((m * (rad - 1)) // rad ^ (j + 1))%NQ). 2: {
  intros j Hj.
  replace (i + 1 + j - i) with (j + 1) by flia.
  rewrite Nat.add_shuffle0, Hmr; [ easy | flia Hin Hj ].
}
rewrite summation_eq_compat with
    (h := λ j, ((m * (rad - 1)) // rad * 1 // rad ^ j)%NQ). 2: {
  intros j Hj.
  rewrite NQmul_pair; [ | easy | pauto ].
  rewrite Nat.mul_1_r; f_equal.
  now rewrite Nat.add_comm.
}
rewrite <- summation_mul_distr_l.
remember NQ_of_pair as f; simpl; subst f.
rewrite NQpower_summation; [ | flia Hr ].
replace (n - 1 - (i + 1)) with (n - i - 1 - 1) by flia Hin.
remember (n - i - 1) as s eqn:Hs.
replace (S (s - 1)) with s by flia Hs Hin.
rewrite NQsub_pair_pos; [ | easy | pauto | ]; cycle 1. {
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_l.
  now apply Nat_pow_ge_1.
}
do 2 rewrite Nat.mul_1_l.
rewrite NQmul_pair; [ | easy | ]. 2: {
  apply Nat.neq_mul_0.
  split; [ pauto | flia Hr ].
}
rewrite Nat.mul_shuffle0, Nat.mul_assoc.
rewrite <- NQmul_pair; [ | | flia Hr ]; cycle 1. {
  apply Nat.neq_mul_0.
  split; [ easy | pauto ].
}
rewrite NQpair_diag; [ | flia Hr ].
rewrite NQmul_1_r.
replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
rewrite <- Nat.pow_add_r.
replace (1 + (s - 1)) with s by flia Hs Hin.
now rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
Qed.

(* generalizes A_upper_bound_for_add *)
Theorem A_upper_bound_for_adds {r : radix} (rg := nat_ord_ring) : ∀ u i n m,
  (∀ k, u (i + k + 1) ≤ m * (rad - 1))
  → (A i n u ≤ (m // 1 * (1 - 1 // rad ^ (n - i - 1))))%NQ.
Proof.
intros * Hur.
specialize radix_ge_2 as Hr.
destruct (lt_dec (n - 1) (i + 1)) as [Hin| Hin].
-unfold A.
 rewrite summation_empty; [ | easy ].
 remember (rad ^ (n - i - 1)) as s eqn:Hs.
 change (0 ≤ m // 1 * (1 - 1 // s))%NQ.
 rewrite <- (NQmul_0_r (m // 1)%NQ).
 apply NQmul_le_mono_nonneg_l.
 +replace 0%NQ with (0 // 1)%NQ by easy.
  apply NQle_pair; [ easy | easy | flia ].
 +apply (NQadd_le_r _ _ (1 // s)).
  rewrite NQadd_0_l, NQsub_add.
  destruct s. {
    symmetry in Hs.
    now apply Nat.pow_nonzero in Hs.
  }
  apply NQle_pair; [ easy | easy | ].
  apply Nat.mul_le_mono_nonneg_r; [ apply Nat.le_0_1 | flia ].
-apply Nat.nlt_ge in Hin.
 remember (n - i - 1) as s eqn:Hs.
 destruct s; [ flia Hin Hs | ].
 rewrite NQpower_summation_inv; [ | flia Hr ].
 unfold A.
 rewrite summation_shift; [ | easy ].
 replace (n - 1 - (i + 1)) with s by flia Hs.
 do 2 rewrite summation_mul_distr_l.
 apply summation_le_compat.
 intros j Hj.
 replace (i + 1 + j - i) with (S j) by flia.
 apply (NQle_trans _ ((m * (rad - 1)) // (rad ^ S j))).
 +apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_comm, Nat.add_shuffle0.
  apply Nat.mul_le_mono_l, Hur.
 +rewrite NQmul_assoc.
  rewrite NQsub_pair_pos; [ | easy | easy | now apply Nat.mul_le_mono_l].
  do 2 rewrite Nat.mul_1_l.
  rewrite NQmul_pair; [ | easy | easy ].
  rewrite Nat.mul_1_l.
  rewrite NQmul_pair; [ | easy | pauto ].
  rewrite Nat.mul_1_r.
  apply NQle_refl.
Qed.

(* generalizes NQintg_A_le_1_for_add *)
Theorem NQintg_A_le_for_adds {r : radix} : ∀ u i j m,
  (∀ k, u (i + k + 1) ≤ m * (rad - 1))
  → NQintg (A i (min_n i j) u) ≤ m - 1.
Proof.
intros * Hmr.
specialize radix_ge_2 as Hr.
remember (min_n i j) as n eqn:Hn.
destruct (zerop m) as [Hm| Hm]. {
  subst m.
  unfold A.
  rewrite all_0_summation_0; [ easy | ].
  intros k Hk.
  specialize (Hmr (k - i - 1)).
  replace (i + (k - i - 1) + 1) with k in Hmr by flia Hk.
  now apply Nat.le_0_r in Hmr; rewrite Hmr.
}
specialize (A_upper_bound_for_adds u i n m Hmr) as H2.
rewrite NQmul_sub_distr_l, NQmul_1_r in H2.
apply NQintg_le_mono in H2; [ | easy ].
eapply le_trans; [ apply H2 | ].
rewrite (Nat.sub_1_r m).
apply Nat.lt_le_pred.
apply NQintg_sub_nat_l_lt.
split.
-rewrite NQmul_comm.
 replace 0%NQ with (0 * m // 1)%NQ by easy.
 apply NQmul_lt_le_mono_pos; [ easy | easy | | apply NQle_refl ].
 replace 0%NQ with (0 // 1)%NQ by easy.
 apply NQlt_pair; [ easy | easy | now rewrite Nat.mul_1_l ].
-replace (m // 1)%NQ with (m // 1 * 1)%NQ at 2 by apply NQmul_1_r.
 apply NQmul_le_mono_pos_l. 2: {
   apply NQle_pair; [ pauto | easy | ].
   now do 2 rewrite Nat.mul_1_r; apply Nat_pow_ge_1.
 }
 replace 0%NQ with (0 // 1)%NQ by easy.
 apply NQlt_pair; [ easy | easy | now rewrite Nat.mul_1_l ].
Qed.

(* generalizes carry_upper_bound_for_add *)
Theorem carry_upper_bound_for_adds {r : radix} : ∀ u i m,
  m ≠ 0
  → (∀ k, u (i + k + 1) ≤ m * (rad - 1))
  → ∀ k, carry u (i + k) < m.
Proof.
intros * Hm Hur *.
specialize radix_ge_2 as Hr.
unfold carry.
enough (∀ l, NQintg (A (i + k) (min_n (i + k) l) u) < m). {
  destruct (LPO_fst (fA_ge_1_ε u (i + k))) as [| (j & Hj)]; apply H.
}
intros l.
destruct m; [ easy | ].
apply -> Nat.succ_le_mono.
replace m with (S m - 1) by flia.
apply NQintg_A_le_for_adds.
intros j.
replace (i + k + j + 1) with (i + (k + j) + 1) by flia.
apply Hur.
Qed.

(* Says that if P(u) ends with an infinity of 9s, and u is
   - limited by 18, then u_i is 8, 9 or 18,
   - limited by 27, then u is 7, 8, 9, 17, 18, 19 or 27,
   - and so on.
   This just gives the start u_i of the sequence; the following
   values (u_(i+1), u_(i+2), etc.) are given by an automat
   decribed later.
   Generalizes all_P_9_999_9818_1818 (at least for u_i). *)
Theorem P_999_start {r : radix} : ∀ u i m,
  (∀ k, u (i + k) ≤ m * (rad - 1))
  → (∀ k, P u (i + k) = rad - 1)
  → (∃ j k, 1 ≤ j < m ∧ 1 ≤ k ≤ m ∧ u i = j * rad - k)
     ∨ u i = m * (rad - 1).
Proof.
intros * Hur Hpu.
specialize radix_ge_2 as Hr.
destruct (eq_nat_dec (u i) (m * (rad - 1))) as [H1| H1]; [ now right | left ].
destruct (zerop m) as [Hm| Hm]. {
  exfalso.
  subst m; rewrite Nat.mul_0_l in Hur.
  rewrite Nat.mul_0_l in H1.
  specialize (Hur 0); rewrite Nat.add_0_r in Hur.
  now apply Nat.le_0_r in Hur.
}
apply Nat.neq_0_lt_0 in Hm.
specialize (Hpu 0) as H2.
rewrite Nat.add_0_r in H2.
unfold P, d2n, prop_carr in H2; cbn in H2.
specialize (carry_upper_bound_for_adds u i m Hm) as H3.
assert (H : ∀ k, u (i + k + 1) ≤ m * (rad - 1)). {
  intros; rewrite <- Nat.add_assoc; apply Hur.
}
specialize (H3 H); clear H.
specialize (H3 0) as H4.
rewrite Nat.add_0_r in H4.
destruct (le_dec m rad) as [Hmr| Hmr].
-exists (u i / rad + 1), (carry u i + 1).
 assert (H5 : u i mod rad = rad - 1 - carry u i). {
   specialize (Nat.div_mod (u i + carry u i) rad radix_ne_0) as H5.
   rewrite H2 in H5.
   apply Nat.add_sub_eq_r in H5.
   rewrite <- Nat.add_sub_assoc in H5 by flia H4 Hmr.
   rewrite <- H5, Nat.add_comm, Nat.mul_comm.
   rewrite Nat.mod_add; [ | easy ].
   apply Nat.mod_small.
   flia H4 Hmr.
 }
 specialize (Nat.div_mod (u i) rad radix_ne_0) as H6.
 rewrite H5 in H6.
 rewrite Nat_sub_sub_swap, <- Nat.sub_add_distr in H6.
 rewrite Nat.add_sub_assoc in H6; [ | flia H4 Hmr ].
 replace rad with (rad * 1) in H6 at 3 by flia.
 rewrite <- Nat.mul_add_distr_l, Nat.mul_comm in H6.
 split; [ | split ]; [ | flia H4 | easy ].
 split; [ flia | ].
 specialize (Hur 0) as H7; rewrite Nat.add_0_r in H7.
 assert (H8 : u i < m * (rad - 1)) by flia H1 H7.
 assert (H9 : (u i + carry u i) / rad = u i / rad). {
   specialize (Nat.div_mod (u i + carry u i) rad radix_ne_0) as H9.
   rewrite H2 in H9.
   rewrite Nat.add_sub_assoc in H9; [ | easy ].
   apply (Nat.add_cancel_r _ _ (carry u i + 1)) in H6.
   rewrite Nat.sub_add in H6.
   -rewrite Nat.add_assoc in H6.
    rewrite H9 in H6.
    rewrite Nat.sub_add in H6; [ | flia Hr ].
    replace rad with (rad * 1) in H6 at 3 by flia.
    rewrite <- Nat.mul_add_distr_l in H6.
    rewrite Nat.mul_comm in H6.
    apply Nat.mul_cancel_r in H6; [ | easy ].
    now apply Nat.add_cancel_r in H6.
   -apply (le_trans _ m); [ flia H4 | ].
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
    flia Hmr.
 }
 specialize (Nat.div_mod (u i + carry u i) rad radix_ne_0) as H10.
 rewrite H2, H9 in H10.
 assert (H11 : u i + carry u i + 1 = (u i / rad + 1) * rad). {
   rewrite H10, Nat.mul_comm, Nat.mul_add_distr_r, Nat.mul_1_l.
   rewrite Nat.add_sub_assoc; [ | easy ].
   rewrite Nat.sub_add; [ easy | flia Hr ].
 }
 apply (Nat.mul_lt_mono_pos_r rad); [ easy | ].
 rewrite <- H11.
 destruct (le_dec (rad * (m - 1)) (u i)) as [H12| H12].
 +exfalso.
  move H8 before H12.
  assert (H13 : (u i - rad * (m - 1) + carry u i) mod rad = rad - 1). {
    rewrite <- (Nat.mod_add _ (m - 1)); [ | easy ].
    rewrite Nat.add_shuffle0.
    rewrite Nat.mul_comm, Nat.sub_add; [ easy | now rewrite Nat.mul_comm ].
  }
  specialize (Nat.div_mod (u i - rad * (m - 1) + carry u i) rad radix_ne_0)
    as H14.
  rewrite H13 in H14.
  apply Nat.nle_gt in H8; apply H8; clear H8.
  rewrite <- Nat.add_sub_swap in H14; [ | easy ].
  apply (Nat.add_cancel_r _ _ (rad * (m - 1))) in H14.
  rewrite Nat.sub_add in H14; [ | flia H12 ].
  apply (Nat.add_le_mono_r _ _ (carry u i)).
  rewrite H14.
  rewrite <- Nat.add_assoc.
  eapply le_trans; [ | apply Nat_le_add_l ].
  apply (le_trans _ (m * (rad - 1) + (m - 1))).
  *apply Nat.add_le_mono_l; flia H4.
  *do 2 rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   flia Hmr Hm.
 +apply Nat.nle_gt in H12.
  clear -Hmr H4 H12.
  apply (lt_le_trans _ (rad * (m - 1) + carry u i + 1)).
  *now do 2 apply Nat.add_lt_mono_r.
  *rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   rewrite Nat.mul_comm, <- Nat.add_assoc.
   rewrite <- Nat_sub_sub_distr.
  --apply Nat.le_sub_l.
  --split.
   ++apply (le_trans _ m); [ flia H4 | easy ].
   ++destruct m; [ easy | cbn; flia ].
-apply Nat.nle_gt in Hmr.
 destruct (le_dec (carry u i) (rad - 1)) as [Hcr| Hcr].
 +exists (u i / rad + 1), (carry u i + 1).
  assert (H5 : u i mod rad = rad - 1 - carry u i). {
    specialize (Nat.div_mod (u i + carry u i) rad radix_ne_0) as H5.
    rewrite H2 in H5.
    apply Nat.add_sub_eq_r in H5.
    rewrite <- Nat.add_sub_assoc in H5; [ | easy ].
    rewrite <- H5, Nat.add_comm, Nat.mul_comm.
    rewrite Nat.mod_add; [ | easy ].
    apply Nat.mod_small; flia Hr.
  }
  specialize (Nat.div_mod (u i) rad radix_ne_0) as H6.
  rewrite H5 in H6.
  rewrite Nat_sub_sub_swap, <- Nat.sub_add_distr in H6.
  rewrite Nat.add_sub_assoc in H6; [ | flia Hr Hcr ].
  replace rad with (rad * 1) in H6 at 3 by flia.
  rewrite <- Nat.mul_add_distr_l, Nat.mul_comm in H6.
  split; [ | split ]; [ | flia H4 | easy ].
  split; [ flia | ].
  specialize (Hur 0) as H7; rewrite Nat.add_0_r in H7.
  assert (H8 : u i < m * (rad - 1)) by flia H1 H7.
...
 }
...

Theorem pre_Hugo_Herbelin_112 {r : radix} : ∀ u v i n j,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → n = min_n i 0
  → (∀ k, fA_ge_1_ε (u ⊕ P v) i k = true)
  → (∀ k, fA_ge_1_ε (u ⊕ v) i k = true)
  → (∀ k, k < j → fA_ge_1_ε v i k = true)
  → fA_ge_1_ε v i j = false
  → (NQintg (A i (min_n i j) v) + NQintg (A i n (u ⊕ P v))) mod rad =
     NQintg (A i n (u ⊕ v)) mod rad.
Proof.
(*
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hn H1 H2 Hj Hjj.
assert (H : ∀ k, (u ⊕ P v) (i + k + 1) ≤ 2 * (rad - 1)). {
  intros.
  unfold "⊕".
  replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
  replace (i + k + 1) with (i + (k + 1)) by flia.
  apply Nat.add_le_mono; [ apply Hu | apply digit_le_pred_radix ].
}
specialize (A_ge_1_add_all_true_if _ i H H1) as H'1; clear H.
rewrite Nat.add_comm.
destruct H'1 as [H'1| [H'1| H'1]].
-rewrite A_all_9 by (intros k Hk; apply H'1).
 rewrite NQintg_small. 2: {
   split.
   -apply NQle_0_sub.
    apply NQle_pair; [ pauto | easy | ].
    do 2 rewrite Nat.mul_1_r.
    now apply Nat_pow_ge_1.
   -apply NQsub_lt.
    replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQlt_pair; [ easy | pauto | flia ].
 }
 rewrite Nat.add_0_l.
 f_equal.
 apply A_ge_1_false_iff in Hjj.
...
*)
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hn H1 H2 Hj Hjj.
assert (H : ∀ k, (u ⊕ P v) (i + k + 1) ≤ 2 * (rad - 1)). {
  intros.
  unfold "⊕".
  replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
  replace (i + k + 1) with (i + (k + 1)) by flia.
  apply Nat.add_le_mono; [ apply Hu | apply digit_le_pred_radix ].
}
specialize (A_ge_1_add_all_true_if _ i H H1) as H'1; clear H.
rewrite Nat.add_comm.
do 2 rewrite A_additive.
rewrite NQintg_add; [ symmetry | easy | easy ].
rewrite NQintg_add; [ symmetry | easy | easy ].
do 3 rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
apply A_ge_1_false_iff in Hjj.
rewrite Nat.add_assoc.
rewrite Nat.add_comm.
rewrite NQintg_P_M, Nat.add_0_l.
assert (H : min_n i j = min_n i 0 + rad * j). {
  unfold min_n.
  now rewrite <- Nat.mul_add_distr_l, Nat.add_0_r, Nat.add_shuffle0.
}
rewrite H, <- Hn; clear H.
rewrite <- ApB_A. 2: {
  rewrite Hn; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
}
rewrite NQintg_add; [ | easy | apply B_ge_0 ].
do 2 rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
rewrite Nat.add_assoc.
remember (B i n v (rad * j)) as x eqn:Hx.
specialize (B_upper_bound_for_add v i 0 (rad * j)) as Hb.
assert (H : ∀ j, j ≥ i → v j ≤ 2 * (rad - 1)). {
  intros k Hk.
  replace k with (i + (k - i)) by flia Hk.
  apply Hv.
}
specialize (Hb H); clear H.
rewrite <- Hn, <- Hx, Nat.pow_1_r in Hb.
assert (H : (0 ≤ x < 1)%NQ). {
  split; [ subst x; apply B_ge_0 | ].
  eapply NQlt_trans; [ apply Hb | ].
  apply NQlt_pair; [ easy | easy | ].
  now do 2 rewrite Nat.mul_1_r.
}
rewrite NQintg_small; [ | easy ].
rewrite (NQfrac_small x); [ clear H | easy ].
rewrite Nat.add_0_l.
destruct j.
-rewrite Nat.mul_0_r in Hx; unfold B in Hx.
 rewrite Nat.add_0_r in Hx.
 rewrite summation_empty in Hx. 2: {
   apply Nat.sub_lt; [ | pauto ].
   rewrite Hn; unfold min_n.
   destruct rad; [ easy | cbn; flia ].
 }
 subst x.
 rewrite NQadd_0_r.
 rewrite NQintg_NQfrac, Nat.add_0_l.
 rewrite <- Hn in Hjj.
 clear Hj Hb.
 rewrite Nat.pow_1_r in Hjj.
 specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H1 0) as AA1.
 specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H2 0) as AA2.
 rewrite <- Hn, Nat.pow_1_r in AA1, AA2.
 rewrite A_additive in AA1, AA2.
 rewrite NQfrac_add_cond in AA1; [ | easy | easy ].
 rewrite NQfrac_add_cond in AA2; [ | easy | easy ].
 do 2 rewrite NQintg_add_frac.
 destruct (NQlt_le_dec (NQfrac (A i n u) + NQfrac (A i n (P v))) 1)
   as [H3| H3].
 +rewrite NQsub_0_r in AA1.
  destruct (NQlt_le_dec (NQfrac (A i n u) + NQfrac (A i n v)) 1)
    as [H4| H4]; [ easy | exfalso ].
  (* v<1-1/r u+v≥2-1/r u≥2-1/r-v>2-1/r-1+1/r u>1! *)
  apply NQle_add_le_sub_r in AA2.
  apply NQle_sub_le_add_r in AA2.
  apply NQnlt_ge in AA2; apply AA2; clear AA2.
  apply (NQlt_trans _ (1 + (1 - 1 // rad) - (1 - 1 // rad))%NQ).
  *rewrite NQadd_sub.
   apply NQfrac_lt_1.
  *rewrite NQadd_sub.
   rewrite <- NQadd_sub_assoc.
   apply NQlt_sub_lt_add_l.
   rewrite NQsub_diag.
   apply NQlt_add_lt_sub_r.
   now rewrite NQadd_0_l.
 +destruct (NQlt_le_dec (NQfrac (A i n u) + NQfrac (A i n v)) 1)
     as [H4| H4]; [ exfalso | easy ].
  (* v<1-1/r
        u+p≥2-1/r
        u+v<1
        u+v≥1-1/r *)
  rewrite NQsub_0_r in AA2.
  remember (NQfrac (A i n u)) as au eqn:Hau.
  remember (NQfrac (A i n v)) as av eqn:Hav.
  remember (NQfrac (A i n (P v))) as ap eqn:Hap.
  move au after av; move ap before av.
  move Hau after Hav; move Hap before Hav.
  (* 2-1/r-p≤u<1-v *)
  assert (S1 : (2 - 1 // rad - ap ≤ au < 1 - av)%NQ). {
    split; [ | now apply NQlt_add_lt_sub_r ].
    apply NQle_sub_le_add_r.
    replace 2%NQ with (1 + 1)%NQ by easy.
    rewrite <- NQadd_sub_assoc.
    now apply NQle_add_le_sub_r.
  }
  (* 2-1/r+v<1+p *)
  assert (S2 : (2 - 1 // rad + av < 1 + ap)%NQ). {
    apply NQlt_sub_lt_add_r.
    rewrite NQadd_sub_swap.
    apply NQlt_add_lt_sub_r.
    eapply NQle_lt_trans; apply S1.
  }
  (* v+1-1/r<p<1 *)
  assert (S3 : (av + 1 - 1 // rad < ap < 1)%NQ). {
    split; [ | rewrite Hap; apply NQfrac_lt_1 ].
    replace 2%NQ with (1 + 1)%NQ in S2 by easy.
    rewrite <- NQadd_sub_assoc, <- NQadd_assoc in S2.
    apply NQadd_lt_mono_l in S2.
    rewrite NQadd_comm in S2.
    now rewrite NQadd_sub_assoc in S2.
  }
  (* v<1/r *)
  assert (S4 : (av < 1 // rad)%NQ). {
    apply (NQadd_lt_mono_r _ _ 1%NQ).
    apply NQlt_sub_lt_add_l.
    eapply NQlt_trans; apply S3.
  }
  (* 1-1/r<u<1 *)
  assert (S5 : (1 - 1 // rad < au < 1)%NQ). {
    split; [ | rewrite Hau; apply NQfrac_lt_1 ].
    eapply NQle_lt_trans; [ apply AA1 | ].
    rewrite NQadd_sub_swap, <- NQsub_sub_distr.
    apply NQsub_lt.
    apply NQlt_add_lt_sub_r.
    now rewrite NQadd_0_l.
  }
(*
  assert (H : ∀ k, (u ⊕ P v) (i + k + 1) ≤ 2 * (rad - 1)). {
    intros.
    unfold "⊕".
    replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
    replace (i + k + 1) with (i + (k + 1)) by flia.
    apply Nat.add_le_mono; [ apply Hu | apply digit_le_pred_radix ].
  }
  specialize (A_ge_1_add_all_true_if _ i H H1) as H'1; clear H.
*)
  assert (Hin : i + 1 ≤ n - 1). {
    rewrite Hn; unfold min_n.
    destruct rad; [ easy | cbn; flia ].
  }
  destruct H'1 as [H'1| [H'1| H'1]].
  *apply NQnlt_ge in H3; apply H3; clear H3.
   rewrite Hau, Hap.
   rewrite NQfrac_small. 2: {
     split; [ easy | ].
     apply (NQle_lt_trans _ (A i n (u ⊕ P v))).
     -rewrite A_additive.
      now apply NQle_add_r.
     -rewrite A_all_9; [ | easy ].
      apply NQsub_lt.
      replace 0%NQ with (0 // 1)%NQ by easy.
      apply NQlt_pair; [ easy | pauto | flia ].
   }
   rewrite NQfrac_small. 2: {
     split; [ easy | ].
     apply (NQle_lt_trans _ (A i n (u ⊕ P v))).
     -rewrite A_additive.
      now apply NQle_add_l.
     -rewrite A_all_9; [ | easy ].
      apply NQsub_lt.
      replace 0%NQ with (0 // 1)%NQ by easy.
      apply NQlt_pair; [ easy | pauto | flia ].
   }
   rewrite <- A_additive.
   rewrite A_all_9; [ | easy ].
   apply NQsub_lt.
   replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | pauto | flia ].
  *assert (Hum : ∀ k, u (i + k + 1) = rad - 1). {
     intros k.
     specialize (H'1 k); unfold "⊕" in H'1.
     apply Nat.le_antisymm.
     -rewrite <- Nat.add_assoc; apply Hu.
     -apply (Nat.add_le_mono_r _ _ (P v (i + k + 1))).
      rewrite H'1.
      replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
      apply Nat.add_le_mono_l.
      apply digit_le_pred_radix.
   }
   assert (Hpm : ∀ k, P v (i + k + 1) = rad - 1). {
     intros k.
     specialize (H'1 k); unfold "⊕" in H'1.
     apply (Nat.add_cancel_l _ _ (u (i + k + 1))).
     rewrite H'1.
     replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
     f_equal.
     now rewrite Hum.
   }
   assert (Hu9 : au = (1 - 1 // rad ^ (n - i - 1))%NQ). {
     rewrite Hau.
     rewrite A_all_9; [ | intros; apply Hum ].
     rewrite NQfrac_small; [ easy | ].
     split.
     -apply NQle_add_le_sub_l.
      rewrite NQadd_0_l.
      apply NQle_pair; [ pauto | easy | ].
      rewrite Nat.mul_1_l, Nat.mul_1_r.
      now apply Nat_pow_ge_1.
     -apply NQsub_lt.
      replace 0%NQ with (0 // 1)%NQ by easy.
      apply NQlt_pair; [ easy | pauto | flia ].
   }
   assert (Hv0 : av = 0%NQ). {
     rewrite Hu9 in H4.
     rewrite <- NQadd_sub_swap in H4.
     apply NQlt_sub_lt_add_l in H4.
     rewrite NQadd_comm in H4.
     apply NQadd_lt_mono_r in H4.
     rewrite Hav, A_num_den, NQfrac_pair in H4.
     unfold den_A in H4.
     apply NQlt_pair in H4; [ | pauto | pauto ].
     rewrite Nat.mul_comm in H4.
     apply Nat.mul_lt_mono_pos_l in H4; [ | apply Nat.neq_0_lt_0; pauto ].
     apply Nat.lt_1_r in H4.
     rewrite Hav, A_num_den, NQfrac_pair.
     unfold den_A.
     now rewrite H4.
   }
   move Hv0 at top; subst av.
   symmetry in Hav.
   clear Hjj S2 S4 S5 AA2 H4 H'1.
   rewrite NQadd_0_l in S3.
   rewrite NQsub_0_r in S1.
   move Hav at bottom.
   specialize (all_P_9_all_fA_true v i) as H4.
   assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
     intros; rewrite <- Nat.add_assoc; apply Hv.
   }
   specialize (H4 H Hpm); clear H.
   move H4 before H2.
   specialize (proj1 (frac_ge_if_all_fA_ge_1_ε v i) H4 0) as H5.
   rewrite <- Hn, Hav, Nat.pow_1_r in H5.
   apply NQnlt_ge in H5; apply H5; clear H5.
   apply NQlt_0_sub.
   apply NQlt_pair; [ easy | easy | flia Hr ].
  *destruct H'1 as (j & Hbef & Hwhi & Haft).
   apply NQnlt_ge in H3; apply H3; clear H3.
   rewrite Hau, Hap.
   rewrite NQfrac_small. 2: {
     split; [ easy | ].
     apply (NQle_lt_trans _ (A i n (u ⊕ P v))).
     -rewrite A_additive.
      now apply NQle_add_r.
     -rewrite (A_9_8_all_18 j); [ | easy | easy | easy ].
      apply NQsub_lt.
      replace 0%NQ with (0 // 1)%NQ by easy.
      apply NQlt_pair; [ easy | pauto | ].
      rewrite Nat.mul_1_l.
      destruct (le_dec (i + j + 1) (n - 1)); flia.
   }
   rewrite NQfrac_small. 2: {
     split; [ easy | ].
     apply (NQle_lt_trans _ (A i n (u ⊕ P v))).
     -rewrite A_additive.
      now apply NQle_add_l.
     -rewrite (A_9_8_all_18 j); [ | easy | easy | easy ].
      apply NQsub_lt.
      replace 0%NQ with (0 // 1)%NQ by easy.
      apply NQlt_pair; [ easy | pauto | ].
      rewrite Nat.mul_1_l.
      destruct (le_dec (i + j + 1) (n - 1)); flia.
   }
   rewrite <- A_additive.
   rewrite (A_9_8_all_18 j); [ | easy | easy | easy ].
   apply NQsub_lt.
   replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | pauto | ].
   destruct (le_dec (i + j + 1) (n - 1)); flia.
-specialize (Hj _ (Nat.lt_0_succ _)) as Hj0.
 apply A_ge_1_true_iff in Hj0.
 rewrite <- Hn, Nat.pow_1_r in Hj0.
 destruct (NQlt_le_dec (NQfrac (A i n v) + x) 1) as [Ha1| Ha1].
 +destruct (lt_dec (n - 1) (i + 1)) as [Hin| Hin]. {
    exfalso; apply Nat.nle_gt in Hin; apply Hin.
    rewrite Hn; unfold min_n.
    destruct rad; [ easy | cbn; flia ].
  }
  apply Nat.nlt_ge in Hin.
  rewrite NQintg_small. 2: {
    split; [ | easy ].
    replace 0%NQ with (0 + 0 * 0)%NQ by easy.
    apply NQadd_le_mono; [ easy | ].
    rewrite Hx.
    rewrite B_of_A; [ | flia Hin ].
    now apply NQmul_le_mono_nonneg.
  }
  rewrite Nat.add_0_l.
  f_equal.
  specialize (Hj j (Nat.lt_succ_diag_r _)) as Hj1.
  apply A_ge_1_true_iff in Hj1.
  move Hj1 before Hjj.
  do 2 rewrite NQintg_add_frac.
  destruct (NQlt_le_dec (NQfrac (A i n u) + NQfrac (A i n (P v))) 1)
    as [H3| H3].
  *destruct (NQlt_le_dec (NQfrac (A i n u) + NQfrac (A i n v)) 1)
      as [H4| H4]; [ easy | exfalso ].
   destruct H'1 as [H'1| [H'1| H'1]].
  --idtac.
(**)
...

Theorem pre_Hugo_Herbelin {r : radix} : ∀ u v i,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → carry (u ⊕ v) i mod rad = (carry (u ⊕ P v) i + carry v i) mod rad.
Proof.
intros * Hu Hv.
specialize radix_ge_2 as Hr.
symmetry; rewrite Nat.add_comm.
unfold carry.
remember (min_n i 0) as n eqn:Hn.
destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [H1| H1].
-destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [H2| H2].
 +destruct (LPO_fst (fA_ge_1_ε v i)) as [H3| H3].
  *now apply pre_Hugo_Herbelin_111.
  *destruct H3 as (j & Hj & Hjj).
...
   now apply pre_Hugo_Herbelin_112.
 +destruct H2 as (j & Hjj & Hj).
  apply A_ge_1_false_iff in Hj.
  destruct (LPO_fst (fA_ge_1_ε v i)) as [H3| H3].
  *idtac.
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
  add_series (λ j, dig (ureal x j)) (y ⊕ z)%F i =
  add_series (λ j, dig (ureal z j)) (y ⊕ x)%F i.
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
do 2 rewrite truc.
intros i.
unfold ureal_normalize, fd2n; cbn.
apply digit_eq_eq.
do 2 rewrite fold_P.
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
*)
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
