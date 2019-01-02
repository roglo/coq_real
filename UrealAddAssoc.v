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

Theorem all_fA_ge_1_ε_999 {r : radix} : ∀ u i,
  (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k, P u (i + k + 1) = rad - 1.
Proof.
intros * Hu *.
apply fA_ge_1_ε_999.
intros l.
apply A_ge_1_add_r_true_if, Hu.
Qed.

(*
Theorem fA_ge_1_ε_999_P {r : radix} : ∀ u i,
  (∀ k, fA_ge_1_ε u i k = true)
  → P u i ≠ rad - 1
  → P u i = u i mod rad.
Proof.
intros * Hu Hp.
unfold P, d2n, prop_carr in Hp; cbn in Hp.
unfold P, d2n, prop_carr; cbn.
replace (u i) with (u i + 0) at 2 by flia.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal; rewrite Nat.mod_0_l; [ | easy ].
unfold carry in Hp; unfold carry.
destruct (LPO_fst (fA_ge_1_ε u i)) as [H1| H1]. 2: {
  destruct H1 as (j & Hj & H1).
  now rewrite Hu in H1.
}
clear H1.
remember (min_n i 0) as n eqn:Hn.
move n before i.
specialize (all_fA_ge_1_ε_999 _ _ Hu) as H1.
unfold P, d2n, prop_carr in H1; cbn in H1.
(* theorem false, counter example: u=3/9/9/2009/9/9... P(u)=5/9/9/9/9... *)
Search (NQintg (A _ _ _)).
Search ((rad - 1) ^ 2).
...
Theorem glop :
  (∀ k, u (i + k) ≤ (i + k + 1) * (rad - 1) ^ 2)
  → ...
...
*)

(* is it true? is it required?
Theorem P_additive {r : radix} : ∀ u v i,
  P (u ⊕ v) i = (P u i + P v i) mod rad.
Proof.
(*
intros.
destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [H1| H1].
-destruct (LPO_fst (fA_ge_1_ε u i)) as [H2| H2].
 +destruct (LPO_fst (fA_ge_1_ε v i)) as [H3| H3].
  *rewrite fA_ge_1_ε_999_P; [ | easy ].
   rewrite fA_ge_1_ε_999_P; [ | easy ].
   rewrite fA_ge_1_ε_999_P; [ | easy ].
   now rewrite <- Nat.add_mod.
  *idtac.
...
*)
intros.
unfold P, prop_carr, d2n; cbn.
unfold carry.
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite Nat.add_mod_idemp_r; [ | easy ].
rewrite Nat.add_shuffle0, Nat.add_assoc.
rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [H1| H1].
-destruct (LPO_fst (fA_ge_1_ε u i)) as [H2| H2].
 +destruct (LPO_fst (fA_ge_1_ε v i)) as [H3| H3].
  *specialize (frac_ge_if_all_fA_ge_1_ε _ _ H1 0) as H1'.
   specialize (frac_ge_if_all_fA_ge_1_ε _ _ H2 0) as H2'.
   specialize (frac_ge_if_all_fA_ge_1_ε _ _ H3 0) as H3'.
   rewrite Nat.pow_1_r in H1', H2', H3'.
   rewrite A_additive in H1'.
   remember (min_n i 0) as n eqn:Hn.
   rewrite NQfrac_add in H1'; [ | pauto | pauto ].
   rewrite A_additive.
   rewrite NQintg_add; [ | pauto | pauto ].
   symmetry; rewrite Nat.add_comm; symmetry.
   remember (NQintg (A i n u) + NQintg (A i n v)) as x eqn:Hx.
   replace x with (x + 0) at 2 by flia.
   rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
   rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
   f_equal; f_equal; rewrite Nat.mod_0_l; [ | easy ].
   clear x Hx.
   (*exfalso*)
...
   specialize (all_fA_ge_1_ε_999 _ _ H1) as H'1.
   specialize (all_fA_ge_1_ε_999 _ _ H2) as H'2.
   specialize (all_fA_ge_1_ε_999 _ _ H3) as H'3.
   unfold P, d2n, prop_carr in H'1, H'2, H'3.
   cbn in H'1, H'2, H'3.
   unfold carry in H'1, H'2, H'3.
   assert (H''1 :
     ∀ k,
       (u (i + k + 1) + v (i + k + 1) +
        NQintg
          (A (i + k + 1) (min_n (i + k + 1) 0) u +
           A (i + k + 1) (min_n (i + k + 1) 0) v)) mod rad =
       rad - 1). {
     intros; specialize (H'1 k).
     destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) (i + k + 1))) as [H| H].
     -now rewrite A_additive in H'1.
     -destruct H as (j & Hj & Hjj).
      rewrite <- Nat.add_assoc in Hjj.
      rewrite A_ge_1_add_r_true_if in Hjj; [ easy | apply H1 ].
   }
   move H''1 before H'1; clear H'1; rename H''1 into H'1.
   assert (H''2 :
     ∀ k,
       (u (i + k + 1) +
        NQintg (A (i + k + 1) (min_n (i + k + 1) 0) u)) mod rad = rad - 1). {
     intros; specialize (H'2 k).
     destruct (LPO_fst (fA_ge_1_ε u (i + k + 1))) as [H| H]; [ easy | ].
     destruct H as (j & Hj & Hjj).
     rewrite <- Nat.add_assoc in Hjj.
     rewrite A_ge_1_add_r_true_if in Hjj; [ easy | apply H2 ].
   }
   move H''2 before H'2; clear H'2; rename H''2 into H'2.
   assert (H''3 :
     ∀ k,
       (v (i + k + 1) +
        NQintg (A (i + k + 1) (min_n (i + k + 1) 0) v)) mod rad = rad - 1). {
     intros; specialize (H'3 k).
     destruct (LPO_fst (fA_ge_1_ε v (i + k + 1))) as [H| H]; [ easy | ].
     destruct H as (j & Hj & Hjj).
     rewrite <- Nat.add_assoc in Hjj.
     rewrite A_ge_1_add_r_true_if in Hjj; [ easy | apply H3 ].
   }
   move H''3 before H'3; clear H'3; rename H''3 into H'3.
Search (NQintg (_ + _)).
assert (H : ∀ k,
  (2 * rad - 2 + NQintg (NQfrac (A (i + k + 1) (min_n (i + k + 1) 0) u) + NQfrac (A (i + k + 1) (min_n (i + k + 1) 0) v))) mod rad = rad - 1). {
  intros k.
  specialize (H'1 k); specialize (H'2 k); specialize (H'3 k).
  rewrite NQintg_add in H'1; [ | easy | easy ].
  remember (A (i + k + 1) (min_n (i + k + 1) 0) u) as x eqn:Hx.
  remember (A (i + k + 1) (min_n (i + k + 1) 0) v) as y eqn:Hy.
  move y before x.
  rewrite Nat.add_assoc in H'1.
  rewrite Nat.add_shuffle1 in H'1.
  rewrite <- Nat.add_assoc in H'1.
  rewrite <- Nat.add_mod_idemp_l in H'1; [ | easy ].
  rewrite H'2, Nat.add_comm, <- Nat.add_assoc in H'1.
  rewrite <- Nat.add_mod_idemp_l in H'1; [ | easy ].
  rewrite H'3 in H'1; rewrite <- H'1.
  f_equal.
  rewrite Nat.add_comm; symmetry.
  rewrite Nat.add_comm; symmetry.
  rewrite <- Nat.add_assoc; f_equal.
  flia.
}
...
*)

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
split; [ easy | ].
apply A_M_upper_bound.
Qed.

Theorem NQintg_P_M {r : radix} : ∀ i n u, NQintg (A i n (P u)) = 0.
Proof.
intros.
apply NQintg_small.
split; [ easy | ].
apply A_M_upper_bound.
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

Theorem pre_Hugo_Herbelin {r : radix} : ∀ u v i,
  carry (u ⊕ v) i mod rad = (carry (u ⊕ P v) i + carry v i) mod rad.
Proof.
intros.
specialize radix_ge_2 as Hr.
symmetry; rewrite Nat.add_comm.
unfold carry.
remember (min_n i 0) as n eqn:Hn.
destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [H1| H1].
-destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [H2| H2].
 +rewrite Nat.add_comm.
  destruct (LPO_fst (fA_ge_1_ε v i)) as [H3| H3].
  *do 2 rewrite A_additive.
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
   specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H2 0) as AA2.
   rewrite <- Hn, A_additive, Nat.pow_1_r in AA2.
   rewrite NQfrac_add_cond in AA2; [ | easy | easy ].
   do 2 rewrite NQintg_add_frac.
   destruct (NQlt_le_dec (NQfrac (A i n u) + NQfrac (A i n v)) 1)
      as [AA3| AA3].
  --destruct (NQlt_le_dec (NQfrac (A i n u) + NQfrac (A i n (P v))) 1)
      as [AA1| AA1]; [ easy | ].
    exfalso.
    move AA1 after AA2; move AA3 after AA2.
    rewrite NQfrac_P_M in AA1.
    specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H3 0) as H'3.
    rewrite <- Hn, Nat.pow_1_r in H'3.
    (* AA2 useless because of H'3 *)
    clear AA2.
(* d'après H3, A i n (P v) n'a que des 9 ; donc, d'après AA1, u n'a pas
   que des 0 entre i+1 et n-1, sinon ça ne serait pas assez pour dépasser
   1. Donc v ne peut pas avoir que des 9, ça contradirait AA3. Du coup,
   comment est v ? P(v) est 999... mais pas v. D'après H'3, v est supérieur
   ou égal à 9000... Donc, d'après AA3, u est inférieur à 1000... *)
(*
   u ≥ 0/0/0...0/0/1
   P(v)=9/9/9...9/9/9
   u⊕P(v)≥9/9/9...9/9/10
   P(u⊕P(v))≥1/0/0/0...0/0/0
   or, d'après H1, P(u⊕P(v))=9/9/9...9/9/9 → contradiction
*)
    set (s := n - i - 1).
    assert (H4 : (A i n (P v) = 1 - 1 // rad ^ s)%NQ). {
      unfold A.
      rewrite summation_eq_compat with
         (h := λ j, ((rad - 1) // rad ^ (j - i))%NQ). 2: {
        intros j Hj.
        f_equal.
        replace j with (i + (j - i - 1) + 1) by flia Hj.
        now apply all_fA_ge_1_ε_999.
      }
      rewrite NQsummation_pair_distr_l.
      assert (Hin : i + 1 ≤ n - 1). {
        rewrite Hn; unfold min_n.
        destruct rad; [ easy | cbn; flia ].
      }
      rewrite summation_shift; [ | easy ].
      rewrite summation_eq_compat with
        (h := λ j, (1 // rad * 1 // rad ^ j)%NQ). 2: {
        intros j Hj.
        replace (i + 1 + j - i) with (1 + j) by flia.
        rewrite Nat.pow_add_r, Nat.pow_1_r.
        rewrite NQmul_pair; [ | easy | pauto ].
        now rewrite Nat.mul_1_l.
      }
      rewrite <- summation_mul_distr_l.
      rewrite NQpower_summation; [ | easy ].
      replace (n - 1 - (i + 1)) with (s - 1) by flia.
      replace (S (s - 1)) with s by flia Hin.
      rewrite NQmul_pair; [ | easy | ]. 2: {
        apply Nat.neq_mul_0.
        split; [ pauto | flia Hr ].
      }
      rewrite Nat.mul_1_l.
      rewrite NQmul_pair; [ | easy | ]. 2: {
        apply Nat.neq_mul_0.
        split; [ easy | ].
        apply Nat.neq_mul_0.
        split; [ pauto | flia Hr ].
      }
      rewrite Nat.mul_1_l, Nat.mul_comm, Nat.mul_assoc.
      rewrite <- NQmul_pair; [ | | flia Hr ]. 2: {
        apply Nat.neq_mul_0.
        split; [ easy | pauto ].
      }
      rewrite NQpair_diag; [ | flia Hr ].
      rewrite NQmul_1_r.
      replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
      rewrite <- Nat.pow_add_r.
      replace (1 + (s - 1)) with s by flia Hin.
      rewrite NQsub_pair_pos; [ | easy | pauto | ]. 2: {
        do 2 rewrite Nat.mul_1_l.
        now apply Nat_pow_ge_1.
      }
      now do 2 rewrite Nat.mul_1_l.
    }
    assert (H5 : (NQfrac (A i n u) ≥ 1 // rad ^ s)%NQ). {
      rewrite H4, NQadd_comm, <- NQadd_sub_swap, <- NQadd_sub_assoc in AA1.
      apply NQle_sub_le_add_l in AA1.
      rewrite NQsub_diag in AA1.
      apply NQle_sub_le_add_r in AA1.
      now rewrite NQsub_opp_r, NQadd_0_l in AA1.
    }
...
    assert (H6 : u ⊕ P v ≥ 9/9/9...9/9/10
...
  --destruct (NQlt_le_dec (NQfrac (A i n u) + NQfrac (A i n (P v))) 1)
      as [AA3| AA3]; [ | easy ].
    exfalso.
    rewrite NQfrac_P_M in AA3.
    (* if I prove that NQfrac (A i n u) ≤ A i n (P u), it works *)
...
  *destruct H3 as (j & Hj & Hjj).
...
    specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H1) as H'1.
    specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H2) as H'2.
    specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H3) as H'3.
...
    specialize (all_fA_ge_1_ε_999 _ _ H1) as H'1.
    specialize (all_fA_ge_1_ε_999 _ _ H2) as H'2.
    specialize (all_fA_ge_1_ε_999 _ _ H3) as H'3.
...

Theorem Hugo_Herbelin {r : radix} : ∀ u v i,
  (∀ k : nat, v (i + k + 1) ≤ 2 * (rad - 1))
  → P (u ⊕ P v) i = P (u ⊕ v) i.
Proof.
intros * Hv.
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
...

intros * Hv.
specialize radix_ge_2 as Hr.
unfold P, add_series.
remember (prop_carr v) as pv eqn:Hpv; cbn.
replace (λ i, u i + v i) with (u ⊕ v) by easy.
replace (λ i, u i + d2n pv i) with (u ⊕ d2n pv) by easy.
do 2 rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
rewrite Hpv at 1; cbn.
(*
...
intros * Hv.
specialize radix_ge_2 as Hr.
unfold P, add_series; cbn.
do 2 rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
*)
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite <- Nat.add_assoc.
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
f_equal; f_equal.
subst pv.
replace (d2n (prop_carr v)) with (P v) by easy.
(**)
transitivity ((carry v i + carry (u ⊕ M (v ⊕ carry v)) i) mod rad). {
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  f_equal; f_equal.
}
...
unfold carry at 1 2 4.

...
rename i into j.
Print carry.
Search (fA_ge_1_ε (_ ⊕ _)%F).
About A_ge_1_ureal_add_series_comm.
unfold carry at 2.
2: easy.
...
unfold carry at 1.
destruct (LPO_fst (fA_ge_1_ε v j)) as [H1| H1].
-specialize (A_ge_1_add_all_true_if v j Hv H1) as H2.
 destruct H2 as [H2| [H2| H2]].
 +unfold NQintg.
  rewrite Nat.div_small; cycle 1. {
    rewrite A_all_9; [ | intros; apply H2 ].
    remember (min_n j 0) as n eqn:Hn.
    remember (n - j - 1) as s eqn:Hs.
    move s before n.
    rewrite NQsub_pair_pos; [ | easy | pauto | ]; cycle 1. {
      now apply Nat.mul_le_mono_l, Nat_pow_ge_1.
    }
    do 2 rewrite Nat.mul_1_l.
    rewrite NQnum_pair, NQden_pair.
    rewrite Nat.max_r; [ | now apply Nat_pow_ge_1 ].
    remember (Nat.gcd (rad ^ s - 1) (rad ^ s)) as g eqn:Hg.
    assert (Hgz : g ≠ 0). {
      rewrite Hg; intros H.
      now apply Nat.gcd_eq_0_r, Nat.pow_nonzero in H.
    }
    rewrite Nat.max_r; cycle 1. {
      apply (Nat.mul_le_mono_pos_l _ _ g); [ now apply Nat.neq_0_lt_0 | ].
      rewrite Nat.mul_1_r.
      rewrite <- Nat.divide_div_mul_exact; [ | easy | ].
      -rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
       now rewrite Hg; apply Nat_gcd_le_r, Nat.pow_nonzero.
      -rewrite Hg; apply Nat.gcd_divide_r.
    }
    apply (Nat.mul_lt_mono_pos_l g); [ flia Hgz | ].
    rewrite <- Nat.divide_div_mul_exact; [ | easy | ]; cycle 1. {
      rewrite Hg; apply Nat.gcd_divide_l.
    }
    rewrite <- Nat.divide_div_mul_exact; [ | easy | ]; cycle 1. {
      rewrite Hg; apply Nat.gcd_divide_r.
    }
    rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
    rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
    apply Nat.sub_lt; [ | pauto ].
    now apply Nat_pow_ge_1.
  }
  rewrite Nat.add_0_l.
...

Theorem truc {r : radix} : ∀ x u,
  ({| ureal := prop_carr (x ⊕ {| ureal := prop_carr u |}) |} =
   {| ureal := prop_carr (add_series (fd2n x) (d2n (prop_carr u))) |})%F.
Proof. easy. Qed.

Theorem pouet {r : radix} : ∀ x y z i,
  add_series (λ j, dig (ureal x j)) (y ⊕ z) i =
  add_series (λ j, dig (ureal z j)) (y ⊕ x) i.
Proof.
intros.
unfold add_series, "⊕", fd2n.
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
unfold ureal_normalize, fd2n; simpl.
apply digit_eq_eq.
rewrite <- prop_carr_normalizes; cycle 1. {
  intros j.
  apply (ureal_add_series_le_twice_pred x {| ureal := prop_carr (y ⊕ z) |} j).
}
rewrite <- prop_carr_normalizes; cycle 1. {
  intros j.
  apply (ureal_add_series_le_twice_pred z {| ureal := prop_carr (y ⊕ x) |} j).
}
do 2 rewrite Hugo_Herbelin.
apply prop_carr_eq_compat.
intros j.
apply pouet.
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
