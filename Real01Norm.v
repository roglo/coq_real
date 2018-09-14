Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz NPeano.
Require Import Misc Summation FracReal.

Definition is_num_9_strict_after {r : radix} u i j :=
  if eq_nat_dec (u (i + j + 1)) (rad - 1) then true else false.

Theorem is_num_9_strict_after_all_9 {r : radix} : ∀ u i,
  (∀ j, is_num_9_strict_after u i j = true)
  → (∀ k, u (i + k + 1) = rad - 1).
Proof.
intros * Hm9 *.
specialize (Hm9 k); unfold is_num_9_strict_after in Hm9.
now destruct (Nat.eq_dec (u (i + k + 1)) (rad - 1)).
Qed.

Theorem is_num_9_strict_after_true_iff {r : radix} : ∀ i j u,
  is_num_9_strict_after u i j = true ↔ u (i + j + 1) = rad - 1.
Proof.
intros.
unfold is_num_9_strict_after.
now destruct (Nat.eq_dec (u (i + j + 1)) (rad - 1)).
Qed.

Theorem is_num_9_strict_after_false_iff {r : radix} : ∀ i j u,
  is_num_9_strict_after u i j = false ↔ u (i + j + 1) ≠ rad - 1.
Proof.
intros.
unfold is_num_9_strict_after.
now destruct (Nat.eq_dec (u (i + j + 1)) (rad - 1)).
Qed.

Theorem u_9_8_18_nA_ge_999000 {r : radix} : ∀ u n j j1 n1 s1,
  (∀ k, k < S j → u (n + k + 1) = rad - 1)
  → u (n + S j + 1) = rad - 2
  → (∀ k, u (n + S j + k + 2) = 2 * (rad - 1))
  → n1 = rad * (n + 1 + j1 + 3)
  → s1 = n1 - (n + 1) - 1
  → (rad ^ S j1 - 1) * rad ^ (s1 - S j1) ≤ nA (n + 1) n1 u.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hbef Hwhi Haft Hn1 Hs1.
unfold nA.
assert (Hsjs1 : S j1 + (s1 - S j1) = s1). {
  rewrite Hs1, Hn1.
  destruct rad; [ easy | simpl; flia ].
}
assert (Hs12 : 2 ≤ s1). {
  rewrite Hs1, Hn1.
  destruct rad; [ easy | simpl; flia ].
}
assert (H2rsj : 2 ≤ rad ^ (s1 - S j1)). {
  destruct (zerop (s1 - S j1)) as [Hsj| Hsj].
  -rewrite Hs1, Hn1 in Hsj.
   destruct rad; [ easy | simpl in Hsj; flia Hsj ].
  -destruct (s1 - S j1) as [| x]; [ flia Hsj | simpl ].
   replace 2 with (2 * 1) by flia.
   apply Nat.mul_le_mono; [ easy | ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite summation_eq_compat with
    (h := λ k,
          (if le_dec k (n + j + 1) then rad - 1
           else if eq_nat_dec k (n + j + 2) then rad - 2
                else 2 * (rad - 1)) *
          rad ^ (n1 - 1 - k)).
-destruct (zerop j) as [Hj| Hj].
 +subst j; rewrite Nat.add_0_r.
  rewrite summation_split_first.
  *destruct (le_dec (n + 1 + 1) (n + 1)) as [H1| H1]; [ flia H1 | clear H1 ].
   destruct (Nat.eq_dec (n + 1 + 1) (n + 2)) as [H1| H1]; [ | flia H1 ].
   clear H1; remember S as f; simpl; subst f.
   replace (n1 - 1 - (n + 1 + 1)) with (s1 - 1) by flia Hs1.
   rewrite summation_eq_compat with
     (h := λ i, 2 * (rad - 1) * rad ^ (n1 - 1 - i)).
  --rewrite <- summation_mul_distr_l.
    remember S as f; simpl; subst f.
    rewrite summation_rtl.
    rewrite summation_shift.
   **rewrite summation_eq_compat with (h := λ k, rad ^ k).
   ---replace (n1 - 1 - S (n + 1 + 1)) with (s1 - 2) by flia Hs1.
      rewrite <- Nat.mul_assoc.
      rewrite <- power_summation_sub_1; [ | easy ].
      rewrite <- Nat.sub_succ_l; [ | easy ].
      rewrite Nat.sub_succ.
      rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
      rewrite Nat.add_sub_assoc.
    +++remember (rad ^ S j1 - 1) as x eqn:Hx.
       rewrite Nat.mul_sub_distr_r; subst x.
       rewrite Nat.sub_add; [ | now apply Nat.mul_le_mono_r ].
       rewrite <- Nat.pow_succ_r'.
       replace (S (s1 - 1)) with s1 by flia Hs12.
       rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
       rewrite <- Nat.pow_add_r, Hsjs1.
       now apply Nat.sub_le_mono_l.
    +++replace 2 with (2 * 1) at 1 by flia.
       apply Nat.mul_le_mono_l.
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   ---intros i Hi; f_equal; flia Hi.
   **rewrite Hn1.
     destruct rad; [ easy | simpl; flia ].
  --intros i Hi; f_equal.
    destruct (le_dec i (n + 1)) as [H1| H1]; [ flia Hi H1 | ].
    destruct (Nat.eq_dec i (n + 2)) as [H2| H2]; [ flia Hi H2 | easy ].
  *rewrite Hn1.
   destruct rad; [ easy | simpl; flia ].
 +destruct (le_dec (n + j + 1) (n1 - 1)) as [Hnn| Hnn].
  *rewrite summation_split with (e := n + j + 1); [ | flia Hj Hnn ].
   remember S as f; simpl; subst f.
   rewrite summation_eq_compat with
       (h := λ k, (rad - 1) * rad ^ (n1 - 1 - k)).
  --rewrite <- summation_mul_distr_l.
    remember S as f; simpl; subst f.
    rewrite summation_rtl.
    rewrite summation_shift; [ | flia Hj ].
    replace (n + j + 1 - (n + 1 + 1)) with (j - 1) by flia.
    rewrite summation_eq_compat with (h := λ i, rad ^ i * rad ^ (s1 - j)).
   ++rewrite <- summation_mul_distr_r.
     rewrite Nat.mul_assoc.
     rewrite <- power_summation_sub_1; [ | easy ].
     replace (S (j - 1)) with j by flia Hj.
     destruct (eq_nat_dec (n + j + 1) (n1 - 1)) as [H1| H1].
    **rewrite H1, summation_empty; [ | apply Nat.lt_succ_diag_r ].
      rewrite Nat.add_0_r.
      remember S as f; simpl; subst f.
      do 2 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
      do 2 rewrite <- Nat.pow_add_r.
      rewrite Hsjs1.
      replace (j + (s1 - j)) with s1 by flia Hs1 H1.
      apply Nat.sub_le_mono_l.
      apply Nat.pow_le_mono_r; [ easy | ].
      apply Nat.sub_le_mono_l; flia Hsjs1 Hs1 H1.
    **rewrite summation_split_first; [ | flia Hnn H1 ].
      remember (n + j + 1) as x.
      replace (n + j + 2) with (x + 1) by flia Heqx.
      destruct (le_dec (S x) x) as [H2| H2]; [ flia H2 | clear H2 ].
      destruct (eq_nat_dec (S x) (x + 1)) as [H2| H2]; [ clear H2 | flia H2 ].
      destruct (le_dec (S (S x)) (n1 - 1)) as [H2| H2].
    ---rewrite summation_eq_compat with
         (h := λ i, 2 * (rad - 1) * (rad ^ (n1 - 1 - i))).
     +++rewrite <- summation_mul_distr_l.
        remember S as f; simpl; subst f.
        rewrite summation_rtl.
        rewrite summation_shift; [ | easy ].
        rewrite summation_eq_compat with (h := λ i, rad ^ i).
      ***rewrite <- Nat.mul_assoc.
         rewrite <- power_summation_sub_1; [ | easy ].
         replace (n1 - 1 - S x) with (s1 - j - 1) by flia Hs1 Heqx.
         replace (S (n1 - 1 - S (S x))) with (s1 - j - 1) by flia Hs1 H2 Heqx.
         subst x.
         do 2 rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r, Nat.mul_1_l.
         rewrite Hsjs1.
         replace (j + (s1 - j)) with s1 by flia Hs1 Hnn.
         rewrite Nat.mul_sub_distr_r.
         rewrite <- Nat.pow_succ_r'.
         replace (S (s1 - j - 1)) with (s1 - j) by flia Hs1 Hnn H1.
         rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
         rewrite Nat.add_sub_assoc.
      ----rewrite Nat.sub_add.
       ++++rewrite Nat.add_sub_assoc.
        ****rewrite Nat.sub_add; [ now apply Nat.sub_le_mono_l | ].
            apply Nat.pow_le_mono_r; [ easy | flia ].
        ****remember (s1 - j) as x eqn:Hx.
            destruct x; [ flia Hs1 H2 Hx | ].
            simpl; replace 2 with (2 * 1) by flia.
            apply Nat.mul_le_mono; [ easy | ].
            now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
       ++++replace (s1 - j) with (s1 - j - 1 + 1) by flia Hs1 Hnn H1.
           rewrite Nat.add_sub, Nat.pow_add_r, Nat.mul_comm, Nat.pow_1_r.
           now apply Nat.mul_le_mono_l.
      ----replace 2 with (2 * 1) by flia.
          apply Nat.mul_le_mono_l.
          now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
      ***intros i Hi; f_equal; flia Hi.
     +++intros i Hi.
        destruct (le_dec i x) as [H3| H3]; [ flia Hi H3 | ].
        destruct (eq_nat_dec i (x + 1)) as [H4| H4]; [ flia Hi H4 | easy ].
    ---apply Nat.nle_gt in H2; subst x.
       assert (Hnj : n + j + 1 = n1 - 2) by flia H1 H2 Hnn.
       assert (Hsjj : S j1 ≤ j). {
         rewrite Hn1 in Hnj.
         destruct rad; [ easy | simpl in Hnj; flia Hnj ].
       }
       apply le_plus_trans.
       do 2 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
       do 2 rewrite <- Nat.pow_add_r.
       rewrite Hsjs1.
       replace (j + (s1 - j)) with s1 by flia Hs1 Hnj.
       apply Nat.sub_le_mono_l.
       apply Nat.pow_le_mono_r; [ easy | ].
       now apply Nat.sub_le_mono_l.
   ++intros i Hi; rewrite <- Nat.pow_add_r; f_equal.
     rewrite Hs1; flia Hnn Hi.
  --intros i Hi.
    destruct (le_dec i (n + j + 1)) as [H1| H1]; [ easy | flia Hi H1 ].
  *apply Nat.nle_gt in Hnn.
   rewrite summation_eq_compat with
     (h := λ i, (rad - 1) * rad ^ (n1 - 1 - i)).
  --rewrite <- summation_mul_distr_l.
    rewrite summation_rtl.
    rewrite summation_shift; [ | flia Hs1 Hsjs1 ].
    replace (n1 - 1 - (n + 1 + 1)) with (s1 - 1) by flia Hs1.
    rewrite summation_eq_compat with (h := λ i, rad ^ i).
   ++rewrite <- power_summation_sub_1; [ | easy ].
     replace (S (s1 - 1)) with s1 by flia Hs12.
     rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
     rewrite <- Nat.pow_add_r, Hsjs1.
     apply Nat.sub_le_mono_l.
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   ++intros i Hi; f_equal; flia Hs1 Hi.
  --intros i Hi.
    destruct (le_dec i (n + j + 1)) as [H1| H1]; [ easy | flia Hnn Hi H1 ].
-intros k Hk; f_equal.
 destruct (le_dec k (n + j + 1)) as [H1| H1].
 +specialize (Hbef (k - n - 1)) as H2.
  replace (n + (k - n - 1) + 1) with k in H2 by flia Hk.
  apply H2; flia H1 Hk.
 +apply Nat.nle_gt in H1.
  destruct (eq_nat_dec k (n + j + 2)) as [H2| H2].
  **now replace (n + S j + 1) with k in Hwhi by flia H2.
  **specialize (Haft (k - n - j - 3)) as H3.
    replace (n + S j + (k - n - j - 3) + 2) with k in H3; [ easy | ].
    flia H1 H2.
Qed.

Theorem u_18_nA_mod_ge_999000 {r : radix} : ∀ u n1 s1 j1 n,
  (∀ k, u (n + k + 2) = 2 * (rad - 1))
  → n1 = rad * (n + 1 + j1 + 3)
  → s1 = n1 - (n + 1) - 1
  → rad ^ s1 ≤ nA (n + 1) n1 u
  → 0 < s1
  → (rad ^ S j1 - 1) * rad ^ (s1 - S j1) ≤ nA (n + 1) n1 u mod rad ^ s1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hall Hn1 Hs1 H1 Hjs.
rewrite Nat_mod_less_small.
-assert (Hjs1 : S j1 < s1). {
   rewrite Hs1, Hn1.
   destruct rad; [ easy | simpl; flia ].
 }
 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
 rewrite <- Nat.pow_add_r.
 replace (S j1 + (s1 - S j1)) with s1 by flia Hjs1.
 rewrite nA_eq_compat with (v := λ k, 2 * (rad - 1)).
 +unfold nA.
  rewrite <- summation_mul_distr_l.
  rewrite summation_rtl.
  rewrite summation_shift.
  *remember S as f; simpl; subst f.
   replace (n1 - 1 - (n + 1 + 1)) with (s1 - 1) by flia Hs1.
   rewrite summation_eq_compat with (h := λ i, rad ^ i).
   --rewrite <- Nat.mul_assoc.
     rewrite <- power_summation_sub_1; [ | easy ].
     replace (S (s1 - 1)) with s1 by flia Hjs.
     rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
     rewrite Nat_sub_sub_swap.
     replace (2 * rad ^ s1 - rad ^ s1) with (rad ^ s1) by flia.
     apply Nat.sub_le_mono_l.
     destruct (zerop (s1 - S j1)) as [H2| H2]; [ flia Hjs1 H2 | ].
     destruct (s1 - S j1); [ easy | ].
     simpl; replace 2 with (2 * 1) by flia.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   --intros i Hi; f_equal; flia Hs1 Hi.
  *rewrite Hn1.
   destruct rad; [ easy | simpl; flia ].
 +intros j Hj.
  specialize (Hall (j - n - 2)).
  now replace (n + (j - n - 2) + 2) with j in Hall by flia Hj.
-split; [ easy | ].
 specialize (nA_upper_bound_for_add u (n + 1) n1) as H2.
 rewrite <- Hs1 in H2.
 assert (H : ∀ k, u (n + 1 + k + 1) ≤ 2 * (rad - 1)). {
   intros k.
   replace (n + 1 + k + 1) with (n + k + 2) by flia.
   now rewrite Hall.
 }
 specialize (H2 H); clear H.
 rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H2.
 eapply le_lt_trans; [ apply H2 | ].
 specialize (Nat.pow_nonzero rad s1 radix_ne_0) as H.
 flia H2 H.
Qed.

Theorem A_ge_rad_pow {r : radix} : ∀ u i n,
  (∀ k, u (S i + k + 1) ≤ 2 * (rad - 1))
  → rad ^ (n - i - 1) ≤ nA i n u
  → ∃ j,
    j < n - i - 1 ∧
    (∀ k, k < j → u (i + k + 1) = rad - 1) ∧
    u (i + j + 1) ≥ rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hra.
remember (n - i - 1) as m eqn:Hm.
symmetry in Hm.
revert i n Hur Hm Hra.
induction m; intros.
-unfold nA in Hra.
 rewrite summation_empty in Hra; [ easy | flia Hm ].
-destruct n; [ easy | ].
 assert (Hm' : n - i - 1 = m) by flia Hm.
 destruct (le_dec (i + 1) n) as [Hin| Hin]; [ | flia Hin Hm ].
 rewrite nA_split_first in Hra; [ | flia Hin ].
 destruct (le_dec rad (u (i + 1))) as [H1| H1].
 +exists 0.
  split; [ apply Nat.lt_0_succ | ].
  split; [ now intros | ].
  now rewrite Nat.add_0_r.
 +apply Nat.nle_gt in H1.
  replace (S n - i - 2) with m in Hra by flia Hm.
  destruct (le_dec (u (i + 1)) (rad - 2)) as [H2| H2].
  *exfalso; apply Nat.nlt_ge in Hra.
   apply Hra; clear Hra.
   specialize (nA_upper_bound_for_add u (S i) (S n) Hur) as H3.
   replace (S n - S i - 1) with m in H3 by flia Hm'.
   apply le_lt_trans with (m := (rad - 2) * rad ^ m + 2 * (rad ^ m - 1)).
  --apply Nat.add_le_mono; [ | easy ].
    now apply Nat.mul_le_mono_r.
  --rewrite Nat.mul_sub_distr_r, Nat.mul_sub_distr_l, Nat.mul_1_r.
    rewrite Nat.add_sub_assoc.
   ++rewrite Nat.sub_add.
    **apply Nat.sub_lt; [ | flia ].
      simpl; replace 2 with (2 * 1) by flia.
      apply Nat.mul_le_mono; [ easy | ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    **now apply Nat.mul_le_mono_r.
   ++replace 2 with (2 * 1) at 1 by flia.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *assert (H3 : u (i + 1) = rad - 1) by flia H1 H2.
    clear H1 H2.
    specialize (IHm (S i) (S n)) as H1.
    rewrite Nat.sub_succ in H1.
    assert (H : ∀ k, u (S (S i) + k + 1) ≤ 2 * (rad - 1)). {
      intros k.
      replace (S (S i) + k) with (S i + S k) by flia.
      apply Hur.
    }
    specialize (H1 H Hm'); clear H.
    rewrite H3 in Hra.
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l in Hra.
    rewrite <- Nat.add_sub_swap in Hra.
   --apply Nat.add_le_mono_r with (p := rad ^ m) in Hra.
     rewrite Nat.sub_add in Hra.
    ++apply Nat.add_le_mono_l in Hra.
      specialize (H1 Hra).
      destruct H1 as (j & Hjm & Hkj & Hj).
      exists (j + 1).
      split; [ flia Hjm | ].
      split.
     **intros k Hk.
       destruct k; [ now rewrite Nat.add_0_r | ].
       replace (i + S k) with (S i + k) by flia.
       apply Hkj; flia Hk.
     **now replace (i + (j + 1)) with (S i + j) by flia.
    ++apply le_plus_trans.
      rewrite <- Nat.pow_succ_r'.
      apply Nat.pow_le_mono_r; [ easy | apply Nat.le_succ_diag_r ].
   --rewrite <- Nat.pow_succ_r'.
     apply Nat.pow_le_mono_r; [ easy | apply Nat.le_succ_diag_r ].
Qed.

Theorem not_prop_carr_all_9_all_ge_1 {r : radix} : ∀ u n,
  (∀ k : nat, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k : nat, A_ge_1 u n k = true)
  → (u n + nA n (rad * (n + 3)) u / rad ^ (rad * (n + 3) - n - 1) + 1)
       mod rad = rad - 1
  → ¬ (∀ k, d2n (prop_carr u) (n + k) = rad - 1).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur H2 H1 Hn.
specialize (A_ge_1_add_all_true_if _ _ Hur H2) as H3.
destruct H3 as [H3| [H3| H3]].
-rewrite Nat.div_small in H1.
 +rewrite Nat.add_0_r in H1.
  specialize (Hn 1) as H4.
  unfold prop_carr, d2n in H4; simpl in H4.
  unfold nat_prop_carr in H4.
  destruct (LPO_fst (A_ge_1 u (n + 1))) as [H5| H5].
  *rewrite Nat.div_small in H4.
   --rewrite Nat.add_0_l in H4.
     specialize (H3 0); rewrite Nat.add_0_r in H3.
     rewrite H3, Nat.sub_add in H4; [ | easy ].
     rewrite Nat.mod_same in H4; [ | easy ].
     flia Hr H4.
   --apply nA_dig_seq_ub.
     ++intros j Hj.
       specialize (H3 (j - n - 1)).
       replace (n + (j - n - 1) + 1) with j in H3 by flia Hj.
       flia Hr H3.
     ++destruct rad; [ easy | simpl; flia ].
  *destruct H5 as (j & Hjj & Hj); clear H4.
   apply A_ge_1_false_iff in Hj.
   apply Nat.nle_gt in Hj; apply Hj; clear Hj.
   rewrite Nat.mod_small.
   --apply nA_ge_999000.
     intros k.
     replace (n + 1 + k + 1) with (n + (1 + k) + 1) by flia.
     now rewrite H3.
   --apply nA_dig_seq_ub.
     ++intros k Hk.
       specialize (H3 (k - n - 1)).
       replace (n + (k - n - 1) + 1) with k in H3 by flia Hk.
       flia Hr H3.
     ++destruct rad; [ easy | simpl; flia ].
 +apply nA_dig_seq_ub.
  *intros k Hk.
   specialize (H3 (k - n - 1)).
   replace (n + (k - n - 1) + 1) with k in H3 by flia Hk.
   flia Hr H3.
  *destruct rad; [ easy | simpl; flia ].
-specialize (Hn 1) as H4.
 unfold prop_carr, d2n in H4; simpl in H4.
 unfold nat_prop_carr in H4.
 destruct (LPO_fst (A_ge_1 u (n + 1))) as [H5| H5]; simpl in H4.
 +specialize (H3 0) as H; rewrite Nat.add_0_r in H.
  rewrite H in H4; clear H.
  rewrite eq_nA_div_1 in H4.
  *rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H4.
   replace (2 * rad - 2 + (1 + 1)) with (2 * rad) in H4 by flia Hr.
   rewrite Nat.mod_mul in H4; [ | easy ].
   flia Hr H4.
  *intros k.
   replace (n + 1 + k + 1) with (n + (1 + k) + 1) by flia.
   apply Hur.
  *remember (rad * (n + 1 + 3)) as n1 eqn:Hn1.
   remember (n1 - (n + 1) - 1) as s1 eqn:Hs1.
   move s1 before n1; symmetry in Hs1.
   unfold nA.
   rewrite (summation_eq_compat _ (λ i, 2 * (rad - 1) * rad ^ (n1 - 1 - i))).
   destruct s1.
   --apply Nat.sub_0_le in Hs1; apply Nat.nlt_ge in Hs1.
     exfalso; apply Hs1; clear Hs1; rewrite Hn1.
     destruct rad; [ easy | simpl; flia ].
   --rewrite <- summation_mul_distr_l.
     remember mult as f; remember S as g; simpl; subst f g.
     rewrite summation_rtl.
     rewrite summation_shift.
     ++replace (n1 - 1 - (n + 1 + 1)) with s1 by flia Hs1.
       rewrite (summation_eq_compat _ (λ i, rad ^ i)).
       **rewrite <- Nat.mul_assoc, <- power_summation_sub_1; [ | easy ].
         rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
         replace (2 * rad ^ S s1) with (rad ^ S s1 + rad ^ S s1) by flia.
         rewrite <- Nat.add_sub_assoc; [ flia | simpl ].
         replace 2 with (2 * 1) by apply Nat.mul_1_r.
         apply Nat.mul_le_mono; [ easy | ].
         now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
       **intros i Hi; f_equal; flia Hs1 Hi.
     ++rewrite Hn1.
       destruct rad; [ easy | simpl; flia ].
   --intros i Hi.
     specialize (H3 (i - n - 1)).
     replace (n + (i - n - 1) + 1) with i in H3 by flia Hi.
     now rewrite H3.
 +destruct H5 as (j & Hjj & Hj); simpl in H4.
  apply A_ge_1_false_iff in Hj.
  remember (rad * (n + 1 + j + 3)) as n1 eqn:Hn1.
  remember (n1 - (n + 1) - 1) as s1 eqn:Hs1.
  destruct s1.
  *symmetry in Hs1.
   apply Nat.sub_0_le in Hs1.
   rewrite Hn1 in Hs1.
   destruct rad; [ simpl in Hn1; now subst n1 | simpl in Hs1; flia Hs1 ].
  *assert (HnA : nA (n + 1) n1 u = rad ^ S s1 + (rad ^ S s1 - 2)). {
     unfold nA.
     rewrite summation_rtl.
     rewrite summation_shift; [ | flia Hs1 ].
     replace (n1 - 1 - (n + 1 + 1)) with s1 by flia Hs1.
     rewrite (summation_eq_compat _ (λ i, 2 * (rad - 1) * rad ^ i)).
     -rewrite <- summation_mul_distr_l.
      remember mult as f; remember S as g; simpl; subst f g.
      rewrite <- Nat.mul_assoc.
      rewrite <- power_summation_sub_1; [ | easy ].
      rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
      rewrite Nat.add_sub_assoc; [ flia | ].
      simpl; replace 2 with (2 * 1) by apply Nat.mul_1_r.
      apply Nat.mul_le_mono; [ easy | ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
     -intros i Hi.
      replace (n1 - 1 + (n + 1 + 1) - (n + 1 + 1 + i)) with (n1 - 1 - i)
        by flia.
      replace (n1 - 1 - (n1 - 1 - i)) with i by flia Hs1 Hi; f_equal.
      specialize (H3 (n1 - n - i - 2)).
      replace (n + (n1 - n - i - 2) + 1) with (n1 - 1 - i) in H3
        by flia Hs1 Hi.
      easy.
   }
   rewrite Nat_mod_less_small in Hj.
   --apply Nat.nle_gt in Hj; apply Hj; clear Hj.
     apply Nat.le_add_le_sub_l.
     (* 1/9/9/9/0/0/0/0 ≤ 18/18/18/18/18/18/18 (= 1/9/9/9/9/9/9/8) *)
     rewrite HnA.
     apply Nat.add_le_mono_l.
     rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
     rewrite <- Nat.pow_add_r.
     assert (Hjs : j < s1). {
       apply Nat.succ_lt_mono.
       rewrite Hs1, Hn1.
       destruct rad; [ easy | simpl; flia ].
     }
     replace (S j + (S s1 - S j)) with (S s1); [ | flia Hjs ].
     apply Nat.sub_le_mono_l.
     rewrite Nat.sub_succ_l; [ simpl | easy ].
     replace 2 with (2 * 1) by apply Nat.mul_1_r.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   --rewrite HnA.
     split; [ flia | ].
     remember (S s1) as ss; simpl; subst ss.
     apply Nat.add_lt_mono_l.
     rewrite Nat.add_0_r.
     apply Nat.sub_lt; [ | flia ].
     simpl; replace 2 with (2 * 1) by apply Nat.mul_1_r.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
-destruct H3 as (j & Hjbef & Hjwhi & Hjaft).
 specialize (Hn (j + 1)) as H3.
 unfold d2n, prop_carr in H3; simpl in H3.
 unfold nat_prop_carr in H3.
 destruct (LPO_fst (A_ge_1 u (n + (j + 1)))) as [H4| H4].
 +simpl in H3.
  remember (rad * (n + (j + 1) + 3)) as n2 eqn:Hn2.
  remember (n2 - (n + (j + 1)) - 1) as s2 eqn:Hs2.
  move s2 before n2.
  do 2 rewrite Nat.add_assoc in H3.
  rewrite Hjwhi in H3.
  specialize (nA_all_18 u (n + j + 1) n2) as H5.
  rewrite Nat.add_assoc in Hs2.
  rewrite <- Hs2 in H5.
  assert (H : ∀ k, u (n + j + 1 + k + 1) = 2 * (rad - 1)). {
    intros k.
    replace (n + j + 1 + k + 1) with (n + j + k + 2) by flia.
    apply Hjaft.
  }
  specialize (H5 H); clear H.
  rewrite H5 in H3.
  rewrite Nat_div_less_small in H3.
  *replace (rad - 2 + 1 + 1) with rad in H3 by flia Hr.
   rewrite Nat.mod_same in H3; [ flia Hr H3 | easy ].
  *specialize (Nat.pow_nonzero rad s2 radix_ne_0) as H.
   rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   split; [ | flia H ].
   destruct s2.
   --exfalso.
     symmetry in Hs2.
     apply Nat.sub_0_le in Hs2.
     rewrite Hn2 in Hs2.
     destruct rad; [ easy | simpl in Hs2; flia Hs2 ].
   --enough (H6 : 2 ≤ rad ^ S s2) by flia H6; simpl.
     replace 2 with (2 * 1) by apply Nat.mul_1_r.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +destruct H4 as (k & Hjk & Hk); simpl in H3.
  specialize (H2 (j + 1 + k)).
  apply A_ge_1_add_r_true_if in H2.
  now rewrite H2 in Hk.
Qed.

Theorem eq_all_prop_carr_9_cond {r : radix} : ∀ u n,
  (∀ k, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, d2n (prop_carr u) (n + k) = rad - 1)
  → ∀ i, ∃ j,
  let n1 := rad * (n + i + j + 3) in
  let s1 := n1 - (n + i) - 1 in
  nA (n + i) n1 u mod rad ^ s1 < (rad ^ S j - 1) * rad ^ (s1 - S j) ∧
  (u (n + i) + nA (n + i) n1 u / rad ^ s1) mod rad = rad - 1.
Proof.
intros * Hur Hn *.
specialize (Hn i) as Huni.
unfold prop_carr, d2n in Huni; simpl in Huni.
unfold nat_prop_carr in Huni.
destruct (LPO_fst (A_ge_1 u (n + i))) as [H2| H2]; simpl in Huni.
-assert (Hn' : ∀ k, d2n (prop_carr u) ((n + i) + k) = rad - 1). {
   intros k.
   replace ((n + i) + k) with (n + (i + k)) by flia.
   apply Hn.
 }
 exfalso; revert Hn'.
 rewrite Nat.add_assoc in Huni.
 apply not_prop_carr_all_9_all_ge_1; [ | easy | easy ].
 intros k.
 replace (n + i + k + 1) with (n + (i + k) + 1) by flia.
 apply Hur.
-destruct H2 as (j & Hjj & Hj).
 simpl in Huni.
 apply A_ge_1_false_iff in Hj.
 exists j; easy.
Qed.

Theorem eq_all_prop_carr_9_cond1 {r : radix} : ∀ u i n s j,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → s = n - i - 1
  → j < s
  → nA i n u mod rad ^ s < (rad ^ S j - 1) * rad ^ (s - S j)
  → (u i + nA i n u / rad ^ s) mod rad = rad - 1
  → if lt_dec (nA i n u) (rad ^ s) then
       u i = rad - 1 ∧ u (i + 1) ≠ 2 * (rad - 1)
     else if lt_dec (u i) (rad - 1) then
       u i = rad - 2 ∧ u (i + 1) ≥ rad - 1
     else
       u i = 2 * (rad - 1) ∧ u (i + 1) ≥ rad - 1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hs1 Hs1z Hj1 Hun1.
destruct (lt_dec (nA i n u) (rad ^ s)) as [H4| H4].
-rewrite Nat.div_small in Hun1; [ | easy ].
 rewrite Nat.mod_small in Hj1; [ | easy ].
 clear H4.
 rewrite Nat.add_0_r in Hun1.
 destruct (lt_dec (u i) rad) as [H5| H5].
 +rewrite Nat.mod_small in Hun1; [ clear H5 | easy ].
  assert (Hur2 : u (i + 1) ≠ 2 * (rad - 1)). {
    intros H.
    apply Nat.nle_gt in Hj1; apply Hj1; clear Hj1.
    rewrite nA_split_first.
    -replace (n - i - 2) with (s - 1) by flia Hs1.
     rewrite H.
     apply le_plus_trans.
     rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
     rewrite <- Nat.pow_add_r.
     replace (S j + (s - S j)) with s.
     +rewrite <- Nat.mul_assoc, Nat.mul_sub_distr_r, Nat.mul_1_l.
      rewrite <- Nat.pow_succ_r'.
      rewrite <- Nat.sub_succ_l.
      *rewrite Nat.sub_succ, Nat.sub_0_r.
       rewrite Nat.mul_sub_distr_l.
       replace (2 * rad ^ s) with (rad ^ s + rad ^ s) by flia.
       rewrite <- Nat.add_sub_assoc; [ flia | ].
       destruct s; [ easy | ].
       rewrite Nat.sub_succ, Nat.sub_0_r.
       rewrite Nat.pow_succ_r'.
       now apply Nat.mul_le_mono_r.
      *flia Hs1z.
     +rewrite Nat.add_sub_assoc; [ flia | easy ].
    -flia Hs1 Hs1z.
  }
  easy.
 +apply Nat.nlt_ge in H5.
  specialize (Hur 0); rewrite Nat.add_0_r in Hur.
  rewrite Nat_mod_less_small in Hun1; [ flia Hur Hun1 Hr | ].
  split; [ easy | flia Hr Hur ].
-apply Nat.nlt_ge in H4.
 assert (H : rad ^ s ≤ nA i n u < 2 * rad ^ s). {
   split; [ easy | ].
   specialize (nA_upper_bound_for_add u i n) as H5.
   rewrite <- Hs1 in H5.
   assert (H : ∀ j, u (i + j + 1) ≤ 2 * (rad - 1)). {
     intros k; rewrite <- Nat.add_assoc; apply Hur.
   }
   specialize (H5 H); clear H.
   rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H5.
   specialize (Nat.pow_nonzero rad s radix_ne_0) as H6.
   flia Hr H5 H6.
 }
 rewrite Nat_div_less_small in Hun1; [ | easy ].
 rewrite Nat_mod_less_small in Hj1; [ clear H | easy ].
 assert (Hur1 : u (i + 1) ≥ rad - 1). {
   apply Nat.nlt_ge; intros H.
   apply Nat.nlt_ge in H4; apply H4; clear H4.
   clear - Hur Hs1 Hs1z H.
   specialize radix_ge_2 as Hr.
   replace (n - i - 2) with (s - 1) by flia Hs1.
   apply Nat.lt_le_pred in H.
   replace (pred (rad - 1)) with (rad - 2) in H by flia.
   rewrite nA_split_first.
   -eapply Nat.le_lt_trans.
    +apply Nat.add_le_mono_l.
     apply nA_upper_bound_for_add.
     intros k.
     replace (S i + k + 1) with (i + (k + 2)) by flia; apply Hur.
    +replace (n - S i - 1) with (s - 1) by flia Hs1.
     replace (n - i - 2) with (s - 1) by flia Hs1.
     eapply Nat.lt_le_trans.
     *apply Nat.add_lt_mono_r.
      eapply Nat.le_lt_trans.
     --apply Nat.mul_le_mono_pos_r; [ | apply H ].
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
     --apply Nat.lt_succ_diag_r.
     *destruct s; [ easy | ].
      rewrite Nat.sub_succ, Nat.sub_0_r.
      rewrite <- Nat.add_1_l, <- Nat.add_assoc.
      rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
      rewrite Nat.add_sub_assoc.
     --rewrite <- Nat.mul_add_distr_r.
       rewrite Nat.sub_add; [ | flia Hr ].
       rewrite <- Nat.pow_succ_r'.
       specialize (Nat.pow_nonzero rad (S s) radix_ne_0) as H1.
       flia H1.
     --replace 2 with (2 * 1) at 1 by flia.
       apply Nat.mul_le_mono_l.
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   -flia Hs1 Hs1z.
 }
 destruct (lt_dec (u i) (rad - 1)) as [H3| H3].
 +rewrite Nat.mod_small in Hun1; [ clear H3 | flia H3 ].
  assert (H : u i = rad - 2) by flia Hun1.
  clear Hun1; rename H into Hun1.
  easy.
 +apply Nat.nlt_ge in H3.
  specialize (Hur 0); rewrite Nat.add_0_r in Hur.
  rewrite Nat_mod_less_small in Hun1.
  *assert (H : u i = 2 * (rad - 1)) by flia Hun1.
   clear Hun1; rename H into Hun1.
   (* u(n+1)=18 *)
   easy.
  *split; [ flia H3 | flia Hr Hur ].
Qed.

Theorem eq_all_prop_carr_9_cond2 {r : radix} : ∀ u n,
  (∀ k, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, d2n (prop_carr u) (n + k) = rad - 1)
  → ∀ k (i := n + k + 1),
     u i = rad - 1 ∧ u (i + 1) ≠ 2 * (rad - 1) ∨
     u i = rad - 2 ∧
       (∃ j, (∀ l, l < j → u (i + l + 1) = rad - 1) ∧ u (i + j + 1) ≥ rad) ∨
     u i = 2 * (rad - 1) ∧
       (∃ j, (∀ l, l < j → u (i + l + 1) = rad - 1) ∧ u (i + j + 1) ≥ rad).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hn k.
specialize (eq_all_prop_carr_9_cond u n Hur Hn) as HAF.
specialize (HAF (k + 1)) as Hun1.
destruct Hun1 as (j & Hj & Hun); simpl in Hun.
rewrite Nat.add_assoc in Hj, Hun.
remember (rad * (n + k + 1 + j + 3)) as n1 eqn:Hn1.
remember (n1 - (n + k + 1) - 1) as s1 eqn:Hs1.
move s1 before n1.
replace (n + k + 2) with (n + k + 1 + 1) by flia.
remember (n + k + 1) as i eqn:Hi.
specialize (eq_all_prop_carr_9_cond1 u i n1 s1 j) as H1.
assert (H : ∀ j, u (i + j) ≤ 2 * (rad - 1)). {
  intros l; subst i.
  replace (n + k + 1 + l) with (n + (k + l) + 1) by flia.
  apply Hur.
}
specialize (H1 H Hs1); clear H.
assert (H : j < s1). {
  rewrite Hs1, Hn1.
  destruct rad; [ easy | simpl; flia ].
}
specialize (H1 H Hj Hun); clear H.
destruct (lt_dec (nA i n1 u) (rad ^ s1)) as [H2| H2]; [ now left | right ].
apply Nat.nlt_ge in H2.
rewrite Hs1 in H2.
specialize (A_ge_rad_pow u i n1) as H3.
assert (H : ∀ k, u (S i + k + 1) ≤ 2 * (rad - 1)). {
  intros l; rewrite Hi.
  replace (S (n + k + 1) + l) with (n + (k + l + 2)) by flia.
  apply Hur.
}
specialize (H3 H H2); clear H.
rewrite <- Hs1 in H2.
destruct H3 as (j2 & Hj2 & Hkj2 & Hjr2).
destruct (lt_dec (u i) (rad - 1)) as [H3| H3].
-left; split; [ easy | now exists j2 ].
-right; split; [ easy | now exists j2 ].
Qed.

Theorem eq_all_prop_carr_9_cond3 {r : radix} : ∀ u n,
  (∀ k, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, d2n (prop_carr u) (n + k) = rad - 1)
  → ∀ k (i := n + k + 1),
     u i = rad - 1 ∧
       (u (i + 1) = rad - 2 ∨ u (i + 1) = rad - 1) ∨
     u i = rad - 2 ∧
       (∃ j,
           (∀ l, l < j → u (i + l + 1) = rad - 1) ∧
           u (i + j + 1) = 2 * (rad - 1)) ∨
     u i = 2 * (rad - 1) ∧
       (∃ j,
           (∀ l, l < j → u (i + l + 1) = rad - 1) ∧
           u (i + j + 1) = 2 * (rad - 1)).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hn k.
specialize (eq_all_prop_carr_9_cond2 u n Hur Hn k) as H.
remember (n + k + 1) as i eqn:Hi.
replace (n + k + 2) with (i + 1) by flia Hi.
destruct H as [H| [H| H]]; destruct H as (H1, H2).
-left; split; [ easy | ].
 specialize (eq_all_prop_carr_9_cond2 u n Hur Hn (k + 1)) as H.
 replace (n + (k + 1)) with i in H by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H3, H4).
 +now right.
 +now left.
 +easy.
-right; left; split; [ easy | ].
 destruct H2 as (j2 & Hlj2 & Hj2).
 exists j2.
 split; [ easy | ].
 specialize (eq_all_prop_carr_9_cond2 u n Hur Hn (i + j2 - n)) as H.
 replace (n + (i + j2 - n)) with (i + j2) in H by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H3, H4).
 +rewrite H3 in Hj2; flia Hr Hj2.
 +rewrite H3 in Hj2; flia Hr Hj2.
 +easy.
-right; right; split; [ easy | ].
 destruct H2 as (j2 & Hlj2 & Hj2).
 exists j2.
 specialize (eq_all_prop_carr_9_cond2 u n Hur Hn (i + j2 - n)) as H.
 replace (n + (i + j2 - n)) with (i + j2) in H by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H3, H4).
 +rewrite H3 in Hj2; flia Hr Hj2.
 +rewrite H3 in Hj2; flia Hr Hj2.
 +easy.
Qed.

Theorem eq_all_prop_carr_9_cond4 {r : radix} : ∀ u n,
  (∀ k, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, d2n (prop_carr u) (n + k) = rad - 1)
  → ∀ k (i := n + k + 1),
     u i = rad - 1 ∧ (u (i + 1) = rad - 2 ∨ u (i + 1) = rad - 1) ∨
     u i = rad - 2 ∧ u (i + 1) = 2 * (rad - 1) ∨
     u i = 2 * (rad - 1) ∧ u (i + 1) = 2 * (rad - 1).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hn k.
specialize (eq_all_prop_carr_9_cond3 u n Hur Hn k) as H.
remember (n + k + 1) as i eqn:Hi.
destruct H as [H| [H| H]]; [ now left | | ].
-right; left.
 destruct H as (Hui & j & Hlj & Hj).
 split; [ easy | ].
 destruct j; [ now rewrite Nat.add_0_r in Hj | ].
 specialize (Hlj j (Nat.lt_succ_diag_r j)) as H1.
 specialize (eq_all_prop_carr_9_cond3 u n Hur Hn (k + j + 1)) as H.
 rewrite Hi in Hj.
 replace (n + (k + j + 1) + 1) with (n + k + 1 + S j) in H by flia.
 replace (n + k + 1 + S j) with (i + j + 1) in H, Hj by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H2, H3).
 +exfalso.
  rewrite Hj in H3.
  destruct H3 as [H3| H3]; flia Hr H3.
 +rewrite H1 in H2; flia Hr H2.
 +rewrite H1 in H2; flia Hr H2.
-right; right.
 destruct H as (Hui & j & Hlj & Hj).
 split; [ easy | ].
 destruct j; [ now rewrite Nat.add_0_r in Hj | ].
 specialize (Hlj j (Nat.lt_succ_diag_r j)) as H1.
 specialize (eq_all_prop_carr_9_cond3 u n Hur Hn (k + j + 1)) as H.
 rewrite Hi in Hj.
 replace (n + (k + j + 1) + 1) with (n + k + 1 + S j) in H by flia.
 replace (n + k + 1 + S j) with (i + j + 1) in H, Hj by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H2, H3).
 +exfalso.
  rewrite Hj in H3.
  destruct H3 as [H3| H3]; flia Hr H3.
 +rewrite H1 in H2; flia Hr H2.
 +rewrite H1 in H2; flia Hr H2.
Qed.

Theorem eq_all_prop_carr_9 {r : radix} : ∀ u n,
  (∀ k, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, d2n (prop_carr u) (n + k) = rad - 1)
  → (∀ k, u (n + k + 1) = rad - 1) ∨
     (∀ k, u (n + k + 1) = 2 * (rad - 1)) ∨
     (∃ j,
       (∀ k, k < j → u (n + k + 1) = rad - 1) ∧
       u (n + j + 1) = rad - 2 ∧
       (∀ k, u (n + j + k + 2) = 2 * (rad - 1))).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hn.
specialize (eq_all_prop_carr_9_cond4 u n Hur Hn) as HAF.
destruct (LPO_fst (is_num_9_strict_after u n)) as [H1| H1].
-specialize (is_num_9_strict_after_all_9 u n H1) as H2.
 now left.
-destruct H1 as (i & Hji & Hi).
 apply is_num_9_strict_after_false_iff in Hi.
 destruct i.
 +specialize (HAF 0) as H1.
  rewrite Nat.add_0_r in Hi, H1.
  destruct H1 as [H1| [H1| H1]]; destruct H1 as (H1, H2).
  *easy.
  *right; right.
   exists 0.
   rewrite Nat.add_0_r.
   split; [ now intros | ].
   split; [ easy | ].
   replace (n + 1 + 1) with (n + 2) in H2 by flia.
   intros k.
   induction k; [ now rewrite Nat.add_0_r | ].
   specialize (HAF (k + 1)) as H3.
   replace (n + (k + 1) + 1) with (n + k + 2) in H3 by flia.
   destruct H3 as [H3| [H3| H3]]; destruct H3 as (H3, H4).
  --rewrite H3 in IHk; flia Hr IHk.
  --rewrite H3 in IHk; flia Hr IHk.
  --now replace (n + k + 2 + 1) with (n + S k + 2) in H4 by flia.
  *right; left.
   intros k.
   induction k; [ now rewrite Nat.add_0_r | ].
   specialize (HAF k) as H3.
   destruct H3 as [H3| [H3| H3]]; destruct H3 as (H3, H4).
  --rewrite H3 in IHk; flia Hr IHk.
  --rewrite H3 in IHk; flia Hr IHk.
  --now replace (n + k + 1 + 1) with (n + S k + 1) in H4 by flia.
 +specialize (Hji i (Nat.lt_succ_diag_r i)) as H1.
  apply is_num_9_strict_after_true_iff in H1.
  right; right.
  exists (S i).
  split.
  *intros k Hk.
   specialize (Hji _ Hk).
   now apply is_num_9_strict_after_true_iff in Hji.
  *replace (n + S i + 1) with (n + i + 2) in Hi |-* by flia.
   specialize (HAF i) as H2.
   destruct H2 as [H2| [H2| H2]]; destruct H2 as (H2, H3).
  --replace (n + i + 1 + 1) with (n + i + 2) in H3 by flia.
    destruct H3 as [H3| H3]; [ | easy ].
    split; [ easy | ].
    intros k.
    induction k.
   ++rewrite Nat.add_0_r.
     replace (n + S i + 2) with (n + i + 3) by flia.
     specialize (HAF (i + 1)) as H4.
     destruct H4 as [H4| [H4| H4]]; destruct H4 as (H4, H5).
    **replace (n + (i + 1) + 1) with (n + i + 2) in H4 by flia.
      rewrite H3 in H4; flia Hr H4.
    **now replace (n + (i + 1) + 1 + 1) with (n + i + 3) in H5 by flia.
    **now replace (n + (i + 1) + 1 + 1) with (n + i + 3) in H5 by flia.
   ++replace (n + S i + k + 2) with (n + i + k + 3) in IHk by flia.
     replace (n + S i + S k + 2) with (n + i + k + 4) by flia.
     specialize (HAF (i + k + 2)) as H4.
     replace (n + (i + k + 2) + 1) with (n + i + k + 3) in H4 by flia.
     destruct H4 as [H4| [H4| H4]]; destruct H4 as (H4, H5).
    **rewrite H4 in IHk; flia Hr IHk.
    **rewrite H4 in IHk; flia Hr IHk.
    **now replace (n + i + k + 3 + 1) with (n + i + k + 4) in H5 by flia.
  --rewrite H1 in H2; flia Hr H2.
  --rewrite H1 in H2; flia Hr H2.
Qed.

Theorem not_prop_carr_all_9 {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → ¬ (∀ k, d2n (prop_carr u) (i + k) = rad - 1).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hn.
specialize (eq_all_prop_carr_9 u i Hur Hn) as Hall.
specialize (eq_all_prop_carr_9_cond u i Hur Hn) as HAF.
specialize (HAF 1) as Hun1.
destruct Hun1 as (j1 & Hj1 & Hun1); simpl in Hun1.
remember (rad * (i + 1 + j1 + 3)) as n1 eqn:Hn1.
remember (n1 - (i + 1) - 1) as s1 eqn:Hs1.
move s1 before n1.
destruct (lt_dec (nA (i + 1) n1 u) (rad ^ s1)) as [H1| H1].
-rewrite Nat.div_small in Hun1; [ | easy ].
 rewrite Nat.mod_small in Hj1; [ | easy ].
 clear H1.
 rewrite Nat.add_0_r in Hun1.
 destruct (lt_dec (u (i + 1)) rad) as [H1| H1].
 +rewrite Nat.mod_small in Hun1; [ clear H1 | easy ].
  (* u(n+1)=9 *)
  destruct Hall as [Hall| [Hall| Hall]].
  *apply Nat.nle_gt in Hj1.
   apply Hj1; clear Hj1.
   unfold nA.
   rewrite summation_eq_compat with
     (h := λ j, (rad - 1) * rad ^ (n1 - 1 - j)).
  --rewrite <- summation_mul_distr_l.
    remember S as f; simpl; subst f.
    rewrite summation_rtl, summation_shift.
   ++replace (n1 - 1 - (i + 1 + 1)) with (s1 - 1) by flia Hs1.
     rewrite summation_eq_compat with (h := λ i, rad ^ i).
    **rewrite <- power_summation_sub_1; [ | easy ].
      rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
      rewrite <- Nat.pow_add_r.
      replace (S j1 + (s1 - S j1)) with s1.
    ---rewrite <- Nat.sub_succ_l.
     +++rewrite Nat.sub_succ, Nat.sub_0_r.
        apply Nat.sub_le_mono_l.
        now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
     +++destruct s1; [ | flia ].
        rewrite Hn1 in Hs1.
        destruct rad; [ easy | simpl in Hs1; flia Hs1 ].
    ---rewrite Hs1, Hn1.
       destruct rad; [ easy | simpl; flia ].
    **intros j Hj; f_equal; flia Hs1 Hj.
   ++rewrite Hn1.
     destruct rad; [ easy | simpl; flia ].
  --intros j Hj; f_equal.
    specialize (Hall (j - i - 1)).
    now replace (i + (j - i - 1) + 1) with j in Hall by flia Hj.
  *specialize (Hall 0); rewrite Nat.add_0_r in Hall.
   flia Hr Hall Hun1.
  *destruct Hall as (j & Hkj & Huj & Hall).
   destruct j; [ rewrite Nat.add_0_r in Huj; flia Hr Huj Hun1 | ].
   apply Nat.nle_gt in Hj1.
   apply Hj1; clear Hj1.
   now apply (u_9_8_18_nA_ge_999000 _ _ j).
 +apply Nat.nlt_ge in H1.
  specialize (Hur 0); rewrite Nat.add_0_r in Hur.
  rewrite Nat_mod_less_small in Hun1; [ flia Hr Hur Hun1 | ].
  split; [ easy | flia Hr Hur ].
-apply Nat.nlt_ge in H1.
 specialize (A_ge_rad_pow u (i + 1) n1) as H2.
 rewrite <- Hs1 in H2.
 assert (H : ∀ k, u (S (i + 1) + k + 1) ≤ 2 * (rad - 1)). {
   intros k.
   replace (S (i + 1) + k) with (i + (k + 2)) by flia.
   apply Hur.
 }
 specialize (H2 H H1); clear H.
 destruct H2 as (j & Hjs & Hkj & Huj).
 destruct j.
 +rewrite Nat.add_0_r in Huj; clear Hkj.
  destruct Hall as [Hall| [Hall| Hall]].
  *specialize (Hall 1); rewrite Hall in Huj; flia Hr Huj.
  *assert (H : ∀ k, u (i + k + 2) = 2 * (rad - 1)). {
     intros k.
     replace (i + k + 2) with (i + (k + 1) + 1) by flia.
     apply Hall.
   }
   move H before Hall; clear Hall; rename H into Hall.
   apply Nat.nle_gt in Hj1; apply Hj1; clear Hj1.
   now apply (u_18_nA_mod_ge_999000 u n1 s1 j1 i).
  *destruct Hall as (j & Hbef & Hwhi & Haft).
   destruct j.
  --rewrite Nat.add_0_r in Hwhi, Haft; clear Hbef.
    apply Nat.nle_gt in Hj1; apply Hj1; clear Hj1.
    now apply (u_18_nA_mod_ge_999000 u n1 s1 j1 i).
  --destruct j; [ rewrite Hwhi in Huj; flia Hr Huj | ].
    rewrite Hbef in Huj; [ flia Hr Huj | flia ].
 +destruct Hall as [Hall| [Hall| Hall]].
  *replace (i + 1 + S j + 1) with (i + (j + 2) + 1) in Huj by flia.
   rewrite Hall in Huj; flia Hr Huj.
  *specialize (Hkj 0 (Nat.lt_0_succ j)).
   rewrite Nat.add_0_r in Hkj.
   rewrite Hall in Hkj.
   flia Hr Hkj.
  *destruct Hall as (n & Hbef & Hwhi & Haft).
   destruct (lt_dec n (S (S j))) as [H2| H2].
  --destruct n.
   ++specialize (Haft j).
     replace (i + 0 + j + 2) with (i + 1 + j + 1) in Haft by flia.
     specialize (Hkj j (Nat.lt_succ_diag_r j)).
     rewrite Haft in Hkj; flia Hr Hkj.
   ++apply Nat.succ_lt_mono in H2.
     specialize (Hkj n H2).
     replace (i + 1 + n) with (i + S n) in Hkj by flia.
     rewrite Hwhi in Hkj; flia Hr Hkj.
  --destruct (eq_nat_dec n (S (S j))) as [H3| H3].
   ++rewrite H3 in Hwhi.
     replace (i + S (S j)) with (i + 1 + S j) in Hwhi by flia.
     rewrite Hwhi in Huj; flia Hr Huj.
   ++assert (H4 : S (S j) < n) by flia H2 H3.
     specialize (Hbef _ H4).
     replace (i + S (S j)) with (i + 1 + S j) in Hbef by flia.
     rewrite Hbef in Huj; flia Hr Huj.
Qed.

Theorem prop_carr_normalizes {r : radix} : ∀ u,
  (∀ i, u i ≤ 2 * (rad - 1))
  → ∀ i, prop_carr u i = normalize (prop_carr u) i.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur *.
unfold normalize.
destruct (LPO_fst (is_9_strict_after (prop_carr u) i)) as [H1| ]; [ | easy ].
exfalso.
specialize (is_9_strict_after_all_9 (prop_carr u) _ H1) as H2.
assert (H3 : ∀ k, d2n (prop_carr u) (i + 1 + k) = rad - 1). {
  now intros k; rewrite Nat.add_shuffle0.
}
now apply not_prop_carr_all_9 in H3.
Qed.

Theorem freal_normalize_add {r : radix} : ∀ x y,
  freal_norm_eq (freal_normalize (x + y)) (x + y).
Proof.
intros.
unfold freal_norm_eq, fd2n.
remember freal_add as f; simpl; subst f.
intros i.
unfold "+"%F.
remember prop_carr as f; simpl; subst f.
symmetry.
apply digit_eq_eq.
apply prop_carr_normalizes.
apply freal_add_series_le_twice_pred.
Qed.

Theorem pouet {r : radix} : ∀ u i,
  ¬∀ k,
   let j :=
     match LPO_fst (A_ge_1 u (i + k)) with
     | inl _ => 0
     | inr (exist _ m _) => S m
     end
   in
   let n := rad * (i + k + (j - 1) + 3) in
   let a := nA (i + k) n u / rad ^ (n - (i + k) - 1) in
   (u (i + k) + a + (1 - j)) mod rad = rad - 1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hn.
Abort. (*

Theorem glop {r : radix} : ∀ u i,
  ¬ ∀ k, d2n (prop_carr u) (i + k) = rad - 1.
Proof.
intros * Hn.
specialize (pouet u i) as H; apply H; clear H.
intros k.
specialize (Hn k).
unfold d2n, prop_carr in Hn; simpl in Hn.
unfold nat_prop_carr in Hn.
destruct (LPO_fst (A_ge_1 u (i + k))) as [H1| H1].
-rewrite Nat.add_assoc in Hn.
 now simpl; rewrite Nat.add_0_r.
-destruct H1 as (j & Hjj & Hj); simpl.
 now rewrite Nat.sub_0_r, Nat.add_0_r.
Qed.
*)
