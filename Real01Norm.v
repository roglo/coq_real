Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz NPeano.
Require Import Misc Summation FracReal.

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
