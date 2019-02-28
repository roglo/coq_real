Require Import Utf8 Arith PeanoNat.
Require Import Misc Summation NQ Ureal.

Definition P {r : radix} u := d2n (prop_carr u).
Definition add_series (u v : nat → nat) i := u i + v i.
Notation "u ⊕ v" := (add_series u v) (at level 50).

Definition M {r : radix} (u : nat → _) i := u i mod rad.

Definition num_A {r : radix} (rg := nat_ord_ring) i n u :=
  Σ (j = i + 1, n - 1), u j * rad ^ (n - j - 1).
Definition den_A {r : radix} i n := rad ^ (n - i - 1).

Theorem A_lt_le_pred {r : radix} : ∀ i n u m,
  (A i n u < m // rad ^ (n - i - 1))%NQ
  → (A i n u ≤ (m - 1) // rad ^ (n - i - 1))%NQ.
Proof.
intros * Ha.
remember (n - i - 1) as s eqn:Hs.
destruct (zerop m) as [H1| H1]. {
  subst m.
  now exfalso; apply NQnle_gt in Ha; apply Ha.
}
rewrite A_num_den in Ha |-*.
unfold den_A in Ha |-*.
rewrite <- Hs in Ha |-*.
apply NQlt_pair in Ha; [ | pauto | pauto ].
apply NQle_pair; [ pauto | pauto | ].
rewrite Nat.mul_comm in Ha |-*.
apply Nat.mul_lt_mono_pos_l in Ha; [ | apply Nat.neq_0_lt_0; pauto ].
apply Nat.mul_le_mono_l.
apply Nat.lt_le_pred in Ha.
now rewrite <- Nat.sub_1_r in Ha.
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
  apply NQadd_nonneg_nonneg; [ | easy ].
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

Theorem all_fA_ge_1_ε_P_999 {r : radix} : ∀ u i,
  (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k, P u (i + k + 1) = rad - 1.
Proof.
intros * Hu *.
apply fA_ge_1_ε_999.
intros l.
apply A_ge_1_add_r_true_if, Hu.
Qed.

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

Theorem fA_ge_1_ε_all_true_add_le_999_999 {r : radix} : ∀ u v i,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k + 1) = rad - 1)
  → (∀ k, fA_ge_1_ε (u ⊕ v) i k = true)
  → (∀ k : nat, u (i + k + 1) = 0) ∨ (∀ k : nat, u (i + k + 1) = rad - 1).
Proof.
intros * Hu A3 H2.
specialize radix_ge_2 as Hr.
specialize (A_ge_1_add_all_true_if (u ⊕ v) i) as H5.
assert (H : ∀ k, (u ⊕ v) (i + k + 1) ≤ 2 * (rad - 1)). {
  intros k; unfold "⊕"; rewrite <- Nat.add_assoc at 1.
  replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
  apply Nat.add_le_mono; [ apply Hu | ].
  now rewrite A3.
}
specialize (H5 H H2); clear H.
destruct H5 as [H5| [H5| H5]].
-left; intros k.
 specialize (H5 k); unfold "⊕" in H5.
 rewrite A3 in H5; flia H5.
-right; intros k.
 specialize (H5 k); unfold "⊕" in H5.
 rewrite A3 in H5; flia H5.
-exfalso.
 destruct H5 as (l & _ & H5 & _); unfold "⊕" in H5.
 rewrite A3 in H5; flia H5 Hr.
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

Theorem NQintg_P_M {r : radix} : ∀ i n u, NQintg (A i n (P u)) = 0.
Proof.
intros.
apply NQintg_small.
split; [ easy | apply A_M_upper_bound ].
Qed.

Theorem pre_Hugo_Herbelin_1 {r : radix} : ∀ u v i kup kuv,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, fA_ge_1_ε v i k = true)
  → kup = match LPO_fst (fA_ge_1_ε (u ⊕ P v) i) with
          | inl _ => 0
          | inr (exist _ k _) => k
          end
  → kuv = match LPO_fst (fA_ge_1_ε (u ⊕ v) i) with
          | inl _ => 0
          | inr (exist _ k _) => k
          end
  → NQintg (A i (min_n i kuv) v) = 0
  → (A i (min_n i kup) u + A i (min_n i kup) (P v) < 1)%NQ
  → (A i (min_n i kuv) u + A i (min_n i kuv) v < 1)%NQ.
Proof.
intros * Hu H3 Hkup Hkuv Hm H4.
apply NQnle_gt; intros H5.
specialize radix_ge_2 as Hr.
remember (min_n i 0) as nv eqn:Hnv.
remember (min_n i kup) as nup eqn:Hnup.
remember (min_n i kuv) as nuv eqn:Hnuv.
specialize (all_fA_ge_1_ε_P_999 _ _ H3) as A3.
rewrite (A_all_9 (P v)) in H4; [ | intros; apply A3 ].
rewrite NQadd_comm, <- NQadd_sub_swap, <- NQadd_sub_assoc in H4.
replace 1%NQ with (1 + 0)%NQ in H4 at 2 by easy.
apply NQadd_lt_mono_l, NQlt_sub_lt_add_r in H4.
rewrite NQadd_0_l in H4.
assert (HAu : A i nup u = 0%NQ). {
  rewrite A_num_den in H4.
  rewrite A_num_den.
  unfold den_A in H4.
  apply NQlt_pair in H4; [ | pauto | pauto ].
  rewrite Nat.mul_comm in H4.
  apply Nat.mul_lt_mono_pos_l in H4; [ | now apply Nat_pow_ge_1 ].
  rewrite Nat.lt_1_r in H4.
  now rewrite H4.
}
clear H4.
destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [H6| H6].
-subst kuv.
 rewrite <- Hnv in Hnuv; subst nuv.
 apply eq_NQintg_0 in Hm; [ | easy ].
 apply NQnlt_ge in H5; apply H5; clear H5.
 apply (NQle_lt_trans _ (A i nup u + A i nv v)).
 +apply NQadd_le_mono_r.
  rewrite (A_split nv _ _ nup). 2: {
    rewrite Hnv, Hnup; unfold min_n.
    split.
    -destruct rad; [ easy | cbn; flia ].
    -apply Nat.mul_le_mono_l; flia.
  }
  replace (A i nv u) with (A i nv u + 0)%NQ at 1 by apply NQadd_0_r.
  apply NQadd_le_mono_l.
  replace 0%NQ with (0 * 0)%NQ by easy.
  now apply NQmul_le_mono_nonneg.
 +now rewrite HAu, NQadd_0_l.
-destruct H6 as (j & Hjj & Hj).
 subst kuv.
 apply A_ge_1_false_iff in Hj.
 rewrite <- Hnuv in Hj.
 rewrite <- A_additive in H5.
 move Hj at bottom; move H5 at bottom.
 rewrite NQintg_frac in H5; [ | easy ].
 apply NQnlt_ge in H5; apply H5; clear H5.
 remember (A i nuv (u ⊕ v)) as x eqn:Hx.
 apply (NQlt_le_trans _ (NQintg x // 1 + (1 - 1 // rad ^ S j))%NQ).
 +now apply NQadd_lt_mono_l.
 +subst x.
  rewrite A_additive.
  rewrite A_additive in Hj.
  rewrite NQintg_add; [ | easy | easy ].
  rewrite Hm, Nat.add_0_r.
  rewrite NQfrac_add_cond in Hj; [ | easy | easy ].
  assert (Hau : ∀ n, (0 ≤ A i n u < 1)%NQ). {
    intros n.
    split; [ easy | ].
    apply A_upper_bound_for_dig.
    intros k Hk; replace k with (i + (k - i)) by flia Hk.
    apply Hu.
  }
  rewrite (NQintg_small (A i nuv u)); [ | easy ].
  rewrite (NQfrac_small (A i nuv u)); [ | easy ].
  rewrite (NQfrac_small (A i nuv u)) in Hj; [ | easy ].
  rewrite Nat.add_0_l.
  destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [H2| H2].
  *subst kup.
   rewrite <- Hnv in Hnup; subst nup.
   rewrite <- (NQfrac_small (A i nuv u)); [ | easy ].
   rewrite NQintg_add_frac.
   rewrite (NQfrac_small (A i nuv u)); [ | easy ].
   rewrite (NQfrac_small (A i nuv v)). 2: {
     split; [ easy | now apply eq_NQintg_0 in Hm ].
   }
   rewrite (NQfrac_small (A i nuv v)) in Hj. 2: {
     split; [ easy | now apply eq_NQintg_0 in Hm ].
   }
   destruct (NQlt_le_dec (A i nuv u + A i nuv v) 1) as [H4| H4].
   --now rewrite NQadd_0_l; apply NQle_sub_l.
   --exfalso.
     specialize (fA_ge_1_ε_all_true_add_le_999_999 u (P v) i Hu A3 H2) as H5.
     destruct H5 as [H5| H5].
     ++unfold A in H4 at 1.
       rewrite all_0_summation_0 in H4. 2: {
         intros l Hl; replace l with (i + (l - i - 1) + 1) by flia Hl.
         now rewrite H5.
       }
       rewrite NQadd_0_l in H4.
       apply eq_NQintg_0 in Hm; [ | easy ].
       now apply NQnlt_ge in H4.
     ++rewrite A_all_9 in HAu by (intros; apply H5).
       rewrite NQsub_pair_pos in HAu; [ | easy | pauto | ]. 2: {
         now do 2 rewrite Nat.mul_1_l; apply Nat_pow_ge_1.
       }
       do 2 rewrite Nat.mul_1_l in HAu.
       replace 0%NQ with (0 // 1)%NQ in HAu; [ | easy ].
       apply NQeq_pair in HAu; [ | pauto | easy ].
       rewrite Nat.mul_1_r, Nat.mul_0_r in HAu.
       apply Nat.sub_0_le, Nat.nlt_ge in HAu; apply HAu; clear HAu.
       apply Nat.pow_gt_1; [ easy | ].
       rewrite Hnv; unfold min_n.
       destruct rad; [ easy | cbn; flia ].
  *destruct H2 as (j2 & Hjj2 & Hj2); subst kup.
   move Hj2 at bottom.
   apply A_ge_1_false_iff in Hj2.
   rewrite <- Hnup in Hj2.
   rewrite A_additive in Hj2.
   rewrite HAu, NQadd_0_l in Hj2.
   rewrite (NQfrac_small (A _ _ (P v))) in Hj2. 2: {
     split; [ easy | ].
     apply eq_NQintg_0; [ easy | ].
     apply NQintg_P_M.
   }
   exfalso.
   apply NQnle_gt in Hj2; apply Hj2; clear Hj2.
   rewrite A_all_9 by (intros; apply A3).
   apply NQsub_le_mono; [ apply NQle_refl | ].
   apply NQle_pair; [ pauto | pauto | ].
   rewrite Nat.mul_1_l, Nat.mul_1_r.
   apply Nat.pow_le_mono_r; [ easy | ].
   rewrite Hnup; unfold min_n.
   destruct rad; [ easy | cbn; flia ].
Qed.

Theorem pre_Hugo_Herbelin_21 {r : radix} : ∀ u v i,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k, fA_ge_1_ε v i k = true)
  → (∀ k, fA_ge_1_ε (u ⊕ P v) i k = true)
  → (A i (min_n i 0) u + A i (min_n i 0) v < 1)%NQ
  → (A i (min_n i 0) u + A i (min_n i 0) (P v) < 1)%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hvt Hupt Huv1.
assert (Hin : i + 1 ≤ min_n i 0). {
  unfold min_n; destruct rad; [ easy | cbn; flia ].
}
remember (min_n i 0) as nv eqn:Hnv.
specialize (A_ge_1_add_all_true_if v i) as H4.
assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
  intros k; rewrite <- Nat.add_assoc; apply Hv.
}
specialize (H4 H Hvt); clear H.
specialize (all_fA_ge_1_ε_P_999 _ _ Hvt) as Hpa.
destruct H4 as [Hva| [Hva| Hva]].
-rewrite (A_all_9 (P v)); [ | easy ].
 now rewrite (A_all_9 v) in Huv1.
-eapply NQle_lt_trans; [ | apply Huv1 ].
 apply NQadd_le_mono_l.
 rewrite A_all_9; [ | easy ].
 rewrite A_all_18; [ | easy ].
 remember (nv - i - 1) as s eqn:Hs.
 rewrite NQsub_pair_pos; [ | easy | pauto | ]. 2: {
   apply Nat.mul_le_mono_l.
   now apply Nat_pow_ge_1.
 }
 rewrite NQsub_pair_pos; [ | easy | pauto | ]. 2: {
   rewrite Nat.mul_comm.
   apply Nat.mul_le_mono_l.
   now apply Nat_pow_ge_1.
 }
 do 3 rewrite Nat.mul_1_l.
 apply NQle_pair; [ pauto | pauto | ].
 rewrite Nat.mul_comm.
 apply Nat.mul_le_mono_l; flia.
-destruct Hva as (j & Hbef & Hwhi & Haft).
 rewrite (A_9_8_all_18 j v) in Huv1; [ | easy | easy | easy ].
 rewrite (A_all_9 (P v)); [ | easy ].
 apply NQlt_add_lt_sub_r in Huv1.
 rewrite NQsub_sub_distr, NQsub_diag, NQadd_0_l in Huv1.
 apply NQlt_add_lt_sub_r.
 rewrite NQsub_sub_distr, NQsub_diag, NQadd_0_l.
 remember (nv - i - 1) as s eqn:Hs.
 move Huv1 at bottom.
 destruct (le_dec (i + j + 1) (nv - 1)) as [H1| H1]; [ | easy ].
 apply NQnle_gt; intros H7.
 apply NQle_antisymm in H7. 2: {
   rewrite Hs in Huv1.
   apply A_lt_le_pred in Huv1.
   now rewrite <- Hs in Huv1.
 }
 clear Huv1.
 assert (H4 : (∀ k, i + 1 ≤ k ≤ nv - 2 → u k = 0) ∧ u (nv - 1) = 1). {
   rewrite A_num_den in H7.
   unfold den_A in H7.
   rewrite <- Hs in H7.
   apply NQeq_pair in H7; [ | pauto | pauto ].
   rewrite Nat.mul_comm in H7.
   apply Nat.mul_cancel_l in H7; [ | pauto ].
   unfold num_A in H7.
   destruct (lt_dec (nv - 1) (i + 1)) as [H4| H4]. {
     now rewrite summation_empty in H7.
   }
   apply Nat.nlt_ge in H4.
   replace (nv - 1) with (S (nv - 2)) in H7 by flia H4.
   rewrite summation_split_last in H7; [ | flia H4 ].
   replace (S (nv - 2)) with (nv - 1) in H7 by flia H4.
   rewrite Nat.sub_diag in H7.
   rewrite Nat.pow_0_r, Nat.mul_1_r in H7.
   apply Nat.eq_add_1 in H7.
   destruct H7 as [(H7, H8)| (H7, H8)]. {
     exfalso.
     rewrite summation_eq_compat with
         (h := λ j, u j * rad ^ (nv - j - 2) * rad) in H7. 2: {
       intros k Hk.
       rewrite <- Nat.mul_assoc; f_equal.
       rewrite Nat.mul_comm, <- Nat.pow_succ_r'; f_equal.
       flia Hk.
     }
     rewrite <- summation_mul_distr_r in H7.
     rewrite Nat.mul_comm in H7.
     apply Nat.eq_mul_1 in H7.
     flia Hr H7.
   }
   split; [ | easy ].
   intros k Hk.
   specialize (eq_nat_summation_0 _ _ _ H7 _ Hk) as H9.
   cbn in H9.
   apply Nat.eq_mul_0 in H9.
   destruct H9 as [| H9]; [ easy | ].
   now apply Nat.pow_nonzero in H9.
 }
 destruct H4 as (Huz & Hu1).
 specialize (A_ge_1_add_all_true_if (u ⊕ P v) i) as H4.
 assert (H : ∀ k, (u ⊕ P v) (i + k + 1) ≤ 2 * (rad - 1)). {
   intros k; unfold "⊕".
   replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
   rewrite <- Nat.add_assoc at 1.
   apply Nat.add_le_mono; [ easy | ].
   now rewrite Hpa.
 }
 specialize (H4 H Hupt); clear H.
 unfold "⊕" in H4.
 destruct H4 as [H4| [H4| H4]].
 +specialize (H4 (nv - 2 - i)).
  rewrite Hpa in H4.
  replace (i + (nv - 2 - i) + 1) with (nv - 1) in H4 by flia H1.
  rewrite Hu1 in H4.
  flia H4.
 +specialize (H4 0).
  rewrite Huz in H4. 2: {
    rewrite Nat.add_0_r.
    split; [ easy | ].
    rewrite Hnv; unfold min_n.
    destruct rad; [ easy | cbn; flia ].
  }
  rewrite Hpa in H4; flia Hr H4.
 +destruct H4 as (k & Hkbef & Hkwhi & Hkaft).
  rewrite Hpa in Hkwhi.
  flia Hkwhi Hr.
Qed.
