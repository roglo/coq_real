Set Nested Proofs Allowed.
Require Import Utf8 Arith PeanoNat.
Require Import Misc Summation NQ Ureal.

Definition P {r : radix} u := d2n (prop_carr u).
Definition add_series (u v : nat → nat) i := u i + v i.
Notation "u ⊕ v" := (add_series u v) (at level 50).

Definition M {r : radix} (u : nat → _) i := u i mod rad.

Theorem P_le {r : radix} : ∀ u i, P u i ≤ rad - 1.
Proof.
intros.
unfold P, d2n, prop_carr; cbn.
rewrite Nat.sub_1_r.
apply Nat.lt_le_pred.
now apply Nat.mod_upper_bound.
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
 apply NQmul_pos_cancel_l; [ easy | ].
 now apply NQlt_0_pair.
-replace (m // 1)%NQ with (m // 1 * 1)%NQ at 2 by apply NQmul_1_r.
 apply NQmul_le_mono_pos_l. 2: {
   apply NQle_pair_mono_l; split; [ pauto | now apply Nat_pow_ge_1 ].
 }
 now apply NQlt_0_pair.
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

Theorem P_idemp {r : radix} : ∀ u i, P (P u) i = P u i.
Proof.
intros.
unfold P at 1 3; cbn.
rewrite Nat.add_mod_idemp_l; [ | easy ].
rewrite <- (Nat.add_mod_idemp_r _ (carry (P _) _)); [ | easy ].
f_equal; symmetry.
rewrite <- (Nat.add_0_r (u _ + _)) at 1.
f_equal; symmetry.
rewrite Nat.mod_small; [ apply NQintg_P_M | ].
apply (lt_le_trans _ 1); [ | easy ].
replace i with (0 + i) at 1 by easy.
apply (carry_upper_bound_for_adds _ _ 1); [ easy | ].
intros k; rewrite Nat.add_0_l, Nat.mul_1_l.
apply P_le.
Qed.

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

Theorem A_le_pred_lt {r : radix} : ∀ i n u m,
  m ≠ 0
  → i + 1 < n
  → (A i n u ≤ (m - 1) // rad ^ (n - i - 1))%NQ
  → (A i n u < m // rad ^ (n - i - 1))%NQ.
Proof.
intros * Hm Hin Ha.
remember (n - i - 1) as s eqn:Hs.
rewrite A_num_den in Ha |-*.
unfold den_A in Ha |-*.
rewrite <- Hs in Ha |-*.
apply NQle_pair in Ha; [ | pauto | pauto ].
apply NQlt_pair; [ pauto | pauto | ].
rewrite Nat.mul_comm in Ha |-*.
assert (Hsz : 0 < rad ^ s). {
  destruct s; [ flia Hin Hs | ].
  now apply Nat_pow_ge_1.
}
apply Nat.mul_le_mono_pos_l in Ha; [ | easy ].
apply Nat.mul_lt_mono_pos_l; [ easy | ].
eapply Nat.le_lt_trans; [ apply Ha | ].
apply Nat.sub_lt; [ flia Hm | pauto ].
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

Theorem NQintg_A_slow_incr {r : radix} : ∀ u i,
  (∀ k, u (i + k) ≤ 3 * (rad - 1))
  → ∀ k n, min_n i k ≤ n
  → NQintg (A i n u) < NQintg (A i (n + 1) u)
  → NQintg (A i (n + 1) u) = NQintg (A i n u) + 1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur k n Hn Hlt.
assert (Hin : i + 1 < n - 1). {
  unfold min_n in Hn.
  destruct rad; [ easy | cbn in Hn; flia Hn ].
}
rewrite <- ApB_A in Hlt; [ | flia Hin ].
rewrite <- ApB_A; [ | flia Hin ].
rewrite NQintg_add in Hlt; [ | easy | apply B_ge_0 ].
rewrite NQintg_add; [ | easy | apply B_ge_0 ].
remember (NQintg (A i n u)) as x eqn:Hx.
replace x with (x + 0) in Hlt at 1 by easy; subst x.
rewrite <- Nat.add_assoc in Hlt.
apply Nat.add_lt_mono_l in Hlt.
rewrite <- Nat.add_assoc; f_equal.
destruct (zerop (NQintg (NQfrac (A i n u) + NQfrac (B i n u 1)))) as [H1| H1].
-rewrite H1, Nat.add_0_r in Hlt.
 rewrite NQintg_small in Hlt; [ easy | ].
 split; [ apply B_ge_0 | ].
 now apply B_lt_1.
-rewrite NQintg_add_frac in H1.
 destruct (NQlt_le_dec (NQfrac (A i n u) + NQfrac (B i n u 1)) 1)
   as [| H2]; [ easy | clear H1 ].
 rewrite (NQfrac_small (B _ _ _ _)) in H2. 2: {
   split; [ apply B_ge_0 | now apply B_lt_1 ].
 }
 rewrite (NQintg_small (B _ _ _ _)) in Hlt. 2: {
   split; [ apply B_ge_0 | now apply B_lt_1 ].
 }
 rewrite Nat.add_0_l in Hlt.
 rewrite (NQintg_small (B _ _ _ _)). 2: {
   split; [ apply B_ge_0 | now apply B_lt_1 ].
 }
 rewrite Nat.add_0_l.
 rewrite NQintg_add_frac in Hlt.
 rewrite NQintg_add_frac.
 rewrite (NQfrac_small (B _ _ _ _)) in Hlt. 2: {
   split; [ apply B_ge_0 | now apply B_lt_1 ].
 }
 rewrite (NQfrac_small (B _ _ _ _)). 2: {
   split; [ apply B_ge_0 | now apply B_lt_1 ].
 }
 now destruct (NQlt_le_dec (NQfrac (A i n u) + B i n u 1) 1).
Qed.

Theorem all_fA_ge_1_ε_NQintg_A {r : radix} : ∀ i u,
  (∀ k, u (i + k) ≤ 3 * (rad - 1))
  → (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k l, NQintg (A i (min_n i k + l) u) = NQintg (A i (min_n i k) u).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hut k l.
assert (Hin : i + 1 ≤ min_n i k). {
  unfold min_n.
  destruct rad; [ easy | cbn; flia ].
}
symmetry; apply Nat.le_antisymm. {
  apply NQintg_le_mono; [ easy | ].
  rewrite <- ApB_A; [ | easy ].
  apply NQle_add_r, B_ge_0.
}
apply Nat.nlt_ge; intros H1.
induction l; [ rewrite Nat.add_0_r in H1; flia H1 | ].
apply IHl.
eapply Nat.lt_le_trans; [ apply H1 | ].
remember (min_n i k) as n eqn:Hn.
replace (n + S l) with (n + l + 1) by flia.
apply Nat.nlt_ge.
intros H2.
assert (Hur2 : ∀ k, u (i + k) ≤ 3 * (rad - 1)). {
  intros; eapply le_trans; [ apply Hur | ].
  apply Nat.mul_le_mono_r; pauto.
}
specialize (NQintg_A_slow_incr u i Hur2 k (n + l)) as H3.
assert (H : min_n i k ≤ n + l) by (rewrite Hn; flia).
specialize (H3 H H2); clear H H1 H2 IHl.
symmetry in H3.
rewrite Nat.add_comm in H3.
rewrite <- NQintg_add_nat_l in H3; [ | easy ].
symmetry in H3.
apply (NQpair_eq_r _ _ 1) in H3.
rewrite NQintg_of_frac in H3; [ | easy ].
rewrite NQintg_of_frac in H3. 2: {
  apply (NQle_trans _ (A i (n + l) u)); [ easy | ].
  now apply NQle_add_l.
}
rewrite NQfrac_add_nat_l in H3; [ | easy ].
apply NQadd_move_l in H3.
rewrite NQadd_sub_assoc in H3; symmetry in H3.
apply NQadd_move_l in H3.
remember (A i (n + l + 1) u) as x eqn:Hx.
rewrite Hx in H3 at 1.
rewrite <- ApB_A in Hx; [ | flia Hin ].
rewrite NQadd_comm in Hx; subst x.
do 2 rewrite NQadd_assoc in H3.
apply NQadd_cancel_r in H3.
unfold B in H3.
rewrite Nat.add_sub in H3.
rewrite summation_only_one in H3.
specialize (proj1 (frac_ge_if_all_fA_ge_1_ε_for_add u i Hur) Hut k) as H1.
rewrite <- Hn in H1.
specialize (H1 (l + 1)) as H2.
apply NQnlt_ge in H2; apply H2; clear H2.
apply (NQadd_lt_mono_r _ _ 1).
rewrite Nat.add_assoc, H3.
remember (n + l - i) as m eqn:Hm.
apply (NQlt_le_trans _ (1 + u (n + l)%nat // rad ^ m)%NQ).
-apply NQadd_lt_mono_r, NQfrac_lt_1.
-rewrite NQadd_comm.
 apply NQadd_le_mono_r.
 apply (NQle_trans _ ((3 * (rad - 1)) // rad ^ m)).
 +apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_comm.
  replace (n + l) with (i + (n + l - i)) by flia Hin.
  apply Nat.mul_le_mono_l, Hur.
 +rewrite NQsub_pair_pos; [ | easy | pauto | ]. 2: {
    now do 2 rewrite Nat.mul_1_l; apply Nat_pow_ge_1.
  }
  do 2 rewrite Nat.mul_1_l.
  apply NQle_pair; [ pauto | pauto | ].
  replace m with (S k + (m - S k)). 2: {
    rewrite Hm, Hn; unfold min_n.
    destruct rad; [ easy | cbn; flia ].
  }
  rewrite Nat.pow_add_r, Nat.mul_comm, <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  apply Nat.mul_le_mono.
  *remember (m - S k) as p eqn:Hp.
   destruct p.
  --rewrite Hm, Hn in Hp.
    unfold min_n in Hp.
    destruct rad; [ easy | cbn in Hp; flia Hp ].
  --cbn.
    destruct p.
   ++rewrite Hm, Hn in Hp.
     unfold min_n in Hp.
     destruct rad; [ easy | cbn in Hp; flia Hp ].
   ++cbn; rewrite Nat.mul_assoc.
     replace 3 with (3 * 1) by easy.
     apply Nat.mul_le_mono; [ | now apply Nat_pow_ge_1 ].
     destruct rad as [| rr]; [ easy | ].
     destruct rr; [ flia Hr | cbn; flia ].
  *apply Nat.sub_le_mono_r; cbn.
   replace rad with (rad * 1) at 1 by flia.
   apply Nat.mul_le_mono_l.
   now apply Nat_pow_ge_1.
Qed.

Theorem all_fA_ge_1_ε_NQintg_A' {r : radix} : ∀ i u,
  (∀ k, u (i + k) ≤ 3 * (rad - 1))
  → (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k, NQintg (A i (min_n i k) u) = NQintg (A i (min_n i 0) u).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hut k.
replace (min_n i k) with (min_n i 0 + rad * k). 2: {
  unfold min_n.
  rewrite Nat.add_0_r.
  do 3 rewrite Nat.mul_add_distr_l.
  apply Nat.add_shuffle0.
}
now apply all_fA_ge_1_ε_NQintg_A.
Qed.

Theorem fA_lt_1_ε_NQintg_A {r : radix} : ∀ i u j,
  (∀ k, u (i + k) ≤ 3 * (rad - 1))
  → (∀ k, k < j → fA_ge_1_ε u i k = true)
  → fA_ge_1_ε u i j = false
  → ∀ k, j ≤ k → NQintg (A i (min_n i k) u) = NQintg (A i (min_n i j) u).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hjj Huf * Hjk.
replace k with (j + (k - j)) by flia Hjk.
rewrite min_n_add.
rewrite <- ApB_A. 2: {
  unfold min_n; destruct rad; [ easy | cbn; flia ].
}
rewrite NQintg_add; [ | easy | apply B_ge_0 ].
rewrite <- Nat.add_assoc, <- Nat.add_0_r.
f_equal.
assert (HB : (B i (min_n i j) u (rad * (k - j)) < 1 // rad ^ S j)%NQ). {
  specialize (B_upper_bound_for_adds 3 u i j) as HB.
  specialize (HB (rad * (k - j))).
  assert (H : 0 < 3 ≤ rad ^ 2). {
    split; [ pauto | ].
    destruct rad as [| rr]; [ easy | ].
    destruct rr; [ flia Hr | cbn; flia ].
  }
  specialize (HB H); clear H.
  assert (H : ∀ j, j ≥ i → u j ≤ 3 * (rad - 1)). {
    intros p Hp; replace p with (i + (p - i)) by flia Hp.
    apply Hur.
  }
  now specialize (HB H); clear H.
}
rewrite NQintg_small; [ | split ]; [ | apply B_ge_0 | ]. 2: {
  eapply NQlt_le_trans; [ apply HB | ].
  apply NQle_pair_mono_l; split; [ pauto | ].
  now apply Nat_pow_ge_1.
}
rewrite Nat.add_0_l.
rewrite (NQfrac_small (B _ _ _ _)); [ | split ]; [ | apply B_ge_0 | ]. 2: {
  eapply NQlt_le_trans; [ apply HB | ].
  apply NQle_pair_mono_l; split; [ pauto | ].
  now apply Nat_pow_ge_1.
}
apply A_ge_1_false_iff in Huf.
apply NQintg_small.
split.
-replace 0%NQ with (0 + 0)%NQ by easy.
 apply NQadd_le_mono; [ easy | apply B_ge_0 ].
-eapply NQlt_le_trans; [ apply NQadd_lt_mono_l, HB | ].
 apply NQle_add_le_sub_l.
 now apply NQlt_le_incl.
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
  now apply NQmul_nonneg_cancel_r.
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
       replace 0%NQ with (0 // rad ^ (nv - i - 1))%NQ in HAu; [ | easy ].
       apply NQpair_eq_r in HAu.
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
   apply NQpair_eq_r in H7.
   destruct (lt_dec (nv - 1) (i + 1)) as [H4| H4]. {
     unfold num_A in H7.
     now rewrite summation_empty in H7.
   }
   apply Nat.nlt_ge in H4.
   unfold num_A in H7.
   replace (nv - 1) with (S (nv - 2)) in H7 by flia H4.
   rewrite summation_split_last in H7; [ | flia H4 ].
   replace (S (nv - 2)) with (nv - 1) in H7 by flia H4.
   rewrite Nat_sub_sub_swap, Nat.sub_diag in H7.
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

Theorem pre_Hugo_Herbelin_22 {r : radix} : ∀ u v i j,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k, fA_ge_1_ε v i k = true)
  → (∀ k, fA_ge_1_ε (u ⊕ P v) i k = true)
  → fA_ge_1_ε (u ⊕ v) i j = false
  → NQintg (A i (min_n i j) v) = 0
  → (A i (min_n i j) u + A i (min_n i j) v < 1)%NQ
  → (A i (min_n i 0) u + A i (min_n i 0) (P v) < 1)%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hvt Hupt Huvf Hm H5.
remember (min_n i 0) as nv eqn:Hnv.
remember (min_n i j) as nuv eqn:Hnuv.
assert (Hin : i + 1 ≤ nv). {
  rewrite Hnv; unfold min_n; destruct rad; [ easy | cbn; flia ].
}
apply A_ge_1_false_iff in Huvf.
rewrite <- Hnuv in Huvf.
rewrite A_additive in Huvf.
rewrite NQfrac_add_cond in Huvf; [ | easy | easy ].
rewrite NQfrac_small in Huvf. 2: {
  split; [ easy | ].
  apply A_upper_bound_for_dig; intros k Hk.
  replace k with (i + (k - i)) by flia Hk; apply Hu.
}
rewrite NQfrac_small in Huvf. 2: {
  split; [ easy | now apply eq_NQintg_0 in Hm ].
}
apply NQnle_gt in H5.
destruct (NQlt_le_dec (A i nuv u + A i nuv v) 1) as [H4| H4]; [ | easy ].
rewrite NQsub_0_r in Huvf.
clear H4 H5.
rewrite Hnuv in Huvf.
replace j with (0 + j) in Huvf at 1 2 by easy.
rewrite min_n_add, <- Hnv in Huvf.
rewrite <- ApB_A in Huvf; [ | easy ].
rewrite <- ApB_A in Huvf; [ | easy ].
rewrite NQadd_add_swap, NQadd_assoc in Huvf.
specialize (A_ge_1_add_all_true_if v i) as H4.
assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
  intros k; rewrite <- Nat.add_assoc; apply Hv.
}
specialize (H4 H Hvt); clear H.
specialize (all_fA_ge_1_ε_P_999 _ _ Hvt) as Hpa.
destruct H4 as [Hva| [Hva| Hva]].
-rewrite (A_all_9 (P v)); [ | easy ].
 rewrite (A_all_9 v) in Huvf; [ | intros; apply Hva ].
 remember (nv - i - 1) as s eqn:Hs.
 apply (NQle_lt_trans _ (1 - 1 // rad ^ S j)%NQ). 2: {
   now apply NQsub_lt.
 }
 eapply NQle_trans; [ | apply NQlt_le_incl, Huvf ].
 rewrite <- NQadd_assoc.
 apply NQle_add_r.
 replace 0%NQ with (0 + 0)%NQ by easy.
 apply NQadd_le_mono; apply B_ge_0.
-rewrite (A_all_9 (P v)); [ | easy ].
 rewrite (A_all_18 v) in Huvf; [ | intros; apply Hva ].
 remember (nv - i - 1) as s eqn:Hs.
 apply (NQle_lt_trans _ (1 - 1 // rad ^ S j)%NQ); [ | now apply NQsub_lt ].
 eapply NQle_trans; [ | apply NQlt_le_incl, Huvf ].
 do 2 rewrite <- NQadd_assoc.
 apply NQadd_le_mono_l.
 eapply NQle_trans; [ | apply NQle_add_r ]. 2: {
   replace 0%NQ with (0 + 0)%NQ by easy.
   apply NQadd_le_mono; apply B_ge_0.
 }
 apply NQle_sub_le_add_l.
 rewrite NQadd_sub_assoc.
 apply NQle_add_le_sub_r.
 replace 2%NQ with (1 + 1)%NQ by easy.
 rewrite NQadd_assoc.
 apply NQadd_le_mono_r.
 eapply NQle_trans; [ | now apply NQle_add_l ].
 apply NQle_pair; [ pauto | easy | ].
 apply Nat.mul_le_mono_r.
 rewrite Hs, Hnv; apply rad_pow_min_n.
-destruct Hva as (k & Hbef & Hwhi & Haft).
 rewrite (A_all_9 (P v)); [ | easy ].
 rewrite (A_9_8_all_18 k v) in Huvf; [ | easy | easy | easy ].
 remember (nv - i - 1) as s eqn:Hs.
 apply NQlt_add_lt_sub_r in Huvf.
 apply NQlt_add_lt_sub_r.
 rewrite NQsub_sub_distr, NQsub_diag, NQadd_0_l.
 move Huvf at bottom.
 do 3 rewrite <- NQadd_assoc in Huvf.
 rewrite NQadd_comm in Huvf.
 rewrite <- NQadd_sub_swap in Huvf.
 rewrite NQadd_comm in Huvf.
 rewrite NQadd_sub_assoc in Huvf.
 apply NQlt_sub_lt_add_r in Huvf.
 rewrite NQadd_comm in Huvf.
 do 3 rewrite <- NQadd_assoc in Huvf.
 apply NQadd_lt_mono_l in Huvf.
 rewrite NQadd_assoc in Huvf.
 rewrite NQadd_comm in Huvf.
 apply (NQle_lt_trans (A i nv u + 1 // rad ^ S j)%NQ) in Huvf. 2: {
   rewrite NQadd_comm.
   apply NQle_add_r.
   replace 0%NQ with (0 + 0)%NQ by easy.
   apply NQadd_le_mono; apply B_ge_0.
 }
 destruct (le_dec (i + k + 1) (nv - 1)) as [H4| H4]. 2: {
   eapply NQlt_trans; [ | apply Huvf ].
   apply NQlt_sub_lt_add_l.
   now rewrite NQsub_diag.
 }
 apply NQnle_gt; intros H7.
 apply NQle_antisymm in H7. 2: {
   assert (H : (A i nv u < 2 // rad ^ s)%NQ). {
     eapply NQle_lt_trans; [ | apply Huvf ].
     now apply NQle_add_r.
   }
   rewrite Hs in H.
   apply A_lt_le_pred in H.
   now rewrite <- Hs in H.
 }
 assert (H6 : (∀ k, i + 1 ≤ k ≤ nv - 2 → u k = 0) ∧ u (nv - 1) = 1). {
   rewrite A_num_den in H7.
   unfold den_A in H7.
   rewrite <- Hs in H7.
   apply NQpair_eq_r in H7.
   destruct (lt_dec (nv - 1) (i + 1)) as [H6| H6]. {
     unfold num_A in H7.
     now rewrite summation_empty in H7.
   }
   apply Nat.nlt_ge in H6.
   unfold num_A in H7.
   replace (nv - 1) with (S (nv - 2)) in H7 by flia H6.
   rewrite summation_split_last in H7; [ | flia H6 ].
   replace (S (nv - 2)) with (nv - 1) in H7 by flia H6.
   rewrite Nat_sub_sub_swap, Nat.sub_diag in H7.
   rewrite Nat.pow_0_r, Nat.mul_1_r in H7.
   apply Nat.eq_add_1 in H7.
   destruct H7 as [(H7, H8)| (H7, H8)]. {
     exfalso.
     rewrite summation_eq_compat with
         (h := λ j, u j * rad ^ (nv - j - 2) * rad) in H7. 2: {
       intros p Hp.
       rewrite <- Nat.mul_assoc; f_equal.
       rewrite Nat.mul_comm, <- Nat.pow_succ_r'; f_equal.
       flia Hp.
     }
     rewrite <- summation_mul_distr_r in H7.
     rewrite Nat.mul_comm in H7.
     apply Nat.eq_mul_1 in H7.
     flia Hr H7.
   }
   split; [ | easy ].
   intros p Hp.
   specialize (eq_nat_summation_0 _ _ _ H7 _ Hp) as H9.
   cbn in H9.
   apply Nat.eq_mul_0 in H9.
   destruct H9 as [| H9]; [ easy | ].
   now apply Nat.pow_nonzero in H9.
 }
 destruct H6 as (Huz & Hu1).
 specialize (A_ge_1_add_all_true_if (u ⊕ P v) i) as H6.
 assert (H : ∀ k, (u ⊕ P v) (i + k + 1) ≤ 2 * (rad - 1)). {
   intros p; unfold "⊕".
   replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
   rewrite <- Nat.add_assoc at 1.
   apply Nat.add_le_mono; [ easy | ].
   now rewrite Hpa.
 }
 specialize (H6 H Hupt); clear H.
 unfold "⊕" in H6.
 destruct H6 as [H6| [H6| H6]].
 +specialize (H6 (nv - 2 - i)).
  rewrite Hpa in H6.
  replace (i + (nv - 2 - i) + 1) with (nv - 1) in H6 by flia H4.
  rewrite Hu1 in H6.
  flia H6.
 +specialize (H6 0).
  rewrite Huz in H6. 2: {
    rewrite Nat.add_0_r.
    split; [ easy | ].
    rewrite Hnv; unfold min_n.
    destruct rad; [ easy | cbn; flia ].
  }
  rewrite Hpa in H6; flia Hr H6.
 +destruct H6 as (p & Hkbef & Hkwhi & Hkaft).
  rewrite Hpa in Hkwhi.
  flia Hkwhi Hr.
Qed.

Theorem pre_Hugo_Herbelin_31 {r : radix} : ∀ u v i j,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k, fA_ge_1_ε v i k = true)
  → fA_ge_1_ε (u ⊕ P v) i j = false
  → (∀ k, fA_ge_1_ε (u ⊕ v) i k = true)
  → (A i (min_n i 0) u + A i (min_n i 0) v < 1)%NQ
  → (∀ k, P v (i + k + 1) = rad - 1)
  → A i (min_n i j) u = 0%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hvt Hj Huvt H5 H2.
remember (min_n i 0) as nv eqn:Hnv.
remember (min_n i j) as nup eqn:Hnup.
specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) Huvt) as A7.
specialize (A_ge_1_add_all_true_if v i) as H4.
assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
  intros k; rewrite <- Nat.add_assoc; apply Hv.
}
specialize (H4 H Hvt); clear H.
destruct H4 as [H4| [H4| H4]].
-rewrite (A_all_9 v) in H5; [ | intros k Hk; apply H4 ].
 rewrite NQadd_comm in H5.
 apply NQlt_add_lt_sub_l in H5.
 rewrite NQsub_sub_distr, NQsub_diag, NQadd_0_l in H5.
 apply A_lt_le_pred in H5.
 rewrite Nat.sub_diag in H5.
 apply NQle_antisymm in H5; [ | easy ].
 symmetry in H5; remember A as x; cbn in H5; subst x.
 specialize (A7 j) as H7.
 rewrite <- Hnup in H7.
 rewrite A_additive in H7.
 rewrite NQfrac_add_cond in H7; [ | easy | easy ].
 rewrite (NQfrac_small (A _ _ v)) in H7. 2: {
   split; [ easy | ].
   rewrite A_all_9; [ | intros; apply H4 ].
   now apply NQsub_lt.
 }
 rewrite NQfrac_small in H7. 2: {
   split; [ easy | ].
   apply A_upper_bound_for_dig; intros k Hk.
   replace k with (i + (k - i)) by flia Hk.
   apply Hu.
 }
 destruct (NQlt_le_dec (A i nup u + A i nup v) 1) as [H1| H1].
 +rewrite (A_all_9 v) in H1; [ | intros; apply H4 ].
  rewrite NQadd_comm in H1.
  apply NQlt_add_lt_sub_l in H1.
  rewrite NQsub_sub_distr, NQsub_diag, NQadd_0_l in H1.
  apply A_lt_le_pred in H1.
  rewrite Nat.sub_diag in H1.
  now apply NQle_antisymm in H1.
 +move H4 after H2.
  exfalso; apply NQnlt_ge in H7; apply H7; clear H7.
  apply NQlt_sub_lt_add_r.
  rewrite (A_all_9 v); [ | intros; apply H4 ].
  apply NQlt_add_lt_sub_r.
  rewrite NQsub_sub_distr, NQadd_sub.
  rewrite Hnup.
  replace j with (0 + j) at 1 by easy.
  rewrite min_n_add, <- Hnv.
  rewrite <- ApB_A. 2: {
    rewrite Hnv; unfold min_n.
    destruct rad; [ easy | cbn; flia ].
  }
  rewrite H5, NQadd_0_l.
  eapply NQlt_le_trans.
  rewrite Hnv.
  apply B_upper_bound_for_add. {
    intros p Hp.
    replace p with (i + (p - i)) by flia Hp.
    eapply le_trans; [ apply Hu | ].
    flia Hr.
  }
  rewrite Nat.pow_1_r.
  rewrite <- NQadd_sub_swap.
  apply NQle_add_le_sub_l.
  eapply NQle_trans; [ | now apply NQle_add_r ].
  rewrite NQadd_pair; [ | easy | pauto ].
  rewrite Nat.mul_1_l, Nat.mul_1_r.
  apply NQle_pair; [ | easy | ].
  *apply Nat.neq_mul_0.
   split; [ easy | pauto ].
  *apply Nat.mul_le_mono_r.
   rewrite Nat.pow_succ_r' at 1.
   replace rad with (rad * 1) at 3 by flia.
   rewrite <- Nat.mul_add_distr_l.
   apply Nat.mul_le_mono_l.
   cbn; rewrite Nat.mul_comm.
   destruct j; [ cbn; flia Hr | ].
   eapply le_trans; [ | apply Nat.add_le_mul ]; [ | | easy ].
   --now apply Nat.add_le_mono_l.
   --now apply Nat.pow_gt_1.
-apply NQnle_gt in H5.
 exfalso; apply H5; clear H5.
 rewrite (A_all_18 v); [ | intros; apply H4 ].
 eapply NQle_trans; [ | now apply NQle_add_l ].
 apply NQle_add_le_sub_l.
 replace 2%NQ with (1 + 1)%NQ by easy.
 apply NQadd_le_mono_l.
 apply NQle_pair; [ pauto | easy | ].
 apply Nat.mul_le_mono_r.
 rewrite Hnv; apply rad_pow_min_n.
-destruct H4 as (k & Hbef & Hwhi & Haft).
 specialize (A7 j) as H7.
 rewrite <- Hnup in H7.
 rewrite A_additive in H7.
 rewrite NQfrac_add_cond in H7; [ | easy | easy ].
 rewrite NQfrac_small in H7. 2: {
   split; [ easy | ].
   apply A_upper_bound_for_dig; intros p Hp.
   replace p with (i + (p - i)) by flia Hp.
   apply Hu.
 }
 rewrite (A_9_8_all_18 k v) in H7; [ | easy | easy | easy ].
 remember (nup - i - 1) as s eqn:Hs.
 destruct (le_dec (i + k + 1) (nup - 1)) as [Hnk| Hnk].
 +rewrite (NQfrac_small) in H7. 2: {
    split; [ | now apply NQsub_lt ].
    apply NQle_add_le_sub_r; rewrite NQadd_0_r.
    apply NQle_pair; [ pauto | easy | ].
    apply Nat.mul_le_mono_r.
    rewrite Hs, Hnup; apply rad_pow_min_n.
  }
  destruct (NQlt_le_dec (A i nup u + (1 - 2 // rad ^ s))%NQ 1) as [Ha1| Ha1].
  *clear H7.
   rewrite NQadd_comm in Ha1.
   apply NQlt_add_lt_sub_l in Ha1.
   rewrite NQsub_sub_distr, NQsub_diag, NQadd_0_l in Ha1.
   rewrite Hs in Ha1.
   apply A_lt_le_pred in Ha1.
   rewrite Nat.sub_succ, Nat.sub_0_r in Ha1.
   rewrite <- Hs in Ha1.
   destruct (NQeq_dec (A i nup u) 0) as [Ha0| Ha0]; [ easy | exfalso ].
   assert (Ha : A i nup u = (1 // rad ^ s)%NQ). {
     rewrite A_num_den in Ha1, Ha0 |-*; unfold den_A in Ha1, Ha0 |-*.
     rewrite <- Hs in Ha1, Ha0 |-*; f_equal.
     apply NQle_pair in Ha1; [ | pauto | pauto ].
     rewrite Nat.mul_comm in Ha1.
     apply Nat.mul_le_mono_pos_l in Ha1; [ | apply Nat.neq_0_lt_0; pauto ].
     apply Nat.le_antisymm; [ easy | ].
     apply Nat.nlt_ge; intros H; apply Ha0; clear Ha0.
     apply Nat.lt_1_r in H.
     now rewrite H.
   }
   clear Ha0 Ha1.
   specialize (A7 (j + 1)) as H7.
   replace (S (j + 1)) with (j + 2) in H7 by easy.
   rewrite min_n_add, Nat.mul_1_r, <- Hnup in H7.
   rewrite <- ApB_A in H7. 2: {
     rewrite Hnup; unfold min_n; destruct rad; [ easy | cbn; flia ].
   }
   rewrite A_additive in H7.
   rewrite NQfrac_add_cond in H7; [ | | apply B_ge_0 ]. 2: {
     replace 0%NQ with (0 + 0)%NQ by easy.
     now apply NQadd_le_mono.
   }
   rewrite NQfrac_add_cond in H7; [ | easy | easy ].
   rewrite (NQfrac_small (A i nup u)) in H7. 2: {
     split; [ easy | ].
     apply A_upper_bound_for_dig; intros p Hp.
     replace p with (i + (p - i)) by flia Hp; apply Hu.
   }
   rewrite Ha in H7.
   rewrite NQfrac_small in H7. 2: {
     split; [ easy | ].
     rewrite (A_9_8_all_18 k); [ | easy | easy | easy ].
     apply NQsub_lt.
     destruct (le_dec (i + k + 1) (nup - 1)) as [H| H]; [ easy | flia H Hnk ].
   }
   rewrite NQfrac_small in H7. 2: {
     split; [ apply B_ge_0 | ].
     rewrite Hnup.
     eapply NQlt_trans.
     -apply (B_upper_bound_for_adds 3).
      +split; [ pauto | ].
       destruct rad as [| rr]; [ easy | ].
       destruct rr; [ flia Hr | cbn; flia ].
      +intros p Hp; replace p with (i + (p - i)) by flia Hp.
       unfold "⊕"; replace 3 with (1 + 2) by easy.
       rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
       apply Nat.add_le_mono; [ apply Hu | apply Hv ].
     -apply NQlt_pair; [ pauto | easy | ].
      apply Nat.mul_lt_mono_pos_r; [ pauto | ].
      cbn; apply (lt_le_trans _ 2); [ pauto | ].
      replace 2 with (2 * 1) by easy.
      apply Nat.mul_le_mono; [ easy | ].
      now apply Nat_pow_ge_1.
   }
   rewrite (A_9_8_all_18 k v) in H7; [ | easy | easy | easy ].
   destruct (le_dec (i + k + 1) (nup - 1)) as [H| H]; [ | flia Hnk H ].
   clear H; rewrite <- Hs in H7.
   rewrite NQadd_sub_assoc in H7.
   replace (1 // rad ^ s + 1)%NQ with (1 + 1 // rad ^ s)%NQ in H7
     by apply NQadd_comm.
   rewrite (NQadd_sub_swap 1%NQ) in H7.
   rewrite <- (NQsub_sub_distr 1%NQ) in H7.
   rewrite <- NQpair_sub_l in H7; [ | pauto ].
   replace (2 - 1) with 1 in H7 by easy.
   destruct (NQlt_le_dec (1 - 1 // rad ^ s)%NQ 1) as [H11| H11].
  --rewrite NQsub_0_r in H7.
    destruct (NQlt_le_dec (1 - 1 // rad ^ s + B i nup (u ⊕ v) rad)%NQ 1)
      as [Hrb| Hrb].
   ++apply NQnle_gt in Hrb; apply Hrb; clear Hrb.
     rewrite <- NQadd_sub_swap.
     apply NQle_add_le_sub_r.
     rewrite NQadd_comm.
     apply NQadd_le_mono_l.
     unfold B.
     rewrite summation_split_first; [ | flia Hr ].
     unfold "⊕" at 1.
     replace nup with (i + k + (nup - i - k - 2) + 2) at 2 by flia Hnk.
     rewrite Haft.
     replace (nup - i) with (s + 1). 2: {
       rewrite Hs.
       rewrite Nat.sub_add; [ easy | ].
       rewrite Hnup; unfold min_n.
       destruct rad; [ easy | cbn; flia ].
     }
     eapply NQle_trans; [ | apply NQle_add_r ].
    **rewrite NQpair_add_l.
      eapply NQle_trans; [ | apply NQle_add_l ].
    ---apply NQle_pair; [ pauto | pauto | ].
       rewrite Nat.mul_1_l, Nat.mul_sub_distr_l, Nat.mul_1_r.
       rewrite Nat.pow_add_r, Nat.pow_1_r.
       apply Nat.mul_le_mono_l.
       destruct rad as [| rr]; [ easy | ].
       destruct rr; [ flia Hr | cbn; flia ].
    ---replace 0%NQ with (0 // 1)%NQ by easy.
       apply NQle_pair; [ easy | pauto | cbn; flia ].
    **specialize
        (@all_0_summation_0 _ NQ_ord_ring (λ j, 0%NQ) (S nup) (nup + rad - 1))
        as Hsum0.
      remember summation as f; cbn in Hsum0; subst f.
      rewrite <- Hsum0; [ | easy ].
      apply summation_le_compat.
      intros p Hp.
      replace 0%NQ with (0 // 1)%NQ by easy.
      apply NQle_pair; [ easy | pauto | cbn; flia ].
   ++apply NQnlt_ge in H7; apply H7; clear H7.
     rewrite NQadd_sub_swap, NQsub_sub_swap.
     rewrite NQsub_diag, NQsub_0_l, NQadd_comm, NQadd_opp_r.
     apply NQlt_sub_lt_add_r.
     eapply NQlt_le_trans.
    **rewrite Hnup.
      apply (B_upper_bound_for_adds 3).
    ---split; [ pauto | ].
       destruct rad as [| rr]; [ easy | ].
       destruct rr; [ flia Hr | cbn; flia ].
    ---intros p Hp; replace p with (i + (p - i)) by flia Hp.
       unfold "⊕"; replace 3 with (1 + 2) by easy.
       rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
       apply Nat.add_le_mono; [ apply Hu | apply Hv ].
    **rewrite <- NQadd_sub_swap.
      apply NQle_add_le_sub_r.
      rewrite NQadd_pair; [ | pauto | pauto ].
      rewrite Nat.mul_1_l, Nat.mul_1_r, <- Nat.pow_add_r.
      rewrite NQadd_pair; [ | pauto | pauto ].
      rewrite Nat.mul_1_l, Nat.mul_1_r.
      apply NQle_pair; [ pauto | pauto | ].
      rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
      eapply Nat.le_trans; [ | apply Nat.le_add_r ].
      apply Nat.mul_le_mono_r.
      replace (j + 2) with (S j + 1) by flia.
      rewrite Nat.pow_add_r, Nat.pow_1_r.
      replace (rad ^ S j) with (rad ^ S j * 1) at 1 by flia.
      rewrite <- Nat.mul_add_distr_l.
      rewrite Nat.pow_add_r, Nat.mul_comm.
      apply Nat.mul_le_mono_r.
      replace (S j + 1) with (S (S j)) by flia.
      clear - Hr.
      induction j.
      destruct rad as [| rr]; [ easy | ].
      destruct rr; [ flia Hr | cbn; flia ].
      eapply le_trans; [ apply IHj | ].
      apply Nat.pow_le_mono_r; [ easy | flia ].
  --apply NQnlt_ge in H11; apply H11; clear H11.
    now apply NQsub_lt.
  *apply NQle_sub_le_add_r in Ha1.
   rewrite NQsub_sub_distr, NQsub_diag, NQadd_0_l in Ha1.
   rewrite NQadd_sub_swap, NQadd_sub_assoc, NQsub_add in H7.
   apply A_ge_1_false_iff in Hj.
   rewrite <- Hnup in Hj.
   rewrite A_additive in Hj.
   rewrite NQfrac_add_cond in Hj; [ | easy | easy ].
   rewrite NQfrac_small in Hj. 2: {
     split; [ easy | ].
     apply A_upper_bound_for_dig; intros p Hp.
     replace p with (i + (p - i)) by flia Hp.
     apply Hu.
   }
   rewrite NQfrac_small in Hj. 2: {
     split; [ easy | ].
     rewrite A_all_9; [ | intros; apply H2 ].
     now apply NQsub_lt.
   }
   destruct (NQlt_le_dec (A i nup u + A i nup (P v)) 1) as [H8| H8].
  --rewrite (A_all_9 (P v)) in H8; [ | intros; apply H2 ].
    apply NQlt_add_lt_sub_r in H8.
    rewrite NQsub_sub_distr, NQsub_diag, NQadd_0_l in H8.
    apply A_lt_le_pred in H8.
    rewrite Nat.sub_diag in H8.
    now apply NQle_antisymm in H8.
  --move Hj at bottom.
    rewrite (A_all_9 (P v)) in Hj; [ | intros; apply H2 ].
    rewrite <- Hs, NQadd_sub_swap, NQadd_sub_assoc in Hj.
    rewrite NQsub_add in Hj.
    exfalso; apply NQnlt_ge in H7; apply H7; clear H7.
    eapply NQle_lt_trans; [ | apply Hj ].
    apply NQsub_le_mono; [ apply NQle_refl | ].
    apply NQle_pair; [ pauto | pauto | ].
    rewrite Nat.mul_1_l.
    replace (rad ^ s * 2) with (rad ^ s + rad ^ s) by flia.
    apply Nat.le_sub_le_add_l.
    rewrite Nat.sub_diag.
    apply Nat.le_0_l.
 +apply Nat.nle_gt in Hnk.
  rewrite NQfrac_small in H7. 2: {
    split; [ | now apply NQsub_lt ].
    apply NQle_add_le_sub_r.
    rewrite NQadd_0_r.
    apply NQle_pair; [ pauto | easy | ].
    apply Nat.mul_le_mono_r.
    now apply Nat_pow_ge_1.
  }
  destruct (NQlt_le_dec (A i nup u + (1 - 1 // rad ^ s))%NQ 1) as [Ha1| Ha1].
  *apply NQlt_add_lt_sub_r in Ha1.
   rewrite NQsub_sub_distr, NQsub_diag, NQadd_0_l in Ha1.
   rewrite Hs in Ha1.
   apply A_lt_le_pred in Ha1.
   rewrite Nat.sub_diag in Ha1.
   now apply NQle_antisymm in Ha1.
  *exfalso; apply NQnlt_ge in H7; apply H7; clear H7.
   rewrite NQadd_sub_swap, NQadd_sub_assoc, NQsub_add.
   apply NQlt_sub_lt_add_r.
   rewrite Hnup.
   replace j with (0 + j) at 1 by easy.
   rewrite min_n_add, <- Hnv.
   rewrite <- ApB_A. 2: {
     rewrite Hnv; unfold min_n.
     destruct rad; [ easy | cbn; flia ].
   }
   rewrite (A_all_9 v) in H5. 2: {
     intros p Hp; apply Hbef.
     rewrite Hnup in Hnk.
     replace j with (0 + j) in Hnk at 1 by easy.
     rewrite min_n_add, <- Hnv in Hnk.
     flia Hnk Hp.
   }
   apply NQlt_add_lt_sub_r in H5.
   rewrite NQsub_sub_distr, NQsub_diag, NQadd_0_l in H5.
   apply A_lt_le_pred in H5.
   rewrite Nat.sub_diag in H5.
   apply NQle_antisymm in H5; [ | easy ].
   rewrite <- H5, NQadd_0_l.
   specialize (B_upper_bound_for_adds 1 u i 0 (rad * j)) as H1.
   assert (H : 0 < 1 ≤ rad ^ 2). {
     split; [ pauto | now apply Nat_pow_ge_1 ].
   }
   specialize (H1 H); clear H.
   assert (H : ∀ j, j ≥ i → u j ≤ 1 * (rad - 1)). {
     intros p Hp; rewrite Nat.mul_1_l.
     replace p with (i + (p - i)) by flia Hp; apply Hu.
   }
   specialize (H1 H); clear H.
   rewrite <- Hnv, Nat.pow_1_r in H1.
   eapply NQlt_le_trans; [ apply H1 | ].
   rewrite <- NQadd_sub_swap.
   apply NQle_add_le_sub_r.
   rewrite NQadd_pair; [ | pauto | easy ].
   rewrite NQadd_pair; [ | easy | pauto ].
   do 2 rewrite Nat.mul_1_l, Nat.mul_1_r.
   apply NQle_pair; [ | pauto | ]. {
     apply Nat.neq_mul_0; split; [ pauto | easy ].
   }
   rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
   apply Nat.le_sub_le_add_l.
   rewrite <- Nat.mul_sub_distr_r.
   replace (rad + rad ^ S j - rad ^ S j * rad) with 0; [ cbn; flia | ].
   symmetry; apply Nat.sub_0_le.
   replace (rad ^ S j) with (rad ^ j * rad) at 1 by (cbn; flia).
   replace rad with (1 * rad) at 1 by flia.
   rewrite <- Nat.mul_add_distr_r.
   apply Nat.mul_le_mono_r.
   enough (H : 1 ≤ rad ^ S j - rad ^ j). {
     apply (Nat.add_le_mono_r _ _ (rad ^ j)) in H.
     rewrite Nat.sub_add in H; [ easy | ].
     cbn; replace (rad ^ j) with (1 * rad ^ j) at 1 by flia.
     now apply Nat.mul_le_mono_r.
   }
   cbn; replace (rad ^ j) with (1 * rad ^ j) at 2 by flia.
   rewrite <- Nat.mul_sub_distr_r.
   destruct j.
  --rewrite Nat.pow_0_r, Nat.mul_1_r; flia Hr.
  --replace 1 with (1 * 1) at 1 by easy.
    apply Nat.mul_le_mono; [ flia Hr | ].
    now apply Nat_pow_ge_1.
Qed.

Theorem pre_Hugo_Herbelin_32_lemma_999 {r : radix} : ∀ u v i j k,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, P v (i + k + 1) = rad - 1)
  → (∀ p, i + p + 1 < min_n i k → v (i + p + 1) = rad - 1)
  → fA_ge_1_ε (u ⊕ P v) i j = false
  → fA_ge_1_ε (u ⊕ v) i k = false
  → (A i (min_n i k) u + A i (min_n i k) v < 1)%NQ
  → A i (min_n i j) u = 0%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hpr Hbef Hup Huv Haa.
remember (min_n i j) as nij eqn:Hnij.
remember (min_n i k) as nik eqn:Hnik.
apply A_ge_1_false_iff in Huv.
rewrite <- Hnik in Huv.
rewrite A_additive in Huv.
rewrite (A_all_9 v) in Huv; [ | easy ].
rewrite (A_all_9 v) in Haa; [ | easy ].
rewrite NQadd_comm in Haa.
apply NQlt_add_lt_sub_l in Haa.
rewrite NQsub_sub_distr, NQsub_diag, NQadd_0_l in Haa.
apply A_lt_le_pred in Haa.
rewrite Nat.sub_diag in Haa.
apply NQle_antisymm in Haa; [ | easy ].
symmetry in Haa; remember A as f; cbn in Haa; subst f.
destruct (le_dec j k) as [Hljk| Hljk].
-rewrite Hnik in Haa; replace k with (j + (k - j)) in Haa by flia Hljk.
 rewrite min_n_add, <- Hnij in Haa.
 rewrite <- ApB_A in Haa. 2: {
   rewrite Hnij; unfold min_n; destruct rad; [ easy | cbn; flia ].
 }
 move Haa at bottom.
 apply NQeq_add_0 in Haa; [ easy | easy | apply B_ge_0 ].
-apply Nat.nle_gt in Hljk.
 apply A_ge_1_false_iff in Hup.
 move Hup at bottom.
 rewrite <- Hnij in Hup.
 rewrite A_additive in Hup.
 rewrite (A_all_9 (P v)) in Hup; [ | easy ].
 remember (nij - i - 1) as sj eqn:Hsj.
 assert (Hrp : (0 ≤ 1 - 1 // rad ^ sj)%NQ). {
   rewrite NQsub_pair_pos; [ | easy | pauto | ]. 2: {
     apply Nat.mul_le_mono_l.
     now apply Nat_pow_ge_1.
   }
   do 2 rewrite Nat.mul_1_l.
   replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQle_pair; [ easy | pauto | cbn; flia ].
 }
 rewrite NQfrac_add_cond in Hup; [ | easy | easy ].
 rewrite NQfrac_small in Hup. 2: {
   split; [ easy | ].
   apply A_upper_bound_for_dig.
   intros q Hq; replace q with (i + (q - i)) by flia Hq; apply Hu.
 }
 rewrite NQfrac_small in Hup. 2: {
   split; [ easy | now apply NQsub_lt ].
 }
 destruct (NQlt_le_dec (A i nij u + (1 - 1 // rad ^ sj))%NQ 1) as [Har| Har].
 +exfalso; apply NQnle_gt in Hup; apply Hup; clear Hup.
  rewrite NQsub_0_r, NQadd_sub_assoc.
  apply NQle_sub_le_add_l.
  rewrite NQadd_sub_assoc.
  apply NQle_add_le_sub_l.
  rewrite NQadd_assoc, NQadd_comm.
  apply NQadd_le_mono_r.
  eapply NQle_trans; [ | now apply NQle_add_r ].
  apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_1_l, Nat.mul_1_r.
  apply Nat.pow_le_mono_r; [ easy | ].
  rewrite Hsj, Hnij; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
 +move Har at bottom.
  rewrite NQadd_sub_assoc in Har.
  apply NQle_add_le_sub_r in Har.
  apply NQadd_le_mono_r in Har.
  rewrite Haa, NQadd_0_l in Huv.
  remember (nik - i - 1) as sk eqn:Hsk.
  assert (Hrv : (0 ≤ 1 - 1 // rad ^ sk)%NQ). {
    rewrite NQsub_pair_pos; [ | easy | pauto | ]. 2: {
      apply Nat.mul_le_mono_l.
      now apply Nat_pow_ge_1.
    }
    do 2 rewrite Nat.mul_1_l.
    replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQle_pair; [ easy | pauto | cbn; flia ].
  }
  rewrite NQfrac_small in Huv. 2: {
    split; [ easy | now apply NQsub_lt ].
  }
  exfalso; apply NQnle_gt in Huv; apply Huv; clear Huv.
  apply NQsub_le_mono; [ apply NQle_refl | ].
  apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_1_l, Nat.mul_1_r.
  apply Nat.pow_le_mono_r; [ easy | ].
  rewrite Hsk, Hnik; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
Qed.

(* cui-là est plus propre que les précédents ; faut donc peut-être
   nettoyer ces derniers... trucs : les cas 999 et 99981818 peuvent
   être regroupés, et le cas 99981818 avec 181818... *)
Theorem pre_Hugo_Herbelin_32 {r : radix} : ∀ u v i j k,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k, fA_ge_1_ε v i k = true)
  → fA_ge_1_ε (u ⊕ P v) i j = false
  → fA_ge_1_ε (u ⊕ v) i k = false
  → (A i (min_n i k) u + A i (min_n i k) v < 1)%NQ
  → A i (min_n i j) u = 0%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hvt Hup Huv Haa.
specialize (all_fA_ge_1_ε_P_999 v i Hvt) as Hpr.
remember (min_n i j) as nij eqn:Hnij.
remember (min_n i k) as nik eqn:Hnik.
specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) Hvt) as Avt.
specialize (A_ge_1_add_all_true_if v i) as Hvr.
assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
  intros p; rewrite <- Nat.add_assoc; apply Hv.
}
specialize (Hvr H Hvt); clear H.
destruct Hvr as [Hvr| [Hvr| Hvr]].
-subst nij nik.
 now apply (pre_Hugo_Herbelin_32_lemma_999 _ v _ _ k).
-rewrite (A_all_18 v) in Haa; [ | intros p; apply Hvr ].
 exfalso; apply NQnle_gt in Haa; apply Haa; clear Haa.
 rewrite NQadd_comm, <- NQadd_sub_swap.
 apply NQle_add_le_sub_l.
 replace 2%NQ with (1 + 1)%NQ by easy.
 rewrite <- NQadd_assoc.
 apply NQadd_le_mono_l.
 eapply NQle_trans; [ | now apply NQle_add_r ].
 apply NQle_pair; [ pauto | pauto | ].
 apply Nat.mul_le_mono_pos_r; [ pauto | ].
 rewrite Hnik; apply rad_pow_min_n.
-destruct Hvr as (p & Hbef & Hwhi & Haft).
 destruct (lt_dec (nik - 1) (i + p + 1)) as [Hip| Hip].
 +destruct (le_dec (i + p + 1) (nik - 1)) as [H| H]. {
    now apply Nat.nlt_ge in H.
  }
  subst nij nik.
  apply (pre_Hugo_Herbelin_32_lemma_999 _ v _ _ k); try easy.
  intros l Hl; apply Hbef; flia H Hl.
 +apply Nat.nlt_ge in Hip.
  apply A_ge_1_false_iff in Huv.
  exfalso; apply NQnle_gt in Huv; apply Huv; clear Huv.
  rewrite <- Hnik.
  rewrite NQfrac_small. 2: {
    split; [ easy | now rewrite A_additive ].
  }
  rewrite A_additive.
  rewrite (A_9_8_all_18 p v); [ | easy | easy | easy ].
  destruct (le_dec (i + p + 1) (nik - 1)) as [H| H]; [ clear H | easy ].
  rewrite NQadd_sub_assoc.
  apply NQle_sub_le_add_r.
  rewrite <- NQadd_sub_assoc.
  rewrite <- NQadd_assoc, NQadd_comm.
  rewrite <- NQadd_assoc, <- NQadd_sub_swap.
  apply NQle_add_le_sub_l, NQadd_le_mono_l.
  eapply NQle_trans; [ | now apply NQle_add_r ].
  apply NQle_pair; [ pauto | pauto | ].
  remember (nik - i - 1) as s eqn:Hs.
  rewrite Hnik in Hs; unfold min_n in Hs.
  destruct s.
  *destruct rad; [ easy | cbn in Hs; flia Hs ].
  *rewrite (Nat.pow_succ_r' _ s), Nat.mul_1_r.
   apply Nat.mul_le_mono; [ easy | ].
   apply Nat.pow_le_mono_r; [ easy | ].
   apply Nat.succ_le_mono.
   rewrite Hs.
   destruct rad; [ easy | cbn; flia ].
Qed.

Theorem pre_Hugo_Herbelin_41 {r : radix} : ∀ u v i j,
  (∀ k : nat, u (i + k) ≤ rad - 1)
  → (∀ k : nat, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k : nat, fA_ge_1_ε v i k = true)
  → (∀ k : nat, fA_ge_1_ε (u ⊕ P v) i k = true)
  → A i (min_n i 0) u = 0%NQ
  → (A i (min_n i j) u + A i (min_n i j) v < 2)%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hvt H2 H1.
specialize (all_fA_ge_1_ε_P_999 v i Hvt) as Hpr.
remember (min_n i 0) as ni eqn:Hni.
remember (min_n i j) as nij eqn:Hnij.
specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) H2) as Hup.
specialize (Hup j) as H4; rewrite <- Hnij in H4.
rewrite A_additive in H4.
rewrite (A_all_9 (P v)) in H4; [ | easy ].
remember (nij - i - 1) as s eqn:Hs.
rewrite NQfrac_add_cond in H4; [ | easy | ]. 2: {
  apply NQle_add_le_sub_r.
  rewrite NQadd_0_r.
  apply NQle_pair; [ pauto | easy | ].
  now apply Nat.mul_le_mono_r, Nat_pow_ge_1.
}
rewrite NQfrac_small in H4. 2: {
  split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros k Hk; replace k with (i + (k - i)) by flia Hk; apply Hu.
}
rewrite NQfrac_small in H4. 2: {
  split.
  -apply NQle_add_le_sub_r.
   rewrite NQadd_0_r.
   apply NQle_pair; [ pauto | easy | ].
   now apply Nat.mul_le_mono_r, Nat_pow_ge_1.
  -now apply NQsub_lt.
}
rewrite NQadd_sub_assoc in H4.
destruct (NQlt_le_dec (A i nij u + 1 - 1 // rad ^ s)%NQ 1) as [Har| Har].
-apply NQlt_sub_lt_add_l, NQadd_lt_mono_r in Har.
 rewrite Hs in Har.
 apply A_lt_le_pred in Har.
 apply NQle_antisymm in Har; [ | easy ].
 rewrite <- Har, NQadd_0_l.
 eapply NQle_lt_trans.
 +apply A_upper_bound_for_add.
  intros k; rewrite <- Nat.add_assoc; apply Hv.
 +rewrite NQmul_sub_distr_l, NQmul_1_r.
  now apply NQsub_lt.
-rewrite NQsub_sub_swap, NQadd_sub in H4.
 rewrite Hnij in H4.
 replace j with (0 + j) in H4 at 1 by easy.
 rewrite min_n_add, <- Hni in H4.
 rewrite <- ApB_A in H4. 2: {
   rewrite Hni; unfold min_n.
   destruct rad; [ easy | cbn; flia ].
 }
 rewrite H1, NQadd_0_l in H4.
 exfalso; apply NQnlt_ge in H4; apply H4; clear H4.
 apply NQlt_sub_lt_add_r.
 eapply NQlt_le_trans.
 +rewrite Hni.
  apply (B_upper_bound_for_adds 1).
  *split; [ pauto | ].
   rewrite Nat.pow_2_r.
   replace 1 with (1 * 1) by easy.
   now apply Nat.mul_le_mono.
  *intros p Hp; rewrite Nat.mul_1_l.
   replace p with (i + (p - i)) by flia Hp; apply Hu.
 +rewrite Nat.pow_1_r.
  eapply NQle_trans; [ | now apply NQle_add_r ].
  apply NQle_add_le_sub_r.
  rewrite NQadd_pair; [ | pauto | easy ].
  rewrite Nat.mul_1_l, Nat.mul_1_r.
  apply NQle_pair; [ apply Nat.neq_mul_0; pauto | easy | ].
  apply Nat.mul_le_mono_r.
  replace rad with (1 + (rad - 1)) at 4 by flia Hr.
  rewrite Nat.mul_add_distr_l, Nat.mul_1_r, Nat.add_comm.
  apply Nat.add_le_mono_l.
  rewrite Nat.pow_succ_r', <- Nat.mul_assoc.
  replace rad with (rad * 1) at 1 by flia.
  apply Nat.mul_le_mono_l.
  replace 1 with (1 * 1) at 1 by easy.
  apply Nat.mul_le_mono; [ | flia Hr ].
  now apply Nat_pow_ge_1.
Qed.

(* bizarre, ces hypothèses H4 et H1, c'est en fait A i nup u = 0
   que je prouve ci-dessous (Hau) *)
Theorem pre_Hugo_Herbelin_42 {r : radix} : ∀ u v i j k,
  (∀ k : nat, u (i + k) ≤ rad - 1)
  → (∀ k : nat, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k : nat, fA_ge_1_ε v i k = true)
  → fA_ge_1_ε (u ⊕ P v) i k = false
  → (∀ j0 : nat, j0 < j → fA_ge_1_ε (u ⊕ v) i j0 = true)
  → fA_ge_1_ε (u ⊕ v) i j = false
  → NQintg (A i (min_n i j) v) = 1
  → B i (min_n i 0) u (rad * k) = 0%NQ
  → A i (min_n i 0) u = 0%NQ
  → (A i (min_n i j) u + A i (min_n i j) v < 2)%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv H3 Hk Hjj Hj Hm H4 H1.
remember (min_n i 0) as nv eqn:Hnv.
remember (min_n i k) as nup eqn:Hnup.
remember (min_n i j) as nuv eqn:Hnuv.
move nv after nuv; move nup before nuv.
move Hnv after Hnuv; move Hnup before Hnuv.
specialize (all_fA_ge_1_ε_P_999 v i H3) as Hap.
assert (Hau : A i nup u = 0%NQ). {
  rewrite Hnup.
  replace k with (0 + k) by easy.
  rewrite min_n_add, <- Hnv.
  rewrite <- ApB_A, H1, H4; [ easy | ].
  rewrite Hnv; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
}
rewrite Hnuv at 1.
replace j with (0 + j) at 1 by easy.
rewrite min_n_add, <- Hnv.
rewrite <- ApB_A. 2: {
  rewrite Hnv; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
}
rewrite H1, NQadd_0_l.
destruct (le_dec j k) as [Hljk| Hljk].
-replace k with (j + (k - j)) in H4 by flia Hljk.
 rewrite Nat.mul_add_distr_l in H4.
 rewrite B_add_r in H4. 2: {
   intros H; apply Nat.eq_add_0 in H.
   destruct H as (H, _).
   rewrite Hnv in H; unfold min_n in H.
   destruct rad; [ easy | cbn in H; flia H ].
 }
 apply NQeq_add_0 in H4; [ | apply B_ge_0 | apply B_ge_0 ].
 destruct H4 as (H4, H5); rewrite H4, NQadd_0_l.
 eapply NQle_lt_trans.
 +apply A_upper_bound_for_add.
  intros p; rewrite <- Nat.add_assoc; apply Hv.
 +rewrite NQmul_sub_distr_l, NQmul_1_r.
  now apply NQsub_lt.
-apply Nat.nle_gt in Hljk.
 replace j with (k + (j - k)) by flia Hljk.
 rewrite Nat.mul_add_distr_l.
 rewrite B_add_r. 2: {
   intros H; apply Nat.eq_add_0 in H.
   destruct H as (H, _).
   rewrite Hnv in H; unfold min_n in H.
   destruct rad; [ easy | cbn in H; flia H ].
 }
 rewrite H4, NQadd_0_l.
 rewrite Hnv, <- min_n_add, Nat.add_0_l, <- Hnup.
 specialize (Hjj _ Hljk) as H2.
 apply A_ge_1_true_iff in H2.
 apply A_ge_1_false_iff in Hj.
 rewrite <- Hnup in H2.
 rewrite <- Hnuv in Hj.
 move Hj at bottom.
 rewrite A_additive in H2, Hj.
 rewrite Hau, NQadd_0_l in H2.
 rewrite NQfrac_add_cond in Hj; [ | easy | easy ].
 assert (H : (∀ n, 0 ≤ A i n u < 1)%NQ). {
   intros n.
   split; [ easy | ].
   apply A_upper_bound_for_dig.
   intros p Hp; replace p with (i + (p - i)) by flia Hp; apply Hu.
 }
 rewrite NQfrac_small in Hj; [ clear H | easy ].
 rename nup into nik; rename nuv into nij.
 rename Hnup into Hnik; rename Hnuv into Hnij.
 rewrite (NQfrac_less_small 1) in Hj. 2: {
   split.
   -specialize (NQintg_of_frac (A i nij v) (A_ge_0 _ _ _)) as H.
    rewrite Hm in H; rewrite H.
    now apply NQle_sub_l.
   -eapply NQle_lt_trans.
    +apply A_upper_bound_for_add.
     intros p; rewrite <- Nat.add_assoc; apply Hv.
    +rewrite NQmul_sub_distr_l, NQmul_1_r.
     now apply NQsub_lt.
 }
 rewrite NQadd_sub_assoc in Hj.
 destruct (NQlt_le_dec (A i nij u + A i nij v - 1)%NQ 1) as [Hjuv| Hjuv].
 +rewrite NQsub_0_r in Hj; clear Hjuv.
  apply (NQlt_sub_lt_add_l (A i nij u + A i nij v)%NQ) in Hj.
  rewrite NQadd_sub_assoc in Hj.
  replace (1 + 1)%NQ with 2%NQ in Hj by easy.
  rewrite Hnij in Hj at 1.
  replace j with (k + (j - k)) in Hj at 1 by flia Hljk.
  rewrite min_n_add in Hj.
  rewrite <- ApB_A in Hj. 2: {
    unfold min_n; destruct rad; [ easy | cbn; flia ].
  }
  rewrite <- Hnik in Hj.
  rewrite Hau, NQadd_0_l in Hj.
  eapply NQlt_le_trans; [ apply Hj | ].
  now apply NQle_sub_l.
 +apply A_ge_1_false_iff in Hk.
  rewrite A_additive, <- Hnik in Hk.
  rewrite NQfrac_add_cond in Hk; [ | easy | easy ].
  rewrite Hau, NQfrac_0, NQadd_0_l in Hk.
  rewrite NQfrac_small in Hk. 2: {
    split; [ easy | ].
    apply A_upper_bound_for_dig.
    intros p Hp; replace p with (i + (p - i - 1) + 1) by flia Hp.
    now rewrite Hap.
  }
  rewrite A_all_9 in Hk; [ | easy ].
  remember (nik - i - 1) as s eqn:Hs.
  destruct (NQlt_le_dec (1 - 1 // rad ^ s)%NQ 1) as [Hup| Hup].
  *rewrite NQsub_0_r in Hk; clear Hup.
   exfalso; apply NQnle_gt in Hk; apply Hk; clear Hk.
   apply NQsub_le_mono; [ apply NQle_refl | ].
   apply NQle_pair; [ pauto | pauto | ].
   rewrite Nat.mul_1_l, Nat.mul_1_r.
   apply Nat.pow_le_mono_r; [ easy | ].
   rewrite Hs, Hnik; unfold min_n.
   destruct rad; [ easy | cbn; flia ].
  *exfalso; apply NQnlt_ge in Hup; apply Hup; clear Hup.
   now apply NQsub_lt.
Qed.

Theorem pre_Hugo_Herbelin_51 {r : radix} : ∀ u v i,
  (∀ k : nat, u (i + k) ≤ rad - 1)
  → (∀ k : nat, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k : nat, fA_ge_1_ε v i k = true)
  → (∀ k : nat, fA_ge_1_ε (u ⊕ P v) i k = true)
  → NQintg (A i (min_n i 0) v) = 1
  → (A i (min_n i 0) u + A i (min_n i 0) v < 2)%NQ
  → (A i (min_n i 0) u + A i (min_n i 0) (P v) < 1)%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hvt Hupt Ha1 Haa.
remember (min_n i 0) as ni eqn:Hni.
move ni before i.
specialize (all_fA_ge_1_ε_P_999 v i Hvt) as Hpr.
rewrite (A_all_9 (P _)); [ | easy ].
rewrite NQadd_sub_assoc.
apply NQlt_sub_lt_add_l, NQadd_lt_mono_r.
apply A_le_pred_lt; [ easy | | ]. {
  rewrite Hni; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
}
rewrite Nat.sub_diag.
enough (H : A i ni u = 0%NQ) by (rewrite H; apply NQle_refl).
specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) Hupt) as Haup.
specialize (Haup 0) as H1.
rewrite <- Hni in H1.
rewrite A_additive in H1.
rewrite (A_all_9 (P _)) in H1; [ | easy ].
remember (ni - i - 1) as s eqn:Hs.
assert (H11 : (0 ≤ 1 - 1 // rad ^ s)%NQ). {
  apply NQle_add_le_sub_r; rewrite NQadd_0_r.
  apply NQle_pair; [ pauto | easy | ].
  apply Nat.mul_le_mono_r.
  now apply Nat_pow_ge_1.
}
rewrite NQfrac_add_cond in H1; [ | easy | easy ].
rewrite NQfrac_small in H1. 2: {
  split; [ easy | ].
  apply A_upper_bound_for_dig; intros k Hk.
  replace k with (i + (k - i)) by flia Hk; apply Hu.
}
rewrite (NQfrac_small (_ - _)%NQ) in H1. 2: {
  split; [ easy | now apply NQsub_lt ].
}
destruct (NQlt_le_dec (A i ni u + (1 - 1 // rad ^ s))%NQ 1) as [H2| H2].
-rewrite NQadd_sub_assoc in H2.
 apply NQlt_sub_lt_add_l, NQadd_lt_mono_r in H2.
 rewrite Hs in H2.
 apply A_lt_le_pred in H2.
 now apply NQle_antisymm in H2.
-specialize (A_ge_1_add_all_true_if v i) as Hvr.
 assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
   intros k; rewrite <- Nat.add_assoc; apply Hv.
 }
 specialize (Hvr H Hvt); clear H.
 exfalso.
 destruct Hvr as [Hvr| [Hvr| Hvr]].
 *rewrite A_all_9, <- Hs in Ha1; [ | easy ].
  rewrite NQintg_small in Ha1; [ easy | ].
  split; [ easy | now apply NQsub_lt ].
 *apply NQnle_gt in Haa; apply Haa.
  rewrite (A_all_18 v); [ | easy ].
  rewrite <- Hs, NQadd_sub_assoc.
  apply NQle_add_le_sub_r, NQadd_le_mono_r.
  rewrite NQadd_sub_assoc, NQsub_sub_swap, NQadd_sub in H1.
  apply NQle_add_le_sub_r in H1.
  eapply NQle_trans; [ | apply H1 ].
  replace 2 with (1 + 1) by easy.
  rewrite NQpair_add_l, Nat.pow_1_r.
  apply NQadd_le_mono_l, NQle_add_le_sub_r.
  rewrite NQadd_pair; [ | easy | pauto ].
  rewrite Nat.mul_1_l, Nat.mul_1_r.
  apply NQle_pair; [ apply Nat.neq_mul_0; pauto | easy | ].
  apply Nat.mul_le_mono_r.
  rewrite Hni in Hs; unfold min_n in Hs.
  destruct rad as [| rr]; [ easy | cbn ].
  apply Nat.add_le_mono_l.
  destruct rr; [ flia Hr | cbn ].
  destruct s; [ cbn in Hs; flia Hs | ].
  eapply Nat.le_trans; [ | apply Nat.le_add_r ].
  replace (S (S rr)) with (S (S rr) ^ 1) at 1 by apply Nat.pow_1_r.
  apply Nat.pow_le_mono_r; [ easy | flia ].
 *destruct Hvr as (j & Hbef & Hwhi & Haft).
  rewrite (A_9_8_all_18 j) in Ha1; [ | easy | easy | easy ].
  rewrite <- Hs, NQintg_small in Ha1; [ easy | ].
  split.
 --apply NQle_add_le_sub_l; rewrite NQadd_0_l.
   apply NQle_pair; [ pauto | easy | ].
   apply Nat.mul_le_mono_r.
   destruct (le_dec (i + j + 1) (ni - 1)) as [H3| H3].
  ++rewrite Hni in Hs; unfold min_n in Hs.
    destruct rad as [| rr]; [ easy | cbn ].
    destruct rr; [ flia Hr | cbn ].
    destruct s; [ cbn in Hs; flia Hs | ].
    replace 2 with (2 ^ 1) by easy.
    apply Nat.pow_le_mono; [ easy | easy | flia ].
  ++rewrite Hni in Hs; unfold min_n in Hs.
    destruct rad as [| rr]; [ easy | cbn ].
    destruct s; [ cbn in Hs; flia Hs | ].
    replace 1 with (1 ^ 1) by easy.
    apply Nat.pow_le_mono; [ easy | flia | flia ].
 --apply NQsub_lt.
   now destruct (le_dec (i + j + 1) (ni - 1)).
Qed.

Theorem pre_Hugo_Herbelin_52 {r : radix} : ∀ u v i j,
  (∀ k : nat, u (i + k) ≤ rad - 1)
  → (∀ k : nat, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k : nat, fA_ge_1_ε v i k = true)
  → (∀ k : nat, fA_ge_1_ε (u ⊕ v) i k = true)
  → fA_ge_1_ε (u ⊕ P v) i j = false
  → NQintg (A i (min_n i 0) v) = 1
  → (A i (min_n i j) u + A i (min_n i j) (P v) < 1)%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hvt Huvt Hpi Ha1.
remember (min_n i 0) as ni eqn:Hni.
remember (min_n i j) as nij eqn:Hnij.
move ni before j; move nij before ni.
move Hnij before Hni.
specialize (all_fA_ge_1_ε_P_999 v i Hvt) as Hpr.
rewrite (A_all_9 (P _)); [ | easy ].
rewrite NQadd_sub_assoc.
apply NQlt_sub_lt_add_l, NQadd_lt_mono_r.
apply A_le_pred_lt; [ easy | | ]. {
  rewrite Hnij; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
}
rewrite Nat.sub_diag.
enough (H : A i nij u = 0%NQ) by (rewrite H; apply NQle_refl).
apply A_ge_1_false_iff in Hpi.
rewrite <- Hnij, A_additive in Hpi.
rewrite (A_all_9 (P _)) in Hpi; [ | easy ].
remember (nij - i - 1) as sij eqn:Hsij.
assert (H1s : ∀ s n, (0 ≤ n // 1 - n // rad ^ s)%NQ). {
  intros.
  apply NQle_add_le_sub_l; rewrite NQadd_0_l.
  apply NQle_pair; [ pauto | easy | ].
  rewrite Nat.mul_comm.
  now apply Nat.mul_le_mono_r, Nat_pow_ge_1.
}
rewrite NQfrac_add_cond in Hpi; [ | easy | easy ].
rewrite NQfrac_small in Hpi. 2: {
  split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros p Hp; replace p with (i + (p - i)) by flia Hp; apply Hu.
}
rewrite NQfrac_small in Hpi. 2: {
  split; [ easy | now apply NQsub_lt ].
}
rewrite NQadd_sub_assoc in Hpi.
destruct (NQlt_le_dec (A i nij u + 1 - 1 // rad ^ sij)%NQ 1) as [Hau1| Hau1].
-apply NQlt_sub_lt_add_l, NQadd_lt_mono_r in Hau1.
 rewrite Hsij in Hau1.
 apply A_lt_le_pred in Hau1.
 now apply NQle_antisymm in Hau1.
-specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) Huvt) as Hauv.
 specialize (A_ge_1_add_all_true_if v i) as Hvr.
 assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
   intros k; rewrite <- Nat.add_assoc; apply Hv.
 }
 specialize (Hvr H Hvt); clear H.
 destruct Hvr as [Hvr| [Hvr| Hvr]].
 *exfalso.
  rewrite A_all_9 in Ha1; [ | easy ].
  rewrite NQintg_small in Ha1; [ easy | ].
  split; [ easy | now apply NQsub_lt ].
 *specialize (Hauv j) as H1.
  rewrite <- Hnij, A_additive in H1.
  rewrite (A_all_18 v), <- Hsij in H1; [ | easy ].
  rewrite NQfrac_add_cond in H1; [ | easy | easy ].
  rewrite NQfrac_small in H1. 2: {
    split; [ easy | ].
    apply A_upper_bound_for_dig.
    intros p Hp; replace p with (i + (p - i)) by flia Hp; apply Hu.
  }
  assert (H012r : ∀ n, n ≠ 0 → (0 ≤ 1 - 2 // rad ^ n)%NQ). {
    intros n Hn.
    destruct n; [ easy | ].
    apply NQle_add_le_sub_r; rewrite NQadd_0_r.
    apply NQle_pair; [ pauto | easy | ].
    apply Nat.mul_le_mono_r.
    replace 2 with (2 ^ 1) by easy.
    apply Nat.pow_le_mono; [ easy | easy | flia ].
  }
  rewrite (NQfrac_less_small 1) in H1. 2: {
    split; [ | now apply NQsub_lt ].
    apply NQle_add_le_sub_l.
    replace 2%NQ with (1 + 1)%NQ by easy.
    apply NQadd_le_mono_l.
    apply NQle_pair; [ pauto | easy | ].
    apply Nat.mul_le_mono_r.
    rewrite Hsij, Hnij; apply rad_pow_min_n.
  }
  rewrite NQsub_sub_swap in H1.
  replace (2 - 1)%NQ with 1%NQ in H1 by easy.
  rewrite NQadd_sub_assoc in H1.
  destruct (NQlt_le_dec (A i nij u + 1 - 2 // rad ^ sij)%NQ 1) as [H2| H2].
 --exfalso.
   apply NQlt_sub_lt_add_l, NQadd_lt_mono_r in H2.
   rewrite Hsij in H2.
   apply A_lt_le_pred in H2.
   replace (2 - 1) with 1 in H2 by easy.
   rewrite <- Hsij in H2.
   apply NQle_add_le_sub_r, NQadd_le_mono_r in Hau1.
   apply NQle_antisymm in Hau1; [ clear H2 | easy ].
   move Hau1 at bottom.
   clear H1 Hpi.
   specialize (Hauv (j + 1)) as H1.
   rewrite A_additive in H1.
   rewrite (A_all_18 v) in H1; [ | easy ].
   rewrite min_n_add, Nat.mul_1_r, <- Hnij in H1.
   rewrite <- Nat.sub_add_distr in H1.
   assert (Hinij : i + 1 ≤ nij). {
     rewrite Hnij; unfold min_n.
     destruct rad; [ easy | cbn; flia ].
   }
   rewrite Nat.add_sub_swap in H1; [ | easy ].
   rewrite Nat.sub_add_distr, <- Hsij in H1.
   rewrite <- ApB_A in H1; [ | easy ].
   rewrite Hau1 in H1.
   apply NQnlt_ge in H1; apply H1; clear H1.
   rewrite NQadd_comm, NQadd_assoc.
   rewrite <- NQadd_sub_swap, <- NQadd_sub_assoc, <- NQadd_assoc.
   rewrite Nat.pow_add_r.
   replace (1 // rad ^ sij)%NQ with (1 // rad ^ sij * 1)%NQ at 1
     by apply NQmul_1_r.
   replace 2 with (1 * 2) at 2 by easy.
   rewrite <- NQmul_pair; [ | pauto | pauto ].
   rewrite <- NQmul_sub_distr_l.
   rewrite NQfrac_add_nat_l. 2: {
     apply NQadd_nonneg_nonneg; [ | apply B_ge_0 ].
     apply NQmul_nonneg_cancel_l; [ easy | now apply H012r ].
   }
   specialize (B_upper_bound_for_adds 1 u i j rad) as H1.
   rewrite Nat.mul_1_l, <- Hnij in H1.
   assert (H : 0 < 1 ≤ rad ^ 2). {
     split; [ pauto | now apply Nat_pow_ge_1 ].
   }
   specialize (H1 H); clear H.
   assert (H : ∀ j : nat, j ≥ i → u j ≤ rad - 1). {
     intros p Hp; replace p with (i + (p - i)) by flia Hp; apply Hu.
   }
   specialize (H1 H); clear H.
   rewrite NQfrac_small. 2: {
     split.
     -apply NQadd_nonneg_nonneg; [ | apply B_ge_0 ].
      apply NQmul_nonneg_cancel_l; [ easy | ].
      apply NQle_add_le_sub_r; rewrite NQadd_0_r.
      apply NQle_pair; [ pauto | easy | ].
      apply Nat.mul_le_mono_r.
      replace 2 with (2 ^ 1) by easy.
      now apply Nat.pow_le_mono.
     -eapply NQlt_le_trans; [ apply NQadd_lt_mono_l, H1 | ].
      eapply NQle_trans.
      +apply NQadd_le_mono_r.
       apply NQmul_le_mono_nonneg with (t := 1%NQ); [ easy | | | ].
       *apply NQle_refl.
       *now apply H012r.
       *now apply NQle_sub_l.
      +rewrite NQmul_1_r.
       rewrite NQadd_pair; [ | pauto | pauto ].
       rewrite Nat.mul_1_l, Nat.mul_1_r.
       apply NQle_pair; [ | easy | ].
       *apply Nat.neq_mul_0; pauto.
       *apply Nat.mul_le_mono_r.
        rewrite Nat.add_comm.
        apply Nat.add_le_mul.
        --rewrite Hnij in Hsij; unfold min_n in Hsij.
          replace 1 with (1 ^ sij) by apply Nat.pow_1_l.
          apply Nat.pow_lt_mono_l; [ | easy ].
          intros H; rewrite H in Hsij.
          destruct rad; [ easy | cbn in Hsij; flia Hsij ].
        --replace 1 with (1 ^ S j) by apply Nat.pow_1_l.
          now apply Nat.pow_lt_mono_l.
   }
   eapply NQlt_le_trans; [ apply NQadd_lt_mono_l, H1 | ].
   apply -> NQle_add_le_sub_l.
   apply (NQle_trans _ (2 // rad ^ S (S j) + 1 // rad ^ S j)%NQ).
  ++replace 2 with (1 + 1) at 2 by easy.
    rewrite NQpair_add_l, NQadd_add_swap, (Nat.add_1_r j).
    do 2 apply NQadd_le_mono_r.
    rewrite NQmul_sub_distr_l, NQmul_1_r.
    eapply NQle_trans; [ now apply NQle_sub_l | ].
    apply NQle_pair_mono_l; split; [ apply Nat.neq_0_lt_0; pauto | ].
    apply Nat.pow_le_mono_r; [ easy | ].
    rewrite Hsij, Hnij; unfold min_n.
    destruct rad; [ easy | cbn; flia ].
  ++rewrite <- (NQmul_1_l (1 // rad ^ S j)%NQ).
    rewrite Nat.pow_succ_r'.
    rewrite NQpair_inv_mul; [ | easy | pauto ].
    rewrite <- NQmul_add_distr_r.
    rewrite NQadd_pair; [ | easy | easy ].
    do 2 rewrite Nat.mul_1_r.
    rewrite NQmul_pair; [ | easy | pauto ].
    rewrite Nat.mul_1_r.
    apply NQle_pair; [ apply Nat.neq_mul_0; pauto | easy | ].
    apply Nat.mul_le_mono_r.
    eapply Nat.le_trans; [ apply Nat.add_le_mul; flia Hr | ].
    rewrite Nat.mul_comm.
    apply Nat.mul_le_mono_l; cbn.
    replace 2 with (2 * 1) by easy.
    apply Nat.mul_le_mono; [ easy | ].
    now apply Nat_pow_ge_1.
 --exfalso.
   move H1 at bottom; move Hpi at bottom.
   rewrite NQsub_sub_swap, NQadd_sub in H1, Hpi.
   apply NQnlt_ge in H1; apply H1; clear H1.
   eapply NQle_lt_trans; [ | apply Hpi ].
   apply NQsub_le_mono; [ apply NQle_refl | ].
   apply NQle_pair_mono_r; pauto.
 *destruct Hvr as (k & Hbef & Hwhi & Haft).
  rewrite (A_9_8_all_18 k) in Ha1; [ | easy | easy | easy ].
  rewrite NQintg_small in Ha1; [ easy | ].
  split.
 --apply NQle_add_le_sub_l; rewrite NQadd_0_l.
   apply NQle_pair; [ pauto | easy | ].
   apply Nat.mul_le_mono_r.
   remember (ni - i - 1) as si eqn:Hsi.
   destruct (le_dec (i + k + 1) (ni - 1)) as [H3| H3].
  ++rewrite Hni in Hsi; unfold min_n in Hsi.
    destruct rad as [| rr]; [ easy | cbn ].
    destruct rr; [ flia Hr | cbn ].
    destruct si; [ cbn in Hsi; flia Hsi | ].
    replace 2 with (2 ^ 1) by easy.
    apply Nat.pow_le_mono; [ easy | easy | flia ].
  ++rewrite Hni in Hsi; unfold min_n in Hsi.
    destruct rad as [| rr]; [ easy | cbn ].
    destruct si; [ cbn in Hsi; flia Hsi | ].
    apply Nat_pow_ge_1, Nat.lt_0_succ.
 --apply NQsub_lt.
   now destruct (le_dec (i + k + 1) (ni - 1)).
Qed.

Theorem pre_Hugo_Herbelin_61 {r : radix} : ∀ u v i j,
  (∀ k : nat, u (i + k) ≤ rad - 1)
  → (∀ k : nat, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k : nat, fA_ge_1_ε v i k = true)
  → (∀ k : nat, fA_ge_1_ε (u ⊕ P v) i k = true)
  → NQintg (A i (min_n i j) v) = 1
  → (A i (min_n i j) u + A i (min_n i j) v < 2)%NQ
  → (A i (min_n i 0) u + A i (min_n i 0) (P v) < 1)%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hvt Hupt Haj Haa.
remember (min_n i 0) as ni eqn:Hni.
remember (min_n i j) as nij eqn:Hnij.
move ni before j; move nij before ni.
move Hnij before Hni.
specialize (all_fA_ge_1_ε_P_999 v i Hvt) as Hpr.
rewrite (A_all_9 (P _)); [ | easy ].
rewrite NQadd_sub_assoc.
apply NQlt_sub_lt_add_l, NQadd_lt_mono_r.
apply A_le_pred_lt; [ easy | | ]. {
  rewrite Hni; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
}
rewrite Nat.sub_diag.
enough (H : A i ni u = 0%NQ) by (rewrite H; apply NQle_refl).
specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) Hupt) as Haup.
specialize (Haup 0) as H1.
rewrite <- Hni in H1.
rewrite A_additive in H1.
rewrite (A_all_9 (P _)) in H1; [ | easy ].
remember (ni - i - 1) as si eqn:Hsi.
assert (H11 : ∀ s, (0 ≤ 1 - 1 // rad ^ s)%NQ). {
  intros s.
  apply NQle_add_le_sub_r; rewrite NQadd_0_r.
  apply NQle_pair; [ pauto | easy | ].
  apply Nat.mul_le_mono_r.
  now apply Nat_pow_ge_1.
}
rewrite NQfrac_add_cond in H1; [ | easy | easy ].
rewrite NQfrac_small in H1. 2: {
  split; [ easy | ].
  apply A_upper_bound_for_dig; intros k Hk.
  replace k with (i + (k - i)) by flia Hk; apply Hu.
}
rewrite (NQfrac_small (_ - _)%NQ) in H1. 2: {
  split; [ easy | now apply NQsub_lt ].
}
destruct (NQlt_le_dec (A i ni u + (1 - 1 // rad ^ si))%NQ 1) as [H2| H2].
-rewrite NQadd_sub_assoc in H2.
 apply NQlt_sub_lt_add_l, NQadd_lt_mono_r in H2.
 rewrite Hsi in H2.
 apply A_lt_le_pred in H2.
 now apply NQle_antisymm in H2.
-exfalso.
 specialize (A_ge_1_add_all_true_if v i) as Hvr.
 assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
   intros k; rewrite <- Nat.add_assoc; apply Hv.
 }
 specialize (Hvr H Hvt); clear H.
 destruct Hvr as [Hvr| [Hvr| Hvr]].
 *rewrite A_all_9 in Haj; [ | easy ].
  rewrite NQintg_small in Haj; [ easy | ].
  split; [ easy | now apply NQsub_lt ].
 *apply NQnle_gt in Haa; apply Haa; clear Haa.
  rewrite (A_all_18 v); [ | easy ].
  rewrite NQadd_sub_assoc.
  apply NQle_add_le_sub_r, NQadd_le_mono_r.
  rewrite NQadd_sub_assoc in H2.
  apply NQle_add_le_sub_r, NQadd_le_mono_r in H2.
  rewrite Hnij at 2.
  replace j with (0 + j) by easy.
  rewrite min_n_add, <- Hni.
  rewrite <- ApB_A. 2: {
    rewrite Hni; unfold min_n.
    destruct rad; [ easy | cbn; flia ].
  }
  rewrite NQadd_sub_assoc, NQsub_sub_swap, NQadd_sub in H1.
  apply NQle_add_le_sub_l in H1.
  rewrite Nat.pow_1_r in H1.
  destruct j.
 --rewrite <- Hni in Hnij; subst nij; rewrite <- Hsi.
   rewrite Nat.mul_0_r.
   unfold B; rewrite summation_empty. 2: {
     rewrite Nat.add_0_r; apply Nat.sub_lt; [ | pauto ].
     rewrite Hni; unfold min_n.
     destruct rad; [ easy | cbn; flia ].
   }
   rewrite NQadd_0_r.
   eapply NQle_trans; [ | apply H1 ].
   replace 2 with (1 + 1) by easy.
   rewrite NQpair_add_l.
   apply NQadd_le_mono_r.
   apply NQle_add_le_sub_r.
   rewrite NQadd_pair; [ | easy | pauto ].
   rewrite Nat.mul_1_l, Nat.mul_1_r.
   apply NQle_pair; [ | easy | ]. {
     apply Nat.neq_mul_0; pauto.
   }
   rewrite Nat.add_comm.
   apply Nat.mul_le_mono_r, Nat.add_le_mul; [ easy | ].
   rewrite Hsi, Hni; apply rad_pow_min_n.
 --eapply NQle_trans; [ | apply NQle_add_r, B_ge_0 ].
   eapply NQle_trans; [ | apply H2 ].
   rewrite Hsi.
   apply NQle_pair; [ pauto | pauto | ].
   rewrite Nat.mul_1_r, Hnij.
   replace (S j) with (0 + S j) by easy.
   rewrite min_n_add, <- Hni.
   do 2 rewrite <- Nat.sub_add_distr.
   rewrite Nat.add_sub_swap. 2: {
     rewrite Hni; unfold min_n.
     destruct rad; [ easy | cbn; flia ].
   }
   rewrite Nat.pow_add_r, Nat.mul_comm.
   apply Nat.mul_le_mono_l.
   replace 2 with (2 ^ (1 * 1)) by easy.
   apply Nat.pow_le_mono; [ easy | easy | ].
   apply Nat.mul_le_mono; [ easy | flia ].
 *destruct Hvr as (k & Hbef & Hwhi & Haft).
  rewrite (A_9_8_all_18 k) in Haj; [ | easy | easy | easy ].
  rewrite NQintg_small in Haj; [ easy | ].
  split.
 --apply NQle_add_le_sub_l; rewrite NQadd_0_l.
   apply NQle_pair; [ pauto | easy | ].
   apply Nat.mul_le_mono_r.
   destruct (le_dec (i + k + 1) (nij - 1)) as [H3| H3].
  ++rewrite Hnij; unfold min_n.
    destruct rad as [| rr]; [ easy | cbn ].
    destruct rr; [ flia Hr | cbn ].
    replace 2 with (2 ^ 1) by easy.
    apply Nat.pow_le_mono; [ easy | easy | flia ].
  ++rewrite Hni in Hsi; unfold min_n in Hsi.
    destruct rad as [| rr]; [ easy | cbn ].
    destruct si; [ cbn in Hsi; flia Hsi | ].
    apply Nat_pow_ge_1, Nat.lt_0_succ.
 --apply NQsub_lt.
   now destruct (le_dec (i + k + 1) (nij - 1)).
Qed.

Theorem pre_Hugo_Herbelin_62 {r : radix} : ∀ u v i j k,
  (∀ k : nat, u (i + k) ≤ rad - 1)
  → (∀ k : nat, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k : nat, fA_ge_1_ε v i k = true)
  → fA_ge_1_ε (u ⊕ P v) i k = false
  → fA_ge_1_ε (u ⊕ v) i j = false
  → NQintg (A i (min_n i j) v) = 1
  → (A i (min_n i j) u + A i (min_n i j) v < 2)%NQ
  → (A i (min_n i k) u + A i (min_n i k) (P v) < 1)%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hvt Hk Hj Haj Haa.
remember (min_n i 0) as ni eqn:Hni.
remember (min_n i j) as nij eqn:Hnij.
remember (min_n i k) as nik eqn:Hnik.
move ni before k; move nij before ni; move nik before nij.
move Hnij before Hni; move Hnik before Hnij.
specialize (all_fA_ge_1_ε_P_999 v i Hvt) as Hpr.
rewrite (A_all_9 (P _)); [ | easy ].
rewrite NQadd_sub_assoc.
apply NQlt_sub_lt_add_l, NQadd_lt_mono_r.
apply A_le_pred_lt; [ easy | | ]. {
  rewrite Hnik; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
}
rewrite Nat.sub_diag.
enough (H : A i nik u = 0%NQ) by (rewrite H; apply NQle_refl).
apply A_ge_1_false_iff in Hk.
rewrite <- Hnik, A_additive in Hk.
rewrite NQfrac_add_cond in Hk; [ | easy | easy ].
rewrite NQfrac_small in Hk. 2: {
  split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros p Hp; replace p with (i + (p - i)) by flia Hp; apply Hu.
}
rewrite NQfrac_small in Hk. 2: {
  split; [ easy | ].
  rewrite (A_all_9 (P _)); [ | easy ].
  now apply NQsub_lt.
}
rewrite (A_all_9 (P _)) in Hk; [ | easy ].
remember (nik - i - 1) as sik eqn:Hsik.
rewrite NQadd_sub_assoc in Hk.
destruct (NQlt_le_dec (A i nik u + 1 - 1 // rad ^ sik)%NQ 1) as [H1| H1].
-apply NQlt_sub_lt_add_l, NQadd_lt_mono_r in H1.
 rewrite Hsik in H1.
 apply A_lt_le_pred in H1.
 now apply NQle_antisymm in H1.
-apply A_ge_1_false_iff in Hj.
 rewrite <- Hnij, A_additive in Hj.
 rewrite NQfrac_add_cond in Hj; [ | easy | easy ].
 rewrite NQfrac_small in Hj. 2: {
   split; [ easy | ].
   apply A_upper_bound_for_dig.
   intros p Hp; replace p with (i + (p - i)) by flia Hp; apply Hu.
 }
 rewrite (NQfrac_less_small 1) in Hj. 2: {
   split.
   -specialize (NQintg_of_frac (A i nij v) (A_ge_0 _ _ _)) as H.
    rewrite Haj in H; rewrite H.
    now apply NQle_sub_l.
   -eapply NQle_lt_trans.
    +apply A_upper_bound_for_add.
     intros p; rewrite <- Nat.add_assoc; apply Hv.
    +rewrite NQmul_sub_distr_l, NQmul_1_r.
     now apply NQsub_lt.
 }
 rewrite NQadd_sub_assoc in Hj.
 destruct (NQlt_le_dec (A i nij u + A i nij v - 1)%NQ 1) as [H2| H2].
 +rewrite NQsub_0_r in Hj.
  apply -> NQlt_sub_lt_add_l in Hj.
  rewrite NQadd_sub_assoc in Hj.
  replace (1 + 1)%NQ with 2%NQ in Hj by easy.
  clear H2.
  specialize (A_ge_1_add_all_true_if v i) as Hvr.
  assert (H : ∀ k, v (i + k + 1) ≤ 2 * (rad - 1)). {
    intros p; rewrite <- Nat.add_assoc; apply Hv.
  }
  specialize (Hvr H Hvt); clear H.
  destruct Hvr as [Hvr| [Hvr| Hvr]].
  *rewrite A_all_9 in Haj; [ | easy ].
   rewrite NQintg_small in Haj; [ easy | ].
   split; [ | now apply NQsub_lt ].
   apply NQle_add_le_sub_r.
   rewrite NQadd_0_r.
   apply NQle_pair_mono_l.
   split; [ pauto | now apply Nat_pow_ge_1 ].
  *exfalso.
   apply NQnle_gt in Hj; apply Hj; clear Hj.
   rewrite (A_all_18 v); [ | easy ].
   eapply NQle_trans; [ | now apply NQle_add_l ].
   apply NQsub_le_mono; [ apply NQle_refl | ].
   apply NQle_pair; [ pauto | pauto | ].
   rewrite Nat.mul_1_r.
   eapply (le_trans _ (rad * rad ^ S j)).
  --now apply Nat.mul_le_mono_r.
  --rewrite <- Nat.pow_succ_r'.
    apply Nat.pow_le_mono_r; [ easy | ].
    rewrite Hnij; unfold min_n.
    destruct rad; [ easy | cbn; flia ].
  *destruct Hvr as (m & Hbef & Hwhi & Haft).
   rewrite (A_9_8_all_18 m) in Haj; [ | easy | easy | easy ].
   rewrite NQintg_small in Haj; [ easy | ].
   split.
  --apply NQle_add_le_sub_l; rewrite NQadd_0_l.
    apply NQle_pair; [ pauto | easy | ].
    apply Nat.mul_le_mono_r.
    destruct (le_dec (i + m + 1) (nij - 1)) as [H3| H3].
   ++rewrite Hnij; unfold min_n.
     destruct rad as [| rr]; [ easy | cbn ].
     destruct rr; [ flia Hr | cbn ].
     replace 2 with (2 ^ 1) by easy.
     apply Nat.pow_le_mono; [ easy | easy | flia ].
   ++now apply Nat_pow_ge_1.
  --apply NQsub_lt.
    now destruct (le_dec (i + m + 1) (nij - 1)).
 +now apply NQle_add_le_sub_r, NQnlt_ge in H2.
Qed.

Theorem pre_Hugo_Herbelin_71 {r : radix} : ∀ u v i j,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k, fA_ge_1_ε (u ⊕ v) i k = true)
  → NQintg (A i (min_n i 0) v) ≤ 1
  → NQintg (A i (min_n i j) v) ≤ 1
  → (A i (min_n i 0) u + NQfrac (A i (min_n i 0) v) < 1)%NQ
  → NQintg (A i (min_n i 0) v) = NQintg (A i (min_n i j) v).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Huvt Ha0 Haj Haav.
remember (min_n i 0) as n eqn:Hn.
remember (min_n i j) as nj eqn:Hnj.
move nj before n; move Hnj before Hn.
assert (Hii : NQintg (A i nj (u ⊕ v)) = NQintg (A i n (u ⊕ v))). {
  specialize (all_fA_ge_1_ε_NQintg_A' i (u ⊕ v)) as Hii.
  assert (H : ∀ k, (u ⊕ v) (i + k) ≤ 3 * (rad - 1)). {
    intros p.
    unfold "⊕"; replace 3 with (1 + 2) by easy.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
    apply Nat.add_le_mono; [ apply Hu | apply Hv ].
  }
  specialize (Hii H Huvt j); clear H.
  now rewrite <- Hn, <- Hnj in Hii.
}
rewrite A_additive in Hii.
destruct (Nat.eq_dec (NQintg (A i n v)) 0) as [Hai0| Hai0].
-rewrite Hai0.
 rewrite NQfrac_small in Haav; [ | now apply eq_NQintg_0 in Hai0 ].
 destruct (Nat.eq_dec (NQintg (A i nj v)) 0) as [Haj0| Haj0]; [ easy | ].
 assert (Haj1 : NQintg (A i nj v) = 1) by flia Haj Haj0.
 exfalso.
 rewrite A_additive in Hii.
 symmetry in Hii.
 rewrite NQintg_small in Hii; [ | split ]; [ | | easy ]. 2: {
   replace 0%NQ with (0 + 0)%NQ by easy.
   now apply NQadd_le_mono.
 }
 rewrite NQintg_add in Hii; [ | easy | easy ].
 now rewrite Haj1, <- Nat.add_assoc, Nat.add_comm in Hii.
-assert (H : NQintg (A i n v) = 1) by flia Ha0 Hai0.
 move H before Ha0; clear Ha0 Hai0; rename H into Ha0.
 rewrite Ha0; symmetry.
 destruct (Nat.eq_dec (NQintg (A i nj v)) 1) as [Haj1| Haj1]; [ easy | ].
 assert (Haj0 : NQintg (A i nj v) = 0) by flia Haj Haj1.
 exfalso.
 rewrite Hnj in Haj0.
 replace j with (0 + j) in Haj0 by easy.
 rewrite min_n_add, <- Hn in Haj0.
 rewrite <- ApB_A in Haj0.
 rewrite NQintg_add, Ha0 in Haj0; [ easy | easy | apply B_ge_0 ].
 rewrite Hn; unfold min_n.
 destruct rad; [ easy | cbn; flia ].
Qed.

Theorem pre_Hugo_Herbelin_72_lemma_1 {r : radix} : ∀ u v i j k,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → fA_ge_1_ε v i j = false
  → (∀ j, j < k → fA_ge_1_ε (u ⊕ v) i j = true)
  → NQintg (A i (min_n i k) v) ≤ 1
  → NQintg (A i (min_n i j) v) = 0
  → NQintg (A i (min_n i k) v) = 0.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Hj Hjk Hak Haj0.
apply A_ge_1_false_iff in Hj.
rewrite NQfrac_small in Hj; [ | split ]; [ | easy | ]. 2: {
   now apply eq_NQintg_0 in Haj0.
}
remember (min_n i j) as nj eqn:Hnj.
remember (min_n i k) as nk eqn:Hnk.
assert (Haui : ∀ n, (0 ≤ A i n u < 1)%NQ). {
  intros; split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros p Hp; replace p with (i + (p - i)) by flia Hp.
  apply Hu.
}
assert (Hinik : i + 1 ≤ nk - 1). {
  rewrite Hnk; unfold min_n; destruct rad; [ easy | cbn; flia ].
}
destruct (Nat.eq_dec (NQintg (A i nk v)) 0) as [Hak0| Hak0]; [ easy | ].
exfalso.
assert (Hak1 : NQintg (A i nk v) = 1) by flia Hak Hak0.
clear Hak Hak0; apply eq_NQintg_0 in Haj0; [ | easy ].
move Hj at bottom; clear Haj0.
assert (Havi : (1 ≤ A i nk v < 2)%NQ). {
  split.
  -specialize (NQintg_of_frac (A i nk v) (A_ge_0 _ _ _)) as H.
   rewrite Hak1 in H; rewrite H.
   now apply NQle_sub_l.
  -eapply NQle_lt_trans; [ apply A_upper_bound_for_add | ].
   intros p; rewrite <- Nat.add_assoc; apply Hv.
   rewrite NQmul_sub_distr_l, NQmul_1_r.
   now apply NQsub_lt.
}
destruct (le_dec k j) as [Hlkj| Hljk]. {
  apply NQnle_gt in Hj; apply Hj; clear Hj.
  replace nj with (nk + (nj - nk)). 2: {
    rewrite Nat.add_sub_assoc.
    -now rewrite Nat.add_comm, Nat.add_sub.
    -rewrite Hnj, Hnk; unfold min_n.
     apply Nat.mul_le_mono_l.
     now apply Nat.add_le_mono_r, Nat.add_le_mono_l.
  }
  rewrite <- ApB_A; [ | flia Hinik ].
  apply (NQle_trans _ 1); [ now apply NQle_sub_l | ].
  eapply NQle_trans; [ apply Havi | ].
  apply NQle_add_r, B_ge_0.
}
apply Nat.nle_gt in Hljk.
specialize (Hjk _ Hljk) as Hauvt.
apply A_ge_1_true_iff in Hauvt.
rewrite <- Hnj, A_additive in Hauvt.
rewrite NQfrac_add_cond in Hauvt; [ | easy | easy ].
rewrite NQfrac_small in Hauvt; [ | easy ].
rewrite NQfrac_small in Hauvt; [ | split ]; [ | easy | ]. 2: {
  eapply NQlt_trans; [ apply Hj | now apply NQsub_lt ].
}
destruct (NQlt_le_dec (A i nj u + A i nj v)%NQ 1) as [Hajv| Hajv].
-rewrite NQsub_0_r in Hauvt.
 destruct Havi as (Havi, _).
 apply NQnlt_ge in Havi; apply Havi; clear Havi.
 subst nj nk.
 remember (min_n i j) as nj eqn:Hnj.
 remember (min_n i k) as nk eqn:Hnk.
 move nj before k; move nk before nj.
 move Hnk before Hnj.
 assert (Hinij : i + 1 ≤ nj - 1). {
   rewrite Hnj; unfold min_n; destruct rad; [ easy | cbn; flia ].
 }
 assert (Hum : (A i nj u ≥ 1 // rad ^ (nj - i - 1))%NQ). {
   rewrite A_num_den; unfold den_A.
   apply NQle_pair_mono_r.
   apply Nat.nlt_ge; intros H.
   apply Nat.lt_1_r in H.
   apply NQnlt_ge in Hauvt; apply Hauvt; clear Hauvt.
   now rewrite A_num_den, H, NQadd_0_l.
 }
 apply NQnle_gt; intros Havi.
 destruct (NQlt_le_dec (1 // rad ^ (nj - i - 1))%NQ (A i nj u))
   as [Hum1| Hum1]. {
   apply NQnle_gt in Hajv; apply Hajv; clear Hajv.
   eapply NQle_trans; [ apply Havi | ].
   rewrite Hnk; replace k with (j + (k - j)) by flia Hljk.
   rewrite min_n_add, <- Hnj.
   rewrite NQadd_comm, <- ApB_A; [ | flia Hinij ].
   apply NQadd_le_mono_l.
   eapply NQle_trans.
   -apply (B_upper_bound_for_adds' 2).
    +split; [ pauto | cbn; rewrite Nat.mul_1_r ].
     replace 2 with (2 * 1) by easy.
     now apply Nat.mul_le_mono.
    +flia Hinij.
    +intros p Hp; replace p with (i + (p - i)) by flia Hp.
     apply Hv.
   -apply (NQle_trans _ (2 // rad ^ (nj - i - 1))).
    +rewrite NQmul_sub_distr_l, NQmul_1_r.
     now apply NQle_sub_l.
    +rewrite A_num_den; unfold den_A.
     apply NQle_pair_mono_r.
     apply Nat.nlt_ge; intros H.
     remember (num_A i nj u) as x eqn:Hx.
     destruct x.
     *apply NQnlt_ge in Hauvt; apply Hauvt; clear Hauvt.
      now rewrite A_num_den, <- Hx, NQadd_0_l.
     *destruct x; [ | flia H ].
      apply NQnle_gt in Hum1; apply Hum1; clear Hum1.
      rewrite A_num_den, <- Hx.
      apply NQle_refl.
 }
 apply NQle_antisymm in Hum; [ clear Hum1 | easy ].
 remember (nj - i - 1) as sj eqn:Hsj.
 move Hum at bottom.
 move Hauvt at bottom.
 move Hj at bottom.
 assert (Hsnj : S j ≤ sj). {
   rewrite Hsj, Hnj; unfold min_n.
   destruct rad; [ easy | cbn; flia ].
 }
 assert (Hvm : A i nj v = (1 - 1 // rad ^ S j - 1 // rad ^ sj)%NQ). {
   rewrite <- Hum.
   apply NQadd_move_l, NQle_antisymm; [ | easy ].
   rewrite Hum.
   apply NQlt_add_lt_sub_r in Hj.
   apply -> NQle_add_le_sub_r.
   rewrite NQadd_comm, <- NQadd_assoc.
   apply NQle_add_le_sub_r.
   rewrite A_num_den in Hj; unfold den_A in Hj; rewrite <- Hsj in Hj.
   rewrite A_num_den; unfold den_A; rewrite <- Hsj.
   rewrite NQsub_pair_pos; [ | easy | pauto | ]. 2: {
     now apply Nat.mul_le_mono_l, Nat_pow_ge_1.
   }
   do 2 rewrite Nat.mul_1_l.
   replace sj with ((sj - S j) + S j) at 1 3 by flia Hsnj.
   rewrite Nat.pow_add_r.
   rewrite NQpair_inv_mul; [ | pauto | pauto ].
   replace (1 // rad ^ S j)%NQ with (1 * 1 // rad ^ S j)%NQ at 2
     by apply NQmul_1_l.
   rewrite <- NQmul_add_distr_r.
   rewrite NQpair_inv_mul; [ | pauto | pauto ].
   apply NQmul_le_mono_pos_r; [ easy | ].
   rewrite <- (NQpair_diag (rad ^ (sj - S j))); [ | pauto ].
   rewrite <- NQpair_add_l.
   apply NQle_pair_mono_r.
   apply (NQmul_lt_mono_pos_r (rad ^ sj // 1)%NQ) in Hj. 2: {
     replace 0%NQ with (0 // 1)%NQ by easy.
     apply NQlt_pair; [ easy | easy | ].
     rewrite Nat.mul_0_l, Nat.mul_1_l.
     apply Nat.neq_0_lt_0; pauto.
   }
   rewrite NQmul_add_distr_r in Hj.
   rewrite NQmul_pair_den_num in Hj; [ | pauto ].
   rewrite NQmul_1_l in Hj.
   rewrite <- NQpair_mul_l in Hj.
   rewrite Nat.mul_1_l in Hj.
   rewrite NQpow_pair_l in Hj; [ | easy | easy ].
   rewrite <- NQpair_add_l in Hj.
   apply NQlt_pair in Hj; [ | easy | easy ].
   rewrite Nat.mul_1_r, Nat.mul_1_l in Hj.
   rewrite Nat.sub_1_r.
   now apply Nat.lt_le_pred.
 }
 move Hum at bottom.
 apply NQnlt_ge in Havi; apply Havi; clear Havi.
 rewrite Hnk.
 replace k with (j + (k - j)) by flia Hljk.
 rewrite min_n_add, <- Hnj.
 rewrite <- ApB_A; [ | flia Hinij ].
 rewrite Hvm, <- NQsub_add_distr.
 rewrite <- NQadd_sub_swap.
 apply NQlt_sub_lt_add_r, NQadd_lt_mono_l.
 specialize (B_upper_bound_for_adds' 2 v i nj (rad * (k - j))) as H1.
 rewrite <- Hsj in H1.
 assert (H : 0 < 2 ≤ rad ^ 2). {
   split; [ pauto | cbn; rewrite Nat.mul_1_r ].
   replace 2 with (2 * 1) by easy.
   now apply Nat.mul_le_mono.
 }
 specialize (H1 H); clear H.
 assert (H : i + 1 ≤ nj) by flia Hinij.
 specialize (H1 H); clear H.
 assert (H : ∀ j, j ≥ i → v j ≤ 2 * (rad - 1)). {
   intros p Hp; replace p with (i + (p - i)) by flia Hp.
   apply Hv.
 }
 specialize (H1 H); clear H.
 eapply NQle_lt_trans; [ apply H1 | ].
 eapply NQlt_le_trans; [ | now apply NQle_add_r ].
 rewrite NQmul_sub_distr_l, NQmul_1_r.
 eapply NQlt_le_trans; [ now apply NQsub_lt | ].
 apply NQle_pair; [ pauto | pauto | ].
 rewrite Nat.mul_1_r.
 apply (Nat.le_trans _ (rad * rad ^ S j)).
 +now apply Nat.mul_le_mono_r.
 +rewrite <- Nat.pow_succ_r'.
  apply Nat.pow_le_mono_r; [ easy | ].
  rewrite Hsj, Hnj; unfold min_n.
  destruct rad; [ easy | cbn; flia ].
-apply NQnlt_ge in Hauvt; apply Hauvt; clear Hauvt.
 apply NQlt_sub_lt_add_l.
 apply NQadd_lt_mono; [ apply Haui | apply Hj ].
Qed.

Theorem pre_Hugo_Herbelin_72_lemma_2 {r : radix} : ∀ u v i j k,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ j0 : nat, j0 < j → fA_ge_1_ε v i j0 = true)
  → fA_ge_1_ε v i j = false
  → fA_ge_1_ε (u ⊕ v) i k = false
  → (A i (min_n i k) u + NQfrac (A i (min_n i k) v) < 1)%NQ
  → NQintg (A i (min_n i j) v) = 1
  → NQintg (A i (min_n i k) v) ≤ 1
  → NQintg (A i (min_n i k) v) = 1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hjj Hj Hk Haav Haj Hak.
remember (min_n i j) as nj eqn:Hnj.
remember (min_n i k) as nk eqn:Hnk.
move nj before k; move nk before nj; move Hnk before Hnj.
destruct (Nat.eq_dec (NQintg (A i nk v)) 1) as [Hak0| Hak0]; [ easy | ].
exfalso.
assert (H : NQintg (A i nk v) = 0) by flia Hak Hak0.
clear Hak Hak0; rename H into Hak.
move Hak before Haj.
assert (Havi : (0 ≤ A i nk v < 1)%NQ). {
  split; [ easy | ].
  rewrite (NQintg_frac (A _ _ _)); [ | easy ].
  rewrite Hak, NQadd_0_l.
  apply NQfrac_lt_1.
}
rewrite NQfrac_small in Haav; [ | easy ].
apply A_ge_1_false_iff in Hk.
rewrite <- Hnk in Hk.
rewrite A_additive in Hk.
rewrite NQfrac_add_cond in Hk; [ | easy | easy ].
rewrite NQfrac_small in Hk; [ | split ]; [ | easy | ]. 2: {
  apply A_upper_bound_for_dig.
  intros p Hp; replace p with (i + (p - i)) by flia Hp.
  apply Hu.
}
rewrite NQfrac_small in Hk; [ | easy ].
apply NQnle_gt in Haav.
destruct (NQlt_le_dec (A i nk u + A i nk v)%NQ 1) as [H| ]; [ | easy ].
apply NQnle_gt in Haav; clear H.
rewrite NQsub_0_r in Hk.
apply A_ge_1_false_iff in Hj.
rewrite <- Hnj in Hj.
move Hj before Hk.
rewrite NQfrac_of_intg in Hj; [ | easy ].
rewrite Haj in Hj.
apply -> NQlt_sub_lt_add_l in Hj.
rewrite NQadd_sub_assoc in Hj.
replace (1 + 1)%NQ with 2%NQ in Hj by easy.
destruct (le_dec j k) as [Hljk| Hlkj]. {
  replace nk with (nj + (nk - nj)) in Hak. 2: {
    rewrite Nat.add_sub_assoc.
    -now rewrite Nat.add_comm, Nat.add_sub.
    -rewrite Hnj, Hnk; unfold min_n.
     apply Nat.mul_le_mono_l.
     now apply Nat.add_le_mono_r, Nat.add_le_mono_l.
  }
  assert (Hinij : i + 1 ≤ nj - 1). {
    rewrite Hnj; unfold min_n; destruct rad; [ easy | cbn; flia ].
  }
  rewrite <- ApB_A in Hak; [ | flia Hinij ].
  rewrite NQintg_add in Hak; [ | easy | apply B_ge_0 ].
  now rewrite Haj in Hak.
}
apply Nat.nle_gt in Hlkj.
specialize (Hjj _ Hlkj) as Havt.
apply A_ge_1_true_iff in Havt.
apply NQnlt_ge in Havt; apply Havt; clear Havt.
rewrite <- Hnk, NQfrac_small; [ | easy ].
eapply NQle_lt_trans; [ | apply Hk ].
now apply NQle_add_l.
Qed.

Theorem pre_Hugo_Herbelin_72 {r : radix} : ∀ u v i j k,
  (∀ k : nat, u (i + k) ≤ rad - 1)
  → (∀ k : nat, v (i + k) ≤ 2 * (rad - 1))
  → (∀ j0 : nat, j0 < j → fA_ge_1_ε v i j0 = true)
  → fA_ge_1_ε v i j = false
  → (∀ j : nat, j < k → fA_ge_1_ε (u ⊕ v) i j = true)
  → fA_ge_1_ε (u ⊕ v) i k = false
  → NQintg (A i (min_n i j) v) ≤ 1
  → NQintg (A i (min_n i k) v) ≤ 1
  → (A i (min_n i k) u + NQfrac (A i (min_n i k) v) < 1)%NQ
  → NQintg (A i (min_n i k) v) = NQintg (A i (min_n i j) v).
Proof.
intros *.
intros Hu Hv Hjj Hj Hjk Hk Haj Hak Haav.
remember (min_n i j) as nj eqn:Hnj.
remember (min_n i k) as nk eqn:Hnk.
move nj before k; move nk before nj; move Hnk before Hnj.
destruct (Nat.eq_dec (NQintg (A i nj v)) 0) as [Haj0| Haj0].
-rewrite Haj0; subst nj nk.
 now apply (pre_Hugo_Herbelin_72_lemma_1 u _ _ j).
-assert (H : NQintg (A i nj v) = 1) by flia Haj Haj0.
 rewrite H; subst nj nk.
 now apply (pre_Hugo_Herbelin_72_lemma_2 u _ _ j).
Qed.
