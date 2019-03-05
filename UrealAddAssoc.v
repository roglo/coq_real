(* Reals between 0 and 1; associativity of addition *)

Require Import Utf8 Arith NPeano Psatz PeanoNat.
Require Import Misc Summation Ureal UrealNorm NQ UrealAddAssoc1.
Set Nested Proofs Allowed.

Theorem pred_rad_lt_rad {r : radix} : rad - 1 < rad.
Proof.
specialize radix_ge_2 as H; lia.
Qed.

Definition digit_9 {r : radix} := mkdig _ (rad - 1) pred_rad_lt_rad.
Definition ureal_999 {r : radix} := {| ureal i := digit_9 |}.

Definition ureal_shift {r : radix} k x := {| ureal i := ureal x (k + i) |}.
Arguments ureal_shift _ _ x%F.

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
   apply NQle_pair_mono_l; split; [ pauto | now apply Nat_pow_ge_1 ].
  -apply NQsub_lt.
   replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | pauto | flia ].
}
apply NQsub_le_mono; [ apply NQle_refl | ].
apply NQle_pair_mono_l; split; [ apply Nat.neq_0_lt_0; pauto | ].
apply Nat.pow_le_mono_r; [ easy | ].
unfold min_n.
destruct rad; [ easy | cbn; flia ].
Qed.

Theorem NQintg_A_M {r : radix} : ∀ i n u, NQintg (A i n (M u)) = 0.
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
   -apply NQadd_nonneg_nonneg; [ now subst x | ].
    apply NQle_0_sub.
    apply NQle_pair_mono_l; split; [ pauto | ].
    now apply Nat_pow_ge_1.
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
  apply NQle_pair_mono_l; split; [ pauto | flia ].
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

Theorem B_upper_bound_for_adds' {r : radix} : ∀ m u i n l,
  0 < m ≤ rad ^ 2
  → i + 1 ≤ n
  → (∀ j : nat, j ≥ i → u j ≤ m * (rad - 1))
  → (B i n u l ≤ m // rad ^ (n - i - 1) * (1 - 1 // rad ^ l))%NQ.
Proof.
intros * Hm Hin Hu.
rewrite B_of_A; [ | easy ].
remember (n - i - 1) as s eqn:Hs.
specialize (A_upper_bound_for_adds u (n - 1) (n + l) m) as H1.
replace (n + l - (n - 1) - 1) with l in H1 by flia Hin.
assert (H : ∀ k : nat, u (n - 1 + k + 1) ≤ m * (rad - 1)). {
  intros.
  rewrite Nat.add_shuffle0.
  rewrite Nat.sub_add; [ apply Hu; flia Hin | flia Hin ].
}
specialize (H1 H); clear H.
apply (NQmul_le_mono_pos_r (1 // rad ^ s)%NQ) in H1; [ | easy ].
rewrite NQmul_mul_swap in H1.
now rewrite NQmul_pair_den_num in H1.
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
   apply NQle_pair_mono_l; split; [ pauto | now apply Nat_pow_ge_1 ].
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
   values (u_(i+1), u_(i+2), etc.) will be treated separately. *)
Theorem P_999_start {r : radix} : ∀ u i m,
  (∀ k, u (i + k) ≤ m * (rad - 1))
  → (∀ k, P u (i + k) = rad - 1)
  → if lt_dec rad m then True
     else if eq_nat_dec (u i) (m * (rad - 1)) then True
     else
       let j := u i / rad + 1 in
       let k := carry u i + 1 in
       1 ≤ j < m ∧ 1 ≤ k ≤ m ∧ u i = j * rad - k.
Proof.
intros * Hur Hpu.
specialize radix_ge_2 as Hr.
destruct (zerop m) as [Hm| Hm]. {
  exfalso.
  subst m; rewrite Nat.mul_0_l in Hur.
  specialize (Hpu 0) as H1; rewrite Nat.add_0_r in H1.
  unfold P, d2n, prop_carr in H1; cbn in H1.
  specialize (Hur 0) as H2; rewrite Nat.add_0_r in H2.
  apply Nat.le_0_r in H2.
  rewrite H2, Nat.add_0_l in H1.
  unfold carry, A in H1.
  rewrite all_0_summation_0 in H1.
  -rewrite Nat.mod_0_l in H1; [ flia H1 Hr | easy ].
  -intros k Hk.
   specialize (Hur (k - i)) as H4.
   replace (i + (k - i)) with k in H4 by flia Hk.
   now apply Nat.le_0_r in H4; rewrite H4.
}
apply Nat.neq_0_lt_0 in Hm.
destruct (lt_dec rad m) as [Hrm| Hmr]; [ easy | ].
apply Nat.nlt_ge in Hmr.
destruct (eq_nat_dec (u i) (m * (rad - 1))) as [H1| H1]; [ easy | ].
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
assert (H12 : u i < rad * (m - 1)). {
  specialize (Hur 0) as H7; rewrite Nat.add_0_r in H7.
  assert (H8 : u i < m * (rad - 1)) by flia H1 H7.
  apply Nat.nle_gt.
  intros H12.
  exfalso.
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
  apply (le_trans _ (m * (rad - 1) + (m - 1))).
  -apply Nat.add_le_mono_l; flia H4.
  -rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   rewrite Nat.add_sub_assoc; [ | flia Hm ].
   rewrite Nat.sub_add. 2: {
     replace m with (m * 1) at 1 by flia.
     now apply Nat.mul_le_mono_l.
   }
   rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   rewrite Nat.add_assoc.
   rewrite Nat.add_sub_assoc. 2: {
     replace rad with (rad * 1) at 1 by flia.
     apply Nat.mul_le_mono_l; flia Hm.
   }
   apply (Nat.add_le_mono_r _ _ 1).
   rewrite Nat.sub_add. 2: {
     destruct m; [ easy | ].
     destruct rad; [ easy | cbn; flia ].
   }
   rewrite <- Nat.add_sub_swap. 2: {
     rewrite Nat.add_comm, Nat.mul_comm.
     destruct m; [ flia Hm | cbn; flia ].
   }
   rewrite <- Nat.add_assoc, Nat.add_comm.
   rewrite <- Nat.add_assoc.
   rewrite <- Nat.add_sub_assoc; [ flia | flia Hr ].
}
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
clear -Hmr H4 H12.
apply (lt_le_trans _ (rad * (m - 1) + carry u i + 1)).
+now do 2 apply Nat.add_lt_mono_r.
+rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
 rewrite Nat.mul_comm, <- Nat.add_assoc.
 rewrite <- Nat_sub_sub_distr; [ apply Nat.le_sub_l | ].
 split.
 *apply (le_trans _ m); [ flia H4 | easy ].
 *destruct m; [ easy | cbn; flia ].
Qed.

Theorem P_999_after_mod_is_9 {r : radix} : ∀ u i m,
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
 specialize (carry_upper_bound_for_adds u i 1) as H2.
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
   apply eq_NQintg_0 in Hcu; [ | easy ].
   apply NQnle_gt in Hcu; apply Hcu; clear Hcu.
   rewrite A_split_first.
   -rewrite <- (Nat.add_1_r (i + j)).
    eapply NQle_trans. 2: {
      apply NQle_add_r.
      replace 0%NQ with (0 * 1 // rad)%NQ by easy.
      now apply NQmul_le_mono_pos_r.
    }
    apply NQle_pair; [ easy | easy | ].
    now do 2 rewrite Nat.mul_1_l.
   -unfold min_n.
    destruct rad; [ easy | cbn; flia ].
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

(* special case of P_999_start whem m=2 *)
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
specialize (P_999_start u (i + k) 2) as H1.
assert (H : ∀ n, u (i + k + n) ≤ 2 * (rad - 1)). {
  intros n; rewrite <- Nat.add_assoc; apply Hur.
}
specialize (H1 H); clear H.
assert (H : ∀ n, P u (i + k + n) = rad - 1). {
  intros n; rewrite <- Nat.add_assoc; apply Hpr.
}
specialize (H1 H); clear H.
destruct (lt_dec rad 2) as [H2| H2]; [ flia Hr H2 | clear H2 ].
destruct (eq_nat_dec (u (i + k)) (2 * (rad - 1))) as [H2| H2].
-clear H1.
 destruct (zerop (carry u (i + k))) as [H3| H3].
 +specialize (Hpr k) as H1.
  unfold P, d2n, prop_carr in H1; cbn in H1.
  rewrite H3, H2, Nat.add_0_r in H1.
  replace (2 * (rad - 1)) with (rad + (rad - 2)) in H1 by flia Hr.
  rewrite Nat_mod_add_same_l in H1; [ | easy ].
  rewrite Nat.mod_small in H1; [ flia Hr H1 | flia Hr ].
 +destruct (lt_dec (u (i + k) + 1) rad) as [H4| H4]; [ | easy ].
  rewrite H2 in H4.
  apply Nat.nle_gt in H4.
  exfalso; apply H4; clear H4.
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
  flia Hr.
-destruct H1 as ((H4 & H5) & H6 & H7).
 destruct (zerop (carry u (i + k))) as [H3| H3].
 +rewrite H3 in H7.
  cbn in H7.
  replace (u (i + k) / rad) with 0 in H7 by flia H5.
  now rewrite Nat.mul_1_l in H7.
 +replace (carry u (i + k)) with 1 in H7 by flia H6 H3.
  replace (u (i + k) / rad) with 0 in H7 by flia H5.
  cbn in H7; rewrite Nat.add_0_r in H7.
  destruct (lt_dec (u (i + k) + 1) rad) as [H1| H1]; [ easy | ].
  flia H7 H1.
Qed.

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
Theorem A_all_nth_pred_rad {r : radix} : ∀ u i m n,
  (∀ k : nat, i + k + 1 < n → u (i + k + 1) = m * (rad - 1))
  → A i n u = (m // 1 - m // rad ^ (n - i - 1))%NQ.
Proof.
intros * Hmr.
specialize radix_ge_2 as Hr.
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

Theorem NQintg_A_for_dig {r : radix} : ∀ i n u,
  (∀ k, i + 1 ≤ k ≤ n - 1 → u k ≤ rad - 1)
  → NQintg (A i n u) = 0.
Proof.
intros * Hur.
apply NQintg_small.
split; [ easy | ].
now apply A_upper_bound_for_dig.
Qed.

Theorem B_lt_1 {r : radix} : ∀ i n u,
  (∀ k, u (i + k) ≤ 3 * (rad - 1))
  → i + 1 < n - 1
  → (B i n u 1 < 1)%NQ.
Proof.
intros * Hur Hin.
specialize radix_ge_2 as Hr.
rewrite B_of_A; [ | flia Hin ].
unfold A.
rewrite Nat.add_sub, Nat.sub_add; [ | flia Hin ].
rewrite summation_only_one.
replace (n - (n - 1)) with 1 by flia Hin.
rewrite Nat.pow_1_r.
rewrite NQmul_pair; [ | pauto | pauto ].
rewrite Nat.mul_1_r, <- Nat.pow_succ_r'.
replace (S (n - i - 1)) with (n - i) by flia Hin.
apply NQlt_pair; [ pauto | easy | ].
do 2 rewrite Nat.mul_1_r.
replace n with (i + (n - i)) at 1 by flia Hin.
eapply le_lt_trans; [ apply Hur | ].
remember (n - i) as m eqn:Hm.
destruct m; [ flia Hin Hm | ].
destruct m; [ flia Hin Hm | ].
destruct m; [ flia Hin Hm | ].
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
apply (lt_le_trans _ (3 * rad)).
-apply Nat.sub_lt; [ flia Hr | pauto ].
-apply (le_trans _ (rad * S (S (S m)))).
 +rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_l; flia.
 +apply Nat.lt_le_incl, Nat_mul_lt_pow; [ easy | flia ].
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
apply NQeq_of_eq_nat in H3.
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

Theorem P_le {r : radix} : ∀ u i, P u i ≤ rad - 1.
Proof.
intros.
unfold P, d2n, prop_carr; cbn.
rewrite Nat.sub_1_r.
apply Nat.lt_le_pred.
now apply Nat.mod_upper_bound.
Qed.

Theorem pre_Hugo_Herbelin_91 {r : radix} : ∀ u v i j,
  (∀ k : nat, u (i + k) ≤ rad - 1)
  → (∀ k : nat, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k : nat, fA_ge_1_ε (u ⊕ P v) i k = true)
  → (∀ k : nat, fA_ge_1_ε (u ⊕ v) i k = true)
  → NQintg (A i (min_n i j) v) ≤ 1
  → NQintg (A i (min_n i 0) v) ≤ 1
  → (A i (min_n i 0) u + A i (min_n i 0) (P v) < 1)%NQ
  → (A i (min_n i 0) u + NQfrac (A i (min_n i 0) v) < 1)%NQ
  → NQintg (A i (min_n i 0) v) = NQintg (A i (min_n i j) v).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Haup Hauv Haj Ha0 Haap Haav.
remember (min_n i 0) as ni eqn:Hni.
remember (min_n i j) as nij eqn:Hnij.
move ni before j; move nij before ni; move Hni after Hnij.
assert (Hini : i + 1 ≤ ni - 1). {
  rewrite Hni; unfold min_n; destruct rad; [ easy | cbn; flia ].
}
assert (Hinij : i + 1 ≤ nij - 1). {
  rewrite Hnij; unfold min_n; destruct rad; [ easy | cbn; flia ].
}
specialize (all_fA_ge_1_ε_NQintg_A' i (u ⊕ v)) as H1.
assert (H : ∀ k : nat, (u ⊕ v) (i + k) ≤ 3 * (rad - 1)). {
  intros k.
  unfold "⊕"; replace 3 with (1 + 2) by easy.
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  apply Nat.add_le_mono; [ apply Hu | apply Hv ].
}
specialize (H1 H Hauv j); clear H.
rewrite <- Hni, <- Hnij in H1.
rewrite A_additive, NQintg_add in H1; symmetry in H1; [ | easy | easy ].
rewrite A_additive, NQintg_add in H1; symmetry in H1; [ | easy | easy ].
specialize (all_fA_ge_1_ε_NQintg_A' i (u ⊕ P v)) as H2.
assert (H : ∀ k : nat, (u ⊕ P v) (i + k) ≤ 3 * (rad - 1)). {
  intros k.
  unfold "⊕"; replace 3 with (1 + 2) by easy.
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  apply Nat.add_le_mono; [ apply Hu | ].
  eapply Nat.le_trans; [ apply P_le | flia Hr ].
}
specialize (H2 H Haup j); clear H.
rewrite <- Hni, <- Hnij in H2.
rewrite A_additive, NQintg_add in H2; symmetry in H2; [ | easy | easy ].
rewrite A_additive, NQintg_add in H2; symmetry in H2; [ | easy | easy ].
assert (Haui : ∀ n, (0 ≤ A i n u < 1)%NQ). {
  intros; split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros k Hk; replace k with (i + (k - i)) by flia Hk.
  apply Hu.
}
assert (Hapi : ∀ n, (0 ≤ A i n (P v) < 1)%NQ). {
  intros; split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros; apply P_le.
}
rewrite (NQintg_small (A _ _ u)) in H1; [ | easy ].
rewrite (NQintg_small (A _ _ u)) in H1; [ | easy ].
rewrite (NQintg_small (A _ _ u)) in H2; [ | easy ].
rewrite (NQintg_small (A _ _ u)) in H2; [ | easy ].
rewrite (NQintg_small (A _ _ (P _))) in H2; [ | easy ].
rewrite (NQintg_small (A _ _ (P _))) in H2; [ | easy ].
do 2 rewrite Nat.add_0_l in H1, H2.
do 2 rewrite NQintg_add_frac in H1, H2.
rewrite (NQfrac_small (A _ _ u)) in H1; [ | easy ].
rewrite (NQfrac_small (A _ _ u)) in H1; [ | easy ].
rewrite (NQfrac_small (A _ _ u)) in H2; [ | easy ].
rewrite (NQfrac_small (A _ _ u)) in H2; [ | easy ].
rewrite (NQfrac_small (A _ _ (P v))) in H2; [ | easy ].
rewrite (NQfrac_small (A _ _ (P v))) in H2; [ | easy ].
destruct (NQlt_le_dec (A i nij u + NQfrac (A i nij v))%NQ 1) as [H3| H3].
-destruct (NQlt_le_dec (A i ni u + NQfrac (A i ni v))%NQ 1) as [H4| H4].
 +now apply Nat.add_cancel_r in H1.
 +now apply NQnlt_ge in H4.
-destruct (NQlt_le_dec (A i ni u + NQfrac (A i ni v))%NQ 1) as [H4| H4].
 +rewrite Nat.add_0_r in H1.
  assert (H5 : NQintg (A i nij v) = 0) by flia Haj Ha0 H1.
  assert (H6 : NQintg (A i ni v) = 1) by flia Haj Ha0 H1.
  rewrite NQfrac_small in H3; [ | split ]; [ | easy | ]. 2: {
    now apply eq_NQintg_0.
  }
  destruct (NQlt_le_dec (A i ni u + A i ni (P v))%NQ 1) as [H9| H9].
  *destruct (NQlt_le_dec (A i nij u + A i nij (P v))%NQ 1) as [H10| H10].
  --rewrite Hnij in H5.
    replace j with (0 + j) in H5 by easy.
    rewrite min_n_add, <- Hni in H5.
    rewrite <- ApB_A in H5; [ | flia Hini ].
    rewrite NQintg_add in H5; [ | easy | apply B_ge_0 ].
    now rewrite H6 in H5.
  --easy.
  *now apply NQnlt_ge in H9.
 +now apply Nat.add_cancel_r in H1.
Qed.

Theorem pre_Hugo_Herbelin_92 {r : radix} : ∀ u v i j k,
  (∀ k : nat, u (i + k) ≤ rad - 1)
  → (∀ k : nat, v (i + k) ≤ 2 * (rad - 1))
  → (∀ k : nat, fA_ge_1_ε (u ⊕ P v) i k = true)
  → (∀ j0 : nat, j0 < j → fA_ge_1_ε v i j0 = true)
  → fA_ge_1_ε v i j = false
  → (∀ j : nat, j < k → fA_ge_1_ε (u ⊕ v) i j = true)
  → fA_ge_1_ε (u ⊕ v) i k = false
  → NQintg (A i (min_n i j) v) ≤ 1
  → NQintg (A i (min_n i k) v) ≤ 1
  → (A i (min_n i k) u + NQfrac (A i (min_n i k) v) < 1)%NQ
  → (A i (min_n i 0) u + A i (min_n i 0) (P v) < 1)%NQ
  → NQintg (A i (min_n i k) v) = NQintg (A i (min_n i j) v).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hv Haup Hjj Hj Hjk Hk Haj Hak Haav Haap.
remember (min_n i 0) as ni eqn:Hni.
remember (min_n i j) as nj eqn:Hnj.
remember (min_n i k) as nk eqn:Hnk.
move ni before k; move nj before ni; move nk before nj.
move Hni after Hnj; move Hnk before Hnj.
(**)
assert (Haui : ∀ n, (0 ≤ A i n u < 1)%NQ). {
  intros; split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros p Hp; replace p with (i + (p - i)) by flia Hp.
  apply Hu.
}
assert (Hapi : ∀ n, (0 ≤ A i n (P v) < 1)%NQ). {
  intros; split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros; apply P_le.
}
assert (Hinij : i + 1 ≤ nj - 1). {
  rewrite Hnj; unfold min_n; destruct rad; [ easy | cbn; flia ].
}
assert (Hinik : i + 1 ≤ nk - 1). {
  rewrite Hnk; unfold min_n; destruct rad; [ easy | cbn; flia ].
}
apply A_ge_1_false_iff in Hj.
rewrite <- Hnj in Hj.
apply A_ge_1_false_iff in Hk.
rewrite <- Hnk, A_additive in Hk.
move Hj at bottom; move Hk at bottom.
destruct (Nat.eq_dec (NQintg (A i nj v)) 0) as [Haj0| Haj0].
-clear Haj; rewrite Haj0.
 destruct (Nat.eq_dec (NQintg (A i nk v)) 0) as [Hak0| Hak0]; [ easy | ].
 exfalso.
 assert (Hak1 : NQintg (A i nk v) = 1) by flia Hak Hak0.
 clear Hak Hak0; apply eq_NQintg_0 in Haj0; [ | easy ].
 rewrite NQfrac_small in Hj; [ | easy ].
 move Hj at bottom; clear Haj0.
 rewrite NQfrac_add_cond in Hk; [ | easy | easy ].
 rewrite NQfrac_small in Hk; [ | easy ].
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
 move Havi before Hapi.
 rewrite NQfrac_less_small in Haav; [ | easy ].
 rewrite NQfrac_less_small in Hk; [ | easy ].
 rewrite NQadd_sub_assoc in Haav, Hk.
 apply NQnle_gt in Haav.
 destruct (NQlt_le_dec (A i nk u + A i nk v - 1)%NQ 1) as [H| ]; [ | easy ].
 rewrite NQsub_0_r in Hk; clear H Haav Hak1.
 apply -> NQlt_sub_lt_add_r in Hk.
 rewrite <- NQadd_sub_swap in Hk.
 replace (1 + 1)%NQ with 2%NQ in Hk by easy.
 specialize (Hjk _ Hljk) as Hauvt.
 apply A_ge_1_true_iff in Hauvt.
 rewrite <- Hnj, A_additive in Hauvt.
 rewrite NQfrac_add_cond in Hauvt; [ | easy | easy ].
 specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) Haup 0) as Hup.
 specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) Haup j) as Hupj.
 specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) Haup k) as Hupk.
 rewrite <- Hni in Hup; rewrite <- Hnj in Hupj; rewrite <- Hnk in Hupk.
 rewrite A_additive in Hup, Hupj, Hupk.
 rewrite Nat.pow_1_r in Hup.
 rewrite NQfrac_add_cond in Hup; [ | easy | easy ].
 rewrite NQfrac_add_cond in Hupj; [ | easy | easy ].
 rewrite NQfrac_add_cond in Hupk; [ | easy | easy ].
 rewrite NQfrac_small in Hauvt; [ | easy ].
 rewrite NQfrac_small in Hup; [ | easy ].
 rewrite NQfrac_small in Hup; [ | easy ].
 rewrite NQfrac_small in Hupj; [ | easy ].
 rewrite NQfrac_small in Hupj; [ | easy ].
 rewrite NQfrac_small in Hupk; [ | easy ].
 rewrite NQfrac_small in Hupk; [ | easy ].
 rewrite NQfrac_small in Hauvt; [ | split ]; [ | easy | ]. 2: {
   eapply NQlt_trans; [ apply Hj | now apply NQsub_lt ].
 }
 apply NQnle_gt in Haap.
 destruct (NQlt_le_dec (A i ni u + A i ni (P v))%NQ 1) as [Hap| Hap]; [ | easy ].
 rewrite NQsub_0_r in Hup; clear Haap.
 destruct (NQlt_le_dec (A i nj u + A i nj (P v))%NQ 1) as [Hajp| Hajp].
 +rewrite NQsub_0_r in Hupj.
  destruct (NQlt_le_dec (A i nk u + A i nk (P v))%NQ 1) as [Hakp| Hakp].
  *rewrite NQsub_0_r in Hupk.
   specialize (A_ge_1_add_all_true_if (u ⊕ P v) i) as Hupv.
   assert (H : ∀ k, (u ⊕ P v) (i + k + 1) ≤ 2 * (rad - 1)). {
     intros p; unfold "⊕".
     replace 2 with (1 + 1) by easy.
     rewrite Nat.mul_add_distr_r, Nat.mul_1_l, <- Nat.add_assoc.
     apply Nat.add_le_mono; [ apply Hu | apply P_le ].
   }
   specialize (Hupv H Haup); clear H.
   destruct Hupv as [Hupv| [Hupv| Hupv]].
  --clear Hap Hup Hajp Hupj Hakp Hupk.
    destruct (NQlt_le_dec (A i nj u + A i nj v)%NQ 1) as [Hajv| Hajv].
   ++rewrite NQsub_0_r in Hauvt.
     assert (Hum : (A i nj u ≥ 1 // rad ^ (nj - i - 1))%NQ). {
       rewrite A_num_den; unfold den_A.
       apply NQle_pair_mono_r.
       apply Nat.nlt_ge; intros H.
       apply Nat.lt_1_r in H.
       apply NQnlt_ge in Hauvt; apply Hauvt; clear Hauvt.
       now rewrite A_num_den, H, NQadd_0_l.
     }
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
     (* d'après Hajv, A i nj v ≤ 0,999...9998 ; donc pour que, d'après
        Havi, A i nk v ≥ 1, faut que la retenue soit au moins 2, ce qui
        n'est pas possible ; enfin, je crois *)
     destruct Havi as (Havi1, Havi2).
     move Hajv at bottom; move Havi1 at bottom.
     rewrite Hnk in Havi1.
     replace k with (j + (k - j)) in Havi1 by flia Hljk.
     rewrite min_n_add, <- Hnj in Havi1.
     rewrite <- ApB_A in Havi1; [ | flia Hinij ].
     specialize (B_upper_bound_for_adds' 2 v i nj) as Hb.
     specialize (Hb (rad * (k - j))).
...
     apply NQnlt_ge in Havi1; apply Havi1; clear Havi1.
     rewrite Hnk; replace k with (j + (k - j)) by flia Hljk.
     rewrite min_n_add, <- Hnj.
     rewrite <- ApB_A; [ | flia Hinij ].
     apply (NQadd_lt_mono_l (A i nj u)).
     rewrite NQadd_assoc.
     eapply (NQlt_le_trans _ (1 + B i nj v (rad * (k - j)))%NQ).
    **now apply NQadd_lt_mono_r.
    **rewrite NQadd_comm; apply NQadd_le_mono_r.
      eapply NQle_trans.
    ---apply (B_upper_bound_for_adds' 2).
     +++split; [ pauto | cbn; rewrite Nat.mul_1_r ].
        replace 2 with (2 * 1) by easy.
        now apply Nat.mul_le_mono.
     +++flia Hinij.
     +++intros p Hp; replace p with (i + (p - i)) by flia Hp.
        apply Hv.
    ---idtac.
(* ah merde, ça marche pas *)
...
specialize (proj1 (frac_ge_if_all_fA_ge_1_ε _ _) Haup) as H2.
specialize (H2 k) as H1k.
specialize (H2 j) as H1j.
rewrite <- Hnik in H1k.
rewrite <- Hnij in H1j.
rewrite A_additive in H1k, H1j.
clear H2.
...
specialize (all_fA_ge_1_ε_NQintg_A' i (u ⊕ P v)) as H2.
assert (H : ∀ k : nat, (u ⊕ P v) (i + k) ≤ 3 * (rad - 1)). {
  intros p.
  unfold "⊕"; replace 3 with (1 + 2) by easy.
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  apply Nat.add_le_mono; [ apply Hu | ].
  eapply Nat.le_trans; [ apply P_le | flia Hr ].
}
specialize (H2 H Haup); clear H.
rewrite <- Hni in H2.
specialize (H2 k) as H1k.
specialize (H2 j) as H1j.
rewrite <- H1j in H1k; clear H1j.
rewrite <- Hnik, <- Hnij in H1k.
do 2 rewrite A_additive in H1k.
...
(*
specialize (A_ge_1_add_all_true_if (u ⊕ P v) i) as Hup.
assert (H : ∀ k, (u ⊕ P v) (i + k + 1) ≤ 2 * (rad - 1)). {
  intros p; unfold "⊕".
  replace 2 with (1 + 1) by easy.
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l, <- Nat.add_assoc.
  apply Nat.add_le_mono; [ apply Hu | apply P_le ].
}
specialize (Hup H Haup); clear H.
destruct Hup as [Hup| [Hup| Hup]].
-idtac.
...
*)
assert (Hinij : i + 1 ≤ nij - 1). {
  rewrite Hnij; unfold min_n; destruct rad; [ easy | cbn; flia ].
}
assert (Hinik : i + 1 ≤ nik - 1). {
  rewrite Hnik; unfold min_n; destruct rad; [ easy | cbn; flia ].
}
specialize (all_fA_ge_1_ε_NQintg_A' i (u ⊕ P v)) as H2.
assert (H : ∀ k : nat, (u ⊕ P v) (i + k) ≤ 3 * (rad - 1)). {
  intros p.
  unfold "⊕"; replace 3 with (1 + 2) by easy.
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  apply Nat.add_le_mono; [ apply Hu | ].
  eapply Nat.le_trans; [ apply P_le | flia Hr ].
}
specialize (H2 H Haup); clear H.
rewrite <- Hni in H2.
specialize (H2 j) as H3; rewrite <- Hnij in H3.
specialize (H2 k) as H4; rewrite <- Hnik in H4.
rewrite <- H3 in H4.
rewrite A_additive, NQintg_add in H4; symmetry in H4; [ | easy | easy ].
rewrite A_additive, NQintg_add in H4; symmetry in H4; [ | easy | easy ].
assert (Haui : ∀ n, (0 ≤ A i n u < 1)%NQ). {
  intros; split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros p Hp; replace p with (i + (p - i)) by flia Hp.
  apply Hu.
}
assert (Hapi : ∀ n, (0 ≤ A i n (P v) < 1)%NQ). {
  intros; split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros; apply P_le.
}
rewrite (NQintg_small (A _ _ u)) in H4; [ | easy ].
rewrite (NQintg_small (A _ _ u)) in H4; [ | easy ].
do 2 rewrite Nat.add_0_l in H4.
rewrite (NQintg_small (A _ _ (P _))) in H4; [ | easy ].
rewrite (NQintg_small (A _ _ (P _))) in H4; [ | easy ].
do 2 rewrite Nat.add_0_l in H4.
do 2 rewrite NQintg_add_frac in H4.
rewrite (NQfrac_small (A _ _ u)) in H4; [ | easy ].
rewrite (NQfrac_small (A _ _ u)) in H4; [ | easy ].
rewrite (NQfrac_small (A _ _ (P v))) in H4; [ | easy ].
rewrite (NQfrac_small (A _ _ (P v))) in H4; [ | easy ].
(*
clear H2 H3.
*)
destruct (NQlt_le_dec (A i nik u + A i nik (P v))%NQ 1) as [Hakp| Hakp].
-destruct (NQlt_le_dec (A i nij u + A i nij (P v))%NQ 1) as [Hajp| Hajp].
 +clear H4.
(**)
  destruct (Nat.eq_dec (NQintg (A i nij v)) 0) as [Haj0| Haj0]. {
    rewrite Haj0.
    destruct (Nat.eq_dec (NQintg (A i nik v)) 0) as [Hak0| Hak0]; [ easy | ].
    exfalso.
    assert (Hak1 : NQintg (A i nik v) = 1) by flia Hak Hak0.
    clear Haj Hak Hak0.
    destruct (lt_dec j k) as [Hljk| Hgjk].
    -replace nik with (nij + (nik - nij)) in Hak1. 2: {
       rewrite Nat.add_sub_assoc.
       -now rewrite Nat.add_comm, Nat.add_sub.
       -rewrite Hnij, Hnik; unfold min_n.
        apply Nat.mul_le_mono_l.
        apply Nat.add_le_mono_r, Nat.add_le_mono_l.
        now apply Nat.lt_le_incl in Hljk.
     }
     rewrite <- ApB_A in Hak1; [ | flia Hinij ].
     apply A_ge_1_false_iff in Hk.
     rewrite <- Hnik, A_additive in Hk.
     apply A_ge_1_false_iff in Hj.
     rewrite <- Hnij in Hj.
specialize (Hjk _ Hljk) as H1.
apply A_ge_1_true_iff in H1.
rewrite <- Hnij, A_additive in H1.
rewrite NQfrac_add_cond in H1.
move Hj at bottom.
destruct (NQlt_le_dec (NQfrac (A i nij u) + NQfrac (A i nij v))%NQ 1)
  as [H4| H4].
rewrite NQsub_0_r in H1.
Check NQintg_A_slow_incr.
...
    rewrite NQfrac_add_cond in Hk; [ | easy | easy ].
    rewrite NQfrac_small in Hk; [ | easy ].
    rewrite NQfrac_less_small in Hk. 2: {
      split.
      -specialize (NQintg_of_frac (A i nik v) (A_ge_0 _ _ _)) as H.
       rewrite Hak1 in H; rewrite H.
       now apply NQle_sub_l.
      -eapply NQle_lt_trans; [ apply A_upper_bound_for_add | ].
       intros p; rewrite <- Nat.add_assoc; apply Hv.
       rewrite NQmul_sub_distr_l, NQmul_1_r.
       now apply NQsub_lt.
    }
    rewrite NQadd_sub_assoc in Hk.
    destruct (NQlt_le_dec (A i nik u + A i nik v - 1)%NQ 1) as [H1| H1].
    -rewrite NQsub_0_r in Hk.
...
  move Haap before Hakp.
  destruct (NQlt_le_dec (A i nik u + NQfrac (A i nik v))%NQ 1) as [H7| H7].
  *rewrite NQsub_0_r in Hk.
...
   destruct (lt_dec j k) as [Hljk| Hgjk].
  --specialize (Hjk _ Hljk) as H1.
    apply A_ge_1_true_iff in H1.
    rewrite <- Hnij in H1.
...
  *now apply NQnle_gt in Haav.
 +easy.
-destruct (NQlt_le_dec (A i nij u + A i nij (P v))%NQ 1) as [Hajp| Hajp].
 +easy.
...
rewrite (NQintg_small (A _ _ u)) in H1; [ | easy ].
rewrite (NQintg_small (A _ _ u)) in H1; [ | easy ].
rewrite (NQintg_small (A _ _ u)) in H2; [ | easy ].
rewrite (NQintg_small (A _ _ u)) in H2; [ | easy ].
rewrite (NQintg_small (A _ _ (P _))) in H2; [ | easy ].
rewrite (NQintg_small (A _ _ (P _))) in H2; [ | easy ].
do 2 rewrite Nat.add_0_l in H1, H2.
do 2 rewrite NQintg_add_frac in H1, H2.
rewrite (NQfrac_small (A _ _ u)) in H1; [ | easy ].
rewrite (NQfrac_small (A _ _ u)) in H1; [ | easy ].
rewrite (NQfrac_small (A _ _ u)) in H2; [ | easy ].
rewrite (NQfrac_small (A _ _ u)) in H2; [ | easy ].
rewrite (NQfrac_small (A _ _ (P v))) in H2; [ | easy ].
rewrite (NQfrac_small (A _ _ (P v))) in H2; [ | easy ].
destruct (NQlt_le_dec (A i nij u + NQfrac (A i nij v))%NQ 1) as [H3| H3].
-destruct (NQlt_le_dec (A i ni u + NQfrac (A i ni v))%NQ 1) as [H4| H4].
 +now apply Nat.add_cancel_r in H1.
 +now apply NQnlt_ge in H4.
-destruct (NQlt_le_dec (A i ni u + NQfrac (A i ni v))%NQ 1) as [H4| H4].
 +rewrite Nat.add_0_r in H1.
  assert (H5 : NQintg (A i nij v) = 0) by flia Haj Ha0 H1.
  assert (H6 : NQintg (A i ni v) = 1) by flia Haj Ha0 H1.
  rewrite NQfrac_small in H3; [ | split ]; [ | easy | ]. 2: {
    now apply eq_NQintg_0.
  }
  destruct (NQlt_le_dec (A i ni u + A i ni (P v))%NQ 1) as [H9| H9].
  *destruct (NQlt_le_dec (A i nij u + A i nij (P v))%NQ 1) as [H10| H10].
  --rewrite Hnij in H5.
    replace j with (0 + j) in H5 by easy.
    rewrite min_n_add, <- Hni in H5.
    rewrite <- ApB_A in H5; [ | flia Hini ].
    rewrite NQintg_add in H5; [ | easy | apply B_ge_0 ].
    now rewrite H6 in H5.
  --easy.
  *now apply NQnlt_ge in H9.
 +now apply Nat.add_cancel_r in H1.
...

Theorem pre_Hugo_Herbelin {r : radix} : ∀ u v i,
  (∀ k, u (i + k) ≤ rad - 1)
  → (∀ k, v (i + k) ≤ 2 * (rad - 1))
  → carry (u ⊕ v) i mod rad = (carry (u ⊕ P v) i + carry v i) mod rad.
Proof.
intros * Hu Hv.
specialize radix_ge_2 as Hr.
symmetry; rewrite Nat.add_comm; symmetry.
unfold carry.
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
remember (min_n i kv) as nv eqn:Hnv.
remember (min_n i kup) as nup eqn:Hnup.
remember (min_n i kuv) as nuv eqn:Hnuv.
move nuv before kuv; move nup before kuv; move nv before kuv.
do 2 rewrite A_additive.
rewrite NQintg_add; [ symmetry | easy | easy ].
rewrite NQintg_add; [ symmetry | easy | easy ].
do 2 rewrite Nat.add_assoc.
remember (NQintg (A i nv v) + NQintg (A i nup u)) as x eqn:Hx.
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
do 2 rewrite NQintg_add_frac.
rewrite (NQfrac_small (A i nup u)). 2: {
  split; [ easy | ].
  apply A_upper_bound_for_dig.
  intros k Hk; replace k with (i + (k - i)) by flia Hk; apply Hu.
}
rewrite (NQfrac_small (A i nuv u)). 2: {
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
-rewrite Hnv, Hnuv at 1.
 rewrite all_fA_ge_1_ε_NQintg_A'; [ symmetry | easy | easy ].
 rewrite all_fA_ge_1_ε_NQintg_A'; [ symmetry | easy | easy ].
 rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
 rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
 f_equal; f_equal; f_equal.
 subst kv.
 remember (NQintg (A i nuv v)) as m eqn:Hm.
 symmetry in Hm.
 destruct m.
 +clear H2.
  rewrite NQfrac_small. 2: {
    split; [ easy | ].
    now apply eq_NQintg_0 in Hm.
  }
  destruct (NQlt_le_dec (A i nup u + A i nup (P v)) 1) as [H4| H4].
  *destruct (NQlt_le_dec (A i nuv u + A i nuv v) 1) as [H5| H5]; [ easy | ].
   exfalso.
   apply NQnlt_ge in H5; apply H5; clear H5.
   subst nv nup nuv.
   now apply (pre_Hugo_Herbelin_1 u v i kup kuv).
  *destruct (NQlt_le_dec (A i nuv u + A i nuv v) 1) as [H5| H5]; [ | easy ].
   exfalso.
   apply NQnlt_ge in H4; apply H4; clear H4.
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
    enough (H : A i nup u = 0%NQ). {
      rewrite H, NQadd_0_l.
      rewrite A_all_9; [ | intros k Hk; apply H2 ].
      now apply NQsub_lt.
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
  rewrite NQfrac_less_small. 2: {
    split.
    -specialize (NQintg_of_frac (A i nuv v) (A_ge_0 _ _ _)) as H2.
     rewrite Hm in H2; rewrite H2.
     now apply NQle_sub_l.
    -eapply NQle_lt_trans; [ apply A_upper_bound_for_add | ].
     intros k; rewrite <- Nat.add_assoc; apply Hv.
     rewrite NQmul_sub_distr_l, NQmul_1_r.
     now apply NQsub_lt.
  }
  rewrite NQadd_sub_assoc.
  destruct (NQlt_le_dec (A i nup u + A i nup (P v))%NQ 1) as [H4| H4].
  *destruct (NQlt_le_dec (A i nuv u + A i nuv v - 1)%NQ 1)
      as [H5| H5]; [ easy | exfalso ].
   apply NQnlt_ge in H5; apply H5; clear H5.
   apply NQlt_sub_lt_add_r; replace (1 + 1)%NQ with 2%NQ by easy.
   specialize (all_fA_ge_1_ε_P_999 v i H3) as Hap.
   rewrite (A_all_9 (P v)) in H4; [ | easy ].
   rewrite NQadd_comm, <- NQadd_sub_swap in H4.
   apply NQlt_sub_lt_add_r, NQadd_lt_mono_l in H4.
   apply A_lt_le_pred in H4.
   apply NQle_antisymm in H4; [ | easy ].
   symmetry in H4; rewrite Nat.sub_diag in H4.
   rewrite Hnup in H4 at 1.
   replace kup with (0 + kup) in H4 by easy.
   rewrite min_n_add, <- Hnv in H4.
   rewrite <- ApB_A in H4. 2: {
     rewrite Hnv; unfold min_n.
     destruct rad; [ easy | cbn; flia ].
   }
   apply NQeq_add_0 in H4; [ | easy | apply B_ge_0 ].
   clear H1; destruct H4 as (H1, H4).
   destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [H6| H6].
  --subst kuv; rewrite <- Hnv in Hnuv; subst nuv.
    rewrite H1, NQadd_0_l.
    eapply NQle_lt_trans.
   ++apply A_upper_bound_for_add.
     intros k; rewrite <- Nat.add_assoc; apply Hv.
   ++rewrite NQmul_sub_distr_l, NQmul_1_r.
     now apply NQsub_lt.
  --destruct H6 as (j & Hjj & Hj); subst kuv; move j before i.
    destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [H2| H2].
   ++subst kup; rewrite <- Hnv in Hnup; subst nup nv nuv.
     now apply pre_Hugo_Herbelin_41.
   ++destruct H2 as (k & Hjk & Hk); subst kup; move k before j.
     subst nv nup nuv.
     now apply (pre_Hugo_Herbelin_42 _ _ _ _ k).
  *destruct (NQlt_le_dec (A i nuv u + A i nuv v - 1)%NQ 1)
      as [H5| H5]; [ exfalso | easy ].
   apply NQnlt_ge in H4; apply H4; clear H4.
   apply NQlt_sub_lt_add_r in H5.
   replace (1 + 1)%NQ with 2%NQ in H5 by easy.
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
 destruct (NQlt_le_dec (A i nuv u + NQfrac (A i nuv v))%NQ 1) as [Huv| Huv].
 +rewrite Nat.add_0_r.
  rewrite (Nat.mod_small (NQintg (A i nuv v))). 2: {
    eapply Nat.le_lt_trans; [ apply H2 | easy ].
  }
  destruct (NQlt_le_dec (A i nup u + A i nup (P v))%NQ 1) as [Hup| Hup].
  *rewrite Nat.add_0_r.
   rewrite Nat.mod_small. 2: {
     eapply Nat.le_lt_trans; [ apply H1 | easy ].
   }
   destruct (LPO_fst (fA_ge_1_ε (u ⊕ P v) i)) as [Haup| Haup].
  --subst kup.
    destruct (LPO_fst (fA_ge_1_ε (u ⊕ v) i)) as [Hauv| Hauv].
   ++subst kuv; rewrite <- Hnup in Hnuv; subst nuv nv nup.
     now apply (pre_Hugo_Herbelin_91 u).
   ++destruct Hauv as (k & Hjk & Hk); subst kuv.
     move j before i; move k before j.
     subst nv nup nuv; clear Hr.
...
     now apply (pre_Hugo_Herbelin_92 u).
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
