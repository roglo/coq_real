Require Import Utf8 Arith NPeano Psatz.
Require Import Misc Summation.

Notation "a ^ b" := (Nat.pow a b).

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
do 2 rewrite <- Nat.sub_add_distr.
f_equal.
apply Nat.add_comm.
Qed.

Theorem Nat_mul_lt_pow : ∀ a b, a ≥ 2 → b ≥ 3 → a * b < a ^ b.
Proof.
intros a b Ha2 Hb3.
induction b; [ easy | ].
 apply Nat.succ_le_mono in Hb3.
 destruct (Nat.eq_dec b 2) as [Ha| Ha].
  subst b; simpl.
  rewrite Nat.mul_1_r.
  destruct a; [ easy | ].
  apply Nat.succ_le_mono in Ha2.
  apply Mult.mult_S_lt_compat_l; simpl.
  apply Lt.lt_n_S.
  rewrite Nat.mul_comm; simpl.
  destruct a; [ easy | clear Ha2; simpl ].
  do 3 rewrite Nat.add_succ_r.
  do 2 apply -> Nat.succ_lt_mono.
  apply Nat.lt_0_succ.

  apply Nat.neq_sym in Ha.
  assert (Hb: b ≥ 3) by now apply Nat_le_neq_lt.
  specialize (IHb Hb).
  simpl.
  destruct a; [ easy | ].
  apply Nat.succ_le_mono in Ha2.
  apply Mult.mult_S_lt_compat_l.
  eapply Nat.le_lt_trans; [ | eassumption ].
  rewrite <- Nat.add_1_r; simpl.
  apply Nat.add_le_mono; [ easy | ].
  destruct a; [ easy | simpl ].
  destruct b; [ easy | simpl ].
  apply -> Nat.succ_le_mono.
  apply Nat.le_0_l.
Qed.

Theorem pow_lt_pow_succ : ∀ a b, a ≥ 2 → b ≥ 1 → a ^ b + (a - 1) < a ^ S b.
Proof.
intros * Ha Hb.
induction b; [ easy | clear Hb ].
destruct (Nat.eq_dec b 0) as [Hb| Hb].
 subst b; simpl.
 rewrite Nat.mul_1_r.
 clear IHb.
 induction a; [ easy | ].
 destruct a; [ easy | simpl; lia ].

 assert (Hb1 : b ≥ 1) by lia.
 specialize (IHb Hb1); simpl.
 apply Nat.lt_le_trans with (m := a * (a ^ b + (a - 1))).
  rewrite Nat.mul_add_distr_l.
  apply Nat.add_le_lt_mono; [ easy | ].
  destruct a; [ easy | simpl ].
  rewrite Nat.sub_0_r.
  apply Nat.succ_le_mono in Ha.
  destruct a; [ easy | simpl; lia ].

  apply Nat.mul_le_mono_nonneg_l; [ lia | ].
  destruct a; [ easy | ].
  rewrite Nat.sub_succ, Nat.sub_0_r; simpl.
  apply Nat.add_le_mono; [ easy | ].
  destruct b; [ easy | ].
  apply Nat.succ_le_mono in Ha.
  replace a with (a * 1) at 1 by lia.
  apply Nat.mul_le_mono; [ easy | ].
  replace 1 with (S a ^ 0) by easy.
  apply Nat.pow_le_mono_r; [ easy | lia ].
Qed.

Theorem small : ∀ r, r ≥ 2 →
  ∀ i n, n ≥ r * (i + 2)
  → n * (r - 1) + r < r ^ (n - (i + 1)).
Proof.
intros r Hr * Hnr.
assert (Hni : n ≥ i + 1).
 destruct r; [ easy | ].
 simpl in Hnr; lia.

 remember (n - (i + 1)) as m eqn:Hm.
 assert (Hn : n = m + (i + 1)) by lia.
 subst n; clear Hm Hni.
 apply Nat.sub_le_mono_r with (p := i + 1) in Hnr.
 rewrite Nat.add_sub in Hnr.
 replace (i + 1) with (1 * (i + 1)) in Hnr by lia.
 replace (r * (i + 2)) with (r * (i + 1) + r) in Hnr by lia.
 rewrite Nat.add_sub_swap in Hnr.
  rewrite <- Nat.mul_sub_distr_r in Hnr.
  rewrite Nat.mul_add_distr_r.
  rewrite <- Nat.add_assoc.
  rewrite Nat.mul_comm in Hnr.
  remember ((i + 1) * (r - 1) + r) as b eqn:Hb.
  induction m; [ simpl; lia | ].
  destruct (Nat.eq_dec b (S m)) as [Hbm| Hbm].
   replace b with (b * 1) by lia.
   move Hbm at top; subst b.
   rewrite <- Nat.mul_add_distr_l.
   rewrite Nat.sub_add; [ | lia ].
   rewrite Nat.mul_comm.
   apply Nat_mul_lt_pow; [ easy | ].
   rewrite Hb.
   apply Nat.le_trans with (m := (i + 1) * (r - 1) + 2).
    do 2 rewrite Nat.add_succ_r.
    do 2 apply -> Nat.succ_le_mono.
    rewrite Nat.add_0_r, Nat.mul_add_distr_r; lia.

    now apply Nat.add_le_mono_l.

   apply Nat_le_neq_lt in Hbm; [ | easy ].
   apply Nat.succ_le_mono in Hbm.
   specialize (IHm Hbm).
   apply Nat.lt_trans with (m := r - 1 + r ^ m).
    simpl; rewrite <- Nat.add_assoc.
    now apply Nat.add_le_lt_mono.

    rewrite Nat.add_comm.
    apply pow_lt_pow_succ; lia.

  rewrite Nat.mul_1_l.
  destruct r; [ easy | simpl; lia ].
Qed.

(* This theorem could have been written as:
Theorem small_sum : ∀ r, r ≥ 2 →
  ∀ u, (∀ i, u i ≤ (i + 1) * (r - 1) ^ 2) →
  ∀ i n, n ≥ r * (i + 2) → ∀ m, Σ (j = n, m), u j * r ^ (i - j) < 1.
But, it works in rationals not in naturals, since i-j can be negative.
Therefore, we written the same theorem the following way to use
naturals. *)
(*
Theorem small_sum (rg := nat_ord_ring) : ∀ r, r ≥ 2 →
  ∀ u, (∀ i, u i ≤ (i + 1) * (r - 1) ^ 2) →
  ∀ i n, n ≥ r * (i + 2) →
  ∀ m, Σ (j = n, m), u j * r ^ (m - j) < r ^ (m - i).
Proof.
intros * Hr * Hu * Hni *.
assert
  (Hss :
   Σ (j = n, m), u j * r ^ (m - j) ≤
   Σ (j = n, m), (j + 1) * (r - 1) ^ 2 * r ^ (m - j)). {
  apply (@summation_le_compat nat_ord_ring_def).
  intros j Hj.
  apply Nat.mul_le_mono_nonneg_r; [ apply Nat.le_0_l | ].
  apply Hu.
}
eapply Nat.le_lt_trans; [ apply Hss | clear Hss ].
assert
  (Hss :
   Σ (j = n, m), (j + 1) * (r - 1) ^ 2 * r ^ (m - j) =
   Σ (j = n, m), (j + 1) * r ^ (m - j) * (r - 1) ^ 2). {
  apply summation_eq_compat.
  intros j Hj.
  apply Nat.mul_shuffle0.
}
rewrite Hss; clear Hss.
rewrite <- summation_mul_distr_r.
rewrite Nat.mul_comm.
assert
  (Hss :
   Σ (j = n, m), (j + 1) * r ^ (m - j) =
   Σ (j = n, m), (j * r ^ (m - j) + r ^ (m - j))). {
  apply summation_eq_compat.
  intros j Hj.
  now rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
}
rewrite Hss; clear Hss.
specialize (small r Hr i n Hni) as H.
...
   rewrite summation_add_distr.
   simpl.
   rewrite Nat.mul_1_r.


bbb.
*)
