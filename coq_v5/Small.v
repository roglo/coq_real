Require Import Utf8 Arith NPeano Psatz.

Notation "a ^ b" := (Nat.pow a b).

Theorem Nat_le_neq_lt : ∀ a b, a ≤ b → a ≠ b → a < b.
Proof.
intros a b Hab Hnab.
apply le_lt_eq_dec in Hab.
destruct Hab as [Hle| Heq]; [ assumption | idtac ].
exfalso; apply Hnab; assumption.
Qed.

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
do 2 rewrite <- Nat.sub_add_distr.
f_equal.
apply Nat.add_comm.
Qed.

Theorem small : ∀ r, r ≥ 2 →
  ∀ i n, n ≥ r * (i + 2) → n * (r - 1) + r < r ^ (n - (i + 1)).
Proof.
intros r Hr * Hnr.
induction n.
 exfalso.
 apply Nat.le_0_r in Hnr.
 apply Nat.eq_mul_0 in Hnr.
 destruct Hnr; [ subst r; easy | ].
 now apply Nat.eq_add_0 in H.

 destruct (Nat.eq_dec (S n) (r * (i + 2))) as [Hn| Hn].
  rewrite Hn.
  remember (r * (i + 2) - (i + 1)) as a eqn:Ha.
  replace r with (r * 1) at 3 by apply Nat.mul_1_r.
  rewrite <- Nat.mul_assoc.
  rewrite <- Nat.mul_add_distr_l.
  replace ((i + 2) * (r - 1) + 1) with a.
   assert (Ha3 : a ≥ 3).
    subst a; clear -Hr.
    destruct r; [ easy | simpl ].
    apply Nat.succ_le_mono in Hr.
    destruct r; [ easy | clear Hr ].
    do 2 rewrite Nat.add_succ_r.
    rewrite Nat.add_0_r.
    rewrite Nat.add_sub_swap; [ | apply Nat.le_succ_diag_r ].
    rewrite Nat.sub_succ.
    rewrite Nat.sub_succ_l; [ | easy ].
    rewrite Nat.sub_diag; simpl.
    do 3 apply -> Nat.succ_le_mono.
    apply Nat.le_0_l.

    clear -Hr Ha3.
    induction a; [ easy | ].
     apply Nat.succ_le_mono in Ha3.
     destruct (Nat.eq_dec a 2) as [Ha| Ha].
      clear IHa Ha3.
      subst a; simpl.
      rewrite Nat.mul_1_r.
      destruct r; [ easy | ].
      apply Nat.succ_le_mono in Hr.
      apply Mult.mult_S_lt_compat_l; simpl.
      apply Lt.lt_n_S.
      rewrite Nat.mul_comm; simpl.
      destruct r; [ easy | clear Hr; simpl ].
      do 3 rewrite Nat.add_succ_r.
      do 2 apply -> Nat.succ_lt_mono.
      apply Nat.lt_0_succ.

      apply Nat.neq_sym in Ha.
      assert (Ha2: a ≥ 3) by now apply Nat_le_neq_lt.
      specialize (IHa Ha2).
      simpl.
      destruct r; [ easy | ].
      apply Nat.succ_le_mono in Hr.
      apply Mult.mult_S_lt_compat_l.
      eapply Nat.le_lt_trans; [ | eassumption ].
      rewrite <- Nat.add_1_r; simpl.
      apply Nat.add_le_mono; [ easy | ].
      destruct r; [ easy | simpl ].
      destruct a; [ easy | simpl ].
      apply -> Nat.succ_le_mono.
      apply Nat.le_0_l.

   subst a.
   destruct r; [ easy | ].
   apply Nat.add_sub_eq_l.
   rewrite Nat.sub_succ, Nat.sub_0_r.
   ring.

  simpl in r.
  apply Nat.neq_sym in Hn.
  assert (Hn2 : n ≥ r * ( i + 2)).
   apply lt_n_Sm_le.
   now apply Nat_le_neq_lt.

   specialize (IHn Hn2).
   rewrite Nat.sub_succ_l.
Focus 2.
eapply Nat.le_trans; [ | apply Hn2 ].
Unfocus.
simpl.
eapply

bbb,

   rewrite Nat.sub_add_distr.
   rewrite Nat_sub_sub_swap.
   rewrite Nat.sub_succ, Nat.sub_0_r.
   simpl.
bbb.
   apply Nat.lt_trans with (m := r - 1 + r ^ (n - (i + 1))).
Focus 2.
rewrite Nat.sub_add_distr.
destruct n.
apply le_n_0_eq in Hn2.
symmetry in Hn2.
apply mult_is_O in Hn2.
destruct Hn2.
subst r; easy.
now rewrite Nat.add_comm in H.
rewrite Nat_sub_sub_swap.
rewrite Nat.sub_succ, Nat.sub_0_r.
destruct i.
simpl.
rewrite Nat.sub_0_r.
simpl in IHn.
rewrite Nat.sub_0_r in IHn.
rewrite <- Nat.add_sub_swap; [ | lia ].
bbb.
