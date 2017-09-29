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
bbb.

Theorem small : ∀ r, r ≥ 2 →
  ∀ i n, n ≥ r * (i + 2) → n * (r - 1) + r < r ^ (n - (i + 1)).
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
bbb.

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
   apply Nat_mul_lt_pow; [ easy | ].
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
    apply Nat.le_trans with (m := r * (i + 1)).
     rewrite Nat.mul_add_distr_l.
     rewrite Nat.mul_1_r.
     apply Nat.add_le_mono; [ | lia ].
     replace i with (1 * i) at 1 by lia.
     apply Nat.mul_le_mono; lia.

     apply Nat.mul_le_mono; lia.

    remember (n - (i + 1)) as b.
    remember (S b) as bb; simpl; subst bb.
    rewrite <- Nat.add_assoc.
    remember (n * ( r - 1) + r) as a.
    apply Nat.lt_le_trans with (m := r - 1 + r ^ b); [ lia | ].
    clear -Hr.
    destruct r; [ easy | ].
    rewrite Nat.sub_succ, Nat.sub_0_r.
    induction b; [ simpl; rewrite Nat.mul_1_r; lia | ].
    remember (S (S b)) as bb; simpl; subst bb.
    apply Nat.le_trans with (m := S r ^ S b + r * S r ^ b).
    rewrite Nat.add_assoc, Nat.add_shuffle0.
    apply Nat.add_le_mono.
     simpl.
     apply Nat.add_le_mono; [ | easy ].
bbb.


    apply Nat.le_trans with (m := r * S r ^ b + S r ^ S b).


    apply Nat.le_trans with (m := 


bbb.

destruct r; [ easy | ].
rewrite Nat.sub_succ.
rewrite Nat.sub_0_r.
simpl.
bbb.
    remember (S n) as m; simpl; subst m.

    apply Nat.le_trans with (m :=

bbb.
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
