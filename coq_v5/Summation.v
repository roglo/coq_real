(* summation of nat *)

Require Import Utf8 QArith NPeano.
Require Import Misc.

Open Scope nat_scope.

Fixpoint summation_loop b len g :=
  match len with
  | O => O
  | S len1 => g b + summation_loop (S b) len1 g
  end.

Definition summation b e g := summation_loop b (S e - b) g.

Notation "'Σ' ( i = b , e ) , g" := (summation b e (λ i, (g)))
  (at level 0, i at level 0, b at level 60, e at level 60, g at level 40).

(* Summation model and theorems borrowed from my proof of Puiseux's theorem,
   file Fsummation.v *)

Theorem summation_loop_compat : ∀ g h b1 b2 len,
  (∀ i, i < len → (g (b1 + i) = h (b2 + i)))
  → summation_loop b1 len g = summation_loop b2 len h.
Proof.
intros g h b1 b2 len Hgh.
revert b1 b2 Hgh.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen with (b2 := S b2).
 f_equal.
 pose proof (Hgh 0 (Nat.lt_0_succ len)) as H.
 do 2 rewrite Nat.add_0_r in H; assumption.

 intros i Hi.
 do 2 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hgh.
 apply Nat.succ_lt_mono in Hi; assumption.
Qed.

Theorem summation_compat : ∀ g h b e,
  (∀ i, b ≤ i ≤ e → g i = h i)
  → Σ (i = b, e), g i = Σ (i = b, e), h i.
Proof.
intros g h b e H.
apply summation_loop_compat.
intros i Hie.
apply H; omega.
Qed.

Theorem summation_loop_succ_first : ∀ g b len,
  summation_loop b (S len) g =
  g b + summation_loop (S b) len g.
Proof. reflexivity. Qed.

Theorem summation_loop_succ_last : ∀ g b len,
  summation_loop b (S len) g =
  summation_loop b len g + g (b + len).
Proof.
intros g b len.
revert b.
induction len; intros.
 simpl.
 do 2 rewrite Nat.add_0_r; reflexivity.

 remember (S len) as x; simpl; subst x.
 rewrite IHlen; simpl.
 rewrite Nat.add_succ_r, Nat.add_assoc; reflexivity.
Qed.

Theorem summation_loop_rev : ∀ b len g,
  summation_loop b len g =
  summation_loop b len (λ i, g (b + len - 1 + b - i)).
Proof.
intros b len g.
revert b.
induction len; intros; [ reflexivity | idtac ].
remember (S len) as x.
rewrite Heqx in |- * at 1; simpl; subst x.
rewrite IHlen.
rewrite summation_loop_succ_last.
rewrite Nat.add_comm; f_equal.
 apply summation_loop_compat.
 intros i Hi; f_equal.
 do 2 rewrite Nat.add_succ_r; reflexivity.

 f_equal.
 rewrite Nat.add_succ_r, Nat.sub_succ, Nat.sub_0_r.
 rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Theorem all_0_summation_loop_0 : ∀ g b len,
  (∀ i, (b ≤ i < b + len) → g i = 0)
  → summation_loop b len (λ i, g i) = 0.
Proof.
intros g b len H.
revert b H.
induction len; intros; [ reflexivity | simpl ].
rewrite H; [ idtac | split; auto ].
 rewrite Nat.add_0_l, IHlen; [ reflexivity | idtac ].
 intros i (Hbi, Hib); apply H.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 split; [ apply Nat.lt_le_incl; auto | auto ].

 rewrite Nat.add_succ_r.
 apply le_n_S, le_plus_l.
Qed.

Theorem all_0_summation_0 : ∀ g i1 i2,
  (∀ i, i1 ≤ i ≤ i2 → g i = 0)
  → Σ (i = i1, i2), g i = 0.
Proof.
intros g i1 i2 H.
apply all_0_summation_loop_0.
intros i (H1, H2).
apply H.
split; [ assumption | idtac ].
destruct (le_dec i1 (S i2)) as [H3| H3].
 rewrite Nat.add_sub_assoc in H2; auto.
 rewrite Nat.add_comm, Nat.add_sub in H2.
 apply Nat.succ_le_mono; assumption.

 apply not_le_minus_0 in H3.
 rewrite H3, Nat.add_0_r in H2.
 apply Nat.nle_gt in H2; contradiction.
Qed.

Theorem summation_only_one : ∀ g n, Σ (i = n, n), g i = g n.
Proof.
intros g n.
unfold summation.
rewrite Nat.sub_succ_l; [ idtac | reflexivity ].
rewrite Nat.sub_diag; simpl.
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem summation_empty : ∀ f b k, k < b → Σ (i = b, k), f i = 0.
Proof.
intros f b k Hkb.
unfold summation.
destruct b; [ exfalso; revert Hkb; apply Nat.nlt_0_r | idtac ].
rewrite Nat.sub_succ.
apply le_S_n in Hkb.
apply Nat.sub_0_le in Hkb; rewrite Hkb; reflexivity.
Qed.

Theorem summation_split_first : ∀ g b k,
  b ≤ k
  → Σ (i = b, k), g i = g b + Σ (i = S b, k), g i.
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ.
rewrite <- summation_loop_succ_first.
rewrite <- Nat.sub_succ_l; [ reflexivity | assumption ].
Qed.

Theorem summation_split_last : ∀ g b k,
  b ≤ S k
  → Σ (i = b, S k), g i = Σ (i = b, k), g i + g (S k).
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ_l; [ idtac | assumption ].
rewrite summation_loop_succ_last.
rewrite Nat.add_sub_assoc; [ f_equal | assumption ].
rewrite Nat.add_comm, Nat.add_sub.
reflexivity.
Qed.

Theorem summation_le : ∀ f n, (∀ i, f i ≤ 1) → Σ (i = 1, n), f i ≤ n.
Proof.
intros f n Hf.
induction n; [ reflexivity | idtac ].
rewrite summation_split_last; [ idtac | apply le_n_S, Nat.le_0_l ].
remember 1 as one; rewrite <- Nat.add_1_r; subst one.
apply Nat.add_le_mono; [ assumption | apply Hf ].
Qed.

Theorem summation_split : ∀ b1 e1 f k,
  b1 ≤ S k ≤ S e1
  → Σ (i = b1, e1), f i =
    Σ (i = b1, k), f i + Σ (i = S k, e1), f i.
Proof.
intros b1 e1 f k (Hb, He).
revert b1 k Hb He.
induction e1; intros.
 apply le_S_n, Nat.le_0_r in He; subst k.
 symmetry; rewrite Nat.add_comm.
 rewrite summation_empty; [ reflexivity | apply Nat.lt_0_1 ].

 destruct (le_dec k e1) as [H1| H1].
  apply le_n_S in H1.
  rewrite summation_split_last; [ idtac | eapply le_trans; eassumption ].
  rewrite summation_split_last; [ idtac | assumption ].
  erewrite IHe1; [ idtac | eassumption | assumption ].
  rewrite Nat.add_assoc; reflexivity.

  apply Nat.nle_gt, le_n_S in H1.
  apply Nat.le_antisymm in He; [ idtac | assumption ].
  apply Nat.succ_inj in He; subst k.
  symmetry; rewrite Nat.add_comm.
  rewrite summation_empty; [ reflexivity | idtac ].
  apply Nat.lt_succ_r; reflexivity.
Qed.

Theorem summation_split3 : ∀ b1 e1 f k,
  b1 ≤ S k ≤ e1
  → Σ (i = b1, e1), f i =
    Σ (i = b1, k), f i + f (S k) + Σ (i = S (S k), e1), f i.
Proof.
intros b1 e1 f k (Hb, He).
rewrite summation_split with (k := k).
 rewrite <- Nat.add_assoc; f_equal.
 apply summation_split_first; assumption.

 split; [ assumption | idtac ].
 apply Nat.lt_le_incl, le_n_S; assumption.
Qed.

Theorem summation_add_distr : ∀ g h b k,
  Σ (i = b, k), (g i + h i) =
  Σ (i = b, k), g i + Σ (i = b, k), h i.
Proof.
intros g h b k.
destruct (le_dec b k) as [Hbk| Hbk].
 revert b Hbk.
 induction k; intros.
  destruct b; [ idtac | reflexivity ].
  do 3 rewrite summation_only_one; reflexivity.

  rewrite summation_split_last; [ idtac | assumption ].
  rewrite summation_split_last; [ idtac | assumption ].
  rewrite summation_split_last; [ idtac | assumption ].
  destruct (eq_nat_dec b (S k)) as [H₂| H₂].
   subst b.
   unfold summation; simpl.
   rewrite Nat.sub_diag; reflexivity.

   apply Nat_le_neq_lt in Hbk; [ idtac | assumption ].
   apply Nat.succ_le_mono in Hbk.
   rewrite IHk; [ idtac | assumption ].
   do 2 rewrite <- Nat.add_assoc.
   f_equal; rewrite Nat.add_comm, Nat.add_assoc.
   apply Nat.add_shuffle0.

 unfold summation.
 apply Nat.nle_gt in Hbk.
 replace (S k - b) with O by omega; reflexivity.
Qed.

Theorem summation_loop_rtl : ∀ g b len,
  summation_loop b len g =
  summation_loop b len (λ i, g (b + len - 1 + b - i)).
Proof.
intros g b len.
revert g b.
induction len; intros; [ reflexivity | idtac ].
remember (S len) as x.
rewrite Heqx in |- * at 1.
simpl; subst x.
rewrite IHlen.
rewrite summation_loop_succ_last.
rewrite Nat.add_succ_l, Nat_sub_succ_1.
do 2 rewrite Nat.add_succ_r; rewrite Nat_sub_succ_1.
rewrite Nat.add_sub_swap, Nat.sub_diag; auto.
rewrite Nat.add_comm; f_equal.
apply summation_loop_compat.
intros; reflexivity.
Qed.

Theorem summation_rtl : ∀ g b k,
  Σ (i = b, k), g i = Σ (i = b, k), g (k + b - i).
Proof.
intros g b k.
unfold summation.
rewrite summation_loop_rtl.
apply summation_loop_compat; intros i Hi.
destruct b; simpl; [ rewrite Nat.sub_0_r; reflexivity | idtac ].
rewrite Nat.sub_0_r; simpl in Hi.
apply Nat.lt_add_lt_sub_r in Hi.
apply Nat.le_trans with (n := b) in Hi.
 remember (b + (k - b))%nat as x eqn:H .
 rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
 rewrite Nat.add_sub_swap in H; auto.
 rewrite Nat.sub_diag in H; subst x; reflexivity.

 rewrite <- Nat.add_succ_l.
 apply Nat.le_sub_le_add_r.
 rewrite Nat.sub_diag.
 apply Nat.le_0_l.
Qed.

Theorem summation_shift : ∀ b g k n,
  n ≤ b
  → n ≤ k
  → Σ (i = b, k), g i =
    Σ (i = b - n, k - n), g (i + n).
Proof.
intros b g k n Hnb Hnk.
destruct (le_dec b k) as [H1| H1].
 unfold summation; symmetry.
 rewrite Nat.sub_succ_l; [ idtac | apply Nat.sub_le_mono_r; assumption ].
 rewrite Nat_sub_sub_distr; [ idtac | assumption ].
 rewrite Nat.sub_add; [ idtac | eassumption ].
 rewrite Nat.sub_succ_l; [ idtac | assumption ].
 apply summation_loop_compat; intros j Hj.
 rewrite Nat.add_shuffle0, Nat.sub_add; [ reflexivity | assumption ].

 apply Nat.nle_gt in H1.
 rewrite summation_empty; [ idtac | assumption ].
 rewrite summation_empty; [ reflexivity | idtac ].
 apply Nat.lt_add_lt_sub_l.
 rewrite Nat.add_sub_assoc; [ idtac | assumption ].
 rewrite Nat.add_comm, Nat.add_sub; assumption.
Qed.
