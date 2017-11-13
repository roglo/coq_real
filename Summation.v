(* Summation.v *)

Require Import Utf8 Arith NPeano Psatz.
Require Import Misc.

Fixpoint summation_aux b len g :=
  match len with
  | O => 0
  | S len₁ => g b + summation_aux (S b) len₁ g
  end.

Definition summation b e g := summation_aux b (S e - b) g.

Notation "'Σ' ( i = b , e ) , g" := (summation b e (λ i, g))
  (at level 45, i at level 0, b at level 60, e at level 60).

Lemma summation_aux_succ_last : ∀ g b len,
  summation_aux b (S len) g =
  summation_aux b len g + g (b + len).
Proof.
intros g b len.
revert b.
induction len; intros.
 now simpl; do 2 rewrite Nat.add_0_r.

 remember (S len) as x; simpl; subst x.
 rewrite IHlen; simpl.
 now rewrite Nat.add_assoc, Nat.add_succ_r.
Qed.

Theorem summation_split_last : ∀ g b k,
  b ≤ S k
  → Σ (i = b, S k), g i = Σ (i = b, k), g i + g (S k).
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite summation_aux_succ_last; f_equal.
rewrite Nat.add_sub_assoc; [ | easy ].
now rewrite Nat.add_comm, Nat.add_sub.
Qed.

Theorem summation_succ_succ : ∀ b k g,
  Σ (i = S b, S k), g i = Σ (i = b, k), g (S i).
Proof.
intros b k g.
unfold summation.
rewrite Nat.sub_succ.
remember (S k - b)%nat as len; clear Heqlen.
revert b.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen; reflexivity.
Qed.

Theorem summation_empty : ∀ g b k, k < b → Σ (i = b, k), g i = 0.
Proof.
intros * Hkb.
unfold summation.
now replace (S k - b)%nat with O by lia.
Qed.

Lemma summation_aux_eq_compat : ∀ g h b₁ b₂ len,
  (∀ i, 0 ≤ i < len → g (b₁ + i) = h (b₂ + i))
  → summation_aux b₁ len g = summation_aux b₂ len h.
Proof.
intros g h b₁ b₂ len Hgh.
revert b₁ b₂ Hgh.
induction len; intros; [ easy | simpl ].
erewrite IHlen.
 f_equal.
 assert (0 ≤ 0 < S len) as H.
  split; [ easy | apply Nat.lt_0_succ ].

  apply Hgh in H.
  now do 2 rewrite Nat.add_0_r in H.

 intros i Hi.
 do 2 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hgh.
 split; [ apply Nat.le_0_l | ].
 apply lt_n_S.
 now destruct Hi.
Qed.

Theorem summation_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → g i = h i)
  → Σ (i = b, k), g i = Σ (i = b, k), h i.
Proof.
intros g h b k Hgh.
apply summation_aux_eq_compat.
intros i (_, Hi).
apply Hgh.
split; [ apply Nat.le_add_r | idtac ].
apply Nat.lt_add_lt_sub_r, le_S_n in Hi.
now rewrite Nat.add_comm.
Qed.

Lemma summation_aux_le_compat : ∀ g h b₁ b₂ len,
  (∀ i, 0 ≤ i < len → g (b₁ + i) ≤ h (b₂ + i))
  → summation_aux b₁ len g ≤ summation_aux b₂ len h.
Proof.
intros g h b₁ b₂ len Hgh.
revert b₁ b₂ Hgh.
induction len; intros; simpl; [ easy | ].
apply Nat.add_le_mono.
 assert (H : 0 ≤ 0 < S len).
  split; [ easy | apply Nat.lt_0_succ ].

  apply Hgh in H.
  now do 2 rewrite Nat.add_0_r in H.

 apply IHlen; intros i Hi.
 do 2 rewrite Nat.add_succ_comm.
 apply Hgh.
 split; [ apply Nat.le_0_l | ].
 now apply -> Nat.succ_lt_mono.
Qed.

Theorem summation_le_compat : ∀ b k f g,
  (∀ i, b ≤ i ≤ k → f i ≤ g i)
  → Σ (i = b, k), f i ≤ Σ (i = b, k), g i.
Proof.
intros * Hfg.
unfold summation.
apply summation_aux_le_compat; intros i Hi.
apply Hfg; lia.
Qed.

Theorem summation_mul_distr_r : ∀ f b k a,
  (Σ (i = b, k), (f i)) * a =
  Σ (i = b, k), f i * a.
Proof.
intros.
unfold summation.
remember (S k - b) as len eqn:Hlen.
clear; revert b.
induction len; intros; simpl; [ easy | ].
rewrite Nat.mul_add_distr_r.
now rewrite IHlen.
Qed.

Theorem summation_only_one : ∀ g n, (Σ (i = n, n), g i = g n).
Proof.
intros g n.
unfold summation.
rewrite Nat.sub_succ_l; [ idtac | easy ].
rewrite Nat.sub_diag; simpl; lia.
Qed.

Theorem summation_add_distr : ∀ g h b k,
  (Σ (i = b, k), (g i + h i) =
   Σ (i = b, k), g i + Σ (i = b, k), h i).
Proof.
intros g h b k.
destruct (le_dec b k) as [Hbk| Hbk].
 revert b Hbk.
 induction k; intros.
  destruct b; [ | easy ].
  now do 3 rewrite summation_only_one.

  rewrite summation_split_last; [ idtac | assumption ].
  rewrite summation_split_last; [ idtac | assumption ].
  rewrite summation_split_last; [ idtac | assumption ].
  destruct (eq_nat_dec b (S k)) as [H₂| H₂].
   subst b.
   unfold summation; simpl.
   now rewrite Nat.sub_diag.

   apply Nat_le_neq_lt in Hbk; [ | easy ].
   apply Nat.succ_le_mono in Hbk.
   rewrite IHk; [ lia | easy ].

 unfold summation.
 apply Nat.nle_gt in Hbk.
 now replace (S k - b) with O by lia.
Qed.

Theorem summation_shift : ∀ b g k,
  b ≤ k
  → (Σ (i = b, k), g i =
     Σ (i = 0, k - b), g (b + i)%nat).
Proof.
intros b g k Hbk.
unfold summation.
rewrite Nat.sub_0_r.
rewrite Nat.sub_succ_l; [ idtac | assumption ].
now apply summation_aux_eq_compat.
Qed.

Theorem summation_aux_rtl : ∀ g b len,
  (summation_aux b len g =
   summation_aux b len (λ i, g (b + len - 1 + b - i)%nat)).
Proof.
intros g b len.
revert g b.
induction len; intros; [ reflexivity | idtac ].
remember (S len) as x.
rewrite Heqx in |- * at 1.
simpl; subst x.
rewrite IHlen.
rewrite summation_aux_succ_last.
rewrite Nat.add_succ_l, Nat.sub_succ, Nat.sub_0_r.
do 2 rewrite Nat.add_succ_r; rewrite Nat.sub_succ, Nat.sub_0_r.
rewrite Nat.add_sub_swap, Nat.sub_diag; [ | easy ].
rewrite Nat.add_comm; f_equal.
now apply summation_aux_eq_compat.
Qed.

Theorem summation_rtl : ∀ g b k,
  (Σ (i = b, k), g i = Σ (i = b, k), g (k + b - i)%nat).
Proof.
intros g b k.
unfold summation.
rewrite summation_aux_rtl.
apply summation_aux_eq_compat; intros i (Hi, Hikb).
destruct b; simpl.
 rewrite Nat.sub_0_r; reflexivity.

 rewrite Nat.sub_0_r.
 simpl in Hikb.
 eapply Nat.le_lt_trans in Hikb; eauto .
 apply lt_O_minus_lt, Nat.lt_le_incl in Hikb.
 remember (b + (k - b))%nat as x eqn:H .
 rewrite Nat.add_sub_assoc in H; auto.
 rewrite Nat.add_sub_swap in H; auto.
 rewrite Nat.sub_diag in H; subst x; reflexivity.
Qed.

(*
Theorem summation_mul_comm : ∀ g h b k,
  (Σ (i = b, k), g i * h i
   = Σ (i = b, k), h i * g i).
Proof.
intros g h b len.
apply summation_compat; intros i Hi.
apply rng_mul_comm.
Qed.

Theorem all_0_summation_aux_0 : ∀ g b len,
  (∀ i, (b ≤ i < b + len) → (g i = 0))
  → (summation_aux r b len (λ i, g i) = 0).
Proof.
intros g b len H.
revert b H.
induction len; intros; [ reflexivity | simpl ].
rewrite H; [ idtac | split; auto ].
 rewrite rng_add_0_l, IHlen; [ reflexivity | idtac ].
 intros i (Hbi, Hib); apply H.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 split; [ apply Nat.lt_le_incl; auto | auto ].

 rewrite Nat.add_succ_r.
 apply le_n_S, le_plus_l.
Qed.

Theorem all_0_summation_0 : ∀ g i₁ i₂,
  (∀ i, i₁ ≤ i ≤ i₂ → (g i = 0))
  → (Σ (i = i₁, i₂), g i = 0).
Proof.
intros g i₁ i₂ H.
apply all_0_summation_aux_0.
intros i (H₁, H₂).
apply H.
split; [ assumption | idtac ].
destruct (le_dec i₁ (S i₂)) as [H₃| H₃].
 rewrite Nat.add_sub_assoc in H₂; auto.
 rewrite minus_plus in H₂.
 apply le_S_n; auto.

 apply not_le_minus_0 in H₃.
 rewrite H₃, Nat.add_0_r in H₂.
 apply Nat.nle_gt in H₂; contradiction.
Qed.

Theorem summation_aux_mul_swap : ∀ a g b len,
  (summation_aux r b len (λ i, a * g i) =
   a * summation_aux r b len g).
Proof.
intros a g b len; revert b.
induction len; intros; simpl.
 rewrite rng_mul_0_r; reflexivity.

 rewrite IHlen, rng_mul_add_distr_l.
 reflexivity.
Qed.

Theorem summation_aux_summation_aux_mul_swap : ∀ g₁ g₂ g₃ b₁ b₂ len,
  (summation_aux r b₁ len
     (λ i, summation_aux r b₂ (g₁ i) (λ j, g₂ i * g₃ i j))
   = summation_aux r b₁ len
       (λ i, g₂ i * summation_aux r b₂ (g₁ i) (λ j, g₃ i j))).
Proof.
intros g₁ g₂ g₃ b₁ b₂ len.
revert b₁ b₂.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen.
apply rng_add_compat_r.
apply summation_aux_mul_swap.
Qed.

Theorem summation_summation_mul_swap : ∀ g₁ g₂ g₃ k,
  (Σ (i = 0, k), Σ (j = 0, g₁ i), g₂ i * g₃ i j
   = Σ (i = 0, k), g₂ i * Σ (j = 0, g₁ i), g₃ i j).
Proof.
intros g₁ g₂ g₃ k.
apply summation_aux_summation_aux_mul_swap.
Qed.

Theorem summation_only_one_non_0 : ∀ g b v k,
  (b ≤ v ≤ k)
  → (∀ i, (b ≤ i ≤ k) → (i ≠ v) → (g i = 0))
    → (Σ (i = b, k), g i = g v).
Proof.
intros g b v k (Hbv, Hvk) Hi.
unfold summation.
rewrite Nat.sub_succ_l; [ idtac | etransitivity; eassumption ].
remember (k - b) as len.
replace k with (b + len) in * .
 clear k Heqlen.
 revert b v Hbv Hvk Hi.
 induction len; intros.
  simpl.
  rewrite rng_add_0_r.
  replace b with v ; [ reflexivity | idtac ].
  rewrite Nat.add_0_r in Hvk.
  apply Nat.le_antisymm; assumption.

  remember (S len) as x; simpl; subst x.
  destruct (eq_nat_dec b v) as [H₁| H₁].
   subst b.
   rewrite all_0_summation_aux_0.
    rewrite rng_add_0_r; reflexivity.

    intros j (Hvj, Hjv).
    simpl in Hjv.
    apply le_S_n in Hjv.
    apply Hi; [ split; auto; apply Nat.lt_le_incl; auto | idtac ].
    intros H; subst j.
    revert Hvj; apply Nat.nle_succ_diag_l.

   rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hvk.
   rewrite Hi; auto.
    rewrite rng_add_0_l.
    apply IHlen; auto; [ apply Nat_le_neq_lt; auto | idtac ].
    intros j (Hvj, Hjvl) Hjv.
    rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hjvl.
    apply Hi; auto; split; auto.
    apply Nat.lt_le_incl; auto.

    split; auto.
    apply Nat.le_sub_le_add_l.
    rewrite Nat.sub_diag.
    apply Nat.le_0_l.

 subst len.
 eapply Nat.le_trans in Hvk; eauto .
 rewrite Nat.add_sub_assoc; auto.
 rewrite Nat.add_comm.
 apply Nat.add_sub.
Qed.

Theorem summation_summation_shift : ∀ g k,
  (Σ (i = 0, k), Σ (j = i, k), g i j =
   Σ (i = 0, k), Σ (j = 0, k - i), g i (i + j)%nat).
Proof.
intros g k.
apply summation_compat; intros i Hi.
unfold summation.
rewrite Nat.sub_0_r.
rewrite Nat.sub_succ_l; [ idtac | destruct Hi; assumption ].
apply summation_aux_eq_compat; intros j Hj.
rewrite Nat.add_0_l; reflexivity.
Qed.
*)

Theorem summation_aux_succ_first : ∀ g b len,
  summation_aux b (S len) g = (g b + summation_aux (S b) len g).
Proof. reflexivity. Qed.

Theorem summation_split_first : ∀ g b k,
  b ≤ k
  → Σ (i = b, k), g i = (g b + Σ (i = S b, k), g i).
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ.
rewrite <- summation_aux_succ_first.
rewrite <- Nat.sub_succ_l; [ reflexivity | assumption ].
Qed.

(*
Theorem summation_summation_exch : ∀ g k,
  (Σ (j = 0, k), Σ (i = 0, j), g i j =
   Σ (i = 0, k), Σ (j = i, k), g i j).
Proof.
intros g k.
induction k; [ reflexivity | idtac ].
rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
rewrite summation_split_last; [ idtac | apply Nat.le_0_l ].
rewrite IHk.
rewrite summation_only_one.
rewrite rng_add_assoc.
apply rng_add_compat_r.
rewrite <- summation_add_distr.
apply summation_compat; intros i (_, Hi).
rewrite summation_split_last; [ reflexivity | idtac ].
apply Nat.le_le_succ_r; assumption.
Qed.

Theorem summation_aux_ub_add : ∀ g b k₁ k₂,
  (summation_aux r b (k₁ + k₂) g =
   summation_aux r b k₁ g + summation_aux r (b + k₁) k₂ g).
Proof.
intros g b k₁ k₂.
revert b k₁.
induction k₂; intros.
 simpl.
 rewrite Nat.add_0_r, rng_add_0_r; reflexivity.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 rewrite IHk₂; simpl.
 rewrite <- Nat.add_succ_r.
 rewrite rng_add_assoc.
 apply rng_add_compat_r.
 clear k₂ IHk₂.
 revert b.
 induction k₁; intros; simpl.
  rewrite Nat.add_0_r.
  apply rng_add_comm.

  rewrite <- rng_add_assoc.
  rewrite IHk₁.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l; reflexivity.
Qed.

Theorem summation_ub_add : ∀ g k₁ k₂,
  (Σ (i = 0, k₁ + k₂), g i =
   Σ (i = 0, k₁), g i + Σ (i = S k₁, k₁ + k₂), g i).
Proof.
intros g k₁ k₂.
unfold summation.
do 2 rewrite Nat.sub_0_r.
rewrite <- Nat.add_succ_l.
rewrite summation_aux_ub_add; simpl.
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Theorem summation_aux_mul_summation_aux_summation_aux : ∀ g k n,
  (summation_aux r 0 (S k * S n) g =
   summation_aux r 0 (S k)
     (λ i, summation_aux r 0 (S n) (λ j, g (i * S n + j)%nat))).
Proof.
intros g k n.
revert n; induction k; intros.
 simpl; rewrite Nat.add_0_r, rng_add_0_r; reflexivity.

 remember (S n) as x.
 remember (S k) as y.
 simpl; subst x y.
 rewrite Nat.add_comm.
 rewrite summation_aux_ub_add, IHk.
 symmetry; rewrite rng_add_comm.
 symmetry.
 rewrite summation_aux_succ_first.
 rewrite rng_add_shuffle0, rng_add_comm.
 symmetry.
 replace (S k) with (k + 1)%nat by omega.
 rewrite summation_aux_ub_add.
 rewrite <- rng_add_assoc.
 apply rng_add_compat_l.
 simpl.
 rewrite rng_add_comm.
 apply rng_add_compat_l.
 symmetry; rewrite Nat.add_comm; simpl.
 rewrite Nat.add_0_r, rng_add_0_r.
 apply rng_add_compat_l.
 apply summation_aux_eq_compat; intros i Hi; simpl.
 rewrite Nat.add_succ_r; reflexivity.
Qed.

Theorem summation_mul_summation_summation : ∀ g n k,
  (0 < n)%nat
  → (0 < k)%nat
    → (Σ (i = 0, k * n - 1), g i =
       Σ (i = 0, k - 1), Σ (j = 0, n - 1), g (i * n + j)%nat).
Proof.
intros g n k Hn Hk.
unfold summation.
do 2 rewrite Nat.sub_0_r.
destruct n; [ exfalso; revert Hn; apply Nat.lt_irrefl | clear Hn ].
destruct k; [ exfalso; revert Hk; apply Nat.lt_irrefl | clear Hk ].
rewrite Nat.sub_succ, Nat.sub_0_r.
rewrite <- Nat.sub_succ_l, Nat.sub_succ, Nat.sub_0_r.
 rewrite summation_aux_mul_summation_aux_summation_aux.
 apply summation_aux_eq_compat; intros i Hi.
 rewrite Nat.sub_succ, Nat.sub_0_r, Nat.sub_0_r.
 reflexivity.

 simpl; apply le_n_S, Nat.le_0_l.
Qed.

Theorem inserted_0_summation : ∀ g h k n,
  n ≠ O
  → (∀ i, i mod n ≠ O → (g i = 0))
    → (∀ i, (g (n * i)%nat = h i))
      → (Σ (i = 0, k * n), g i = Σ (i = 0, k), h i).
Proof.
intros g h k n Hn Hf Hfg.
destruct k.
 rewrite Nat.mul_0_l.
 apply summation_compat; intros i (_, Hi).
 apply Nat.le_0_r in Hi; subst i.
 rewrite <- Hfg, Nat.mul_0_r; reflexivity.

 destruct n; [ exfalso; apply Hn; reflexivity | clear Hn ].
 replace (S k * S n)%nat with (S k * S n - 1 + 1)%nat.
  rewrite summation_ub_add.
  rewrite summation_mul_summation_summation; try apply Nat.lt_0_succ.
  rewrite Nat_sub_succ_1, Nat.add_comm, summation_only_one.
  simpl; do 2 rewrite Nat.sub_0_r.
  symmetry.
  rewrite <- Nat.add_1_r, summation_ub_add, Nat.add_1_r.
  rewrite summation_only_one, rng_add_comm, <- Hfg.
  symmetry.
  rewrite rng_add_comm.
  apply rng_add_compat; [ symmetry; rewrite Nat.mul_comm; reflexivity |  ].
  apply summation_compat; intros i Hi.
  rewrite summation_only_one_non_0 with (v := 0).
   rewrite Nat.add_0_r, Nat.mul_comm; apply Hfg.

   split; [ reflexivity | apply Nat.le_0_l ].

   intros j Hjn Hj.
   rewrite Hf; [ reflexivity |  ].
   rewrite Nat.add_comm.
   rewrite Nat.mod_add; [  | apply Nat.neq_succ_0 ].
   intros H; apply Hj; clear Hj.
   apply Nat.mod_divides in H; auto.
   destruct H as (c, Hc).
   destruct c.
    rewrite Nat.mul_0_r in Hc; assumption.

    rewrite Hc in Hjn.
    rewrite Nat.mul_comm in Hjn.
    simpl in Hjn.
    destruct Hjn as (_, H).
    apply Nat.nlt_ge in H.
    exfalso; apply H.
    apply le_n_S, Nat.le_add_r.

  rewrite Nat.sub_add; [ apply eq_refl |  ].
  simpl; apply le_n_S, Nat.le_0_l.

Qed.

Theorem summation_add_add_sub : ∀ g b k n,
  (Σ (i = b, k), g i = Σ (i = b + n, k + n), g (i - n)%nat).
Proof.
intros g b k n.
unfold summation.
replace (S (k + n) - (b + n))%nat with (S k - b)%nat by omega.
apply summation_aux_eq_compat.
intros i Hi.
replace (b + n + i - n)%nat with (b + i)%nat by omega.
reflexivity.
Qed.
*)
