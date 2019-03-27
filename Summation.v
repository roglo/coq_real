(* Summation.v *)

Require Import Utf8 Arith NPeano Psatz.
Require Import Misc.

Class ord_ring_def :=
   { rng_t : Type;
     rng_zero : rng_t;
     rng_add : rng_t → rng_t → rng_t;
     rng_sub : rng_t → rng_t → rng_t;
     rng_mul : rng_t → rng_t → rng_t;
     rng_le : rng_t → rng_t → Prop }.

Delimit Scope rng_scope with Rg.

Notation "0" := (rng_zero) : rng_scope.
Notation "a + b" := (rng_add a b) : rng_scope.
Notation "a - b" := (rng_sub a b) : rng_scope.
Notation "a * b" := (rng_mul a b) : rng_scope.
Notation "a ≤ b" := (rng_le a b) : rng_scope.

Class ord_ring {rnd : ord_ring_def} :=
  { rng_add_0_l : ∀ a, (0 + a = a)%Rg;
    rng_add_comm : ∀ a b, (a + b = b + a)%Rg;
    rng_add_assoc : ∀ a b c, (a + (b + c) = (a + b) + c)%Rg;
    rng_sub_diag : ∀ a, (a - a = 0)%Rg;
    rng_mul_comm : ∀ a b, (a * b = b * a)%Rg;
    rng_mul_assoc : ∀ a b c, (a * (b * c) = (a * b) * c)%Rg;
    rng_mul_add_distr_l : ∀ a b c, (a * (b + c) = a * b + a * c)%Rg;
    rng_mul_sub_distr_l : ∀ a b c, (a * (b - c) = a * b - a * c)%Rg;
    rng_le_refl : ∀ a, (a ≤ a)%Rg;
    rng_le_antisymm : ∀ n m, (n ≤ m → m ≤ n → n = m)%Rg;
    rng_add_le_compat : ∀ n m p q, (n ≤ m → p ≤ q → n + p ≤ m + q)%Rg }.

Theorem rng_add_0_r `{rg : ord_ring} : ∀ a, (a + 0 = a)%Rg.
Proof.
intros.
rewrite rng_add_comm.
apply rng_add_0_l.
Qed.

Theorem rng_mul_add_distr_r `{rg : ord_ring} : ∀ a b c,
   ((a + b) * c = a * c + b * c)%Rg.
Proof.
intros.
rewrite rng_mul_comm, rng_mul_add_distr_l.
f_equal; apply rng_mul_comm.
Qed.

Theorem rng_mul_sub_distr_r `{rg : ord_ring} : ∀ a b c,
   ((a - b) * c = a * c - b * c)%Rg.
Proof.
intros.
rewrite rng_mul_comm, rng_mul_sub_distr_l.
f_equal; apply rng_mul_comm.
Qed.

Theorem rng_mul_0_l `{rg : ord_ring} : ∀ a, (0 * a = 0)%Rg.
Proof.
intros.
replace 0%Rg with (0 - 0)%Rg at 1 by apply rng_sub_diag.
rewrite rng_mul_sub_distr_r.
now rewrite rng_sub_diag.
Qed.

Theorem rng_mul_0_r `{rg : ord_ring} : ∀ a, (a * 0 = 0)%Rg.
Proof.
intros.
rewrite rng_mul_comm.
apply rng_mul_0_l.
Qed.

Theorem rng_add_eq_compat `{rg : ord_ring} : ∀ n m p q,
  n = m → p = q → (n + p = m + q)%Rg.
Proof.
intros * Hnm Hpq.
apply rng_le_antisymm.
-apply rng_add_le_compat; subst; apply rng_le_refl.
-apply rng_add_le_compat; subst; apply rng_le_refl.
Qed.

Fixpoint summation_aux `{rg : ord_ring} (b len : nat) (g : nat → _) :=
  match len with
  | O => 0%Rg
  | S len₁ => (g b + summation_aux (S b) len₁ g)%Rg
  end.

Definition summation `{rg : ord_ring} b e g :=
  summation_aux b (S e - b) g.

Notation "'Σ' ( i = b , e ) , g" := (summation b e (λ i, g))
  (at level 45, i at level 0, b at level 60, e at level 60).

Theorem summation_empty `{rg : ord_ring} : ∀ g b k,
  k < b → Σ (i = b, k), g i = 0%Rg.
Proof.
intros * Hkb.
unfold summation.
now replace (S k - b)%nat with O by lia.
Qed.

Theorem summation_aux_succ_last `{rg : ord_ring} :
  ∀ g b len,
  (summation_aux b (S len) g =
   summation_aux b len g + g (b + len)%nat)%Rg.
Proof.
intros g b len.
revert b.
induction len; intros.
 simpl; rewrite Nat.add_0_r.
 now rewrite rng_add_0_l, rng_add_0_r.

 remember (S len) as x; simpl; subst x.
 rewrite IHlen; simpl.
 now rewrite rng_add_assoc, Nat.add_succ_r.
Qed.

Theorem summation_aux_succ_first `{rg : ord_ring} : ∀ g b len,
  summation_aux b (S len) g = (g b + summation_aux (S b) len g)%Rg.
Proof. easy. Qed.

Theorem summation_split_first `{rg : ord_ring} : ∀ g b k,
  b ≤ k
  → Σ (i = b, k), g i = (g b + Σ (i = S b, k), g i)%Rg.
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ.
rewrite <- summation_aux_succ_first.
now rewrite <- Nat.sub_succ_l.
Qed.

Theorem summation_split_last `{rg : ord_ring} : ∀ g b k,
  b ≤ S k
  → (Σ (i = b, S k), g i = Σ (i = b, k), g i + g (S k))%Rg.
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite summation_aux_succ_last; f_equal.
rewrite Nat.add_sub_assoc; [ | easy ].
now rewrite Nat.add_comm, Nat.add_sub.
Qed.

Theorem summation_aux_split `{rg : ord_ring} : ∀ g b len1 len2,
  summation_aux b (len1 + len2) g =
  (summation_aux b len1 g + summation_aux (b + len1) len2 g)%Rg.
Proof.
intros.
revert b len2.
induction len1; intros.
-now simpl; rewrite rng_add_0_l, Nat.add_0_r.
-replace (S len1 + len2) with (len1 + S len2) by lia.
 replace (b + S len1) with (S b + len1) by lia.
 rewrite IHlen1; simpl.
 rewrite rng_add_assoc; f_equal.
 rewrite <- summation_aux_succ_first.
 now rewrite summation_aux_succ_last.
Qed.

Theorem summation_split `{rg : ord_ring} : ∀ g b e k,
  b + 1 ≤ e + 2 ≤ k + 2
  → (Σ (i = b, k), g i = Σ (i = b, e), g i + Σ (i = S e, k), g i)%Rg.
Proof.
intros * (Hbe, Hek).
unfold summation.
rewrite Nat.sub_succ.
destruct (eq_nat_dec b (S k)) as [H1| H1].
-assert (e = k) by lia; subst b e.
 do 2 rewrite Nat.sub_diag; simpl.
 now rewrite rng_add_0_r.
-rewrite Nat.sub_succ_l; [ | lia ].
 destruct (eq_nat_dec b (S e)) as [H2| H2].
 +rewrite H2, Nat.sub_diag.
  replace (S (k - S e)) with (k - e) by lia.
  now simpl; rewrite rng_add_0_l.
 +destruct (eq_nat_dec e k) as [H3| H3].
  *subst e.
   rewrite Nat.sub_diag.
   rewrite Nat.sub_succ_l; [ simpl | lia ].
   now rewrite rng_add_0_r.
  *rewrite Nat.sub_succ_l; [ | lia ].
   simpl; rewrite <- rng_add_assoc; f_equal.
   remember (e - b) as len1 eqn:Hlen1.
   replace (k - b) with (len1 + k - e) by lia.
   rewrite <- Nat.add_sub_assoc; [ | lia ].
   remember (k - e) as len2 eqn:Hlen2.
   replace (S e) with (S b + len1) by lia.
   apply summation_aux_split.
Qed.
(*
Theorem summation_split `{rg : ord_ring} : ∀ g b e k,
  b ≤ e ≤ k
  → (Σ (i = b, k), g i = Σ (i = b, e), g i + Σ (i = S e, k), g i)%Rg.
Proof.
intros * (Hbe, Hek).
unfold summation.
rewrite Nat.sub_succ.
rewrite Nat.sub_succ_l; [ | lia ].
rewrite Nat.sub_succ_l; [ | easy ].
simpl; rewrite <- rng_add_assoc; f_equal.
remember (e - b) as len1 eqn:Hlen1.
replace (k - b) with (len1 + k - e) by lia.
rewrite <- Nat.add_sub_assoc; [ | easy ].
remember (k - e) as len2 eqn:Hlen2.
replace (S e) with (S b + len1) by lia.
apply summation_aux_split.
Qed.
*)

Theorem summation_succ_succ `{rg : ord_ring} : ∀ b k g,
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

Theorem summation_aux_eq_compat `{rg : ord_ring} : ∀ g h b₁ b₂ len,
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

Theorem summation_eq_compat `{rg : ord_ring} : ∀ g h b k,
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

Theorem summation_aux_le_compat `{rg : ord_ring} : ∀ g h b₁ b₂ len,
  (∀ i, 0 ≤ i < len → (g (b₁ + i)%nat ≤ h (b₂ + i)%nat)%Rg)
  → (summation_aux b₁ len g ≤ summation_aux b₂ len h)%Rg.
Proof.
intros g h b₁ b₂ len Hgh.
revert b₁ b₂ Hgh.
induction len; intros; [ apply rng_le_refl | simpl ].
apply rng_add_le_compat.
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

Theorem summation_le_compat `{rg : ord_ring} : ∀ b k f g,
  (∀ i, b ≤ i ≤ k → (f i ≤ g i)%Rg)
  → (Σ (i = b, k), f i ≤ Σ (i = b, k), g i)%Rg.
Proof.
intros * Hfg.
unfold summation.
apply summation_aux_le_compat; intros i Hi.
apply Hfg; lia.
Qed.

Theorem summation_mul_distr_r `{rg : ord_ring} : ∀ f b k a,
  ((Σ (i = b, k), (f i)) * a = Σ (i = b, k), f i * a)%Rg.
Proof.
intros.
unfold summation.
remember (S k - b) as len eqn:Hlen.
clear; revert b.
induction len; intros; simpl; [ apply rng_mul_0_l | ].
rewrite rng_mul_add_distr_r.
now rewrite IHlen.
Qed.

Theorem summation_mul_distr_l `{rg : ord_ring} : ∀ f b k a,
  (a * (Σ (i = b, k), f i) = Σ (i = b, k), a * f i)%Rg.
Proof.
intros.
rewrite rng_mul_comm.
rewrite summation_mul_distr_r.
apply summation_eq_compat.
intros; apply rng_mul_comm.
Qed.

Theorem summation_only_one `{rg : ord_ring} : ∀ g n,
  (Σ (i = n, n), g i = g n)%Rg.
Proof.
intros g n.
unfold summation.
rewrite Nat.sub_succ_l; [ idtac | easy ].
rewrite Nat.sub_diag; simpl.
now rewrite rng_add_0_r.
Qed.

Theorem summation_add_distr `{rg : ord_ring} : ∀ g h b k,
  (Σ (i = b, k), (g i + h i) =
   Σ (i = b, k), g i + Σ (i = b, k), h i)%Rg.
Proof.
intros g h b k.
destruct (le_dec b k) as [Hbk| Hbk].
 revert b Hbk.
 induction k; intros.
  destruct b; [ | easy ].
  now do 3 rewrite summation_only_one.

  rewrite summation_split_last; [ | easy ].
  rewrite summation_split_last; [ | easy ].
  rewrite summation_split_last; [ | easy ].
  destruct (eq_nat_dec b (S k)) as [H₂| H₂].
   subst b.
   unfold summation; simpl.
   rewrite Nat.sub_diag; simpl.
   now do 3 rewrite rng_add_0_l.

   apply Nat_le_neq_lt in Hbk; [ | easy ].
   apply Nat.succ_le_mono in Hbk.
   rewrite IHk; [ | easy ].
   do 2 rewrite rng_add_assoc; f_equal.
   do 2 rewrite <- rng_add_assoc; f_equal.
   apply rng_add_comm.

 unfold summation.
 apply Nat.nle_gt in Hbk.
 replace (S k - b) with O by lia; simpl.
 now rewrite rng_add_0_l.
Qed.

(*
Theorem summation_sub_distr `{rg : ord_ring} : ∀ g h b k,
  (Σ (i = b, k), (g i - h i) =
   Σ (i = b, k), g i - Σ (i = b, k), h i)%Rg.
Proof.
intros.
destruct (le_dec b k) as [Hbk| Hbk].
 revert b Hbk.
 induction k; intros.
  destruct b; [ | easy ].
  now do 3 rewrite summation_only_one.

  rewrite summation_split_last; [ | easy ].
  rewrite summation_split_last; [ | easy ].
  rewrite summation_split_last; [ | easy ].
  destruct (eq_nat_dec b (S k)) as [H₂| H₂].
   subst b.
   unfold summation; simpl.
   rewrite Nat.sub_diag; simpl.
   now do 3 rewrite rng_add_0_l.

   apply Nat_le_neq_lt in Hbk; [ | easy ].
   apply Nat.succ_le_mono in Hbk.
   rewrite IHk; [ | easy ].
...
   do 2 rewrite rng_add_assoc; f_equal.
   do 2 rewrite <- rng_add_assoc; f_equal.
   apply rng_add_comm.

 unfold summation.
 apply Nat.nle_gt in Hbk.
 replace (S k - b) with O by lia; simpl.
 now rewrite rng_add_0_l.
...
*)

Theorem summation_aux_shift `{rg : ord_ring} : ∀ b len g,
  summation_aux b len g = summation_aux 0 len (λ i, g (b + i)).
Proof.
intros.
now apply summation_aux_eq_compat.
Qed.

Theorem summation_shift `{rg : ord_ring} : ∀ b g k,
  b ≤ k
  → (Σ (i = b, k), g i =
     Σ (i = 0, k - b), g (b + i)%nat)%Rg.
Proof.
intros b g k Hbk.
unfold summation.
rewrite Nat.sub_0_r.
rewrite Nat.sub_succ_l; [ idtac | assumption ].
apply summation_aux_shift.
Qed.

Theorem summation_aux_rtl `{rg : ord_ring} : ∀ g b len,
  (summation_aux b len g =
   summation_aux b len (λ i, g (b + len - 1 + b - i)%nat)).
Proof.
intros g b len.
revert g b.
induction len; intros; [ easy | ].
remember (S len) as x.
rewrite Heqx in |- * at 1.
simpl; subst x.
rewrite IHlen.
rewrite summation_aux_succ_last.
rewrite Nat.add_succ_l, Nat.sub_succ, Nat.sub_0_r.
do 2 rewrite Nat.add_succ_r; rewrite Nat.sub_succ, Nat.sub_0_r.
rewrite Nat.add_sub_swap, Nat.sub_diag; [ | easy ].
rewrite rng_add_comm; f_equal.
now apply summation_aux_eq_compat.
Qed.

Theorem summation_rtl `{rg : ord_ring} : ∀ g b k,
  (Σ (i = b, k), g i = Σ (i = b, k), g (k + b - i)%nat).
Proof.
intros g b k.
unfold summation.
rewrite summation_aux_rtl.
apply summation_aux_eq_compat; intros i (Hi, Hikb).
destruct b; simpl; [ now rewrite Nat.sub_0_r | ].
rewrite Nat.sub_0_r.
simpl in Hikb.
eapply Nat.le_lt_trans in Hikb; eauto .
apply lt_O_minus_lt, Nat.lt_le_incl in Hikb.
remember (b + (k - b))%nat as x eqn:H .
rewrite Nat.add_sub_assoc in H; auto.
rewrite Nat.add_sub_swap in H; auto.
rewrite Nat.sub_diag in H; subst x; reflexivity.
Qed.

Theorem summation_mul_comm `{rg : ord_ring} : ∀ g h b k,
  (Σ (i = b, k), g i * h i
   = Σ (i = b, k), h i * g i)%Rg.
Proof.
intros g h b len.
apply summation_eq_compat; intros i Hi.
apply rng_mul_comm.
Qed.

Theorem all_0_summation_aux_0 `{rg : ord_ring} : ∀ g b len,
  (∀ i, (b ≤ i < b + len) → (g i = 0%Rg))
  → (summation_aux b len (λ i, g i) = 0%Rg).
Proof.
intros g b len H.
revert b H.
induction len; intros; [ easy | simpl ].
rewrite H; [ | lia ].
rewrite rng_add_0_l, IHlen; [ easy | ].
intros i (Hbi, Hib); apply H.
rewrite Nat.add_succ_r, <- Nat.add_succ_l.
now split; [ apply Nat.lt_le_incl | ].
Qed.

Theorem all_0_summation_0 `{rg : ord_ring} : ∀ g i₁ i₂,
  (∀ i, i₁ ≤ i ≤ i₂ → (g i = 0%Rg))
  → (Σ (i = i₁, i₂), g i = 0%Rg).
Proof.
intros g i₁ i₂ H.
apply all_0_summation_aux_0.
intros i (H₁, H₂).
apply H.
split; [ easy | ].
destruct (le_dec i₁ (S i₂)) as [H₃| H₃].
 rewrite Nat.add_sub_assoc in H₂; lia.

 apply not_le_minus_0 in H₃.
 rewrite H₃, Nat.add_0_r in H₂.
 now apply Nat.nle_gt in H₂.
Qed.

Theorem summation_aux_mul_swap `{rg : ord_ring} : ∀ a g b len,
  summation_aux b len (λ i, a * g i)%Rg =
  (a * summation_aux b len g)%Rg.
Proof.
intros a g b len; revert b.
induction len; intros; simpl; [ now rewrite rng_mul_0_r | ].
rewrite IHlen, rng_mul_add_distr_l.
reflexivity.
Qed.

Theorem summation_aux_summation_aux_mul_swap `{rg : ord_ring} :
  ∀ g₁ g₂ g₃ b₁ b₂ len,
  (summation_aux b₁ len
     (λ i, summation_aux b₂ (g₁ i) (λ j, g₂ i * g₃ i j)%Rg)
   = summation_aux b₁ len
       (λ i, g₂ i * summation_aux b₂ (g₁ i) (λ j, g₃ i j))%Rg).
Proof.
intros g₁ g₂ g₃ b₁ b₂ len.
revert b₁ b₂.
induction len; intros; [ easy | simpl ].
rewrite IHlen.
apply rng_add_eq_compat; [ | easy ].
apply summation_aux_mul_swap.
Qed.

Theorem summation_summation_mul_swap `{rg : ord_ring} : ∀ g₁ g₂ g₃ k,
  Σ (i = 0, k), (Σ (j = 0, g₁ i), (g₂ i * g₃ i j)%Rg)
  = Σ (i = 0, k), (g₂ i * Σ (j = 0, g₁ i), g₃ i j)%Rg.
Proof.
intros g₁ g₂ g₃ k.
apply summation_aux_summation_aux_mul_swap.
Qed.

(*
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
*)

Theorem summation_summation_shift `{rg : ord_ring} : ∀ g k,
  Σ (i = 0, k), (Σ (j = i, k), g i j) =
  Σ (i = 0, k), Σ (j = 0, k - i), g i (i + j).
Proof.
intros g k.
apply summation_eq_compat; intros i Hi.
unfold summation.
rewrite Nat.sub_0_r.
rewrite Nat.sub_succ_l; [ | now destruct Hi ].
apply summation_aux_eq_compat; intros j Hj.
now rewrite Nat.add_0_l.
Qed.

Theorem summation_summation_exch `{rg : ord_ring} : ∀ g k,
  (Σ (j = 0, k), (Σ (i = 0, j), g i j) =
   Σ (i = 0, k), Σ (j = i, k), g i j).
Proof.
intros g k.
induction k; [ easy | ].
rewrite summation_split_last; [ | apply Nat.le_0_l ].
rewrite summation_split_last; [ | apply Nat.le_0_l ].
rewrite summation_split_last; [ | apply Nat.le_0_l ].
rewrite IHk.
rewrite summation_only_one.
rewrite rng_add_assoc.
apply rng_add_eq_compat; [ | easy ].
rewrite <- summation_add_distr.
apply summation_eq_compat; intros i (_, Hi).
rewrite summation_split_last; [ easy | ].
now apply Nat.le_le_succ_r.
Qed.

Theorem summation_aux_ub_add `{rg : ord_ring} : ∀ g b k₁ k₂,
  (summation_aux b (k₁ + k₂) g =
   summation_aux b k₁ g + summation_aux (b + k₁) k₂ g)%Rg.
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
 apply rng_add_eq_compat; [ | easy ].
 clear k₂ IHk₂.
 revert b.
 induction k₁; intros; simpl.
  rewrite Nat.add_0_r.
  apply rng_add_comm.

  rewrite <- rng_add_assoc.
  rewrite IHk₁.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l; reflexivity.
Qed.

Theorem summation_ub_add `{rg : ord_ring} : ∀ g b k k₁ k₂,
  b ≤ S k₁
  → k = k₁ + k₂
  → (Σ (i = b, k), g i =
     Σ (i = b, k₁), g i + Σ (i = S k₁, k), g i)%Rg.
Proof.
intros * Hbk Hk; subst k.
unfold summation.
rewrite <- Nat.add_succ_l.
rewrite Nat.add_sub_swap; [ | easy ].
rewrite summation_aux_ub_add; f_equal.
f_equal; lia.
Qed.

(*
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

Definition nat_ord_ring_def :=
  {| rng_t := nat;
     rng_zero := 0;
     rng_add := Nat.add;
     rng_sub := Nat.sub;
     rng_mul := Nat.mul;
     rng_le := Nat.le |}.

Canonical Structure nat_ord_ring_def.

Definition nat_ord_ring :=
  {| rng_add_0_l := Nat.add_0_l;
     rng_add_comm := Nat.add_comm;
     rng_add_assoc := Nat.add_assoc;
     rng_sub_diag := Nat.sub_diag;
     rng_mul_comm := Nat.mul_comm;
     rng_mul_assoc := Nat.mul_assoc;
     rng_mul_add_distr_l := Nat.mul_add_distr_l;
     rng_mul_sub_distr_l := λ a b c, Nat.mul_sub_distr_l b c a;
     rng_le_refl := Nat.le_refl;
     rng_le_antisymm := Nat.le_antisymm;
     rng_add_le_compat := Nat.add_le_mono |}.

Theorem eq_nat_summation_0 (rg := nat_ord_ring) : ∀ b e (g : _ → nat),
  Σ (i = b, e), g i = 0 → ∀ i, b ≤ i ≤ e → g i = 0.
Proof.
intros * Hs * (Hbi, Hie).
remember (e - b) as n eqn:Hn.
assert (H : e = b + n). {
  rewrite Hn, Nat.add_comm.
  rewrite Nat.sub_add; [ easy | ].
  now apply (le_trans _ i).
}
subst e; clear Hn.
rewrite summation_shift in Hs; [ | now apply (le_trans _ i)  ].
rewrite Nat.add_comm, Nat.add_sub in Hs.
revert i Hbi Hie.
induction n; intros.
-cbn in Hs; do 2 rewrite Nat.add_0_r in Hs.
 rewrite Nat.add_0_r in Hie.
 replace i with b; [ easy | now apply Nat.le_antisymm ].
-rewrite summation_split_last in Hs; [ | apply Nat.le_0_l ].
 apply Nat.eq_add_0 in Hs.
 destruct Hs as (Hs, Hgs).
 destruct (eq_nat_dec i (b + S n)) as [Hi| Hi]; [ now subst i | ].
 apply IHn; [ easy | easy | ].
 apply Nat.nlt_ge.
 intros H; apply Hi; clear Hi.
 apply Nat.le_antisymm; [ easy | ].
 rewrite Nat.add_succ_r; apply H.
Qed.
