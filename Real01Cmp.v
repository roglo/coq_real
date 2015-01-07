(* comparison in I *)

Require Import Utf8 QArith NPeano.
Require Import Real01Add.

Set Implicit Arguments.

Open Scope nat_scope.

Definition I_compare x y :=
  match fst_same (x + 0%I) (- (y + 0))%I 0 with
  | Some j => if (x + 0)%I.[j] then Gt else Lt
  | None => Eq
  end.

Definition I_lt x y := I_compare x y = Lt.
Definition I_le x y := I_compare x y ≠ Gt.
Definition I_gt x y := I_compare x y = Gt.
Definition I_ge x y := I_compare x y ≠ Lt.

Notation "x < y" := (I_lt x y) : I_scope.
Notation "x ≤ y" := (I_le x y) : I_scope.
Notation "x > y" := (I_gt x y) : I_scope.
Notation "x ≥ y" := (I_ge x y) : I_scope.
Notation "x ?= y" := (I_compare x y) : I_scope.

Theorem I_compare_eq : ∀ x y, (x = y)%I ↔ I_compare x y = Eq.
Proof.
intros x y.
split; intros H.
 unfold I_compare.
 unfold I_eq in H; simpl in H.
 remember (fst_same (x + 0%I) (- (y + 0)%I) 0) as s eqn:Hs .
 apply fst_same_sym_iff in Hs; simpl in Hs.
 destruct s as [j| ]; [ exfalso | reflexivity ].
 destruct Hs as (Hn, Hs).
 rewrite H in Hs.
 symmetry in Hs; revert Hs; apply no_fixpoint_negb.

 unfold I_compare in H.
 remember (fst_same (x + 0%I) (- (y + 0)%I) 0) as s eqn:Hs .
 apply fst_same_sym_iff in Hs; simpl in Hs.
 destruct s as [j| ]; [ exfalso | idtac ].
  destruct (x + 0)%I .[ j]; discriminate H.

  unfold I_eq; intros i; simpl.
  rewrite Hs, negb_involutive; reflexivity.
Qed.

Theorem I_compare_lt : ∀ x y, (x < y)%I ↔ I_compare x y = Lt.
Proof.
intros x y.
split; intros H; assumption.
Qed.

Theorem I_compare_gt : ∀ x y, (x > y)%I ↔ I_compare x y = Gt.
Proof.
intros x y.
split; intros H; assumption.
Qed.

Theorem I_gt_lt_iff : ∀ x y, (x > y)%I ↔ (y < x)%I.
Proof.
intros x y.
unfold I_gt, I_lt, I_compare; simpl.
remember (fst_same (x + 0%I) (- (y + 0)%I) 0) as s1 eqn:Hs1 .
remember (fst_same (y + 0%I) (- (x + 0)%I) 0) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [j1| ].
 destruct Hs1 as (Hs1, Hn1).
 remember (I_add_i x 0 j1) as x0 eqn:Hx0 .
 symmetry in Hx0; apply negb_sym in Hn1.
 destruct s2 as [j2| ].
  destruct Hs2 as (Hs2, Hn2).
  remember (I_add_i y 0 j2) as y0 eqn:Hy0 .
  symmetry in Hy0; apply negb_sym in Hn2.
  destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
   apply Hs2 in H1.
   rewrite negb_involutive, Hn1 in H1.
   rewrite Hx0 in H1.
   exfalso; revert H1; apply no_fixpoint_negb.

   subst j2.
   destruct x0.
    split; intros H; [ clear H | reflexivity ].
    destruct y0; [ exfalso | reflexivity ].
    rewrite Hx0 in Hn2; discriminate Hn2.

    split; intros H; [ discriminate H | exfalso ].
    destruct y0; [ discriminate H | clear H ].
    rewrite Hx0 in Hn2; discriminate Hn2.

   apply Hs1 in H1.
   rewrite negb_involutive, Hn2 in H1.
   rewrite Hy0 in H1.
   exfalso; revert H1; apply no_fixpoint_negb.

  split; intros H; [ exfalso | discriminate H ].
  destruct x0; [ clear H | discriminate H ].
  rewrite Hs2, Hx0 in Hn1; discriminate Hn1.

 destruct s2 as [j2| ].
  destruct Hs2 as (Hs2, Hn2).
  split; intros H; [ discriminate H | exfalso ].
  rewrite Hs1, negb_involutive in Hn2.
  symmetry in Hn2; revert Hn2; apply no_fixpoint_negb.

  split; intros H; discriminate H.
Qed.

Theorem I_ge_le_iff : ∀ x y, (x ≥ y)%I ↔ (y ≤ x)%I.
Proof.
intros x y.
unfold I_ge, I_le.
split; intros H1 H; apply H1; clear H1.
 apply I_gt_lt_iff; assumption.

 apply I_gt_lt_iff; assumption.
Qed.

(* inequality ≤ is order *)

Theorem I_le_refl : reflexive _ I_le.
Proof.
intros x H.
unfold I_compare in H; simpl in H.
remember (fst_same (x + 0%I) (- (x + 0)%I) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate H ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
symmetry in Ht1; revert Ht1; apply no_fixpoint_negb.
Qed.

Theorem I_le_antisym : Antisymmetric _ I_eq I_le.
Proof.
intros x y Hxy Hyx.
unfold I_le in Hxy, Hyx.
unfold I_compare in Hxy; simpl in Hxy.
unfold I_compare in Hyx; simpl in Hyx.
remember (fst_same (x + 0%I) (- (y + 0)%I) 0) as s1 eqn:Hs1 .
remember (fst_same (y + 0%I) (- (x + 0)%I) 0) as s2 eqn:Hs2 .
destruct s1 as [dj1| ]; [ idtac | clear Hxy ].
 remember (I_add_i x 0 dj1) as bx eqn:Hbx .
 symmetry in Hbx.
 destruct bx; [ exfalso; apply Hxy; reflexivity | clear Hxy ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Ht1).
 destruct s2 as [dj2| ]; [ idtac | clear Hyx ].
  remember (I_add_i y 0 dj2) as yb eqn:Hby .
  symmetry in Hby.
  destruct yb; [ exfalso; apply Hyx; reflexivity | clear Hyx ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  destruct (lt_eq_lt_dec dj1 dj2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H; rewrite negb_involutive in H.
   rewrite Ht1 in H; symmetry in H.
   exfalso; revert H; apply no_fixpoint_negb.

   subst dj2.
   rewrite Hbx, Hby in Ht1; discriminate Ht1.

   remember H1 as H; clear HeqH.
   apply Hn1 in H; rewrite negb_involutive in H.
   rewrite Ht2 in H; symmetry in H.
   exfalso; revert H; apply no_fixpoint_negb.

  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  rewrite Hs2 in Ht1.
  rewrite negb_involutive in Ht1; symmetry in Ht1.
  exfalso; revert Ht1; apply no_fixpoint_negb.

 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 unfold I_eq; simpl; intros i.
 rewrite Hs1, negb_involutive.
 reflexivity.
Qed.

Theorem I_le_trans : transitive _ I_le.
Proof.
intros x y z Hxy Hyz.
unfold I_le in Hxy, Hyz; unfold I_le.
unfold I_compare in Hxy, Hyz; unfold I_compare.
simpl in Hxy, Hyz; simpl.
remember (fst_same (x + 0%I) (- (y + 0)%I) 0) as s1 eqn:Hs1 .
remember (fst_same (y + 0%I) (- (z + 0)%I) 0) as s2 eqn:Hs2 .
remember (fst_same (x + 0%I) (- (z + 0)%I) 0) as s3 eqn:Hs3 .
destruct s3 as [dj3| ]; [ idtac | intros H; discriminate H ].
remember (I_add_i x 0 dj3) as b3 eqn:Hb3 .
symmetry in Hb3.
destruct b3; [ exfalso | intros H; discriminate H ].
apply fst_same_sym_iff in Hs3; simpl in Hs3.
destruct Hs3 as (Hn3, Ht3).
rewrite Hb3 in Ht3; apply negb_sym in Ht3; simpl in Ht3.
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [dj1| ]; [ idtac | clear Hxy ].
 destruct Hs1 as (Hn1, Ht1).
 remember (I_add_i x 0 dj1) as b1 eqn:Hb1 .
 symmetry in Hb1.
 apply negb_sym in Ht1.
 destruct b1; [ apply Hxy; reflexivity | clear Hxy ].
 simpl in Ht1.
 destruct s2 as [dj2| ]; [ idtac | clear Hyz ].
  destruct Hs2 as (Hn2, Ht2).
  remember (I_add_i y 0 dj2) as b2 eqn:Hb2 .
  symmetry in Hb2.
  apply negb_sym in Ht2.
  destruct b2; [ apply Hyz; reflexivity | clear Hyz ].
  simpl in Ht2.
  destruct (lt_eq_lt_dec dj1 dj2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   rewrite negb_involutive in H.
   rename H into Hyz.
   destruct (lt_eq_lt_dec dj1 dj3) as [[H2| H2]| H2].
    remember H2 as H; clear HeqH.
    apply Hn3 in H.
    rewrite negb_involutive in H.
    rewrite <- Hyz, Hb1, Ht1 in H.
    discriminate H.

    subst dj3.
    rewrite Hb1 in Hb3; discriminate Hb3.

    remember H2 as H; clear HeqH.
    apply Hn1 in H.
    rewrite negb_involutive in H.
    apply Nat.lt_trans with (n := dj3) in H1; [ idtac | assumption ].
    remember H1 as HH; clear HeqHH.
    apply Hn2 in HH.
    rewrite negb_involutive in HH.
    rewrite Hb3, HH, Ht3 in H.
    discriminate H.

   subst dj2.
   rewrite Ht1 in Hb2; discriminate Hb2.

   remember H1 as H; clear HeqH.
   apply Hn1 in H; simpl in H.
   rewrite negb_involutive in H.
   rename H into Hxy.
   destruct (lt_eq_lt_dec dj2 dj3) as [[H2| H2]| H2].
    remember H2 as H; clear HeqH.
    apply Hn3 in H.
    rewrite negb_involutive in H.
    rewrite Hxy, Hb2, Ht2 in H.
    discriminate H.

    subst dj3.
    rewrite Ht2 in Ht3; discriminate Ht3.

    remember H2 as H; clear HeqH.
    apply Hn2 in H; simpl in H.
    rewrite negb_involutive in H.
    rename H into Hyz.
    remember H1 as H; clear HeqH.
    apply Nat.lt_trans with (n := dj3) in H; [ idtac | assumption ].
    apply Hn1 in H.
    rewrite negb_involutive in H.
    rewrite Hb3, Hyz, Ht3 in H.
    discriminate H.

  destruct (lt_eq_lt_dec dj1 dj3) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn3 in H.
   rewrite Hb1, <- Hs2, Ht1 in H.
   discriminate H.

   subst dj3.
   rewrite Hb1 in Hb3; discriminate Hb3.

   remember H1 as H; clear HeqH.
   apply Hn1 in H.
   rewrite Hb3, Hs2, Ht3 in H.
   discriminate H.

 destruct s2 as [dj2| ]; [ idtac | clear Hyz ].
  remember (I_add_i y 0 dj2) as b2 eqn:Hb2 .
  destruct Hs2 as (Hn2, Ht2).
  symmetry in Hb2.
  apply negb_sym in Ht2.
  destruct b2; [ apply Hyz; reflexivity | clear Hyz ].
  simpl in Ht2.
  destruct (lt_eq_lt_dec dj2 dj3) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn3 in H.
   rewrite Hs1, Hb2, Ht2 in H.
   discriminate H.

   subst dj3.
   rewrite Ht2 in Ht3; discriminate Ht3.

   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   apply negb_sym in H; symmetry in H.
   apply negb_sym in H.
   rewrite Ht3, <- Hs1, Hb3 in H.
   discriminate H.

  rewrite Hs1, Hs2, Ht3 in Hb3.
  discriminate Hb3.
Qed.

(* inequality ≥ is order *)

Theorem I_ge_refl : reflexive _ I_ge.
Proof.
intros x H.
unfold I_compare in H; simpl in H.
remember (fst_same (x + 0%I) (- (x + 0)%I) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate H ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
symmetry in Ht1; revert Ht1; apply no_fixpoint_negb.
Qed.

Theorem I_ge_antisym : Antisymmetric _ I_eq I_ge.
Proof.
intros x y Hxy Hyx.
apply I_le_antisym; intros H.
 apply I_gt_lt_iff in H; contradiction.

 apply I_gt_lt_iff in H; contradiction.
Qed.

Theorem I_ge_trans : transitive _ I_ge.
Proof.
intros x y z Hxy Hyz H.
apply I_gt_lt_iff in H.
revert H.
apply I_le_trans with (y := y); intros H.
 apply I_gt_lt_iff in H; contradiction.

 apply I_gt_lt_iff in H; contradiction.
Qed.

(* decidability < vs ≥ and > vs ≤ *)

Theorem I_lt_dec : ∀ x y, {(x < y)%I} + {(x ≥ y)%I}.
Proof.
intros x y.
unfold I_lt, I_ge; simpl.
unfold I_compare; simpl.
remember (fst_same (x + 0%I) (- (y + 0))%I 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Ht).
 remember (I_add_i x 0 di) as xb eqn:Hxb .
 symmetry in Hxb; apply negb_sym in Ht.
 destruct xb; simpl in Ht.
  right; intros H; discriminate H.

  left; reflexivity.

 right; intros H; discriminate H.
Qed.

Theorem I_gt_dec : ∀ x y, {(x > y)%I} + {(x ≤ y)%I}.
Proof.
intros x y.
destruct (I_lt_dec y x) as [H1| H1].
 left.
 apply I_gt_lt_iff; assumption.

 right; intros H; apply H1.
 apply I_gt_lt_iff; assumption.
Qed.

(* *)

Theorem I_lt_decidable : ∀ x y, Decidable.decidable (x < y)%I.
Proof.
intros x y.
destruct (I_lt_dec x y); [ left | right ]; assumption.
Qed.

Theorem I_gt_decidable : ∀ x y, Decidable.decidable (x > y)%I.
Proof.
intros x y.
destruct (I_gt_dec x y); [ left | right ]; assumption.
Qed.

Theorem I_eq_compare_compat : ∀ x y z t,
  (x = y)%I
  → (z = t)%I
  → ((x ?= z)%I = (y ?= t)%I).
Proof.
intros x y z t Hxy Hzt.
unfold I_eq in Hxy; simpl in Hxy.
unfold I_eq in Hzt; simpl in Hzt.
unfold I_compare; simpl.
remember (fst_same (x + 0%I) (- (z + 0)%I) 0) as s1 eqn:Hs1 .
remember (fst_same (y + 0%I) (- (t + 0)%I) 0) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [j1| ].
 destruct Hs1 as (Hn1, Ht1).
 remember (I_add_i x 0 j1) as b1 eqn:Hb1 .
 symmetry in Hb1; apply negb_sym in Ht1.
 destruct s2 as [j2| ].
  destruct Hs2 as (Hn2, Ht2).
  remember (I_add_i y 0 j2) as b2 eqn:Hb2 .
  symmetry in Hb2; apply negb_sym in Ht2.
  destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   rewrite negb_involutive in H.
   rewrite <- Hxy, <- Hzt, Hb1, Ht1 in H.
   symmetry in H.
   exfalso; revert H; apply no_fixpoint_negb.

   subst j2.
   rewrite Hxy, Hb2 in Hb1.
   subst b2; reflexivity.

   remember H1 as H; clear HeqH.
   apply Hn1 in H.
   rewrite negb_involutive in H.
   rewrite Hxy, Hzt, Hb2, Ht2 in H.
   symmetry in H.
   exfalso; revert H; apply no_fixpoint_negb.

  rewrite Hxy, Hs2 in Hb1.
  rewrite negb_involutive in Hb1.
  rewrite Hzt in Ht1.
  rewrite Ht1 in Hb1.
  exfalso; revert Hb1; apply no_fixpoint_negb.

 destruct s2 as [j2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Ht2).
 rewrite <- Hxy, Hs1 in Ht2.
 rewrite negb_involutive in Ht2.
 symmetry in Ht2.
 rewrite Hzt in Ht2.
 exfalso; revert Ht2; apply no_fixpoint_negb.
Qed.

Theorem I_eq_lt_compat : ∀ x y z t,
  (x = y)%I
  → (z = t)%I
  → (x < z)%I
  → (y < t)%I.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold I_lt in Hxz; unfold I_lt.
rewrite <- Hxz; symmetry.
apply I_eq_compare_compat; eassumption.
Qed.

Theorem I_eq_le_compat : ∀ x y z t,
  (x = y)%I
  → (z = t)%I
  → (x ≤ z)%I
  → (y ≤ t)%I.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold I_le in Hxz; unfold I_le.
intros H; apply Hxz; rewrite <- H.
apply I_eq_compare_compat; eassumption.
Qed.

Theorem I_eq_gt_compat : ∀ x y z t,
  (x = y)%I
  → (z = t)%I
  → (x > z)%I
  → (y > t)%I.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold I_gt in Hxz; unfold I_gt.
rewrite <- Hxz; symmetry.
apply I_eq_compare_compat; eassumption.
Qed.

Theorem I_eq_ge_compat : ∀ x y z t,
  (x = y)%I
  → (z = t)%I
  → (x ≥ z)%I
  → (y ≥ t)%I.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold I_ge in Hxz; unfold I_ge.
intros H; apply Hxz; rewrite <- H.
apply I_eq_compare_compat; eassumption.
Qed.

(* morphisms *)

Add Parametric Morphism : I_lt
  with signature I_eq ==> I_eq ==> iff
  as I_lt_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply I_eq_lt_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply I_eq_lt_compat; eassumption.
Qed.

Add Parametric Morphism : I_le
  with signature I_eq ==> I_eq ==> iff
  as I_le_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply I_eq_le_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply I_eq_le_compat; eassumption.
Qed.

Add Parametric Morphism : I_gt
  with signature I_eq ==> I_eq ==> iff
  as I_gt_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply I_eq_gt_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply I_eq_gt_compat; eassumption.
Qed.

Add Parametric Morphism : I_ge
  with signature I_eq ==> I_eq ==> iff
  as I_ge_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply I_eq_ge_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply I_eq_ge_compat; eassumption.
Qed.

(* miscellaneous *)

Theorem I_le_0_r : ∀ x, (x ≤ 0)%I ↔ (x = 0)%I.
Proof.
intros x.
split; intros H.
 unfold I_le in H; simpl in H.
 unfold I_eq; intros i; simpl.
 unfold I_compare in H; simpl in H.
 remember (fst_same (x + 0%I) (- (0 + 0)%I) 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [j1| ].
  destruct Hs1 as (Hn1, Ht1).
  remember (I_add_i x 0 j1) as b1 eqn:Hb1 .
  destruct b1; [ exfalso; apply H; reflexivity | clear H ].
  symmetry in Hb1; apply negb_sym in Ht1; simpl in Ht1.
  unfold I_add_i in Ht1; simpl in Ht1.
  rewrite carry_diag in Ht1; discriminate Ht1.

  rewrite Hs1, negb_involutive; reflexivity.

 unfold I_eq in H; simpl in H.
 unfold I_le; simpl.
 unfold I_compare; simpl.
 remember (fst_same (x + 0%I) (- (0 + 0)%I) 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [j1| ]; [ idtac | intros HH; discriminate HH ].
 destruct Hs1 as (Hn1, Ht1).
 remember (I_add_i x 0 j1) as b1 eqn:Hb1 .
 destruct b1; [ exfalso | intros HH; discriminate HH ].
 symmetry in Hb1; apply negb_sym in Ht1; simpl in Ht1.
 rewrite H, Ht1 in Hb1; discriminate Hb1.
Qed.

Theorem I_lt_nge : ∀ x y, (x < y)%I ↔ ¬(y ≤ x)%I.
Proof.
intros x y.
unfold I_lt, I_le.
unfold I_compare; simpl.
remember (fst_same (y + 0%I) (- (x + 0)%I) 0) as s1 eqn:Hs1 .
remember (fst_same (x + 0%I) (- (y + 0)%I) 0) as s2 eqn:Hs2 .
split; intros H.
 intros HH; apply HH; clear HH.
 destruct s2 as [j2| ]; [ idtac | discriminate H ].
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct Hs2 as (Hn2, Ht2).
 remember (I_add_i x 0 j2) as b2 eqn:Hb2 .
 symmetry in Hb2; apply negb_sym in Ht2.
 destruct b2; [ discriminate H | clear H; simpl in Ht2 ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [j1| ]; [ idtac | exfalso ].
  destruct Hs1 as (Hn1, Ht1).
  remember (I_add_i y 0 j1) as b1 eqn:Hb1 .
  symmetry in Hb1; apply negb_sym in Ht1.
  destruct b1; [ reflexivity | exfalso; simpl in Ht1 ].
  destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   rewrite Ht1, Hb1 in H; discriminate H.

   subst j2.
   rewrite Hb1 in Ht2; discriminate Ht2.

   remember H1 as H; clear HeqH.
   apply Hn1 in H.
   rewrite Ht2, Hb2 in H; discriminate H.

  rewrite Hs1, Hb2 in Ht2; discriminate Ht2.

 destruct s1 as [j1| ].
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, Ht1).
  remember (I_add_i y 0 j1) as b1 eqn:Hb1 .
  symmetry in Hb1; apply negb_sym in Ht1.
  destruct b1; [ clear H | exfalso; apply H; intros HH; discriminate HH ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s2 as [j2| ].
   destruct Hs2 as (Hn2, Ht2).
   remember (I_add_i x 0 j2) as b2 eqn:Hb2 .
   symmetry in Hb2; apply negb_sym in Ht2.
   destruct b2; [ exfalso | reflexivity ].
   destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
    remember H1 as H; clear HeqH.
    apply Hn2 in H.
    rewrite Ht1, Hb1 in H; discriminate H.

    subst j2.
    rewrite Hb1 in Ht2; discriminate Ht2.

    remember H1 as H; clear HeqH.
    apply Hn1 in H.
    rewrite Ht2, Hb2 in H; discriminate H.

   rewrite Hs2, Hb1 in Ht1; discriminate Ht1.

  exfalso; apply H; intros HH; discriminate HH.
Qed.

Theorem I_lt_irrefl : ∀ x, ¬(x < x)%I.
Proof.
intros x Hx.
unfold I_lt, I_compare in Hx; simpl in Hx.
remember (fst_same (x + 0%I) (- (x + 0)%I) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate Hx ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
symmetry in Ht1.
revert Ht1; apply no_fixpoint_negb.
Qed.

Close Scope nat_scope.
