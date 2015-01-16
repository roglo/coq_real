(* comparison in I *)

Require Import Utf8 QArith NPeano.
Require Import Real01Add.

Set Implicit Arguments.

Open Scope nat_scope.

Definition I_compare x y :=
  match fst_same x (- y)%I 0 with
  | Some j => if x.[j] then Gt else Lt
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

Definition I_eqs x y := I_compare x y = Eq.
Notation "x == y" := (I_eqs x y) : I_scope.
Notation "x ≠≠ y" := (¬ I_eqs x y) (at level 70, no associativity) : I_scope.

Theorem I_eqs_eq : ∀ x y, (x == y)%I → (x = y)%I.
Proof.
intros x y H.
unfold I_eqs, I_compare in H.
remember (fst_same x (- y) 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [j| ]; [ exfalso | idtac ].
 destruct (x .[ j]); discriminate H.

 unfold I_eq; intros i; simpl.
 unfold I_add_i; simpl.
 rewrite Hs, negb_involutive; f_equal.
 apply carry_compat_r; intros j.
 rewrite Hs, negb_involutive; reflexivity.
Qed.

Theorem I_compare_eqs : ∀ x y, (x == y)%I ↔ I_compare x y = Eq.
Proof.
intros x y.
split; intros H; assumption.
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
remember (fst_same x (- y) 0) as s1 eqn:Hs1 .
remember (fst_same y (- x) 0) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [j1| ].
 destruct Hs1 as (Hs1, Hn1).
 destruct s2 as [j2| ].
  destruct Hs2 as (Hs2, Hn2).
  destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
   apply Hs2 in H1.
   rewrite negb_involutive, Hn1 in H1; symmetry in H1.
   exfalso; revert H1; apply no_fixpoint_negb.

   subst j2; rewrite Hn1.
   split; intros H.
    destruct (y .[ j1]); [ discriminate H | reflexivity ].

    destruct (y .[ j1]); [ discriminate H | reflexivity ].

   apply Hs1 in H1.
   rewrite negb_involutive, Hn2 in H1.
   symmetry in H1.
   exfalso; revert H1; apply no_fixpoint_negb.

  split; intros H; [ exfalso | discriminate H ].
  rewrite Hs2, negb_involutive in Hn1.
  symmetry in Hn1.
  revert Hn1; apply no_fixpoint_negb.

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

(* strong equality == is equivalence relation *)

Theorem I_eqs_refl : reflexive _ I_eqs.
Proof.
intros x.
unfold I_eqs, I_compare.
remember (fst_same x (- x) 0) as s eqn:Hs .
destruct s as [j| ]; [ idtac | reflexivity ].
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct Hs as (Hn, Hs).
symmetry in Hs.
exfalso; revert Hs; apply no_fixpoint_negb.
Qed.

Theorem I_eqs_sym : symmetric _ I_eqs.
Proof.
intros x y Hxy.
unfold I_eqs, I_compare in Hxy.
unfold I_eqs, I_compare.
remember (fst_same x (- y) 0) as s1 eqn:Hs1 .
remember (fst_same y (- x) 0) as s2 eqn:Hs2 .
destruct s1 as [dj1| ]; [ idtac | clear Hxy ].
 destruct (x .[ dj1]); discriminate Hxy.

 destruct s2 as [dj2| ]; [ exfalso | reflexivity ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct Hs2 as (Hn2, Ht2).
 rewrite Hs1, negb_involutive in Ht2.
 symmetry in Ht2.
 revert Ht2; apply no_fixpoint_negb.
Qed.

Theorem I_eqs_trans : transitive _ I_eqs.
Proof.
intros x y z Hxy Hyz.
unfold I_eqs in Hxy, Hyz; unfold I_eqs.
unfold I_compare in Hxy, Hyz; unfold I_compare.
remember (fst_same x (- y) 0) as s1 eqn:Hs1 .
remember (fst_same y (- z) 0) as s2 eqn:Hs2 .
remember (fst_same x (- z) 0) as s3 eqn:Hs3 .
destruct s3 as [dj3| ]; [ exfalso | reflexivity ].
apply fst_same_sym_iff in Hs3; simpl in Hs3.
destruct Hs3 as (Hn3, Ht3).
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [j| ]; [ destruct (x .[ j]); discriminate Hxy | clear Hxy ].
destruct s2 as [j| ]; [ destruct (y .[ j]); discriminate Hyz | clear Hyz ].
rewrite Hs1, Hs2, negb_involutive in Ht3.
rewrite negb_involutive in Ht3; symmetry in Ht3.
revert Ht3; apply no_fixpoint_negb.
Qed.

Add Parametric Relation : _ I_eqs
 reflexivity proved by I_eqs_refl
 symmetry proved by I_eqs_sym
 transitivity proved by I_eqs_trans
 as I_rels.

(* inequality ≤ is order *)

Theorem I_le_refl : reflexive _ I_le.
Proof.
intros x H.
unfold I_compare in H; simpl in H.
remember (fst_same x (- x) 0) as s1 eqn:Hs1 .
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
remember (fst_same x (- y) 0) as s1 eqn:Hs1 .
remember (fst_same y (- x) 0) as s2 eqn:Hs2 .
destruct s1 as [dj1| ]; [ idtac | clear Hxy ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Ht1).
 destruct s2 as [dj2| ]; [ idtac | clear Hyx ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  destruct (lt_eq_lt_dec dj1 dj2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H; rewrite negb_involutive in H.
   rewrite Ht1 in H; symmetry in H.
   exfalso; revert H; apply no_fixpoint_negb.

   subst dj2.
   destruct (x .[ dj1]); [ exfalso; apply Hxy; reflexivity | idtac ].
   destruct (y .[ dj1]); [ exfalso; apply Hyx; reflexivity | idtac ].
   discriminate Ht1.

   remember H1 as H; clear HeqH.
   apply Hn1 in H; rewrite negb_involutive in H.
   rewrite Ht2 in H; symmetry in H.
   exfalso; revert H; apply no_fixpoint_negb.

  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  rewrite Hs2 in Ht1.
  rewrite negb_involutive in Ht1; symmetry in Ht1.
  exfalso; revert Ht1; apply no_fixpoint_negb.

 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s2 as [dj2| ]; [ idtac | clear Hyx ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  rewrite Hs1, negb_involutive in Ht2.
  symmetry in Ht2.
  exfalso; revert Ht2; apply no_fixpoint_negb.

  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  unfold I_eq; simpl; intros i.
  unfold I_add_i; simpl.
  rewrite Hs1, negb_involutive; f_equal.
  apply carry_compat_r; intros j.
  rewrite Hs1, negb_involutive; reflexivity.
Qed.

Theorem I_le_trans_trans : transitive _ I_le.
Proof.
intros x y z Hxy Hyz.
unfold I_le in Hxy, Hyz; unfold I_le.
unfold I_compare in Hxy, Hyz; unfold I_compare.
simpl in Hxy, Hyz; simpl.
remember (fst_same x (- y) 0) as s1 eqn:Hs1 .
remember (fst_same y (- z) 0) as s2 eqn:Hs2 .
remember (fst_same x (- z) 0) as s3 eqn:Hs3 .
destruct s3 as [dj3| ]; [ idtac | intros H; discriminate H ].
apply fst_same_sym_iff in Hs3; simpl in Hs3.
destruct Hs3 as (Hn3, Ht3).
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
remember (x .[ dj3]) as x3 eqn:Hx3 .
destruct x3; [ idtac | intros H; discriminate H ].
symmetry in Hx3, Ht3.
apply negb_true_iff in Ht3.
exfalso.
destruct s1 as [dj1| ]; [ idtac | clear Hxy ].
 destruct Hs1 as (Hn1, Ht1).
 remember (x .[ dj1]) as x1 eqn:Hx1 .
 destruct x1; [ apply Hxy; reflexivity | clear Hxy ].
 destruct s2 as [dj2| ]; [ idtac | clear Hyz ].
  destruct Hs2 as (Hn2, Ht2).
  remember (y .[ dj2]) as y2 eqn:Hy2 .
  destruct y2; [ apply Hyz; reflexivity | clear Hyz ].
  destruct (lt_eq_lt_dec dj1 dj2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   rewrite negb_involutive in H.
   destruct (lt_eq_lt_dec dj1 dj3) as [[H2| H2]| H2].
    apply Hn3 in H2.
    rewrite <- Hx1, <- H, <- Ht1 in H2.
    discriminate H2.

    subst dj3.
    rewrite <- Hx1 in Hx3; discriminate Hx3.

    rename H into Hyz.
    remember H2 as H; clear HeqH.
    apply Hn1 in H.
    apply Nat.lt_trans with (n := dj3) in H1; [ idtac | assumption ].
    remember H1 as HH; clear HeqHH.
    apply Hn2 in HH.
    rewrite Hx3, HH, Ht3 in H.
    discriminate H.

   subst dj2.
   rewrite <- Hy2 in Ht1; discriminate Ht1.

   remember H1 as H; clear HeqH.
   apply Hn1 in H; simpl in H.
   rename H into Hxy.
   destruct (lt_eq_lt_dec dj2 dj3) as [[H2| H2]| H2].
    remember H2 as H; clear HeqH.
    apply Hn3 in H.
    rewrite Hxy, <- Hy2, <- Ht2 in H.
    discriminate H.

    subst dj3.
    rewrite Ht3 in Ht2; discriminate Ht2.

    remember H2 as H; clear HeqH.
    apply Hn2 in H; simpl in H.
    rewrite Ht3 in H.
    apply Nat.lt_trans with (n := dj3) in H1; [ idtac | assumption ].
    apply Hn1 in H1.
    rewrite Hx3, H in H1.
    discriminate H1.

  destruct (lt_eq_lt_dec dj1 dj3) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn3 in H.
   rewrite <- Hx1, <- Hs2 in H.
   rewrite <- H in Ht1; discriminate Ht1.

   subst dj3.
   rewrite Hx3 in Hx1; discriminate Hx1.

   remember H1 as H; clear HeqH.
   apply Hn1 in H.
   rewrite Hx3, Hs2, Ht3 in H; discriminate H.

 rewrite Hs1 in Hx3.
 destruct s2 as [dj2| ]; [ idtac | clear Hyz ].
  destruct Hs2 as (Hn2, Ht2).
  remember (y .[ dj2]) as y2 eqn:Hy2 .
  destruct y2; [ apply Hyz; reflexivity | clear Hyz ].
  destruct (lt_eq_lt_dec dj2 dj3) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn3 in H.
   rewrite Hs1, <- Hy2, <- Ht2 in H; discriminate H.

   subst dj3.
   rewrite Ht3 in Ht2; discriminate Ht2.

   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   rewrite H, Ht3 in Hx3; discriminate Hx3.

  rewrite Hs2, Ht3 in Hx3; discriminate Hx3.
Qed.

Theorem I_le_trans : ∀ x y z, (x ≤ y)%I → (y ≤ z)%I → (x ≤ z)%I.
Proof. intros; eapply I_le_trans_trans; eassumption. Qed.

(* inequality ≥ is order *)

Theorem I_ge_refl : reflexive _ I_ge.
Proof.
intros x H.
unfold I_compare in H; simpl in H.
remember (fst_same x (- x) 0) as s1 eqn:Hs1 .
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

(* decidability == *)

Theorem I_eqs_dec : ∀ x y, {(x == y)%I} + {(x ≠≠ y)%I}.
Proof.
intros x y.
unfold I_eqs; simpl.
unfold I_compare; simpl.
remember (fst_same x (- y) 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 right; destruct (x .[ di]); intros H; discriminate H.

 left; reflexivity.
Qed.

(* decidability < vs ≥ and > vs ≤ *)

Theorem I_lt_dec : ∀ x y, {(x < y)%I} + {(x ≥ y)%I}.
Proof.
intros x y.
unfold I_lt, I_ge; simpl.
unfold I_compare; simpl.
remember (fst_same x (- y) 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct (x .[ di]).
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

Theorem I_eqs_compare_compat : ∀ x y z t,
  (x == y)%I
  → (z == t)%I
  → ((x ?= z)%I = (y ?= t)%I).
Proof.
intros x y z t Hxy Hzt.
unfold I_eqs, I_compare in Hxy; simpl in Hxy.
unfold I_eqs, I_compare in Hzt; simpl in Hzt.
unfold I_compare; simpl.
remember (fst_same x (- z) 0) as s1 eqn:Hs1 .
remember (fst_same y (- t) 0) as s2 eqn:Hs2 .
remember (fst_same x (- y) 0) as s3 eqn:Hs3 .
remember (fst_same z (- t) 0) as s4 eqn:Hs4 .
destruct s3 as [j| ]; [ destruct (x .[ j]); discriminate Hxy | clear Hxy ].
destruct s4 as [j| ]; [ destruct (z .[ j]); discriminate Hzt | clear Hzt ].
apply fst_same_sym_iff in Hs3; simpl in Hs3.
apply fst_same_sym_iff in Hs4; simpl in Hs4.
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [j1| ].
 destruct Hs1 as (Hn1, Ht1).
 destruct s2 as [j2| ].
  destruct Hs2 as (Hn2, Ht2).
  rewrite Hs3, negb_involutive.
  destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   rewrite Hs3, H, <- Hs4, negb_involutive in Ht1.
   symmetry in Ht1.
   exfalso; revert Ht1; apply no_fixpoint_negb.

   subst j2; reflexivity.

   remember H1 as H; clear HeqH.
   apply Hn1 in H.
   rewrite Hs3, Hs4, <- Ht2, negb_involutive in H.
   symmetry in H.
   exfalso; revert H; apply no_fixpoint_negb.

  rewrite Hs3, Hs4, <- Hs2, negb_involutive in Ht1.
  symmetry in Ht1.
  exfalso; revert Ht1; apply no_fixpoint_negb.

 destruct s2 as [dj2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Ht2).
 rewrite <- negb_involutive, <- Hs4 in Ht2.
 rewrite <- negb_involutive, <- Hs1 in Ht2.
 rewrite Hs3, negb_involutive in Ht2.
 symmetry in Ht2.
 exfalso; revert Ht2; apply no_fixpoint_negb.
Qed.

Theorem I_eqs_lt_compat : ∀ x y z t,
  (x == y)%I
  → (z == t)%I
  → (x < z)%I
  → (y < t)%I.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold I_lt in Hxz; unfold I_lt.
rewrite <- Hxz; symmetry.
apply I_eqs_compare_compat; eassumption.
Qed.

Theorem I_eqs_le_compat : ∀ x y z t,
  (x == y)%I
  → (z == t)%I
  → (x ≤ z)%I
  → (y ≤ t)%I.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold I_le in Hxz; unfold I_le.
intros H; apply Hxz; rewrite <- H.
apply I_eqs_compare_compat; eassumption.
Qed.

Theorem I_eqs_gt_compat : ∀ x y z t,
  (x == y)%I
  → (z == t)%I
  → (x > z)%I
  → (y > t)%I.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold I_gt in Hxz; unfold I_gt.
rewrite <- Hxz; symmetry.
apply I_eqs_compare_compat; eassumption.
Qed.

Theorem I_eqs_ge_compat : ∀ x y z t,
  (x == y)%I
  → (z == t)%I
  → (x ≥ z)%I
  → (y ≥ t)%I.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold I_ge in Hxz; unfold I_ge.
intros H; apply Hxz; rewrite <- H.
apply I_eqs_compare_compat; eassumption.
Qed.

(* morphisms *)

Add Parametric Morphism : I_lt
  with signature I_eqs ==> I_eqs ==> iff
  as I_lt_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply I_eqs_lt_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply I_eqs_lt_compat; eassumption.
Qed.

Add Parametric Morphism : I_le
  with signature I_eqs ==> I_eqs ==> iff
  as I_le_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply I_eqs_le_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply I_eqs_le_compat; eassumption.
Qed.

Add Parametric Morphism : I_gt
  with signature I_eqs ==> I_eqs ==> iff
  as I_gt_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply I_eqs_gt_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply I_eqs_gt_compat; eassumption.
Qed.

Add Parametric Morphism : I_ge
  with signature I_eqs ==> I_eqs ==> iff
  as I_ge_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply I_eqs_ge_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply I_eqs_ge_compat; eassumption.
Qed.

(* miscellaneous *)

Theorem I_le_0_r : ∀ x, (x ≤ 0)%I → (x = 0)%I.
Proof.
intros x H.
unfold I_le in H; simpl in H.
unfold I_eq; intros i; simpl.
unfold I_compare in H; simpl in H.
remember (fst_same x (- 0%I) 0) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [j1| ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1 in H; exfalso; apply H; reflexivity.

 unfold I_add_i; simpl.
 rewrite Hs1, <- xorb_false_r, carry_diag; simpl.
 unfold carry; simpl.
 remember (fst_same x 0 (S i)) as s2 eqn:Hs2 .
 destruct s2 as [dj2| ].
  rewrite Hs1; reflexivity.

  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  clear H.
  pose proof (Hs2 O) as H.
  rewrite Hs1 in H; discriminate H.
Qed.

Theorem I_le_0_r_eqs_iff : ∀ x, (x ≤ 0)%I ↔ (x == 0)%I.
Proof.
intros x.
split; intros H.
 unfold I_le, I_compare in H; simpl in H.
 unfold I_eqs, I_compare; simpl.
 remember (fst_same x (- 0%I) 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [j1| ]; [ idtac | reflexivity ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1 in H.
 exfalso; apply H; reflexivity.

 rewrite H; apply I_le_refl.
Qed.

Theorem I_ge_0_l_eqs_iff : ∀ x, (0 ≥ x)%I ↔ (x == 0)%I.
Proof.
intros x.
rewrite I_ge_le_iff.
apply I_le_0_r_eqs_iff.
Qed.

Theorem I_lt_nle : ∀ x y, (x < y)%I ↔ ¬(y ≤ x)%I.
Proof.
intros x y.
unfold I_lt, I_le.
unfold I_compare; simpl.
remember (fst_same y (- x) 0) as s1 eqn:Hs1 .
remember (fst_same x (- y) 0) as s2 eqn:Hs2 .
split; intros H.
 intros HH; apply HH; clear HH.
 destruct s2 as [j2| ]; [ idtac | discriminate H ].
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct Hs2 as (Hn2, Ht2).
 remember (x .[ j2]) as b eqn:Hx2 .
 destruct b; [ discriminate H | clear H ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [j1| ]; [ idtac | exfalso ].
  destruct Hs1 as (Hn1, Ht1).
  remember (y .[ j1]) as y1 eqn:Hy1 .
  destruct y1; [ reflexivity | exfalso ].
  destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2, negb_sym in H.
   rewrite <- Hy1, <- Ht1 in H; discriminate H.

   subst j2.
   rewrite <- Hy1 in Ht2; discriminate Ht2.

   remember H1 as H; clear HeqH.
   apply Hn1, negb_sym in H.
   rewrite <- Hx2, <- Ht2 in H; discriminate H.

  rewrite Hs1, <- Hx2 in Ht2; discriminate Ht2.

 destruct s1 as [j1| ].
  remember (y .[ j1]) as y1 eqn:Hy1 .
  destruct y1; [ idtac | exfalso; apply H; intros I; discriminate I ].
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, Ht1).
  clear H.
  destruct s2 as [j2| ].
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   remember (x .[ j2]) as x2 eqn:Hx2 .
   destruct x2; [ exfalso | reflexivity ].
   destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
    remember H1 as H; clear HeqH.
    apply Hn2 in H.
    apply negb_sym in H.
    rewrite <- Ht1, <- Hy1 in H; discriminate H.

    subst j2.
    rewrite <- Hy1 in Ht2; discriminate Ht2.

    remember H1 as H; clear HeqH.
    apply Hn1 in H.
    apply negb_sym in H.
    rewrite <- Hx2, <- Ht2 in H; discriminate H.

   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   rewrite Hs2, <- Hy1 in Ht1; discriminate Ht1.

  exfalso; apply H; intros I; discriminate I.
Qed.

Theorem I_lt_nge : ∀ x y, (x < y)%I ↔ ¬(x ≥ y)%I.
Proof.
intros x y.
split; intros H.
 apply I_lt_nle in H.
 intros H1; apply H.
 apply I_ge_le_iff; assumption.

 apply I_lt_nle.
 intros H1; apply H.
 apply I_ge_le_iff; assumption.
Qed.

Theorem I_lt_irrefl : ∀ x, ¬(x < x)%I.
Proof.
intros x Hx.
unfold I_lt, I_compare in Hx; simpl in Hx.
remember (fst_same x (- x) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate Hx ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
symmetry in Ht1.
revert Ht1; apply no_fixpoint_negb.
Qed.

Theorem I_nlt_0_r : ∀ x, ¬(x < 0)%I.
Proof.
intros x H.
unfold I_lt, I_compare in H.
remember (fst_same x (- 0%I) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate H ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
rewrite Ht1 in H; discriminate H.
Qed.

Theorem I_eqs_iff : ∀ x y, (x == y)%I ↔ (∀ i, x.[i] = y.[i])%I.
Proof.
intros x y.
split; intros Hxy.
 intros i.
 unfold I_eqs, I_compare in Hxy.
 remember (fst_same x (- y) 0) as s1 eqn:Hs1 .
 destruct s1 as [dj1| ]; [ idtac | clear Hxy ].
  destruct (x .[ dj1]); discriminate Hxy.

  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  rewrite Hs1, negb_involutive; reflexivity.

 unfold I_eqs, I_compare.
 remember (fst_same x (- y) 0) as s1 eqn:Hs1 .
 destruct s1 as [dj1| ]; [ idtac | reflexivity ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hxy in Hs1; symmetry in Hs1.
 exfalso; revert Hs1; apply no_fixpoint_negb.
Qed.

Theorem I_zero_eqs_iff : ∀ x, (x == 0)%I ↔ (∀ i, x.[i] = false).
Proof.
intros x.
split; intros Hx.
 intros i; rewrite I_eqs_iff in Hx; apply Hx.

 apply I_eqs_iff; assumption.
Qed.

Theorem I_sub_diag_eqs : ∀ x, (x - x == 0)%I.
Proof.
intros x.
apply I_eqs_iff; simpl; intros i.
unfold I_add_i; simpl.
rewrite negb_xorb_diag_r, xorb_true_l.
apply negb_false_iff.
unfold carry; simpl.
remember (fst_same x (- x) (S i)) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | reflexivity ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
symmetry in Ht1.
exfalso; revert Ht1; apply no_fixpoint_negb.
Qed.

Theorem I_lt_le_incl : ∀ x y, (x < y)%I → (x ≤ y)%I.
Proof.
intros x y Hxy.
intros H; rewrite Hxy in H; discriminate H.
Qed.

(* inequality < is transitive *)

Theorem I_lt_trans : transitive _ I_lt.
Proof.
intros x y z Hxy Hyz.
destruct (I_eqs_dec x z) as [H1| H1].
 rewrite H1 in Hxy.
 apply I_lt_nle in Hxy.
 unfold I_le in Hxy.
 unfold I_lt in Hyz.
 exfalso; apply Hxy; intros H; rewrite Hyz in H.
 discriminate H.

 apply I_lt_le_incl in Hxy.
 apply I_lt_le_incl in Hyz.
 apply I_le_trans with (z := z) in Hxy; [ idtac | assumption ].
 unfold I_le in Hxy.
 unfold I_eqs in H1.
 unfold I_lt.
 destruct (x ?= z)%I; [ idtac | reflexivity | idtac ].
  exfalso; apply H1; reflexivity.

  exfalso; apply Hxy; reflexivity.
Qed.

(* *)

Add Parametric Morphism : I_add
  with signature I_eqs ==> I_eqs ==> I_eqs
  as I_add_eqs_morph.
Proof.
intros x y Hxy z t Hzt.
rewrite I_eqs_iff in Hxy.
rewrite I_eqs_iff in Hzt.
apply I_eqs_iff; simpl; intros i.
unfold I_add_i; simpl.
rewrite Hxy, Hzt.
f_equal.
unfold carry; simpl.
remember (fst_same x z (S i)) as s1 eqn:Hs1 .
remember (fst_same y t (S i)) as s2 eqn:Hs2 .
destruct s1 as [dj1| ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Ht1).
 destruct s2 as [dj2| ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  destruct (lt_eq_lt_dec dj1 dj2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   rewrite Hxy, Hzt, H in Ht1.
   exfalso; revert Ht1; apply no_fixpoint_negb.

   subst dj2.
   apply Hxy.

   remember H1 as H; clear HeqH.
   apply Hn1 in H.
   rewrite Hxy, Hzt, Ht2 in H.
   symmetry in H.
   exfalso; revert H; apply no_fixpoint_negb.

  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  rewrite Hxy, Hzt, Hs2 in Ht1.
  exfalso; revert Ht1; apply no_fixpoint_negb.

 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s2 as [dj2| ]; [ idtac | reflexivity ].
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct Hs2 as (Hn2, Ht2).
 rewrite <- Hxy, <- Hzt, Hs1 in Ht2.
 exfalso; revert Ht2; apply no_fixpoint_negb.
Qed.

Add Parametric Morphism : I_opp
  with signature I_eqs ==> I_eqs
  as I_opp_eqs_morph.
Proof.
intros x y Hxy.
rewrite I_eqs_iff in Hxy; simpl in Hxy.
apply I_eqs_iff; simpl; intros i.
rewrite Hxy; reflexivity.
Qed.

Add Parametric Morphism : I_sub
  with signature I_eqs ==> I_eqs ==> I_eqs
  as I_sub_eqs_morph.
Proof.
intros x y Hxy z t Hzt.
unfold I_sub.
rewrite Hxy, Hzt; reflexivity.
Qed.

Close Scope nat_scope.
