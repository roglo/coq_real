(* comparison in I *)

Require Import Utf8 QArith NPeano.
Require Import Digit Real01 Real01Add.

Set Implicit Arguments.

Open Scope nat_scope.

Definition I_compare x y :=
  match fst_same x (- y)%I 0 with
  | Some j => if Digit.dec (x.[j]) then Gt else Lt
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

Definition I_eqc x y := I_compare x y = Eq.
Arguments I_eqc x%I y%I.

Theorem I_eqc_eqs_iff : ∀ x y, I_eqc x y ↔ (x == y)%I.
Proof.
intros x y.
split; intros Hxy.
 intros i.
 unfold I_eqc, I_compare in Hxy.
 remember (fst_same x (- y) 0) as s1 eqn:Hs1 .
 destruct s1 as [dj1| ]; [ idtac | clear Hxy ].
  remember (Digit.dec (x .[ dj1])) as u.
  destruct u; discriminate Hxy.

  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  rewrite Hs1, Digit.opp_involutive; reflexivity.

 unfold I_eqc, I_compare.
 remember (fst_same x (- y) 0) as s1 eqn:Hs1 .
 destruct s1 as [dj1| ]; [ idtac | reflexivity ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Hs1).
 unfold I_eqs in Hxy.
 rewrite Hxy in Hs1; symmetry in Hs1.
 exfalso; revert Hs1; apply Digit.no_fixpoint_opp.
Qed.

Theorem I_compare_eq : ∀ x y, (x == y)%I ↔ I_compare x y = Eq.
Proof.
intros x y.
split; intros H; apply I_eqc_eqs_iff; assumption.
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
   rewrite Digit.opp_involutive, Hn1 in H1; symmetry in H1.
   exfalso; revert H1; apply Digit.no_fixpoint_opp.

   subst j2.
   split; intros H.
    destruct (Digit.dec (x .[ j1])) as [H1|H1].
     destruct (Digit.dec (y .[ j1])) as [H2|H2]; [ idtac | reflexivity ].
     rewrite H1, H2 in Hn1; discr_digit Hn1.

     destruct (Digit.dec (y .[ j1])) as [H2|H2]; [ idtac | reflexivity ].
     discriminate H.

    destruct (Digit.dec (x .[ j1])) as [H1|H1]; [ reflexivity | idtac ].
    destruct (Digit.dec (y .[ j1])) as [H2|H2].
     discriminate H.

     rewrite H1, H2 in Hn1; discr_digit Hn1.

   apply Hs1 in H1.
   rewrite Digit.opp_involutive, Hn2 in H1.
   symmetry in H1.
   exfalso; revert H1; apply Digit.no_fixpoint_opp.

  split; intros H; [ exfalso | discriminate H ].
  rewrite Hs2, Digit.opp_involutive in Hn1.
  symmetry in Hn1.
  revert Hn1; apply Digit.no_fixpoint_opp.

 destruct s2 as [j2| ].
  destruct Hs2 as (Hs2, Hn2).
  split; intros H; [ discriminate H | exfalso ].
  rewrite Hs1, Digit.opp_involutive in Hn2.
  symmetry in Hn2; revert Hn2; apply Digit.no_fixpoint_opp.

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
remember (fst_same x (- x) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate H ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
symmetry in Ht1; revert Ht1; apply Digit.no_fixpoint_opp.
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
   apply Hn2 in H; rewrite Digit.opp_involutive in H.
   rewrite Ht1 in H; symmetry in H.
   exfalso; revert H; apply Digit.no_fixpoint_opp.

   subst dj2.
   destruct (Digit.dec (x.[dj1])) as [H1|H1].
    exfalso; apply Hxy; reflexivity.

    destruct (Digit.dec (y.[dj1])) as [H2|H2].
     exfalso; apply Hyx; reflexivity.

     rewrite H1, H2 in Ht1; discr_digit Ht1.

   remember H1 as H; clear HeqH.
   apply Hn1 in H; rewrite Digit.opp_involutive in H.
   rewrite Ht2 in H; symmetry in H.
   exfalso; revert H; apply Digit.no_fixpoint_opp.

  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  rewrite Hs2 in Ht1.
  rewrite Digit.opp_involutive in Ht1; symmetry in Ht1.
  exfalso; revert Ht1; apply Digit.no_fixpoint_opp.

 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s2 as [dj2| ]; [ idtac | clear Hyx ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  rewrite Hs1, Digit.opp_involutive in Ht2.
  symmetry in Ht2.
  exfalso; revert Ht2; apply Digit.no_fixpoint_opp.

  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  unfold I_eq; intros i; simpl.
  unfold I_add_i; simpl.
  rewrite Hs1, Digit.opp_involutive; f_equal.
  apply Digit.add_compat; [ reflexivity | idtac ].
  apply carry_compat_r; intros j.
  rewrite Hs1, Digit.opp_involutive; reflexivity.
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
remember (Digit.dec (x.[dj3])) as u.
destruct u as [Hx3|Hx3]; [ clear Hequ | intros H; discriminate H ].
rewrite Hx3 in *.
symmetry in Ht3.
apply Digit.opp_1_iff in Ht3.
exfalso.
destruct s1 as [dj1| ]; [ idtac | clear Hxy ].
 destruct Hs1 as (Hn1, Ht1).
 remember (Digit.dec (x.[dj1])) as u.
 destruct u as [Hx1|Hx1]; [ apply Hxy; reflexivity | clear Hequ ].
 destruct s2 as [dj2| ]; [ idtac | clear Hyz ].
 destruct Hs2 as (Hn2, Ht2).
 remember (Digit.dec (y.[dj2])) as u.
 destruct u as [Hy2|Hy2]; [ apply Hyz; reflexivity | clear Hequ ].
 clear Hxy Hyz.
  destruct (lt_eq_lt_dec dj1 dj2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   rewrite Digit.opp_involutive in H.
   destruct (lt_eq_lt_dec dj1 dj3) as [[H2| H2]| H2].
    apply Hn3 in H2.
    rewrite <- H, <- Ht1, Hx1 in H2; discr_digit H2.

    subst dj3.
    rewrite Hx1 in Hx3; discr_digit Hx3.

    rename H into Hyz.
    remember H2 as H; clear HeqH.
    apply Hn1 in H.
    apply Nat.lt_trans with (n := dj3) in H1; [ idtac | assumption ].
    remember H1 as HH; clear HeqHH.
    apply Hn2 in HH.
    rewrite Hx3, HH, Ht3 in H.
    discr_digit H.

   subst dj2.
   rewrite Hx1, Hy2 in Ht1; discr_digit Ht1.

   remember H1 as H; clear HeqH.
   apply Hn1 in H; simpl in H.
   rename H into Hxy.
   destruct (lt_eq_lt_dec dj2 dj3) as [[H2| H2]| H2].
    remember H2 as H; clear HeqH.
    apply Hn3 in H.
    rewrite Hxy, <- Ht2, Hy2 in H; discr_digit H.

    subst dj3.
    rewrite Ht3, Hy2 in Ht2; discr_digit Ht2.

    remember H2 as H; clear HeqH.
    apply Hn2 in H; simpl in H.
    rewrite Ht3 in H.
    apply Nat.lt_trans with (n := dj3) in H1; [ idtac | assumption ].
    apply Hn1 in H1.
    rewrite Hx3, H in H1; discr_digit H1.

  destruct (lt_eq_lt_dec dj1 dj3) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn3 in H.
   rewrite Hx1, <- Hs2 in H.
   rewrite Hx1, <- H in Ht1; discr_digit Ht1.

   subst dj3.
   rewrite Hx3 in Hx1; discr_digit Hx1.

   remember H1 as H; clear HeqH.
   apply Hn1 in H.
   rewrite Hx3, Hs2, Ht3 in H; discr_digit H.

 rewrite Hs1 in Hx3.
 destruct s2 as [dj2| ]; [ idtac | clear Hyz ].
  destruct Hs2 as (Hn2, Ht2).
  remember (Digit.dec (y .[ dj2])) as u.
  destruct u as [Hy2|Hy2]; [ apply Hyz; reflexivity | clear Hyz Hequ ].
  destruct (lt_eq_lt_dec dj2 dj3) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn3 in H.
   rewrite Hs1, <- Ht2, Hy2 in H; discr_digit H.

   subst dj3.
   rewrite Ht3, Hy2 in Ht2; discr_digit Ht2.

   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   rewrite H, Ht3 in Hx3; discr_digit Hx3.

  rewrite Hs2, Ht3 in Hx3; discr_digit Hx3.
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
symmetry in Ht1; revert Ht1; apply Digit.no_fixpoint_opp.
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
unfold I_eqs.
remember (fst_same x (- y) 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Ht).
 right; intros H.
 rewrite H in Ht.
 symmetry in Ht.
 revert Ht; apply Digit.no_fixpoint_opp.

 left; intros i.
 rewrite Hs, Digit.opp_involutive; reflexivity.
Qed.
Arguments I_eqs_dec x%I y%I.

(* decidability < vs ≥ and > vs ≤ *)

Theorem I_lt_dec : ∀ x y, {(x < y)%I} + {(x ≥ y)%I}.
Proof.
intros x y.
unfold I_lt, I_ge; simpl.
unfold I_compare; simpl.
remember (fst_same x (- y) 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct (Digit.dec (x .[ di])).
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
unfold I_eqs in Hxy, Hzt.
unfold I_compare; simpl.
remember (fst_same x (- z) 0) as s1 eqn:Hs1 .
remember (fst_same y (- t) 0) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [j1| ].
 destruct Hs1 as (Hn1, Ht1).
 destruct s2 as [j2| ].
  destruct Hs2 as (Hn2, Ht2).
  destruct (Digit.dec (x.[j1])) as [H1| H1].
   destruct (Digit.dec (y.[j2])) as [H2| H2]; [ reflexivity | idtac ].
   destruct (lt_eq_lt_dec j1 j2) as [[H3| H3]| H3].
    remember H3 as H; clear HeqH; apply Hn2 in H.
    rewrite <- Hxy, <- Hzt, <- Ht1, H1 in H; discr_digit H.

    subst j2.
    rewrite <- Hxy, H1 in H2; discr_digit H2.

    remember H3 as H; clear HeqH; apply Hn1 in H.
    rewrite Hxy, Hzt, <- Ht2, H2 in H; discr_digit H.

   destruct (Digit.dec (y.[j2])) as [H2| H2]; [ idtac | reflexivity ].
   destruct (lt_eq_lt_dec j1 j2) as [[H3| H3]| H3].
    remember H3 as H; clear HeqH; apply Hn2 in H.
    rewrite <- Hxy, <- Hzt, <- Ht1, H1 in H; discr_digit H.

    subst j2.
    rewrite <- Hxy, H1 in H2; discr_digit H2.

    remember H3 as H; clear HeqH; apply Hn1 in H.
    rewrite Hxy, Hzt, <- Ht2, H2 in H; discr_digit H.

  exfalso.
  rewrite Hxy, Hs2, Hzt in Ht1.
  revert Ht1; apply Digit.no_fixpoint_opp.

 destruct s2 as [j2| ]; [ exfalso | reflexivity ].
 destruct Hs2 as (Hn2, Ht2).
 rewrite <- Hxy, Hs1, Hzt in Ht2.
 revert Ht2; apply Digit.no_fixpoint_opp.
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
 remember (Digit.dec (x.[j1])) as u.
 destruct u as [|Hx]; [ exfalso; apply H; reflexivity | clear Hequ ].
 rewrite Hx in Ht1; discr_digit Ht1.

 unfold I_add_i; simpl.
 rewrite Hs1, carry_diag; simpl.
 do 3 rewrite Digit.add_0_r.
 rewrite Digit.add_0_l.
 unfold carry; simpl.
 remember (fst_same x 0 (S i)) as s2 eqn:Hs2 .
 destruct s2 as [dj2| ].
  rewrite Hs1; reflexivity.

  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  clear H.
  pose proof (Hs2 O) as H.
  rewrite Hs1 in H; discr_digit H.
Qed.

Theorem I_le_0_r_eqs_iff : ∀ x, (x ≤ 0)%I ↔ (x == 0)%I.
Proof.
intros x.
split; intros H.
 unfold I_le, I_compare in H; simpl in H.
 remember (fst_same x (- 0%I) 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [j1| ].
  destruct Hs1 as (Hn1, Ht1).
  remember (Digit.dec (x.[j1])) as u.
  destruct u as [|Hx]; [ exfalso; apply H; reflexivity | clear Hequ ].
  rewrite Ht1 in Hx; discr_digit Hx.

  intros i; simpl.
  rewrite Hs1; reflexivity.

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
 remember (Digit.dec (x .[ j2])) as u.
 destruct u as [Hx2| Hx2]; [ discriminate H | clear Hequ H ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [j1| ]; [ idtac | exfalso ].
  destruct Hs1 as (Hn1, Ht1).
  remember (Digit.dec (y .[ j1])) as u.
  destruct u as [Hy1| Hy1]; [ reflexivity | clear Hequ ].
  destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2, Digit.opp_sym in H.
   rewrite <- Ht1, Hy1 in H; discr_digit H.

   subst j2.
   rewrite Ht2, Hy1 in Hx2; discr_digit Hx2.

   remember H1 as H; clear HeqH.
   apply Hn1, Digit.opp_sym in H.
   rewrite <- Ht2, Hx2 in H; discr_digit H.

  rewrite Hs1, Hx2 in Ht2; discr_digit Ht2.

 destruct s2 as [j2| ].
  remember (Digit.dec (x .[ j2])) as u.
  destruct u as [Hx| Hx]; [ exfalso; clear Hequ | reflexivity ].
  apply H; clear H.
  destruct s1 as [j1| ].
   remember (Digit.dec (y .[ j1])) as u.
   destruct u as [Hy| Hy]; [ exfalso; clear Hequ | intros H; discriminate H ].
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct Hs1 as (Hn1, Ht1).
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   rewrite Hx in Ht2.
   rewrite Hy in Ht1.
   destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
    remember H1 as H; clear HeqH.
    apply Hn2 in H.
    rewrite H, Hy in Ht1; discr_digit Ht1.

    subst j2.
    rewrite Hy in Ht2; discr_digit Ht2.

    remember H1 as H; clear HeqH.
    apply Hn1 in H.
    rewrite H, Hx in Ht2; discr_digit Ht2.

   intros H; discriminate H.

  exfalso; apply H; clear H; intros H.
  destruct s1 as [j1| ]; [ idtac | discriminate H ].
  remember (Digit.dec (y .[ j1])) as u.
  destruct u as [H1| H1]; [ clear Hequ | discriminate H ].
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, Ht1).
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  rewrite Hs2, H1 in Ht1; discr_digit Ht1.
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
revert Ht1; apply Digit.no_fixpoint_opp.
Qed.

Theorem I_nlt_0_r : ∀ x, ¬(x < 0)%I.
Proof.
intros x H.
unfold I_lt, I_compare in H.
remember (fst_same x (- 0%I) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate H ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
remember (Digit.dec (x.[dj1])) as u.
destruct u as [Hx|Hx]; [ discriminate H | clear Hequ ].
rewrite Ht1 in Hx; discr_digit Hx.
Qed.

Theorem I_zero_eqs_iff : ∀ x, (x == 0)%I ↔ (∀ i, (x.[i] = 0)%D).
Proof. intros x; split; intros i; assumption. Qed.

Theorem I_sub_diag_eqc : ∀ x, (x - x == 0)%I.
Proof.
intros x i; simpl.
unfold I_add_i; simpl.
rewrite Digit.opp_add_diag_r, Digit.add_1_l.
apply Digit.opp_0_iff.
unfold carry; simpl.
remember (fst_same x (- x) (S i)) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | reflexivity ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
symmetry in Ht1.
exfalso; revert Ht1; apply Digit.no_fixpoint_opp.
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
 unfold I_lt.
 remember (x ?= z)%I as cmp eqn:Hcmp.
 symmetry in Hcmp.
 destruct cmp; [ idtac | reflexivity | idtac ].
  apply I_compare_eq in Hcmp; contradiction.

  exfalso; apply Hxy; reflexivity.
Qed.

(* *)

Add Parametric Morphism : I_add
  with signature I_eqs ==> I_eqs ==> I_eqs
  as I_add_eqs_morph.
Proof.
intros x y Hxy z t Hzt.
bbb.

rewrite I_eqc_iff in Hxy.
rewrite I_eqc_iff in Hzt.
apply I_eqc_iff; simpl; intros i.
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
   exfalso; revert Ht1; apply Digit.no_fixpoint_opp.

   subst dj2.
   apply Digit.add_compat; [ reflexivity | idtac ].
   apply Hxy.

   remember H1 as H; clear HeqH.
   apply Hn1 in H.
   rewrite Hxy, Hzt, Ht2 in H.
   symmetry in H.
   exfalso; revert H; apply Digit.no_fixpoint_opp.

  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  rewrite Hxy, Hzt, Hs2 in Ht1.
  exfalso; revert Ht1; apply Digit.no_fixpoint_opp.

 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s2 as [dj2| ]; [ idtac | reflexivity ].
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct Hs2 as (Hn2, Ht2).
 rewrite <- Hxy, <- Hzt, Hs1 in Ht2.
 exfalso; revert Ht2; apply Digit.no_fixpoint_opp.
Qed.

Add Parametric Morphism : I_opp
  with signature I_eqs ==> I_eqs
  as I_opp_eqs_morph.
Proof.
intros x y Hxy.
rewrite I_eqc_iff in Hxy; simpl in Hxy.
apply I_eqc_iff; simpl; intros i.
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
