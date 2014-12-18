Require Import Utf8 QArith NPeano.
Require Import Real01Add.

Set Implicit Arguments.

Open Scope Z_scope.

Record real := mkre { re_int : Z; re_frac : real_mod_1 }.
Arguments mkre _%Z _%rm.

Delimit Scope R_scope with R.
Arguments re_int _%R.
Arguments re_frac _%R.

Definition b2z (b : bool) := if b then 1 else 0.

Definition re_add x y :=
  {| re_int := re_int x + re_int y + b2z (carry (re_frac x) (re_frac y) 0);
     re_frac := rm_add (re_frac x) (re_frac y) |}.
Arguments re_add x%R y%R.

Definition re_zero := {| re_int := 0; re_frac := rm_zero |}.

Notation "x + y" := (re_add x y) : R_scope.
Notation "0" := re_zero : R_scope.

Definition re_norm x :=
  {| re_int := re_int x + b2z (carry (re_frac x) 0 0);
     re_frac := (re_frac x + 0)%rm |}.
Arguments re_norm x%R.

Definition re_eq x y :=
  re_int (re_norm x) = re_int (re_norm y) ∧
  (re_frac x = re_frac y)%rm.
Arguments re_eq x%R y%R.

Definition re_opp x := {| re_int := - re_int x - 1; re_frac := - re_frac x |}.
Definition re_sub x y := re_add x (re_opp y).
Arguments re_opp x%R.
Arguments re_sub x%R y%R.

Notation "x = y" := (re_eq x y) : R_scope.
Notation "x ≠ y" := (¬ re_eq x y) : R_scope.
Notation "- x" := (re_opp x) : R_scope.
Notation "x - y" := (re_sub x y) : R_scope.

(* equality is equivalence relation *)

Theorem re_eq_refl : reflexive _ re_eq.
Proof.
intros x; split; reflexivity.
Qed.

Theorem re_eq_sym : symmetric _ re_eq.
Proof.
intros x y Hxy.
unfold re_eq in Hxy; unfold re_eq.
destruct Hxy; split; symmetry; assumption.
Qed.

Theorem re_eq_trans : transitive _ re_eq.
Proof.
intros x y z Hxy Hyz.
destruct Hxy, Hyz.
unfold re_eq.
split; etransitivity; eassumption.
Qed.

Add Parametric Relation : _ re_eq
 reflexivity proved by re_eq_refl
 symmetry proved by re_eq_sym
 transitivity proved by re_eq_trans
 as re_rel.

(* commutativity *)

Theorem re_add_comm : ∀ x y, (x + y = y + x)%R.
Proof.
intros x y.
unfold re_eq.
unfold re_add; simpl; split; [ idtac | apply rm_add_comm ].
f_equal; [ idtac | rewrite carry_comm_l; reflexivity ].
rewrite carry_comm; f_equal.
apply Z.add_comm.
Qed.

(* neutral element *)

Theorem carry_norm_add_0_r : ∀ x, carry (x + 0%rm) 0 0 = false.
Proof.
intros x.
unfold carry; simpl.
remember (fst_same (x + 0%rm) 0 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [j| ].
 destruct Hs as (_, Hs); rewrite Hs; reflexivity.

 pose proof (not_rm_add_0_inf_1 x 0) as H.
 contradiction.
Qed.

Theorem re_add_0_r : ∀ x, (x + 0 = x)%R.
Proof.
intros x.
unfold re_eq.
unfold re_add; simpl; split; [ idtac | apply rm_add_0_r ].
rewrite Z.add_0_r.
rewrite <- Z.add_assoc; f_equal.
rewrite carry_norm_add_0_r, Z.add_0_r.
reflexivity.
Qed.

(* opposite *)

Theorem re_sub_diag : ∀ x, (x - x = 0)%R.
Proof.
intros x.
unfold re_eq, re_sub, re_opp; simpl.
split; [ idtac | rewrite fold_rm_sub, rm_sub_diag; reflexivity ].
unfold carry; simpl.
rewrite fst_same_diag.
rewrite fold_rm_sub.
rewrite Z.add_sub_assoc, Z.add_opp_r, Z.sub_diag.
remember (fst_same (re_frac x) (- re_frac x) 0) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [j1| ].
 destruct Hs1 as (Hn1, Hs1).
 symmetry in Hs1.
 exfalso; revert Hs1; apply no_fixpoint_negb.

 clear Hs1.
 remember (fst_same (re_frac x - re_frac x) 0 0) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [j2| ].
  destruct Hs2 as (Hn2, Hs2).
  rewrite Hs2; reflexivity.

  pose proof (Hs2 O) as H.
  unfold rm_add_i in H; simpl in H.
  unfold carry in H; simpl in H.
  remember (fst_same (re_frac x) (- re_frac x) 1) as s3 eqn:Hs3 .
  destruct s3 as [dj3| ].
   apply fst_same_sym_iff in Hs3; simpl in Hs3.
   destruct Hs3 as (Hn3, Hs3).
   symmetry in Hs3.
   exfalso; revert Hs3; apply no_fixpoint_negb.

   rewrite negb_xorb_diag_r in H.
   discriminate H.
Qed.

(* compatibility with equality *)

Theorem rm_eq_neq_if : ∀ x y i,
  (x = y)%rm
  → x.[i] = true
  → y.[i] = false
  → (∀ di, x.[i+di] = true) ∧ (∀ di, y.[i+di] = false) ∨
    (∀ di, x.[i+S di] = false) ∧ (∀ di, y.[i+S di] = true).
Proof.
intros x y i Hxy Hx Hy.
unfold rm_eq in Hxy; simpl in Hxy.
pose proof (Hxy i) as H.
unfold rm_add_i in H; simpl in H.
rewrite Hx, Hy, xorb_true_l, xorb_false_l in H.
unfold carry in H; simpl in H.
remember (fst_same x 0 (S i)) as sx eqn:Hsx .
remember (fst_same y 0 (S i)) as sy eqn:Hsy .
destruct sx as [dx| ].
 remember Hsx as HH; clear HeqHH.
 apply fst_same_sym_iff in HH; simpl in HH.
 destruct HH as (Hnx, Htx); rewrite Htx in H.
 destruct sy as [dy| ]; [ idtac | clear H ].
  remember Hsy as HH; clear HeqHH.
  apply fst_same_sym_iff in HH; simpl in HH.
  destruct HH as (Hny, Hty).
  rewrite Hty in H; discriminate H.

  right.
  remember Hsy as Hny; clear HeqHny.
  apply fst_same_sym_iff in Hny; simpl in Hny.
  split; intros di.
   destruct (lt_eq_lt_dec di dx) as [[H1| H1]| H1].
    pose proof (Hnx di H1) as H.
    rename H into Hdi.
    destruct dx; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
    pose proof (Hxy (S (i + dx))%nat) as H.
    unfold rm_add_i in H; simpl in H.
    do 2 rewrite xorb_false_r in H.
    rewrite Hnx in H; [ idtac | apply Nat.lt_succ_diag_r ].
    rewrite Hny in H.
    rewrite xorb_true_l in H.
    symmetry in H.
    rewrite xorb_true_l in H.
    apply negb_sym in H.
    rewrite negb_involutive in H.
    rewrite <- Nat.add_succ_l in H.
    symmetry in Hsx.
    erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
    symmetry in Hsy.
    simpl in H.
    do 2 rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
    simpl in H; rewrite Htx in H; discriminate H.

    subst di.
    rewrite Nat.add_succ_r; assumption.

    remember (di - S dx)%nat as n eqn:Hn .
    apply nat_sub_add_r in Hn; [ idtac | assumption ].
    subst di; clear H1.
    rewrite Nat.add_succ_r.
    induction n as (n, IHn) using all_lt_all.
    destruct n.
     rewrite Nat.add_succ_r.
     rewrite <- negb_involutive.
     apply neq_negb; simpl; intros Hdi.
     rewrite Nat.add_0_r in Hdi.
     pose proof (Hxy (S (i + dx))) as H.
     unfold rm_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite Htx, Hny, xorb_false_l, xorb_true_l in H.
     symmetry in H, Hsx, Hsy.
     rewrite <- Nat.add_succ_l in H.
     rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
     symmetry in H.
     unfold carry in H; simpl in H.
     remember (fst_same x 0 (S (S (i + dx)))) as s1 eqn:Hs1 .
     destruct s1 as [di1| ]; [ idtac | discriminate H ].
     rename H into Hx1.
     destruct di1.
      rewrite Nat.add_0_r, <- Nat.add_succ_r in Hx1.
      rewrite Hdi in Hx1; discriminate Hx1.

      remember Hs1 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn1, _).
      pose proof (Hxy (S (S (i + dx)))) as H.
      unfold rm_add_i in H; simpl in H.
      do 2 rewrite xorb_false_r in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hdi, Hny, xorb_true_l in H.
      apply negb_sym in H.
      rewrite negb_involutive in H.
      rewrite <- Nat.add_succ_l in H.
      rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
      symmetry in H, Hs1.
      replace dx with (dx + 0)%nat in H by apply Nat.add_0_r.
      simpl in H.
      rewrite Nat.add_succ_r, Nat.add_assoc in H.
      do 2 rewrite <- Nat.add_succ_l in H.
      assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H.
      rewrite Hx1 in H; discriminate H.

     rewrite Nat.add_succ_r.
     rewrite <- negb_involutive.
     apply neq_negb; simpl; intros Hdi.
     pose proof (Hxy (S (i + dx + S n))) as H.
     unfold rm_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite IHn in H; [ idtac | apply Nat.lt_succ_diag_r ].
     rewrite Hny, xorb_false_l, xorb_true_l in H.
     symmetry in H, Hsx, Hsy.
     rewrite <- Nat.add_succ_l in H.
     rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
     symmetry in H.
     unfold carry in H; simpl in H.
     remember (fst_same x 0 (S (S (i + (dx + S n))))) as s1 eqn:Hs1 .
     destruct s1 as [di1| ]; [ idtac | discriminate H ].
     rename H into Hx1.
     destruct di1.
      rewrite Nat.add_0_r, <- Nat.add_succ_r in Hx1.
      rewrite Hdi in Hx1; discriminate Hx1.

      remember Hs1 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn1, _).
      pose proof (Hxy (S (S (i + dx + S n)))) as H.
      unfold rm_add_i in H; simpl in H.
      do 2 rewrite xorb_false_r in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Nat.add_assoc in H.
      rewrite Nat.add_succ_r in H.
      rewrite Hdi, Hny, xorb_true_l in H.
      apply negb_sym in H.
      rewrite negb_involutive in H.
      rewrite <- Nat.add_succ_l in H.
      rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
      symmetry in H, Hs1.
      remember (S i + S (dx + S n))%nat as z.
      replace (S z) with (S z + 0)%nat in H by apply Nat.add_0_r.
      subst z.
      rewrite <- Nat.add_succ_l in H; simpl in H.
      rewrite <- Nat.add_succ_l in H.
      rewrite <- Nat.add_succ_r in Hs1.
      assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H.
      do 4 rewrite Nat.add_succ_r in H.
      do 3 rewrite Nat.add_succ_r in Hx1.
      simpl in H.
      rewrite Nat.add_assoc in Hx1.
      simpl in Hx1.
      rewrite Nat.add_assoc in H.
      rewrite Hx1 in H; discriminate H.

   rewrite Nat.add_succ_r; simpl; apply Hny.

 destruct sy as [dy| ]; [ idtac | discriminate H ].
 symmetry in H; simpl in H.
 remember Hsy as HH; clear HeqHH.
 apply fst_same_sym_iff in HH; simpl in HH.
 destruct HH as (Hny, Hty); clear H.
 left.
 remember Hsx as Hnx; clear HeqHnx.
 apply fst_same_sym_iff in Hnx; simpl in Hnx.
 split; intros di.
  destruct (lt_eq_lt_dec di dy) as [[H1| H1]| H1].
   pose proof (Hny di H1) as H.
   destruct dy; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
   rename H into Hdi.
   pose proof (Hxy (S (i + dy))%nat) as H.
   unfold rm_add_i in H; simpl in H.
   do 2 rewrite xorb_false_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite xorb_true_l in H.
   apply negb_sym in H.
   rewrite negb_involutive in H.
   rewrite <- Nat.add_succ_l in H.
   symmetry in Hsy.
   erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
   symmetry in Hsx.
   rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
   simpl in H; rewrite Hty in H; discriminate H.

   subst di.
   destruct dy; [ rewrite Nat.add_0_r; assumption | idtac ].
   rewrite Nat.add_succ_r; apply Hnx.

   destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
   rewrite Nat.add_succ_r; apply Hnx.

  destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
  rewrite Nat.add_succ_r.
  destruct (lt_eq_lt_dec di dy) as [[H1| H1]| H1].
   pose proof (Hny di H1) as H.
   destruct dy; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
   rename H into Hdi.
   pose proof (Hxy (S (i + dy))%nat) as H.
   unfold rm_add_i in H; simpl in H.
   do 2 rewrite xorb_false_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite xorb_true_l in H.
   apply negb_sym in H.
   rewrite negb_involutive in H.
   rewrite <- Nat.add_succ_l in H.
   symmetry in Hsy.
   erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
   symmetry in Hsx.
   rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
   simpl in H; rewrite Hty in H; discriminate H.

   subst di; assumption.

   remember (di - S dy)%nat as n eqn:Hn .
   apply nat_sub_add_r in Hn; [ idtac | assumption ].
   subst di; clear H1.
   rewrite Nat.add_succ_r.
   induction n as (n, IHn) using all_lt_all.
   destruct n; [ clear IHn | idtac ].
    rewrite Nat.add_succ_r.
    rewrite <- negb_involutive.
    apply neq_negb; simpl; intros Hdi.
    rewrite Nat.add_0_r in Hdi.
    pose proof (Hxy (S (i + dy))) as H.
    unfold rm_add_i in H; simpl in H.
    do 2 rewrite xorb_false_r in H.
    rewrite Hnx, Hty, xorb_false_l, xorb_true_l in H.
    symmetry in Hsx, Hsy.
    rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
    symmetry in H.
    unfold carry in H; simpl in H.
    remember (fst_same y 0 (S (S (i + dy)))) as s1 eqn:Hs1 .
    destruct s1 as [di1| ]; [ idtac | discriminate H ].
    rename H into Hx1.
    destruct di1.
     rewrite Nat.add_0_r in Hx1.
     rewrite Hdi in Hx1; discriminate Hx1.

     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, _).
     pose proof (Hxy (S (S (i + dy)))) as H.
     unfold rm_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite <- Nat.add_succ_r in H.
     pose proof (Hn1 O (Nat.lt_0_succ di1)) as HH.
     rewrite Nat.add_0_r, <- Nat.add_succ_r in HH.
     rewrite HH, Hnx, xorb_true_l in H.
     apply negb_sym in H.
     rewrite negb_involutive in H.
     rewrite <- Nat.add_succ_l in H.
     symmetry in H.
     rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     symmetry in H, Hs1.
     replace dy with (dy + 0)%nat in H by apply Nat.add_0_r.
     simpl in H.
     rewrite Nat.add_succ_r, Nat.add_assoc in H.
     do 2 rewrite <- Nat.add_succ_l in H.
     clear HH.
     assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H.
     rewrite Hx1 in H; discriminate H.

    rewrite Nat.add_succ_r.
    rewrite <- negb_involutive.
    apply neq_negb; simpl; intros Hdi.
    pose proof (Hxy (S (i + dy + S n))) as H.
    unfold rm_add_i in H; simpl in H.
    do 2 rewrite xorb_false_r in H.
    rewrite <- Nat.add_assoc in H.
    pose proof (IHn n (Nat.lt_succ_diag_r n)) as HH.
    rewrite <- Nat.add_succ_r in HH.
    rewrite <- Nat.add_succ_r in HH.
    rewrite Nat.add_succ_r in HH.
    rewrite Hnx, HH, xorb_false_l, xorb_true_l in H.
    symmetry in Hsx, Hsy.
    rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
    symmetry in H.
    unfold carry in H; simpl in H.
    remember (fst_same y 0 (S (S (i + (dy + S n))))) as s1 eqn:Hs1 .
    destruct s1 as [di1| ]; [ idtac | discriminate H ].
    rename H into Hx1.
    destruct di1.
     rewrite Nat.add_0_r in Hx1.
     rewrite Hdi in Hx1; discriminate Hx1.

     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, _).
     pose proof (Hxy (S (S (i + dy + S n)))) as H.
     unfold rm_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite Hdi in H.
     rewrite <- Nat.add_succ_r in H.
     rewrite Hnx, xorb_true_l in H.
     rewrite <- Nat.add_succ_l in H.
     erewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     apply negb_sym in H; simpl in H.
     rewrite Nat.add_succ_r in H.
     remember (S (S (i + (dy + S n)))) as z.
     replace z with (z + 0)%nat in H by apply Nat.add_0_r.
     subst z.
     symmetry in Hs1.
     assert (0 < S di1)%nat as HHH by apply Nat.lt_0_succ.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H.
     rewrite Hx1 in H; discriminate H.
Qed.

Theorem case_4 : ∀ x y z dx dy,
  (x = y)%rm
  → fst_same x 0 0 = Some dx
  → fst_same y 0 0 = Some dy
  → carry x z 0 = true
  → carry y z 0 = false
  → carry (y + z) 0 0 = false
  → False.
Proof.
intros x y z dx dy Hf_v Hsx Hsy Hc1 Hc3 Hc4.
remember Hsx as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hnx, Htx).
remember Hsy as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hny, Hty).
remember Hf_v as H; clear HeqH.
unfold rm_eq in H; simpl in H.
rename H into Hf.
destruct (lt_eq_lt_dec dx dy) as [[H1| H1]| H1].
  remember H1 as H; clear HeqH.
  apply Hny in H.
  symmetry in Hf_v.
  eapply rm_eq_neq_if in H; try eassumption.
  destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
   pose proof (Hyx (dy - dx)%nat) as H.
   apply Nat.lt_le_incl in H1.
   rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
   rewrite Nat.add_comm, Nat.add_sub, Hty in H.
   discriminate H.

   destruct dx.
    clear Hnx; simpl in Hyx, Hxx.
    unfold carry in Hc1, Hc3.
    remember (fst_same x z 0) as s1 eqn:Hs1 .
    remember (fst_same y z 0) as s3 eqn:Hs3 .
    destruct s3 as [di3| ]; [ idtac | discriminate Hc3 ].
    simpl in Hc3; apply fst_same_sym_iff in Hs3.
    simpl in Hs3; destruct Hs3 as (Hn3, Ht3).
    rewrite Hc3 in Ht3; symmetry in Ht3.
    destruct s1 as [di1| ]; [ simpl in Hc1 | clear Hc1 ].
     apply fst_same_sym_iff in Hs1; simpl in Hs1.
     destruct Hs1 as (Hn1, Ht1).
     rewrite Hc1 in Ht1; symmetry in Ht1.
     destruct di1.
      rewrite Hc1 in Htx; discriminate Htx.

      destruct di3.
       pose proof (Hny O H1) as H.
       rewrite Hc3 in H; discriminate H.

       pose proof (Hn1 O (Nat.lt_0_succ di1)) as H2.
       pose proof (Hn3 O (Nat.lt_0_succ di3)) as H3.
       rewrite Htx in H2.
       rewrite Hny in H3; [ idtac | assumption ].
       rewrite <- H2 in H3; discriminate H3.

     apply fst_same_sym_iff in Hs1; simpl in Hs1.
     destruct di3.
      pose proof (Hny O H1) as H.
      rewrite Hc3 in H; discriminate H.

      pose proof (Hs1 O) as H2.
      pose proof (Hn3 O (Nat.lt_0_succ di3)) as H3.
      rewrite Htx in H2.
      rewrite Hny in H3; [ idtac | assumption ].
      rewrite <- H2 in H3; discriminate H3.

    unfold carry in Hc1, Hc3.
    remember (fst_same x z 0) as s1 eqn:Hs1 .
    remember (fst_same y z 0) as s3 eqn:Hs3 .
    destruct s3 as [di3| ]; [ idtac | discriminate Hc3 ].
    simpl in Hc3; apply fst_same_sym_iff in Hs3.
    simpl in Hs3; destruct Hs3 as (Hn3, Ht3).
    rewrite Hc3 in Ht3; symmetry in Ht3.
    destruct s1 as [di1| ]; [ simpl in Hc1 | clear Hc1 ].
     apply fst_same_sym_iff in Hs1; simpl in Hs1.
     destruct Hs1 as (Hn1, Ht1).
     rewrite Hc1 in Ht1; symmetry in Ht1.
     destruct di1.
      destruct di3.
       rewrite Ht1 in Ht3; discriminate Ht3.

       pose proof (Hn3 O (Nat.lt_0_succ di3)) as H.
       rewrite Ht1 in H; simpl in H.
       destruct dy; [ revert H1; apply Nat.nlt_0_r | idtac ].
       rewrite Hny in H; [ idtac | apply Nat.lt_0_succ ].
       discriminate H.

      destruct dy; [ revert H1; apply Nat.nlt_0_r | idtac ].
      destruct di3.
       rewrite Hny in Hc3; [ idtac | apply Nat.lt_0_succ ].
       discriminate Hc3.

       destruct (lt_eq_lt_dec di1 di3) as [[H2| H2]| H2].
        remember H2 as H; clear HeqH.
        apply Nat.succ_lt_mono in H.
        apply Hn3 in H.
        rewrite Ht1 in H; simpl in H.
        rename H into Hy1.
        destruct (lt_eq_lt_dec di1 dx) as [[H3| H3]| H3].
         remember H3 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         eapply Nat.lt_trans with (m := S dx) in H; [ idtac | eassumption ].
         apply Hny in H.
         rewrite Hy1 in H; discriminate H.

         subst di1.
         rewrite Htx in Hc1; discriminate Hc1.

         remember H3 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         apply Hn1 in H.
         rewrite Htx in H.
         apply negb_sym in H; simpl in H.
         rename H into Hz1.
         remember H3 as H; clear HeqH.
         eapply Nat.lt_trans with (m := di1) in H; [ idtac | eassumption ].
         apply Nat.succ_lt_mono in H.
         apply Hn3 in H.
         rewrite Hz1 in H; simpl in H.
         rewrite Hny in H; [ idtac | assumption ].
         discriminate H.

        subst di3.
        rewrite Ht1 in Ht3; discriminate Ht3.

        remember H2 as H; clear HeqH.
        apply Nat.succ_lt_mono in H.
        apply Hn1 in H.
        rewrite Ht3 in H; simpl in H.
        rename H into Hx3.
        destruct (lt_eq_lt_dec di3 dy) as [[H3| H3]| H3].
         remember H3 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         apply Hny in H.
         rewrite Hc3 in H; discriminate H.

         subst di3.
         remember H2 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         eapply Nat.lt_trans with (m := S dy) in H; [ idtac | eassumption ].
         apply Hn1 in H.
         rewrite Htx in H.
         apply negb_sym in H; simpl in H.
         rename H into Hz1.
         pose proof (Hn3 (S dx) H1) as H.
         rewrite Hz1 in H; simpl in H.
         rewrite Hny in H; [ idtac | assumption ].
         discriminate H.

         remember H1 as H; clear HeqH.
         apply Hny in H.
         rename H into Hy1.
         remember H3 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         eapply Nat.lt_trans with (m := S dy) in H; [ idtac | eassumption ].
         apply Hn3 in H.
         rewrite Hy1 in H.
         apply negb_sym in H; simpl in H.
         rename H into Hz1.
         remember H3 as H; clear HeqH.
         eapply Nat.lt_trans with (m := di3) in H; [ idtac | eassumption ].
         apply Nat.succ_lt_mono in H.
         eapply Nat.lt_trans with (m := S dy) in H; [ idtac | eassumption ].
         apply Hn1 in H.
         rewrite Hz1, Htx in H.
         discriminate H.

     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     rename H into Hn1.
     destruct dy; [ revert H1; apply Nat.nlt_0_r | idtac ].
     destruct (eq_nat_dec dy (S dx)) as [H2| H2].
      subst dy.
      destruct di3.
       rewrite Hny in Hc3; [ idtac | apply Nat.lt_0_succ ].
       discriminate Hc3.

       destruct (lt_eq_lt_dec di3 dx) as [[H2| H2]| H2].
        remember H2 as H; clear HeqH.
        apply Nat.succ_lt_mono in H.
        apply Nat.lt_lt_succ_r in H.
        apply Hny in H.
        rewrite Hc3 in H; discriminate H.

        subst di3.
        rewrite Hn1, Ht3 in Htx.
        discriminate Htx.

        remember H2 as H; clear HeqH.
        apply Nat.succ_lt_mono in H.
        apply Hn3 in H.
        rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
        rewrite <- Hn1 in H.
        rewrite Htx in H; discriminate H.

      pose proof (Hyx O) as H.
      rewrite Nat.add_1_r in H.
      rewrite Hny in H; [ discriminate H | idtac ].
      revert H1 H2; clear; intros; omega.

  subst dy.
  unfold carry in Hc1; simpl in Hc1.
  unfold carry in Hc3; simpl in Hc3.
  remember (fst_same x z 0) as s1 eqn:Hs1 .
  remember (fst_same y z 0) as s3 eqn:Hs3 .
  destruct s3 as [di3| ]; [ idtac | discriminate Hc3 ].
  remember Hs3 as H; clear HeqH.
  apply fst_same_sym_iff in H.
  simpl in H; destruct H as (Hn3, Ht3).
  rewrite Hc3 in Ht3; symmetry in Ht3.
  destruct s1 as [di1| ]; [ simpl in Hc1 | clear Hc1 ].
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct Hs1 as (Hn1, Ht1).
   rewrite Hc1 in Ht1; symmetry in Ht1.
   destruct di1.
    destruct dx; [ rewrite Hc1 in Htx; discriminate Htx | idtac ].
    destruct di3.
     rewrite Ht1 in Ht3; discriminate Ht3.

     pose proof (Hny O (Nat.lt_0_succ dx)) as H.
     rewrite Hn3 in H; [ idtac | apply Nat.lt_0_succ ].
     rewrite Ht1 in H; discriminate H.

    destruct di3.
     destruct dx.
      rewrite Hn1 in Htx; [ idtac | apply Nat.lt_0_succ ].
      rewrite Ht3 in Htx; discriminate Htx.

      rewrite Hny in Hc3; [ idtac | apply Nat.lt_0_succ ].
      discriminate Hc3.

     destruct (lt_eq_lt_dec di1 di3) as [[H1| H1]| H1].
      remember H1 as H; clear HeqH.
      apply Nat.succ_lt_mono in H.
      apply Hn3 in H.
      rewrite Ht1 in H; simpl in H.
      eapply rm_eq_neq_if in H; try eassumption.
      destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
       remember H1 as H; clear HeqH.
       unfold carry in Hc4; simpl in Hc4.
       remember (fst_same (y + z) 0 0) as s2 eqn:Hs2 .
       destruct s2 as [di2| ]; [ idtac | discriminate Hc4 ].
       apply fst_same_sym_iff in Hs2; simpl in Hs2.
       destruct Hs2 as (Hs2, _).
       destruct di2.
        clear Hs2.
        unfold rm_add_i in Hc4.
        rewrite Hn3 in Hc4; [ idtac | apply Nat.lt_0_succ ].
        rewrite negb_xorb_diag_l, xorb_true_l in Hc4.
        apply negb_false_iff in Hc4.
        rewrite <- Nat.add_1_r in Hc4.
        symmetry in Hs3.
        assert (1 ≤ S di3) as HH by apply Nat.lt_0_succ.
        erewrite carry_before_relay in Hc4; try eassumption.
        rewrite Nat.add_0_l, Hc3 in Hc4; discriminate Hc4.

        clear H.
        pose proof (Hf di1) as H.
        unfold rm_add_i in H; simpl in H.
        rewrite Hn1 in H; [ idtac | apply Nat.lt_succ_diag_r ].
        apply Nat.lt_lt_succ_r in H1.
        rewrite Hn3 in H; [ idtac | assumption ].
        rewrite xorb_false_r in H.
        apply xorb_move_l_r_1 in H.
        rewrite <- xorb_assoc, xorb_nilpotent, xorb_false_l in H.
        replace (S di1) with (S di1 + 0)%nat in H by apply Nat.add_0_r.
        rewrite carry_before_inf_relay in H.
         rewrite carry_before_relay with (di := O) in H.
          simpl in H; rewrite Hxx in H; discriminate H.

          apply fst_same_iff; simpl.
          split; [ idtac | rewrite Hxx; reflexivity ].
          intros dj Hdj.
          exfalso; revert Hdj; apply Nat.nlt_0_r.

          reflexivity.

         apply fst_same_iff; simpl.
         intros dj; apply Hyx.

       pose proof (Hxx (di3 - S di1)%nat) as H.
       rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
       rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
       rewrite Nat.add_comm, Nat.add_sub in H.
       rewrite Hc3 in H; discriminate H.

      subst di3.
      rewrite Ht1 in Ht3; discriminate Ht3.

      remember H1 as H; clear HeqH.
      apply Nat.succ_lt_mono in H.
      apply Hn1 in H.
      rewrite Ht3 in H; simpl in H.
      remember H as Hx1; clear HeqHx1.
      eapply rm_eq_neq_if in H; try eassumption.
      destruct H as [(Hxy, Hyy)| (Hxy, Hyy)]; simpl in Hxy, Hyy.
       pose proof (Hf di3) as H.
       unfold rm_add_i in H; simpl in H.
       rewrite Hn3 in H; [ idtac | apply Nat.lt_succ_diag_r ].
       apply Nat.lt_lt_succ_r in H1.
       rewrite Hn1 in H; [ idtac | assumption ].
       rewrite xorb_false_r in H.
       apply xorb_move_l_r_1 in H.
       rewrite <- xorb_assoc, xorb_nilpotent, xorb_false_l in H.
       replace (S di3) with (S di3 + 0)%nat in H by apply Nat.add_0_r.
       rewrite carry_before_inf_relay in H.
        rewrite carry_before_relay with (di := O) in H.
         rewrite Nat.add_0_r, Hc3 in H; discriminate H.

         apply fst_same_iff; simpl.
         split; [ idtac | rewrite Hyy; reflexivity ].
         intros dj Hdj.
         exfalso; revert Hdj; apply Nat.nlt_0_r.

         reflexivity.

        apply fst_same_iff; simpl.
        intros dj; apply Hxy.

       pose proof (Hxy (di1 - S di3)%nat) as H.
       rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
       rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
       rewrite Nat.add_comm, Nat.add_sub in H.
       rewrite Hc1 in H; discriminate H.

   remember Hs1 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rename H into Hxz.
   pose proof (Hxz di3) as Hx1.
   rewrite Ht3 in Hx1; simpl in Hx1.
   remember Hx1 as H; clear HeqH.
   eapply rm_eq_neq_if in H; try eassumption.
   destruct H as [(Hxy, Hyy)| (Hxy, Hyy)]; simpl in Hxy, Hyy.
    destruct di3.
     simpl in Hxy; rewrite Hxy in Htx; discriminate Htx.

     pose proof (Hf di3) as H.
     unfold rm_add_i in H; simpl in H.
     rewrite Hn3 in H; [ idtac | apply Nat.lt_succ_diag_r ].
     rewrite Hxz in H.
     rewrite xorb_false_r in H.
     apply xorb_move_l_r_1 in H.
     rewrite <- xorb_assoc, xorb_nilpotent, xorb_false_l in H.
     replace (S di3) with (S di3 + 0)%nat in H by apply Nat.add_0_r.
     rewrite carry_before_inf_relay in H.
      rewrite carry_before_relay with (di := O) in H.
       rewrite Nat.add_0_r, Hc3 in H; discriminate H.

       apply fst_same_iff; simpl.
       simpl in Hyy.
       split; [ idtac | rewrite Hyy; reflexivity ].
       intros dj Hdj.
       exfalso; revert Hdj; apply Nat.nlt_0_r.

       reflexivity.

      apply fst_same_iff; simpl.
      intros dj; apply Hxy.

    destruct di3.
     destruct dx; [ rewrite Htx in Hx1; discriminate Hx1 | idtac ].
     rewrite Hny in Hc3; [ idtac | apply Nat.lt_0_succ ].
     discriminate Hc3.

     replace O with (0 + 0)%nat in Hc4 by reflexivity.
     rewrite carry_before_inf_relay in Hc4; [ discriminate Hc4 | idtac ].
     apply fst_same_iff; simpl.
     intro j.
     unfold rm_add_i.
     destruct (lt_eq_lt_dec j (S di3)) as [[H1| H1]| H1].
      rewrite Hn3; [ idtac | assumption ].
      rewrite negb_xorb_diag_l.
      apply negb_true_iff.
      unfold carry; simpl.
      remember (fst_same y z (S j)) as s2 eqn:Hs2 .
      apply fst_same_sym_iff in Hs2; simpl in Hs2.
      destruct s2 as [dj2| ].
       destruct Hs2 as (Hn2, Hs2).
       destruct (lt_eq_lt_dec (j + dj2) di3) as [[H2| H2]| H2].
        remember H2 as H; clear HeqH.
        apply Nat.succ_lt_mono in H.
        apply Hn3 in H.
        rewrite Hs2 in H; symmetry in H.
        exfalso; revert H; apply no_fixpoint_negb.

        rewrite H2; assumption.

        destruct dj2; [ exfalso; omega | idtac ].
        remember H2 as H; clear HeqH.
        assert (0 < S dj2)%nat as HH by apply Nat.lt_0_succ.
        apply lt_add_sub_lt_r with (d := O) in H; try assumption.
        apply Hn2 in H.
        apply le_S_n in H1.
        rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
        rewrite Nat.add_comm, Nat.add_sub in H.
        rewrite Hc3, Ht3 in H; discriminate H.

       pose proof (Hs2 (di3 - j)%nat) as H.
       apply le_S_n in H1.
       rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
       rewrite Nat.add_comm, Nat.add_sub in H.
       rewrite Hc3, Ht3 in H; discriminate H.

      subst j.
      rewrite Hc3, Ht3, xorb_false_l.
      unfold carry; simpl.
      remember (fst_same y z (S (S di3))) as s2 eqn:Hs2 .
      destruct s2 as [dj2| ]; [ idtac | reflexivity ].
      rewrite <- Nat.add_succ_r, <- Nat.add_succ_l.
      apply Hyy.

      remember (j - S (S di3))%nat as v eqn:Hv .
      apply nat_sub_add_r in Hv; [ idtac | assumption ].
      subst j.
      rewrite Hyy, xorb_true_l.
      rewrite <- Hxz, Hxy, xorb_false_l.
      unfold carry.
      remember (fst_same y z (S (S di3 + S v))) as s2 eqn:Hs2 .
      destruct s2 as [dj2| ]; [ idtac | reflexivity ].
      rewrite <- Nat.add_succ_r, <- Nat.add_assoc.
      apply Hyy.

  remember H1 as H; clear HeqH.
  apply Hnx in H.
  eapply rm_eq_neq_if in H; try eassumption.
  destruct H as [(Hxy, Hyy)| (Hxy, Hyy)]; simpl in Hxy, Hyy.
   pose proof (Hxy (dx - dy)%nat) as H.
   apply Nat.lt_le_incl in H1.
   rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
   rewrite Nat.add_comm, Nat.add_sub, Htx in H.
   discriminate H.

   destruct (lt_dec (S dy) dx) as [H2| H2].
    remember H2 as H; clear HeqH.
    apply Hnx in H.
    rewrite <- Nat.add_1_r, Hxy in H.
    discriminate H.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H2; [ idtac | assumption ].
    subst dx; clear H1.
    unfold carry in Hc3; simpl in Hc3.
    remember (fst_same y z 0) as s3 eqn:Hs3 .
    destruct s3 as [dj3| ]; [ idtac | discriminate Hc3 ].
    remember Hs3 as H; clear HeqH.
    apply fst_same_sym_iff in H; simpl in H.
    destruct H as (Hn3, Ht3).
    rewrite Hc3 in Ht3; symmetry in Ht3.
    destruct (lt_eq_lt_dec dj3 dy) as [[H1| H1]| H1].
     remember H1 as H; clear HeqH.
     apply Hny in H.
     rewrite Hc3 in H; discriminate H.

     Focus 2.
     pose proof (Hyy (dj3 - S dy)%nat) as H.
     rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
     rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
     rewrite Nat.add_comm, Nat.add_sub, Hc3 in H.
     discriminate H.

     subst dj3.
     unfold carry in Hc1; simpl in Hc1.
     remember (fst_same x z 0) as s1 eqn:Hs1 .
     destruct s1 as [dj1| ]; [ idtac | clear Hc1 ].
      apply fst_same_sym_iff in Hs1; simpl in Hs1.
      destruct Hs1 as (Hn1, Ht1).
      rewrite Hc1 in Ht1; symmetry in Ht1.
      destruct (lt_eq_lt_dec dj1 dy) as [[H1| H1]| H1].
       remember H1 as H; clear HeqH.
       apply Hn3 in H.
       rewrite Hny in H; [ idtac | assumption ].
       rewrite Ht1 in H; discriminate H.

       subst dj1.
       rewrite Ht3 in Ht1; discriminate Ht1.

       pose proof (Hxy (dj1 - S dy)%nat) as H.
       rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
       rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
       rewrite Nat.add_comm, Nat.add_sub, Hc1 in H.
       discriminate H.

      remember Hs1 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      rename H into Ht1.
      unfold carry in Hc4; simpl in Hc4.
      remember (fst_same (y + z) 0 0) as s4 eqn:Hs4 .
      destruct s4 as [di4| ]; [ idtac | discriminate Hc4 ].
      apply fst_same_sym_iff in Hs4; simpl in Hs4.
      destruct Hs4 as (Hn4, _).
      destruct di4.
       unfold rm_add_i in Hc4.
       destruct dy.
        rewrite Hc3, Ht3, xorb_false_l in Hc4.
        unfold carry in Hc4; simpl in Hc4.
        remember (fst_same y z 1) as s5 eqn:Hs5 .
        destruct s5 as [dj5| ]; [ idtac | discriminate Hc4 ].
        simpl in Hyy; rewrite Hyy in Hc4; discriminate Hc4.

        rewrite Hn3 in Hc4; [ idtac | apply Nat.lt_0_succ ].
        rewrite negb_xorb_diag_l, xorb_true_l in Hc4.
        apply negb_false_iff in Hc4.
        unfold carry in Hc4; simpl in Hc4.
        remember (fst_same y z 1) as s5 eqn:Hs5 .
        apply fst_same_sym_iff in Hs5; simpl in Hs5.
        destruct s5 as [dj5| ]; [ idtac | clear Hc4 ].
         destruct Hs5 as (Hn5, Ht5).
         rewrite Hc4 in Ht5; symmetry in Ht5.
         destruct (lt_eq_lt_dec dj5 dy) as [[H1| H1]| H1].
          remember H1 as H; clear HeqH.
          apply Nat.succ_lt_mono in H.
          apply Hn3 in H.
          rewrite Ht5, Hc4 in H; discriminate H.

          subst dj5.
          rewrite Hc3 in Hc4; discriminate Hc4.

          rewrite Hn5 in Hty; [ idtac | assumption ].
          rewrite Ht3 in Hty; discriminate Hty.

         rewrite Hs5 in Hty.
         rewrite Ht3 in Hty; discriminate Hty.

       unfold rm_add_i in Hc4.
       destruct dy.
        simpl in Hxy, Hyy.
        rewrite Hyy, <- Ht1, Hxy, xorb_false_l in Hc4.
        unfold carry in Hc4; simpl in Hc4.
        remember (fst_same y z (S (S di4))) as s5 eqn:Hs5 .
        destruct s5 as [dj5| ]; [ idtac | discriminate Hc4 ].
        rewrite Hyy in Hc4; discriminate Hc4.

        destruct (lt_eq_lt_dec di4 dy) as [[H1| H1]| H1].
         remember H1 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         rewrite Hn3 in Hc4; [ idtac | assumption ].
         rewrite negb_xorb_diag_l, xorb_true_l in Hc4.
         apply negb_false_iff in Hc4.
         unfold carry in Hc4; simpl in Hc4.
         remember (fst_same y z (S (S di4))) as s5 eqn:Hs5 .
         destruct s5 as [dj5| ]; [ idtac | clear Hc4 ].
          apply fst_same_sym_iff in Hs5; simpl in Hs5.
          destruct Hs5 as (Hn5, Ht5).
          rewrite Hc4 in Ht5; symmetry in Ht5.
          clear H.
          destruct (lt_eq_lt_dec (S (di4 + dj5)) dy) as [[H2| H2]| H2].
           remember H2 as H; clear HeqH.
           apply Nat.succ_lt_mono in H.
           apply Hn3 in H.
           rewrite Ht5, Hc4 in H; discriminate H.

           rewrite H2, Ht3 in Ht5; discriminate Ht5.

           destruct dj5.
            revert H1 H2; clear; intros; omega.

            remember H2 as H; clear HeqH.
            rewrite <- Nat.add_succ_l in H.
            assert (0 < S dj5)%nat as HH by apply Nat.lt_0_succ.
            eapply lt_add_sub_lt_r with (d := O) in H; try assumption.
            apply Hn5 in H.
            rewrite <- Nat.add_succ_l in H.
            rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
            rewrite Nat.add_comm, Nat.add_sub in H.
            rewrite Hc3, Ht3 in H; discriminate H.

          apply fst_same_sym_iff in Hs5; simpl in Hs5.
          clear H.
          pose proof (Hs5 (dy - S di4)%nat) as H.
          rewrite <- Nat.add_succ_l in H.
          rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
          rewrite Nat.add_comm, Nat.add_sub in H.
          rewrite Hc3, Ht3 in H; discriminate H.

         subst di4.
         rewrite Hty, Ht3, xorb_false_l in Hc4.
         remember (S (S dy)) as u.
         replace u with (u + 0)%nat in Hc4 by apply Nat.add_0_r.
         subst u.
         rewrite carry_before_relay with (di := O) in Hc4.
          simpl in Hc4.
          rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in Hc4.
          rewrite Hyy in Hc4; discriminate Hc4.

          apply fst_same_iff; simpl.
          split.
           intros dj Hdj.
           exfalso; revert Hdj; apply Nat.nlt_0_r.

           rewrite <- Nat.add_succ_l, <- Nat.add_succ_r.
           rewrite Hyy, <- negb_involutive.
           rewrite <- Ht1, Hxy; reflexivity.

          reflexivity.

         pose proof (Hyy (di4 - S dy)%nat) as H.
         rewrite Nat.add_succ_r in H.
         rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
         rewrite Nat.add_comm, Nat.add_sub in H.
         rewrite H in Hc4.
         rename H into Hy4.
         rewrite <- Ht1 in Hc4.
         pose proof (Hxy (di4 - S dy)%nat) as H.
         rewrite Nat.add_succ_r in H.
         rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
         rewrite Nat.add_comm, Nat.add_sub in H.
         rewrite H in Hc4.
         rewrite xorb_false_l in Hc4.
         remember (S (S di4)) as u.
         replace u with (u + 0)%nat in Hc4 by apply Nat.add_0_r.
         subst u.
         rewrite carry_before_relay with (di := O) in Hc4.
          rewrite Nat.add_0_r in Hc4.
          rename H into Hx4.
          pose proof (Hyy (di4 - dy)%nat) as H.
          rewrite Nat.add_succ_l, Nat.add_succ_r in H.
          rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
          rewrite Nat.add_comm, Nat.add_sub in H.
          rewrite Hc4 in H; discriminate H.

          apply fst_same_iff; simpl.
          split.
           intros dj Hdj.
           exfalso; revert Hdj; apply Nat.nlt_0_r.

           rewrite Nat.add_0_r.
           remember (di4 - S dy)%nat as v eqn:Hv .
           apply nat_sub_add_r in Hv; [ idtac | assumption ].
           subst di4.
           rewrite <- Nat.add_succ_l, <- Nat.add_succ_r.
           rewrite Hyy, <- negb_involutive.
           rewrite <- Ht1, Hxy; reflexivity.

          reflexivity.
Qed.

Theorem case_5 : ∀ x y z dx dy,
  (x = y)%rm
  → fst_same x 0 0 = Some dx
  → fst_same y 0 0 = Some dy
  → carry x z 0 = false
  → carry (x + z) 0 0 = true
  → carry y z 0 = false
  → carry (y + z) 0 0 = false
  → False.
Proof.
intros x y z dx dy Hf_v Hsx Hsy Hc1 Hc2 Hc3 Hc4.
remember Hsx as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hnx, Htx).
remember Hsy as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hny, Hty).
remember Hf_v as H; clear HeqH.
unfold rm_eq in H; simpl in H.
rename H into Hf.
unfold carry in Hc1; simpl in Hc1.
remember (fst_same x z 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate Hc1 ].
remember Hs1 as H; clear HeqH.
apply fst_same_sym_iff in H; simpl in H.
destruct H as (Hn1, Ht1).
rewrite Hc1 in Ht1; symmetry in Ht1.
destruct (lt_eq_lt_dec dj1 dx) as [[H1| H1]| H1].
 rewrite Hnx in Hc1; [ idtac | assumption ].
 discriminate Hc1.

 Focus 2.
 pose proof (Hn1 dx H1) as Hz1.
 apply negb_sym in Hz1.
 rewrite Htx in Hz1; simpl in Hz1.
 unfold carry in Hc2; simpl in Hc2.
 remember (fst_same (x + z) 0 0) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [dj2| ]; [ idtac | clear Hc2 ].
  destruct Hs2 as (Hn2, Ht2).
  rewrite Ht2 in Hc2; discriminate Hc2.

  assert (∀ dj, rm_add_i x z (0 + dj) = true) as H.
   intros dj; simpl; apply Hs2.

   destruct dj1; [ revert H1; apply Nat.nlt_0_r | idtac ].
   pose proof (Hn1 O (Nat.lt_0_succ dj1)) as HH.
   apply rm_add_inf_true_neq_if in H; [ idtac | assumption ].
   simpl in H.
   destruct H as (j, (Hj, (Hxz, (Hxj, (Hzj, (Hxd, Hzd)))))).
   destruct (lt_eq_lt_dec j dx) as [[H2| H2]| H2].
    rewrite Hn1 in Hxj; [ idtac | omega ].
    rewrite Hzj in Hxj; discriminate Hxj.

    subst j.
    rewrite Hz1 in Hzj; discriminate Hzj.

    destruct (lt_eq_lt_dec (S dj1) j) as [[H3| H3]| H3].
     remember H3 as H; clear HeqH.
     apply Hxz in H.
     rewrite Hc1, Ht1 in H; discriminate H.

     Focus 2.
     rewrite Hn1 in Hxj; [ idtac | assumption ].
     rewrite Hzj in Hxj; discriminate Hxj.

     subst j.
     clear Hxj H2 Hzj Hxz Hj.
     destruct (lt_eq_lt_dec dx dy) as [[H2| H2]| H2].
      remember H2 as H; clear HeqH.
      apply Hny in H.
      rename H into Hy1.
      symmetry in Hf_v.
      remember Hy1 as H; clear HeqH.
      eapply rm_eq_neq_if in H; try eassumption.
      destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
       pose proof (Hyx (dy - dx)%nat) as H.
       apply Nat.lt_le_incl in H2.
       rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
       rewrite Nat.add_comm, Nat.add_sub, Hty in H.
       discriminate H.

       destruct (lt_dec (S dx) dy) as [H3| H3].
        remember H3 as H; clear HeqH.
        apply Hny in H.
        rewrite <- Nat.add_1_r, Hyx in H.
        discriminate H.

        apply Nat.nlt_ge in H3.
        apply Nat.le_antisymm in H3; [ idtac | assumption ].
        subst dy; clear H2.
        pose proof (Hxx (dj1 - dx)%nat) as H.
        rewrite Nat.add_succ_r in H.
        rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
        rewrite Nat.add_comm, Nat.add_sub in H.
        rewrite Hc1 in H; discriminate H.

      subst dy.
      unfold carry in Hc3; simpl in Hc3.
      remember (fst_same y z 0) as s3 eqn:Hs3 .
      destruct s3 as [dj3| ]; [ idtac | discriminate Hc3 ].
      remember Hs3 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn3, Ht3).
      rewrite Hc3 in Ht3; symmetry in Ht3.
      unfold carry in Hc4; simpl in Hc4.
      remember (fst_same (y + z) 0 0) as s4 eqn:Hs4 .
      destruct s4 as [dj4| ]; [ idtac | discriminate Hc4 ].
      remember Hs4 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn4, _).
      destruct (lt_eq_lt_dec dj3 dx) as [[H2| H2]| H2].
       rewrite Hny in Hc3; [ idtac | assumption ].
       discriminate Hc3.

       subst dj3.
       rewrite Hz1 in Ht3; discriminate Ht3.

       destruct (lt_eq_lt_dec dj3 (S dj1)) as [[H3| H3]| H3].
        remember H3 as H; clear HeqH.
        apply Hn1 in H.
        rewrite Ht3 in H; simpl in H.
        rename H into Hx3.
        pose proof (Hf dj3) as H.
        unfold rm_add_i in H; simpl in H.
        do 2 rewrite xorb_false_r in H.
        rewrite Hx3, Hc3, xorb_true_l, xorb_false_l in H.
        unfold carry in H; simpl in H.
        remember (fst_same x 0 (S dj3)) as sx3 eqn:Hsx3 .
        remember (fst_same y 0 (S dj3)) as sy3 eqn:Hsy3 .
        apply fst_same_sym_iff in Hsx3; simpl in Hsx3.
        apply fst_same_sym_iff in Hsy3; simpl in Hsy3.
        destruct sx3 as [dx3| ].
         destruct Hsx3 as (Hnx3, Htx3).
         destruct sy3 as [dy3| ].
          destruct Hsy3 as (Hny3, Hty3).
          rewrite Htx3, Hty3 in H; discriminate H.

          clear H.
          remember Hx3 as H; clear HeqH.
          eapply rm_eq_neq_if in H; try eassumption.
          destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
           pose proof (Hyx (S dj1 - dj3)%nat) as H.
           apply Nat.lt_le_incl in H3.
           rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
           rewrite Nat.add_comm, Nat.add_sub in H.
           rewrite Hc1 in H; discriminate H.

           pose proof (Hyx (S dj1 - dj3)%nat) as H.
           rewrite Nat.add_succ_r in H.
           rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
           rewrite Nat.add_comm, Nat.add_sub in H.
           rewrite <- Nat.add_1_r, Hxd in H.
           discriminate H.

         destruct sy3 as [dy3| ]; [ idtac | discriminate H ].
         destruct Hsy3 as (Hny3, Hty3).
         clear H.
         remember Hx3 as H; clear HeqH.
         eapply rm_eq_neq_if in H; try eassumption.
         destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
          pose proof (Hyx (S dj1 - dj3)%nat) as H.
          apply Nat.lt_le_incl in H3.
          rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
          rewrite Nat.add_comm, Nat.add_sub in H.
          rewrite Hc1 in H; discriminate H.

          pose proof (Hyx (S dj1 - dj3)%nat) as H.
          rewrite Nat.add_succ_r in H.
          rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
          rewrite Nat.add_comm, Nat.add_sub in H.
          rewrite <- Nat.add_1_r, Hxd in H.
          discriminate H.

        subst dj3.
        destruct dj4.
         unfold rm_add_i in Hc4.
         rewrite Hn3 in Hc4; [ idtac | apply Nat.lt_0_succ ].
         rewrite negb_xorb_diag_l, xorb_true_l in Hc4.
         apply negb_false_iff in Hc4.
         unfold carry in Hc4; simpl in Hc4.
         remember (fst_same y z 1) as s5 eqn:Hs5 .
         apply fst_same_sym_iff in Hs5; simpl in Hs5.
         destruct s5 as [dj5| ]; [ idtac | clear Hc4 ].
          destruct Hs5 as (Hn5, Ht5).
          rewrite Hc4 in Ht5; symmetry in Ht5.
          destruct (lt_eq_lt_dec dj5 dj1) as [[H3| H3]| H3].
           remember H3 as H; clear HeqH.
           apply Nat.succ_lt_mono in H.
           rewrite Hn3 in Hc4; [ idtac | assumption ].
           rewrite Ht5 in Hc4; discriminate Hc4.

           subst dj5.
           rewrite Ht3 in Ht5; discriminate Ht5.

           remember H3 as H; clear HeqH.
           rewrite Hn5 in Hc3; [ idtac | assumption ].
           rewrite Ht3 in Hc3; discriminate Hc3.

          rewrite Hs5 in Hc3.
          rewrite Ht3 in Hc3; discriminate Hc3.

         destruct (lt_eq_lt_dec dj4 dj1) as [[H3| H3]| H3].
          unfold rm_add_i in Hc4.
          remember H3 as H; clear HeqH.
          apply Nat.succ_lt_mono in H.
          rewrite Hn3 in Hc4; [ idtac | assumption ].
          rewrite negb_xorb_diag_l, xorb_true_l in Hc4.
          apply negb_false_iff in Hc4.
          unfold carry in Hc4; simpl in Hc4.
          remember (fst_same y z (S (S dj4))) as s5 eqn:Hs5 .
          apply fst_same_sym_iff in Hs5; simpl in Hs5.
          destruct s5 as [dj5| ]; [ idtac | clear Hc4 ].
           destruct Hs5 as (Hn5, Ht5).
           rewrite Hc4 in Ht5; symmetry in Ht5.
           destruct (lt_eq_lt_dec (S (dj4 + dj5)) dj1) as [[H4| H4]| H4].
            clear H.
            remember H4 as H; clear HeqH.
            apply Nat.succ_lt_mono in H.
            rewrite Hn3 in Hc4; [ idtac | assumption ].
            rewrite Ht5 in Hc4; discriminate Hc4.

            rewrite H4, Ht1 in Ht5; discriminate Ht5.

            clear H.
            destruct dj5.
             exfalso; omega.

             remember H4 as H; clear HeqH.
             rewrite <- Nat.add_succ_l in H.
             rename HH into Hxz.
             assert (0 < S dj5)%nat as HH by apply Nat.lt_0_succ.
             apply lt_add_sub_lt_r with (d := O) in H; try assumption.
             apply Hn5 in H.
             rewrite <- Nat.add_succ_l in H.
             rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
             rewrite Nat.add_comm, Nat.add_sub in H.
             rewrite Ht1, Hc3 in H; discriminate H.

           clear H.
           pose proof (Hs5 (dj1 - S dj4)%nat) as H.
           rewrite <- Nat.add_succ_l in H.
           rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
           rewrite Nat.add_comm, Nat.add_sub in H.
           rewrite Ht1, Hc3 in H; discriminate H.

          subst dj4.
          unfold rm_add_i in Hc4.
          rewrite Hc3, Ht3, xorb_false_l in Hc4.
          unfold carry in Hc4; simpl in Hc4.
          remember (fst_same y z (S (S dj1))) as s5 eqn:Hs5 .
          destruct s5 as [dj5| ]; [ idtac | discriminate Hc4 ].
          apply fst_same_sym_iff in Hs5; simpl in Hs5.
          destruct Hs5 as (Hn5, Ht5).
          rewrite Hc4 in Ht5; symmetry in Ht5.
          rewrite <- Nat.add_succ_r, <- Nat.add_succ_l in Ht5.
          rewrite Hzd in Ht5; discriminate Ht5.

          unfold rm_add_i in Hc4.
          remember y .[ S dj4] as y4 eqn:Hy4 .
          symmetry in Hy4.
          destruct y4.
           pose proof (Hzd (dj4 - S dj1)%nat) as H.
           rewrite Nat.add_succ_r in H.
           rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
           rewrite Nat.add_comm, Nat.add_sub in H.
           rename H into Hz4.
           rewrite Hz4, xorb_nilpotent, xorb_false_l in Hc4.
           unfold carry in Hc4.
           remember (fst_same y z (S (S dj4))) as s5 eqn:Hs5 .
           destruct s5 as [dj5| ]; [ idtac | discriminate Hc4 ].
           apply fst_same_sym_iff in Hs5; simpl in Hs5.
           destruct Hs5 as (Hn5, Ht5); simpl in Hc4.
           rewrite Hc4 in Ht5; symmetry in Ht5.
           pose proof (Hzd (dj4 + dj5 - dj1)%nat).
           rewrite Nat.add_succ_r, Nat.add_succ_l in H.
           rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
           rewrite Nat.add_comm, Nat.add_sub in H.
           rewrite Ht5 in H; discriminate H.

           pose proof (Hxd (dj4 - S dj1)%nat) as H.
           rewrite Nat.add_succ_r in H.
           rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
           rewrite Nat.add_comm, Nat.add_sub in H.
           rename H into Hx4.
           remember Hx4 as H; clear HeqH.
           eapply rm_eq_neq_if in H; try eassumption.
           destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
            pose proof (Hf (S dj1)) as H.
            unfold rm_add_i in H; simpl in H.
            do 2 rewrite xorb_false_r in H.
            rewrite Hc1, Hc3 in H.
            do 2 rewrite xorb_false_l in H.
            unfold carry in H; simpl in H.
            remember (fst_same x 0 (S (S dj1))) as s5 eqn:Hs5 .
            destruct s5 as [dj5| ].
             apply fst_same_sym_iff in Hs5; simpl in Hs5.
             destruct Hs5 as (Hn5, Ht5).
             rewrite <- Nat.add_succ_r, <- Nat.add_succ_l in Ht5.
             rewrite Hxd in Ht5; discriminate Ht5.

             remember (fst_same y 0 (S (S dj1))) as s6 eqn:Hs6 .
             destruct s6 as [dj6| ]; [ idtac | clear H ].
              apply fst_same_sym_iff in Hs6; simpl in Hs6.
              destruct Hs6 as (Hn6, Ht6).
              rewrite Ht6 in H; discriminate H.

              apply fst_same_sym_iff in Hs6; simpl in Hs6.
              pose proof (Hs6 (dj4 - S dj1)%nat) as H.
              rewrite <- Nat.add_succ_l in H.
              rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
              rewrite Nat.add_comm, Nat.add_sub in H.
              rewrite Hy4 in H; discriminate H.

            pose proof (Hxd (dj4 - dj1)%nat) as H.
            rewrite Nat.add_succ_r, Nat.add_succ_l in H.
            rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
            rewrite Nat.add_comm, Nat.add_sub in H.
            rewrite <- Nat.add_1_r in H; simpl in H.
            rewrite Hyx in H; discriminate H.

        pose proof (Hzd (dj3 - S (S dj1))%nat) as H.
        rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
        rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
        rewrite Nat.add_comm, Nat.add_sub in H.
        rewrite Ht3 in H; discriminate H.

      remember H2 as H; clear HeqH.
      apply Hnx in H.
      rename H into Hx1.
      remember Hx1 as H; clear HeqH.
      eapply rm_eq_neq_if in H; try eassumption.
      destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
       pose proof (Hyx (dx - dy)%nat) as H.
       apply Nat.lt_le_incl in H2.
       rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
       rewrite Nat.add_comm, Nat.add_sub, Htx in H.
       discriminate H.

       pose proof (Hyx (S dj1 - dy)%nat) as H.
       rewrite Nat.add_succ_r in H.
       rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
       rewrite Nat.add_comm, Nat.add_sub in H.
       rewrite <- Nat.add_1_r, Hxd in H.
       discriminate H.

 subst dj1.
 destruct (lt_eq_lt_dec dx dy) as [[H1| H1]| H1].
  remember H1 as H; clear HeqH.
  apply Hny in H.
  rename H into Hy1.
  symmetry in Hf_v.
  remember Hy1 as H; clear HeqH.
  eapply rm_eq_neq_if in H; try eassumption.
  destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
   pose proof (Hyx (dy - dx)%nat) as H.
   apply Nat.lt_le_incl in H1.
   rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
   rewrite Nat.add_comm, Nat.add_sub, Hty in H.
   discriminate H.

   destruct (lt_dec (S dx) dy) as [H2| H2].
    remember H2 as H; clear HeqH.
    apply Hny in H.
    rewrite <- Nat.add_1_r, Hyx in H.
    discriminate H.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H2; [ idtac | assumption ].
    subst dy; clear H1.
    unfold carry in Hc1; simpl in Hc1.
    unfold carry in Hc2; simpl in Hc2.
    remember (fst_same (x + z) 0 0) as s2 eqn:Hs2 .
    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    destruct s2 as [dj2| ]; [ idtac | clear Hc2 ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2 in Hc2; discriminate Hc2.

     assert (∀ dj, rm_add_i x z (0 + dj) = true) as H.
      intros dj; simpl; apply Hs2.

      destruct dx.
       rewrite <- Ht1 in Hc1.
       apply rm_add_inf_true_eq_if in H; [ idtac | assumption ].
       simpl in H; destruct H as (Hxd, Hyd).
       unfold carry in Hc3; simpl in Hc3.
       remember (fst_same y z 0) as s3 eqn:Hs3 .
       destruct s3 as [dj3| ]; [ idtac | discriminate Hc3 ].
       remember Hs3 as H; clear HeqH.
       apply fst_same_sym_iff in H; simpl in H.
       destruct H as (Hn3, Ht3).
       rewrite Hc3 in Ht3; symmetry in Ht3.
       destruct dj3.
        rewrite Hc3 in Hy1; discriminate Hy1.

        rewrite Hyd in Ht3; discriminate Ht3.

       pose proof (Hn1 O (Nat.lt_0_succ dx)) as HH.
       apply rm_add_inf_true_neq_if in H; [ idtac | assumption ].
       simpl in H.
       destruct H as (j, (Hj, (Hxz, (Hxj, (Hzj, (Hxd, Hzd)))))).
       destruct (lt_eq_lt_dec j (S dx)) as [[H1| H1]| H1].
        rewrite Hn1 in Hxj; [ idtac | assumption ].
        rewrite Hzj in Hxj; discriminate Hxj.

        subst j.
        unfold carry in Hc3; simpl in Hc3.
        remember (fst_same y z 0) as s3 eqn:Hs3 .
        destruct s3 as [dj3| ]; [ idtac | discriminate Hc3 ].
        remember Hs3 as H; clear HeqH.
        apply fst_same_sym_iff in H; simpl in H.
        destruct H as (Hn3, Ht3).
        rewrite Hc3 in Ht3; symmetry in Ht3.
        destruct (lt_dec dj3 (S (S dx))) as [H1| H1].
         rewrite Hny in Hc3; [ idtac | assumption ].
         discriminate Hc3.

         apply Nat.nlt_ge in H1.
         pose proof (Hzd (dj3 - S (S dx))%nat) as H.
         rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
         rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
         rewrite Nat.add_comm, Nat.add_sub in H.
         rewrite Ht3 in H; discriminate H.

        rewrite Hxz in Hc1; [ idtac | assumption ].
        rewrite Ht1 in Hc1; discriminate Hc1.

  subst dy.
  unfold carry in Hc2; simpl in Hc2.
  remember (fst_same (x + z) 0 0) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s2 as [dj2| ]; [ idtac | clear Hc2 ].
   destruct Hs2 as (Hn2, Ht2).
   rewrite Ht2 in Hc2; discriminate Hc2.

   assert (∀ dj, rm_add_i x z (dx + dj) = true) as H.
    intros dj; apply Hs2.

    rewrite <- Ht1 in Hc1.
    apply rm_add_inf_true_eq_if in H; [ idtac | assumption ].
    destruct H as (Hxd, Hzd).
    pose proof (Hf dx) as H.
    unfold rm_add_i in H; simpl in H.
    do 2 rewrite xorb_false_r in H.
    rewrite Htx, Hty in H.
    do 2 rewrite xorb_false_l in H.
    unfold carry in H; simpl in H.
    remember (fst_same x 0 (S dx)) as s5 eqn:Hs5 .
    apply fst_same_sym_iff in Hs5; simpl in Hs5.
    destruct s5 as [dj5| ].
     destruct Hs5 as (Hn5, Ht5).
     rewrite <- Nat.add_succ_r in Ht5.
     rewrite Hxd in Ht5; discriminate Ht5.

     remember (fst_same y 0 (S dx)) as s6 eqn:Hs6 .
     apply fst_same_sym_iff in Hs6; simpl in Hs6.
     destruct s6 as [dj6| ]; [ idtac | clear H ].
      destruct Hs6 as (Hn6, Hs6).
      rewrite Hs6 in H; discriminate H.

      unfold carry in Hc4; simpl in Hc4.
      remember (fst_same (y + z) 0 0) as s4 eqn:Hs4 .
      destruct s4 as [dj4| ]; [ idtac | discriminate Hc4 ].
      apply fst_same_sym_iff in Hs4; simpl in Hs4.
      destruct Hs4 as (Hn4, _).
      destruct (lt_eq_lt_dec dj4 dx) as [[H1| H1]| H1].
       unfold rm_add_i in Hc4; simpl in Hc4.
       rewrite Hny in Hc4; [ idtac | assumption ].
       rewrite <- Hn1 in Hc4; [ idtac | assumption ].
       rewrite Hnx in Hc4; [ idtac | assumption ].
       apply negb_false_iff in Hc4.
       replace (S dj4) with (S dj4 + 0)%nat in Hc4 by apply Nat.add_0_r.
       rewrite carry_before_relay with (di := (dx - S dj4)%nat) in Hc4.
        rewrite Nat.add_sub_assoc in Hc4; [ idtac | assumption ].
        rewrite Nat.add_comm, Nat.add_sub in Hc4.
        rewrite Hty in Hc4; discriminate Hc4.

        apply fst_same_iff; simpl.
        split.
         intros dj Hdj.
         apply Nat.lt_add_lt_sub_l in Hdj.
         rewrite Hny; [ idtac | assumption ].
         rewrite <- Hn1; [ idtac | assumption ].
         rewrite Hnx; [ idtac | assumption ].
         reflexivity.

         rewrite <- Nat.add_succ_l.
         rewrite Nat.add_sub_assoc; [ idtac | assumption ].
         rewrite Nat.add_comm, Nat.add_sub.
         rewrite Hty, Ht1; reflexivity.

        apply Nat.le_0_l.

       subst dj4.
       unfold rm_add_i in Hc4; simpl in Hc4.
       rewrite Hty, Ht1, xorb_false_l in Hc4.
       replace (S dx) with (S dx + 0)%nat in Hc4 by apply Nat.add_0_r.
       rewrite carry_before_relay with (di := O) in Hc4.
        simpl in Hc4; rewrite Hs6 in Hc4.
        discriminate Hc4.

        apply fst_same_iff; simpl.
        split.
         intros dj Hdj.
         exfalso; revert Hdj; apply Nat.nlt_0_r.

         rewrite Hs6, <- Nat.add_succ_r, Hzd; reflexivity.

        reflexivity.

       remember (dj4 - S dx)%nat as v eqn:Hv .
       apply nat_sub_add_r in Hv; [ idtac | assumption ].
       subst dj4.
       unfold rm_add_i in Hc4; simpl in Hc4.
       rewrite Hzd, Nat.add_succ_r, Hs6 in Hc4.
       remember (S (S (dx + v))) as u.
       replace u with (u + 0)%nat in Hc4 by apply Nat.add_0_r.
       subst u.
       rewrite carry_before_relay with (di := O) in Hc4.
        rewrite Nat.add_0_r, <- Nat.add_succ_r in Hc4.
        rewrite Hs6 in Hc4; discriminate Hc4.

        apply fst_same_iff; simpl.
        split.
         intros dj Hdj.
         exfalso; revert Hdj; apply Nat.nlt_0_r.

         rewrite Nat.add_0_r.
         rewrite <- Nat.add_succ_r, Hs6.
         rewrite <- Nat.add_succ_r, Hzd; reflexivity.

        reflexivity.

  pose proof (Hnx dy H1) as Hx1.
  remember Hx1 as H; clear HeqH.
  eapply rm_eq_neq_if in H; try eassumption.
  destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
   pose proof (Hyx (dx - dy)%nat) as H.
   apply Nat.lt_le_incl in H1.
   rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
   rewrite Nat.add_comm, Nat.add_sub in H.
   rewrite Htx in H; discriminate H.

   destruct (lt_dec (S dy) dx) as [H2| H2].
    destruct dx; [ revert H2; apply Nat.nlt_0_r | idtac ].
    pose proof (Hyx (dx - S dy)%nat) as H.
    rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
    rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
    rewrite Nat.add_comm, Nat.add_sub in H.
    rewrite Hnx in H; [ idtac | apply Nat.lt_succ_diag_r ].
    discriminate H.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H2; [ idtac | assumption ].
    subst dx; clear H1.
    unfold carry in Hc2; simpl in Hc2.
    remember (fst_same (x + z) 0 0) as s2 eqn:Hs2 .
    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    destruct s2 as [dj2| ]; [ idtac | clear Hc2 ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2 in Hc2; discriminate Hc2.

     assert (∀ dj, rm_add_i x z (S dy + dj) = true) as H.
      intros dj; apply Hs2.

      rewrite <- Ht1 in Hc1.
      apply rm_add_inf_true_eq_if in H; [ idtac | assumption ].
      destruct H as (Hxd, Hzd).
      pose proof (Hxd O) as H.
      rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
      rewrite Hyx in H; discriminate H.
Qed.

Theorem case_6 : ∀ x y z a b c1 c2 c3 c4 dx,
  Some dx = fst_same x 0 0
  → None = fst_same y 0 0
  → a = b + 1
  → (x = y)%rm
  → carry x z 0 = c1
  → carry (x + z) 0 0 = c2
  → carry y z 0 = c3
  → carry (y + z) 0 0 = c4
  → (∀ dj : nat, (dj < dx)%nat → x .[ dj] = true)
  → x .[ dx] = false
  → b2z c1 + b2z c2 + a = b2z c3 + b2z c4 + b.
Proof.
intros x y z a b c1 c2 c3 c4 dx.
intros Hsx Hsy Hi Hf Hc1 Hc2 Hc3 Hc4 Hnx Htx.
remember Hsy as H; clear HeqH.
apply fst_same_sym_iff in H; simpl in H.
rename H into Hny.
destruct dx; [ clear Hnx | idtac ].
 pose proof (Hny O) as H.
 symmetry in Hf.
 eapply rm_eq_neq_if in H; try eassumption; simpl in H.
 destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
  clear Htx Hyx.
  simpl in Hi.
  rewrite Z.add_comm in Hi; subst a.
  rewrite Z.add_assoc; f_equal.
  destruct c1, c2, c3, c4; simpl; try reflexivity; exfalso.
   rewrite carry_comm in Hc2.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsx; reflexivity.

   rewrite carry_comm in Hc2.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsx; reflexivity.

   rewrite carry_comm in Hc2.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsx; reflexivity.

   rewrite carry_comm in Hc2.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsx; reflexivity.

   unfold carry in Hc1; simpl in Hc1.
   remember (fst_same x z 0) as s1 eqn:Hs1 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct s1 as [dj1| ]; [ idtac | clear Hc1 ].
    rewrite Hxx in Hc1; discriminate Hc1.

    unfold carry in Hc4; simpl in Hc4.
    remember (fst_same (y + z) 0 0) as s4 eqn:Hs4 .
    destruct s4 as [dj4| ]; [ idtac | discriminate Hc4 ].
    unfold rm_add_i in Hc4; simpl in Hc4.
    rewrite Hny, <- Hs1, Hxx, xorb_false_l in Hc4.
    unfold carry in Hc4; simpl in Hc4.
    remember (fst_same y z (S dj4)) as s5 eqn:Hs5 .
    destruct s5 as [dj5| ]; [ idtac | discriminate Hc4 ].
    rewrite Hny in Hc4; discriminate Hc4.

   unfold carry in Hc3; simpl in Hc3.
   remember (fst_same y z 0) as s3 eqn:Hs3 .
   destruct s3 as [dj3| ]; [ idtac | discriminate Hc3 ].
   rewrite Hny in Hc3; discriminate Hc3.

   rewrite carry_comm in Hc3.
   rewrite carry_comm_l in Hc4.
   eapply case_2; try eassumption.
   unfold carry; simpl.
   rewrite <- Hsy; reflexivity.

   unfold carry in Hc2; simpl in Hc2.
   remember (fst_same (x + z) 0 0) as s2 eqn:Hs2 .
   destruct s2 as [dj2| ]; [ idtac | clear Hc2 ].
    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    destruct Hs2 as (_, Ht2).
    rewrite Ht2 in Hc2; discriminate Hc2.

    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    unfold carry in Hc1; simpl in Hc1.
    remember (fst_same x z 0) as s1 eqn:Hs1 .
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    destruct s1 as [dj1| ]; [ idtac | discriminate Hc1 ].
    destruct Hs1 as (Hn1, Ht1).
    assert (∀ dj, rm_add_i x z (dj1 + dj) = true) as H.
     intros dj; apply Hs2.

     apply rm_add_inf_true_eq_if in H; [ idtac | assumption ].
     destruct H as (Hx1, _).
     pose proof (Hxx (dj1 + 1)%nat) as H.
     rewrite Hx1 in H; discriminate H.

   unfold carry in Hc3; simpl in Hc3.
   remember (fst_same y z 0) as s3 eqn:Hs3 .
   destruct s3 as [dj3| ]; [ idtac | discriminate Hc3 ].
   rewrite Hny in Hc3; discriminate Hc3.

   unfold carry in Hc3; simpl in Hc3.
   remember (fst_same y z 0) as s3 eqn:Hs3 .
   destruct s3 as [dj3| ]; [ idtac | discriminate Hc3 ].
   rewrite Hny in Hc3; discriminate Hc3.

   unfold carry in Hc4; simpl in Hc4.
   remember (fst_same (y + z) 0 0) as s4 eqn:Hs4 .
   apply fst_same_sym_iff in Hs4; simpl in Hs4.
   destruct s4 as [dj4| ]; [ idtac | clear Hc4 ].
    destruct Hs4 as (Hn4, Ht4).
    rewrite Ht4 in Hc4; discriminate Hc4.

    unfold carry in Hc3; simpl in Hc3.
    remember (fst_same y z 0) as s3 eqn:Hs3 .
    apply fst_same_sym_iff in Hs3; simpl in Hs3.
    destruct s3 as [dj3| ]; [ idtac | clear Hc3 ].
     destruct Hs3 as (Hn3, Ht3).
     assert (∀ dj, rm_add_i y z (dj3 + dj) = true) as H.
      intros dj; apply Hs4.

      apply rm_add_inf_true_eq_if in H; [ idtac | assumption ].
      destruct H as (Hy3, Hz3).
      unfold carry in Hc1; simpl in Hc1.
      remember (fst_same x z 0) as s1 eqn:Hs1 .
      apply fst_same_sym_iff in Hs1; simpl in Hs1.
      destruct s1 as [dj1| ]; [ idtac | discriminate Hc1 ].
      destruct Hs1 as (Hn1, Ht1).
      unfold carry in Hc2; simpl in Hc2.
      remember (fst_same (x + z) 0 0) as s2 eqn:Hs2 .
      destruct s2 as [dj2| ]; [ idtac | discriminate Hc2 ].
      apply fst_same_sym_iff in Hs2; simpl in Hs2.
      destruct Hs2 as (Hn2, _).
      unfold rm_add_i in Hc2; simpl in Hc2.
      destruct dj3.
       destruct dj1.
        rewrite Hc1, <- Ht3, Hc3 in Ht1; discriminate Ht1.

        simpl in Hz3.
        rewrite Hz3, Hc1 in Ht1; discriminate Ht1.

       pose proof (Hs4 O) as H.
       unfold rm_add_i in H; simpl in H.
       rewrite Hn3 in H; [ idtac | apply Nat.lt_0_succ ].
       rewrite negb_xorb_diag_l, xorb_true_l in H.
       apply negb_true_iff in H.
       unfold carry in H.
       remember (fst_same y z 1) as s5 eqn:Hs5 .
       destruct s5 as [dj5| ]; [ idtac | discriminate H ].
       rewrite Hny in H; discriminate H.

     pose proof (Hs4 O) as H.
     unfold rm_add_i in H.
     rewrite Hs3, negb_xorb_diag_l, xorb_true_l in H.
     apply negb_true_iff in H.
     unfold carry in H; simpl in H.
     remember (fst_same y z 1) as s5 eqn:Hs5 .
     destruct s5 as [dj5| ]; [ idtac | discriminate H ].
     rewrite Hny in H; discriminate H.

   unfold carry in Hc3; simpl in Hc3.
   remember (fst_same y z 0) as s3 eqn:Hs3 .
   destruct s3 as [dj3| ]; [ idtac | discriminate Hc3 ].
   rewrite Hny in Hc3; discriminate Hc3.

  pose proof (Hyx O) as H.
  rewrite Hny in H; discriminate H.

 pose proof (Hny (S dx)) as H.
 symmetry in Hf.
 eapply rm_eq_neq_if in H; try eassumption; simpl in H.
 destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
  remember Hf as H; clear HeqH.
  unfold rm_eq in H; simpl in H.
  rename H into Hr.
  pose proof (Hr O) as H.
  unfold rm_add_i in H; simpl in H.
  do 2 rewrite xorb_false_r in H.
  rewrite Hnx in H; [ idtac | apply Nat.lt_0_succ ].
  rewrite Hny, xorb_true_l in H.
  symmetry in H.
  rewrite xorb_true_l in H.
  apply negb_sym in H.
  rewrite negb_involutive in H.
  unfold carry in H.
  remember (fst_same x 0 1) as s1 eqn:Hs1 .
  remember (fst_same y 0 1) as s2 eqn:Hs2 .
  destruct s1 as [dj1| ].
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct Hs1 as (Hn1, Ht1).
   simpl in H.
   rewrite Ht1 in H.
   destruct s2 as [dj2| ]; [ idtac | discriminate H ].
   rewrite Hny in H; discriminate H.

   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   rewrite Hs1 in Htx; discriminate Htx.

  pose proof (Hyx O) as H.
  rewrite Hny in H; discriminate H.
Qed.

Theorem case_7 : ∀ x y z,
  fst_same x 0 0 = None
  → fst_same y 0 0 = None
  → carry (x + z) 0 0 = true
  → carry (y + z) 0 0 = false
  → False.
Proof.
intros x y z Hsx Hsy Hc2 Hc4.
remember Hsx as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
rename H into Hnx.
remember Hsy as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
rename H into Hny.
unfold carry in Hc2; simpl in Hc2.
remember (fst_same (x + z) 0 0) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s2 as [dj2| ]; [ idtac | clear Hc2 ].
 destruct Hs2 as (Hn2, Ht2).
 rewrite Ht2 in Hc2; discriminate Hc2.

 unfold carry in Hc4; simpl in Hc4.
 remember (fst_same (y + z) 0 0) as s4 eqn:Hs4 .
 destruct s4 as [dj4| ]; [ idtac | discriminate Hc4 ].
 apply fst_same_sym_iff in Hs4; simpl in Hs4.
 destruct Hs4 as (Hn4, _).
 unfold rm_add_i in Hc4.
 rewrite Hny, xorb_true_l in Hc4.
 remember z .[ dj4] as z4 eqn:Hz4 .
 symmetry in Hz4.
 destruct z4.
  rewrite xorb_false_l in Hc4.
  unfold carry in Hc4.
  remember (fst_same y z (S dj4)) as s5 eqn:Hs5 .
  destruct s5 as [dj5| ]; [ idtac | discriminate Hc4 ].
  rewrite Hny in Hc4; discriminate Hc4.

  rewrite xorb_true_l in Hc4.
  apply negb_false_iff in Hc4.
  pose proof (Hnx dj4) as H.
  rewrite <- negb_involutive in H.
  apply negb_sym in H; simpl in H.
  rewrite <- Hz4 in H.
  apply negb_sym in H; simpl in H.
  apply rm_add_inf_true_neq_if in H.
   destruct H as (j, (Hj, (Hdi, (H, _)))).
   rewrite Hnx in H; discriminate H.

   intros di; apply Hs2.
Qed.

Theorem re_add_compat_r : ∀ x y z, (x = y)%R → (x + z = y + z)%R.
Proof.
intros x y z Hxy.
unfold re_eq in Hxy; simpl in Hxy.
destruct Hxy as (Hi, Hf).
unfold re_eq; simpl.
split; [ idtac | rewrite Hf; reflexivity ].
do 4 rewrite <- Z.add_assoc.
rewrite Z.add_comm; symmetry.
rewrite Z.add_comm; symmetry.
do 4 rewrite <- Z.add_assoc.
f_equal.
remember (re_frac x) as X.
remember (re_frac y) as Y.
remember (re_frac z) as Z.
remember (re_int x) as XI.
remember (re_int y) as YI.
clear x y z HeqX HeqY HeqXI HeqYI HeqZ.
move Z before Y.
rename X into x; rename Y into y; rename Z into z.
rename XI into a; rename YI into b.
do 2 rewrite Z.add_assoc.
unfold carry in Hi; simpl in Hi.
remember (fst_same x 0 0) as sx eqn:Hsx .
remember (fst_same y 0 0) as sy eqn:Hsy .
remember (carry x z 0) as c1 eqn:Hc1 .
remember (carry (x + z) 0 0) as c2 eqn:Hc2 .
remember (carry y z 0) as c3 eqn:Hc3 .
remember (carry (y + z) 0 0) as c4 eqn:Hc4 .
symmetry in Hc1, Hc2, Hc3, Hc4.
destruct sx as [dx| ].
 remember Hsx as H; clear HeqH.
 apply fst_same_sym_iff in H; simpl in H.
 destruct H as (Hnx, Htx); rewrite Htx, Z.add_0_r in Hi.
 destruct sy as [dy| ].
  remember Hsy as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hny, Hty); rewrite Hty, Z.add_0_r in Hi.
  subst b; f_equal.
  remember Hf as Hf_v; clear HeqHf_v.
  unfold rm_eq in Hf; simpl in Hf.
  destruct c1, c2, c3, c4; simpl; try reflexivity; exfalso.
   rewrite carry_comm in Hc2.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsx; reflexivity.

   rewrite carry_comm in Hc2.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsx; reflexivity.

   rewrite carry_comm in Hc2.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsx; reflexivity.

   rewrite carry_comm in Hc4.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsy; reflexivity.

   symmetry in Hsx, Hsy.
   eapply case_4 with (x := x); try eassumption.

   rewrite carry_comm in Hc4.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsy; reflexivity.

   Focus 2.
   remember (carry 0 y 0) as c5 eqn:Hc5 .
   symmetry in Hc5.
   destruct c5.
    unfold carry in Hc5; simpl in Hc5.
    remember (fst_same 0 y 0) as s5 eqn:Hs5 .
    destruct s5; [ discriminate Hc5 | clear Hc5 ].
    remember Hs5 as H; clear HeqH.
    rewrite fst_same_comm in H.
    apply fst_same_sym_iff in H; simpl in H.
    rewrite H in Hty; discriminate Hty.

    rewrite carry_comm in Hc4.
    eapply case_1; eassumption.

   Focus 2.
   symmetry in Hsx, Hsy, Hf_v.
   eapply case_4 with (y := x); eassumption.

   symmetry in Hsx, Hsy.
   eapply case_5; eassumption.

   symmetry in Hsx, Hsy.
   symmetry in Hf_v.
   eapply case_5 with (x := y) (y := x); eassumption.

  eapply case_6; eassumption.

 destruct sy as [dy| ]; simpl in Hi.
  remember Hsy as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hny, Hty); rewrite Hty, Z.add_0_r in Hi.
  symmetry in Hf, Hi; symmetry.
  eapply case_6; eassumption.

  apply Z.add_cancel_r in Hi; subst a; f_equal.
  remember Hsx as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  rename H into Hnx.
  remember Hsy as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  rename H into Hny.
  symmetry in Hsx, Hsy.
  destruct c1, c2, c3, c4; try reflexivity; exfalso.
   eapply case_7 with (x := x); eassumption.

   unfold carry in Hc3; simpl in Hc3.
   destruct (fst_same y z 0); [ idtac | discriminate Hc3 ].
   rewrite Hny in Hc3; discriminate Hc3.

   unfold carry in Hc3; simpl in Hc3.
   destruct (fst_same y z 0); [ idtac | discriminate Hc3 ].
   rewrite Hny in Hc3; discriminate Hc3.

   eapply case_7 with (y := x); eassumption.

   unfold carry in Hc3; simpl in Hc3.
   destruct (fst_same y z 0); [ idtac | discriminate Hc3 ].
   rewrite Hny in Hc3; discriminate Hc3.

   unfold carry in Hc1; simpl in Hc1.
   destruct (fst_same x z 0); [ idtac | discriminate Hc1 ].
   rewrite Hnx in Hc1; discriminate Hc1.

   unfold carry in Hc1; simpl in Hc1.
   destruct (fst_same x z 0); [ idtac | discriminate Hc1 ].
   rewrite Hnx in Hc1; discriminate Hc1.

   unfold carry in Hc1; simpl in Hc1.
   destruct (fst_same x z 0); [ idtac | discriminate Hc1 ].
   rewrite Hnx in Hc1; discriminate Hc1.

   unfold carry in Hc1; simpl in Hc1.
   destruct (fst_same x z 0); [ idtac | discriminate Hc1 ].
   rewrite Hnx in Hc1; discriminate Hc1.

   unfold carry in Hc1; simpl in Hc1.
   destruct (fst_same x z 0); [ idtac | discriminate Hc1 ].
   rewrite Hnx in Hc1; discriminate Hc1.
Qed.

Theorem re_add_compat : ∀ x y z t,
  (x = y)%R
  → (z = t)%R
  → (x + z = y + t)%R.
Proof.
intros x y z t Hxy Hzt.
transitivity (x + t)%R; [ idtac | apply re_add_compat_r; assumption ].
rewrite re_add_comm; symmetry.
rewrite re_add_comm; symmetry.
apply re_add_compat_r; assumption.
Qed.

Add Parametric Morphism : re_add
  with signature re_eq ==> re_eq ==> re_eq
  as re_add_morph.
Proof.
intros x y Hxy z t Hct.
apply re_add_compat; assumption.
Qed.

(* associativity *)

Theorem re_add_assoc_norm : ∀ x y z,
  (re_norm x + (re_norm y + re_norm z) =
   (re_norm x + re_norm y) + re_norm z)%R.
Proof.
intros x y z.
rename x into x0; rename y into y0; rename z into z0.
remember (re_norm x0) as x.
remember (re_norm y0) as y.
remember (re_norm z0) as z.
unfold re_eq; simpl.
split; [ idtac | apply rm_add_assoc ].
subst x y z; simpl.
remember (re_frac x0) as x.
remember (re_frac y0) as y.
remember (re_frac z0) as z.
remember (re_int x0) as xi.
remember (re_int y0) as yi.
remember (re_int z0) as zi.
rename x0 into x1; rename y0 into y1; rename z0 into z1.
rename x into x0; rename y into y0; rename z into z0.
remember (x0 + 0)%rm as x.
remember (y0 + 0)%rm as y.
remember (z0 + 0)%rm as z.
remember (carry (x + (y + z))%rm 0%rm (0)) as c1 eqn:Hc1 .
remember (carry (x + y + z)%rm 0%rm (0)) as c2 eqn:Hc2 .
remember (carry x (y + z)%rm (0)) as c3 eqn:Hc3 .
remember (carry (x + y)%rm z (0)) as c4 eqn:Hc4 .
remember (carry y z (0)) as c5 eqn:Hc5 .
remember (carry x y (0)) as c6 eqn:Hc6 .
symmetry in Hc1, Hc2, Hc3, Hc4, Hc5, Hc6.
move c2 before c1; move c3 before c2.
move c4 before c3; move c5 before c4.
move c6 before c5.
remember Hc1 as H; clear HeqH.
erewrite carry_sum_3_norm_assoc_r in H; try eassumption.
move H at top; subst c1.
remember Hc2 as H; clear HeqH.
erewrite carry_sum_3_norm_assoc_l in H; try eassumption.
move H at top; subst c2.
simpl; do 2 rewrite Z.add_0_r.
do 12 rewrite <- Z.add_assoc.
do 4 f_equal.
symmetry; rewrite Z.add_comm.
do 2 rewrite <- Z.add_assoc.
do 2 f_equal.
destruct c3, c4, c5, c6; try reflexivity; exfalso.
 eapply case_1; eassumption.

 rewrite carry_comm_l in Hc4.
 eapply case_1; rewrite carry_comm; eassumption.

 eapply case_3; eassumption.

 eapply case_1; eassumption.

 eapply case_3; eassumption.

 rewrite carry_comm, carry_comm_l in Hc3.
 rewrite carry_comm, carry_comm_r in Hc4.
 rewrite carry_comm in Hc5, Hc6.
 eapply case_3; try eassumption.

 rewrite carry_comm_l in Hc4.
 eapply case_1; rewrite carry_comm; eassumption.

 rewrite carry_comm, carry_comm_l in Hc3.
 rewrite carry_comm, carry_comm_r in Hc4.
 rewrite carry_comm in Hc5, Hc6.
 eapply case_3; eassumption.

 clear Hc1 Hc2.
 eapply case_2; eassumption.

 rewrite carry_comm_r in Hc3.
 eapply case_2; rewrite carry_comm; eassumption.
Qed.

Theorem re_norm_eq : ∀ x, (re_norm x = x)%R.
Proof.
intros x.
unfold re_eq.
split; simpl.
 rewrite Z.add_comm, Z.add_assoc.
 f_equal.
 unfold carry; simpl.
 remember (fst_same (re_frac x + 0%rm) 0 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [dj1| ].
  destruct Hs1 as (Hn1, Ht1).
  rewrite Ht1; reflexivity.

  pose proof (not_rm_add_0_inf_1 (re_frac x) 0) as H.
  contradiction.

 apply rm_add_0_r.
Qed.

Theorem re_add_assoc : ∀ x y z, (x + (y + z) = (x + y) + z)%R.
Proof.
intros x y z.
pose proof (re_add_assoc_norm x y z) as H.
do 3 rewrite re_norm_eq in H; assumption.
Qed.

(* decidability *)

Theorem re_norm_zerop : ∀ x, {(re_norm x = 0)%R} + {(re_norm x ≠ 0)%R}.
Proof.
intros x.
remember (re_norm x) as y eqn:Hy .
unfold re_eq; simpl.
destruct (Z_zerop (re_int y)) as [H1| H1].
 rewrite H1; simpl.
 destruct (rm_zerop (re_frac y)) as [H2| H2].
  left.
  split; [ idtac | assumption ].
  subst y; simpl in H1, H2; simpl; f_equal.
  unfold rm_eq in H2; simpl in H2.
  unfold carry; simpl.
  rewrite fst_same_diag.
  remember (fst_same (re_frac x + 0%rm) 0 0) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1; [ destruct Hs1; assumption | exfalso ].
  pose proof (not_rm_add_0_inf_1 (re_frac x) 0) as H.
  contradiction.
bbb.

intros x.
remember (re_norm x) as y eqn:Hy .
unfold re_eq; simpl.
destruct (Z_zerop (re_int y)) as [H1| H1].
 rewrite H1; simpl.
 destruct (rm_zerop (re_frac y)) as [H2| H2].
  left.
  split; [ idtac | assumption ].
  subst y.
  simpl in H1, H2; simpl.
  unfold carry; simpl.
  f_equal; rewrite fst_same_diag.
  remember (fst_same (re_frac x + 0%rm) 0 0) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [di1| ].
   destruct Hs1; assumption.
bbb.

Theorem re_zerop : ∀ x, {(x = 0)%R} + {(x ≠ 0)%R}.
Proof.
intros x.
unfold re_eq; simpl.
destruct (Z_zerop (re_int x)) as [H1| H1].
 rewrite H1; simpl.
 remember (fst_same (re_frac x) rm_ones 0) as s eqn:Hs .
 apply fst_same_sym_iff in Hs; simpl in Hs.
 destruct s as [di| ].
  destruct Hs as (Hn, Ht).
  right; intros H.
  unfold rm_eq in H; simpl in H.
  destruct H as (Hb, Hi).
bbb.

intros x.
unfold re_eq; simpl.
destruct (Z_zerop (re_int x)) as [H1| H1].
 rewrite H1; simpl.
 remember (fst_same (re_frac x + 0%rm) rm_ones 0) as s eqn:Hs .
 apply fst_same_sym_iff in Hs; simpl in Hs.
 destruct s as [di| ].
  destruct Hs as (Hn, Ht).
  right; intros H.
  unfold rm_eq in H; simpl in H.
  destruct H as (Hb, Hi).
  pose proof (Hi di) as HH.
  rewrite Ht in HH; symmetry in HH.
  unfold rm_add_i in HH; simpl in HH.
  unfold carry in HH; simpl in HH.
  rewrite fst_same_diag in HH; discriminate HH.

bbb.
  left.
  split.
   f_equal.
   unfold carry; simpl.
   rewrite fst_same_diag.
   remember (fst_same (re_frac x) 0 0) as s1 eqn:Hs1 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct s1 as [dj1| ].
    destruct Hs1; assumption.

    pose proof (Hs O) as H.
    unfold rm_add_i in H; simpl in H.
    rewrite Hs1 in H.
    rewrite xorb_false_r, xorb_true_l in H.
    apply negb_false_iff in H.
    unfold carry in H; simpl in H.
    remember (fst_same (re_frac x) 0 1) as s2 eqn:Hs2 .
    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    destruct s2 as [dj2| ]; [ idtac | clear H ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2 in H; discriminate H.
bbb.

Close Scope Z_scope.
