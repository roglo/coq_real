(* definition ℝ and addition *)

Require Import Utf8 QArith NPeano.
Require Import Real01Add Real01Cmp.

Set Implicit Arguments.

Open Scope Z_scope.

Record ℝ := mkre { R_int : Z; R_frac : I }.
Arguments mkre _%Z _%I.

Delimit Scope R_scope with R.
Arguments R_int _%R.
Arguments R_frac _%R.

Definition b2z (b : bool) := if b then 1 else 0.

Definition R_add x y :=
  {| R_int := R_int x + R_int y + b2z (carry (R_frac x) (R_frac y) 0);
     R_frac := I_add (R_frac x) (R_frac y) |}.
Arguments R_add x%R y%R.

Definition R_zero := {| R_int := 0; R_frac := I_zero |}.
Definition R_one := {| R_int := 1; R_frac := I_zero |}.

Notation "x + y" := (R_add x y) : R_scope.
Notation "0" := R_zero : R_scope.
Notation "1" := R_one : R_scope.

Definition R_norm x :=
  {| R_int := R_int x + b2z (carry (R_frac x) 0 0);
     R_frac := (R_frac x + 0)%I |}.
Arguments R_norm x%R.

Definition R_eq x y :=
  R_int (R_norm x) = R_int (R_norm y) ∧
  (R_frac x = R_frac y)%I.
Arguments R_eq x%R y%R.

Definition R_opp x := {| R_int := - R_int x - 1; R_frac := - R_frac x |}.
Definition R_sub x y := R_add x (R_opp y).
Arguments R_opp x%R.
Arguments R_sub x%R y%R.

Definition R_is_neg x := Z.ltb (R_int x) 0.
Definition R_abs x := if R_is_neg x then R_opp x else x.
Arguments R_abs x%R.
Arguments R_is_neg x%R.

Notation "x = y" := (R_eq x y) : R_scope.
Notation "x ≠ y" := (¬ R_eq x y) : R_scope.
Notation "- x" := (R_opp x) : R_scope.
Notation "x - y" := (R_sub x y) : R_scope.

Theorem fold_R_sub : ∀ x y, (x + - y)%R = (x - y)%R.
Proof. intros; reflexivity. Qed.

(* equality is equivalence relation *)

Theorem R_eq_refl : reflexive _ R_eq.
Proof.
intros x; split; reflexivity.
Qed.

Theorem R_eq_sym : symmetric _ R_eq.
Proof.
intros x y Hxy.
unfold R_eq in Hxy; unfold R_eq.
destruct Hxy; split; symmetry; assumption.
Qed.

Theorem R_eq_trans : transitive _ R_eq.
Proof.
intros x y z Hxy Hyz.
destruct Hxy, Hyz.
unfold R_eq.
split; etransitivity; eassumption.
Qed.

Add Parametric Relation : _ R_eq
 reflexivity proved by R_eq_refl
 symmetry proved by R_eq_sym
 transitivity proved by R_eq_trans
 as R_rel.

(* commutativity *)

Theorem R_add_comm : ∀ x y, (x + y = y + x)%R.
Proof.
intros x y.
unfold R_eq.
unfold R_add; simpl; split; [ idtac | apply I_add_comm ].
f_equal; [ idtac | rewrite carry_comm_l; reflexivity ].
rewrite carry_comm; f_equal.
apply Z.add_comm.
Qed.

(* neutral element *)

Theorem carry_noI_add_0_r : ∀ x, carry (x + 0%I) 0 0 = false.
Proof.
intros x.
unfold carry; simpl.
remember (fst_same (x + 0%I) 0 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [j| ].
 destruct Hs as (_, Hs); rewrite Hs; reflexivity.

 pose proof (not_I_add_0_inf_1 x 0) as H.
 contradiction.
Qed.

Theorem R_add_0_r : ∀ x, (x + 0 = x)%R.
Proof.
intros x.
unfold R_eq.
unfold R_add; simpl; split; [ idtac | apply I_add_0_r ].
rewrite Z.add_0_r.
rewrite <- Z.add_assoc; f_equal.
rewrite carry_noI_add_0_r, Z.add_0_r.
reflexivity.
Qed.

(* opposite *)

Theorem R_sub_diag : ∀ x, (x - x = 0)%R.
Proof.
intros x.
unfold R_eq, R_sub, R_opp; simpl.
split; [ idtac | rewrite fold_I_sub, I_sub_diag; reflexivity ].
unfold carry; simpl.
rewrite fst_same_diag.
rewrite fold_I_sub.
rewrite Z.add_sub_assoc, Z.add_opp_r, Z.sub_diag.
remember (fst_same (R_frac x) (- R_frac x) 0) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [j1| ].
 destruct Hs1 as (Hn1, Hs1).
 symmetry in Hs1.
 exfalso; revert Hs1; apply no_fixpoint_negb.

 clear Hs1.
 remember (fst_same (R_frac x - R_frac x) 0 0) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [j2| ].
  destruct Hs2 as (Hn2, Hs2).
  rewrite Hs2; reflexivity.

  pose proof (Hs2 O) as H.
  unfold I_add_i in H; simpl in H.
  unfold carry in H; simpl in H.
  remember (fst_same (R_frac x) (- R_frac x) 1) as s3 eqn:Hs3 .
  destruct s3 as [dj3| ].
   apply fst_same_sym_iff in Hs3; simpl in Hs3.
   destruct Hs3 as (Hn3, Hs3).
   symmetry in Hs3.
   exfalso; revert Hs3; apply no_fixpoint_negb.

   rewrite negb_xorb_diag_r in H.
   discriminate H.
Qed.

(* compatibility with equality *)

Theorem case_4 : ∀ x y z dx dy,
  (x = y)%I
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
unfold I_eq in H; simpl in H.
rename H into Hf.
destruct (lt_eq_lt_dec dx dy) as [[H1| H1]| H1].
  remember H1 as H; clear HeqH.
  apply Hny in H.
  symmetry in Hf_v.
  eapply I_eq_neq_if in H; try eassumption.
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
      eapply I_eq_neq_if in H; try eassumption.
      destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
       remember H1 as H; clear HeqH.
       unfold carry in Hc4; simpl in Hc4.
       remember (fst_same (y + z) 0 0) as s2 eqn:Hs2 .
       destruct s2 as [di2| ]; [ idtac | discriminate Hc4 ].
       apply fst_same_sym_iff in Hs2; simpl in Hs2.
       destruct Hs2 as (Hs2, _).
       destruct di2.
        clear Hs2.
        unfold I_add_i in Hc4.
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
        unfold I_add_i in H; simpl in H.
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
      eapply I_eq_neq_if in H; try eassumption.
      destruct H as [(Hxy, Hyy)| (Hxy, Hyy)]; simpl in Hxy, Hyy.
       pose proof (Hf di3) as H.
       unfold I_add_i in H; simpl in H.
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
   eapply I_eq_neq_if in H; try eassumption.
   destruct H as [(Hxy, Hyy)| (Hxy, Hyy)]; simpl in Hxy, Hyy.
    destruct di3.
     simpl in Hxy; rewrite Hxy in Htx; discriminate Htx.

     pose proof (Hf di3) as H.
     unfold I_add_i in H; simpl in H.
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
     unfold I_add_i.
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
  eapply I_eq_neq_if in H; try eassumption.
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
       unfold I_add_i in Hc4.
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

       unfold I_add_i in Hc4.
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
  (x = y)%I
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
unfold I_eq in H; simpl in H.
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

  assert (∀ dj, I_add_i x z (0 + dj) = true) as H.
   intros dj; simpl; apply Hs2.

   destruct dj1; [ revert H1; apply Nat.nlt_0_r | idtac ].
   pose proof (Hn1 O (Nat.lt_0_succ dj1)) as HH.
   apply I_add_inf_true_neq_if in H; [ idtac | assumption ].
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
      eapply I_eq_neq_if in H; try eassumption.
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
        unfold I_add_i in H; simpl in H.
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
          eapply I_eq_neq_if in H; try eassumption.
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
         eapply I_eq_neq_if in H; try eassumption.
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
         unfold I_add_i in Hc4.
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
          unfold I_add_i in Hc4.
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
          unfold I_add_i in Hc4.
          rewrite Hc3, Ht3, xorb_false_l in Hc4.
          unfold carry in Hc4; simpl in Hc4.
          remember (fst_same y z (S (S dj1))) as s5 eqn:Hs5 .
          destruct s5 as [dj5| ]; [ idtac | discriminate Hc4 ].
          apply fst_same_sym_iff in Hs5; simpl in Hs5.
          destruct Hs5 as (Hn5, Ht5).
          rewrite Hc4 in Ht5; symmetry in Ht5.
          rewrite <- Nat.add_succ_r, <- Nat.add_succ_l in Ht5.
          rewrite Hzd in Ht5; discriminate Ht5.

          unfold I_add_i in Hc4.
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
           eapply I_eq_neq_if in H; try eassumption.
           destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
            pose proof (Hf (S dj1)) as H.
            unfold I_add_i in H; simpl in H.
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
      eapply I_eq_neq_if in H; try eassumption.
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
  eapply I_eq_neq_if in H; try eassumption.
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

     assert (∀ dj, I_add_i x z (0 + dj) = true) as H.
      intros dj; simpl; apply Hs2.

      destruct dx.
       rewrite <- Ht1 in Hc1.
       apply I_add_inf_true_eq_if in H; [ idtac | assumption ].
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
       apply I_add_inf_true_neq_if in H; [ idtac | assumption ].
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

   assert (∀ dj, I_add_i x z (dx + dj) = true) as H.
    intros dj; apply Hs2.

    rewrite <- Ht1 in Hc1.
    apply I_add_inf_true_eq_if in H; [ idtac | assumption ].
    destruct H as (Hxd, Hzd).
    pose proof (Hf dx) as H.
    unfold I_add_i in H; simpl in H.
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
       unfold I_add_i in Hc4; simpl in Hc4.
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
       unfold I_add_i in Hc4; simpl in Hc4.
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
       unfold I_add_i in Hc4; simpl in Hc4.
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
  eapply I_eq_neq_if in H; try eassumption.
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

     assert (∀ dj, I_add_i x z (S dy + dj) = true) as H.
      intros dj; apply Hs2.

      rewrite <- Ht1 in Hc1.
      apply I_add_inf_true_eq_if in H; [ idtac | assumption ].
      destruct H as (Hxd, Hzd).
      pose proof (Hxd O) as H.
      rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
      rewrite Hyx in H; discriminate H.
Qed.

Theorem case_6 : ∀ x y z a b c1 c2 c3 c4 dx,
  Some dx = fst_same x 0 0
  → None = fst_same y 0 0
  → a = b + 1
  → (x = y)%I
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
 eapply I_eq_neq_if in H; try eassumption; simpl in H.
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
    unfold I_add_i in Hc4; simpl in Hc4.
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
    assert (∀ dj, I_add_i x z (dj1 + dj) = true) as H.
     intros dj; apply Hs2.

     apply I_add_inf_true_eq_if in H; [ idtac | assumption ].
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
     assert (∀ dj, I_add_i y z (dj3 + dj) = true) as H.
      intros dj; apply Hs4.

      apply I_add_inf_true_eq_if in H; [ idtac | assumption ].
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
      unfold I_add_i in Hc2; simpl in Hc2.
      destruct dj3.
       destruct dj1.
        rewrite Hc1, <- Ht3, Hc3 in Ht1; discriminate Ht1.

        simpl in Hz3.
        rewrite Hz3, Hc1 in Ht1; discriminate Ht1.

       pose proof (Hs4 O) as H.
       unfold I_add_i in H; simpl in H.
       rewrite Hn3 in H; [ idtac | apply Nat.lt_0_succ ].
       rewrite negb_xorb_diag_l, xorb_true_l in H.
       apply negb_true_iff in H.
       unfold carry in H.
       remember (fst_same y z 1) as s5 eqn:Hs5 .
       destruct s5 as [dj5| ]; [ idtac | discriminate H ].
       rewrite Hny in H; discriminate H.

     pose proof (Hs4 O) as H.
     unfold I_add_i in H.
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
 eapply I_eq_neq_if in H; try eassumption; simpl in H.
 destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
  remember Hf as H; clear HeqH.
  unfold I_eq in H; simpl in H.
  rename H into Hr.
  pose proof (Hr O) as H.
  unfold I_add_i in H; simpl in H.
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
 unfold I_add_i in Hc4.
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
  apply I_add_inf_true_neq_if in H.
   destruct H as (j, (Hj, (Hdi, (H, _)))).
   rewrite Hnx in H; discriminate H.

   intros di; apply Hs2.
Qed.

Theorem R_add_compat_r : ∀ x y z, (x = y)%R → (x + z = y + z)%R.
Proof.
intros x y z Hxy.
unfold R_eq in Hxy; simpl in Hxy.
destruct Hxy as (Hi, Hf).
unfold R_eq; simpl.
split; [ idtac | rewrite Hf; reflexivity ].
do 4 rewrite <- Z.add_assoc.
rewrite Z.add_comm; symmetry.
rewrite Z.add_comm; symmetry.
do 4 rewrite <- Z.add_assoc.
f_equal.
remember (R_frac x) as X.
remember (R_frac y) as Y.
remember (R_frac z) as Z.
remember (R_int x) as XI.
remember (R_int y) as YI.
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
  unfold I_eq in Hf; simpl in Hf.
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

Theorem R_add_compat : ∀ x y z t,
  (x = y)%R
  → (z = t)%R
  → (x + z = y + t)%R.
Proof.
intros x y z t Hxy Hzt.
transitivity (x + t)%R; [ idtac | apply R_add_compat_r; assumption ].
rewrite R_add_comm; symmetry.
rewrite R_add_comm; symmetry.
apply R_add_compat_r; assumption.
Qed.

Add Parametric Morphism : R_add
  with signature R_eq ==> R_eq ==> R_eq
  as R_add_morph.
Proof.
intros x y Hxy z t Hct.
apply R_add_compat; assumption.
Qed.

(* associativity *)

Theorem R_add_assoc_norm : ∀ x y z,
  (R_norm x + (R_norm y + R_norm z) =
   (R_norm x + R_norm y) + R_norm z)%R.
Proof.
intros x y z.
rename x into x0; rename y into y0; rename z into z0.
remember (R_norm x0) as x.
remember (R_norm y0) as y.
remember (R_norm z0) as z.
unfold R_eq; simpl.
split; [ idtac | apply I_add_assoc ].
subst x y z; simpl.
remember (R_frac x0) as x.
remember (R_frac y0) as y.
remember (R_frac z0) as z.
remember (R_int x0) as xi.
remember (R_int y0) as yi.
remember (R_int z0) as zi.
rename x0 into x1; rename y0 into y1; rename z0 into z1.
rename x into x0; rename y into y0; rename z into z0.
remember (x0 + 0)%I as x.
remember (y0 + 0)%I as y.
remember (z0 + 0)%I as z.
remember (carry (x + (y + z))%I 0%I (0)) as c1 eqn:Hc1 .
remember (carry (x + y + z)%I 0%I (0)) as c2 eqn:Hc2 .
remember (carry x (y + z)%I (0)) as c3 eqn:Hc3 .
remember (carry (x + y)%I z (0)) as c4 eqn:Hc4 .
remember (carry y z (0)) as c5 eqn:Hc5 .
remember (carry x y (0)) as c6 eqn:Hc6 .
symmetry in Hc1, Hc2, Hc3, Hc4, Hc5, Hc6.
move c2 before c1; move c3 before c2.
move c4 before c3; move c5 before c4.
move c6 before c5.
remember Hc1 as H; clear HeqH.
erewrite carry_sum_3_noI_assoc_r in H; try eassumption.
move H at top; subst c1.
remember Hc2 as H; clear HeqH.
erewrite carry_sum_3_noI_assoc_l in H; try eassumption.
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

Theorem R_noI_eq : ∀ x, (R_norm x = x)%R.
Proof.
intros x.
unfold R_eq.
split; simpl.
 rewrite Z.add_comm, Z.add_assoc.
 f_equal.
 unfold carry; simpl.
 remember (fst_same (R_frac x + 0%I) 0 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [dj1| ].
  destruct Hs1 as (Hn1, Ht1).
  rewrite Ht1; reflexivity.

  pose proof (not_I_add_0_inf_1 (R_frac x) 0) as H.
  contradiction.

 apply I_add_0_r.
Qed.

Theorem R_add_assoc : ∀ x y z, (x + (y + z) = (x + y) + z)%R.
Proof.
intros x y z.
pose proof (R_add_assoc_norm x y z) as H.
do 3 rewrite R_noI_eq in H; assumption.
Qed.

(* decidability *)

Theorem R_noI_zerop : ∀ x, {(R_norm x = 0)%R} + {(R_norm x ≠ 0)%R}.
Proof.
intros x.
remember (R_norm x) as y eqn:Hy .
unfold R_eq; simpl.
destruct (Z_zerop (R_int y)) as [H1| H1].
 rewrite H1; simpl.
 destruct (I_zerop (R_frac y)) as [H2| H2].
  left.
  split; [ idtac | assumption ].
  subst y; simpl in H1, H2; simpl; f_equal.
  unfold I_eq in H2; simpl in H2.
  unfold carry; simpl.
  rewrite fst_same_diag.
  remember (fst_same (R_frac x + 0%I) 0 0) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1; [ destruct Hs1; assumption | exfalso ].
  pose proof (not_I_add_0_inf_1 (R_frac x) 0) as H.
  contradiction.

  right; intros (Hb, Hi); contradiction.

 right; intros (Hb, Hi).
 unfold carry at 2 in Hb.
 rewrite fst_same_diag in Hb; simpl in Hb.
 unfold carry in Hb; simpl in Hb.
 remember (fst_same (R_frac y) 0 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [dj1| ].
  destruct Hs1 as (Hn1, Ht1).
  rewrite Ht1 in Hb; simpl in Hb.
  rewrite Z.add_0_r in Hb; contradiction.

  subst y; simpl in Hs1.
  pose proof (not_I_add_0_inf_1 (R_frac x) 0) as H.
  contradiction.
Qed.

Theorem R_zerop : ∀ x, {(x = 0)%R} + {(x ≠ 0)%R}.
Proof.
intros x.
destruct (R_noI_zerop x) as [H1| H1].
 left; rewrite R_noI_eq in H1; assumption.

 right; rewrite R_noI_eq in H1; assumption.
Qed.

Theorem R_dec : ∀ x y, {(x = y)%R} + {(x ≠ y)%R}.
Proof.
intros x y.
destruct (R_zerop (x - y)%R) as [Hxy| Hxy].
 left; unfold R_sub in Hxy; rewrite R_add_comm in Hxy.
 eapply R_add_compat with (x := y) in Hxy; [ idtac | reflexivity ].
 rewrite R_add_assoc, fold_R_sub, R_sub_diag, R_add_comm in Hxy.
 do 2 rewrite R_add_0_r in Hxy.
 assumption.

 right; unfold R_sub in  Hxy; intros H; apply Hxy; rewrite H.
 apply R_sub_diag.
Qed.

Theorem R_decidable : ∀ x y, Decidable.decidable (x = y)%R.
Proof.
intros x y.
destruct (R_dec x y); [ left | right ]; assumption.
Qed.

(* comparison *)

Definition R_compare x y :=
  let nx := R_norm x in
  let ny := R_norm y in
  match Zcompare (R_int nx) (R_int ny) with
  | Eq =>
      match fst_same (R_frac nx) (- (R_frac ny)) 0 with
      | Some j => if (R_frac nx)%R.[j] then Gt else Lt
      | None => Eq
      end
  | Lt => Lt
  | Gt => Gt
  end.

Definition R_lt x y := R_compare x y = Lt.
Definition R_le x y := R_compare x y ≠ Gt.
Definition R_gt x y := R_compare x y = Gt.
Definition R_ge x y := R_compare x y ≠ Lt.

Notation "x < y" := (R_lt x y) : R_scope.
Notation "x ≤ y" := (R_le x y) : R_scope.
Notation "x > y" := (R_gt x y) : R_scope.
Notation "x ≥ y" := (R_ge x y) : R_scope.
Notation "x ?= y" := (R_compare x y) : R_scope.

Theorem R_compare_eq : ∀ x y, (x = y)%R ↔ R_compare x y = Eq.
Proof.
intros x y.
split; intros H.
 unfold R_compare; simpl.
 unfold R_eq in H; simpl in H.
 destruct H as (Hi, Hf).
 apply Z.compare_eq_iff in Hi.
 rewrite Hi.
 remember (R_frac x) as xf.
 remember (R_frac y) as yf.
 remember (fst_same (xf + 0%I) (- (yf + 0)%I) 0) as s1 eqn:Hs1 .
 destruct s1 as [dj1| ]; [ exfalso | reflexivity ].
 subst xf yf.
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Ht1).
 unfold I_eq in Hf; simpl in Hf.
 rewrite Hf in Ht1; symmetry in Ht1.
 revert Ht1; apply no_fixpoint_negb.

 unfold R_compare in H.
 remember (R_int (R_norm x) ?= R_int (R_norm y)) as c eqn:Hc .
 symmetry in Hc.
 destruct c; [ idtac | discriminate H | discriminate H ].
 unfold R_eq; simpl.
 apply Z.compare_eq in Hc; simpl in Hc.
 split; [ assumption | idtac ].
 remember (R_norm x) as nx.
 remember (R_norm y) as ny.
 remember (fst_same (R_frac nx) (- R_frac ny) 0) as s1 eqn:Hs1 .
 destruct s1 as [dj1| ].
  destruct (R_frac nx) .[ dj1]; discriminate H.

  clear H.
  subst nx ny.
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  unfold I_eq; intros i; simpl.
  rewrite Hs1, negb_involutive; reflexivity.
Qed.

Theorem R_compare_lt : ∀ x y, (x < y)%R ↔ R_compare x y = Lt.
Proof.
intros x y.
split; intros H; assumption.
Qed.

Theorem R_compare_gt : ∀ x y, (x > y)%R ↔ R_compare x y = Gt.
Proof.
intros x y.
split; intros H; assumption.
Qed.

Theorem R_gt_lt_iff : ∀ x y, (x > y)%R ↔ (y < x)%R.
Proof.
intros x y.
unfold R_gt, R_lt, R_compare.
remember (R_norm x) as nx eqn:Hnx .
remember (R_norm y) as ny eqn:Hny .
rewrite Z.compare_antisym.
remember (R_int ny ?= R_int nx) as c eqn:Hc .
symmetry in Hc.
destruct c; simpl.
 remember (fst_same (R_frac nx) (- R_frac ny) 0) as s1 eqn:Hs1 .
 remember (fst_same (R_frac ny) (- R_frac nx) 0) as s2 eqn:Hs2 .
 subst nx ny; simpl.
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s1 as [j1| ].
  destruct Hs1 as (Hs1, Hn1).
  remember (I_add_i (R_frac x) 0 j1) as x0 eqn:Hx0 .
  symmetry in Hx0; apply negb_sym in Hn1.
  destruct s2 as [j2| ].
   destruct Hs2 as (Hs2, Hn2).
   remember (I_add_i (R_frac y) 0 j2) as y0 eqn:Hy0 .
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

 split; intros H; reflexivity.

 split; intros H; discriminate H.
Qed.

Theorem R_ge_le_iff : ∀ x y, (x ≥ y)%R ↔ (y ≤ x)%R.
Proof.
intros x y.
unfold R_ge, R_le.
split; intros H1 H; apply H1; clear H1.
 apply R_gt_lt_iff; assumption.

 apply R_gt_lt_iff; assumption.
Qed.

(* inequality ≤ is order *)

Theorem R_le_refl : reflexive _ R_le.
Proof.
intros x H.
unfold R_compare in H.
rewrite Z.compare_refl in H.
remember (R_norm x) as nx.
remember (fst_same (R_frac nx) (- R_frac nx) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate H ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
symmetry in Ht1.
revert Ht1; apply no_fixpoint_negb.
Qed.

Theorem R_le_antisym : Antisymmetric _ R_eq R_le.
Proof.
intros x y Hxy Hyx.
unfold R_le in Hxy, Hyx.
unfold R_compare in Hxy, Hyx.
rewrite Z.compare_antisym in Hyx.
remember (R_norm x) as nx.
remember (R_norm y) as ny.
remember (R_int nx ?= R_int ny) as c eqn:Hc .
symmetry in Hc.
destruct c; simpl in Hyx.
 remember (fst_same (R_frac nx) (- R_frac ny) 0) as sx eqn:Hsx .
 remember (fst_same (R_frac ny) (- R_frac nx) 0) as sy eqn:Hsy .
 subst nx ny.
 apply fst_same_sym_iff in Hsx; simpl in Hsx.
 apply fst_same_sym_iff in Hsy; simpl in Hsy.
 destruct sx as [dx| ]; [ idtac | clear Hxy ].
  destruct Hsx as (Hnx, Htx).
  simpl in Hxy.
  remember (I_add_i (R_frac x) 0 dx) as xb eqn:Hxb .
  symmetry in Hxb; apply negb_sym in Htx.
  destruct sy as [dy| ]; [ idtac | clear Hyx ].
   destruct Hsy as (Hny, Hty).
   simpl in Hyx.
   remember (I_add_i (R_frac y) 0 dy) as yb eqn:Hyb .
   symmetry in Hyb; apply negb_sym in Hty.
   destruct xb; [ exfalso; apply Hxy; reflexivity | clear Hxy ].
   destruct yb; [ exfalso; apply Hyx; reflexivity | clear Hyx ].
   destruct (lt_eq_lt_dec dx dy) as [[H1| H1]| H1].
    remember H1 as H; clear HeqH.
    apply Hny in H.
    rewrite Htx, Hxb in H; discriminate H.

    subst dy.
    rewrite Hxb in Hty; discriminate Hty.

    remember H1 as H; clear HeqH.
    apply Hnx in H.
    rewrite Hty, Hyb in H; discriminate H.

   rewrite Hsy, Hxb in Htx.
   exfalso; revert Htx; apply no_fixpoint_negb.

  destruct sy as [dy| ]; [ idtac | clear Hyx ].
   destruct Hsy as (Hny, Hty).
   simpl in Hyx.
   rewrite Hsx in Hty.
   rewrite negb_involutive in Hty.
   symmetry in Hty.
   exfalso; revert Hty; apply no_fixpoint_negb.

   unfold R_eq; simpl.
   apply Z.compare_eq in Hc; simpl in Hc.
   split; [ assumption | idtac ].
   unfold I_eq; simpl; intros i.
   rewrite Hsx, negb_involutive; reflexivity.

 exfalso; apply Hyx; reflexivity.

 exfalso; apply Hxy; reflexivity.
Qed.

Theorem R_le_trans : transitive _ R_le.
Proof.
intros x y z Hxy Hyz.
unfold R_le in Hxy, Hyz; unfold R_le.
unfold R_compare in Hxy, Hyz; unfold R_compare.
remember (R_norm x) as nx eqn:Hnx .
remember (R_norm y) as ny eqn:Hny .
remember (R_norm z) as nz eqn:Hnz .
remember (R_int nx ?= R_int ny) as cxy eqn:Hcxy .
remember (R_int ny ?= R_int nz) as cyz eqn:Hcyz .
remember (R_int nx ?= R_int nz) as cxz eqn:Hcxz .
symmetry in Hcxy, Hcyz, Hcxz.
destruct cxz; [ idtac | intros H; discriminate H | exfalso ].
 remember (fst_same (R_frac nx) (- R_frac nz) 0) as sxz eqn:Hsxz .
 apply fst_same_sym_iff in Hsxz; simpl in Hsxz.
 destruct sxz as [dxz| ]; [ idtac | intros H; discriminate H ].
 rewrite Hnx; simpl.
 rewrite Hnx, Hnz in Hsxz; simpl in Hsxz.
 destruct Hsxz as (Hnxz, Htxz).
 remember (I_add_i (R_frac x) 0 dxz) as bxz eqn:Hbxz .
 destruct bxz; [ exfalso | intros H; discriminate H ].
 symmetry in Hbxz; apply negb_sym in Htxz; simpl in Htxz.
 destruct cxy; [ idtac | clear Hxy | apply Hxy; reflexivity ].
  remember (fst_same (R_frac nx) (- R_frac ny) 0) as sxy eqn:Hsxy .
  apply fst_same_sym_iff in Hsxy; simpl in Hsxy.
  destruct sxy as [dxy| ]; [ idtac | clear Hxy ].
   rewrite Hnx, Hny in Hsxy; simpl in Hsxy.
   rewrite Hnx in Hxy; simpl in Hxy.
   destruct Hsxy as (Hnxy, Htxy).
   remember (I_add_i (R_frac x) 0 dxy) as bxy eqn:Hbxy .
   destruct bxy; [ apply Hxy; reflexivity | clear Hxy ].
   symmetry in Hbxy; apply negb_sym in Htxy; simpl in Htxy.
   destruct cyz; [ idtac | clear Hyz | apply Hyz; reflexivity ].
    remember (fst_same (R_frac ny) (- R_frac nz) 0) as syz eqn:Hsyz .
    apply fst_same_sym_iff in Hsyz; simpl in Hsyz.
    destruct syz as [dyz| ]; [ idtac | clear Hyz ].
     rewrite Hny, Hnz in Hsyz; simpl in Hsyz.
     rewrite Hny in Hyz; simpl in Hyz.
     destruct Hsyz as (Hnyz, Htyz).
     remember (I_add_i (R_frac y) 0 dyz) as byz eqn:Hbyz .
     destruct byz; [ apply Hyz; reflexivity | clear Hyz ].
     symmetry in Hbyz; apply negb_sym in Htyz; simpl in Htyz.
     destruct (lt_eq_lt_dec dxy dyz) as [[H1| H1]| H1].
      remember H1 as H; clear HeqH.
      apply Hnyz in H.
      rewrite Htxy in H.
      rename H into Hz.
      destruct (lt_eq_lt_dec dxy dxz) as [[H2| H2]| H2].
       remember H2 as H; clear HeqH.
       apply Hnxz in H.
       rewrite Hbxy, <- Hz in H; discriminate H.

       subst dxz.
       rewrite Hbxy in Hbxz; discriminate Hbxz.

       remember H2 as H; clear HeqH.
       apply Hnxy in H.
       rewrite Hbxz in H; rename H into Hy.
       remember H2 as H; clear HeqH.
       eapply Nat.lt_trans with (m := dxy) in H; [ idtac | eassumption ].
       apply Hnyz in H.
       rewrite H, Htxz in Hy; discriminate Hy.

      subst dyz.
      rewrite Htxy in Hbyz; discriminate Hbyz.

      remember H1 as H; clear HeqH.
      apply Hnxy in H.
      rewrite Hbyz in H.
      rename H into Hx.
      destruct (lt_eq_lt_dec dyz dxz) as [[H2| H2]| H2].
       remember H2 as H; clear HeqH.
       apply Hnxz in H.
       rewrite Hx, Htyz in H; discriminate H.

       subst dxz.
       rewrite Htyz in Htxz; discriminate Htxz.

       remember H2 as H; clear HeqH.
       apply Hnyz in H; simpl in H.
       rewrite Htxz in H.
       rename H into Hy.
       remember H1 as H; clear HeqH.
       apply Nat.lt_trans with (n := dxz) in H; [ idtac | assumption ].
       apply Hnxy in H.
       rewrite Hbxz, Hy in H; discriminate H.

     rewrite Hny, Hnz in Hsyz; simpl in Hsyz.
     destruct (lt_eq_lt_dec dxy dxz) as [[H1| H1]| H1].
      remember H1 as H; clear HeqH.
      apply Hnxz in H.
      rewrite Hbxy, <- Hsyz, Htxy in H; discriminate H.

      subst dxz.
      rewrite Hbxy in Hbxz; discriminate Hbxz.

      remember H1 as H; clear HeqH.
      apply Hnxy in H.
      rewrite Hbxz, Hsyz, Htxz in H; discriminate H.

    apply Z.compare_eq in Hcxy.
    apply Z.compare_eq in Hcxz.
    rewrite <- Hcxy, Hcxz in Hcyz.
    revert Hcyz; apply Z.lt_irrefl.

   destruct cyz; [ idtac | clear Hyz | apply Hyz; reflexivity ].
    remember (fst_same (R_frac ny) (- R_frac nz) 0) as syz eqn:Hsyz .
    apply fst_same_sym_iff in Hsyz; simpl in Hsyz.
    destruct syz as [dyz| ]; [ idtac | clear Hyz ].
     rewrite Hny, Hnz in Hsyz; simpl in Hsyz.
     rewrite Hny in Hyz; simpl in Hyz.
     destruct Hsyz as (Hnyz, Htyz).
     remember (I_add_i (R_frac y) 0 dyz) as byz eqn:Hbyz .
     destruct byz; [ apply Hyz; reflexivity | clear Hyz ].
     symmetry in Hbyz; apply negb_sym in Htyz; simpl in Htyz.
     rewrite Hnx, Hny in Hsxy; simpl in Hsxy.
     destruct (lt_eq_lt_dec dyz dxz) as [[H1| H1]| H1].
      remember H1 as H; clear HeqH.
      apply Hnxz in H.
      rewrite Hsxy, Hbyz, Htyz in H; discriminate H.

      subst dxz.
      rewrite Htyz in Htxz; discriminate Htxz.

      remember H1 as H; clear HeqH.
      apply Hnyz in H.
      apply negb_sym in H; symmetry in H.
      apply negb_sym in H.
      rewrite Htxz, <- Hsxy, Hbxz in H; discriminate H.

     rewrite Hnx, Hny in Hsxy; simpl in Hsxy.
     rewrite Hny, Hnz in Hsyz; simpl in Hsyz.
     rewrite Hsxy, Hsyz, Htxz in Hbxz; discriminate Hbxz.

    apply Z.compare_eq in Hcxy.
    apply Z.compare_eq in Hcxz.
    rewrite <- Hcxy, Hcxz in Hcyz.
    revert Hcyz; apply Z.lt_irrefl.

  destruct cyz; [ idtac | clear Hyz | apply Hyz; reflexivity ].
   apply Z.compare_eq in Hcyz.
   apply Z.compare_eq in Hcxz.
   rewrite Hcyz, Hcxz in Hcxy.
   revert Hcxy; apply Z.lt_irrefl.

   apply Z.compare_eq in Hcxz.
   rewrite Hcxz in Hcxy.
   apply Z.nle_gt in Hcxy; apply Hcxy.
   apply Z.lt_le_incl; assumption.

 destruct cxy; [ idtac | clear Hxy | apply Hxy; reflexivity ].
  destruct cyz; [ idtac | clear Hyz | apply Hyz; reflexivity ].
   apply Z.compare_eq in Hcxy.
   apply Z.compare_eq in Hcyz.
   rewrite Hcxy, <- Hcyz in Hcxz.
   apply Z.compare_gt_iff in Hcxz.
   revert Hcxz; apply Z.lt_irrefl.

   apply Z.compare_eq in Hcxy.
   rewrite Hcxy in Hcxz.
   apply Z.compare_gt_iff in Hcxz.
   apply Z.nle_gt in Hcyz; apply Hcyz.
   apply Z.lt_le_incl; assumption.

  destruct cyz; [ idtac | clear Hyz | apply Hyz; reflexivity ].
   apply Z.compare_eq in Hcyz.
   rewrite Hcyz in Hcxy.
   apply Z.compare_gt_iff in Hcxz.
   apply Z.nle_gt in Hcxy; apply Hcxy.
   apply Z.lt_le_incl; assumption.

   apply Z.compare_gt_iff in Hcxz.
   apply Z.nle_gt in Hcxz; apply Hcxz.
   apply Z.lt_le_incl.
   eapply Z.lt_trans; eassumption.
Qed.

(* inequality ≥ is order *)

Theorem R_ge_refl : reflexive _ R_ge.
Proof.
intros x H.
unfold R_compare in H.
rewrite Z.compare_refl in H.
remember (R_norm x) as nx.
remember (fst_same (R_frac nx) (- R_frac nx) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate H ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
symmetry in Ht1.
revert Ht1; apply no_fixpoint_negb.
Qed.

Theorem R_ge_antisym : Antisymmetric _ R_eq R_ge.
Proof.
intros x y Hxy Hyx.
apply R_le_antisym; intros H.
 apply R_gt_lt_iff in H; contradiction.

 apply R_gt_lt_iff in H; contradiction.
Qed.

Theorem R_ge_trans : transitive _ R_ge.
Proof.
intros x y z Hxy Hyz H.
apply R_gt_lt_iff in H.
revert H.
apply R_le_trans with (y := y); intros H.
 apply R_gt_lt_iff in H; contradiction.

 apply R_gt_lt_iff in H; contradiction.
Qed.

(* decidability < vs ≥ and > vs ≤ *)

Theorem R_lt_dec : ∀ x y, {(x < y)%R} + {(x ≥ y)%R}.
Proof.
intros x y.
unfold R_lt, R_ge; simpl.
unfold R_compare.
remember (R_norm x) as nx eqn:Hnx .
remember (R_norm y) as ny eqn:Hny .
remember (R_int nx ?= R_int ny) as c eqn:Hc .
symmetry in Hc.
destruct c.
 remember (fst_same (R_frac nx) (- R_frac ny) 0) as s eqn:Hs .
 apply fst_same_sym_iff in Hs; simpl in Hs.
 destruct s as [di| ].
  destruct Hs as (Hn, Ht).
  rewrite Hnx; simpl.
  rewrite Hnx, Hny in Ht; simpl in Ht.
  remember (I_add_i (R_frac x) 0 di) as xb eqn:Hxb .
  symmetry in Hxb; apply negb_sym in Ht.
  destruct xb; simpl in Ht.
   right; intros H; discriminate H.

   left; reflexivity.

  right; intros H; discriminate H.

 left; reflexivity.

 right; intros H; discriminate H.
Qed.

Theorem R_gt_dec : ∀ x y, {(x > y)%R} + {(x ≤ y)%R}.
Proof.
intros x y.
destruct (R_lt_dec y x) as [H1| H1].
 left.
 apply R_gt_lt_iff; assumption.

 right; intros H; apply H1.
 apply R_gt_lt_iff; assumption.
Qed.

(* *)

Theorem R_lt_decidable : ∀ x y, Decidable.decidable (x < y)%R.
Proof.
intros x y.
destruct (R_lt_dec x y); [ left | right ]; assumption.
Qed.

Theorem R_gt_decidable : ∀ x y, Decidable.decidable (x > y)%R.
Proof.
intros x y.
destruct (R_gt_dec x y); [ left | right ]; assumption.
Qed.

(* miscellaneous *)

Theorem Z_nlt_1_0 : (1 <? 0) = false.
Proof. reflexivity. Qed.

Theorem R_nneg_1 : R_is_neg 1 = false.
Proof. apply Z_nlt_1_0. Qed.

Theorem R_int_abs : ∀ x, 0 <= R_int (R_abs x).
Proof.
intros x.
unfold R_abs; simpl.
remember (R_is_neg x) as ng eqn:Hng .
symmetry in Hng.
destruct ng; simpl; [ idtac | apply Z.ltb_ge; assumption ].
apply Z.ltb_lt in Hng.
unfold Z.sub.
rewrite <- Z.opp_add_distr, <- Z.opp_0.
apply Z.opp_le_mono.
do 2 rewrite Z.opp_involutive.
apply Zlt_succ_le; simpl.
apply Z.add_lt_mono_r with (p := 1) in Hng.
assumption.
Qed.

Theorem R_abs_nonneg: ∀ x, (0 ≤ R_abs x)%R.
Proof.
intros x.
unfold R_le, R_compare; intros H.
remember (R_int (R_norm 0) ?= R_int (R_norm (R_abs x))) as c eqn:Hc .
symmetry in Hc.
destruct c; [ simpl in H | discriminate H | clear H ].
 apply Z.compare_eq in Hc; simpl in Hc.
 rewrite carry_diag in Hc; simpl in Hc.
 symmetry in Hc.
 remember (R_frac (R_abs x) + 0)%I as a.
 remember (fst_same (0%I + 0%I) (- a) 0) as s1 eqn:Hs1 ; subst a.
 destruct s1 as [dj1| ]; [ idtac | discriminate H ].
 remember (I_add_i 0 0 dj1) as b1 eqn:Hb1 .
 destruct b1; [ clear H | discriminate H ].
 unfold I_add_i in Hb1; simpl in Hb1.
 rewrite carry_diag in Hb1; discriminate Hb1.

 apply Z.compare_gt_iff in Hc; simpl in Hc.
 rewrite carry_diag in Hc; simpl in Hc.
 apply Z.add_neg_cases in Hc.
 destruct Hc as [Hc| Hc].
  pose proof (R_int_abs x) as H.
  apply Z.nlt_ge in H; contradiction.

  remember (carry (R_frac (R_abs x)) 0 0) as c.
  apply Z.nle_gt in Hc; apply Hc.
  destruct c; [ apply Z.le_0_1 | reflexivity ].
Qed.

Theorem R_zero_if : ∀ x,
  (x = 0)%R
  → (R_int x = 0 ∧ ∀ i : nat, (R_frac x).[i] = false) ∨
    (R_int x = -1 ∧ ∀ i : nat, (R_frac x).[i] = true).
Proof.
intros x Hx.
unfold R_eq in Hx.
destruct Hx as (Hi, Hf).
simpl in Hi.
rewrite carry_diag in Hi; simpl in Hi.
unfold carry in Hi; simpl in Hi.
remember (fst_same (R_frac x) 0 0) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply I_zero_iff in Hf.
destruct Hf as [Hf| Hf]; [ left | right ].
 split; [ idtac | assumption ].
 destruct s1 as [dj1| ].
  rewrite Hf, Z.add_0_r in Hi; assumption.

  pose proof (Hs1 O) as H.
  rewrite Hf in H; discriminate H.

 split; [ idtac | assumption ].
 destruct s1 as [dj1| ].
  destruct Hs1 as (Hn1, Ht1).
  rewrite Hf in Ht1; discriminate Ht1.

  simpl in Hi.
  apply Z.add_move_r in Hi; assumption.
Qed.

Theorem R_opp_involutive : ∀ x, (- - x = x)%R.
Proof.
intros x.
unfold R_eq; simpl.
split.
 rewrite Z.opp_sub_distr, Z.opp_involutive.
 rewrite <- Z.add_sub_assoc, Z.add_0_r.
 f_equal; f_equal.
 apply carry_compat; [ intros i; simpl | reflexivity ].
 apply negb_involutive.

 apply I_opp_involutive.
Qed.

Theorem R_const_if : ∀ x b, (∀ i, x.[i] = b) → (x = 0)%I.
Proof.
intros x b H.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
rewrite H, xorb_false_r, carry_diag; simpl.
unfold carry; simpl.
remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
destruct s1 as [dj1| ].
 rewrite H, xorb_nilpotent; reflexivity.

 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 pose proof (Hs1 O) as Hi.
 rewrite H in Hi; rewrite Hi; reflexivity.
Qed.

Add Parametric Morphism : R_opp
  with signature R_eq ==> R_eq
  as R_opp_morph.
Proof.
intros x y Hxy.
unfold R_eq; simpl.
unfold R_eq in Hxy; simpl in Hxy.
destruct Hxy as (Hi, Hf).
split.
 (* not fully satisfactory: why is the first goal hard to prove,
    and not the second one? *)
 unfold carry in Hi; simpl in Hi.
 unfold carry; simpl.
 remember (fst_same (R_frac x) 0 0) as s1 eqn:Hs1 .
 remember (fst_same (R_frac y) 0 0) as s2 eqn:Hs2 .
 remember (fst_same (- R_frac x) 0 0) as s3 eqn:Hs3 .
 remember (fst_same (- R_frac y) 0 0) as s4 eqn:Hs4 .
 apply fst_same_sym_iff in Hs3; simpl in Hs3.
 apply fst_same_sym_iff in Hs4; simpl in Hs4.
 destruct s3 as [dj3| ].
  destruct Hs3 as (Hn3, Ht3); rewrite Ht3, Z.add_0_r.
  apply negb_false_iff in Ht3.
  destruct s4 as [dj4| ].
   destruct Hs4 as (Hn4, Ht4); rewrite Ht4, Z.add_0_r.
   apply negb_false_iff in Ht4.
   f_equal.
   apply Z.opp_inj_wd.
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s1 as [dj1| ].
    destruct Hs1 as (Hn1, Ht1); rewrite Ht1, Z.add_0_r in Hi.
    destruct s2 as [dj2| ].
     destruct Hs2 as (Hn2, Ht2); rewrite Ht2, Z.add_0_r in Hi.
     assumption.

     apply R_const_if in Hs2.
     rewrite Hs2 in Hf.
     apply I_zero_iff in Hf.
     destruct Hf as [Hf| Hf].
      rewrite Hf in Ht3; discriminate Ht3.

      rewrite Hf in Ht1; discriminate Ht1.

    destruct s2 as [dj2| ].
     destruct Hs2 as (Hn2, Ht2).
     apply R_const_if in Hs1.
     rewrite Hs1 in Hf; symmetry in Hf.
     apply I_zero_iff in Hf.
     destruct Hf as [Hf| Hf].
      rewrite Hf in Ht4; discriminate Ht4.

      rewrite Hf in Ht2; discriminate Ht2.

     apply Z.add_cancel_r in Hi; assumption.

   unfold Z.sub.
   rewrite Z.add_shuffle0; f_equal; simpl.
   rewrite <- Z.opp_sub_distr.
   apply Z.opp_inj_wd, Z.add_move_r.
   assert (∀ dj, (R_frac y) .[ dj] = false) as H.
    intros dj; apply negb_true_iff, Hs4.

    apply R_const_if in H.
    rewrite H in Hf.
    rename H into Hy.
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    destruct s1 as [dj1| ].
     destruct Hs1 as (Hn1, Ht1).
     apply I_zero_iff in Hf.
     destruct Hf as [Hf| Hf].
      rewrite Hf in Ht3; discriminate Ht3.

      rewrite Hf in Ht1; discriminate Ht1.

     destruct s2 as [dj2| ].
      destruct Hs2 as (Hn2, Ht2).
      rewrite Ht2 in Hi.
      rewrite Z.add_0_r in Hi; assumption.

      pose proof (Hs4 O) as H.
      rewrite Hs2 in H; discriminate H.

  assert (∀ dj, (R_frac x) .[ dj] = false) as H.
   intros dj; apply negb_true_iff, Hs3.

   rewrite Z.sub_simpl_r.
   unfold Z.sub.
   rewrite <- Z.opp_add_distr.
   rewrite <- Z.opp_sub_distr.
   apply Z.opp_inj_wd, Z.add_move_r.
   apply R_const_if in H.
   rewrite H in Hf; symmetry in Hf.
   rename H into Hx.
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s1 as [dj1| ].
    destruct Hs1 as (Hn1, Ht1).
    destruct s2 as [dj2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht1, Ht2 in Hi.
     do 2 rewrite Z.add_0_r in Hi.
     destruct s4 as [dj4| ].
      destruct Hs4 as (Hn4, Ht4).
      apply I_zero_iff in Hf.
      destruct Hf as [Hf| Hf].
       rewrite Hf in Ht4; discriminate Ht4.

       rewrite Hf in Ht2; discriminate Ht2.

      rewrite Hi; reflexivity.

     destruct s4 as [dj4| ].
      destruct Hs4 as (Hn4, Ht4).
      pose proof (Hs3 dj1) as H.
      apply negb_true_iff in H.
      rewrite H, Z.add_0_r in Hi.
      rewrite Ht4, Z.add_0_r; assumption.

      pose proof (Hs4 O) as H.
      rewrite Hs2 in H; discriminate H.

    pose proof (Hs3 O) as H.
    rewrite Hs1 in H; discriminate H.

 rewrite Hf; reflexivity.
Qed.

Theorem R_eq_R_int_opp_sign : ∀ x y,
  (x = y)%R
  → R_int x < 0
  → 0 <= R_int y
  → R_int x = -1 ∧ R_int y = 0 ∧
    (∀ i, (R_frac x).[i] = true) ∧
    (∀ i, (R_frac y).[i] = false).
Proof.
intros x y Hxy Hxb Hyb.
remember Hxy as Heq; clear HeqHeq.
unfold R_eq in Hxy; simpl in Hxy.
destruct Hxy as (Hf, Hi).
unfold carry in Hf; simpl in Hf.
remember (fst_same (R_frac x) 0 0) as s1 eqn:Hs1 .
remember (fst_same (R_frac y) 0 0) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [dj1| ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1, Z.add_0_r in Hf.
 destruct s2 as [dj2| ].
  destruct Hs2 as (Hn2, Ht2).
  rewrite Ht2, Z.add_0_r in Hf.
  apply Z.nlt_ge in Hyb.
  rewrite Hf in Hxb; contradiction.

  rewrite Hf in Hxb.
  exfalso; revert Hxb Hyb; simpl; intros; omega.

 destruct s2 as [dj2| ].
  destruct Hs2 as (Hn2, Ht2).
  rewrite Ht2, Z.add_0_r in Hf.
  rewrite <- Hf in Hyb; simpl in Hyb.
  assert (R_int x = - 1) as Hx by omega.
  split; [ assumption | idtac ].
  rewrite Hx in Hf; simpl in Hf; symmetry in Hf.
  split; [ assumption | idtac ].
  split; [ assumption | idtac ].
  assert (R_frac x = 0)%I as H by (apply I_zero_iff; right; assumption).
  rename H into Hfx.
  rewrite Hfx in Hi; symmetry in Hi.
  apply I_zero_iff in Hi; simpl in Hi.
  destruct Hi as [Hi| Hi]; [ assumption | idtac ].
  rewrite Hi in Ht2; discriminate Ht2.

  apply Z.add_cancel_r in Hf.
  rewrite Hf in Hxb.
  exfalso; revert Hxb Hyb; simpl; intros; omega.
Qed.

Theorem R_eq_neg_nneg : ∀ x y,
  (x = y)%R
  → R_is_neg x = true
  → R_is_neg y = false
  → (- x = y)%R.
Proof.
intros x y Hxy Hxb Hyb.
remember Hxy as Heq; clear HeqHeq.
rewrite Hxy.
unfold R_eq in Hxy; simpl in Hxy.
destruct Hxy as (Hi, Hf).
unfold R_eq; simpl.
unfold R_is_neg in Hxb, Hyb.
apply Z.ltb_lt in Hxb.
apply Z.ltb_ge in Hyb.
remember Heq as H; clear HeqH.
apply R_eq_R_int_opp_sign in H; try assumption.
clear Hxb Hyb.
destruct H as (Hxb, (Hyb, (Hx, Hy))).
rewrite Hxb, Hyb, Z.add_0_l in Hi.
apply Z.add_move_l in Hi.
split.
 rewrite Hyb, Z.opp_0, Z.add_0_l, Z.sub_0_l.
 apply Z.add_move_l.
 rewrite Z.sub_opp_r.
 unfold carry; simpl.
 remember (fst_same (R_frac y) 0 0) as s1 eqn:Hs1 .
 remember (fst_same (- R_frac y) 0 0) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [dj2| ].
  destruct Hs2 as (Hn2, Ht2).
  rewrite Hy in Ht2; discriminate Ht2.

  destruct s1 as [dj1| ].
   destruct Hs1 as (Hn1, Ht1); rewrite Ht1; reflexivity.

   pose proof (Hs1 O) as H.
   rewrite Hy in H; discriminate H.

 unfold I_eq; simpl; intros i.
 unfold I_add_i; simpl.
 do 2 rewrite xorb_false_r.
 rewrite Hy, xorb_true_l, xorb_false_l.
 unfold carry; simpl.
 remember (fst_same (R_frac y) 0 (S i)) as s1 eqn:Hs1 .
 remember (fst_same (- R_frac y) 0 (S i)) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [dj2| ].
  destruct Hs2 as (Hn2, Ht2).
  rewrite Hy in Ht2; discriminate Ht2.

  destruct s1 as [dj1| ].
   destruct Hs1 as (Hn1, Ht1); rewrite Ht1; reflexivity.

   pose proof (Hs1 O) as H.
   rewrite Hy in H; discriminate H.
Qed.

Add Parametric Morphism : R_abs
  with signature R_eq ==> R_eq
  as R_abs_morph.
Proof.
intros x y Hxy.
unfold R_abs.
remember (R_is_neg x) as xb eqn:Hxb .
remember (R_is_neg y) as yb eqn:Hyb .
symmetry in Hxb, Hyb.
destruct xb.
 destruct yb; [ rewrite Hxy; reflexivity | idtac ].
 apply R_eq_neg_nneg; assumption.

 destruct yb; [ idtac | assumption ].
 symmetry in Hxy; symmetry.
 apply R_eq_neg_nneg; assumption.
Qed.

Theorem R_le_antisymm : ∀ x y, (x ≤ y)%R → (y ≤ x)%R → (x = y)%R.
Proof.
intros x y Hxy Hyx.
apply R_ge_le_iff in Hyx.
unfold R_le in Hxy; simpl in Hxy.
unfold R_ge in Hyx; simpl in Hyx.
apply R_compare_eq.
remember (x ?= y)%R as c eqn:Hc .
symmetry in Hc.
destruct c; [ reflexivity | exfalso | exfalso ].
 apply Hyx; reflexivity.

 apply Hxy; reflexivity.
Qed.

Theorem R_opp_inj : ∀ x y, (- x = - y)%R → (x = y)%R.
Proof.
intros x y H.
rewrite <- R_opp_involutive.
rewrite H.
apply R_opp_involutive.
Qed.

Theorem R_opp_0 : (- 0 = 0)%R.
Proof.
unfold R_eq.
remember (- 0)%R as z.
simpl.
rewrite carry_diag; simpl.
split.
 unfold carry; simpl.
 remember (fst_same (R_frac z) 0 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [dj1| ].
  destruct Hs1 as (Hn1, Ht1).
  subst z; discriminate Ht1.

  subst z; reflexivity.

 subst z; simpl.
 apply I_opp_0.
Qed.

Theorem R_abs_0 : (R_abs 0 = 0)%R.
Proof. split; reflexivity. Qed.

Theorem R_abs_0_iff : ∀ x, (R_abs x = 0)%R ↔ (x = 0)%R.
Proof.
intros x; split; intros H.
 unfold R_abs in H; simpl in H.
 remember (R_is_neg x) as c eqn:Hc .
 symmetry in Hc.
 destruct c; [ idtac | assumption ].
 rewrite <- R_opp_involutive, H.
 apply R_opp_0.

 rewrite H; apply R_abs_0.
Qed.

Theorem R_eq_compare_compat : ∀ x y z t,
  (x = y)%R
  → (z = t)%R
  → ((x ?= z)%R = (y ?= t)%R).
Proof.
intros x y z t Hxy Hzt.
unfold R_eq in Hxy, Hzt.
unfold R_compare.
destruct Hxy as (Hixy, Hfxy).
destruct Hzt as (Hizt, Hfzt).
rewrite Hixy, Hizt.
remember (R_int (R_norm y) ?= R_int (R_norm t)) as c eqn:Hc .
symmetry in Hc.
destruct c; try reflexivity.
remember (R_frac (R_norm x)) as xn eqn:Hxn .
remember (R_frac (R_norm y)) as yn eqn:Hyn .
remember (R_frac (R_norm z)) as zn eqn:Hzn .
remember (R_frac (R_norm t)) as tn eqn:Htn .
remember (fst_same xn (- zn) 0) as s1 eqn:Hs1 .
remember (fst_same yn (- tn) 0) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [dj1| ].
 destruct Hs1 as (Hn1, Ht1).
 remember xn .[ dj1] as xb eqn:Hxb .
 symmetry in Hxb; apply negb_sym in Ht1.
 destruct s2 as [dj2| ].
  destruct Hs2 as (Hn2, Ht2).
  remember yn .[ dj2] as yb eqn:Hyb .
  symmetry in Hyb; apply negb_sym in Ht2.
  subst xn yn zn tn.
  simpl in Hxb, Hyb, Ht1, Ht2, Hn1, Hn2.
  unfold I_eq in Hfxy, Hfzt; simpl in Hfxy, Hfzt.
  rewrite Hfxy in Hxb; simpl in Hxb.
  rewrite Hfzt in Ht1; simpl in Ht1.
  destruct (lt_eq_lt_dec dj1 dj2) as [[H1| H1]| H1].
   apply Hn2 in H1; simpl in H1.
   rewrite Hxb, Ht1 in H1.
   rewrite negb_involutive in H1; symmetry in H1.
   exfalso; revert H1; apply no_fixpoint_negb.

   subst dj2.
   rewrite Hxb in Hyb.
   rewrite Hyb; reflexivity.

   apply Hn1 in H1.
   rewrite Hfxy, Hfzt, Hyb, Ht2 in H1.
   rewrite negb_involutive in H1; symmetry in H1.
   exfalso; revert H1; apply no_fixpoint_negb.

  subst xn yn zn tn.
  simpl in Hxb, Ht1, Hn1, Hs2.
  unfold I_eq in Hfxy, Hfzt; simpl in Hfxy, Hfzt.
  rewrite Hfxy in Hxb; simpl in Hxb.
  rewrite Hfzt in Ht1; simpl in Ht1.
  rewrite Hs2 in Hxb.
  rewrite Ht1, negb_involutive in Hxb.
  exfalso; revert Hxb; apply no_fixpoint_negb.

 destruct s2 as [dj2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Ht2).
 subst xn yn zn tn.
 simpl in Hs1, Ht2, Hn2.
 unfold I_eq in Hfxy, Hfzt; simpl in Hfxy, Hfzt.
 rewrite <- Hfxy, <- Hfzt in Ht2.
 rewrite Hs1, negb_involutive in Ht2.
 symmetry in Ht2.
 exfalso; revert Ht2; apply no_fixpoint_negb.
Qed.

Theorem R_eq_lt_compat : ∀ x y z t,
  (x = y)%R
  → (z = t)%R
  → (x < z)%R
  → (y < t)%R.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold R_lt in Hxz; unfold R_lt.
rewrite <- Hxz; symmetry.
apply R_eq_compare_compat; eassumption.
Qed.

Theorem R_eq_le_compat : ∀ x y z t,
  (x = y)%R
  → (z = t)%R
  → (x ≤ z)%R
  → (y ≤ t)%R.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold R_le in Hxz; unfold R_le.
intros H; apply Hxz; rewrite <- H.
apply R_eq_compare_compat; eassumption.
Qed.

Theorem R_eq_gt_compat : ∀ x y z t,
  (x = y)%R
  → (z = t)%R
  → (x > z)%R
  → (y > t)%R.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold R_gt in Hxz; unfold R_gt.
rewrite <- Hxz; symmetry.
apply R_eq_compare_compat; eassumption.
Qed.

Theorem R_eq_ge_compat : ∀ x y z t,
  (x = y)%R
  → (z = t)%R
  → (x ≥ z)%R
  → (y ≥ t)%R.
Proof.
intros x y z t Hxy Hzt Hxz.
unfold R_ge in Hxz; unfold R_ge.
intros H; apply Hxz; rewrite <- H.
apply R_eq_compare_compat; eassumption.
Qed.

Add Parametric Morphism : R_lt
  with signature R_eq ==> R_eq ==> iff
  as R_lt_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply R_eq_lt_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply R_eq_lt_compat; eassumption.
Qed.

Add Parametric Morphism : R_le
  with signature R_eq ==> R_eq ==> iff
  as R_le_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply R_eq_le_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply R_eq_le_compat; eassumption.
Qed.

Add Parametric Morphism : R_gt
  with signature R_eq ==> R_eq ==> iff
  as R_gt_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply R_eq_gt_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply R_eq_gt_compat; eassumption.
Qed.

Add Parametric Morphism : R_ge
  with signature R_eq ==> R_eq ==> iff
  as R_ge_morph.
Proof.
intros x y Hxy z t Hzt.
split; intros H.
 eapply R_eq_ge_compat; eassumption.

 symmetry in Hxy, Hzt.
 eapply R_eq_ge_compat; eassumption.
Qed.

Theorem R_lt_irrefl : ∀ x, ¬(x < x)%R.
Proof.
intros x Hx.
unfold R_lt, R_compare in Hx.
remember (R_int (R_norm x) ?= R_int (R_norm x)) as c eqn:Hc .
symmetry in Hc.
destruct c; [ idtac | idtac | discriminate Hx ].
 simpl in Hx.
 remember (fst_same (R_frac x + 0%I) (- (R_frac x + 0)%I) 0) as s1 eqn:Hs1 .
 destruct s1 as [dj1| ]; [ idtac | discriminate Hx ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Ht1).
 symmetry in Ht1; revert Ht1; apply no_fixpoint_negb.

 revert Hc; apply Z.lt_irrefl.
Qed.

Close Scope Z_scope.
