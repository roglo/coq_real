(* Implementation of rationals using only nat *)

Require Import Utf8 Arith Morphisms.
Require Import PQ.

Delimit Scope MQ_scope with MQ.

Record MQ := MQmake { MQsign : bool; MQpos : PQ }.
Arguments MQmake _ _%PQ.
Arguments MQsign x%MQ : rename.
Arguments MQpos x%MQ : rename.

Notation "0" := (MQmake true 0) : MQ_scope.

(* equality *)

Definition MQeq x y :=
  if Bool.eqb (MQsign x) (MQsign y) then (MQpos x == MQpos y)%PQ
  else if zerop (PQnum (MQpos x) + PQnum (MQpos y)) then True
  else False.

Notation "x == y" := (MQeq x y) (at level 70) : MQ_scope.

Theorem MQeq_refl : ∀ x : MQ, (x == x)%MQ.
Proof.
intros.
unfold "=="%MQ.
now rewrite Bool.eqb_reflx.
Qed.

Theorem Bool_eqb_comm : ∀ b1 b2, Bool.eqb b1 b2 = Bool.eqb b2 b1.
Proof.
intros.
unfold Bool.eqb.
now destruct b1, b2.
Qed.

Theorem Bool_eqb_assoc : ∀ b1 b2 b3,
  Bool.eqb (Bool.eqb b1 b2) b3 = Bool.eqb b1 (Bool.eqb b2 b3).
Proof.
intros.
unfold Bool.eqb.
now destruct b1, b2, b3.
Qed.

Theorem MQeq_symm : ∀ x y : MQ, (x == y)%MQ → (y == x)%MQ.
Proof.
unfold "=="%MQ.
intros * Hxy.
rewrite Bool_eqb_comm, Nat.add_comm.
now destruct (Bool.eqb (MQsign x) (MQsign y)).
Qed.

Theorem MQeq_trans : ∀ x y z : MQ, (x == y)%MQ → (y == z)%MQ → (x == z)%MQ.
Proof.
unfold "=="%MQ.
intros * Hxy Hyz.
remember (Bool.eqb (MQsign x) (MQsign y)) as b1 eqn:Hb1.
symmetry in Hb1.
destruct b1.
-apply -> Bool.eqb_true_iff in Hb1.
 rewrite Hb1.
 remember (Bool.eqb (MQsign y) (MQsign z)) as b2 eqn:Hb2.
 symmetry in Hb2.
 destruct b2; [ now rewrite Hxy | ].
 destruct (zerop (PQnum (MQpos y) + PQnum (MQpos z))) as [H1| H1]; [ | easy ].
 apply Nat.eq_add_0 in H1.
 destruct H1 as (H1, H2).
 rewrite H2, Nat.add_0_r.
 unfold "=="%PQ in Hxy.
 unfold nd in Hxy.
 rewrite H1, Nat.mul_0_l in Hxy.
 apply Nat.eq_mul_0_l in Hxy; [ | easy ].
 now rewrite Hxy.
-destruct (zerop (PQnum (MQpos x) + PQnum (MQpos y))) as [H1| H1]; [ | easy ].
 apply Nat.eq_add_0 in H1.
 destruct H1 as (H1, H2).
 rewrite H1, Nat.add_0_l.
 rewrite H2, Nat.add_0_l in Hyz.
 apply -> Bool.eqb_false_iff in Hb1.
 remember (Bool.eqb (MQsign y) (MQsign z)) as b2 eqn:Hb2.
 remember (Bool.eqb (MQsign x) (MQsign z)) as b3 eqn:Hb3.
 symmetry in Hb2, Hb3.
 destruct b2.
 +apply -> Bool.eqb_true_iff in Hb2.
  destruct b3.
  *apply -> Bool.eqb_true_iff in Hb3.
   now rewrite Hb2 in Hb1.
  *destruct (zerop (PQnum (MQpos z))) as [| H3]; [ easy | ].
   unfold "=="%PQ, nd in Hyz.
   rewrite H2, Nat.mul_0_l in Hyz.
   symmetry in Hyz.
   apply Nat.eq_mul_0_l in Hyz; [ | easy ].
   now rewrite Hyz in H3.
 +destruct (zerop (PQnum (MQpos z))) as [H3| ]; [ | easy ].
  destruct b3; [ | easy ].
  unfold "=="%PQ, nd.
  now rewrite H1, H3.
Qed.

Add Parametric Relation : _ MQeq
 reflexivity proved by MQeq_refl
 symmetry proved by MQeq_symm
 transitivity proved by MQeq_trans
 as MQeq_equiv_rel.

Instance MQmake_morph : Proper (eq ==> PQeq ==> MQeq) MQmake.
Proof.
intros sx sy Hs x y Hxy.
unfold "=="%MQ; simpl.
rewrite Hs.
now rewrite Bool.eqb_reflx.
Qed.

(*
Instance MQeq_morph : Proper (MQeq ==> MQeq ==> iff) MQeq.
Proof.
Admitted.
*)

(*
Notation "x < y" := (MQlt x y) : MQ_scope.
Notation "x ≤ y" := (MQle x y) : MQ_scope.
Notation "x > y" := (¬ MQle x y) : MQ_scope.
Notation "x ≥ y" := (¬ MQlt x y) : MQ_scope.
*)

(* addition *)

Definition MQadd x y :=
  if Bool.eqb (MQsign x) (MQsign y) then
    MQmake (MQsign x) (MQpos x + MQpos y)
  else if PQlt_le_dec (MQpos x) (MQpos y) then
    MQmake (MQsign y) (MQpos y - MQpos x)
  else
    MQmake (MQsign x) (MQpos x - MQpos y).

Definition MQopp x := MQmake (negb (MQsign x)) (MQpos x).

Notation "- x" := (MQopp x) : MQ_scope.
Notation "x + y" := (MQadd x y) : MQ_scope.
Notation "x - y" := (MQadd x (MQopp y)) : MQ_scope.

(*
Instance MQpos_morph : Proper (MQeq ==> PQeq) MQpos.
Proof.
Admitted.
*)

Open Scope MQ_scope.

Theorem MQadd_comm : ∀ x y, x + y == y + x.
Proof.
intros.
unfold "==".
remember (Bool.eqb (MQsign (x + y)) (MQsign (y + x))) as b1 eqn:Hb1.
symmetry in Hb1.
unfold "+"%MQ in Hb1 |-*.
rewrite Bool_eqb_comm in Hb1 |-*.
remember (Bool.eqb (MQsign y) (MQsign x)) as byx eqn:Hbyx.
symmetry in Hbyx.
destruct b1.
-destruct byx; simpl; [ apply PQadd_comm | ].
 destruct (PQlt_le_dec (MQpos x) (MQpos y)) as [H1| H1]; simpl.
 +destruct (PQlt_le_dec (MQpos y) (MQpos x)) as [H2| H2]; [ simpl | easy ].
  now apply PQlt_le_incl, PQnlt_ge in H2.
 +destruct (PQlt_le_dec (MQpos y) (MQpos x)) as [H2| H2]; [ easy | simpl ].
  now rewrite (PQle_antisymm _ _ H1 H2).
-rewrite Bool_eqb_comm in Hbyx.
 rewrite Hbyx in Hb1.
 destruct byx; simpl in Hb1 |-*.
 +now rewrite Bool_eqb_comm, Hb1 in Hbyx.
 +destruct (PQlt_le_dec (MQpos y) (MQpos x)) as [H1| H1]; simpl in Hb1; simpl.
  *destruct (PQlt_le_dec (MQpos x) (MQpos y)) as [H2| H2].
  --apply PQnle_gt in H2; exfalso; apply H2.
    now apply PQlt_le_incl.
  --simpl in Hb1.
    now rewrite Bool.eqb_reflx in Hb1.
  *destruct (PQlt_le_dec (MQpos x) (MQpos y)) as [H2| H2]; simpl in Hb1 |-*.
  --now rewrite Bool.eqb_reflx in Hb1.
  --specialize (PQle_antisymm _ _ H1 H2) as H3.
    destruct
      (zerop (PQsub_num (MQpos x) (MQpos y) + PQsub_num (MQpos y) (MQpos x)))
      as [H4| H4]; [ easy | ].
    unfold "=="%PQ, nd in H3.
    unfold PQsub_num, nd in H4.
    now rewrite H3, Nat.sub_diag in H4.
Qed.

Theorem MQadd_assoc : ∀ x y z, (x + y) + z == x + (y + z).
Proof.
intros.
unfold "=="%MQ.
remember (Bool.eqb (MQsign (x + y + z)) (MQsign (x + (y + z)))) as b1 eqn:Hb1.
symmetry in Hb1.
destruct b1.
-apply -> Bool.eqb_true_iff in Hb1.
 unfold "+"%MQ.
 remember (Bool.eqb (MQsign x) (MQsign y)) as bxy eqn:Hbxy.
 remember (Bool.eqb (MQsign x) (MQsign z)) as bxz eqn:Hbxz.
 remember (Bool.eqb (MQsign y) (MQsign z)) as byz eqn:Hbyz.
 symmetry in Hbxy, Hbyz, Hbxz.
 move byz before bxy; move bxz before byz.
 destruct bxy; simpl.
 +apply -> Bool.eqb_true_iff in Hbxy.
  rewrite Hbxy, Hbyz.
  destruct byz.
  *rewrite Bool.eqb_reflx; simpl; apply PQadd_assoc.
  *destruct (PQlt_le_dec (MQpos x + MQpos y) (MQpos z)) as [H1| H1].
  --simpl.
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2].
   ++simpl; rewrite Hbyz.
     destruct (PQlt_le_dec (MQpos x) (MQpos z - MQpos y)) as [H3| H3].
    **simpl.
      rewrite PQadd_comm.
      apply PQsub_add_distr.
    **exfalso.
      apply PQnlt_ge in H3; apply H3; clear H3.
      now apply PQlt_add_lt_sub_r.
   ++exfalso.
     apply PQnle_gt in H1; apply H1.
     rewrite <- PQadd_0_l.
     apply PQadd_le_mono; [ apply PQle_0_l | easy ].
  --simpl.
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2].
   ++simpl; rewrite Hbyz.
     destruct (PQlt_le_dec (MQpos x) (MQpos z - MQpos y)) as [H3| H3].
    **exfalso.
      apply PQnle_gt in H3; apply H3.
      now apply PQle_sub_le_add_r.
    **simpl; symmetry.
      apply PQsub_sub_assoc.
      split; [ now apply PQlt_le_incl | easy ].
   ++rewrite Bool.eqb_reflx; simpl; symmetry.
     now apply PQadd_sub_assoc.
 +destruct (PQlt_le_dec (MQpos x) (MQpos y)) as [H1| H1].
  *simpl; rewrite Hbyz.
   destruct byz.
  --simpl; rewrite Hbxy.
    destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H2| H2].
   ++simpl; setoid_rewrite PQadd_comm.
     now apply PQadd_sub_assoc, PQlt_le_incl.
   ++exfalso.
     apply PQnlt_ge in H2; apply H2; clear H2.
     eapply PQlt_le_trans; [ apply H1 | ].
     rewrite <- PQadd_0_r at 1.
     apply PQadd_le_mono; [ | apply PQle_0_l ].
     now unfold "≤"%PQ.
  --destruct (PQlt_le_dec (MQpos y - MQpos x) (MQpos z)) as [H2| H2].
   ++simpl.
     destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H3| H3].
    **simpl; rewrite Hbxz.
      destruct bxz.
    ---simpl.
       rewrite PQadd_sub_assoc; [ | now apply PQlt_le_incl ].
       rewrite PQadd_comm.
       apply PQsub_sub_assoc.
       split; [ now apply PQlt_le_incl | ].
       eapply PQle_trans; [ apply PQlt_le_incl, H3 | ].
       rewrite <- PQadd_0_r at 1.
       apply PQadd_le_mono; [ | apply PQle_0_l ].
       now unfold "≤"%PQ.
    ---apply Bool.eqb_false_iff in Hbxy.
       apply Bool.eqb_false_iff in Hbyz.
       apply Bool.eqb_false_iff in Hbxz.
       now destruct (MQsign x), (MQsign y), (MQsign z).
    **simpl; rewrite Hbxy.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H4| H4].
    ---exfalso.
       apply PQnle_gt in H4; apply H4.
       apply PQle_sub_le_add_r.
       rewrite PQadd_comm.
       now apply PQle_sub_le_add_r, PQlt_le_incl.
    ---simpl.
       rewrite PQsub_sub_assoc.
     +++rewrite PQsub_sub_assoc; [ now rewrite PQadd_comm | ].
        split; [ easy | now apply PQle_sub_le_add_r ].
     +++split; [ now apply PQlt_le_incl | ].
        now apply PQle_sub_le_add_r, PQlt_le_incl.
   ++simpl.
     destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H3| H3].
    **simpl; rewrite Hbxz.
      destruct bxz.
    ---exfalso.
       apply PQnlt_ge in H2; apply H2; clear H2.
       eapply PQle_lt_trans; [ | apply H3 ].
       apply PQle_sub_le_add_r.
       rewrite <- PQadd_0_r at 1.
       apply PQadd_le_mono; [ | apply PQle_0_l ].
       now unfold "≤"%PQ.
    ---apply Bool.eqb_false_iff in Hbxy.
       apply Bool.eqb_false_iff in Hbyz.
       apply Bool.eqb_false_iff in Hbxz.
       now destruct (MQsign x), (MQsign y), (MQsign z).
    **simpl; rewrite Hbxy.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H4| H4].
    ---apply PQsub_sub_swap.
    ---simpl.
       transitivity 0%PQ; [ | symmetry ].
     +++rewrite PQsub_sub_swap.
        now apply PQsub_0_le.
     +++apply PQsub_0_le.
        apply PQle_add_le_sub_l.
        apply (PQadd_le_mono_r _ _ (MQpos x)) in H2.
        rewrite PQsub_add in H2; [ easy | ].
        now apply PQlt_le_incl.
  *simpl; rewrite Hbxz.
   destruct bxz.
  --simpl.
    destruct byz.
   ++exfalso.
     apply Bool.eqb_false_iff in Hbxy.
     apply -> Bool.eqb_true_iff in Hbyz.
     apply -> Bool.eqb_true_iff in Hbxz.
     now rewrite Hbyz, <- Hbxz in Hbxy.
   ++simpl.
     destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2].
    **simpl; rewrite Hbxz; simpl.
      rewrite PQadd_sub_assoc; [ | now apply PQlt_le_incl ].
      rewrite PQadd_comm.
      rewrite PQadd_sub_assoc; [ | easy ].
      now rewrite PQadd_comm.
    **simpl; rewrite Hbxy.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H3| H3].
    ---exfalso.
       apply PQnle_gt in H3; apply H3.
       apply (PQle_trans _ (MQpos y)); [ | easy ].
       apply PQle_sub_le_add_r.
       rewrite <- PQadd_0_r at 1.
       apply PQadd_le_mono; [ | apply PQle_0_l ].
       now unfold "≤"%PQ.
    ---simpl; symmetry.
       rewrite PQsub_sub_assoc.
     +++now apply PQadd_sub_swap.
     +++split; [ easy | ].
        now apply PQle_sub_le_add_r.
  --destruct (PQlt_le_dec (MQpos x - MQpos y) (MQpos z)) as [H2| H2].
   **simpl.
     destruct byz.
   ---simpl; rewrite Hbxy.
      destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H3| H3].
    +++simpl.
       rewrite PQadd_comm.
       apply PQsub_sub_assoc.
       split; [ easy | now rewrite PQadd_comm; apply PQlt_le_incl ].
    +++exfalso.
       apply PQle_add_le_sub_l in H3.
       now apply PQnlt_ge in H3.
   ---exfalso.
      apply Bool.eqb_false_iff in Hbxy.
      apply Bool.eqb_false_iff in Hbyz.
      apply Bool.eqb_false_iff in Hbxz.
      now destruct (MQsign x), (MQsign y), (MQsign z).
   **simpl.
     destruct byz.
   ---simpl; rewrite Hbxy.
      destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H3| H3].
    +++exfalso.
       apply PQnlt_ge in H2; apply H2; clear H2.
       apply (PQadd_lt_mono_r _ _ (MQpos y)).
       rewrite PQsub_add; [ | easy ].
       now rewrite PQadd_comm.
    +++simpl; symmetry.
       apply PQsub_add_distr.
   ---exfalso.
      apply Bool.eqb_false_iff in Hbxy.
      apply Bool.eqb_false_iff in Hbyz.
      apply Bool.eqb_false_iff in Hbxz.
      now destruct (MQsign x), (MQsign y), (MQsign z).
-destruct (zerop (PQnum (MQpos (x + y + z)) + PQnum (MQpos (x + (y + z)))))
    as [H1| H1]; [ easy | ].
 apply Bool.eqb_false_iff in Hb1.
 unfold "+"%MQ in Hb1, H1.
 remember (Bool.eqb (MQsign x) (MQsign y)) as bxy eqn:Hbxy.
 remember (Bool.eqb (MQsign x) (MQsign z)) as bxz eqn:Hbxz.
 remember (Bool.eqb (MQsign y) (MQsign z)) as byz eqn:Hbyz.
 symmetry in Hbxy, Hbxz, Hbyz.
 move bxz before bxy; move byz before bxz.
 move Hbxz before Hbxy; move Hbyz before Hbxz.
 destruct bxy.
 +simpl in Hb1, H1.
  apply -> Bool.eqb_true_iff in Hbxy.
  rewrite <- Hbxy, Hbxz in Hbyz; subst byz.
  rewrite <- Hbxy, Hbxz in Hb1, H1.
  destruct bxz.
  *simpl in Hb1, H1.
   rewrite Bool.eqb_reflx in Hb1, H1.
   now simpl in Hb1, H1.
  *destruct (PQlt_le_dec (MQpos x + MQpos y) (MQpos z)) as [H2| H2].
  --simpl in Hb1, H1.
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H3| H3].
   ++simpl in Hb1, H1.
     rewrite Hbxz in Hb1, H1.
     destruct (PQlt_le_dec (MQpos x) (MQpos z - MQpos y)) as [H4| H4].
    **now simpl in Hb1.
    **simpl in Hb1, H1.
      apply PQle_sub_le_add_r in H4.
      now apply PQnlt_ge in H4; apply H4.
   ++apply PQnlt_ge in H3; apply H3.
     eapply PQle_lt_trans; [ | apply H2 ].
     apply PQle_sub_le_add_r.
     rewrite PQsub_diag.
     apply PQle_0_l.
  --simpl in Hb1, H1.
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H3| H3].
   ++simpl in Hb1, H1.
     rewrite Hbxz in Hb1, H1.
     destruct (PQlt_le_dec (MQpos x) (MQpos z - MQpos y)) as [H4| H4].
    **simpl in Hb1, H1.
      apply PQlt_add_lt_sub_r in H4.
      now apply PQnlt_ge in H2.
    **easy.
   ++now rewrite Bool.eqb_reflx in Hb1.
 +destruct (PQlt_le_dec (MQpos x) (MQpos y)) as [H2| H2].
  *simpl in Hb1, H1.
   rewrite Hbyz in Hb1, H1.
   destruct byz.
  --simpl in Hb1, H1.
    rewrite Hbxy in Hb1, H1.
    destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H3| H3].
   ++easy.
   ++apply PQnlt_ge in H3; apply H3.
     eapply PQlt_le_trans; [ apply H2 | ].
     rewrite PQadd_comm.
     apply PQle_sub_le_add_r.
     rewrite PQsub_diag.
     apply PQle_0_l.
  --destruct (PQlt_le_dec (MQpos y - MQpos x) (MQpos z)) as [H3| H3].
   ++simpl in Hb1, H1.
     destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H4| H4].
    **simpl in Hb1, H1.
      rewrite Hbxz in Hb1, H1.
      destruct bxz.
    ---simpl in Hb1, H1.
       apply -> Bool.eqb_true_iff in Hbxz.
       now symmetry in Hbxz.
    ---apply Bool.eqb_false_iff in Hbxy.
       apply Bool.eqb_false_iff in Hbxz.
       apply Bool.eqb_false_iff in Hbyz.
       now destruct (MQsign x), (MQsign y), (MQsign z).
    **simpl in Hb1, H1.
      rewrite Hbxy in Hb1, H1.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H5| H5].
    ---apply PQnle_gt in H5; apply H5.
       apply PQle_sub_le_add_r.
       rewrite PQadd_comm.
       now apply PQle_sub_le_add_r, PQlt_le_incl.
    ---simpl in Hb1, H1.
       destruct bxz.
     +++apply -> Bool.eqb_true_iff in Hbxz.
        now symmetry in Hbxz.
     +++apply Bool.eqb_false_iff in Hbxy.
        apply Bool.eqb_false_iff in Hbxz.
        apply Bool.eqb_false_iff in Hbyz.
        now destruct (MQsign x), (MQsign y), (MQsign z).
   ++simpl in Hb1, H1.
     destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H4| H4]; simpl in Hb1, H1.
    **clear Hb1 H1.
      apply PQnlt_ge in H3; apply H3.
      eapply PQle_lt_trans; [ | apply H4 ].
      apply PQle_sub_le_add_r.
      rewrite <- PQadd_0_r at 1.
      apply PQadd_le_mono; [ | apply PQle_0_l ].
      now unfold "≤"%PQ.
    **rewrite Hbxy in Hb1, H1.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H5| H5].
    ---easy.
    ---simpl in Hb1, H1.
       apply PQle_sub_le_add_r in H5.
       rewrite PQadd_comm in H5.
       apply PQle_sub_le_add_r in H5.
       specialize (PQle_antisymm _ _ H3 H5) as H6.
       unfold "=="%PQ in H6.
       unfold PQsub_num in H1.
       rewrite H6, Nat.sub_diag, Nat.add_0_l in H1.
       apply (PQadd_le_mono_r _ _ (MQpos x)) in H3.
       apply (PQadd_le_mono_r _ _ (MQpos x)) in H5.
       rewrite PQsub_add in H3; [ | now apply PQlt_le_incl ].
       rewrite PQsub_add in H5; [ | now apply PQlt_le_incl ].
       rewrite PQadd_comm in H3, H5.
       apply PQle_add_le_sub_r in H3.
       apply PQle_sub_le_add_r in H5.
       specialize (PQle_antisymm _ _ H3 H5) as H7.
       unfold "=="%PQ in H7.
       now rewrite H7, Nat.sub_diag in H1.
  *simpl in Hb1, H1.
   rewrite Hbxz in Hb1, H1.
   destruct bxz; simpl in Hb1, H1.
  --destruct byz; simpl in Hb1, H1.
   ++apply Bool.eqb_false_iff in Hbxy.
     apply -> Bool.eqb_true_iff in Hbxz.
     apply -> Bool.eqb_true_iff in Hbyz.
     now rewrite Hbxz, Hbyz in Hbxy.
   ++destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H3| H3]; simpl in Hb1, H1.
    **now rewrite Hbxz in Hb1.
    **rewrite Hbxy in Hb1, H1; simpl in Hb1, H1.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H4| H4].
    ---clear Hb1 H1.
       apply PQnlt_ge in H2; apply H2.
       eapply PQlt_le_trans; [ apply H4 | ].
       apply PQle_sub_le_add_r.
       rewrite PQadd_comm.
       apply PQle_sub_le_add_r.
       rewrite PQsub_diag.
       apply PQle_0_l.
    ---easy.
  --destruct byz; simpl in Hb1, H1.
   ++rewrite Hbxy in Hb1, H1.
     destruct (PQlt_le_dec (MQpos x - MQpos y) (MQpos z)) as [H3| H3].
    **simpl in Hb1, H1.
      destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H4| H4].
    ---simpl in Hb1, H1.
       apply -> Bool.eqb_true_iff in Hbyz.
       now rewrite Hbyz in Hb1.
    ---simpl in Hb1, H1.
       apply PQnle_gt in H3; apply H3.
       now apply PQle_add_le_sub_l.
    **simpl in Hb1, H1.
      destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H4| H4].
    ---simpl in Hb1, H1.
       apply PQnlt_ge in H3; apply H3.
       apply (PQadd_lt_mono_r _ _ (MQpos y)).
       rewrite PQsub_add; [ | easy ].
       now rewrite PQadd_comm.
    ---easy.
   ++clear Hb1 H1.
     apply Bool.eqb_false_iff in Hbxy.
     apply Bool.eqb_false_iff in Hbxz.
     apply Bool.eqb_false_iff in Hbyz.
     now destruct (MQsign x), (MQsign y), (MQsign z).
Qed.

(* multiplication *)

Definition MQmul x y :=
  MQmake (Bool.eqb (MQsign x) (MQsign y)) (MQpos x * MQpos y).

Notation "x * y" := (MQmul x y) : MQ_scope.

Theorem MQmul_comm : ∀ x y, x * y == y * x.
Proof.
intros.
unfold MQmul.
now rewrite Bool_eqb_comm, PQmul_comm.
Qed.

Theorem MQmul_assoc : ∀ x y z, (x * y) * z == x * (y * z).
Proof.
intros.
unfold MQmul; simpl.
now rewrite Bool_eqb_assoc, PQmul_assoc.
Qed.

Theorem MQpos_mul : ∀ x y, (MQpos (x * y) == MQpos x * MQpos y)%PQ.
Proof. easy. Qed.

Theorem MQmul_add_distr_l : ∀ x y z, x * (y + z) == x * y + x * z.
Proof.
intros.
unfold "=="; simpl.
remember
  (Bool.eqb (Bool.eqb (MQsign x) (MQsign (y + z))) (MQsign (x * y + x * z)))
  as b1 eqn:Hb1.
symmetry in Hb1.
destruct b1.
-rewrite <- MQpos_mul.
 unfold "+"%MQ, "*"%MQ; simpl.
 remember (Bool.eqb (MQsign y) (MQsign z)) as byz eqn:Hbyz.
 symmetry in Hbyz.
 destruct byz; simpl.
 +apply -> Bool.eqb_true_iff in Hbyz.
  rewrite Hbyz, Bool.eqb_reflx; simpl.
  apply PQmul_add_distr_l.
 +assert
    (H : Bool.eqb
           (Bool.eqb (MQsign x) (MQsign y)) (Bool.eqb (MQsign x) (MQsign z)) =
      false). {
    now destruct (MQsign x), (MQsign y), (MQsign z).
  }
  rewrite H; clear H.
  destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H1| H1]; simpl.
  *destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z)) as [H2| H2].
  --apply PQmul_sub_distr_l.
  --simpl.
    destruct (PQeq_dec (MQpos x) 0) as [H3| H3].
   ++rewrite H3.
     do 3 rewrite PQmul_0_l.
     now rewrite PQsub_0_r.
   ++exfalso.
     apply PQmul_le_mono_pos_l in H2; [ | easy ].
     now apply PQnlt_ge in H2.
  *destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z)) as [H2| H2].
  --simpl.
    destruct (PQeq_dec (MQpos x) 0) as [H3| H3].
   ++rewrite H3.
     do 3 rewrite PQmul_0_l.
     now rewrite PQsub_0_r.
   ++exfalso.
     apply PQnle_gt in H2; apply H2.
     now apply PQmul_le_mono_pos_l.
  --apply PQmul_sub_distr_l.
-destruct
   (zerop
      (PQmul_num (MQpos x) (MQpos (y + z)) + PQnum (MQpos (x * y + x * z))))
   as [H1| H1]; [ easy | ].
 unfold PQmul_num in H1.
 remember (MQsign x) as sx eqn:Hsx.
 symmetry in Hsx.
 destruct sx; simpl in Hb1.
 +remember (MQsign (y + z)) as syz eqn:Hsyz.
  symmetry in Hsyz.
  unfold "+" in Hsyz.
  remember (MQsign y) as sy eqn:Hsy.
  symmetry in Hsy.
  remember (MQsign z) as sz eqn:Hsz.
  symmetry in Hsz.
  destruct syz; simpl in Hb1.
  *remember (MQsign (x * y + x * z)) as s eqn:Hs.
   symmetry in Hs.
   destruct s; [ easy | clear Hb1 ].
   unfold "+" in Hs; simpl in Hs.
   rewrite Hsx in Hs; simpl in Hs.
   rewrite Hsy, Hsz in Hs; simpl in Hs.
   destruct sy; simpl in Hsyz, Hs.
  --destruct sz; simpl in Hs; [ easy | ].
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2]; [ easy | ].
    clear Hsyz.
    destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z))
      as [H3| H3]; [ clear Hs | easy ].
    apply PQnle_gt in H3.
    apply H3; clear H3.
    now apply PQmul_le_mono_l.
  --destruct sz; simpl in Hsyz, Hs; [ | easy ].
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2]; [ | easy ].
    clear Hsyz.
    destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z))
      as [H3| H3]; [ easy | clear Hs ].
    destruct (PQeq_dec (MQpos x) 0) as [H4| H4].
   ++unfold "=="%PQ, nd in H4.
     simpl in H4.
     apply Nat.eq_mul_0_l in H4; [ | easy ].
     rewrite H4, Nat.add_0_l in H1.
     unfold "+", "*", nd in H1; simpl in H1.
     rewrite Hsx, Hsy, Hsz in H1; simpl in H1.
     destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z))
       as [H5| H5]; simpl in H1.
    **now apply PQnle_gt in H5.
    **unfold PQsub_num, nd in H1; simpl in H1.
      unfold PQmul_num in H1.
      now rewrite H4 in H1; simpl in H1.
   ++apply PQnle_gt in H2; apply H2.
     now apply PQmul_le_mono_pos_l in H3.
  *destruct sy; simpl in Hsyz.
  --destruct sz; simpl in Hsyz; [ easy | ].
    unfold "*", "+" in Hb1; simpl in Hb1.
    rewrite Hsx, Hsy, Hsz in Hb1; simpl in Hb1.
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2]; [ | easy ].
    clear Hsyz.
    destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z))
      as [H3| H3]; [ easy | clear Hb1 ].
    destruct (PQeq_dec (MQpos x) 0) as [H4| H4].
   ++unfold "=="%PQ, nd in H4.
     simpl in H4.
     apply Nat.eq_mul_0_l in H4; [ | easy ].
     rewrite H4, Nat.add_0_l in H1.
     unfold "+", "*", nd in H1; simpl in H1.
     rewrite Hsx, Hsy, Hsz in H1; simpl in H1.
     destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z))
       as [H5| H5]; simpl in H1.
    **now apply PQnle_gt in H5.
    **unfold PQsub_num, nd in H1; simpl in H1.
      unfold PQmul_num in H1.
      now rewrite H4 in H1; simpl in H1.
   ++apply PQnle_gt in H2; apply H2.
     now apply PQmul_le_mono_pos_l in H3.
  --remember (MQsign (x * y + x * z)) as b eqn:Hb.
    symmetry in Hb.
    destruct b; [ clear Hb1 | easy ].
    unfold "*", "+" in Hb; simpl in Hb.
    rewrite Hsx, Hsy, Hsz in Hb; simpl in Hb.
    destruct sz; simpl in Hb; [ simpl in Hsyz | easy ].
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2]; [ easy | ].
    clear Hsyz.
    destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z))
      as [H3| H3]; [ clear Hb | easy ].
    apply PQnle_gt in H3; apply H3; clear H3.
    now apply PQmul_le_mono_l.
 +idtac.
...
