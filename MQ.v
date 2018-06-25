(* Implementation of rationals using only nat *)

Require Import Utf8 Arith Morphisms.
Require Import PQ.

Delimit Scope MQ_scope with MQ.

Record MQ := MQmake { MQsign : bool; MQpos : PQ }.
Arguments MQmake _ _%PQ.
Arguments MQsign x%MQ : rename.
Arguments MQpos x%MQ : rename.

Notation "0" := (MQmake true 0) : MQ_scope.
Notation "1" := (MQmake true 1) : MQ_scope.

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

(* allows to use rewrite inside a Qmake
   e.g.
      Hs : sx = sy
      H : x = y
      ====================
      ... (Qmake sx x) ...
   rewrite Hs, H.
 *)
Instance MQmake_morph : Proper (eq ==> PQeq ==> MQeq) MQmake.
Proof.
intros sx sy Hs x y Hxy.
unfold "=="%MQ; simpl.
rewrite Hs.
now rewrite Bool.eqb_reflx.
Qed.

Definition MQlt x y :=
  if MQsign x then
    if MQsign y then PQlt (MQpos x) (MQpos y)
    else False
  else
    if negb (MQsign y) then PQlt (MQpos y) (MQpos x)
    else if PQeq_dec (MQpos x + MQpos y) 0 then False
    else True.
Arguments MQlt x%MQ y%MQ.

Definition MQle x y :=
  if MQsign x then
    if MQsign y then PQle (MQpos x) (MQpos y)
    else if PQeq_dec (MQpos x + MQpos y) 0 then True
    else False
  else
    if negb (MQsign y) then PQle (MQpos y) (MQpos x)
    else True.
Arguments MQle x%MQ y%MQ.

Notation "x < y" := (MQlt x y) : MQ_scope.
Notation "x ≤ y" := (MQle x y) : MQ_scope.
Notation "x > y" := (¬ MQle x y) : MQ_scope.
Notation "x ≥ y" := (¬ MQlt x y) : MQ_scope.

Ltac MQlt_morph_tac :=
  match goal with
  | H : False |- _ => easy
  | |- ?H ↔ False =>
      let H1 := fresh "Hxy" in
      split; [ intros H1 | easy ];
      MQlt_morph_tac
  | |- False ↔ ?H =>
      let H1 := fresh "Hxy" in
      split; [ easy | intros H1 ];
      MQlt_morph_tac
  | H : True |- _ =>
      clear H;
      MQlt_morph_tac
  | [ H :
      if zerop (PQnum (MQpos ?x1) + PQnum (MQpos ?x2)) then True else False
      |- _ ] =>
      let H1 := fresh "H1n" in
      let H2 := fresh "H2n" in
      let H3 := fresh "H1p" in
      let H4 := fresh "H2p" in
      destruct (zerop (PQnum (MQpos x1) + PQnum (MQpos x2))) as [H1| ];
        [ clear H | easy ];
      apply Nat.eq_add_0 in H1;
      destruct H1 as (H1, H2);
      generalize H1; intros H3;
      apply PQeq_num_0 in H3;
      generalize H2; intros H4;
      apply PQeq_num_0 in H4;
      MQlt_morph_tac
  | [ H :
      if PQeq_dec (MQpos ?x + MQpos ?y) 0 then False else True
      |- _ ] =>
      let H1 := fresh "H1" in
      destruct (PQeq_dec (MQpos x + MQpos y) 0) as [H1| H1];
        [ apply PQeq_add_0 in H1;
          let H2 := fresh "H2" in
          destruct H1 as (H1, H2)
        | ];
       MQlt_morph_tac
  | _ => idtac
  end.

Instance MQlt_morph : Proper (MQeq ==> MQeq ==> iff) MQlt.
Proof.
unfold "<"%MQ, "=="%MQ.
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
remember (MQsign x1) as sx1 eqn:Hsx1.
remember (MQsign x2) as sx2 eqn:Hsx2.
remember (MQsign y1) as sy1 eqn:Hsy1.
remember (MQsign y2) as sy2 eqn:Hsy2.
move sx2 before sx1; move sy1 before sx2; move sy2 before sy1.
move Hsy1 before Hsx2; move Hsy2 before Hsy1.
symmetry in Hsx1, Hsx2, Hsy1, Hsy2.
destruct sx1, sx2, sy1, sy2; simpl in Hx, Hy |-*; MQlt_morph_tac.
-now rewrite Hx, Hy.
-unfold "<"%PQ, nd in Hxy.
 rewrite H1n in Hxy; simpl in Hxy.
 now apply Nat.nlt_0_r in Hxy.
-unfold "<"%PQ, nd in Hxy.
 rewrite H2n in Hxy; simpl in Hxy.
 now apply Nat.nlt_0_r in Hxy.
-rewrite Hy, H1p.
 destruct (PQeq_dec (MQpos x2 + MQpos y2) 0) as [H5| H5].
 +split; [ intros H | easy ].
  apply PQeq_add_0 in H5.
  rewrite (proj2 H5) in H.
  now apply PQnlt_0_r in H.
 +split; [ easy | intros _ ].
  rewrite H2p, PQadd_0_l in H5.
  now apply PQneq_0_lt_0.
-now rewrite H1p, H2p0.
-rewrite H2p, H2p0, PQadd_0_r in H1.
 now apply H1.
-rewrite H2p in Hxy.
 now apply PQnlt_0_r in Hxy.
-rewrite PQif_eq_if_eqb, H1p, Hy, PQadd_0_l, <- PQif_eq_if_eqb.
 destruct (PQeq_dec (MQpos y2) 0) as [H1| H1].
 +now rewrite H2p, H1.
 +split; [ intros _ | easy ].
  now rewrite H2p; apply PQneq_0_lt_0.
-rewrite H1p0, H1p in H1; apply H1.
 apply PQadd_0_l.
-now rewrite H1p0, H2p.
-now rewrite H1p in Hxy.
-do 2 rewrite PQif_eq_if_eqb.
 now rewrite Hx, Hy.
-rewrite PQif_eq_if_eqb, H1p, PQadd_0_r, <- PQif_eq_if_eqb.
 destruct (PQeq_dec (MQpos x1) 0) as [H1| H1].
 +now rewrite <- Hx, H1.
 +split; [ intros _ | easy ].
  now rewrite <- Hx, H2p; apply PQneq_0_lt_0.
-rewrite PQif_eq_if_eqb, H2p, PQadd_0_r, <- PQif_eq_if_eqb.
 destruct (PQeq_dec (MQpos x2) 0) as [H1| H1].
 +now rewrite Hx, H1.
 +split; [ easy | intros _ ].
  now rewrite H1p, Hx; apply PQneq_0_lt_0.
-now rewrite Hx, Hy.
Qed.

(* addition, opposite, subtraction *)

Definition MQadd x y :=
  if Bool.eqb (MQsign x) (MQsign y) then
    MQmake (MQsign x) (MQpos x + MQpos y)
  else if PQlt_le_dec (MQpos x) (MQpos y) then
    MQmake (MQsign y) (MQpos y - MQpos x)
  else
    MQmake (MQsign x) (MQpos x - MQpos y).

Definition MQopp x := MQmake (negb (MQsign x)) (MQpos x).
Definition MQabs x := MQmake true (MQpos x).

Notation "- x" := (MQopp x) : MQ_scope.
Notation "x + y" := (MQadd x y) : MQ_scope.
Notation "x - y" := (MQadd x (MQopp y)) : MQ_scope.

Open Scope MQ_scope.

Instance MQabs_morph : Proper (MQeq ==> MQeq) MQabs.
Proof.
intros x y Hxy.
unfold MQabs, "=="%MQ; simpl.
unfold "==" in Hxy.
remember (MQsign x) as sx eqn:Hsx.
remember (MQsign y) as sy eqn:Hsy.
destruct sx, sy; simpl in Hxy; [ easy | | | easy ].
-destruct (zerop (PQnum (MQpos x) + PQnum (MQpos y))) as [H1| ]; [ | easy ].
 apply Nat.eq_add_0 in H1.
 destruct H1 as (H1, H2).
 apply PQeq_num_0 in H1.
 apply PQeq_num_0 in H2.
 now rewrite H1, H2.
-destruct (zerop (PQnum (MQpos x) + PQnum (MQpos y))) as [H1| ]; [ | easy ].
 apply Nat.eq_add_0 in H1.
 destruct H1 as (H1, H2).
 apply PQeq_num_0 in H1.
 apply PQeq_num_0 in H2.
 now rewrite H1, H2.
Qed.

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

Theorem MQadd_opp_r : ∀ x, (x - x == 0)%MQ.
Proof.
intros.
unfold "-", "+", "=="; simpl.
rewrite Bool.eqb_negb2.
destruct (PQlt_le_dec (MQpos x) (MQpos x)) as [H1| H1]; simpl.
-now apply PQlt_irrefl in H1.
-destruct (Bool.eqb (MQsign x) true); [ apply PQsub_diag | ].
 rewrite Nat.add_0_r.
 destruct (zerop (PQsub_num (MQpos x) (MQpos x))) as [H2| H2]; [ easy | ].
 unfold PQsub_num in H2.
 now rewrite Nat.sub_diag in H2.
Qed.

Theorem MQadd_opp_l : ∀ x, (- x + x == 0)%MQ.
Proof. intros; rewrite MQadd_comm; apply MQadd_opp_r. Qed.

(* multiplication, inverse, division *)

Definition MQmul x y :=
  MQmake (Bool.eqb (MQsign x) (MQsign y)) (MQpos x * MQpos y).

Definition MQinv x :=
  MQmake (MQsign x) (PQinv (MQpos x)).

Notation "x * y" := (MQmul x y) : MQ_scope.
Notation "/ x" := (MQinv x) : MQ_scope.
Notation "x / y" := (MQmul x (MQinv y)) : MQ_scope.

Ltac MQmul_morph_tac :=
  match goal with
  | [ H : if (zerop (PQnum (MQpos ?x) + PQnum (MQpos ?y))) then ?P else ?Q
       |- _ ] =>
      destruct (zerop (PQnum (MQpos x) + PQnum (MQpos y)))
        as [H1| H1]; [ | easy ];
      apply Nat.eq_add_0 in H1;
      unfold "=="%PQ, "*"%PQ, nd; simpl; unfold PQmul_num;
      now rewrite (proj1 H1), (proj2 H1)
  | [ H : if (zerop (PQnum (MQpos ?x) + PQnum (MQpos ?y))) then ?P else ?Q
       |- _ ] =>
      destruct (zerop (PQnum (MQpos x) + PQnum (MQpos y)))
        as [H1| H1]; [ | easy ];
      apply Nat.eq_add_0 in H1;
      unfold PQmul_num;
      now rewrite (proj1 H1), (proj2 H1), Nat.mul_0_r, Nat.mul_0_r
  | [ Hx : (MQpos ?x1 == MQpos ?x2)%PQ, Hy : (MQpos ?y1 == MQpos ?y2)%PQ
       |- _ ] =>
      now rewrite Hx, Hy
  | _ => idtac
  end.

(* allows to use rewrite inside a multiplication
   e.g.
      H : x = y
      ====================
      ... (x * z) ...
   rewrite H.
 *)
Instance MQmul_morph : Proper (MQeq ==> MQeq ==> MQeq) MQmul.
Proof.
unfold "=="%MQ; simpl.
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
unfold "*"%MQ; simpl.
remember (MQsign x1) as sx1 eqn:Hsx1; symmetry in Hsx1.
remember (MQsign x2) as sx2 eqn:Hsx2; symmetry in Hsx2.
remember (MQsign y1) as sy1 eqn:Hsy1; symmetry in Hsy1.
remember (MQsign y2) as sy2 eqn:Hsy2; symmetry in Hsy2.
move sx2 before sx1; move sy1 before sx2; move sy2 before sy1.
move Hsy1 before Hsx2; move Hsy2 before Hsy1.
destruct sx1, sx2, sy1, sy2; simpl in Hx, Hy |-*; MQmul_morph_tac.
Qed.

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
(* the 2nd case is almost the first one by swapping y and z *)
intros.
unfold "=="; simpl.
unfold "+", "*"; simpl.
remember (MQsign x) as sx eqn:Hsx; symmetry in Hsx.
remember (MQsign y) as sy eqn:Hsy; symmetry in Hsy.
remember (MQsign z) as sz eqn:Hsz; symmetry in Hsz.
destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2]; simpl.
-destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z)) as [H3| H3].
 +destruct sx, sy, sz; simpl;
    try apply PQmul_add_distr_l; apply PQmul_sub_distr_l.
 +destruct (PQeq_dec (MQpos x) 0) as [H4| H4].
  *unfold "=="%PQ, nd in H4; simpl in H4.
   unfold PQmul_num, PQsub_num, nd; simpl.
   unfold PQmul_num.
   apply Nat.eq_mul_0_l in H4; [ | easy ].
   unfold "*"%PQ, "+"%PQ; simpl.
   unfold PQmul_num; simpl.
   rewrite H4.
   destruct sx, sy, sz; simpl; try easy; try apply PQmul_add_distr_l.
  *apply PQmul_le_mono_pos_l in H3; [ | easy ].
   now apply PQnlt_ge in H2.
-destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z)) as [H3| H3].
 +destruct (PQeq_dec (MQpos x) 0) as [H4| H4].
  *unfold "=="%PQ, nd in H4; simpl in H4.
   unfold PQmul_num, PQsub_num, nd; simpl.
   unfold PQmul_num.
   apply Nat.eq_mul_0_l in H4; [ | easy ].
   unfold "*"%PQ, "+"%PQ; simpl.
   unfold PQmul_num; simpl.
   rewrite H4.
   destruct sx, sy, sz; simpl; try easy; try apply PQmul_add_distr_l.
  *apply PQnle_gt in H3; exfalso; apply H3.
   now apply PQmul_le_mono_pos_l.
 +destruct sx, sy, sz; simpl;
    try apply PQmul_add_distr_l; apply PQmul_sub_distr_l.
Qed.
