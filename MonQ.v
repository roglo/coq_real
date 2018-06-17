(* Implementation of positive rationals using only nat *)

Require Import Utf8 Arith Morphisms Psatz.

Require Import Misc.

Delimit Scope PQ_scope with PQ.

Record PQ := PQmake { PQnum : nat; PQden1 : nat }.
Arguments PQnum x%PQ : rename.
Arguments PQden1 x%PQ : rename.

Definition nd x y := PQnum x * S (PQden1 y).

Definition PQadd_num x y := nd x y + nd y x.
Definition PQsub_num x y := nd x y - nd y x.
Definition PQadd_den1 x y := S (PQden1 x) * S (PQden1 y) - 1.

Definition PQadd x y := PQmake (PQadd_num x y) (PQadd_den1 x y).
Definition PQsub x y := PQmake (PQsub_num x y) (PQadd_den1 x y).

Arguments PQadd x%PQ y%PQ.
Arguments PQsub x%PQ y%PQ.

Definition PQeq x y := nd x y = nd y x.
Definition PQlt x y := nd x y < nd y x.
Definition PQle x y := nd x y ≤ nd y x.

Notation "0" := (PQmake 0 1) : PQ_scope.
Notation "x == y" := (PQeq x y) (at level 70) : PQ_scope.
Notation "x + y" := (PQadd x y) : PQ_scope.
Notation "x - y" := (PQsub x y) : PQ_scope.
Notation "x < y" := (PQlt x y) : PQ_scope.
Notation "x ≤ y" := (PQle x y) : PQ_scope.
Notation "x > y" := (¬ PQle x y) : PQ_scope.
Notation "x ≥ y" := (¬ PQlt x y) : PQ_scope.

Theorem PQeq_refl : ∀ x : PQ, (x == x)%PQ.
Proof. easy. Qed.

Theorem PQeq_symm : ∀ x y : PQ, (x == y)%PQ → (y == x)%PQ.
Proof. easy. Qed.

Theorem PQeq_trans : ∀ x y z : PQ, (x == y)%PQ → (y == z)%PQ → (x == z)%PQ.
Proof.
unfold "==".
intros * Hxy Hyz.
unfold nd in *.
destruct (zerop (PQnum y)) as [Hy| Hy].
-rewrite Hy in Hxy, Hyz; simpl in Hxy, Hyz.
 symmetry in Hyz.
 apply Nat.eq_mul_0_l in Hxy; [ | easy ].
 apply Nat.eq_mul_0_l in Hyz; [ | easy ].
 now rewrite Hxy, Hyz.
-apply (Nat.mul_cancel_l _ _ (PQnum y)).
 +now intros H; rewrite H in Hy.
 +rewrite Nat.mul_assoc, Nat.mul_shuffle0, Hyz.
  rewrite Nat.mul_shuffle0, <- Nat.mul_assoc, Hxy.
  rewrite Nat.mul_comm, Nat.mul_shuffle0.
  symmetry; apply Nat.mul_assoc.
Qed.

Add Parametric Relation : _ PQeq
 reflexivity proved by PQeq_refl
 symmetry proved by PQeq_symm
 transitivity proved by PQeq_trans
 as PQeq_equiv_rel.

Theorem PQlt_le_dec : ∀ x y : PQ, {(x < y)%PQ} + {(y ≤ x)%PQ}.
Proof.
intros (xn, xd) (yn, yd).
unfold PQlt, PQle, nd; simpl.
destruct (lt_dec (xn * S yd) (yn * S xd)) as [H1| H1]; [ now left | ].
now right; apply Nat.nlt_ge.
Qed.
Arguments PQlt_le_dec x%PQ y%PQ.

Theorem PQnum_add_comm : ∀ x y, PQnum (x + y) = PQnum (y + x).
Proof.
intros.
apply Nat.add_comm.
Qed.

Theorem PQden1_add_comm : ∀ x y, PQden1 (x + y) = PQden1 (y + x).
Proof.
intros.
unfold PQadd; simpl.
unfold PQadd_den1.
now rewrite Nat.mul_comm.
Qed.

Theorem PQadd_comm : ∀ x y, (x + y == y + x)%PQ.
Proof.
intros.
unfold "==".
unfold nd; rewrite PQnum_add_comm.
now rewrite PQden1_add_comm.
Qed.

Theorem PQadd_assoc : ∀ x y z, ((x + y) + z == x + (y + z))%PQ.
Proof.
intros.
unfold "==".
unfold nd; simpl.
unfold PQadd_num, PQadd_den1.
unfold nd; simpl.
unfold PQadd_num, PQadd_den1.
unfold nd; simpl.
do 4 rewrite Nat.sub_0_r.
ring.
Qed.

Theorem PQsub_add_distr : ∀ x y z, (x - (y + z) == x - y - z)%PQ.
Proof.
intros.
unfold "==", nd; simpl.
f_equal.
Focus 2.
-f_equal.
 unfold PQadd_den1; simpl.
 unfold PQadd_den1; simpl.
 do 4 rewrite Nat.sub_0_r.
 ring.
-unfold PQsub_num, nd; simpl.
 unfold PQsub_num, PQadd_num, nd; simpl.
 unfold PQadd_den1; simpl.
 do 2 rewrite Nat.sub_0_r.
 destruct x as (xn, xd).
 destruct y as (yn, yd).
 destruct z as (zn, zd); simpl.
 do 2 rewrite <- Nat.add_succ_l.
 do 2 rewrite Nat.mul_add_distr_l.
 rewrite Nat.mul_add_distr_r.
 rewrite Nat.mul_sub_distr_r.
 lia.
Qed.

      (* --------- *)

Delimit Scope MQ_scope with MQ.

Record MQ := MQmake { MQsign : bool; MQpos : PQ }.
Arguments MQmake _ _%PQ.
Arguments MQsign x%MQ : rename.
Arguments MQpos x%MQ : rename.

Definition MQadd x y :=
  if Bool.eqb (MQsign x) (MQsign y) then
    MQmake (MQsign x) (MQpos x + MQpos y)
  else if PQlt_le_dec (MQpos x) (MQpos y) then
    MQmake (MQsign y) (MQpos y - MQpos x)
  else
    MQmake (MQsign x) (MQpos x - MQpos y).

Definition MQopp x := MQmake (negb (MQsign x)) (MQpos x).

Definition MQeq x y :=
  if Bool.eqb (MQsign x) (MQsign y) then (MQpos x == MQpos y)%PQ
  else if zerop (PQnum (MQpos x) + PQnum (MQpos y)) then True
  else False.

Notation "0" := (MQmake true 0) : MQ_scope.
Notation "- x" := (MQopp x) : MQ_scope.
Notation "x == y" := (MQeq x y) (at level 70) : MQ_scope.
Notation "x + y" := (MQadd x y) : MQ_scope.
Notation "x - y" := (MQadd x (MQopp y)) : MQ_scope.
(*
Notation "x < y" := (MQlt x y) : MQ_scope.
Notation "x ≤ y" := (MQle x y) : MQ_scope.
Notation "x > y" := (¬ MQle x y) : MQ_scope.
Notation "x ≥ y" := (¬ MQlt x y) : MQ_scope.
*)

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

Open Scope MQ_scope.

Theorem MQadd_assoc : ∀ x y z, ((x + y) + z == x + (y + z))%MQ.
Proof.
intros.
unfold "=="%MQ.
remember (Bool.eqb (MQsign (x + y + z)) (MQsign (x + (y + z)))) as b1 eqn:Hb1.
symmetry in Hb1.
destruct b1.
-apply -> Bool.eqb_true_iff in Hb1.
 unfold "+"%MQ.
 remember (Bool.eqb (MQsign x) (MQsign y)) as b2 eqn:Hb2.
 remember (Bool.eqb (MQsign y) (MQsign z)) as b3 eqn:Hb3.
 remember (Bool.eqb (MQsign x) (MQsign z)) as b4 eqn:Hb4.
 symmetry in Hb2, Hb3, Hb4.
 move b3 before b2; move b4 before b3.
 destruct b2; simpl.
 +apply -> Bool.eqb_true_iff in Hb2.
  rewrite Hb2, Hb3.
  destruct b3.
  *rewrite Bool.eqb_reflx; simpl; apply PQadd_assoc.
  *destruct (PQlt_le_dec (MQpos x + MQpos y) (MQpos z)) as [H1| H1].
  --simpl.
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2].
   ++simpl; rewrite Hb3.
     destruct (PQlt_le_dec (MQpos x) (MQpos z - MQpos y)) as [H3| H3].
    **rewrite PQsub_add_distr.
...
