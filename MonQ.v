(* Implementation of positive rationals using only nat *)

Require Import Utf8 Arith.

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
  else if ...
  else False.

Notation "0" := (MQmake true 0) : MQ_scope.
Notation "- x" := (MQopp x) : MQ_scope.
(*
Notation "x == y" := (MQeq x y) (at level 70) : MQ_scope.
*)
Notation "x + y" := (MQadd x y) : MQ_scope.
Notation "x - y" := (MQadd x (MQopp y)) : MQ_scope.
(*
Notation "x < y" := (MQlt x y) : MQ_scope.
Notation "x ≤ y" := (MQle x y) : MQ_scope.
Notation "x > y" := (¬ MQle x y) : MQ_scope.
Notation "x ≥ y" := (¬ MQlt x y) : MQ_scope.
*)
