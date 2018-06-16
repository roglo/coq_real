(* Implementation of rationals using only nat *)
(* Not convincing... e.g. addition associativity is complicated to prove,
   although it was simple in QArith. *)

Require Import Utf8 Arith.

Require Import Misc.

Delimit Scope PQ_scope with PQ.

Record PQ := PQmake { PQnum : nat; PQden1 : nat }.
Arguments PQnum x%PQ : rename.
Arguments PQden1 x%PQ : rename.

Definition nd x y := PQnum x * S (PQden1 y).

Definition PQadd_num x y := nd x y + nd y x.
Definition PQadd_den1 x y := S (PQden1 x) * S (PQden1 y) - 1.

Definition PQadd x y := PQmake (PQadd_num x y) (PQadd_den1 x y).

Arguments PQadd x%PQ y%PQ.

Definition PQeq x y := nd x y = nd y x.

Definition PQlt x y := nd x y < nd y x.
Definition PQle x y := nd x y ≤ nd y x.

Notation "0" := (PQmake 0 1) : PQ_scope.
Notation "x == y" := (PQeq x y) (at level 70) : PQ_scope.
Notation "x + y" := (PQadd x y) : PQ_scope.
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

Theorem fold_nd x y : PQnum x * S (PQden1 y) = nd x y.
Proof. easy. Qed.

Theorem PQadd_assoc : ∀ x y z, ((x + y) + z == x + (y + z))%PQ.
Proof.
intros.
unfold "==".
...

unfold nd; simpl.
unfold nd; simpl.
unfold PQadd_num; simpl.
do 4 rewrite fold_nd.
 do 6 rewrite Nat.mul_assoc.
 do 2 rewrite fold_nd.
 destruct (zerop
   ((nd x y + nd y x) * PQden z + nd z x * PQden y +
    (nd x y * PQden z + (nd y z + nd z y) * PQden x))) as [| H1]; [ easy | ].
 destruct (zerop ((nd x y + nd y x) * PQden z + nd z x * PQden y)) as [H2| H2].
 +rewrite H2 in H1; simpl in H1.
  apply Nat.eq_add_0 in H2.
  destruct H2 as (H2, H4).
  rewrite Nat.mul_add_distr_r in H2.
  apply Nat.eq_add_0 in H2.
  destruct H2 as (H2, H3).
  rewrite H2 in H1; simpl in H1.
  apply Nat.eq_mul_0 in H2.
  apply Nat.eq_mul_0 in H3.
  apply Nat.eq_mul_0 in H4.
  rewrite Nat.mul_add_distr_r in H1.
  unfold nd in H1.
  destruct H3 as [H3| H3].
  *rewrite Nat.mul_shuffle0, fold_nd, H3 in H1; simpl in H1.
   destruct H4 as [H4| H4].
  --now rewrite Nat.mul_shuffle0, fold_nd, H4 in H1.
  --now rewrite H4, Nat.mul_0_r in H1.
  *rewrite H3, Nat.mul_0_r in H1; simpl in H1.
   destruct H4 as [H4| H4].
  --now rewrite Nat.mul_shuffle0, fold_nd, H4 in H1.
  --now rewrite H4, Nat.mul_0_r in H1.
 +destruct (zerop (nd x y * PQden z + (nd y z + nd z y) * PQden x))
     as [H3| H3].
  *apply Nat.eq_add_0 in H3.
   destruct H3 as (H3, H4).
   rewrite Nat.mul_add_distr_r in H2.
   rewrite H3 in H2; simpl in H2.
   unfold nd in H4.
   rewrite Nat.mul_add_distr_r, Nat.mul_shuffle0, fold_nd in H4.
   rewrite Nat.mul_shuffle0, fold_nd in H4.
   now rewrite H4 in H2.
  *f_equal; f_equal; f_equal.
   do 2 rewrite Nat.mul_add_distr_r.
   rewrite <- Nat.add_assoc; f_equal; f_equal.
  --now rewrite <- fold_nd, Nat.mul_shuffle0, fold_nd.
  --now rewrite <- fold_nd, Nat.mul_shuffle0, fold_nd.
-unfold nd; simpl.
 do 4 rewrite fold_nd.
 do 6 rewrite Nat.mul_assoc.
 do 2 rewrite fold_nd.
 destruct (zerop
   (diff (nd z x * PQden y) ((nd x y + nd y x) * PQden z) +
    (if if nd z y <=? nd y z then true else false
     then nd x y * PQden z + diff (nd z y) (nd y z) * PQden x
     else diff (diff (nd z y) (nd y z) * PQden x) (nd x y * PQden z))))
   as [H1| H1]; [ easy | ].
 destruct (zerop (diff (nd z x * PQden y) ((nd x y + nd y x) * PQden z)))
   as [H2| H2].
 +apply eq_diff_0 in H2.
  rewrite <- H2 in H1.
  rewrite diff_id, Nat.add_0_l in H1.
  remember (nd z y <=? nd y z) as b eqn:Hb; symmetry in Hb.
  *destruct b.
  --apply Nat.leb_le in Hb.
    specialize (diff_max_r _ _ Hb) as H.
    rewrite H in H1; clear H.
    rewrite Nat.mul_sub_distr_r in H1.
    remember (nd z y * PQden x) as t eqn:Ht.
    rewrite <- fold_nd, Nat.mul_shuffle0, fold_nd in Ht; subst t.
    rewrite H2, Nat.mul_add_distr_r in H1.
    rewrite Nat.sub_add_distr in H1.
    rewrite Nat_sub_sub_swap in H1.
    remember (nd y z * PQden x) as t eqn:Ht.
    rewrite <- fold_nd, Nat.mul_shuffle0, fold_nd in Ht; subst t.
    rewrite Nat.sub_diag, Nat.sub_0_l, Nat.add_0_r in H1.
    rewrite Nat.mul_add_distr_r in H2.
    remember (nd z x * PQden y) as t eqn:Ht.
    rewrite <- fold_nd, Nat.mul_shuffle0, fold_nd in Ht; subst t.
    remember (nd y x * PQden z) as t eqn:Ht.
    rewrite <- fold_nd, Nat.mul_shuffle0, fold_nd in Ht; subst t.
    rewrite Nat.add_comm in H2.
    apply plus_minus in H2.
    rewrite <- Nat.mul_sub_distr_r in H2.
...
