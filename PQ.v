(* Implementation of positive (non zero) rationals using only nat *)

Require Import Utf8 Arith Morphisms Psatz.
Require Import Misc.

Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Delimit Scope PQ_scope with PQ.

(* A PQ number {PQnum1:=a; PQden1:=b} represents the rational (a+1)/(b+1) *)

Record PQ := PQmake { PQnum1 : nat; PQden1 : nat }.
Arguments PQmake _%nat _%nat.
Arguments PQnum1 x%PQ : rename.
Arguments PQden1 x%PQ : rename.

Notation "1" := (PQmake 0 0) : PQ_scope.

Definition nd x y := (PQnum1 x + 1) * (PQden1 y + 1).

(* equality *)

Definition PQeq x y := nd x y = nd y x.

Notation "x == y" := (PQeq x y) (at level 70) : PQ_scope.
Notation "x ≠≠ y" := (¬ PQeq x y) (at level 70) : PQ_scope.

Theorem PQeq_refl : ∀ x : PQ, (x == x)%PQ.
Proof. easy. Qed.

Theorem PQeq_symm : ∀ x y : PQ, (x == y)%PQ → (y == x)%PQ.
Proof. easy. Qed.

Theorem PQeq_trans : ∀ x y z : PQ, (x == y)%PQ → (y == z)%PQ → (x == z)%PQ.
Proof.
unfold "==".
intros * Hxy Hyz.
unfold nd in *.
apply (Nat.mul_cancel_l _ _ (PQnum1 y + 1)); [ flia | ].
rewrite Nat.mul_assoc, Nat.mul_shuffle0, Hyz.
rewrite Nat.mul_shuffle0, <- Nat.mul_assoc, Hxy.
rewrite Nat.mul_comm, Nat.mul_shuffle0.
symmetry; apply Nat.mul_assoc.
Qed.

Add Parametric Relation : _ PQeq
 reflexivity proved by PQeq_refl
 symmetry proved by PQeq_symm
 transitivity proved by PQeq_trans
 as PQeq_equiv_rel.

Theorem PQeq_dec : ∀ x y : PQ, {(x == y)%PQ} + {(x ≠≠ y)%PQ}.
Proof. intros; apply Nat.eq_dec. Qed.
Arguments PQeq_dec x%PQ y%PQ.

Definition if_PQeq (P Q : Prop) x y := if PQeq_dec x y then P else Q.
Arguments if_PQeq _ _ x%PQ y%PQ.

Notation "'if_PQeq_dec' x y 'then' P 'else' Q" :=
  (if_PQeq P Q x y) (at level 200, x at level 9, y at level 9).

Theorem PQeq_if : ∀ P Q x y,
  (if PQeq_dec x y then P else Q) = if_PQeq P Q x y.
Proof. easy. Qed.

(* allows to use rewrite inside a if_PQeq_dec ...
   through PQeq_if, e.g.
      H : (x = y)%PQ
      ====================
      ... if_PQeq_dec x z then P else Q ...
   > rewrite H.
      ====================
      ... if_PQeq_dec y z then P else Q ...
 *)
Instance PQif_PQeq_morph {P Q} :
  Proper (PQeq ==> PQeq ==> iff) (λ x y, if PQeq_dec x y then P else Q).
Proof.
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
destruct (PQeq_dec x1 y1) as [H1| H1]; rewrite Hx, Hy in H1.
-now destruct (PQeq_dec x2 y2).
-now destruct (PQeq_dec x2 y2).
Qed.

(* inequality *)

Definition PQlt x y := nd x y < nd y x.
Definition PQle x y := nd x y ≤ nd y x.
Definition PQgt x y := PQlt y x.
Definition PQge x y := PQle y x.

Notation "x < y" := (PQlt x y) : PQ_scope.
Notation "x ≤ y" := (PQle x y) : PQ_scope.
Notation "x > y" := (PQgt x y) : PQ_scope.
Notation "x ≥ y" := (PQge x y) : PQ_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%PQ (at level 70, y at next level) :
  PQ_scope.

Theorem PQle_refl : ∀ x, (x ≤ x)%PQ.
Proof. now unfold "≤"%PQ. Qed.

Theorem PQnlt_ge : ∀ x y, ¬ (x < y)%PQ ↔ (y ≤ x)%PQ.
Proof.
intros.
split; intros H; [ now apply Nat.nlt_ge in H | ].
now apply Nat.nlt_ge.
Qed.

Theorem PQnle_gt : ∀ x y, ¬ (x ≤ y)%PQ ↔ (y < x)%PQ.
Proof.
intros.
split; intros H; [ now apply Nat.nle_gt in H | ].
now apply Nat.nle_gt.
Qed.

Theorem PQlt_le_dec : ∀ x y : PQ, {(x < y)%PQ} + {(y ≤ x)%PQ}.
Proof.
intros (xn, xd) (yn, yd).
unfold PQlt, PQle, nd; simpl.
destruct (lt_dec ((xn + 1) * (yd + 1)) ((yn + 1) * (xd + 1))) as [H1| H1].
-now left.
-now right; apply Nat.nlt_ge.
Qed.
Arguments PQlt_le_dec x%PQ y%PQ.

Theorem PQle_lt_dec : ∀ x y : PQ, {(x ≤ y)%PQ} + {(y < x)%PQ}.
Proof.
intros (xn, xd) (yn, yd).
unfold PQlt, PQle, nd; simpl.
destruct (le_dec ((xn + 1) * (yd + 1)) ((yn + 1) * (xd + 1))) as [H1| H1].
-now left.
-now right; apply Nat.nle_gt.
Qed.
Arguments PQle_lt_dec x%PQ y%PQ.

Ltac split_var x :=
  let xn := fresh x in
  let xd := fresh x in
  let Hpn := fresh x in
  let Hpd := fresh x in
  remember (PQnum1 x + 1) as xn eqn:Hxn;
  remember (PQden1 x + 1) as xd eqn:Hxd;
  assert (Hpn : 0 < xn) by flia Hxn;
  assert (Hpd : 0 < xd) by flia Hxd;
  clear Hxn Hxd.

(* allows to use rewrite inside a less than
   e.g.
      H : x = y
      ====================
      (x < z)%PQ
   rewrite H.
 *)
Instance PQlt_morph : Proper (PQeq ==> PQeq ==> iff) PQlt.
Proof.
assert (H : ∀ x1 x2 y1 y2,
  (x1 == x2)%PQ → (y1 == y2)%PQ → (x1 < y1)%PQ → (x2 < y2)%PQ). {
  intros x1q x2q y1q y2q Hx Hy Hxy.
  unfold "<"%PQ, nd in Hxy |-*.
  unfold "=="%PQ, nd in Hx, Hy.
  split_var x1q; split_var x2q; split_var y1q; split_var y2q.
  move Hx before Hy.
  apply (Nat.mul_lt_mono_pos_l y1q0); [ easy | ].
  rewrite Nat.mul_assoc, Nat.mul_shuffle0, Hy; clear Hy.
  remember (y2q0 * y1q1 * x2q0) as u; rewrite Nat.mul_comm; subst u.
  do 2 rewrite <- Nat.mul_assoc.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  apply (Nat.mul_lt_mono_pos_r x1q1); [ easy | ].
  rewrite <- Nat.mul_assoc, <- Hx; clear Hx.
  rewrite Nat.mul_assoc, Nat.mul_comm.
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_lt_mono_pos_l; [ easy | ].
  now rewrite Nat.mul_comm.
}
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
split; intros Hxy.
-now apply (H x1 x2 y1 y2).
-symmetry in Hx, Hy.
 now apply (H x2 x1 y2 y1).
Qed.

(* allows to use rewrite inside a less equal
   e.g.
      H : x = y
      ====================
      (x ≤ z)%PQ
   rewrite H.
 *)
Instance PQle_morph : Proper (PQeq ==> PQeq ==> iff) PQle.
Proof.
assert (H : ∀ x1 x2 y1 y2,
  (x1 == x2)%PQ → (y1 == y2)%PQ → (x1 ≤ y1)%PQ → (x2 ≤ y2)%PQ). {
  intros x1q x2q y1q y2q Hx Hy Hxy.
  unfold "≤"%PQ, nd in Hxy |-*.
  unfold "=="%PQ, nd in Hx, Hy.
  split_var x1q; split_var x2q; split_var y1q; split_var y2q.
  move Hx before Hy.
  apply (Nat.mul_le_mono_pos_l _ _ y1q0); [ easy | ].
  rewrite Nat.mul_assoc, Nat.mul_shuffle0, Hy; clear Hy.
  remember (y2q0 * y1q1 * x2q0) as u; rewrite Nat.mul_comm; subst u.
  do 2 rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_pos_l; [ easy | ].
  apply (Nat.mul_le_mono_pos_r _ _ x1q1); [ easy | ].
  rewrite <- Nat.mul_assoc, <- Hx; clear Hx.
  rewrite Nat.mul_assoc, Nat.mul_comm.
  rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_pos_l; [ easy | ].
  now rewrite Nat.mul_comm.
}
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
split; intros Hxy.
-now apply (H x1 x2 y1 y2).
-symmetry in Hx, Hy.
 now apply (H x2 x1 y2 y1).
Qed.

Theorem PQle_antisymm : ∀ x y, (x ≤ y)%PQ → (y ≤ x)%PQ → (x == y)%PQ.
Proof.
intros * Hxy Hyx.
apply (Nat.le_antisymm _ _ Hxy Hyx).
Qed.

(* addition, subtraction *)

Definition PQadd_num1 x y := nd x y + nd y x - 1.
Definition PQsub_num1 x y := nd x y - nd y x - 1.
Definition PQadd_den1 x y := (PQden1 x + 1) * (PQden1 y + 1) - 1.

Definition PQadd x y := PQmake (PQadd_num1 x y) (PQadd_den1 x y).
Definition PQsub x y := PQmake (PQsub_num1 x y) (PQadd_den1 x y).
Arguments PQadd x%PQ y%PQ.
Arguments PQsub x%PQ y%PQ.

Notation "x + y" := (PQadd x y) : PQ_scope.
Notation "x - y" := (PQsub x y) : PQ_scope.

(* allows to use rewrite inside an addition
   e.g.
      H : x = y
      ====================
      ..... (x + z)%PQ ....
   rewrite H.
 *)
Instance PQadd_morph : Proper (PQeq ==> PQeq ==> PQeq) PQadd.
Proof.
intros x1q x2q Hx y1q y2q Hy.
move Hx before Hy.
unfold "+"%PQ.
unfold "==", nd in Hx, Hy |-*.
unfold PQadd_num1, PQadd_den1, nd; simpl.
rewrite Nat.sub_add; [ | do 4 rewrite Nat.add_1_r; simpl; flia ].
rewrite Nat.sub_add; [ | do 2 rewrite Nat.add_1_r; simpl; flia ].
rewrite Nat.sub_add; [ | do 2 rewrite Nat.add_1_r; simpl; flia ].
rewrite Nat.sub_add; [ | do 2 rewrite Nat.add_1_r; simpl; flia ].
split_var x1q; split_var x2q; split_var y1q; split_var y2q.
move Hx before Hy.
ring_simplify.
rewrite Nat.add_comm; f_equal.
-replace (y1q0 * x1q1 * x2q1 * y2q1) with (y1q0 * y2q1 * x1q1 * x2q1) by flia.
 rewrite Hy; flia.
-replace (x1q0 * y1q1 * x2q1) with (x1q0 * x2q1 * y1q1) by flia.
 rewrite Hx; flia.
Qed.

Theorem PQadd_comm : ∀ x y, (x + y == y + x)%PQ.
Proof.
intros.
unfold "==".
assert (PQnum_add_comm : ∀ x y, PQnum1 (x + y) = PQnum1 (y + x)). {
  intros.
  unfold "+"%PQ; simpl.
  unfold PQadd_num1, nd; f_equal.
  now rewrite Nat.add_comm.
}
assert (PQden1_add_comm : ∀ x y, PQden1 (x + y) = PQden1 (y + x)). {
  intros.
  unfold PQadd; simpl.
  unfold PQadd_den1.
  now rewrite Nat.mul_comm.
}
now unfold nd; rewrite PQnum_add_comm, PQden1_add_comm.
Qed.

Theorem PQadd_assoc : ∀ x y z, ((x + y) + z == x + (y + z))%PQ.
Proof.
intros.
rewrite PQadd_comm.
unfold "==", nd; simpl.
unfold PQadd_num1, PQadd_den1, nd; simpl.
unfold PQadd_num1, PQadd_den1, nd; simpl.
do 14 rewrite Nat.add_1_r; simpl.
do 8 rewrite Nat.sub_0_r.
ring.
Qed.

(* *)

Theorem PQlt_irrefl : ∀ x, (¬ x < x)%PQ.
Proof. intros x; apply Nat.lt_irrefl. Qed.

Theorem PQlt_le_incl : ∀ x y, (x < y)%PQ → (x ≤ y)%PQ.
Proof. intros * Hxy; now apply Nat.lt_le_incl. Qed.

Theorem PQle_trans : ∀ x y z, (x ≤ y)%PQ → (y ≤ z)%PQ → (x ≤ z)%PQ.
Proof.
intros * Hxy Hyz.
unfold "≤"%PQ, nd in Hxy, Hyz |-*.
apply (Nat.mul_le_mono_pos_r _ _ (PQden1 y + 1)); [ flia | ].
rewrite Nat.mul_shuffle0.
apply (Nat.le_trans _ ((PQnum1 y + 1) * (PQden1 x + 1) * (PQden1 z + 1))).
-apply Nat.mul_le_mono_pos_r; [ flia | easy ].
-setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_le_mono_pos_r; [ flia | easy ].
Qed.

Theorem PQlt_trans : ∀ x y z, (x < y)%PQ → (y < z)%PQ → (x < z)%PQ.
Proof.
intros * Hxy Hyz.
unfold "<"%PQ, nd in Hxy, Hyz |-*.
apply (Nat.mul_lt_mono_pos_r (PQden1 y + 1)); [ flia | ].
rewrite Nat.mul_shuffle0.
apply (Nat.lt_trans _ ((PQnum1 y + 1) * (PQden1 x + 1) * (PQden1 z + 1))).
-apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
-setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
Qed.
Arguments PQlt_trans x%PQ y%PQ z%PQ.

Theorem PQle_lt_trans : ∀ x y z, (x ≤ y)%PQ → (y < z)%PQ → (x < z)%PQ.
Proof.
intros * Hxy Hyz.
unfold "<"%PQ, nd in Hyz |-*.
unfold "≤"%PQ, nd in Hxy.
apply (Nat.mul_lt_mono_pos_r (PQden1 y + 1)); [ flia | ].
rewrite Nat.mul_shuffle0.
apply (Nat.le_lt_trans _ ((PQnum1 y + 1) * (PQden1 x + 1) * (PQden1 z + 1))).
-apply Nat.mul_le_mono_pos_r; [ flia | easy ].
-setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
Qed.

Theorem PQlt_le_trans : ∀ x y z, (x < y)%PQ → (y ≤ z)%PQ → (x < z)%PQ.
Proof.
intros * Hxy Hyz.
unfold "<"%PQ, nd in Hxy |-*.
unfold "≤"%PQ, nd in Hyz.
apply (Nat.mul_lt_mono_pos_r (PQden1 y + 1)); [ flia | ].
rewrite Nat.mul_shuffle0.
apply (Nat.lt_le_trans _ ((PQnum1 y + 1) * (PQden1 x + 1) * (PQden1 z + 1))).
-apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
-setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_le_mono_pos_r; [ flia | easy ].
Qed.

Theorem PQadd_lt_mono_r : ∀ x y z, (x < y)%PQ ↔ (x + z < y + z)%PQ.
Proof.
unfold "<"%PQ, "+"%PQ, PQadd_num1, PQadd_den1, nd; simpl.
intros *.
repeat rewrite Nat.add_1_r; simpl.
repeat (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
repeat rewrite Nat.sub_0_r.
split; intros H.
-apply -> Nat.succ_lt_mono.
...
 apply Nat.mul_lt_mono_pos_r; [ flia | ].
 do 2 rewrite Nat.mul_add_distr_r.
 remember (PQnum x * S (PQden1 z)) as u.
 rewrite Nat.mul_shuffle0; subst u.
 apply Nat.add_lt_mono_r.
 setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
-apply Nat.mul_lt_mono_pos_r in H; [ | flia ].
 do 2 rewrite Nat.mul_add_distr_r in H.
 remember (PQnum x * S (PQden1 z)) as u.
 rewrite Nat.mul_shuffle0 in H; subst u.
 apply Nat.add_lt_mono_r in H.
 setoid_rewrite Nat.mul_shuffle0 in H.
 apply Nat.mul_lt_mono_pos_r in H; [ easy | flia ].
Qed.

Theorem PQadd_le_mono_r : ∀ x y z, (x ≤ y ↔ x + z ≤ y + z)%PQ.
Proof.
unfold "≤"%PQ, "+"%PQ, PQadd_num, PQadd_den1, nd.
remember S as f; simpl; subst f.
intros *.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
do 2 rewrite Nat.mul_assoc.
split; intros H.
-apply Nat.mul_le_mono_pos_r; [ flia | ].
 do 2 rewrite Nat.mul_add_distr_r.
 remember (PQnum x * S (PQden1 z)) as u.
 rewrite Nat.mul_shuffle0; subst u.
 apply Nat.add_le_mono_r.
 setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_le_mono_pos_r; [ flia | easy ].
-apply Nat.mul_le_mono_pos_r in H; [ | flia ].
 do 2 rewrite Nat.mul_add_distr_r in H.
 remember (PQnum x * S (PQden1 z)) as u.
 rewrite Nat.mul_shuffle0 in H; subst u.
 apply Nat.add_le_mono_r in H.
 setoid_rewrite Nat.mul_shuffle0 in H.
 apply Nat.mul_le_mono_pos_r in H; [ easy | flia ].
Qed.

Theorem PQadd_le_mono : ∀ x y z t,
  (x ≤ y)%PQ → (z ≤ t)%PQ → (x + z ≤ y + t)%PQ.
Proof.
unfold "≤"%PQ, "+"%PQ, PQadd_num, PQadd_den1, nd.
remember S as f; simpl; subst f.
intros * Hxy Hzt.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
do 2 rewrite Nat.mul_add_distr_r.
apply Nat.add_le_mono.
-rewrite Nat.mul_shuffle0.
 do 2 rewrite Nat.mul_assoc.
 apply Nat.mul_le_mono_r.
 remember (PQnum x * S (PQden1 y)) as u.
 rewrite Nat.mul_shuffle0; subst u.
 now apply Nat.mul_le_mono_r.
-rewrite Nat.mul_assoc.
 rewrite Nat.mul_shuffle0.
 do 2 rewrite <- Nat.mul_assoc.
 rewrite Nat.mul_shuffle0.
 do 3 rewrite Nat.mul_assoc.
 apply Nat.mul_le_mono_r.
 setoid_rewrite Nat.mul_shuffle0.
 now apply Nat.mul_le_mono_r.
Qed.

Theorem PQsub_0_le : ∀ x y, (x - y == 0)%PQ ↔ (x ≤ y)%PQ.
Proof.
unfold "=="%PQ, "-"%PQ, "≤"%PQ, PQsub_num, PQadd_den1, nd; simpl.
intros.
split; intros Hxy.
-apply Nat.eq_mul_0_l in Hxy; [ | easy ].
 now apply Nat.sub_0_le.
-apply Nat.eq_mul_0; left.
 now apply Nat.sub_0_le.
Qed.

Theorem PQlt_add_lt_sub_r : ∀ x y z, (x + z < y)%PQ ↔ (x < y - z)%PQ.
Proof.
intros.
destruct (PQlt_le_dec z y) as [LE| GE].
-rewrite <- (PQsub_add z y) at 1 by now apply PQlt_le_incl.
 now rewrite <- PQadd_lt_mono_r.
-assert (GE' := GE).
 rewrite <- PQsub_0_le in GE'; rewrite GE'.
 split; intros Lt.
 +elim (PQlt_irrefl y).
  apply PQle_lt_trans with (x + z)%PQ; [ | easy ].
  rewrite <- (PQadd_0_l y).
  apply PQadd_le_mono; [ | easy ].
  apply PQle_0_l.
 +now elim (PQnlt_0_r x).
Qed.

Theorem PQsub_add_le : ∀ x y, (x ≤ x - y + y)%PQ.
Proof.
intros.
destruct (PQlt_le_dec x y) as [H1| H1].
-apply PQlt_le_incl in H1.
 apply PQsub_0_le in H1.
 rewrite H1, PQadd_0_l.
 now apply PQsub_0_le.
-rewrite PQsub_add; [ | easy ].
 unfold "≤"%PQ; easy.
Qed.

Theorem PQle_sub_le_add_r : ∀ x y z, (x - z ≤ y ↔ x ≤ y + z)%PQ.
Proof.
intros.
split; intros LE.
-rewrite (PQadd_le_mono_r _ _ z) in LE.
 apply PQle_trans with (x - z + z)%PQ; [ | easy ].
 apply PQsub_add_le.
-destruct (PQlt_le_dec x z) as [LE'|GE].
 +apply PQlt_le_incl in LE'.
  rewrite <- PQsub_0_le in LE'; rewrite LE'.
  apply PQle_0_l.
 +rewrite (PQadd_le_mono_r _ _ z).
  now rewrite PQsub_add.
Qed.

Theorem PQle_add_le_sub_r : ∀ x y z, (x + z ≤ y → x ≤ y - z)%PQ.
Proof.
intros * LE.
apply (PQadd_le_mono_r _ _ z).
rewrite PQsub_add; [ easy | ].
apply PQle_trans with (x + z)%PQ; [ | easy ].
rewrite <- (PQadd_0_l z) at 1.
rewrite <- PQadd_le_mono_r.
apply PQle_0_l.
Qed.

Theorem PQle_add_le_sub_l: ∀ x y z, (x + z ≤ y → z ≤ y - x)%PQ.
Proof.
intros *.
rewrite PQadd_comm.
apply PQle_add_le_sub_r.
Qed.

Theorem PQsub_sub_swap : ∀ x y z, (x - y - z == x - z - y)%PQ.
Proof.
intros.
unfold "=="%PQ, "-"%PQ, PQsub_num, PQadd_den1, nd.
remember S as f; simpl; subst f.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 4 rewrite Nat.sub_succ, Nat.sub_0_r.
f_equal; [ | apply Nat.mul_shuffle0 ].
do 2 rewrite Nat.mul_sub_distr_r.
do 2 rewrite Nat.mul_assoc.
rewrite Nat_sub_sub_swap.
f_equal; f_equal.
apply Nat.mul_shuffle0.
Qed.

Theorem PQadd_sub_swap: ∀ x y z, (z ≤ x)%PQ → (x + y - z == x - z + y)%PQ.
Proof.
intros * Hzx.
unfold "≤"%PQ, nd in Hzx.
unfold "=="%PQ, "-"%PQ, PQsub_num, PQadd_den1, nd.
remember S as f; simpl; subst f.
unfold PQadd_den1, PQadd_num, nd.
remember S as f; simpl; subst f.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 4 rewrite Nat.sub_succ, Nat.sub_0_r.
f_equal; [ | apply Nat.mul_shuffle0 ].
rewrite Nat.mul_sub_distr_r.
rewrite Nat.mul_add_distr_r.
do 2 rewrite Nat.mul_assoc.
rewrite Nat.add_sub_swap.
-f_equal; f_equal.
 apply Nat.mul_shuffle0.
-remember (PQnum z * S (PQden1 x)) as u.
 rewrite Nat.mul_shuffle0; subst u.
 now apply Nat.mul_le_mono_r.
Qed.

Theorem PQsub_diag : ∀ x, (x - x == 0)%PQ.
Proof.
intros.
unfold "=="%PQ, nd; simpl.
unfold PQsub_num.
now rewrite Nat.sub_diag.
Qed.

(* multiplication, inversion, division *)

Definition PQmul_num x y := PQnum x * PQnum y.
Definition PQmul_den1 x y := S (PQden1 x) * S (PQden1 y) - 1.

Definition PQmul x y := PQmake (PQmul_num x y) (PQmul_den1 x y).
Arguments PQmul x%PQ y%PQ.

Definition PQinv x := PQmake (PQden1 x + 1) (PQnum x - 1).

Notation "x * y" := (PQmul x y) : PQ_scope.
Notation "/ x" := (PQinv x) : PQ_scope.

(* allows to use rewrite inside a multiplication
   e.g.
      H : x = y
      ====================
      ..... (x * z)%PQ ....
   rewrite H.
 *)
Instance PQmul_morph : Proper (PQeq ==> PQeq ==> PQeq) PQmul.
Proof.
intros x1 x2 Hx y1 y2 Hy.
move Hx before Hy.
unfold "*"%PQ.
unfold "==", nd in Hx, Hy |-*; simpl.
unfold PQmul_num, PQmul_den1.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
setoid_rewrite Nat.mul_shuffle0.
do 2 rewrite Nat.mul_assoc.
rewrite Hx.
setoid_rewrite <- Nat.mul_assoc.
f_equal.
rewrite Nat.mul_comm, Hy.
apply Nat.mul_comm.
Qed.

Theorem PQmul_comm : ∀ x y, (x * y == y * x)%PQ.
Proof.
intros.
unfold "==", "*"%PQ, nd; f_equal; simpl.
-apply Nat.mul_comm.
-unfold PQmul_den1.
 f_equal; f_equal.
 apply Nat.mul_comm.
Qed.

Theorem PQmul_assoc : ∀ x y z, ((x * y) * z == x * (y * z))%PQ.
Proof.
intros.
unfold "==", "*"%PQ, nd; f_equal; simpl.
-unfold PQmul_num; simpl; symmetry.
 apply Nat.mul_assoc.
-unfold PQmul_den1.
 remember S as f; simpl; subst f.
 f_equal; f_equal.
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
 apply Nat.mul_assoc.
Qed.

Theorem PQmul_le_mono_l : ∀ x y z, (x ≤ y → z * x ≤ z * y)%PQ.
Proof.
unfold "≤"%PQ, nd; simpl.
intros * Hxy.
unfold PQmul_den1.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
do 2 rewrite Nat.mul_assoc.
setoid_rewrite Nat.mul_shuffle0.
apply Nat.mul_le_mono_r.
unfold PQmul_num.
do 2 rewrite <- Nat.mul_assoc.
now apply Nat.mul_le_mono_l.
Qed.

Theorem PQmul_le_mono_r : ∀ x y z, (x ≤ y → x * z ≤ y * z)%PQ.
Proof.
intros * Hxy.
setoid_rewrite PQmul_comm.
now apply PQmul_le_mono_l.
Qed.

Theorem PQmul_le_mono_pos_l : ∀ x y z, (z ≠≠ 0 → x ≤ y ↔ z * x ≤ z * y)%PQ.
Proof.
intros * Hz.
unfold "≤"%PQ, "*"%PQ, nd; simpl.
unfold PQmul_num, PQmul_den1.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
split; intros H.
-do 2 rewrite <- Nat.mul_assoc.
 apply Nat.mul_le_mono_l.
 do 2 rewrite Nat.mul_assoc.
 setoid_rewrite Nat.mul_shuffle0.
 now apply Nat.mul_le_mono_r.
-do 2 rewrite <- Nat.mul_assoc in H.
 apply <- Nat.mul_le_mono_pos_l in H.
 +do 2 rewrite Nat.mul_assoc in H.
  setoid_rewrite Nat.mul_shuffle0 in H.
  apply Nat.mul_le_mono_pos_r in H; [ easy | flia ].
 +apply Nat.neq_0_lt_0.
  intros H1; apply Hz.
  unfold "=="%PQ, nd.
  now rewrite H1.
Qed.

Theorem PQmul_lt_mono_pos_l : ∀ x y z, (x ≠≠ 0 → y < z ↔ x * y < x * z)%PQ.
intros * Hz.
unfold "<"%PQ, "*"%PQ, nd; simpl.
unfold PQmul_num, PQmul_den1.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
split; intros H.
-do 2 rewrite <- Nat.mul_assoc.
 apply Nat.mul_lt_mono_pos_l.
 +apply Nat.neq_0_lt_0.
  unfold "=="%PQ, nd in Hz; simpl in Hz; flia Hz.
 +do 2 rewrite Nat.mul_assoc.
  setoid_rewrite Nat.mul_shuffle0.
  apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
-do 2 rewrite <- Nat.mul_assoc in H.
 apply <- Nat.mul_lt_mono_pos_l in H.
 +do 2 rewrite Nat.mul_assoc in H.
  setoid_rewrite Nat.mul_shuffle0 in H.
  apply Nat.mul_lt_mono_pos_r in H; [ easy | flia ].
 +apply Nat.neq_0_lt_0.
  unfold "=="%PQ, nd in Hz; simpl in Hz; flia Hz.
Qed.

Theorem PQmul_add_distr_l : ∀ x y z, (x * (y + z) == x * y + x * z)%PQ.
Proof.
intros.
unfold "==", "*"%PQ, "+"%PQ, nd; simpl.
unfold PQmul_num, PQadd_den1, PQadd_num, PQmul_den1, nd.
remember S as f; simpl; subst f.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 5 rewrite Nat.sub_succ, Nat.sub_0_r.
ring.
Qed.

Theorem PQmul_sub_distr_l : ∀ x y z, (x * (y - z) == x * y - x * z)%PQ.
Proof.
intros.
destruct (PQlt_le_dec y z) as [H1| H1].
-apply PQlt_le_incl in H1.
 apply PQsub_0_le in H1; rewrite H1.
 unfold "*"%PQ at 1.
 unfold PQmul_num; simpl.
 rewrite Nat.mul_0_r.
 transitivity 0%PQ; [ easy | ].
 destruct (PQlt_le_dec (x * z) (x * y)) as [H2| H2].
 +apply PQnle_gt in H2; exfalso; apply H2; clear H2.
  apply PQmul_le_mono_l.
  now apply PQsub_0_le.
 +now apply PQsub_0_le in H2; rewrite H2.
-assert (Hy : (y == y - z + z)%PQ) by now symmetry; apply PQsub_add.
 pose (t := (y - z)%PQ).
 fold t in Hy |-*.
 rewrite Hy, PQmul_add_distr_l.
 rewrite <- PQadd_sub_assoc.
 +now rewrite PQsub_diag, PQadd_0_r.
 +apply PQmul_le_mono_r, PQle_refl.
Qed.

Theorem PQmul_0_l : ∀ x, (0 * x == 0)%PQ.
Proof.
intros.
rewrite PQmul_comm.
transitivity (x * (x - x))%PQ.
-now rewrite PQsub_diag.
-now rewrite PQmul_sub_distr_l, PQsub_diag.
Qed.

Theorem PQinv_involutive: ∀ x, (x ≠≠ 0 → / / x == x)%PQ.
Proof.
intros * Hnz.
unfold "/"%PQ; simpl.
rewrite Nat.add_sub.
rewrite Nat.sub_add; [ easy | ].
unfold "=="%PQ, nd in Hnz; simpl in Hnz.
rewrite Nat.mul_1_r in Hnz.
now apply Nat.neq_0_lt_0.
Qed.
