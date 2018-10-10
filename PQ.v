(* Implementation of positive (non zero) rationals using only nat *)

Require Import Utf8 Arith Morphisms Psatz.
Require Import Misc.
Set Nested Proofs Allowed.

Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Delimit Scope PQ_scope with PQ.

(* A PQ number {PQnum1:=a; PQden1:=b} represents the rational (a+1)/(b+1) *)

Record PQ := PQmake { PQnum1 : nat; PQden1 : nat }.
Arguments PQmake _%nat _%nat.
Arguments PQnum1 x%PQ : rename.
Arguments PQden1 x%PQ : rename.

Notation "1" := (PQmake 0 0) : PQ_scope.
Notation "2" := (PQmake 1 0) : PQ_scope.

Definition nd x y := (PQnum1 x + 1) * (PQden1 y + 1).
Definition PQone x := PQmake (PQden1 x) (PQden1 x).
Definition PQ_of_nat n := PQmake (n - 1) 0.
Definition PQ_of_pair n d := PQmake (n - 1) (d - 1).

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

Definition if_PQeq {A} (P Q : A) x y := if PQeq_dec x y then P else Q.
Arguments if_PQeq _ _ _ x%PQ y%PQ.

Notation "'if_PQeq_dec' x y 'then' P 'else' Q" :=
  (if_PQeq P Q x y) (at level 200, x at level 9, y at level 9).

Theorem PQeq_if : ∀ A {P Q : A} x y,
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
Instance PQif_PQeq_morph {P Q : Prop} :
  Proper (PQeq ==> PQeq ==> iff) (λ x y, if PQeq_dec x y then P else Q).
Proof.
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
destruct (PQeq_dec x1 y1) as [H1| H1]; rewrite Hx, Hy in H1.
-now destruct (PQeq_dec x2 y2).
-now destruct (PQeq_dec x2 y2).
Qed.

(* inequality *)

Definition PQcompare x y := Nat.compare (nd x y) (nd y x).
Arguments PQcompare x%PQ y%PQ.

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

Theorem PQcompare_eq_iff : ∀ x y, PQcompare x y = Eq ↔ (x == y)%PQ.
Proof. intros; apply Nat.compare_eq_iff. Qed.

Theorem PQcompare_lt_iff : ∀ x y, PQcompare x y = Lt ↔ (x < y)%PQ.
Proof. intros; apply Nat.compare_lt_iff. Qed.

Theorem PQcompare_gt_iff : ∀ x y, PQcompare x y = Gt ↔ (x > y)%PQ.
Proof. intros; apply Nat.compare_gt_iff. Qed.

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

Instance PQgt_morph : Proper (PQeq ==> PQeq ==> iff) PQgt.
Proof.
intros x1 x2 Hx y1 y2 Hy.
now apply PQlt_morph.
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

Instance PQge_morph : Proper (PQeq ==> PQeq ==> iff) PQge.
Proof.
intros x1 x2 Hx y1 y2 Hy.
now apply PQle_morph.
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

(* multiplication, inversion, division *)

Definition PQmul_num1 x y := (PQnum1 x + 1) * (PQnum1 y + 1) - 1.
Definition PQmul_den1 x y := (PQden1 x + 1) * (PQden1 y + 1) - 1.

Definition PQmul x y := PQmake (PQmul_num1 x y) (PQmul_den1 x y).
Arguments PQmul x%PQ y%PQ.

Definition PQinv x := PQmake (PQden1 x) (PQnum1 x).

Notation "x * y" := (PQmul x y) : PQ_scope.
Notation "/ x" := (PQinv x) : PQ_scope.

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

Theorem PQsub_morph : ∀ x1 x2 y1 y2,
  (x1 < y1)%PQ
  → (x1 == x2)%PQ
  → (y1 == y2)%PQ
  → (y1 - x1 == y2 - x2)%PQ.
Proof.
intros * H1 Hx Hy.
generalize H1; intros H2; move H2 before H1.
rewrite Hx, Hy in H2.
unfold "-"%PQ.
unfold "==", nd in Hx, Hy |-*.
unfold "<"%PQ, nd in H1, H2.
unfold PQsub_num1, PQadd_den1, nd; simpl.
do 4 rewrite Nat.add_1_r in H1, H2, Hx, Hy.
do 12 rewrite Nat.add_1_r.
do 2 (rewrite <- Nat.sub_succ_l; [ | flia H1 ]).
rewrite Nat_sub_sub_swap, Nat.sub_succ, Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite Nat.sub_succ, Nat.sub_0_r.
do 2 (rewrite <- Nat.sub_succ_l; [ | flia H2 ]).
rewrite Nat_sub_sub_swap, Nat.sub_succ, Nat.sub_0_r.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite Nat.sub_succ, Nat.sub_0_r.
do 2 rewrite Nat.mul_sub_distr_r.
remember (S (PQnum1 x1)) as x1n eqn:Hx1n.
remember (S (PQden1 x1)) as x1d eqn:Hx1d.
remember (S (PQnum1 x2)) as x2n eqn:Hx2n.
remember (S (PQden1 x2)) as x2d eqn:Hx2d.
remember (S (PQnum1 y1)) as y1n eqn:Hy1n.
remember (S (PQden1 y1)) as y1d eqn:Hy1d.
remember (S (PQnum1 y2)) as y2n eqn:Hy2n.
remember (S (PQden1 y2)) as y2d eqn:Hy2d.
move H1 before H2.
f_equal.
-replace (y1n * x1d * (y2d * x2d)) with (y1n * y2d * x1d * x2d) by flia.
 rewrite Hy; flia.
-replace (x1n * y1d * (y2d * x2d)) with (x1n * x2d * y1d * y2d) by flia.
 rewrite Hx; flia.
Qed.
Arguments PQsub_morph x1%PQ x2%PQ y1%PQ y2%PQ.

(* allows to use rewrite inside a multiplication
   e.g.
      H : x = y
      ====================
      ..... (x * z)%PQ ....
   rewrite H.
 *)
Instance PQmul_morph : Proper (PQeq ==> PQeq ==> PQeq) PQmul.
Proof.
unfold "*"%PQ.
unfold "==", nd; simpl.
unfold PQmul_num1, PQmul_den1; simpl.
intros x1 x2 Hx y1 y2 Hy; simpl.
move Hx before Hy.
do 4 rewrite Nat.add_1_r in Hx, Hy.
do 12 rewrite Nat.add_1_r.
do 4 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 4 rewrite Nat.sub_succ, Nat.sub_0_r.
setoid_rewrite Nat.mul_shuffle0.
do 2 rewrite Nat.mul_assoc; rewrite Hx.
setoid_rewrite <- Nat.mul_assoc; f_equal.
rewrite Nat.mul_comm, Hy.
apply Nat.mul_comm.
Qed.

Ltac split_var2 x xn xd Hpn Hpd :=
  remember (S (PQnum1 x)) as xn eqn:Heqxn;
  remember (S (PQden1 x)) as xd eqn:Heqxd;
  move xn at top; move xd at top;
  assert (Hpn : 0 < xn) by flia Heqxn;
  assert (Hpd : 0 < xd) by flia Heqxd;
  clear Heqxn Heqxd.

Ltac PQtac1 :=
  unfold "+"%PQ, "-"%PQ, "<"%PQ, "=="%PQ, "≤"%PQ;
  unfold PQadd_num1, PQsub_num1, PQadd_den1, nd; simpl;
  repeat rewrite Nat.add_1_r.

Ltac PQtac2 :=
  rewrite <- Nat.sub_succ_l;
  try (rewrite Nat.sub_succ, Nat.sub_0_r);
  match goal with
  | [ |- 1 ≤ S _ * _ ] => try (simpl; flia)
  | [ |- 1 ≤ S _ * _ * _ ] => try (simpl; flia)
  | _ => idtac
  end.

Ltac PQtac3 :=
  repeat rewrite Nat.mul_sub_distr_l;
  repeat rewrite Nat.mul_add_distr_l;
  repeat rewrite Nat.mul_sub_distr_r;
  repeat rewrite Nat.mul_add_distr_r;
  repeat rewrite Nat.mul_assoc.

Theorem PQmul_one_r : ∀ x y, (x * PQone y == x)%PQ.
Proof.
intros.
unfold "*"%PQ, "==", PQone, nd; simpl.
unfold PQmul_num1, PQmul_den1; simpl.
PQtac1; repeat PQtac2; PQtac3.
apply Nat.mul_shuffle0.
Qed.

Theorem PQle_antisymm_eq : ∀ x y,
  (x ≤ y)%PQ → (y ≤ x)%PQ → (x * PQone y = y * PQone x)%PQ.
Proof.
intros x y Hxy Hyx.
unfold PQone, "*"%PQ; simpl.
unfold PQmul_num1, PQmul_den1; simpl.
specialize (Nat.le_antisymm _ _ Hxy Hyx) as H.
unfold nd in H; rewrite H.
f_equal.
now rewrite Nat.mul_comm.
Qed.

Theorem PQle_antisymm : ∀ x y, (x ≤ y)%PQ → (y ≤ x)%PQ → (x == y)%PQ.
Proof.
intros * Hxy Hyx.
apply (Nat.le_antisymm _ _ Hxy Hyx).
Qed.

Theorem PQadd_comm : ∀ x y, (x + y)%PQ = (y + x)%PQ.
Proof.
intros.
unfold "+"%PQ; f_equal.
-now unfold PQadd_num1, nd; rewrite Nat.add_comm.
-now unfold PQadd_den1, nd; rewrite Nat.mul_comm.
Qed.

Theorem PQadd_add_swap : ∀ x y z, (x + y + z)%PQ = (x + z + y)%PQ.
Proof.
intros; PQtac1.
repeat PQtac2; [ | simpl; flia | simpl; flia ].
PQtac3; f_equal; [ | f_equal; apply Nat.mul_shuffle0 ].
f_equal.
rewrite Nat.add_shuffle0.
f_equal; f_equal.
apply Nat.mul_shuffle0.
Qed.

Theorem PQadd_assoc : ∀ x y z, (x + (y + z))%PQ = ((x + y) + z)%PQ.
Proof.
intros.
rewrite PQadd_comm.
remember (x + y)%PQ as t eqn:Ht.
rewrite PQadd_comm in Ht; subst t.
apply PQadd_add_swap.
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
Arguments PQle_trans x%PQ y%PQ z%PQ.

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

Instance PQcompare_morph : Proper (PQeq ==> PQeq ==> eq) PQcompare.
Proof.
intros x1 x2 Hx y1 y2 Hy.
move Hx before Hy.
remember (PQcompare x1 y1) as c1 eqn:Hc1; symmetry in Hc1.
remember (PQcompare x2 y2) as c2 eqn:Hc2; symmetry in Hc2.
move c2 before c1.
destruct c1.
-apply PQcompare_eq_iff in Hc1.
 destruct c2; [ easy | | ].
 +apply PQcompare_lt_iff in Hc2.
  rewrite <- Hy, <- Hc1, Hx in Hc2.
  now apply PQlt_irrefl in Hc2.
 +apply PQcompare_gt_iff in Hc2.
  rewrite <- Hy, <- Hc1, Hx in Hc2.
  now apply PQlt_irrefl in Hc2.
-apply PQcompare_lt_iff in Hc1.
 destruct c2; [ | easy | ].
 +apply PQcompare_eq_iff in Hc2.
  rewrite Hx, Hc2, Hy in Hc1.
  now apply PQlt_irrefl in Hc1.
 +apply PQcompare_gt_iff in Hc2.
  rewrite Hx, Hy in Hc1.
  apply PQnle_gt in Hc2.
  now exfalso; apply Hc2, PQlt_le_incl.
-apply PQcompare_gt_iff in Hc1.
 destruct c2; [ | | easy ].
 +apply PQcompare_eq_iff in Hc2.
  rewrite Hx, Hc2, <- Hy in Hc1.
  now apply PQlt_irrefl in Hc1.
 +apply PQcompare_lt_iff in Hc2.
  rewrite Hx, Hy in Hc1.
  apply PQnle_gt in Hc2.
  now exfalso; apply Hc2, PQlt_le_incl.
Qed.
Arguments PQcompare_morph x1%PQ x2%PQ Hx%PQ y1%PQ y2%PQ Hy%PQ : rename.

Theorem PQadd_lt_mono_r : ∀ x y z, (x < y)%PQ ↔ (x + z < y + z)%PQ.
Proof.
unfold "<"%PQ, "+"%PQ, PQadd_num1, PQadd_den1, nd; simpl.
intros *.
do 10 rewrite Nat.add_1_r.
do 4 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 4 rewrite Nat.sub_succ, Nat.sub_0_r.
do 2 rewrite Nat.mul_add_distr_r.
remember (S (PQnum1 x)) as xn eqn:Hxn.
remember (S (PQden1 x)) as xd eqn:Hxd.
remember (S (PQnum1 y)) as yn eqn:Hyn.
remember (S (PQden1 y)) as yd eqn:Hyd.
remember (S (PQnum1 z)) as zn eqn:Hzn.
remember (S (PQden1 z)) as zd eqn:Hzd.
replace (zn * yd * (xd * zd)) with (zn * xd * (yd * zd)) by flia.
replace (xn * zd * (yd * zd)) with (xn * yd * (zd * zd)) by flia.
replace (yn * zd * (xd * zd)) with (yn * xd * (zd * zd)) by flia.
split; intros H.
-apply Nat.add_lt_mono_r.
 apply Nat.mul_lt_mono_pos_r; [ | easy ].
 subst zd; simpl; flia.
-apply Nat.add_lt_mono_r in H.
 apply Nat.mul_lt_mono_pos_r in H; [ easy | ].
 subst zd; simpl; flia.
Qed.

Theorem PQadd_le_mono_r : ∀ x y z, (x ≤ y ↔ x + z ≤ y + z)%PQ.
Proof.
unfold "≤"%PQ, "+"%PQ, PQadd_num1, PQadd_den1, nd; simpl.
intros *.
do 10 rewrite Nat.add_1_r.
do 4 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 4 rewrite Nat.sub_succ, Nat.sub_0_r.
do 2 rewrite Nat.mul_add_distr_r.
remember (S (PQnum1 x)) as xn eqn:Hxn.
remember (S (PQden1 x)) as xd eqn:Hxd.
remember (S (PQnum1 y)) as yn eqn:Hyn.
remember (S (PQden1 y)) as yd eqn:Hyd.
remember (S (PQnum1 z)) as zn eqn:Hzn.
remember (S (PQden1 z)) as zd eqn:Hzd.
replace (zn * yd * (xd * zd)) with (zn * xd * (yd * zd)) by flia.
replace (xn * zd * (yd * zd)) with (xn * yd * (zd * zd)) by flia.
replace (yn * zd * (xd * zd)) with (yn * xd * (zd * zd)) by flia.
split; intros H.
-apply Nat.add_le_mono_r.
 now apply Nat.mul_le_mono_r.
-apply Nat.add_le_mono_r in H.
 apply Nat.mul_le_mono_pos_r in H; [ easy | ].
 subst zd; simpl; flia.
Qed.

Theorem PQadd_le_mono_l : ∀ x y z, (x ≤ y ↔ z + x ≤ z + y)%PQ.
Proof.
setoid_rewrite PQadd_comm.
apply PQadd_le_mono_r.
Qed.

Theorem PQadd_le_mono : ∀ x y z t,
  (x ≤ y)%PQ → (z ≤ t)%PQ → (x + z ≤ y + t)%PQ.
Proof.
intros * Hxy Hzt.
apply (PQle_trans _ (y + z)%PQ).
-now apply PQadd_le_mono_r.
-now apply PQadd_le_mono_l.
Qed.

Theorem PQsub_add_eq : ∀ x y,
  (y < x)%PQ → (x - y + y = x * PQone y * PQone y)%PQ.
Proof.
intros x y Hxy.
unfold "<"%PQ, nd in Hxy.
unfold "+"%PQ, "-"%PQ, "==", nd; simpl.
unfold PQsub_num1, PQadd_num1, PQadd_den1, nd; simpl.
unfold "*"%PQ, PQone, PQmul_num1, PQmul_den1; simpl.
do 4 rewrite Nat.add_1_r in Hxy.
f_equal.
PQtac1; repeat PQtac2; [ | flia Hxy ].
PQtac3; rewrite Nat.sub_add; [ easy | ].
setoid_rewrite Nat.mul_shuffle0.
rewrite Nat.mul_shuffle0.
now apply Nat.mul_le_mono_r, Nat.lt_le_incl.
Qed.

Theorem PQsub_add : ∀ x y, (y < x)%PQ → (x - y + y == x)%PQ.
Proof.
intros x y Hxy.
rewrite PQsub_add_eq; [ | easy ].
now do 2 rewrite PQmul_one_r.
Qed.

Theorem PQsub_le_mono_r : ∀ x y z,
  (z < x)%PQ → (z < y)%PQ → (x ≤ y ↔ x - z ≤ y - z)%PQ.
Proof.
intros * Hzx Hzy.
split.
-intros Hxy.
 revert Hzx Hxy Hzy.
 unfold "≤"%PQ, "<"%PQ, "-"%PQ, PQsub_num1, PQadd_den1, nd; simpl.
 do 10 rewrite Nat.add_1_r.
 intros.
 rewrite <- Nat.sub_succ_l; [ | flia Hzx ].
 rewrite Nat.sub_succ, Nat.sub_0_r.
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 rewrite Nat.sub_succ, Nat.sub_0_r.
 rewrite <- Nat.sub_succ_l; [ | flia Hzy ].
 rewrite Nat.sub_succ, Nat.sub_0_r.
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 rewrite Nat.sub_succ, Nat.sub_0_r.
 remember (S (PQnum1 x)) as xn eqn:Hxn.
 remember (S (PQden1 x)) as xd eqn:Hxd.
 remember (S (PQnum1 y)) as yn eqn:Hyn.
 remember (S (PQden1 y)) as yd eqn:Hyd.
 remember (S (PQnum1 z)) as zn eqn:Hzn.
 remember (S (PQden1 z)) as zd eqn:Hzd.
 do 2 rewrite Nat.mul_sub_distr_r.
 replace (zn * yd * (xd * zd)) with (zn * xd * (yd * zd)) by flia.
 replace (xn * zd * (yd * zd)) with (xn * yd * (zd * zd)) by flia.
 replace (yn * zd * (xd * zd)) with (yn * xd * (zd * zd)) by flia.
 apply Nat.sub_le_mono_r.
 now apply Nat.mul_le_mono_r.
-intros Hxyz.
 apply (PQadd_le_mono_r _ _ z) in Hxyz.
 rewrite PQsub_add in Hxyz; [ | easy ].
 now rewrite PQsub_add in Hxyz.
Qed.

Theorem PQsub_le_mono_l : ∀ x y z,
  (x < z)%PQ → (y < z)%PQ → (y ≤ x)%PQ ↔ (z - x ≤ z - y)%PQ.
Proof.
intros * Hzx Hzy.
split.
-intros Hxy.
 revert Hzx Hxy Hzy.
 unfold "≤"%PQ, "<"%PQ, "-"%PQ, PQsub_num1, PQadd_den1, nd; simpl.
 do 10 rewrite Nat.add_1_r.
 intros.
 rewrite <- Nat.sub_succ_l; [ | flia Hzx ].
 rewrite Nat.sub_succ, Nat.sub_0_r.
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 rewrite Nat.sub_succ, Nat.sub_0_r.
 rewrite <- Nat.sub_succ_l; [ | flia Hzy ].
 rewrite Nat.sub_succ, Nat.sub_0_r.
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 rewrite Nat.sub_succ, Nat.sub_0_r.
 remember (S (PQnum1 x)) as xn eqn:Hxn.
 remember (S (PQden1 x)) as xd eqn:Hxd.
 remember (S (PQnum1 y)) as yn eqn:Hyn.
 remember (S (PQden1 y)) as yd eqn:Hyd.
 remember (S (PQnum1 z)) as zn eqn:Hzn.
 remember (S (PQden1 z)) as zd eqn:Hzd.
 do 2 rewrite Nat.mul_sub_distr_r.
 replace (zn * yd * (zd * xd)) with (zn * xd * (zd * yd)) by flia.
 replace (xn * zd * (zd * yd)) with (xn * yd * (zd * zd)) by flia.
 replace (yn * zd * (zd * xd)) with (yn * xd * (zd * zd)) by flia.
 apply Nat.sub_le_mono_l.
 now apply Nat.mul_le_mono_r.
-intros Hxyz.
 apply (PQadd_le_mono_r _ _ (x + y)%PQ) in Hxyz.
 do 2 rewrite PQadd_assoc in Hxyz.
 rewrite PQsub_add in Hxyz; [ | easy ].
 rewrite PQadd_add_swap in Hxyz.
 rewrite PQsub_add in Hxyz; [ | easy ].
 now apply PQadd_le_mono_l in Hxyz.
Qed.

Theorem PQsub_le_mono : ∀ x y z t,
  (y < x)%PQ → (t < z)%PQ → (x ≤ z)%PQ → (t ≤ y)%PQ → (x - y ≤ z - t)%PQ.
Proof.
intros * Hyx Htz Hxz Hty.
eapply (PQle_trans _ (z - y)).
-apply PQsub_le_mono_r; [ easy | | easy ].
 eapply PQlt_le_trans; [ apply Hyx | apply Hxz ].
-apply PQsub_le_mono_l; [ | easy | easy ].
 eapply PQlt_le_trans; [ apply Hyx | apply Hxz ].
Qed.

Theorem PQadd_no_neutral : ∀ x y, (y + x ≠≠ x)%PQ.
Proof.
intros x y Hxy.
unfold "+"%PQ, "=="%PQ, nd in Hxy; simpl in Hxy.
unfold PQadd_num1, PQadd_den1, nd in Hxy.
do 6 rewrite Nat.add_1_r in Hxy.
do 2 (rewrite <- Nat.sub_succ_l in Hxy; [ | simpl; flia ]).
do 2 rewrite Nat.sub_succ, Nat.sub_0_r in Hxy.
rewrite Nat.mul_add_distr_r in Hxy.
rewrite Nat.mul_assoc in Hxy.
apply Nat.add_sub_eq_r in Hxy.
now rewrite Nat.sub_diag in Hxy.
Qed.

Theorem PQsub_no_neutral : ∀ x y, (y < x)%PQ → (x - y ≠≠ x)%PQ.
Proof.
intros *; PQtac1; intros Hyz.
PQtac2; [ | flia Hyz ].
PQtac3.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite Nat.sub_succ, Nat.sub_0_r, Nat.mul_assoc.
intros H.
apply Nat.add_sub_eq_nz in H; [ | simpl; flia ].
rewrite Nat.add_comm, Nat.mul_shuffle0 in H.
rewrite <- Nat.add_0_r in H.
now apply Nat.add_cancel_l in H.
Qed.

Theorem PQadd_sub_same_eq : ∀ px py pz,
  (py == pz)%PQ
  → (px + py - pz = px * PQone py * PQone pz)%PQ.
Proof.
intros * Hyz.
unfold "*"%PQ, PQmul_num1, PQmul_den1.
revert Hyz.
PQtac1; intros; PQtac2; [ | simpl; flia ].
PQtac3; do 2 PQtac2; PQtac3; f_equal.
remember (S (PQnum1 px) * S (PQden1 py)) as t.
now rewrite Nat.mul_shuffle0, Hyz, Nat.mul_shuffle0, Nat.add_sub.
Qed.

Theorem PQadd_sub_eq : ∀ x y, (x + y - y = x * PQone y * PQone y)%PQ.
Proof. now intros; rewrite PQadd_sub_same_eq. Qed.

Theorem PQadd_sub : ∀ x y, (x + y - y == x)%PQ.
Proof.
intros x y.
rewrite PQadd_sub_eq.
now do 2 rewrite PQmul_one_r.
Qed.

Theorem PQlt_add_r : ∀ x y, (x < x + y)%PQ.
Proof.
intros.
unfold "<"%PQ, "+"%PQ; simpl.
unfold PQadd_num1, PQadd_den1, nd; simpl.
do 6 rewrite Nat.add_1_r.
do 2 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 2 (rewrite Nat.sub_succ, Nat.sub_0_r).
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_assoc, Nat.mul_shuffle0.
rewrite <- Nat.add_0_r at 1.
apply Nat.add_le_lt_mono; [ easy | simpl; flia ].
Qed.

Theorem PQlt_add_l : ∀ x y, (x < y + x)%PQ.
Proof.
intros.
rewrite PQadd_comm.
apply PQlt_add_r.
Qed.

Theorem PQle_add_r : ∀ x y, (x ≤ x + y)%PQ.
Proof.
intros.
unfold "≤"%PQ, "+"%PQ; simpl.
unfold PQadd_num1, PQadd_den1, nd; simpl.
do 6 rewrite Nat.add_1_r.
do 2 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 2 (rewrite Nat.sub_succ, Nat.sub_0_r).
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_assoc, Nat.mul_shuffle0.
rewrite <- Nat.add_0_r at 1.
apply Nat.add_le_mono; [ easy | simpl; flia ].
Qed.

Theorem PQle_add_l : ∀ x y, (x ≤ y + x)%PQ.
Proof.
intros.
rewrite PQadd_comm.
apply PQle_add_r.
Qed.

Theorem PQsub_lt : ∀ x y, (y < x)%PQ → (x - y < x)%PQ.
Proof.
intros * Hyx.
revert Hyx; PQtac1; intros.
repeat PQtac2.
-rewrite Nat.mul_assoc, Nat.mul_shuffle0.
 apply Nat.mul_lt_mono_pos_r; [ apply Nat.lt_0_succ | ].
 apply Nat.sub_lt; [ | simpl; apply Nat.lt_0_succ ].
 now apply Nat.lt_le_incl.
-flia Hyx.
Qed.

Theorem PQsub_add_distr : ∀ x y z,
  (y < x)%PQ → (x - (y + z))%PQ = (x - y - z)%PQ.
Proof.
intros * Hyx.
revert Hyx; PQtac1; intros.
repeat PQtac2; PQtac3; [ f_equal; flia | flia Hyx | simpl; flia ].
Qed.

Theorem PQsub_sub_swap : ∀ x y z,
  (y < x)%PQ → (z < x)%PQ → (x - y - z)%PQ = (x - z - y)%PQ.
Proof.
intros * Hyx Hzx.
rewrite <- PQsub_add_distr; [ | easy ].
rewrite <- PQsub_add_distr; [ now rewrite PQadd_comm | easy ].
Qed.

Theorem PQsub_sub_distr : ∀ x y z,
  (z < y)%PQ → (y - z < x)%PQ → (x - (y - z))%PQ = (x + z - y)%PQ.
Proof.
intros * Hzy Hyzx.
revert Hzy Hyzx; PQtac1; intros.
rewrite Nat_sub_sub_swap in Hyzx.
do 2 (rewrite <- Nat.sub_succ_l in Hyzx; [ | flia Hzy ]).
rewrite <- Nat.sub_succ_l in Hyzx; [ | simpl; flia ].
do 2 rewrite Nat.sub_succ, Nat.sub_0_r in Hyzx.
rewrite Nat.mul_sub_distr_r, Nat.mul_assoc in Hyzx.
repeat PQtac2; PQtac3; [ | simpl; flia | ].
-f_equal; [ f_equal | now rewrite Nat.mul_shuffle0 ].
 rewrite Nat_sub_sub_assoc.
 +f_equal; [ | now rewrite Nat.mul_shuffle0 ].
  now f_equal; rewrite Nat.mul_shuffle0.
 +split; [ | flia Hyzx ].
  now apply Nat.mul_le_mono_r, Nat.lt_le_incl.
-flia Hzy.
Qed.

Theorem PQadd_sub_assoc : ∀ x y z,
  (z < y)%PQ → (x + (y - z))%PQ = (x + y - z)%PQ.
Proof.
intros * Hzy.
revert Hzy; PQtac1; intros.
repeat PQtac2; [ | simpl; flia | flia Hzy ].
PQtac3.
f_equal; f_equal.
rewrite Nat.add_sub_assoc.
-f_equal; [ f_equal; apply Nat.mul_shuffle0 | apply Nat.mul_shuffle0 ].
-now apply Nat.mul_le_mono_r, Nat.lt_le_incl.
Qed.

Theorem PQadd_sub_swap : ∀ x y z, (z < x)%PQ → (x + y - z = x - z + y)%PQ.
Proof.
intros * Hzx.
revert Hzx; PQtac1; intros.
repeat PQtac2; [ | flia Hzx | simpl; flia ].
PQtac3.
f_equal; [ f_equal | now rewrite Nat.mul_shuffle0 ].
rewrite Nat.add_sub_swap.
-f_equal; f_equal; apply Nat.mul_shuffle0.
-setoid_rewrite Nat.mul_shuffle0.
 rewrite Nat.mul_shuffle0.
 apply Nat.mul_le_mono_pos_r; [ apply Nat.lt_0_succ | ].
 now apply Nat.lt_le_incl.
Qed.

Theorem PQadd_cancel_l_eq : ∀ x y z,
  (z + x == z + y)%PQ → (x * PQone y = y * PQone x)%PQ.
Proof.
intros * H.
revert H; PQtac1; intros.
do 4 (rewrite <- Nat.sub_succ_l in H; [ | simpl; flia ]).
do 4 rewrite Nat.sub_succ, Nat.sub_0_r in H.
setoid_rewrite Nat.mul_comm in H.
do 2 rewrite <- Nat.mul_assoc in H.
apply Nat.mul_cancel_l in H; [ | easy ].
setoid_rewrite Nat.mul_comm in H.
do 2 rewrite Nat.mul_add_distr_r in H.
rewrite Nat.mul_shuffle0 in H.
apply Nat.add_cancel_l in H.
setoid_rewrite Nat.mul_shuffle0 in H.
apply Nat.mul_cancel_r in H; [ | easy ].
unfold "*"%PQ, PQone, PQmul_num1, PQmul_den1; simpl.
PQtac1; rewrite H; f_equal.
now rewrite Nat.mul_comm.
Qed.

Theorem PQadd_cancel_l : ∀ x y z, (z + x == z + y)%PQ ↔ (x == y)%PQ.
Proof.
intros.
split; intros H; [ | now rewrite H ].
specialize (PQadd_cancel_l_eq _ _ _ H) as H1.
unfold "*"%PQ, PQone, PQmul_num1, PQmul_den1 in H1; simpl in H1.
injection H1; clear H1; intros H1 H2.
revert H2; PQtac1; intros.
simpl in H2; simpl; do 2 rewrite Nat.sub_0_r in H2.
now rewrite H2.
Qed.

(* mouais, chais pas si PQadd_cancel_l ci-dessus est très convainquant ;
   est-ce une bonne idée de passer par PQadd_cancel_l_eq ?
   du coup, chais pas, mais je ne le fais pas pour PQadd_cancel_r
   ci-dessous *)

Theorem PQadd_cancel_r : ∀ x y z, (x + z == y + z ↔ x == y)%PQ.
Proof.
intros.
setoid_rewrite PQadd_comm.
apply PQadd_cancel_l.
Qed.
Arguments PQadd_cancel_r x%PQ y%PQ z%PQ.

Theorem PQsub_cancel_l : ∀ x y z,
  (y < x)%PQ → (z < x)%PQ → (x - y == x - z)%PQ ↔ (y == z)%PQ.
Proof.
intros * Hyx Hzx.
split; intros H.
-apply (PQadd_cancel_r _ _ z) in H.
 rewrite PQsub_add in H; [ | easy ].
 apply (PQadd_cancel_r _ _ (x - y)).
 setoid_rewrite PQadd_comm.
 rewrite PQsub_add; [ | easy ].
 now symmetry.
-apply (PQadd_cancel_r _ _ z).
 rewrite PQsub_add; [ | easy ].
 apply (PQadd_cancel_r _ _ (x - y)) in H.
 setoid_rewrite PQadd_comm in H.
 rewrite PQsub_add in H; [ | easy ].
 now symmetry.
Qed.

Theorem PQsub_cancel_r : ∀ x y z,
  (z < x)%PQ → (z < y)%PQ → (x - z == y - z)%PQ ↔ (x == y)%PQ.
Proof.
intros * Hzx Hzy.
split; intros H.
-apply (PQadd_cancel_l _ _ z) in H.
 setoid_rewrite PQadd_comm in H.
 rewrite PQsub_add in H; [ | easy ].
 now rewrite PQsub_add in H.
-apply (PQadd_cancel_r _ _ z).
 rewrite PQsub_add; [ | easy ].
 now rewrite PQsub_add.
Qed.

Theorem PQmul_comm : ∀ x y, (x * y = y * x)%PQ.
Proof.
intros.
unfold "*"%PQ; f_equal.
-now unfold PQmul_num1; simpl; rewrite Nat.mul_comm.
-now unfold PQmul_den1; simpl; rewrite Nat.mul_comm.
Qed.

Theorem PQmul_1_l : ∀ a, (1 * a)%PQ = a.
Proof.
intros.
unfold "*"%PQ.
unfold PQmul_num1, PQmul_den1; simpl.
do 2 rewrite Nat.add_0_r, Nat.add_sub.
now destruct a.
Qed.

Theorem PQmul_assoc : ∀ x y z, (x * (y * z) = (x * y) * z)%PQ.
intros.
unfold "*"%PQ; simpl.
unfold PQmul_num1, PQmul_den1; simpl; PQtac1; repeat PQtac2; f_equal.
-now rewrite Nat.mul_assoc.
-now rewrite Nat.mul_assoc.
Qed.

Theorem PQmul_mul_swap : ∀ x y z, (x * y * z = x * z * y)%PQ.
intros.
unfold "*"%PQ; simpl.
unfold PQmul_num1, PQmul_den1; simpl; PQtac1; repeat PQtac2; f_equal.
-now rewrite Nat.mul_shuffle0.
-now rewrite Nat.mul_shuffle0.
Qed.

Theorem PQmul_le_mono_l : ∀ x y z, (x ≤ y → z * x ≤ z * y)%PQ.
Proof.
intros *.
unfold "≤"%PQ, nd; simpl.
unfold PQmul_num1, PQmul_den1.
do 10 rewrite Nat.add_1_r.
do 4 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 4 rewrite Nat.sub_succ, Nat.sub_0_r.
intros Hxy.
do 2 rewrite Nat.mul_assoc.
setoid_rewrite Nat.mul_shuffle0.
apply Nat.mul_le_mono_r.
do 2 rewrite <- Nat.mul_assoc.
now apply Nat.mul_le_mono_l.
Qed.

Theorem PQmul_le_mono_r : ∀ x y z, (x ≤ y → x * z ≤ y * z)%PQ.
Proof.
intros * Hxy.
setoid_rewrite PQmul_comm.
now apply PQmul_le_mono_l.
Qed.

Theorem PQmul_add_distr_l_eq : ∀ x y z,
  (x * (y + z) * PQone x = x * y + x * z)%PQ.
Proof.
intros.
unfold "==", "*"%PQ, "+"%PQ, nd; simpl.
unfold PQmul_num1, PQadd_den1, PQadd_num1, PQmul_den1, nd; simpl.
PQtac1; do 2 PQtac2; [ | simpl; flia ].
PQtac3; do 6 PQtac2.
PQtac3; f_equal; [ | now rewrite Nat.mul_shuffle0 ].
now f_equal; f_equal; rewrite Nat.mul_shuffle0.
Qed.

Theorem PQmul_add_distr_l : ∀ x y z, (x * (y + z) == x * y + x * z)%PQ.
Proof. now intros; rewrite <- PQmul_add_distr_l_eq, PQmul_one_r. Qed.

Theorem PQmul_sub_distr_l_eq : ∀ x y z,
  (z < y → x * (y - z) * PQone x = x * y - x * z)%PQ.
Proof.
intros *.
unfold "==", "*"%PQ, "+"%PQ, "<"%PQ, nd; simpl.
unfold PQmul_num1, PQadd_den1, PQadd_num1, PQmul_den1, nd; simpl.
PQtac1; intros Hzy.
repeat PQtac2.
-repeat rewrite Nat.mul_assoc; f_equal.
 +f_equal; PQtac3; f_equal; apply Nat.mul_shuffle0.
 +f_equal; apply Nat.mul_shuffle0.
-flia Hzy.
Qed.

Theorem PQmul_sub_distr_l : ∀ x y z,
  (z < y → x * (y - z) == x * y - x * z)%PQ.
Proof.
intros * Hzy.
rewrite <- PQmul_sub_distr_l_eq; [ | easy ].
now rewrite PQmul_one_r.
Qed.

Theorem PQmul_cancel_l_eq : ∀ x y z,
  (z * x == z * y)%PQ → (x * PQone y = y * PQone x)%PQ.
Proof.
intros * H.
revert H; unfold "*"%PQ, PQmul_num1, PQmul_den1.
destruct x as (xn, xd).
destruct y as (yn, yd).
destruct z as (zn, zd); simpl.
PQtac1; do 4 PQtac2.
intros.
do 2 rewrite <- Nat.mul_assoc in H.
apply Nat.mul_cancel_l in H; [ | easy ].
setoid_rewrite Nat.mul_comm in H.
do 2 rewrite <- Nat.mul_assoc in H.
apply Nat.mul_cancel_l in H; [ | easy ].
f_equal; rewrite Nat.mul_comm; [ now rewrite H, Nat.mul_comm | easy ].
Qed.

Theorem PQmul_cancel_l : ∀ x y z, (z * x == z * y ↔ x == y)%PQ.
Proof.
Proof.
intros.
split; intros H; [ | now rewrite H ].
specialize (PQmul_cancel_l_eq _ _ _ H) as H1.
unfold "*"%PQ, PQone, PQmul_num1, PQmul_den1 in H1; simpl in H1.
injection H1; clear H1; intros H1 H2.
revert H2; PQtac1; intros.
simpl in H2; simpl; do 2 rewrite Nat.sub_0_r in H2.
now rewrite H2.
Qed.

Theorem PQinv_involutive : ∀ x, (/ / x = x)%PQ.
Proof. intros. unfold "/"%PQ; now destruct x. Qed.

(* *)

Ltac PQcompare_iff :=
  match goal with
  | [ H : PQcompare _ _ = Eq |- _ ] => apply PQcompare_eq_iff in H
  | [ H : PQcompare _ _ = Lt |- _ ] => apply PQcompare_lt_iff in H
  | [ H : PQcompare _ _ = Gt |- _ ] => apply PQcompare_gt_iff in H
  end.

Theorem PQcompare_refl : ∀ x, PQcompare x x = Eq.
Proof.
intros.
remember (PQcompare x x) as c eqn:Hc; symmetry in Hc.
now destruct c; [ easy | | ]; PQcompare_iff; apply PQlt_irrefl in Hc.
Qed.

Theorem PQmul_lt_cancel_l : ∀ x y z, (x * y < x * z)%PQ ↔ (y < z)%PQ.
Proof.
intros.
unfold "<"%PQ, nd.
unfold "*"%PQ; simpl.
unfold PQmul_num1, PQmul_den1.
rewrite Nat.sub_add; [ | destruct (PQnum1 x); simpl; flia ].
rewrite Nat.sub_add; [ | destruct (PQden1 x); simpl; flia ].
rewrite Nat.sub_add; [ | destruct (PQnum1 x); simpl; flia ].
rewrite Nat.sub_add; [ | destruct (PQden1 x); simpl; flia ].
setoid_rewrite Nat.mul_shuffle1.
split; intros H.
-apply Nat.mul_lt_mono_pos_l in H; [ easy | ].
 do 2 rewrite Nat.add_1_r; simpl; apply Nat.lt_0_succ.
-apply Nat.mul_lt_mono_pos_l; [ | easy ].
 do 2 rewrite Nat.add_1_r; simpl; apply Nat.lt_0_succ.
Qed.

Theorem PQcompare_mul_cancel_l : ∀ x y z,
  PQcompare (x * y) (x * z) = PQcompare y z.
Proof.
intros.
remember (PQcompare (x * y) (x * z)) as b1 eqn:Hb1.
symmetry in Hb1; symmetry.
destruct b1; PQcompare_iff.
-apply PQcompare_eq_iff.
 now apply PQmul_cancel_l in Hb1.
-apply PQcompare_lt_iff.
 now apply PQmul_lt_cancel_l in Hb1.
-apply PQcompare_gt_iff.
 now apply PQmul_lt_cancel_l in Hb1.
Qed.

Require Import Nat_ggcd.

Definition PQred x :=
  let '(_, (aa, bb)) := ggcd (PQnum1 x + 1) (PQden1 x + 1) in
  PQmake (aa - 1) (bb - 1).
Arguments PQred x%PQ.

Instance PQred_morph : Proper (PQeq ==> PQeq) PQred.
Proof.
intros (xn, xd) (yn, yd) Hxy.
unfold "=="%PQ, nd in Hxy |-*; simpl in *.
unfold PQred; simpl.
remember (ggcd (xn + 1) (xd + 1)) as g1 eqn:Hg1; symmetry in Hg1.
remember (ggcd (yn + 1) (yd + 1)) as g2 eqn:Hg2; symmetry in Hg2.
move g2 before g1.
destruct g1 as (g1 & aa1 & bb1).
destruct g2 as (g2 & aa2 & bb2); simpl.
specialize (ggcd_correct_divisors (xn + 1) (xd + 1)) as H1.
rewrite Hg1 in H1; destruct H1 as (Hxn, Hxd).
specialize (ggcd_correct_divisors (yn + 1) (yd + 1)) as H1.
rewrite Hg2 in H1; destruct H1 as (Hyn, Hyd).
rewrite Nat.mul_comm, Nat.add_1_r in Hxn, Hxd, Hyn, Hyd.
rewrite Nat.sub_add; [ | destruct aa1; flia Hxn ].
rewrite Nat.sub_add; [ | destruct bb2; flia Hyd ].
rewrite Nat.sub_add; [ | destruct aa2; flia Hyn ].
rewrite Nat.sub_add; [ | destruct bb1; flia Hxd ].
rewrite Nat.mul_comm in Hxn, Hxd, Hyn, Hyd.
do 4 rewrite Nat.add_1_r in Hxy.
apply (Nat.mul_cancel_l _ _ g1); [ now destruct g1 | ].
rewrite Nat.mul_assoc, <- Hxn, Nat.mul_comm.
apply (Nat.mul_cancel_l _ _ g2); [ now destruct g2 | ].
rewrite Nat.mul_assoc, <- Hyd, Nat.mul_comm.
rewrite Hxy, Hyn, Hxd.
flia.
Qed.

(*
Definition PQH x := PQmake (PQnum1 x + 1) (PQden1 x + 1).
Definition PQF a b := PQmake (a - 1) (b - 1).

Compute (PQH (PQred (PQF 16 24))).
Compute (PQH (PQred (PQF 2 3))).
*)

Theorem PQred_idemp : ∀ x, PQred (PQred x) = PQred x.
Proof.
intros (xn, xd).
unfold PQred; simpl.
remember (ggcd (xn + 1) (xd + 1)) as g eqn:Hg1.
destruct g as (g1, (aa1, bb1)); simpl.
assert (Haa1 : aa1 ≠ 0). {
  intros H; subst aa1.
  specialize (ggcd_succ_l_neq_0 xn (xd + 1)) as H.
  now rewrite <- Nat.add_1_r, <- Hg1 in H.
}
assert (Hbb1 : bb1 ≠ 0). {
  intros H; subst bb1.
  symmetry in Hg1.
  apply ggcd_swap in Hg1.
  specialize (ggcd_succ_l_neq_0 xd (xn + 1)) as H.
  now rewrite <- Nat.add_1_r, Hg1 in H.
}
rewrite Nat.sub_add; [ | flia Haa1 ].
rewrite Nat.sub_add; [ | flia Hbb1 ].
specialize (ggcd_correct_divisors (xn + 1) (xd + 1)) as H1.
rewrite <- Hg1 in H1.
destruct H1 as (H1, H2).
remember (ggcd aa1 bb1) as g eqn:Hg2.
destruct g as (g2, (aa2, bb2)); simpl.
specialize (ggcd_correct_divisors aa1 bb1) as H3.
rewrite <- Hg2 in H3.
destruct H3 as (H3, H4).
move H1 before H3; move H2 before H3.
rewrite H3, Nat.mul_assoc in H1.
rewrite H4, Nat.mul_assoc in H2.
rewrite H1, H2 in Hg1.
remember (g1 * g2) as g eqn:Hg.
specialize (ggcd_gcd (g * aa2) (g * bb2)) as H.
rewrite <- Hg1 in H; simpl in H.
rewrite Nat.gcd_mul_mono_l in H.
rewrite Hg in H; symmetry in H.
rewrite <- Nat.mul_1_r, <- Nat.mul_assoc in H.
apply Nat.mul_cancel_l in H.
-apply Nat.eq_mul_1 in H.
 destruct H as (HH, H); subst g2.
 now rewrite Nat.mul_1_l in H3, H4; subst bb1 aa1.
-intros H5; subst g1; simpl in Hg; subst g.
 now rewrite Nat.add_1_r in H1.
Qed.

Theorem PQred_add_mul_one_l : ∀ x y a, PQred (x + y) = PQred (PQmake a a * x + y).
Proof.
intros (xn, xd) (yn, yd) a.
unfold PQred; simpl.
unfold "*"%PQ, PQ_of_nat.
unfold PQmul_num1, PQmul_den1; simpl.
unfold PQadd_num1, PQadd_den1, nd; simpl.
PQtac1.
PQtac2; [ PQtac2 | simpl; flia ].
PQtac2; [ | simpl; flia ].
do 3 PQtac2.
replace (S yn * (S a * S xd)) with (S a * (S yn * S xd)) by flia.
rewrite <- Nat.mul_assoc, <- Nat.mul_add_distr_l.
rewrite <- Nat.mul_assoc.
rewrite ggcd_mul_mono_l; [ | easy ].
now destruct (ggcd (S xn * S yd + S yn * S xd) (S xd * S yd)).
Qed.

Theorem PQred_sub_mul_one_l : ∀ x y a,
  (y < x)%PQ -> PQred (x - y) = PQred (PQmake a a * x - y).
Proof.
intros (xn, xd) (yn, yd) a Hyx.
unfold PQred; simpl.
unfold "*"%PQ, PQ_of_nat.
unfold PQmul_num1, PQmul_den1; simpl.
unfold PQsub_num1, PQadd_den1, nd; simpl.
revert Hyx; PQtac1; intros.
PQtac2; [ PQtac2 | flia Hyx ].
PQtac2.
-do 3 PQtac2.
 replace (S yn * (S a * S xd)) with (S a * (S yn * S xd)) by flia.
 rewrite <- Nat.mul_assoc, <- Nat.mul_sub_distr_l.
 rewrite <- Nat.mul_assoc.
 rewrite ggcd_mul_mono_l; [ | easy ].
 now destruct (ggcd (S xn * S yd - S yn * S xd) (S xd * S yd)).
-do 2 PQtac2.
 replace (S yn * (S a * S xd)) with (S a * (S yn * S xd)) by flia.
 rewrite <- Nat.mul_assoc, <- Nat.mul_sub_distr_l.
 simpl; flia Hyx.
Qed.

Theorem PQred_sub_mul_one_r : ∀ x y a,
  (y < x)%PQ -> PQred (x - y) = PQred (x - PQmake a a * y).
Proof.
intros (xn, xd) (yn, yd) a Hyx.
unfold PQred; simpl.
unfold "*"%PQ, PQ_of_nat.
unfold PQmul_num1, PQmul_den1; simpl.
unfold PQsub_num1, PQadd_den1, nd; simpl.
revert Hyx; PQtac1; intros.
PQtac2; [ PQtac2 | flia Hyx ].
PQtac2.
-do 3 PQtac2.
 replace (S xn * (S a * S yd)) with (S a * (S xn * S yd)) by flia.
 rewrite <- Nat.mul_assoc, <- Nat.mul_sub_distr_l.
 replace (S xd * (S a * S yd)) with (S a * (S xd * S yd)) by flia.
 rewrite ggcd_mul_mono_l; [ | easy ].
 now destruct (ggcd (S xn * S yd - S yn * S xd) (S xd * S yd)).
-do 2 PQtac2.
 replace (S xn * (S a * S yd)) with (S a * (S xn * S yd)) by flia.
 rewrite <- Nat.mul_assoc, <- Nat.mul_sub_distr_l.
 simpl; flia Hyx.
Qed.

Theorem PQred_mul_mul_one_l : ∀ x y a, PQred (x * y) = PQred (PQmake a a * x * y).
Proof.
intros (xn, xd) (yn, yd) a.
unfold PQred; simpl.
unfold "*"%PQ, PQ_of_nat.
unfold PQmul_num1, PQmul_den1; simpl.
PQtac1.
do 6 PQtac2.
do 2 rewrite <- Nat.mul_assoc.
rewrite ggcd_mul_mono_l; [ | easy ].
now destruct (ggcd (S xn * S yn) (S xd * S yd)).
Qed.

Theorem PQred_lt_l : ∀ x y, (x < y)%PQ → (PQred x < y)%PQ.
Proof.
intros * Hyx.
unfold PQred.
remember (Nat.gcd (PQnum1 x + 1) (PQden1 x + 1)) as a eqn:Ha.
erewrite ggcd_split; [ | apply Ha ].
unfold "<"%PQ, nd; simpl.
assert (Haz : a ≠ 0). {
  intros H; rewrite Ha in H.
  apply Nat.gcd_eq_0_l in H.
  now rewrite Nat.add_1_r in H.
}
specialize (Nat.gcd_divide_l (PQnum1 x + 1) (PQden1 x + 1)) as (c1, Hc1).
rewrite <- Ha in Hc1; rewrite Hc1.
rewrite Nat.div_mul; [ | easy ].
specialize (Nat.gcd_divide_r (PQnum1 x + 1) (PQden1 x + 1)) as (c2, Hc2).
rewrite <- Ha in Hc2; rewrite Hc2.
rewrite Nat.div_mul; [ | easy ].
rewrite Nat.sub_add.
-rewrite Nat.sub_add.
 +rewrite (Nat.mul_lt_mono_pos_r a); [ | flia Haz ].
  rewrite Nat.mul_shuffle0, <- Hc1.
  rewrite <- Nat.mul_assoc, <- Hc2.
  easy.
 +destruct c2; [ flia Hc2 | flia ].
-destruct c1; [ flia Hc1 | flia ].
Qed.

Theorem PQred_lt_r : ∀ x y, (x < y)%PQ → (x < PQred y)%PQ.
Proof.
intros * Hyx.
unfold PQred.
remember (Nat.gcd (PQnum1 y + 1) (PQden1 y + 1)) as a eqn:Ha.
erewrite ggcd_split; [ | apply Ha ].
unfold "<"%PQ, nd; simpl.
assert (Haz : a ≠ 0). {
  intros H; rewrite Ha in H.
  apply Nat.gcd_eq_0_l in H.
  now rewrite Nat.add_1_r in H.
}
specialize (Nat.gcd_divide_l (PQnum1 y + 1) (PQden1 y + 1)) as (c1, Hc1).
rewrite <- Ha in Hc1; rewrite Hc1.
rewrite Nat.div_mul; [ | easy ].
specialize (Nat.gcd_divide_r (PQnum1 y + 1) (PQden1 y + 1)) as (c2, Hc2).
rewrite <- Ha in Hc2; rewrite Hc2.
rewrite Nat.div_mul; [ | easy ].
rewrite Nat.sub_add.
-rewrite Nat.sub_add.
 +rewrite (Nat.mul_lt_mono_pos_r a); [ | flia Haz ].
  rewrite <- Nat.mul_assoc, <- Hc2.
  rewrite Nat.mul_shuffle0, <- Hc1.
  easy.
 +destruct c1; [ flia Hc1 | flia ].
-destruct c2; [ flia Hc2 | flia ].
Qed.

Theorem PQred_le_l : ∀ x y, (x ≤ y)%PQ → (PQred x ≤ y)%PQ.
Proof.
intros * Hyx.
destruct (PQeq_dec x y) as [H1| H1].
-rewrite H1.
 destruct y as (yn, yd); simpl.
 unfold "≤"%PQ, nd; simpl.
 unfold PQred; simpl.
 remember (ggcd (yn + 1) (yd + 1)) as g eqn:Hg; symmetry in Hg.
 destruct g as (g, (aa, bb)); simpl.
 specialize (ggcd_correct_divisors (yn + 1) (yd + 1)) as Hy.
 rewrite Hg in Hy; destruct Hy as (Hyn, Hyd).
 rewrite Nat.add_1_r, Nat.mul_comm in Hyn, Hyd.
 rewrite Nat.sub_add; [ | destruct aa; flia Hyn ].
 rewrite Nat.sub_add; [ | destruct bb; flia Hyd ].
 rewrite Nat.mul_comm in Hyn, Hyd.
 apply (Nat.mul_le_mono_pos_l _ _ g); [ destruct g; flia Hyn | ].
 rewrite Nat.mul_assoc, <- Hyn.
 rewrite Nat.mul_assoc, Nat.mul_shuffle0, <- Hyd.
 flia.
-apply PQlt_le_incl, PQred_lt_l.
 apply PQnle_gt.
 intros H2; apply H1.
 now apply PQle_antisymm.
Qed.

Theorem PQred_le_r : ∀ x y, (x ≤ y)%PQ → (x ≤ PQred y)%PQ.
Proof.
intros * Hyx.
destruct (PQeq_dec x y) as [H1| H1].
-rewrite H1.
 destruct y as (yn, yd); simpl.
 unfold "≤"%PQ, nd; simpl.
 unfold PQred; simpl.
 remember (ggcd (yn + 1) (yd + 1)) as g eqn:Hg; symmetry in Hg.
 destruct g as (g, (aa, bb)); simpl.
 specialize (ggcd_correct_divisors (yn + 1) (yd + 1)) as Hy.
 rewrite Hg in Hy; destruct Hy as (Hyn, Hyd).
 rewrite Nat.add_1_r, Nat.mul_comm in Hyn, Hyd.
 rewrite Nat.sub_add; [ | destruct bb; flia Hyd ].
 rewrite Nat.sub_add; [ | destruct aa; flia Hyn ].
 rewrite Nat.mul_comm in Hyn, Hyd.
 apply (Nat.mul_le_mono_pos_l _ _ g); [ destruct g; flia Hyn | ].
 rewrite Nat.mul_assoc, Nat.mul_shuffle0, <- Hyd.
 rewrite Nat.mul_assoc, <- Hyn.
 flia.
-apply PQlt_le_incl, PQred_lt_r.
 apply PQnle_gt.
 intros H2; apply H1.
 now apply PQle_antisymm.
Qed.

Theorem PQred_add_l : ∀ x y, PQred (x + y) = PQred (PQred x + y).
Proof.
intros.
remember (Nat.gcd (PQnum1 x + 1) (PQden1 x + 1)) as a eqn:Ha.
rewrite (PQred_add_mul_one_l (PQred x) y (a - 1)).
f_equal; f_equal.
destruct x as (xn, xd).
simpl in Ha.
unfold "*"%PQ; simpl.
unfold PQmul_num1, PQmul_den1; simpl.
unfold PQred; simpl.
specialize (ggcd_split (xn + 1) (xd + 1) a Ha) as H.
rewrite H; simpl.
destruct a.
-symmetry in Ha.
 apply Nat.gcd_eq_0_l in Ha; flia Ha.
-replace (S a - 1 + 1) with (S a) by flia.
 assert (H2 : (xn + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (Nat_gcd_le_l (xn + 1) (xd +  1)) as H2.
   assert (H3 : xn + 1 ≠ 0) by flia.
   specialize (H2 H3).
   flia Ha H1 H2.
 }
 assert (H3 : (xd + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (Nat_gcd_le_r (xn + 1) (xd +  1)) as H3.
   assert (H4 : xd + 1 ≠ 0) by flia.
   specialize (H3 H4).
   flia Ha H1 H3.
 }
 rewrite Nat.sub_add; [ | flia H2 ].
 rewrite Nat.sub_add; [ | flia H3 ].
 specialize (Nat.gcd_divide_l (xn + 1) (xd + 1)) as (c1, Hc1).
 rewrite <- Ha in Hc1; rewrite Hc1.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc1, Nat.add_sub.
 specialize (Nat.gcd_divide_r (xn + 1) (xd + 1)) as (c2, Hc2).
 rewrite <- Ha in Hc2; rewrite Hc2.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc2, Nat.add_sub.
 easy.
Qed.

Theorem PQred_sub_l : ∀ x y, (y < x)%PQ → PQred (x - y) = PQred (PQred x - y).
Proof.
intros * Hyx.
remember (Nat.gcd (PQnum1 x + 1) (PQden1 x + 1)) as a eqn:Ha.
rewrite (PQred_sub_mul_one_l (PQred x) y (a - 1)); [ | now apply PQred_lt_r ].
destruct x as (xn, xd).
simpl in Ha.
unfold "*"%PQ; simpl.
unfold PQmul_num1, PQmul_den1; simpl.
unfold PQred; simpl.
specialize (ggcd_split (xn + 1) (xd + 1) a Ha) as H.
rewrite H; simpl.
destruct a.
-symmetry in Ha.
 apply Nat.gcd_eq_0_l in Ha; flia Ha.
-replace (S a - 1 + 1) with (S a) by flia.
 assert (H2 : (xn + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (Nat_gcd_le_l (xn + 1) (xd +  1)) as H2.
   assert (H3 : xn + 1 ≠ 0) by flia.
   specialize (H2 H3).
   flia Ha H1 H2.
 }
 assert (H3 : (xd + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (Nat_gcd_le_r (xn + 1) (xd +  1)) as H3.
   assert (H4 : xd + 1 ≠ 0) by flia.
   specialize (H3 H4).
   flia Ha H1 H3.
 }
 rewrite Nat.sub_add; [ | flia H2 ].
 rewrite Nat.sub_add; [ | flia H3 ].
 specialize (Nat.gcd_divide_l (xn + 1) (xd + 1)) as (c1, Hc1).
 rewrite <- Ha in Hc1; rewrite Hc1.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc1, Nat.add_sub.
 specialize (Nat.gcd_divide_r (xn + 1) (xd + 1)) as (c2, Hc2).
 rewrite <- Ha in Hc2; rewrite Hc2.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc2, Nat.add_sub.
 easy.
Qed.

Theorem PQred_sub_r : ∀ x y, (y < x)%PQ → PQred (x - y) = PQred (x - PQred y).
Proof.
intros * Hyx.
remember (Nat.gcd (PQnum1 y + 1) (PQden1 y + 1)) as a eqn:Ha.
rewrite (PQred_sub_mul_one_r x (PQred y) (a - 1)); [ | now apply PQred_lt_l ].
destruct y as (yn, yd).
simpl in Ha.
unfold "*"%PQ; simpl.
unfold PQmul_num1, PQmul_den1; simpl.
unfold PQred; simpl.
specialize (ggcd_split (yn + 1) (yd + 1) a Ha) as H.
rewrite H; simpl.
destruct a.
-symmetry in Ha.
 apply Nat.gcd_eq_0_l in Ha; flia Ha.
-replace (S a - 1 + 1) with (S a) by flia.
 assert (H2 : (yn + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (Nat_gcd_le_l (yn + 1) (yd +  1)) as H2.
   assert (H3 : yn + 1 ≠ 0) by flia.
   specialize (H2 H3).
   flia Ha H1 H2.
 }
 assert (H3 : (yd + 1) / S a ≠ 0). {
   intros H1.
   apply Nat.div_small_iff in H1; [ | easy ].
   specialize (Nat_gcd_le_r (yn + 1) (yd +  1)) as H3.
   assert (H4 : yd + 1 ≠ 0) by flia.
   specialize (H3 H4).
   flia Ha H1 H3.
 }
 rewrite Nat.sub_add; [ | flia H2 ].
 rewrite Nat.sub_add; [ | flia H3 ].
 specialize (Nat.gcd_divide_l (yn + 1) (yd + 1)) as (c1, Hc1).
 rewrite <- Ha in Hc1; rewrite Hc1.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc1, Nat.add_sub.
 specialize (Nat.gcd_divide_r (yn + 1) (yd + 1)) as (c2, Hc2).
 rewrite <- Ha in Hc2; rewrite Hc2.
 rewrite Nat.div_mul; [ | easy ].
 rewrite Nat.mul_comm, <- Hc2, Nat.add_sub.
 easy.
Qed.

Theorem PQred_add : ∀ x y, PQred (x + y) = PQred (PQred x + PQred y).
Proof.
intros.
rewrite PQred_add_l, PQadd_comm.
rewrite PQred_add_l, PQadd_comm.
easy.
Qed.
(* merci Bérénice ! *)

Theorem PQred_sub : ∀ x y,
  (y < x)%PQ → PQred (x - y) = PQred (PQred x - PQred y).
Proof.
intros.
rewrite PQred_sub_l; [ | easy ].
rewrite PQred_sub_r; [ easy | ].
now apply PQred_lt_r.
Qed.

Theorem PQred_mul_l : ∀ x y, PQred (x * y) = PQred (PQred x * y).
Proof.
intros.
remember (Nat.gcd (PQnum1 x + 1) (PQden1 x + 1)) as a eqn:Ha.
rewrite (PQred_mul_mul_one_l (PQred x) y (a - 1)).
destruct x as (xn, xd).
simpl in Ha.
unfold "*"%PQ; simpl.
unfold PQmul_num1, PQmul_den1; simpl.
unfold PQred; simpl.
specialize (ggcd_split (xn + 1) (xd + 1) a Ha) as H.
rewrite H; simpl.
destruct a.
-symmetry in Ha.
 apply Nat.gcd_eq_0_l in Ha; flia Ha.
-replace (S a - 1 + 1) with (S a) by flia.
 assert (H2 : 1 ≤ (xn + 1) / S a). {
   apply Nat.div_str_pos.
   split; [ apply Nat.lt_0_succ | ].
   rewrite Ha; apply Nat_gcd_le_l.
   now rewrite Nat.add_1_r.
 }
 assert (H3 : 1 ≤ (xd + 1) / S a). {
   apply Nat.div_str_pos.
   split; [ apply Nat.lt_0_succ | ].
   rewrite Ha; apply Nat_gcd_le_r.
   now rewrite Nat.add_1_r.
 }
 do 4 (rewrite Nat.sub_add; [ | do 2 rewrite Nat.add_1_r; simpl; flia ]).
 rewrite Nat.sub_add; [ | easy ].
 rewrite Nat.sub_add.
 +rewrite Nat.sub_add.
  *rewrite Nat.sub_add; [ | easy ].
   rewrite <- Nat.divide_div_mul_exact; [ | easy | ].
  --rewrite <- Nat.divide_div_mul_exact; [ | easy | ].
   ++replace (S a * (xn + 1)) with ((xn + 1) * S a) by apply Nat.mul_comm.
     replace (S a * (xd + 1)) with ((xd + 1) * S a) by apply Nat.mul_comm.
     rewrite Nat.div_mul; [ | easy ].
     now rewrite Nat.div_mul.
   ++rewrite Ha; apply Nat.gcd_divide_r.
  --rewrite Ha; apply Nat.gcd_divide_l.
  *rewrite Nat.sub_add; [ | easy ].
   rewrite <- Nat.divide_div_mul_exact; [ | easy | ].
  --rewrite Nat.mul_comm, Nat.div_mul; [ flia | easy ].
  --rewrite Ha; apply Nat.gcd_divide_r.
 +rewrite Nat.sub_add.
  *rewrite Nat.sub_add; [ | easy ].
   do 2 rewrite Nat.add_1_r.
   eapply Nat.le_trans; [ | apply Nat_mul_le_pos_r; flia ].
   do 2 rewrite Nat.add_1_r in Ha.
   rewrite <- Nat.divide_div_mul_exact; [ | easy | ].
  --rewrite Nat.mul_comm, Nat.div_mul; [ flia | easy ].
  --rewrite Ha; apply Nat.gcd_divide_r.
  *rewrite Nat.sub_add; [ | easy ].
   rewrite <- Nat.divide_div_mul_exact; [ | easy | ].
  --rewrite Nat.mul_comm, Nat.div_mul; [ flia | easy ].
  --rewrite Ha; apply Nat.gcd_divide_r.
Qed.

Theorem PQred_mul : ∀ x y, PQred (x * y) = PQred (PQred x * PQred y).
Proof.
intros.
rewrite PQred_mul_l, PQmul_comm.
rewrite PQred_mul_l, PQmul_comm.
easy.
Qed.

Theorem PQred_gcd : ∀ x,
  Nat.gcd (PQnum1 (PQred x) + 1) (PQden1 (PQred x) + 1) = 1.
Proof.
intros.
unfold PQred.
remember (ggcd (PQnum1 x + 1) (PQden1 x + 1)) as g eqn:Hg1.
destruct g as (g1, (aa1, bb1)); simpl.
remember (Nat.gcd (PQnum1 x + 1) (PQden1 x + 1)) as g eqn:Hg.
specialize (ggcd_split _ _ _ Hg) as H.
rewrite <- Hg1 in H.
do 2 rewrite Nat.add_1_r in Hg1; symmetry in Hg1.
rewrite Nat.sub_add.
-rewrite Nat.sub_add.
 +injection H; clear H; intros; subst g1 aa1 bb1.
  apply ggcd_succ_l in Hg1.
  now apply Nat.gcd_div_gcd.
 +apply ggcd_succ_r in Hg1; flia Hg1.
-apply ggcd_succ_l in Hg1; flia Hg1.
Qed.

Definition PQfrac pq :=
  PQ_of_pair ((PQnum1 pq + 1) mod (PQden1 pq + 1)) (PQden1 pq + 1).
Definition PQintg pq :=
  (PQnum1 pq + 1) / (PQden1 pq + 1).
