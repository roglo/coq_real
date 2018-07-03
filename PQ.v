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

Definition if_PQlt_le {A} (P Q : A) x y := if PQlt_le_dec x y then P else Q.
Arguments if_PQlt_le _ _ _ x%PQ y%PQ.

Notation "'if_PQlt_le_dec' x y 'then' P 'else' Q" :=
  (if_PQlt_le P Q x y) (at level 200, x at level 9, y at level 9).

Theorem PQlt_le_if : ∀ {A} (P Q : A) x y,
  (if PQlt_le_dec x y then P else Q) = @if_PQlt_le A P Q x y.
Proof. easy. Qed.

(* allows to use rewrite inside a if_PQlt_le_dec ...
   through PQlt_le_if, e.g.
      H : (x = y)%PQ
      ====================
      ... if_PQlt_le_dec x z then P else Q ...
   > rewrite H.
      ====================
      ... if_PQlt_le_dec y z then P else Q ...
 *)
Instance PQeq_PQlt_le_morph {P Q} :
  Proper (PQeq ==> PQeq ==> iff) (λ x y, if PQlt_le_dec x y then P else Q).
Proof.
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
destruct (PQlt_le_dec x1 y1) as [H1| H1]; rewrite Hx, Hy in H1.
-destruct (PQlt_le_dec x2 y2) as [| H2]; [ easy | ].
 now apply PQnlt_ge in H2.
-destruct (PQlt_le_dec x2 y2) as [H2| ]; [ | easy ].
 now apply PQnlt_ge in H2.
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

(* Notice that some theorems work with Leibnitz equalities
   (therefore with "=="); it is the case when these equalities
   hold the same variables at the right and left part of the
   equlity (e.g (x+y)+z=x+(y+z), but not x+y-y=x) *)

(* Leibnitz equality applies *)
Theorem PQadd_comm : ∀ x y, (x + y)%PQ = (y + x)%PQ.
Proof.
intros.
unfold "+"%PQ; f_equal.
-now unfold PQadd_num1, nd; rewrite Nat.add_comm.
-now unfold PQadd_den1, nd; rewrite Nat.mul_comm.
Qed.

(* Leibnitz equality applies *)
Theorem PQadd_add_comm : ∀ x y z, (x + y + z)%PQ = (x + z + y)%PQ.
Proof.
intros; PQtac1.
repeat PQtac2; [ | simpl; flia | simpl; flia ].
PQtac3; f_equal; [ | f_equal; apply Nat.mul_shuffle0 ].
f_equal.
rewrite Nat.add_shuffle0.
f_equal; f_equal.
apply Nat.mul_shuffle0.
Qed.

(* Leibnitz equality applies *)
Theorem PQadd_assoc : ∀ x y z, ((x + y) + z)%PQ = (x + (y + z))%PQ.
Proof.
intros.
symmetry.
rewrite PQadd_comm.
remember (x + y)%PQ as t eqn:Ht.
rewrite PQadd_comm in Ht; subst t.
apply PQadd_add_comm.
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
unfold "≤"%PQ, "+"%PQ, PQadd_num1, PQadd_den1, nd; simpl.
intros *.
do 12 rewrite Nat.add_1_r.
intros Hxy Hzt.
do 4 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 4 rewrite Nat.sub_succ, Nat.sub_0_r.
do 2 rewrite Nat.mul_add_distr_r.
remember (S (PQnum1 x)) as xn eqn:Hxn.
remember (S (PQden1 x)) as xd eqn:Hxd.
remember (S (PQnum1 y)) as yn eqn:Hyn.
remember (S (PQden1 y)) as yd eqn:Hyd.
remember (S (PQnum1 z)) as zn eqn:Hzn.
remember (S (PQden1 z)) as zd eqn:Hzd.
remember (S (PQnum1 t)) as tn eqn:Htn.
remember (S (PQden1 t)) as td eqn:Htd.
move Hxy before Hzt.
apply Nat.add_le_mono.
-replace (xn * zd * (yd * td)) with (xn * yd * (td * zd)) by flia.
 replace (yn * td * (xd * zd)) with (yn * xd * (td * zd)) by flia.
 now apply Nat.mul_le_mono_r.
-replace (zn * xd * (yd * td)) with (zn * td * (xd * yd)) by flia.
 replace (tn * yd * (xd * zd)) with (tn * zd * (xd * yd)) by flia.
 now apply Nat.mul_le_mono_r.
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

Theorem PQadd_sub : ∀ x y, (x + y - y == x)%PQ.
Proof.
intros x y.
unfold "+"%PQ, "-"%PQ, "==", nd; simpl.
unfold PQsub_num1, PQadd_num1, PQadd_den1, nd; simpl.
do 8 rewrite Nat.add_1_r.
rewrite <- Nat.sub_succ_l.
-rewrite Nat.sub_succ, Nat.sub_0_r.
 do 3 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
 do 3 rewrite Nat.sub_succ, Nat.sub_0_r.
 rewrite Nat.mul_assoc, Nat.mul_add_distr_r, Nat.add_sub; flia.
-do 2 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
 do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
 rewrite Nat.mul_add_distr_r, Nat.mul_assoc, Nat.add_sub; simpl; flia.
Qed.

Theorem PQsub_add : ∀ x y, (y < x)%PQ → (x - y + y == x)%PQ.
Proof.
intros x y Hxy.
unfold "<"%PQ, nd in Hxy.
unfold "+"%PQ, "-"%PQ, "==", nd; simpl.
unfold PQsub_num1, PQadd_num1, PQadd_den1, nd; simpl.
do 4 rewrite Nat.add_1_r in Hxy.
do 8 rewrite Nat.add_1_r.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite Nat.sub_succ, Nat.sub_0_r.
do 2 (rewrite <- Nat.sub_succ_l; [ | flia Hxy ]).
do 2 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 2 (rewrite Nat.sub_succ, Nat.sub_0_r).
do 3 rewrite Nat.mul_assoc.
rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
rewrite Nat.mul_sub_distr_r.
remember (S (PQnum1 y) * S (PQden1 x) * S (PQden1 y)) as u.
rewrite Nat_sub_sub_swap.
rewrite Nat.sub_add; [ rewrite Nat.mul_sub_distr_r; lia | subst u ].
replace (S (PQden1 y)) with (1 * S (PQden1 y)) by flia.
do 3 rewrite Nat.mul_1_l at 1.
rewrite <- Nat.mul_sub_distr_r.
apply Nat.mul_le_mono_r.
rewrite Nat.sub_succ, Nat.sub_0_r.
now apply Nat.lt_le_incl.
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

(* Leibnitz equality applies *)
Theorem PQsub_add_distr : ∀ x y z,
  (y < x)%PQ → (x - (y + z))%PQ = (x - y - z)%PQ.
Proof.
intros * Hyx.
revert Hyx; PQtac1; intros.
repeat PQtac2; PQtac3; [ f_equal; flia | flia Hyx | simpl; flia ].
Qed.

(* Leibnitz equality applies *)
Theorem PQsub_sub_swap : ∀ x y z,
  (y < x)%PQ → (z < x)%PQ → (x - y - z)%PQ = (x - z - y)%PQ.
Proof.
intros * Hyx Hzx.
rewrite <- PQsub_add_distr; [ | easy ].
rewrite <- PQsub_add_distr; [ now rewrite PQadd_comm | easy ].
Qed.

(* Leibnitz equality applies *)
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

(* Leibnitz equality applies *)
Theorem PQadd_sub_assoc: ∀ x y z,
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

Theorem PQadd_cancel_l : ∀ x y z, (z + x == z + y ↔ x == y)%PQ.
Proof.
intros.
split; intros H; [ | now rewrite H ].
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
now apply Nat.mul_cancel_r in H.
Qed.

(* multiplication, inversion, division *)

Definition PQmul_num1 x y := (PQnum1 x + 1) * (PQnum1 y + 1) - 1.
Definition PQmul_den1 x y := (PQden1 x + 1) * (PQden1 y + 1) - 1.

Definition PQmul x y := PQmake (PQmul_num1 x y) (PQmul_den1 x y).
Arguments PQmul x%PQ y%PQ.

Definition PQinv x := PQmake (PQden1 x) (PQnum1 x).

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

Theorem PQmul_comm : ∀ x y, (x * y == y * x)%PQ.
Proof.
intros.
unfold "==", "*"%PQ, nd; f_equal; simpl.
-unfold PQmul_num1; f_equal; f_equal.
 apply Nat.mul_comm.
-unfold PQmul_den1; f_equal; f_equal.
 apply Nat.mul_comm.
Qed.

Theorem PQmul_assoc : ∀ x y z, ((x * y) * z == x * (y * z))%PQ.
Proof.
intros.
unfold "==", "*"%PQ, nd; f_equal; simpl.
-unfold PQmul_num1; simpl.
 do 7 rewrite Nat.add_1_r.
 do 4 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
 do 4 rewrite Nat.sub_succ, Nat.sub_0_r.
 symmetry; apply Nat.mul_assoc.
-unfold PQmul_den1; simpl.
 do 7 rewrite Nat.add_1_r.
 do 4 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
 do 4 rewrite Nat.sub_succ, Nat.sub_0_r.
 apply Nat.mul_assoc.
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

Theorem PQmul_add_distr_l : ∀ x y z, (x * (y + z) == x * y + x * z)%PQ.
Proof.
intros.
unfold "==", "*"%PQ, "+"%PQ, nd; simpl.
unfold PQmul_num1, PQadd_den1, PQadd_num1, PQmul_den1, nd; simpl.
do 16 rewrite Nat.add_1_r.
do 10 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 10 rewrite Nat.sub_succ, Nat.sub_0_r.
ring.
Qed.

Theorem PQinv_involutive: ∀ x, (/ / x == x)%PQ.
Proof. easy. Qed.

Ltac PQcompare_iff :=
  match goal with
  | [ H : PQcompare _ _ = Eq |- _ ] => apply PQcompare_eq_iff in H
  | [ H : PQcompare _ _ = Lt |- _ ] => apply PQcompare_lt_iff in H
  | [ H : PQcompare _ _ = Gt |- _ ] => apply PQcompare_gt_iff in H
  end.

Theorem PQcompare_comm : ∀ {A} {a b c : A} px py,
  match PQcompare px py with
  | Eq => a
  | Lt => b
  | Gt => c
  end =
  match PQcompare py px with
  | Eq => a
  | Lt => c
  | Gt => b
  end.
Proof.
intros.
remember (PQcompare px py) as b1 eqn:Hb1; symmetry in Hb1.
remember (PQcompare py px) as b2 eqn:Hb2; symmetry in Hb2.
move b2 before b1.
destruct b1, b2; try easy; repeat PQcompare_iff.
-now rewrite Hb1 in Hb2; apply PQlt_irrefl in Hb2.
-now rewrite Hb1 in Hb2; apply PQlt_irrefl in Hb2.
-now rewrite Hb2 in Hb1; apply PQlt_irrefl in Hb1.
-now apply PQnle_gt in Hb2; exfalso; apply Hb2; apply PQlt_le_incl.
-now rewrite Hb2 in Hb1; apply PQlt_irrefl in Hb1.
-now apply PQnle_gt in Hb2; exfalso; apply Hb2; apply PQlt_le_incl.
Qed.
