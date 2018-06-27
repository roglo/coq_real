(* Implementation of positive rationals using only nat *)

Require Import Utf8 Arith Morphisms Psatz.
Require Import Misc.

Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Delimit Scope PQ_scope with PQ.

Record PQ := PQmake { PQnum : nat; PQden1 : nat }.
Arguments PQmake _%nat _%nat.
Arguments PQnum x%PQ : rename.
Arguments PQden1 x%PQ : rename.

Notation "0" := (PQmake 0 0) : PQ_scope.
Notation "1" := (PQmake 1 0) : PQ_scope.

Definition nd x y := PQnum x * S (PQden1 y).

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

Notation "x < y" := (PQlt x y) : PQ_scope.
Notation "x ≤ y" := (PQle x y) : PQ_scope.
Notation "x > y" := (¬ PQle x y) : PQ_scope.
Notation "x ≥ y" := (¬ PQlt x y) : PQ_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%PQ (at level 70, y at next level) :
  PQ_scope.

Theorem PQle_refl : ∀ x, (x ≤ x)%PQ.
Proof. now unfold "≤"%PQ. Qed.

Theorem PQneq_0_lt_0 : ∀ x, (x ≠≠ 0 ↔ 0 < x)%PQ.
Proof.
unfold "=="%PQ, "<"%PQ, nd; simpl.
intros; split; intros H; flia H.
Qed.

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
destruct (lt_dec (xn * S yd) (yn * S xd)) as [H1| H1]; [ now left | ].
now right; apply Nat.nlt_ge.
Qed.
Arguments PQlt_le_dec x%PQ y%PQ.

Theorem PQle_lt_dec : ∀ x y : PQ, {(x ≤ y)%PQ} + {(y < x)%PQ}.
Proof.
intros (xn, xd) (yn, yd).
unfold PQlt, PQle, nd; simpl.
destruct (le_dec (xn * S yd) (yn * S xd)) as [H1| H1]; [ now left | ].
now right; apply Nat.nle_gt.
Qed.
Arguments PQle_lt_dec x%PQ y%PQ.

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
  intros * Hx Hy Hxy.
  unfold "<"%PQ, nd in Hxy |-*.
  unfold "=="%PQ, nd in Hx, Hy.
  destruct x1 as (x1n, x1d).
  destruct x2 as (x2n, x2d).
  destruct y1 as (y1n, y1d).
  destruct y2 as (y2n, y2d).
  remember S as f; simpl in *; subst f.
  remember (S x1d) as u.
  assert (Hx1 : 0 < u) by flia Hequ.
  clear x1d Hequ; rename u into x1d.
  remember (S x2d) as u.
  assert (Hx2 : 0 < u) by flia Hequ.
  clear x2d Hequ; rename u into x2d.
  remember (S y1d) as u.
  assert (Hy1 : 0 < u) by flia Hequ.
  clear y1d Hequ; rename u into y1d.
  remember (S y2d) as u.
  assert (Hy2 : 0 < u) by flia Hequ.
  clear y2d Hequ; rename u into y2d.
  move x1d before y2n; move x2d before x1d.
  move Hx at bottom; move Hy at bottom.
  move Hxy at bottom.
  apply (Nat.mul_lt_mono_pos_r x1d); [ easy | ].
  rewrite Nat.mul_shuffle0, <- Hx.
  setoid_rewrite Nat.mul_shuffle0.
  apply Nat.mul_lt_mono_pos_r; [ easy | ].
  apply (Nat.mul_lt_mono_pos_r y1d); [ easy | ].
  remember (x1n * y2d) as u.
  rewrite Nat.mul_shuffle0; subst u.
  rewrite <- Hy.
  setoid_rewrite Nat.mul_shuffle0.
  now apply Nat.mul_lt_mono_pos_r.
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
  intros * Hx Hy Hxy.
  unfold "≤"%PQ, nd in Hxy |-*.
  unfold "=="%PQ, nd in Hx, Hy.
  destruct x1 as (x1n, x1d).
  destruct x2 as (x2n, x2d).
  destruct y1 as (y1n, y1d).
  destruct y2 as (y2n, y2d).
  remember S as f; simpl in *; subst f.
  remember (S x1d) as u.
  assert (Hx1 : 0 < u) by flia Hequ.
  clear x1d Hequ; rename u into x1d.
  remember (S x2d) as u.
  assert (Hx2 : 0 < u) by flia Hequ.
  clear x2d Hequ; rename u into x2d.
  remember (S y1d) as u.
  assert (Hy1 : 0 < u) by flia Hequ.
  clear y1d Hequ; rename u into y1d.
  remember (S y2d) as u.
  assert (Hy2 : 0 < u) by flia Hequ.
  clear y2d Hequ; rename u into y2d.
  move x1d before y2n; move x2d before x1d.
  move Hx at bottom; move Hy at bottom.
  move Hxy at bottom.
  apply (Nat.mul_le_mono_pos_r _ _ x1d); [ easy | ].
  rewrite Nat.mul_shuffle0, <- Hx.
  setoid_rewrite Nat.mul_shuffle0.
  apply Nat.mul_le_mono_pos_r; [ easy | ].
  apply (Nat.mul_le_mono_pos_r _ _ y1d); [ easy | ].
  remember (x1n * y2d) as u.
  rewrite Nat.mul_shuffle0; subst u.
  rewrite <- Hy.
  setoid_rewrite Nat.mul_shuffle0.
  now apply Nat.mul_le_mono_pos_r.
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

Theorem PQgt_lt_iff : ∀ x y, (x > y)%PQ ↔ (y < x)%PQ.
Proof.
intros.
split; intros H; now apply Nat.nle_gt in H.
Qed.

(* addition, subtraction *)

Definition PQadd_num x y := nd x y + nd y x.
Definition PQsub_num x y := nd x y - nd y x.
Definition PQadd_den1 x y := S (PQden1 x) * S (PQden1 y) - 1.

Definition PQadd x y := PQmake (PQadd_num x y) (PQadd_den1 x y).
Definition PQsub x y := PQmake (PQsub_num x y) (PQadd_den1 x y).
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
intros x1 x2 Hx y1 y2 Hy.
move Hx before Hy.
unfold "+"%PQ.
unfold "==", nd in Hx, Hy |-*; simpl.
unfold PQadd_num, PQadd_den1, nd.
destruct x1 as (x1n, x1d).
destruct x2 as (x2n, x2d).
destruct y1 as (y1n, y1d).
destruct y2 as (y2n, y2d).
remember S as f; simpl in *; subst f.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
remember (S x1d) as u.
assert (Hx1 : 0 < u) by flia Hequ.
clear x1d Hequ; rename u into x1d.
remember (S x2d) as u.
assert (Hx2 : 0 < u) by flia Hequ.
clear x2d Hequ; rename u into x2d.
remember (S y1d) as u.
assert (Hy1 : 0 < u) by flia Hequ.
clear y1d Hequ; rename u into y1d.
remember (S y2d) as u.
assert (Hy2 : 0 < u) by flia Hequ.
clear y2d Hequ; rename u into y2d.
move x1d before y2n; move x2d before x1d.
move Hx at bottom; move Hy at bottom.
ring_simplify.
replace (x1n * y1d * x2d) with (x1n * x2d * y1d) by flia.
rewrite Hx.
replace (y1n * x1d * x2d * y2d) with (y1n * y2d * x1d * x2d) by flia.
rewrite Hy.
ring.
Qed.

(* allows to use rewrite inside a subtraction
   e.g.
      H : x = y
      ====================
      ..... (x - z)%PQ ....
   rewrite H.
 *)
Instance PQsub_morph : Proper (PQeq ==> PQeq ==> PQeq) PQsub.
Proof.
intros x1 x2 Hx y1 y2 Hy.
move Hx before Hy.
unfold "-"%PQ.
unfold "==", nd in Hx, Hy |-*; simpl.
unfold PQsub_num, PQadd_den1, nd.
destruct x1 as (x1n, x1d).
destruct x2 as (x2n, x2d).
destruct y1 as (y1n, y1d).
destruct y2 as (y2n, y2d).
remember S as f; simpl in *; subst f.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
remember (S x1d) as u.
assert (Hx1 : 0 < u) by flia Hequ.
clear x1d Hequ; rename u into x1d.
remember (S x2d) as u.
assert (Hx2 : 0 < u) by flia Hequ.
clear x2d Hequ; rename u into x2d.
remember (S y1d) as u.
assert (Hy1 : 0 < u) by flia Hequ.
clear y1d Hequ; rename u into y1d.
remember (S y2d) as u.
assert (Hy2 : 0 < u) by flia Hequ.
clear y2d Hequ; rename u into y2d.
move x1d before y2n; move x2d before x1d.
move Hx at bottom; move Hy at bottom.
ring_simplify.
do 4 rewrite Nat.mul_sub_distr_r.
replace (x1n * y1d * x2d) with (x1n * x2d * y1d) by flia.
rewrite Hx.
replace (y1n * x1d * x2d * y2d) with (y1n * y2d * x1d * x2d) by flia.
rewrite Hy.
f_equal; ring.
Qed.

Theorem PQadd_comm : ∀ x y, (x + y == y + x)%PQ.
Proof.
intros.
unfold "==".
assert (PQnum_add_comm : ∀ x y, PQnum (x + y) = PQnum (y + x)). {
  intros; apply Nat.add_comm.
}
assert (PQden1_add_comm : ∀ x y, PQden1 (x + y) = PQden1 (y + x)). {
  intros.
  unfold PQadd; simpl.
  unfold PQadd_den1.
  now rewrite Nat.mul_comm.
}
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

Theorem PQadd_0_l : ∀ x, (0 + x == x)%PQ.
Proof.
intros x.
unfold "=="%PQ, "+"%PQ, nd; simpl.
unfold PQadd_num, PQadd_den1, nd; simpl.
rewrite Nat.add_0_r, Nat.sub_0_r.
rewrite <- Nat.mul_assoc; f_equal; simpl.
now rewrite Nat.add_0_r.
Qed.

Theorem PQadd_0_r : ∀ x, (x + 0 == x)%PQ.
Proof.
intros x.
rewrite PQadd_comm.
apply PQadd_0_l.
Qed.

Theorem PQsub_0_r : ∀ x, (x - 0 == x)%PQ.
Proof.
intros x.
unfold "=="%PQ, "-"%PQ, nd; simpl.
unfold PQsub_num, PQadd_den1, nd; simpl.
now do 2 rewrite Nat.sub_0_r, Nat.mul_1_r.
Qed.

(* *)

Theorem PQeq_add_0 : ∀ x y, (x + y == 0 ↔ x == 0 ∧ y == 0)%PQ.
Proof.
intros.
unfold "==", nd; simpl.
do 3 rewrite Nat.mul_1_r.
unfold PQadd_num, nd.
split; intros H.
-apply Nat.eq_add_0 in H.
 destruct H as (H1, H2).
 apply Nat.eq_mul_0_l in H1; [ | easy ].
 apply Nat.eq_mul_0_l in H2; [ | easy ].
 easy.
-now rewrite (proj1 H), (proj2 H).
Qed.

Theorem PQeq_num_0 : ∀ x, PQnum x = 0 ↔ (x == 0)%PQ.
Proof.
intros.
unfold "==", nd; simpl.
now rewrite Nat.mul_1_r.
Qed.

Theorem PQsub_add_distr : ∀ x y z, (x - (y + z) == x - y - z)%PQ.
Proof.
intros.
unfold "==", nd; simpl.
f_equal.
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
-f_equal.
 unfold PQadd_den1; simpl.
 unfold PQadd_den1; simpl.
 do 4 rewrite Nat.sub_0_r.
 ring.
Qed.

Theorem PQadd_sub_assoc : ∀ x y z,
  (z ≤ y)%PQ → (x + (y - z) == x + y - z)%PQ.
Proof.
intros * Hzy.
unfold "==", nd; simpl.
f_equal.
-unfold PQsub_num, nd; simpl.
 unfold PQsub_num, PQadd_num, nd; simpl.
 unfold PQadd_den1.
 unfold "≤"%PQ, nd in Hzy; simpl in Hzy.
 unfold PQsub_num, PQadd_den1, nd.
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
 destruct x as (xn, xd).
 destruct y as (yn, yd).
 destruct z as (zn, zd).
 remember S as f; simpl in *; subst f.
 rewrite Nat.mul_add_distr_r.
 rewrite Nat.mul_sub_distr_r.
 do 2 rewrite Nat.mul_assoc.
 rewrite Nat.add_sub_assoc; [ flia | ].
 now apply Nat.mul_le_mono_r.
-f_equal.
 unfold PQadd_den1; simpl.
 unfold PQadd_den1; simpl.
 do 4 rewrite Nat.sub_0_r.
 ring.
Qed.

Theorem PQsub_sub_assoc : ∀ x y z,
  (z ≤ y ≤ x + z)%PQ → (x - (y - z) == x + z - y)%PQ.
Proof.
intros * (Hzy, Hyx).
unfold "==", nd; simpl.
f_equal.
-unfold PQsub_num, nd; simpl.
 unfold PQsub_num, PQadd_num, nd; simpl.
 unfold PQadd_den1.
 unfold "≤"%PQ, nd in Hzy, Hyx; simpl in Hzy, Hyx.
 unfold PQadd_num, PQadd_den1, nd in Hzy, Hyx.
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
 rewrite <- Nat.sub_succ_l in Hyx; [ | simpl; flia ].
 do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
 rewrite Nat.sub_succ, Nat.sub_0_r in Hyx.
 destruct x as (xn, xd).
 destruct y as (yn, yd).
 destruct z as (zn, zd).
 remember S as f; simpl in *; subst f.
 rewrite Nat.mul_add_distr_r.
 rewrite Nat.mul_sub_distr_r.
 do 2 rewrite Nat.mul_assoc.
 rewrite Nat_sub_sub_assoc; [ flia | ].
 split; [ now apply Nat.mul_le_mono_r | flia Hyx ].
-f_equal.
 unfold PQadd_den1; simpl.
 unfold PQadd_den1; simpl.
 do 4 rewrite Nat.sub_0_r.
 ring.
Qed.

Theorem PQlt_irrefl : ∀ x, (¬ x < x)%PQ.
Proof. intros x; apply Nat.lt_irrefl. Qed.

Theorem PQlt_le_incl : ∀ x y, (x < y)%PQ → (x ≤ y)%PQ.
Proof. intros * Hxy; now apply Nat.lt_le_incl. Qed.

Theorem PQle_0_l : ∀ x, (0 ≤ x)%PQ.
Proof. intros; apply Nat.le_0_l. Qed.

Theorem PQnlt_0_r : ∀ x, (¬ x < 0)%PQ.
Proof. intros; apply Nat.nlt_0_r. Qed.

Theorem PQsub_add : ∀ x y, (x ≤ y)%PQ → (y - x + x == y)%PQ.
Proof.
intros x y Hxy.
unfold "=="%PQ, nd; simpl.
unfold "≤"%PQ, nd in Hxy.
unfold "-"%PQ, PQadd_num, PQadd_den1, PQsub_num, nd.
destruct x as (xn, xd).
destruct y as (yn, yd).
remember S as f; simpl in Hxy |-*; subst f.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
remember (S xd) as u.
assert (Hx : 0 < u) by flia Hequ.
clear xd Hequ; rename u into xd.
remember (S yd) as u.
assert (Hy : 0 < u) by flia Hequ.
clear yd Hequ; rename u into yd.
move Hxy at bottom.
do 3 rewrite Nat.mul_assoc.
rewrite <- Nat.mul_add_distr_r.
replace (yn * yd * xd * xd) with (yn * xd * xd * yd) by flia.
f_equal; f_equal; lia.
Qed.

Theorem PQle_trans : ∀ x y z, (x ≤ y)%PQ → (y ≤ z)%PQ → (x ≤ z)%PQ.
Proof.
intros * Hxy Hyz.
unfold "≤"%PQ, nd in Hxy, Hyz |-*.
apply (Nat.mul_le_mono_pos_r _ _ (S (PQden1 y))); [ flia | ].
rewrite Nat.mul_shuffle0.
apply (Nat.le_trans _ (PQnum y * S (PQden1 x) * S (PQden1 z))).
-apply Nat.mul_le_mono_pos_r; [ flia | easy ].
-setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_le_mono_pos_r; [ flia | easy ].
Qed.

Theorem PQlt_trans : ∀ x y z, (x < y)%PQ → (y < z)%PQ → (x < z)%PQ.
Proof.
intros * Hxy Hyz.
unfold "<"%PQ, nd in Hxy, Hyz |-*.
apply (Nat.mul_lt_mono_pos_r (S (PQden1 y))); [ flia | ].
rewrite Nat.mul_shuffle0.
apply (Nat.lt_trans _ (PQnum y * S (PQden1 x) * S (PQden1 z))).
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
apply (Nat.mul_lt_mono_pos_r (S (PQden1 y))); [ flia | ].
rewrite Nat.mul_shuffle0.
apply (Nat.le_lt_trans _ (PQnum y * S (PQden1 x) * S (PQden1 z))).
-apply Nat.mul_le_mono_pos_r; [ flia | easy ].
-setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
Qed.

Theorem PQlt_le_trans : ∀ x y z, (x < y)%PQ → (y ≤ z)%PQ → (x < z)%PQ.
Proof.
intros * Hxy Hyz.
unfold "<"%PQ, nd in Hxy |-*.
unfold "≤"%PQ, nd in Hyz.
apply (Nat.mul_lt_mono_pos_r (S (PQden1 y))); [ flia | ].
rewrite Nat.mul_shuffle0.
apply (Nat.lt_le_trans _ (PQnum y * S (PQden1 x) * S (PQden1 z))).
-apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
-setoid_rewrite Nat.mul_shuffle0.
 apply Nat.mul_le_mono_pos_r; [ flia | easy ].
Qed.

Theorem PQadd_lt_mono_r : ∀ x y z, (x < y)%PQ ↔ (x + z < y + z)%PQ.
Proof.
unfold "<"%PQ, "+"%PQ, PQadd_num, PQadd_den1, nd.
remember S as f; simpl; subst f.
intros *.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
do 2 rewrite Nat.mul_assoc.
split; intros H.
-apply Nat.mul_lt_mono_pos_r; [ flia | ].
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
