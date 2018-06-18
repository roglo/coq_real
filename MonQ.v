(* Implementation of positive rationals using only nat *)

Require Import Utf8 Arith Morphisms Psatz.
Require Import Misc.

Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Delimit Scope PQ_scope with PQ.

Record PQ := PQmake { PQnum : nat; PQden1 : nat }.
Arguments PQnum x%PQ : rename.
Arguments PQden1 x%PQ : rename.

Notation "0" := (PQmake 0 1) : PQ_scope.

Definition nd x y := PQnum x * S (PQden1 y).

(* equality *)

Definition PQeq x y := nd x y = nd y x.

Notation "x == y" := (PQeq x y) (at level 70) : PQ_scope.

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

(* lt le *)

Definition PQlt x y := nd x y < nd y x.
Definition PQle x y := nd x y ≤ nd y x.

Notation "x < y" := (PQlt x y) : PQ_scope.
Notation "x ≤ y" := (PQle x y) : PQ_scope.
Notation "x > y" := (¬ PQle x y) : PQ_scope.
Notation "x ≥ y" := (¬ PQlt x y) : PQ_scope.

Theorem PQnlt_ge : ∀ x y, ¬ (x < y)%PQ ↔ (y ≤ x)%PQ.
Proof.
intros.
split; intros H; [ now apply Nat.nlt_ge in H | ].
now apply Nat.nlt_ge.
Qed.

Theorem PQlt_le_dec : ∀ x y : PQ, {(x < y)%PQ} + {(y ≤ x)%PQ}.
Proof.
intros (xn, xd) (yn, yd).
unfold PQlt, PQle, nd; simpl.
destruct (lt_dec (xn * S yd) (yn * S xd)) as [H1| H1]; [ now left | ].
now right; apply Nat.nlt_ge.
Qed.
Arguments PQlt_le_dec x%PQ y%PQ.

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

Theorem PQlt_irrefl : ∀ x, (¬ x < x)%PQ.
Proof. intros x; apply Nat.lt_irrefl. Qed.

Theorem PQlt_le_incl : ∀ x y, (x < y)%PQ → (x ≤ y)%PQ.
Proof. intros * Hxy; now apply Nat.lt_le_incl. Qed.

Theorem PQle_0_l : ∀ x, (0 ≤ x)%PQ.
Proof. intros; apply Nat.le_0_l. Qed.

Theorem PQnlt_0_r : ∀ x, (¬ x < 0)%PQ.
Proof. intros; apply Nat.nlt_0_r. Qed.

Theorem PQadd_0_l : ∀ x, (0 + x == x)%PQ.
Proof.
intros x.
unfold "=="%PQ, "+"%PQ, nd; simpl.
unfold PQadd_num, PQadd_den1, nd; simpl.
rewrite Nat.add_0_r, Nat.sub_0_r.
rewrite <- Nat.mul_assoc; f_equal; simpl.
now rewrite Nat.add_0_r.
Qed.

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
rewrite Nat.mul_add_distr_r.
...

Theorem PQadd_lt_mono_r : ∀ n m p, (n < m)%PQ ↔ (n + p < m + p)%PQ.
...

Theorem PQsub_0_le : ∀ n m, (n - m == 0)%PQ ↔ (n ≤ m)%PQ.
...

Theorem PQle_lt_trans : ∀ n m p, (n ≤ m)%PQ → (m < p)%PQ → (n < p)%PQ.
...

Theorem PQadd_le_mono : ∀ n m p q,
  (n ≤ m)%PQ → (p ≤ q)%PQ → (n + p ≤ m + q)%PQ.
...

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

...

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
    **simpl.
      rewrite PQadd_comm.
      apply PQsub_add_distr.
    **exfalso.
      apply PQnlt_ge in H3; apply H3; clear H3.
...
      now apply PQlt_add_lt_sub_r.
