Require Import Utf8.
Require Import Arith.

Delimit Scope MQ_scope with MQ.

Record MQ := MQmake { MQsign : bool; MQnum : nat; MQden : nat }.
Arguments MQsign x%MQ : rename.
Arguments MQnum x%MQ : rename.
Arguments MQden x%MQ : rename.

Definition MQadd_sign x y :=
  if Bool.eqb (MQsign x) (MQsign y) then MQsign x
  else if MQsign x then
    Nat.leb (MQnum y * MQden x) (MQnum x * MQden y)
  else
    Nat.leb (MQnum x * MQden y) (MQnum y * MQden x).

Definition MQadd_num x y :=
  if Bool.eqb (MQsign x) (MQsign y) then
    MQnum x * MQden y + MQnum y * MQden x
  else
    max (MQnum y * MQden x) (MQnum x * MQden y) -
    min (MQnum y * MQden x) (MQnum x * MQden y).

Definition MQadd_den x y := MQden x * MQden y.

Definition MQadd x y :=
  MQmake (MQadd_sign x y) (MQadd_num x y) (MQadd_den x y).

Definition MQopp x := MQmake (negb (MQsign x)) (MQnum x) (MQden x).

Arguments MQadd x%MQ y%MQ.
Arguments MQopp x%MQ.

(* MQeq syntax is "==".
   ∀ x y
   * 0/x == 0/y == -0/x == -0/y
   * x/0 == y/0, -x/0 == -y/0
   * x/0 ≠≠ -y/0, -x/0 ≠≠ y/0
   otherwise ∀ xn xd yn yd, xn*yd = xd*yn
 *)
Definition MQeq x y :=
  if zerop (MQnum x + MQnum y) then True
  else if zerop (MQnum x) then False
  else if zerop (MQnum y) then False
  else if Bool.eqb (MQsign x) (MQsign y) then
    MQnum x * MQden y = MQnum y * MQden x
  else False.

Definition MQabs x := MQmake true (MQnum x) (MQden x).
Definition MQabs_lt x y := MQnum x * MQden y < MQnum y * MQden x.
Definition MQabs_le x y := MQnum x * MQden y ≤ MQnum y * MQden x.

Definition MQlt x y :=
  if MQsign x then
    if MQsign y then MQabs_lt x y else False
  else
    if MQsign y then True else MQabs_lt y x.
Definition MQle x y :=
  if MQsign x then
    if MQsign y then MQabs_le x y else False
  else
    if MQsign y then True else MQabs_le y x.

Notation "0" := (MQmake true 0 1) : MQ_scope.
Notation "- x" := (MQopp x) : MQ_scope.
Notation "x == y" := (MQeq x y) (at level 70) : MQ_scope.
Notation "x + y" := (MQadd x y) : MQ_scope.
Notation "x - y" := (MQadd x (MQopp y)) : MQ_scope.
Notation "x < y" := (MQlt x y) : MQ_scope.
Notation "x ≤ y" := (MQle x y) : MQ_scope.
Notation "x > y" := (¬ MQle x y) : MQ_scope.
Notation "x ≥ y" := (¬ MQlt x y) : MQ_scope.

Theorem MQeq_refl : ∀ x : MQ, (x == x)%MQ.
Proof.
intros.
unfold "==".
destruct (zerop (MQnum x + MQnum x)) as [| H1]; [ easy | ].
destruct (zerop (MQnum x)) as [H2| H2].
-now rewrite H2 in H1.
-now rewrite Bool.eqb_reflx.
Qed.

Theorem Bool_eqb_comm : ∀ b1 b2, Bool.eqb b1 b2 = Bool.eqb b2 b1.
Proof.
intros.
unfold Bool.eqb.
now destruct b1, b2.
Qed.

Theorem MQeq_symm : ∀ x y : MQ, (x == y)%MQ → (y == x)%MQ.
Proof.
intros x y Hxy.
unfold "==" in Hxy |-*.
rewrite Nat.add_comm.
destruct (zerop (MQnum x + MQnum y)) as [| H1]; [ easy | ].
destruct (zerop (MQnum x)) as [| H2]; [ easy | ].
destruct (zerop (MQnum y)) as [H3| H3]; [ easy | ].
rewrite Bool_eqb_comm.
now destruct (Bool.eqb (MQsign x) (MQsign y)).
Qed.

Theorem MQeq_trans : ∀ x y z : MQ, (x == y)%MQ → (y == z)%MQ → (x == z)%MQ.
Proof.
unfold "==".
intros * Hxy Hyz.
destruct (zerop (MQnum x + MQnum z)) as [| Hxz]; [ easy | ].
destruct (zerop (MQnum x)) as [Hx| Hx].
-rewrite Hx in Hxy, Hxz; simpl in Hxy, Hxz.
 destruct (zerop (MQnum y)) as [Hy |]; [ | easy ].
 destruct (zerop (MQnum y + MQnum z)) as [Hz| ]; [ | easy ].
 rewrite Hy in Hz; simpl in Hz.
 now rewrite Hz in Hxz.
-destruct (zerop (MQnum z)) as [Hz| Hz].
 +rewrite Hz, Nat.add_0_r in Hyz, Hxz.
  destruct (zerop (MQnum y)) as [Hy| ]; [ | easy ].
  rewrite Hy, Nat.add_0_r in Hxy.
  destruct (zerop (MQnum x)) as [H| ]; [ | easy ].
  now rewrite H in Hx.
 +destruct (zerop (MQnum x + MQnum y)) as [Hzxy| Hzxy].
  *now destruct (MQnum x).
  *destruct (zerop (MQnum y)) as [| Hy]; [ easy | ].
   destruct (zerop (MQnum y + MQnum z)) as [Hzyz| Hzyz].
  --apply Nat.eq_add_0 in Hzyz.
    destruct Hzyz as (H1, H2).
    now rewrite H1 in Hy.
  --remember (Bool.eqb (MQsign x) (MQsign y)) as b eqn:Hb.
    symmetry in Hb.
    destruct b; [ | easy ].
    apply -> Bool.eqb_true_iff in Hb; rewrite Hb; clear Hb.
    remember (Bool.eqb (MQsign y) (MQsign z)) as b eqn:Hb.
    symmetry in Hb.
    destruct b; [ clear Hb | easy ].
    move Hxy at bottom; move Hyz at bottom.
    apply (Nat.mul_cancel_l _ _ (MQnum y)).
   ++now intros H; rewrite H in Hy.
   ++rewrite Nat.mul_assoc, Nat.mul_shuffle0, Hyz.
     rewrite Nat.mul_shuffle0, <- Nat.mul_assoc, Hxy.
     rewrite Nat.mul_comm, Nat.mul_shuffle0.
     symmetry; apply Nat.mul_assoc.
Qed.

Add Parametric Relation : _ MQeq
 reflexivity proved by MQeq_refl
 symmetry proved by MQeq_symm
 transitivity proved by MQeq_trans
 as MQeq_equiv_rel.

Theorem MQlt_le_dec : ∀ x y : MQ, {(x < y)%MQ} + {(y ≤ x)%MQ}.
Proof.
intros (xs, xn, xd) (ys, yn, yd).
unfold MQlt, MQle, MQabs_lt, MQabs_le; simpl.
destruct xs, ys.
-destruct (lt_dec (xn * yd) (yn * xd)) as [H1| H1]; [ now left | ].
 now right; apply Nat.nlt_ge.
-now right.
-now left.
-destruct (lt_dec (yn * xd) (xn * yd)) as [H1| H1]; [ now left | ].
 now right; apply Nat.nlt_ge.
Qed.

Theorem MQsign_add_comm : ∀ x y, MQsign (x + y) = MQsign (y + x).
Proof.
intros.
unfold MQadd, MQadd_sign; simpl.
rewrite Bool_eqb_comm.
remember (Bool.eqb (MQsign y) (MQsign x)) as b eqn:Hb.
symmetry in Hb.
destruct b; [ now apply -> Bool.eqb_true_iff in Hb | ].
apply Bool.eqb_false_iff in Hb.
now destruct (MQsign x); destruct (MQsign y).
Qed.

Theorem MQnum_add_comm : ∀ x y, MQnum (x + y) = MQnum (y + x).
Proof.
intros.
unfold MQadd, MQadd_num; simpl.
rewrite Bool_eqb_comm.
rewrite Nat.add_comm.
now rewrite Nat.max_comm, Nat.min_comm.
Qed.

Theorem MQden_add_comm : ∀ x y, MQden (x + y) = MQden (y + x).
Proof.
intros.
unfold MQadd, MQadd_den; simpl.
apply Nat.mul_comm.
Qed.

Theorem MQadd_comm : ∀ x y, (x + y == y + x)%MQ.
Proof.
intros.
unfold "==".
destruct (zerop (MQnum (x + y) + MQnum (y + x))) as [| H1]; [ easy | ].
rewrite MQnum_add_comm in H1 |-*.
rewrite MQden_add_comm.
destruct (zerop (MQnum (y + x))) as [H2| H2]; [ now rewrite H2 in H1 | ].
rewrite MQsign_add_comm.
now rewrite Bool.eqb_reflx.
Qed.

Theorem MQadd_assoc : ∀ x y z, ((x + y) + z == x + (y + z))%MQ.
Proof.
intros.
unfold "==".
unfold MQadd; simpl.
unfold MQadd_sign; simpl.
unfold MQadd_num; simpl.
unfold MQadd_den; simpl.
remember (MQsign x) as sx eqn:Hsx; symmetry in Hsx.
remember (MQsign y) as sy eqn:Hsy; symmetry in Hsy.
remember (MQsign z) as sz eqn:Hsz; symmetry in Hsz.
move sy before sx; move sz before sy.
destruct sx, sy, sz; simpl.
...
