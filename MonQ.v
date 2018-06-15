Require Import Utf8.
Require Import Arith.

Delimit Scope MQ_scope with MQ.

Record MQ := MQmake { MQsign : bool; MQnum : nat; MQden : nat }.
Arguments MQsign x%MQ : rename.
Arguments MQnum x%MQ : rename.
Arguments MQden x%MQ : rename.

Definition MQadd_sign x y :=
  if MQsign x then
    if MQsign y then true
    else if lt_dec (MQnum x * MQden y) (MQnum y * MQden x) then false
    else true
  else if MQsign y then
    if lt_dec (MQnum x * MQden y) (MQnum y * MQden x) then true
    else false
   else false.

Definition MQadd_num x y :=
  if MQsign x then
    if MQsign y then MQnum x * MQden y + MQnum y * MQden x
    else if lt_dec (MQnum x * MQden y) (MQnum y * MQden x) then
      MQnum y * MQden x - MQnum x * MQden y
    else
      MQnum x * MQden y - MQnum y * MQden x
  else if MQsign y then
    if lt_dec (MQnum x * MQden y) (MQnum y * MQden x) then
      MQnum y * MQden x - MQnum x * MQden y
    else
      MQnum x * MQden y - MQnum y * MQden x
  else MQnum x * MQden y + MQnum y * MQden x.
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
  if zerop (MQnum x) then
    if zerop (MQnum y) then True else False
  else if zerop (MQnum y) then False
  else if MQsign x then
    if MQsign y then MQnum x * MQden y = MQnum y * MQden x else False
  else
    if MQsign y then False else MQnum x * MQden y = MQnum y * MQden x.

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
destruct (zerop (MQnum x)) as [H1| H1]; [ easy | ].
now destruct (MQsign x).
Qed.

Theorem MQeq_symm : ∀ x y : MQ, (x == y)%MQ → (y == x)%MQ.
Proof.
intros x y Hxy.
unfold "==" in Hxy |-*.
destruct (zerop (MQnum x)) as [H1| H1].
-now destruct (zerop (MQnum y)).
-destruct (zerop (MQnum y)) as [H2| H2]; [ easy | ].
 remember (MQsign x) as sx eqn:Hsx; symmetry in Hsx.
 remember (MQsign y) as sy eqn:Hsy; symmetry in Hsy.
 move sy before sx.
 now destruct sx, sy.
Qed.

Theorem MQeq_trans : ∀ x y z : MQ, (x == y)%MQ → (y == z)%MQ → (x == z)%MQ.
Proof.
unfold "==".
intros * Hxy Hyz.
destruct (zerop (MQnum x)) as [H1| H1].
-now destruct (zerop (MQnum y)).
-destruct (zerop (MQnum y)) as [H2| H2]; [ easy | ].
 +destruct (zerop (MQnum z)) as [H3| H3]; [ easy | ].
  remember (MQsign x) as sx eqn:Hsx; symmetry in Hsx.
  remember (MQsign y) as sy eqn:Hsy; symmetry in Hsy.
  remember (MQsign z) as sz eqn:Hsz; symmetry in Hsz.
  move sy before sx; move sz before sy.
  move Hsz before Hsy.
  move H3 before H2.
  destruct sx.
  *destruct sy; [ | easy ].
   destruct sz; [ | easy ].
   apply (Nat.mul_cancel_l _ _ (MQnum y)).
  --now intros H; rewrite H in H2.
  --rewrite Nat.mul_assoc, Nat.mul_shuffle0, Hyz.
    rewrite Nat.mul_shuffle0, <- Nat.mul_assoc, Hxy.
    rewrite Nat.mul_comm, Nat.mul_shuffle0.
    symmetry; apply Nat.mul_assoc.
  *destruct sy; [ easy | ].
   destruct sz; [ easy | ].
   apply (Nat.mul_cancel_l _ _ (MQnum y)).
  --now intros H; rewrite H in H2.
  --rewrite Nat.mul_assoc, Nat.mul_shuffle0, Hyz.
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
