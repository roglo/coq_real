(* Implementation of rationals using only nat *)
(* Not convincing... e.g. addition associativity is complicated to prove,
   although it was simple in QArith. *)

Require Import Utf8 Arith.

Require Import Misc.

Delimit Scope MQ_scope with MQ.

Record MQ := MQmake { MQsign : bool; MQnum : nat; MQden : nat }.
Arguments MQsign x%MQ : rename.
Arguments MQnum x%MQ : rename.
Arguments MQden x%MQ : rename.

Definition nd x y := MQnum x * MQden y.

Definition MQadd_sign x y :=
  if Bool.eqb (MQsign x) (MQsign y) then MQsign x
  else if MQsign x then Nat.leb (nd y x) (nd x y)
  else Nat.leb (nd x y) (nd y x).

Definition diff x y := max x y - min x y.
Definition MQadd_num x y :=
  if Bool.eqb (MQsign x) (MQsign y) then nd x y + nd y x
  else diff (nd y x) (nd x y).

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
  else if Bool.eqb (MQsign x) (MQsign y) then nd x y = nd y x
  else False.

Definition MQabs x := MQmake true (MQnum x) (MQden x).
Definition MQabs_lt x y := nd x y < nd y x.
Definition MQabs_le x y := nd x y ≤ nd y x.

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
   ++unfold nd in Hxy, Hyz |-*.
     rewrite Nat.mul_assoc, Nat.mul_shuffle0, Hyz.
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
unfold diff.
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
unfold nd; rewrite MQnum_add_comm in H1 |-*.
rewrite MQden_add_comm.
destruct (zerop (MQnum (y + x))) as [H2| H2]; [ now rewrite H2 in H1 | ].
rewrite MQsign_add_comm.
now rewrite Bool.eqb_reflx.
Qed.

Theorem fold_nd x y : MQnum x * MQden y = nd x y.
Proof. easy. Qed.

Theorem eq_diff_0 : ∀ x y, diff x y = 0 → x = y.
Proof.
intros * H.
unfold diff in H.
apply Nat.sub_0_le in H.
destruct (le_dec y x) as [H1| H1].
-rewrite Nat.max_l in H; [ | easy ].
 rewrite Nat.min_r in H; [ | easy ].
 now apply le_antisym.
-apply Nat.nle_gt in H1.
 rewrite Nat.max_r in H; [ | now apply Nat.lt_le_incl ].
 rewrite Nat.min_l in H; [ | now apply Nat.lt_le_incl ].
 now apply Nat.nle_gt in H1.
Qed.

Theorem diff_max_r : ∀ x y, x ≤ y → diff x y = y - x.
Proof.
intros * H.
unfold diff.
rewrite Nat.max_r; [ | easy ].
rewrite Nat.min_l; [ | easy ].
easy.
Qed.

Theorem diff_id : ∀ x, diff x x = 0.
Proof.
intros.
unfold diff.
rewrite Nat.max_id, Nat.min_id.
apply Nat.sub_diag.
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
-unfold nd; simpl.
 do 4 rewrite fold_nd.
 do 6 rewrite Nat.mul_assoc.
 do 2 rewrite fold_nd.
 destruct (zerop
   ((nd x y + nd y x) * MQden z + nd z x * MQden y +
    (nd x y * MQden z + (nd y z + nd z y) * MQden x))) as [| H1]; [ easy | ].
 destruct (zerop ((nd x y + nd y x) * MQden z + nd z x * MQden y)) as [H2| H2].
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
 +destruct (zerop (nd x y * MQden z + (nd y z + nd z y) * MQden x))
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
   (diff (nd z x * MQden y) ((nd x y + nd y x) * MQden z) +
    (if if nd z y <=? nd y z then true else false
     then nd x y * MQden z + diff (nd z y) (nd y z) * MQden x
     else diff (diff (nd z y) (nd y z) * MQden x) (nd x y * MQden z))))
   as [H1| H1]; [ easy | ].
 destruct (zerop (diff (nd z x * MQden y) ((nd x y + nd y x) * MQden z)))
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
    remember (nd z y * MQden x) as t eqn:Ht.
    rewrite <- fold_nd, Nat.mul_shuffle0, fold_nd in Ht; subst t.
    rewrite H2, Nat.mul_add_distr_r in H1.
    rewrite Nat.sub_add_distr in H1.
    rewrite Nat_sub_sub_swap in H1.
    remember (nd y z * MQden x) as t eqn:Ht.
    rewrite <- fold_nd, Nat.mul_shuffle0, fold_nd in Ht; subst t.
    rewrite Nat.sub_diag, Nat.sub_0_l, Nat.add_0_r in H1.
    rewrite Nat.mul_add_distr_r in H2.
    remember (nd z x * MQden y) as t eqn:Ht.
    rewrite <- fold_nd, Nat.mul_shuffle0, fold_nd in Ht; subst t.
    remember (nd y x * MQden z) as t eqn:Ht.
    rewrite <- fold_nd, Nat.mul_shuffle0, fold_nd in Ht; subst t.
    rewrite Nat.add_comm in H2.
    apply plus_minus in H2.
    rewrite <- Nat.mul_sub_distr_r in H2.
...
