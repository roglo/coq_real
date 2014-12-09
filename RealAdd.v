Require Import Utf8 QArith NPeano.
Require Import Real01Add.

Set Implicit Arguments.

Open Scope Z_scope.

Record real := mkre { re_int : Z; re_frac : real_mod_1 }.
Arguments mkre _%Z _%rm.

Delimit Scope R_scope with R.
Arguments re_int _%R.
Arguments re_frac _%R.

Definition b2z (b : bool) := if b then 1 else 0.

Definition re_add x y :=
  {| re_int := re_int x + re_int y + b2z (carry (re_frac x) (re_frac y) 0);
     re_frac := rm_add (re_frac x) (re_frac y) |}.
Arguments re_add x%R y%R.

Definition re_zero := {| re_int := 0; re_frac := rm_zero |}.

Notation "x + y" := (re_add x y) : R_scope.
Notation "0" := re_zero : R_scope.

Definition re_norm x :=
  {| re_int := re_int x + b2z (carry (re_frac x) 0 0);
     re_frac := (re_frac x + 0)%rm |}.
Arguments re_norm x%R.

Definition re_eq x y :=
  re_int (re_norm x) = re_int (re_norm y) ∧
  (re_frac x = re_frac y)%rm.
Arguments re_eq x%R y%R.

Definition is_all_0 x :=
  match fst_same x rm_ones 0 with
  | Some _ => false
  | None => true
  end.

Definition re_opp x :=
  if is_all_0 (re_frac x) then {| re_int := - re_int x; re_frac := 0%rm |}
  else {| re_int := - re_int x - 1; re_frac := - re_frac x |}.
Definition re_sub x y := re_add x (re_opp y).
Arguments re_opp x%R.
Arguments re_sub x%R y%R.

Notation "x = y" := (re_eq x y) : R_scope.
Notation "x ≠ y" := (¬ re_eq x y) : R_scope.
Notation "- x" := (re_opp x) : R_scope.
Notation "x - y" := (re_sub x y) : R_scope.

(* equality is equivalence relation *)

Theorem re_eq_refl : reflexive _ re_eq.
Proof.
intros x; split; reflexivity.
Qed.

Theorem re_eq_sym : symmetric _ re_eq.
Proof.
intros x y Hxy.
unfold re_eq in Hxy; unfold re_eq.
destruct Hxy; split; symmetry; assumption.
Qed.

Theorem re_eq_trans : transitive _ re_eq.
Proof.
intros x y z Hxy Hyz.
destruct Hxy, Hyz.
unfold re_eq.
split; etransitivity; eassumption.
Qed.

Add Parametric Relation : _ re_eq
 reflexivity proved by re_eq_refl
 symmetry proved by re_eq_sym
 transitivity proved by re_eq_trans
 as re_rel.

(* commutativity *)

Theorem re_add_comm : ∀ x y, (x + y = y + x)%R.
Proof.
intros x y.
unfold re_eq.
unfold re_add; simpl; split; [ idtac | apply rm_add_comm ].
f_equal; [ idtac | rewrite carry_comm_l; reflexivity ].
rewrite carry_comm; f_equal.
apply Z.add_comm.
Qed.

(* neutral element *)

Theorem carry_norm_add_0_r : ∀ x, carry (x + 0%rm) 0 0 = false.
Proof.
intros x.
unfold carry; simpl.
remember (fst_same (x + 0%rm) 0 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [j| ].
 destruct Hs as (_, Hs); rewrite Hs; reflexivity.

 pose proof (not_rm_add_0_inf_1 x 0) as H.
 contradiction.
Qed.

Theorem re_add_0_r : ∀ x, (x + 0 = x)%R.
Proof.
intros x.
unfold re_eq.
unfold re_add; simpl; split; [ idtac | apply rm_add_0_r ].
rewrite Z.add_0_r.
rewrite <- Z.add_assoc; f_equal.
rewrite carry_norm_add_0_r, Z.add_0_r.
reflexivity.
Qed.

(* opposite *)

Theorem re_sub_diag : ∀ x, (x - x = 0)%R.
Proof.
intros x.
unfold re_eq, re_sub, re_opp; simpl.
remember (is_all_0 (re_frac x)) as z eqn:Hz .
symmetry in Hz.
destruct z; simpl.
 unfold re_add; simpl.
 rewrite Z.add_opp_r, Z.sub_diag, Z.add_0_l.
 split.
  rewrite carry_norm_add_0_r, Z.add_0_r.
  unfold carry; simpl.
  rewrite fst_same_diag.
  unfold is_all_0 in Hz.
  remember (fst_same (re_frac x) 0 0) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [di1| ].
   destruct Hs1 as (_, Hs1).
   rewrite Hs1; reflexivity.

   remember (fst_same (re_frac x) rm_ones 0) as s2 eqn:Hs2 .
   destruct s2 as [di2| ]; [ discriminate Hz | clear Hz ].
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   pose proof (Hs1 O) as H.
   rewrite Hs2 in H; discriminate H.

  unfold is_all_0 in Hz.
  remember (fst_same (re_frac x) rm_ones 0) as s2 eqn:Hs2 .
  destruct s2 as [j2| ]; [ discriminate Hz | clear Hz ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  rewrite rm_add_0_r.
  unfold rm_eq; intros i; simpl.
  unfold rm_add_i; simpl.
  unfold carry; simpl.
  rewrite fst_same_diag.
  remember (fst_same (re_frac x) 0 (S i)) as s1 eqn:Hs1 .
  destruct s1 as [dj1| ]; [ do 2 rewrite Hs2; reflexivity | idtac ].
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  pose proof (Hs1 O) as H.
  rewrite Hs2 in H; discriminate H.

 split; [ idtac | rewrite fold_rm_sub, rm_sub_diag; reflexivity ].
 unfold carry; simpl.
 rewrite fst_same_diag.
 rewrite fold_rm_sub.
 rewrite Z.add_sub_assoc, Z.add_opp_r, Z.sub_diag.
 remember (fst_same (re_frac x) (- re_frac x) 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [j1| ].
  destruct Hs1 as (Hn1, Hs1).
  symmetry in Hs1.
  exfalso; revert Hs1; apply no_fixpoint_negb.

  clear Hs1.
  remember (fst_same (re_frac x - re_frac x) 0 0) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s2 as [j2| ].
   destruct Hs2 as (Hn2, Hs2).
   rewrite Hs2; reflexivity.

   pose proof (Hs2 O) as H.
   unfold rm_add_i in H; simpl in H.
   unfold carry in H; simpl in H.
   remember (fst_same (re_frac x) (- re_frac x) 1) as s3 eqn:Hs3 .
   destruct s3 as [dj3| ].
    apply fst_same_sym_iff in Hs3; simpl in Hs3.
    destruct Hs3 as (Hn3, Hs3).
    symmetry in Hs3.
    exfalso; revert Hs3; apply no_fixpoint_negb.

    rewrite negb_xorb_diag_r in H.
    discriminate H.
Qed.

(* associativity for normalised reals *)

Theorem re_add_assoc_norm : ∀ x y z,
  (re_norm x + (re_norm y + re_norm z) =
   (re_norm x + re_norm y) + re_norm z)%R.
Proof.
intros x y z.
rename x into x0; rename y into y0; rename z into z0.
remember (re_norm x0) as x.
remember (re_norm y0) as y.
remember (re_norm z0) as z.
unfold re_eq; simpl.
split; [ idtac | apply rm_add_assoc ].
subst x y z; simpl.
remember (re_frac x0) as x.
remember (re_frac y0) as y.
remember (re_frac z0) as z.
remember (re_int x0) as xi.
remember (re_int y0) as yi.
remember (re_int z0) as zi.
rename x0 into x1; rename y0 into y1; rename z0 into z1.
rename x into x0; rename y into y0; rename z into z0.
remember (x0 + 0)%rm as x.
remember (y0 + 0)%rm as y.
remember (z0 + 0)%rm as z.
remember (carry (x + (y + z))%rm 0%rm (0)) as c1 eqn:Hc1 .
remember (carry (x + y + z)%rm 0%rm (0)) as c2 eqn:Hc2 .
remember (carry x (y + z)%rm (0)) as c3 eqn:Hc3 .
remember (carry (x + y)%rm z (0)) as c4 eqn:Hc4 .
remember (carry y z (0)) as c5 eqn:Hc5 .
remember (carry x y (0)) as c6 eqn:Hc6 .
symmetry in Hc1, Hc2, Hc3, Hc4, Hc5, Hc6.
move c2 before c1; move c3 before c2.
move c4 before c3; move c5 before c4.
move c6 before c5.
remember Hc1 as H; clear HeqH.
erewrite carry_sum_3_norm_assoc_r in H; try eassumption.
move H at top; subst c1.
remember Hc2 as H; clear HeqH.
erewrite carry_sum_3_norm_assoc_l in H; try eassumption.
move H at top; subst c2.
simpl; do 2 rewrite Z.add_0_r.
do 12 rewrite <- Z.add_assoc.
do 4 f_equal.
symmetry; rewrite Z.add_comm.
do 2 rewrite <- Z.add_assoc.
do 2 f_equal.
destruct c3, c4, c5, c6; try reflexivity; exfalso.
 eapply case_1; eassumption.

 rewrite carry_comm_l in Hc4.
 eapply case_1; rewrite carry_comm; eassumption.

 eapply case_3; eassumption.

 eapply case_1; eassumption.

 eapply case_3; eassumption.

 rewrite carry_comm, carry_comm_l in Hc3.
 rewrite carry_comm, carry_comm_r in Hc4.
 rewrite carry_comm in Hc5, Hc6.
 eapply case_3; try eassumption.

 rewrite carry_comm_l in Hc4.
 eapply case_1; rewrite carry_comm; eassumption.

 rewrite carry_comm, carry_comm_l in Hc3.
 rewrite carry_comm, carry_comm_r in Hc4.
 rewrite carry_comm in Hc5, Hc6.
 eapply case_3; eassumption.

 clear Hc1 Hc2.
 eapply case_2; eassumption.

 rewrite carry_comm_r in Hc3.
 eapply case_2; rewrite carry_comm; eassumption.
Qed.

(* compatibility with equality *)

Theorem zzz : ∀ x y i,
  (x = y)%rm
  → x.[i] = true
  → y.[i] = false
  → (∀ di, x.[i+di] = true) ∧ (∀ di, y.[i+di] = false) ∨
    (∀ di, x.[i+S di] = false) ∧ (∀ di, y.[i+S di] = true).
Proof.
intros x y i Hxy Hx Hy.
unfold rm_eq in Hxy; simpl in Hxy.
pose proof (Hxy i) as H.
unfold rm_add_i in H; simpl in H.
rewrite Hx, Hy, xorb_true_l, xorb_false_l in H.
unfold carry in H; simpl in H.
remember (fst_same x 0 (S i)) as sx eqn:Hsx .
remember (fst_same y 0 (S i)) as sy eqn:Hsy .
destruct sx as [dx| ].
 remember Hsx as HH; clear HeqHH.
 apply fst_same_sym_iff in HH; simpl in HH.
 destruct HH as (Hnx, Htx); rewrite Htx in H.
 destruct sy as [dy| ]; [ idtac | clear H ].
  remember Hsy as HH; clear HeqHH.
  apply fst_same_sym_iff in HH; simpl in HH.
  destruct HH as (Hny, Hty).
  rewrite Hty in H; discriminate H.

  right.
  remember Hsy as Hny; clear HeqHny.
  apply fst_same_sym_iff in Hny; simpl in Hny.
  split; intros di.
   destruct (lt_eq_lt_dec di dx) as [[H1| H1]| H1].
    pose proof (Hnx di H1) as H.
    rename H into Hdi.
    destruct dx; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
    pose proof (Hxy (S (i + dx))%nat) as H.
    unfold rm_add_i in H; simpl in H.
    do 2 rewrite xorb_false_r in H.
    rewrite Hnx in H; [ idtac | apply Nat.lt_succ_diag_r ].
    rewrite Hny in H.
    rewrite xorb_true_l in H.
    symmetry in H.
    rewrite xorb_true_l in H.
    apply negb_sym in H.
    rewrite negb_involutive in H.
    rewrite <- Nat.add_succ_l in H.
    symmetry in Hsx.
    erewrite carry_before_relay in H; [ idtac | eassumption | auto ].
    symmetry in Hsy.
    simpl in H.
    do 2 rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay in H; [ idtac | assumption ].
    simpl in H; rewrite Htx in H; discriminate H.

    subst di.
    rewrite Nat.add_succ_r; assumption.

bbb.
    pose proof (Hxy (S (i + dx)%nat)) as H.
    unfold rm_add_i in H; simpl in H.
    do 2 rewrite xorb_false_r in H.
    rewrite Htx, Hny, xorb_false_l, xorb_true_l in H.
    unfold carry in H at 1; simpl in H.
    rewrite <- Nat.add_succ_l in H.
    symmetry in Hsy.
    rewrite carry_before_inf_relay in H; [ idtac | assumption ].
    remember (fst_same x 0 (S (S i + dx))) as s1 eqn:Hs1 .
    destruct s1 as [di1| ]; [ idtac | discriminate H ].
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    destruct Hs1 as (Hn1, Hs1); clear H.
bbb.

intros x y i Hxy Hx Hy.
unfold rm_eq in Hxy; simpl in Hxy.
pose proof (Hxy i) as H.
unfold rm_add_i in H; simpl in H.
do 2 rewrite xorb_false_r in H.
rewrite Hx, Hy, xorb_true_l, xorb_false_l in H.
remember (carry x 0 (S i)) as c1 eqn:Hc1 .
rename H into Hc2; symmetry in Hc1, Hc2.
destruct c1; simpl in Hc2.
 left.
 unfold carry in Hc1; simpl in Hc1.
 remember (fst_same x 0 (S i)) as sx eqn:Hsx .
 destruct sx as [dx| ]; [ idtac | clear Hc1 ].
  apply fst_same_sym_iff in Hsx; simpl in Hsx.
  destruct Hsx as (_, H); rewrite Hc1 in H; discriminate H.

  remember Hsx as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  rename H into Hnx.
  unfold carry in Hc2; simpl in Hc2.
  remember (fst_same y 0 (S i)) as sy eqn:Hsy .
  destruct sy as [dy| ]; [ idtac | discriminate Hc2 ].
  remember Hsy as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hny, _).
  split; intros di.
   destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
   rewrite Nat.add_succ_r; apply Hnx.

   destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
   pose proof (Hxy i) as H.
   unfold rm_add_i in H; simpl in H.
   do 2 rewrite xorb_false_r in H.
   rewrite Hx, Hy, xorb_true_l, xorb_false_l in H.
   replace i with (i + 0)%nat in H by apply Nat.add_0_r.
   rewrite carry_before_inf_relay in H.
bbb.
*)

Theorem re_add_compat_r : ∀ x y z, (x = y)%R → (x + z = y + z)%R.
Proof.
intros x y z Hxy.
unfold re_eq in Hxy; simpl in Hxy.
destruct Hxy as (Hi, Hf).
unfold re_eq; simpl.
split; [ idtac | rewrite Hf; reflexivity ].
do 4 rewrite <- Z.add_assoc.
rewrite Z.add_comm; symmetry.
rewrite Z.add_comm; symmetry.
do 4 rewrite <- Z.add_assoc.
f_equal.
remember (re_frac x) as X.
remember (re_frac y) as Y.
remember (re_frac z) as Z.
remember (re_int x) as XI.
remember (re_int y) as YI.
clear x y z HeqX HeqY HeqXI HeqYI HeqZ.
move Z before Y.
rename X into x; rename Y into y; rename Z into z.
rename XI into a; rename YI into b.
do 2 rewrite Z.add_assoc.
unfold carry in Hi; simpl in Hi.
remember (fst_same x 0 0) as sx eqn:Hsx .
remember (fst_same y 0 0) as sy eqn:Hsy .
remember (carry x z 0) as c1 eqn:Hc1 .
remember (carry (x + z) 0 0) as c2 eqn:Hc2 .
remember (carry y z 0) as c3 eqn:Hc3 .
remember (carry (y + z) 0 0) as c4 eqn:Hc4 .
symmetry in Hc1, Hc2, Hc3, Hc4.
destruct sx as [dx| ].
 remember Hsx as H; clear HeqH.
 apply fst_same_sym_iff in H; simpl in H.
 destruct H as (Hnx, Htx); rewrite Htx, Z.add_0_r in Hi.
 destruct sy as [dy| ].
  remember Hsy as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hny, Hty); rewrite Hty, Z.add_0_r in Hi.
  subst b; f_equal.
  unfold rm_eq in Hf; simpl in Hf.
  destruct c1, c2, c3, c4; simpl; try reflexivity; exfalso.
   rewrite carry_comm in Hc2.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsx; reflexivity.

   rewrite carry_comm in Hc2.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsx; reflexivity.

   rewrite carry_comm in Hc2.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsx; reflexivity.

   rewrite carry_comm in Hc4.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsy; reflexivity.

   Focus 2.
   rewrite carry_comm in Hc4.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsy; reflexivity.

   eapply case_2; try eassumption.
   unfold carry; simpl.
   remember (fst_same z 0 0) as sz eqn:Hsz .
   destruct sz as [dz| ]; [ idtac | reflexivity ].
   remember Hsz as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hnz, Htz); exfalso.
   unfold carry in Hc1; simpl in Hc1.
   remember (fst_same x z 0) as s1 eqn:Hs1 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   unfold carry in Hc2; simpl in Hc2.
   remember (fst_same (x + z) 0 0) as s2 eqn:Hs2 .
   destruct s2 as [dj2| ]; [ idtac | discriminate Hc2 ].
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hs2, _).
   destruct s1 as [dj1| ].
    destruct Hs1 as (Hn1, Hs1).
    rewrite Hc1 in Hs1; symmetry in Hs1.
    destruct dj1; [ clear Hn1 | idtac ].
     destruct dx; [ rewrite Hc1 in Htx; discriminate Htx | idtac ].
     destruct dz; [ rewrite Hs1 in Htz; discriminate Htz | idtac ].
     destruct dy; [ clear Hny | idtac ].
      unfold carry in Hc3; simpl in Hc3.
      remember (fst_same y z 0) as s3 eqn:Hs3 .
      destruct s3 as [dj3| ]; [ idtac | discriminate Hc3 ].
      apply fst_same_sym_iff in Hs3; simpl in Hs3.
      destruct Hs3 as (Hn3, Hs3).
      rewrite Hc3 in Hs3; symmetry in Hs3.
      destruct dj3; [ rewrite Hs1 in Hs3; discriminate Hs3 | idtac ].
      pose proof (Hf O) as H.
      unfold rm_add_i in H; simpl in H.
      do 2 rewrite xorb_false_r in H.
      rewrite Hc1, Hty, xorb_true_l, xorb_false_l in H.
bbb.

Theorem rm_add_compat : ∀ x y z d,
  (x = y)%R
  → (z = t)%R
  → (x + z = y + t)%R
Proof.
intros x y z t Hxy Hzt.
bbb.

Close Scope Z_scope.
