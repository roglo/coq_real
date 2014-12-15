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

Definition re_opp x := {| re_int := - re_int x - 1; re_frac := - re_frac x |}.
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

(*
Record real2 (sh : nat) := { re_sign : bool; re_mant : real_mod_1 }.

Definition rm_shift_1_r b x :=
  {| rm i := match i with O => b | S j => x.[j] end |}.

Fixpoint re_to_rm_loop sh xi xf :=
  match sh with
  | O => xf
  | S sh1 =>
      re_to_rm_loop sh1 (xi / 2)%nat
         (rm_shift_1_r (if zerop (xi mod 2) then false else true) xf)
  end.

Fixpoint rm_to_ri_loop sh x acc :=
  match sh with
  | O => acc
  | S sh1 =>
      rm_to_ri_loop sh1 (rm_shift_l 1 x)
        (2 * acc + if x.[0] then 1 else 0)%nat
   end.

Definition re_to_re2 sh x : real2 sh :=
  {| re_sign := Z.geb (re_int x) 0;
     re_mant := re_to_rm_loop sh (Z.abs_nat (re_int x)) (re_frac x) |}.

Definition re2_to_re sh (x : real2 sh) :=
  let n := rm_to_ri_loop sh (re_mant x) O in
  {| re_int := if re_sign x then Z.of_nat n else - Z.of_nat n;
     re_frac := rm_shift_l sh (re_mant x) |}.

Definition re2_norm sh (x : real2 sh) :=
  ...

Definition re2_eq sh (x y : real2 sh) :=
  re_sign (re2_norm x) = re_sign (re2_norm y) ∧
  (re_mant (re2_norm x) = re_mant (re2_norm y))%rm.

Theorem zzz : ∀ x y sh,
  (x = y)%R
  → re2_eq (re_to_re2 sh x) (re_to_re2 sh y).
Proof.
intros x y sh Hxy.
unfold re2_eq; simpl.
split.
 unfold re_eq in Hxy; simpl in Hxy.
 destruct Hxy as (Hi, Hf).
 remember (re_int x) as xi eqn:Hxi .
 remember (re_int y) as yi eqn:Hyi .
 symmetry in Hxi, Hyi.
 destruct xi as [| xi| xi].
  destruct yi as [| yi| yi]; try reflexivity.
  rewrite Z.add_0_l in Hi.
  remember (carry (re_frac x) 0 0) as xb eqn:Hxb .
  remember (carry (re_frac y) 0 0) as yb eqn:Hyb .
  symmetry in Hxb, Hyb.
  symmetry in Hi.
  apply Z.add_move_r in Hi.
  destruct xb.
   destruct yb; simpl in Hi.
    pose proof (Pos2Z.neg_is_neg yi) as H.
    rewrite Hi in H; exfalso; revert H; apply Z.lt_irrefl.

    pose proof (Pos2Z.neg_is_neg yi) as H.
    rewrite Hi in H.
    apply Z.nle_gt in H.
    exfalso; apply H; apply Z.le_0_1.

   destruct yb; simpl in Hi.
    unfold rm_eq in Hf; simpl in Hf.
    unfold carry in Hyb.
    remember (fst_same (re_frac y) 0 0) as sy eqn:Hsy .
    destruct sy as [dy| ].
     apply fst_same_sym_iff in Hsy; simpl in Hsy.
     destruct Hsy as (_, Hsy).
     simpl in Hyb; rewrite Hsy in Hyb; discriminate Hyb.

     clear Hyb.
     apply fst_same_sym_iff in Hsy; simpl in Hsy.
bbb.
*)

Theorem rm_eq_neq_if : ∀ x y i,
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
    erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
    symmetry in Hsy.
    simpl in H.
    do 2 rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
    simpl in H; rewrite Htx in H; discriminate H.

    subst di.
    rewrite Nat.add_succ_r; assumption.

    remember (di - S dx)%nat as n eqn:Hn .
    apply nat_sub_add_r in Hn; [ idtac | assumption ].
    subst di; clear H1.
    rewrite Nat.add_succ_r.
    induction n as (n, IHn) using all_lt_all.
    destruct n.
     rewrite Nat.add_succ_r.
     rewrite <- negb_involutive.
     apply neq_negb; simpl; intros Hdi.
     rewrite Nat.add_0_r in Hdi.
     pose proof (Hxy (S (i + dx))) as H.
     unfold rm_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite Htx, Hny, xorb_false_l, xorb_true_l in H.
     symmetry in H, Hsx, Hsy.
     rewrite <- Nat.add_succ_l in H.
     rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
     symmetry in H.
     unfold carry in H; simpl in H.
     remember (fst_same x 0 (S (S (i + dx)))) as s1 eqn:Hs1 .
     destruct s1 as [di1| ]; [ idtac | discriminate H ].
     rename H into Hx1.
     destruct di1.
      rewrite Nat.add_0_r, <- Nat.add_succ_r in Hx1.
      rewrite Hdi in Hx1; discriminate Hx1.

      remember Hs1 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn1, _).
      pose proof (Hxy (S (S (i + dx)))) as H.
      unfold rm_add_i in H; simpl in H.
      do 2 rewrite xorb_false_r in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hdi, Hny, xorb_true_l in H.
      apply negb_sym in H.
      rewrite negb_involutive in H.
      rewrite <- Nat.add_succ_l in H.
      rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
      symmetry in H, Hs1.
      replace dx with (dx + 0)%nat in H by apply Nat.add_0_r.
      simpl in H.
      rewrite Nat.add_succ_r, Nat.add_assoc in H.
      do 2 rewrite <- Nat.add_succ_l in H.
      assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H.
      rewrite Hx1 in H; discriminate H.

     rewrite Nat.add_succ_r.
     rewrite <- negb_involutive.
     apply neq_negb; simpl; intros Hdi.
     pose proof (Hxy (S (i + dx + S n))) as H.
     unfold rm_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite IHn in H; [ idtac | apply Nat.lt_succ_diag_r ].
     rewrite Hny, xorb_false_l, xorb_true_l in H.
     symmetry in H, Hsx, Hsy.
     rewrite <- Nat.add_succ_l in H.
     rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
     symmetry in H.
     unfold carry in H; simpl in H.
     remember (fst_same x 0 (S (S (i + (dx + S n))))) as s1 eqn:Hs1 .
     destruct s1 as [di1| ]; [ idtac | discriminate H ].
     rename H into Hx1.
     destruct di1.
      rewrite Nat.add_0_r, <- Nat.add_succ_r in Hx1.
      rewrite Hdi in Hx1; discriminate Hx1.

      remember Hs1 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn1, _).
      pose proof (Hxy (S (S (i + dx + S n)))) as H.
      unfold rm_add_i in H; simpl in H.
      do 2 rewrite xorb_false_r in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Nat.add_assoc in H.
      rewrite Nat.add_succ_r in H.
      rewrite Hdi, Hny, xorb_true_l in H.
      apply negb_sym in H.
      rewrite negb_involutive in H.
      rewrite <- Nat.add_succ_l in H.
      rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
      symmetry in H, Hs1.
      remember (S i + S (dx + S n))%nat as z.
      replace (S z) with (S z + 0)%nat in H by apply Nat.add_0_r.
      subst z.
      rewrite <- Nat.add_succ_l in H; simpl in H.
      rewrite <- Nat.add_succ_l in H.
      rewrite <- Nat.add_succ_r in Hs1.
      assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H.
      do 4 rewrite Nat.add_succ_r in H.
      do 3 rewrite Nat.add_succ_r in Hx1.
      simpl in H.
      rewrite Nat.add_assoc in Hx1.
      simpl in Hx1.
      rewrite Nat.add_assoc in H.
      rewrite Hx1 in H; discriminate H.

   rewrite Nat.add_succ_r; simpl; apply Hny.

 destruct sy as [dy| ]; [ idtac | discriminate H ].
 symmetry in H; simpl in H.
 remember Hsy as HH; clear HeqHH.
 apply fst_same_sym_iff in HH; simpl in HH.
 destruct HH as (Hny, Hty); clear H.
 left.
 remember Hsx as Hnx; clear HeqHnx.
 apply fst_same_sym_iff in Hnx; simpl in Hnx.
 split; intros di.
  destruct (lt_eq_lt_dec di dy) as [[H1| H1]| H1].
   pose proof (Hny di H1) as H.
   destruct dy; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
   rename H into Hdi.
   pose proof (Hxy (S (i + dy))%nat) as H.
   unfold rm_add_i in H; simpl in H.
   do 2 rewrite xorb_false_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite xorb_true_l in H.
   apply negb_sym in H.
   rewrite negb_involutive in H.
   rewrite <- Nat.add_succ_l in H.
   symmetry in Hsy.
   erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
   symmetry in Hsx.
   rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
   simpl in H; rewrite Hty in H; discriminate H.

   subst di.
   destruct dy; [ rewrite Nat.add_0_r; assumption | idtac ].
   rewrite Nat.add_succ_r; apply Hnx.

   destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
   rewrite Nat.add_succ_r; apply Hnx.

  destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
  rewrite Nat.add_succ_r.
  destruct (lt_eq_lt_dec di dy) as [[H1| H1]| H1].
   pose proof (Hny di H1) as H.
   destruct dy; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
   rename H into Hdi.
   pose proof (Hxy (S (i + dy))%nat) as H.
   unfold rm_add_i in H; simpl in H.
   do 2 rewrite xorb_false_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite xorb_true_l in H.
   apply negb_sym in H.
   rewrite negb_involutive in H.
   rewrite <- Nat.add_succ_l in H.
   symmetry in Hsy.
   erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
   symmetry in Hsx.
   rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
   simpl in H; rewrite Hty in H; discriminate H.

   subst di; assumption.

   remember (di - S dy)%nat as n eqn:Hn .
   apply nat_sub_add_r in Hn; [ idtac | assumption ].
   subst di; clear H1.
   rewrite Nat.add_succ_r.
   induction n as (n, IHn) using all_lt_all.
   destruct n; [ clear IHn | idtac ].
    rewrite Nat.add_succ_r.
    rewrite <- negb_involutive.
    apply neq_negb; simpl; intros Hdi.
    rewrite Nat.add_0_r in Hdi.
    pose proof (Hxy (S (i + dy))) as H.
    unfold rm_add_i in H; simpl in H.
    do 2 rewrite xorb_false_r in H.
    rewrite Hnx, Hty, xorb_false_l, xorb_true_l in H.
    symmetry in Hsx, Hsy.
    rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
    symmetry in H.
    unfold carry in H; simpl in H.
    remember (fst_same y 0 (S (S (i + dy)))) as s1 eqn:Hs1 .
    destruct s1 as [di1| ]; [ idtac | discriminate H ].
    rename H into Hx1.
    destruct di1.
     rewrite Nat.add_0_r in Hx1.
     rewrite Hdi in Hx1; discriminate Hx1.

     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, _).
     pose proof (Hxy (S (S (i + dy)))) as H.
     unfold rm_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite <- Nat.add_succ_r in H.
     pose proof (Hn1 O (Nat.lt_0_succ di1)) as HH.
     rewrite Nat.add_0_r, <- Nat.add_succ_r in HH.
     rewrite HH, Hnx, xorb_true_l in H.
     apply negb_sym in H.
     rewrite negb_involutive in H.
     rewrite <- Nat.add_succ_l in H.
     symmetry in H.
     rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     symmetry in H, Hs1.
     replace dy with (dy + 0)%nat in H by apply Nat.add_0_r.
     simpl in H.
     rewrite Nat.add_succ_r, Nat.add_assoc in H.
     do 2 rewrite <- Nat.add_succ_l in H.
     clear HH.
     assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H.
     rewrite Hx1 in H; discriminate H.

    rewrite Nat.add_succ_r.
    rewrite <- negb_involutive.
    apply neq_negb; simpl; intros Hdi.
    pose proof (Hxy (S (i + dy + S n))) as H.
    unfold rm_add_i in H; simpl in H.
    do 2 rewrite xorb_false_r in H.
    rewrite <- Nat.add_assoc in H.
    pose proof (IHn n (Nat.lt_succ_diag_r n)) as HH.
    rewrite <- Nat.add_succ_r in HH.
    rewrite <- Nat.add_succ_r in HH.
    rewrite Nat.add_succ_r in HH.
    rewrite Hnx, HH, xorb_false_l, xorb_true_l in H.
    symmetry in Hsx, Hsy.
    rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
    symmetry in H.
    unfold carry in H; simpl in H.
    remember (fst_same y 0 (S (S (i + (dy + S n))))) as s1 eqn:Hs1 .
    destruct s1 as [di1| ]; [ idtac | discriminate H ].
    rename H into Hx1.
    destruct di1.
     rewrite Nat.add_0_r in Hx1.
     rewrite Hdi in Hx1; discriminate Hx1.

     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, _).
     pose proof (Hxy (S (S (i + dy + S n)))) as H.
     unfold rm_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite Hdi in H.
     rewrite <- Nat.add_succ_r in H.
     rewrite Hnx, xorb_true_l in H.
     rewrite <- Nat.add_succ_l in H.
     erewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     apply negb_sym in H; simpl in H.
     rewrite Nat.add_succ_r in H.
     remember (S (S (i + (dy + S n)))) as z.
     replace z with (z + 0)%nat in H by apply Nat.add_0_r.
     subst z.
     symmetry in Hs1.
     assert (0 < S di1)%nat as HHH by apply Nat.lt_0_succ.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H.
     rewrite Hx1 in H; discriminate H.
Qed.

Theorem case_4 : ∀ x y z dx dy,
  (x = y)%rm
  → fst_same x 0 0 = Some dx
  → fst_same y 0 0 = Some dy
  → carry x z 0 = true
  → carry y z 0 = false
  → carry (y + z) 0 0 = false
  → False.
Proof.
intros x y z dx dy Hf_v Hsx Hsy Hc1 Hc3 Hc4.
remember Hsx as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hnx, Htx).
remember Hsy as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hny, Hty).
remember Hf_v as H; clear HeqH.
unfold rm_eq in H; simpl in H.
rename H into Hf.
destruct (lt_eq_lt_dec dx dy) as [[H1| H1]| H1].
  remember H1 as H; clear HeqH.
  apply Hny in H.
  symmetry in Hf_v.
  eapply rm_eq_neq_if in H; try eassumption.
  destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
   pose proof (Hyx (dy - dx)%nat) as H.
   apply Nat.lt_le_incl in H1.
   rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
   rewrite Nat.add_comm, Nat.add_sub, Hty in H.
   discriminate H.

   destruct dx.
    clear Hnx; simpl in Hyx, Hxx.
    unfold carry in Hc1, Hc3.
    remember (fst_same x z 0) as s1 eqn:Hs1 .
    remember (fst_same y z 0) as s3 eqn:Hs3 .
    destruct s3 as [di3| ]; [ idtac | discriminate Hc3 ].
    simpl in Hc3; apply fst_same_sym_iff in Hs3.
    simpl in Hs3; destruct Hs3 as (Hn3, Ht3).
    rewrite Hc3 in Ht3; symmetry in Ht3.
    destruct s1 as [di1| ]; [ simpl in Hc1 | clear Hc1 ].
     apply fst_same_sym_iff in Hs1; simpl in Hs1.
     destruct Hs1 as (Hn1, Ht1).
     rewrite Hc1 in Ht1; symmetry in Ht1.
     destruct di1.
      rewrite Hc1 in Htx; discriminate Htx.

      destruct di3.
       pose proof (Hny O H1) as H.
       rewrite Hc3 in H; discriminate H.

       pose proof (Hn1 O (Nat.lt_0_succ di1)) as H2.
       pose proof (Hn3 O (Nat.lt_0_succ di3)) as H3.
       rewrite Htx in H2.
       rewrite Hny in H3; [ idtac | assumption ].
       rewrite <- H2 in H3; discriminate H3.

     apply fst_same_sym_iff in Hs1; simpl in Hs1.
     destruct di3.
      pose proof (Hny O H1) as H.
      rewrite Hc3 in H; discriminate H.

      pose proof (Hs1 O) as H2.
      pose proof (Hn3 O (Nat.lt_0_succ di3)) as H3.
      rewrite Htx in H2.
      rewrite Hny in H3; [ idtac | assumption ].
      rewrite <- H2 in H3; discriminate H3.

    unfold carry in Hc1, Hc3.
    remember (fst_same x z 0) as s1 eqn:Hs1 .
    remember (fst_same y z 0) as s3 eqn:Hs3 .
    destruct s3 as [di3| ]; [ idtac | discriminate Hc3 ].
    simpl in Hc3; apply fst_same_sym_iff in Hs3.
    simpl in Hs3; destruct Hs3 as (Hn3, Ht3).
    rewrite Hc3 in Ht3; symmetry in Ht3.
    destruct s1 as [di1| ]; [ simpl in Hc1 | clear Hc1 ].
     apply fst_same_sym_iff in Hs1; simpl in Hs1.
     destruct Hs1 as (Hn1, Ht1).
     rewrite Hc1 in Ht1; symmetry in Ht1.
     destruct di1.
      destruct di3.
       rewrite Ht1 in Ht3; discriminate Ht3.

       pose proof (Hn3 O (Nat.lt_0_succ di3)) as H.
       rewrite Ht1 in H; simpl in H.
       destruct dy; [ revert H1; apply Nat.nlt_0_r | idtac ].
       rewrite Hny in H; [ idtac | apply Nat.lt_0_succ ].
       discriminate H.

      destruct dy; [ revert H1; apply Nat.nlt_0_r | idtac ].
      destruct di3.
       rewrite Hny in Hc3; [ idtac | apply Nat.lt_0_succ ].
       discriminate Hc3.

       destruct (lt_eq_lt_dec di1 di3) as [[H2| H2]| H2].
        remember H2 as H; clear HeqH.
        apply Nat.succ_lt_mono in H.
        apply Hn3 in H.
        rewrite Ht1 in H; simpl in H.
        rename H into Hy1.
        destruct (lt_eq_lt_dec di1 dx) as [[H3| H3]| H3].
         remember H3 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         eapply Nat.lt_trans with (m := S dx) in H; [ idtac | eassumption ].
         apply Hny in H.
         rewrite Hy1 in H; discriminate H.

         subst di1.
         rewrite Htx in Hc1; discriminate Hc1.

         remember H3 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         apply Hn1 in H.
         rewrite Htx in H.
         apply negb_sym in H; simpl in H.
         rename H into Hz1.
         remember H3 as H; clear HeqH.
         eapply Nat.lt_trans with (m := di1) in H; [ idtac | eassumption ].
         apply Nat.succ_lt_mono in H.
         apply Hn3 in H.
         rewrite Hz1 in H; simpl in H.
         rewrite Hny in H; [ idtac | assumption ].
         discriminate H.

        subst di3.
        rewrite Ht1 in Ht3; discriminate Ht3.

        remember H2 as H; clear HeqH.
        apply Nat.succ_lt_mono in H.
        apply Hn1 in H.
        rewrite Ht3 in H; simpl in H.
        rename H into Hx3.
        destruct (lt_eq_lt_dec di3 dy) as [[H3| H3]| H3].
         remember H3 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         apply Hny in H.
         rewrite Hc3 in H; discriminate H.

         subst di3.
         remember H2 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         eapply Nat.lt_trans with (m := S dy) in H; [ idtac | eassumption ].
         apply Hn1 in H.
         rewrite Htx in H.
         apply negb_sym in H; simpl in H.
         rename H into Hz1.
         pose proof (Hn3 (S dx) H1) as H.
         rewrite Hz1 in H; simpl in H.
         rewrite Hny in H; [ idtac | assumption ].
         discriminate H.

         remember H1 as H; clear HeqH.
         apply Hny in H.
         rename H into Hy1.
         remember H3 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         eapply Nat.lt_trans with (m := S dy) in H; [ idtac | eassumption ].
         apply Hn3 in H.
         rewrite Hy1 in H.
         apply negb_sym in H; simpl in H.
         rename H into Hz1.
         remember H3 as H; clear HeqH.
         eapply Nat.lt_trans with (m := di3) in H; [ idtac | eassumption ].
         apply Nat.succ_lt_mono in H.
         eapply Nat.lt_trans with (m := S dy) in H; [ idtac | eassumption ].
         apply Hn1 in H.
         rewrite Hz1, Htx in H.
         discriminate H.

     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     rename H into Hn1.
     destruct dy; [ revert H1; apply Nat.nlt_0_r | idtac ].
     destruct (eq_nat_dec dy (S dx)) as [H2| H2].
      subst dy.
      destruct di3.
       rewrite Hny in Hc3; [ idtac | apply Nat.lt_0_succ ].
       discriminate Hc3.

       destruct (lt_eq_lt_dec di3 dx) as [[H2| H2]| H2].
        remember H2 as H; clear HeqH.
        apply Nat.succ_lt_mono in H.
        apply Nat.lt_lt_succ_r in H.
        apply Hny in H.
        rewrite Hc3 in H; discriminate H.

        subst di3.
        rewrite Hn1, Ht3 in Htx.
        discriminate Htx.

        remember H2 as H; clear HeqH.
        apply Nat.succ_lt_mono in H.
        apply Hn3 in H.
        rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
        rewrite <- Hn1 in H.
        rewrite Htx in H; discriminate H.

      pose proof (Hyx O) as H.
      rewrite Nat.add_1_r in H.
      rewrite Hny in H; [ discriminate H | idtac ].
      revert H1 H2; clear; intros; omega.

  subst dy.
  unfold carry in Hc1; simpl in Hc1.
  unfold carry in Hc3; simpl in Hc3.
  remember (fst_same x z 0) as s1 eqn:Hs1 .
  remember (fst_same y z 0) as s3 eqn:Hs3 .
  destruct s3 as [di3| ]; [ idtac | discriminate Hc3 ].
  remember Hs3 as H; clear HeqH.
  apply fst_same_sym_iff in H.
  simpl in H; destruct H as (Hn3, Ht3).
  rewrite Hc3 in Ht3; symmetry in Ht3.
  destruct s1 as [di1| ]; [ simpl in Hc1 | clear Hc1 ].
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct Hs1 as (Hn1, Ht1).
   rewrite Hc1 in Ht1; symmetry in Ht1.
   destruct di1.
    destruct dx; [ rewrite Hc1 in Htx; discriminate Htx | idtac ].
    destruct di3.
     rewrite Ht1 in Ht3; discriminate Ht3.

     pose proof (Hny O (Nat.lt_0_succ dx)) as H.
     rewrite Hn3 in H; [ idtac | apply Nat.lt_0_succ ].
     rewrite Ht1 in H; discriminate H.

    destruct di3.
     destruct dx.
      rewrite Hn1 in Htx; [ idtac | apply Nat.lt_0_succ ].
      rewrite Ht3 in Htx; discriminate Htx.

      rewrite Hny in Hc3; [ idtac | apply Nat.lt_0_succ ].
      discriminate Hc3.

     destruct (lt_eq_lt_dec di1 di3) as [[H1| H1]| H1].
      remember H1 as H; clear HeqH.
      apply Nat.succ_lt_mono in H.
      apply Hn3 in H.
      rewrite Ht1 in H; simpl in H.
      eapply rm_eq_neq_if in H; try eassumption.
      destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
       remember H1 as H; clear HeqH.
       unfold carry in Hc4; simpl in Hc4.
       remember (fst_same (y + z) 0 0) as s2 eqn:Hs2 .
       destruct s2 as [di2| ]; [ idtac | discriminate Hc4 ].
       apply fst_same_sym_iff in Hs2; simpl in Hs2.
       destruct Hs2 as (Hs2, _).
       destruct di2.
        clear Hs2.
        unfold rm_add_i in Hc4.
        rewrite Hn3 in Hc4; [ idtac | apply Nat.lt_0_succ ].
        rewrite negb_xorb_diag_l, xorb_true_l in Hc4.
        apply negb_false_iff in Hc4.
        rewrite <- Nat.add_1_r in Hc4.
        symmetry in Hs3.
        assert (1 ≤ S di3) as HH by apply Nat.lt_0_succ.
        erewrite carry_before_relay in Hc4; try eassumption.
        rewrite Nat.add_0_l, Hc3 in Hc4; discriminate Hc4.

        clear H.
        pose proof (Hf di1) as H.
        unfold rm_add_i in H; simpl in H.
        rewrite Hn1 in H; [ idtac | apply Nat.lt_succ_diag_r ].
        apply Nat.lt_lt_succ_r in H1.
        rewrite Hn3 in H; [ idtac | assumption ].
        rewrite xorb_false_r in H.
        apply xorb_move_l_r_1 in H.
        rewrite <- xorb_assoc, xorb_nilpotent, xorb_false_l in H.
        replace (S di1) with (S di1 + 0)%nat in H by apply Nat.add_0_r.
        rewrite carry_before_inf_relay in H.
         rewrite carry_before_relay with (di := O) in H.
          simpl in H; rewrite Hxx in H; discriminate H.

          apply fst_same_iff; simpl.
          split; [ idtac | rewrite Hxx; reflexivity ].
          intros dj Hdj.
          exfalso; revert Hdj; apply Nat.nlt_0_r.

          reflexivity.

         apply fst_same_iff; simpl.
         intros dj; apply Hyx.

       pose proof (Hxx (di3 - S di1)%nat) as H.
       rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
       rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
       rewrite Nat.add_comm, Nat.add_sub in H.
       rewrite Hc3 in H; discriminate H.

      subst di3.
      rewrite Ht1 in Ht3; discriminate Ht3.

      remember H1 as H; clear HeqH.
      apply Nat.succ_lt_mono in H.
      apply Hn1 in H.
      rewrite Ht3 in H; simpl in H.
      remember H as Hx1; clear HeqHx1.
      eapply rm_eq_neq_if in H; try eassumption.
      destruct H as [(Hxy, Hyy)| (Hxy, Hyy)]; simpl in Hxy, Hyy.
       pose proof (Hf di3) as H.
       unfold rm_add_i in H; simpl in H.
       rewrite Hn3 in H; [ idtac | apply Nat.lt_succ_diag_r ].
       apply Nat.lt_lt_succ_r in H1.
       rewrite Hn1 in H; [ idtac | assumption ].
       rewrite xorb_false_r in H.
       apply xorb_move_l_r_1 in H.
       rewrite <- xorb_assoc, xorb_nilpotent, xorb_false_l in H.
       replace (S di3) with (S di3 + 0)%nat in H by apply Nat.add_0_r.
       rewrite carry_before_inf_relay in H.
        rewrite carry_before_relay with (di := O) in H.
         rewrite Nat.add_0_r, Hc3 in H; discriminate H.

         apply fst_same_iff; simpl.
         split; [ idtac | rewrite Hyy; reflexivity ].
         intros dj Hdj.
         exfalso; revert Hdj; apply Nat.nlt_0_r.

         reflexivity.

        apply fst_same_iff; simpl.
        intros dj; apply Hxy.

       pose proof (Hxy (di1 - S di3)%nat) as H.
       rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
       rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
       rewrite Nat.add_comm, Nat.add_sub in H.
       rewrite Hc1 in H; discriminate H.

   remember Hs1 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rename H into Hxz.
   pose proof (Hxz di3) as Hx1.
   rewrite Ht3 in Hx1; simpl in Hx1.
   remember Hx1 as H; clear HeqH.
   eapply rm_eq_neq_if in H; try eassumption.
   destruct H as [(Hxy, Hyy)| (Hxy, Hyy)]; simpl in Hxy, Hyy.
    destruct di3.
     simpl in Hxy; rewrite Hxy in Htx; discriminate Htx.

     pose proof (Hf di3) as H.
     unfold rm_add_i in H; simpl in H.
     rewrite Hn3 in H; [ idtac | apply Nat.lt_succ_diag_r ].
     rewrite Hxz in H.
     rewrite xorb_false_r in H.
     apply xorb_move_l_r_1 in H.
     rewrite <- xorb_assoc, xorb_nilpotent, xorb_false_l in H.
     replace (S di3) with (S di3 + 0)%nat in H by apply Nat.add_0_r.
     rewrite carry_before_inf_relay in H.
      rewrite carry_before_relay with (di := O) in H.
       rewrite Nat.add_0_r, Hc3 in H; discriminate H.

       apply fst_same_iff; simpl.
       simpl in Hyy.
       split; [ idtac | rewrite Hyy; reflexivity ].
       intros dj Hdj.
       exfalso; revert Hdj; apply Nat.nlt_0_r.

       reflexivity.

      apply fst_same_iff; simpl.
      intros dj; apply Hxy.

    destruct di3.
     destruct dx; [ rewrite Htx in Hx1; discriminate Hx1 | idtac ].
     rewrite Hny in Hc3; [ idtac | apply Nat.lt_0_succ ].
     discriminate Hc3.

     replace O with (0 + 0)%nat in Hc4 by reflexivity.
     rewrite carry_before_inf_relay in Hc4; [ discriminate Hc4 | idtac ].
     apply fst_same_iff; simpl.
     intro j.
     unfold rm_add_i.
     destruct (lt_eq_lt_dec j (S di3)) as [[H1| H1]| H1].
      rewrite Hn3; [ idtac | assumption ].
      rewrite negb_xorb_diag_l.
      apply negb_true_iff.
      unfold carry; simpl.
      remember (fst_same y z (S j)) as s2 eqn:Hs2 .
      apply fst_same_sym_iff in Hs2; simpl in Hs2.
      destruct s2 as [dj2| ].
       destruct Hs2 as (Hn2, Hs2).
       destruct (lt_eq_lt_dec (j + dj2) di3) as [[H2| H2]| H2].
        remember H2 as H; clear HeqH.
        apply Nat.succ_lt_mono in H.
        apply Hn3 in H.
        rewrite Hs2 in H; symmetry in H.
        exfalso; revert H; apply no_fixpoint_negb.

        rewrite H2; assumption.

        destruct dj2; [ exfalso; omega | idtac ].
        remember H2 as H; clear HeqH.
        assert (0 < S dj2)%nat as HH by apply Nat.lt_0_succ.
        apply lt_add_sub_lt_r with (d := O) in H; try assumption.
        apply Hn2 in H.
        apply le_S_n in H1.
        rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
        rewrite Nat.add_comm, Nat.add_sub in H.
        rewrite Hc3, Ht3 in H; discriminate H.

       pose proof (Hs2 (di3 - j)%nat) as H.
       apply le_S_n in H1.
       rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
       rewrite Nat.add_comm, Nat.add_sub in H.
       rewrite Hc3, Ht3 in H; discriminate H.

      subst j.
      rewrite Hc3, Ht3, xorb_false_l.
      unfold carry; simpl.
      remember (fst_same y z (S (S di3))) as s2 eqn:Hs2 .
      destruct s2 as [dj2| ]; [ idtac | reflexivity ].
      rewrite <- Nat.add_succ_r, <- Nat.add_succ_l.
      apply Hyy.

      remember (j - S (S di3))%nat as v eqn:Hv .
      apply nat_sub_add_r in Hv; [ idtac | assumption ].
      subst j.
      rewrite Hyy, xorb_true_l.
      rewrite <- Hxz, Hxy, xorb_false_l.
      unfold carry.
      remember (fst_same y z (S (S di3 + S v))) as s2 eqn:Hs2 .
      destruct s2 as [dj2| ]; [ idtac | reflexivity ].
      rewrite <- Nat.add_succ_r, <- Nat.add_assoc.
      apply Hyy.

  remember H1 as H; clear HeqH.
  apply Hnx in H.
  eapply rm_eq_neq_if in H; try eassumption.
  destruct H as [(Hxy, Hyy)| (Hxy, Hyy)]; simpl in Hxy, Hyy.
   pose proof (Hxy (dx - dy)%nat) as H.
   apply Nat.lt_le_incl in H1.
   rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
   rewrite Nat.add_comm, Nat.add_sub, Htx in H.
   discriminate H.

   destruct (lt_dec (S dy) dx) as [H2| H2].
    remember H2 as H; clear HeqH.
    apply Hnx in H.
    rewrite <- Nat.add_1_r, Hxy in H.
    discriminate H.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H2; [ idtac | assumption ].
    subst dx; clear H1.
    unfold carry in Hc3; simpl in Hc3.
    remember (fst_same y z 0) as s3 eqn:Hs3 .
    destruct s3 as [dj3| ]; [ idtac | discriminate Hc3 ].
    remember Hs3 as H; clear HeqH.
    apply fst_same_sym_iff in H; simpl in H.
    destruct H as (Hn3, Ht3).
    rewrite Hc3 in Ht3; symmetry in Ht3.
    destruct (lt_eq_lt_dec dj3 dy) as [[H1| H1]| H1].
     remember H1 as H; clear HeqH.
     apply Hny in H.
     rewrite Hc3 in H; discriminate H.

     Focus 2.
     pose proof (Hyy (dj3 - S dy)%nat) as H.
     rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
     rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
     rewrite Nat.add_comm, Nat.add_sub, Hc3 in H.
     discriminate H.

     subst dj3.
     unfold carry in Hc1; simpl in Hc1.
     remember (fst_same x z 0) as s1 eqn:Hs1 .
     destruct s1 as [dj1| ]; [ idtac | clear Hc1 ].
      apply fst_same_sym_iff in Hs1; simpl in Hs1.
      destruct Hs1 as (Hn1, Ht1).
      rewrite Hc1 in Ht1; symmetry in Ht1.
      destruct (lt_eq_lt_dec dj1 dy) as [[H1| H1]| H1].
       remember H1 as H; clear HeqH.
       apply Hn3 in H.
       rewrite Hny in H; [ idtac | assumption ].
       rewrite Ht1 in H; discriminate H.

       subst dj1.
       rewrite Ht3 in Ht1; discriminate Ht1.

       pose proof (Hxy (dj1 - S dy)%nat) as H.
       rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
       rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
       rewrite Nat.add_comm, Nat.add_sub, Hc1 in H.
       discriminate H.

      remember Hs1 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      rename H into Ht1.
      unfold carry in Hc4; simpl in Hc4.
      remember (fst_same (y + z) 0 0) as s4 eqn:Hs4 .
      destruct s4 as [di4| ]; [ idtac | discriminate Hc4 ].
      apply fst_same_sym_iff in Hs4; simpl in Hs4.
      destruct Hs4 as (Hn4, _).
      destruct di4.
       unfold rm_add_i in Hc4.
       destruct dy.
        rewrite Hc3, Ht3, xorb_false_l in Hc4.
        unfold carry in Hc4; simpl in Hc4.
        remember (fst_same y z 1) as s5 eqn:Hs5 .
        destruct s5 as [dj5| ]; [ idtac | discriminate Hc4 ].
        simpl in Hyy; rewrite Hyy in Hc4; discriminate Hc4.

        rewrite Hn3 in Hc4; [ idtac | apply Nat.lt_0_succ ].
        rewrite negb_xorb_diag_l, xorb_true_l in Hc4.
        apply negb_false_iff in Hc4.
        unfold carry in Hc4; simpl in Hc4.
        remember (fst_same y z 1) as s5 eqn:Hs5 .
        apply fst_same_sym_iff in Hs5; simpl in Hs5.
        destruct s5 as [dj5| ]; [ idtac | clear Hc4 ].
         destruct Hs5 as (Hn5, Ht5).
         rewrite Hc4 in Ht5; symmetry in Ht5.
         destruct (lt_eq_lt_dec dj5 dy) as [[H1| H1]| H1].
          remember H1 as H; clear HeqH.
          apply Nat.succ_lt_mono in H.
          apply Hn3 in H.
          rewrite Ht5, Hc4 in H; discriminate H.

          subst dj5.
          rewrite Hc3 in Hc4; discriminate Hc4.

          rewrite Hn5 in Hty; [ idtac | assumption ].
          rewrite Ht3 in Hty; discriminate Hty.

         rewrite Hs5 in Hty.
         rewrite Ht3 in Hty; discriminate Hty.

       unfold rm_add_i in Hc4.
       destruct dy.
        simpl in Hxy, Hyy.
        rewrite Hyy, <- Ht1, Hxy, xorb_false_l in Hc4.
        unfold carry in Hc4; simpl in Hc4.
        remember (fst_same y z (S (S di4))) as s5 eqn:Hs5 .
        destruct s5 as [dj5| ]; [ idtac | discriminate Hc4 ].
        rewrite Hyy in Hc4; discriminate Hc4.

        destruct (lt_eq_lt_dec di4 dy) as [[H1| H1]| H1].
         remember H1 as H; clear HeqH.
         apply Nat.succ_lt_mono in H.
         rewrite Hn3 in Hc4; [ idtac | assumption ].
         rewrite negb_xorb_diag_l, xorb_true_l in Hc4.
         apply negb_false_iff in Hc4.
         unfold carry in Hc4; simpl in Hc4.
         remember (fst_same y z (S (S di4))) as s5 eqn:Hs5 .
         destruct s5 as [dj5| ]; [ idtac | clear Hc4 ].
          apply fst_same_sym_iff in Hs5; simpl in Hs5.
          destruct Hs5 as (Hn5, Ht5).
          rewrite Hc4 in Ht5; symmetry in Ht5.
          clear H.
          destruct (lt_eq_lt_dec (S (di4 + dj5)) dy) as [[H2| H2]| H2].
           remember H2 as H; clear HeqH.
           apply Nat.succ_lt_mono in H.
           apply Hn3 in H.
           rewrite Ht5, Hc4 in H; discriminate H.

           rewrite H2, Ht3 in Ht5; discriminate Ht5.

           destruct dj5.
            revert H1 H2; clear; intros; omega.

            remember H2 as H; clear HeqH.
            rewrite <- Nat.add_succ_l in H.
            assert (0 < S dj5)%nat as HH by apply Nat.lt_0_succ.
            eapply lt_add_sub_lt_r with (d := O) in H; try assumption.
            apply Hn5 in H.
            rewrite <- Nat.add_succ_l in H.
            rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
            rewrite Nat.add_comm, Nat.add_sub in H.
            rewrite Hc3, Ht3 in H; discriminate H.

          apply fst_same_sym_iff in Hs5; simpl in Hs5.
          clear H.
          pose proof (Hs5 (dy - S di4)%nat) as H.
          rewrite <- Nat.add_succ_l in H.
          rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
          rewrite Nat.add_comm, Nat.add_sub in H.
          rewrite Hc3, Ht3 in H; discriminate H.

         subst di4.
         rewrite Hty, Ht3, xorb_false_l in Hc4.
         remember (S (S dy)) as u.
         replace u with (u + 0)%nat in Hc4 by apply Nat.add_0_r.
         subst u.
         rewrite carry_before_relay with (di := O) in Hc4.
          simpl in Hc4.
          rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in Hc4.
          rewrite Hyy in Hc4; discriminate Hc4.

          apply fst_same_iff; simpl.
          split.
           intros dj Hdj.
           exfalso; revert Hdj; apply Nat.nlt_0_r.

           rewrite <- Nat.add_succ_l, <- Nat.add_succ_r.
           rewrite Hyy, <- negb_involutive.
           rewrite <- Ht1, Hxy; reflexivity.

          reflexivity.

         pose proof (Hyy (di4 - S dy)%nat) as H.
         rewrite Nat.add_succ_r in H.
         rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
         rewrite Nat.add_comm, Nat.add_sub in H.
         rewrite H in Hc4.
         rename H into Hy4.
         rewrite <- Ht1 in Hc4.
         pose proof (Hxy (di4 - S dy)%nat) as H.
         rewrite Nat.add_succ_r in H.
         rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
         rewrite Nat.add_comm, Nat.add_sub in H.
         rewrite H in Hc4.
         rewrite xorb_false_l in Hc4.
         remember (S (S di4)) as u.
         replace u with (u + 0)%nat in Hc4 by apply Nat.add_0_r.
         subst u.
         rewrite carry_before_relay with (di := O) in Hc4.
          rewrite Nat.add_0_r in Hc4.
          rename H into Hx4.
          pose proof (Hyy (di4 - dy)%nat) as H.
          rewrite Nat.add_succ_l, Nat.add_succ_r in H.
          rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
          rewrite Nat.add_comm, Nat.add_sub in H.
          rewrite Hc4 in H; discriminate H.

          apply fst_same_iff; simpl.
          split.
           intros dj Hdj.
           exfalso; revert Hdj; apply Nat.nlt_0_r.

           rewrite Nat.add_0_r.
           remember (di4 - S dy)%nat as v eqn:Hv .
           apply nat_sub_add_r in Hv; [ idtac | assumption ].
           subst di4.
           rewrite <- Nat.add_succ_l, <- Nat.add_succ_r.
           rewrite Hyy, <- negb_involutive.
           rewrite <- Ht1, Hxy; reflexivity.

          reflexivity.
Qed.

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
  remember Hf as Hf_v; clear HeqHf_v.
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

   symmetry in Hsx, Hsy.
   eapply case_4 with (x := x); try eassumption.

   rewrite carry_comm in Hc4.
   eapply case_1; try eassumption.
   unfold carry; simpl.
   rewrite fst_same_comm, <- Hsy; reflexivity.

   Focus 2.
   remember (carry 0 y 0) as c5 eqn:Hc5 .
   symmetry in Hc5.
   destruct c5.
    unfold carry in Hc5; simpl in Hc5.
    remember (fst_same 0 y 0) as s5 eqn:Hs5 .
    destruct s5; [ discriminate Hc5 | clear Hc5 ].
    remember Hs5 as H; clear HeqH.
    rewrite fst_same_comm in H.
    apply fst_same_sym_iff in H; simpl in H.
    rewrite H in Hty; discriminate Hty.

    rewrite carry_comm in Hc4.
    eapply case_1; eassumption.

   Focus 2.
   symmetry in Hsx, Hsy, Hf_v.
   eapply case_4 with (y := x); eassumption.

   remember (carry x 0 0) as c5 eqn:Hc5.
   remember (carry (0%rm + x) z 0) as c6 eqn:Hc6.
   symmetry in Hc5, Hc6.
   destruct c5.
    unfold carry in Hc5; simpl in Hc5.
    rewrite <- Hsx, Htx in Hc5; discriminate Hc5.

    destruct c6.
     unfold carry in Hc6; simpl in Hc6.
     remember (fst_same (0%rm + x) z 0) as s6 eqn:Hs6 .
     apply fst_same_sym_iff in Hs6; simpl in Hs6.
     destruct s6 as [dj6| ]; [ idtac | clear Hc6 ].
      destruct Hs6 as (Hn6, Ht6).
      rewrite Hc6 in Ht6; symmetry in Ht6.
      rewrite rm_add_i_comm in Hc6.
      unfold rm_add_i in Hc6; simpl in Hc6.
      rewrite xorb_false_r in Hc6.
      unfold carry in Hc6.
      remember (fst_same x 0 (S dj6)) as s7 eqn:Hs7 .
      apply fst_same_sym_iff in Hs7; simpl in Hs7.
      destruct s7 as [dj7| ]; [ idtac | clear Hc6 ].
       destruct Hs7 as (Hn7, Ht7).
       simpl in Hc6.
       rewrite Ht7, xorb_false_r in Hc6.
       unfold carry in Hc1; simpl in Hc1.
       remember (fst_same x z 0) as s1 eqn:Hs1 .
       destruct s1 as [dj1| ]; [ idtac | discriminate Hc1 ].
       apply fst_same_sym_iff in Hs1; simpl in Hs1.
       destruct Hs1 as (Hn1, Hs1).
       rewrite Hc1 in Hs1; symmetry in Hs1.
       destruct (lt_eq_lt_dec dj1 dj6) as [[H1| H1]| H1].
        remember H1 as H; clear HeqH.
        apply Hn6 in H.
        rewrite rm_add_i_comm in H.
        unfold rm_add_i in H; simpl in H.
        rewrite Hc1, Hs1, xorb_false_l in H; simpl in H.
        unfold carry in H; simpl in H.
        remember (fst_same x 0 (S dj1)) as s8 eqn:Hs8 .
        apply fst_same_sym_iff in Hs8; simpl in Hs8.
        destruct s8 as [dj8| ]; [ idtac | clear H ].
         destruct Hs8 as (Hn8, Ht8).
         rewrite Ht8 in H; discriminate H.

         pose proof (Hs8 (dj6 + dj7 - dj1)%nat) as H.
         rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
         rewrite Nat.add_comm, Nat.add_sub in H.
         rewrite Ht7 in H; discriminate H.

        subst dj6.
        rewrite Hc1 in Hc6; discriminate Hc6.

        remember H1 as H; clear HeqH.
        apply Hn1 in H.
        rewrite Ht6, Hc6 in H; discriminate H.

       unfold carry in Hc1; simpl in Hc1.
       remember (fst_same x z 0) as s1 eqn:Hs1 .
       destruct s1 as [dj1| ]; [ idtac | discriminate Hc1 ].
       apply fst_same_sym_iff in Hs1; simpl in Hs1.
       destruct Hs1 as (Hn1, Hs1).
       rewrite Hc1 in Hs1; symmetry in Hs1.
       destruct (lt_eq_lt_dec dj1 dj6) as [[H1| H1]| H1].
        remember H1 as H; clear HeqH.
        apply Hn6 in H.
        rewrite rm_add_i_comm in H.
        unfold rm_add_i in H; simpl in H.
        rewrite Hc1, Hs1, xorb_false_l in H; simpl in H.
        unfold carry in H; simpl in H.
        remember (fst_same x 0 (S dj1)) as s8 eqn:Hs8 .
        apply fst_same_sym_iff in Hs8; simpl in Hs8.
        destruct s8 as [dj8| ]; [ idtac | clear H ].
         destruct Hs8 as (Hn8, Ht8).
         rewrite Ht8 in H; discriminate H.

         unfold carry in Hc2; simpl in Hc2.
         remember (fst_same (x + z) 0 0) as s2 eqn:Hs2 .
         apply fst_same_sym_iff in Hs2; simpl in Hs2.
         destruct s2 as [dj2| ]; [ idtac | clear Hc2 ].
          destruct Hs2 as (Hn2, Ht2).
          rewrite Ht2 in Hc2; discriminate Hc2.
bbb.
   rewrite carry_comm in Hc2.
   eapply case_3 with (x := 0%rm) (y := x) (z := z); try eassumption.
bbb.
   destruct (lt_eq_lt_dec dx dy) as [[H1| H1]| H1].
    remember H1 as H; clear HeqH.
    apply Hny in H.
    rename H into Hy1.
    symmetry in Hf_v.
    remember Hy1 as H; clear HeqH.
    eapply rm_eq_neq_if in H; try eassumption.
    destruct H as [(Hyx, Hxx)| (Hyx, Hxx)]; simpl in Hyx, Hxx.
     pose proof (Hyx (dy - dx)%nat) as H.
     apply Nat.lt_le_incl in H1.
     rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
     rewrite Nat.add_comm, Nat.add_sub, Hty in H.
     discriminate H.

     destruct (lt_dec (S dx) dy) as [H2| H2].
      remember H2 as H; clear HeqH.
      apply Hny in H.
      rewrite <- Nat.add_1_r, Hyx in H.
      discriminate H.

      apply Nat.nlt_ge in H2.
      apply Nat.le_antisymm in H2; [ idtac | assumption ].
      subst dy; clear H1.

bbb.
   unfold carry in Hc1; simpl in Hc1.
   remember (fst_same x z 0) as s1 eqn:Hs1 .
   destruct s1 as [dj1| ]; [ idtac | discriminate Hc1 ].
   remember Hs1 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn1, Ht1).
   rewrite Hc1 in Ht1; symmetry in Ht1.
bbb.
     0   -   dx  -   dy
  x  1   1   0   .   .
  y  1   1   1   1   0
  z  .


   eapply case_2; try eassumption.
bbb.

Theorem rm_add_compat : ∀ x y z d,
  (x = y)%R
  → (z = t)%R
  → (x + z = y + t)%R
Proof.
intros x y z t Hxy Hzt.
bbb.

Close Scope Z_scope.
