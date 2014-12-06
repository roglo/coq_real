Require Import Utf8 QArith NPeano.
Require Import Real01Add.

Set Implicit Arguments.

Open Scope nat_scope.

Record real := { re_mant : real_mod_1; re_power : nat; re_sign : bool }.

Delimit Scope R_scope with R.
Arguments re_mant _%R.
Arguments re_power _%R.
Arguments re_sign _%R.

Definition rm_shift_r n pad x :=
  {| rm i := if lt_dec i n then pad else x.[i-n] |}.
Arguments rm_shift_r n%nat pad%bool x%rm.

Definition rm_final_carry x y :=
  match fst_same x y 0 with
  | Some j => x.[j]
  | None => true
  end.

Definition re_add x y :=
  let xm := rm_shift_r (max 0 (re_power y - re_power x)) false (re_mant x) in
  let ym := rm_shift_r (max 0 (re_power x - re_power y)) false (re_mant y) in
  if bool_dec (re_sign x) (re_sign y) then
    let zm := rm_add xm ym in
    let c := rm_final_carry xm ym in
    {| re_mant := if c then rm_shift_r 1 true zm else zm;
       re_power := max (re_power x) (re_power y) + if c then 1 else 0;
       re_sign := re_sign x |}
  else
    let (zm, sign) :=
      match rm_compare xm ym with
      | Eq => (rm_zero, true)
      | Lt => (rm_sub ym xm, re_sign y)
      | Gt => (rm_sub xm ym, re_sign x)
      end
    in
    {| re_mant := zm;
       re_power := max (re_power x) (re_power y);
       re_sign := sign |}.

Definition re_zero :=
  {| re_mant := rm_zero; re_power := 0; re_sign := true |}.

Notation "x + y" := (re_add x y) : R_scope.
Notation "0" := re_zero : R_scope.

Definition re_norm x :=
  match fst_same (re_mant x) rm_ones 0 with
  | Some j =>
      {| re_mant := rm_shift_l (min j (re_power x)) (re_mant x);
         re_power := re_power x - j;
         re_sign := re_sign x |}
  | None =>
      re_zero
  end.
Arguments re_norm x%R.

Definition re_eq x y :=
  let xn := re_norm x in
  let yn := re_norm y in
  rm_eq (re_mant xn) (re_mant yn) ∧
  re_power x = re_power y ∧
  re_sign x = re_sign y.
Arguments re_eq x%R y%R.

Notation "x = y" := (re_eq x y) : R_scope.

Theorem re_eq_refl : reflexive _ re_eq.
Proof.
intros x.
split; [ reflexivity | split; reflexivity ].
Qed.

Theorem re_eq_sym : symmetric _ re_eq.
Proof.
intros x y Hxy.
destruct Hxy as (Hm, (Hp, Hs)).
unfold re_eq.
rewrite Hm, Hp, Hs.
split; [ reflexivity | split; reflexivity ].
Qed.

Theorem re_eq_trans : transitive _ re_eq.
Proof.
intros x y z Hxy Hyz.
destruct Hxy as (Hm, (Hp, Hs)).
destruct Hyz as (Im, (Ip, Is)).
unfold re_eq.
split; [ etransitivity; eassumption | idtac ].
split; etransitivity; eassumption.
Qed.

Add Parametric Relation : _ re_eq
 reflexivity proved by re_eq_refl
 symmetry proved by re_eq_sym
 transitivity proved by re_eq_trans
 as re_rel.

(* commutativity *)

Theorem rm_final_carry_comm : ∀ x y, rm_final_carry x y = rm_final_carry y x.
Proof.
intros x y.
unfold rm_final_carry.
rewrite fst_same_comm.
remember (fst_same y x (0)) as s eqn:Hs .
destruct s as [di| ]; [ idtac | reflexivity ].
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct Hs; symmetry; assumption.
Qed.

Theorem rm_shift_r_comm : ∀ n p x y,
  (rm_shift_r n p (x + y) = rm_shift_r n p (y + x))%rm.
Proof.
intros n p x y.
unfold rm_eq; intros i; simpl.
unfold rm_add_i; simpl.
destruct (lt_dec i n) as [H1| H1].
 f_equal.
 apply carry_compat_r; intros j; simpl.
 destruct (lt_dec j) as [H2| H2]; [ reflexivity | idtac ].
 apply rm_add_i_comm.

 do 2 rewrite xorb_false_r.
 f_equal; [ apply rm_add_i_comm | idtac ].
 apply carry_compat_r; intros j; simpl.
 destruct (lt_dec j) as [H2| H2]; [ reflexivity | idtac ].
 apply rm_add_i_comm.
Qed.

Theorem fst_same_rm_shift_r_add_comm_l : ∀ x y z n p,
  fst_same (rm_shift_r n p (x + y)) z 0 =
  fst_same (rm_shift_r n p (y + x)) z 0.
Proof.
intros x y z n p.
apply fst_same_iff; simpl.
remember (fst_same (rm_shift_r n p (y + x)) z 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Hs).
 split.
  intros dj Hdj.
  apply Hn in Hdj.
  destruct (lt_dec dj n) as [H1| H1]; [ assumption | idtac ].
  rewrite rm_add_i_comm; assumption.

  destruct (lt_dec di n) as [H1| H1]; [ assumption | idtac ].
  rewrite rm_add_i_comm; assumption.

 intros dj.
 pose proof (Hs dj) as H.
 destruct (lt_dec dj n) as [H1| H1]; [ assumption | idtac ].
 rewrite rm_add_i_comm; assumption.
Qed.

Theorem rm_shift_l_comm : ∀ x y n,
  (rm_shift_l n (x + y) = rm_shift_l n (y + x))%rm.
Proof.
intros x y n.
unfold rm_eq; intros i; simpl.
unfold rm_add_i; simpl.
rewrite rm_add_i_comm.
f_equal.
apply carry_compat_r; intros j; simpl.
apply rm_add_i_comm.
Qed.

Theorem fst_same_comm_l : ∀ x y z n,
  fst_same (x + y) z n = fst_same (y + x) z n.
Proof.
intros x y z n.
apply fst_same_iff; simpl.
remember (fst_same (y + x) z n) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Hs).
 split; [ idtac | rewrite rm_add_i_comm; assumption ].
 intros dj Hdj.
 rewrite rm_add_i_comm.
 apply Hn; assumption.

 intros j.
 rewrite rm_add_i_comm; apply Hs.
Qed.

Theorem rm_compare_eq : ∀ x y, (x = y)%rm ↔ rm_compare x y = Eq.
Proof.
intros x y.
split; intros H.
 unfold rm_compare.
 unfold rm_eq in H; simpl in H.
 remember (fst_same (x + 0%rm) (- (y + 0)%rm) 0) as s eqn:Hs .
 apply fst_same_sym_iff in Hs; simpl in Hs.
 destruct s as [j| ]; [ exfalso | reflexivity ].
 destruct Hs as (Hn, Hs).
 rewrite H in Hs.
 symmetry in Hs; revert Hs; apply no_fixpoint_negb.

 unfold rm_compare in H.
 remember (fst_same (x + 0%rm) (- (y + 0)%rm) 0) as s eqn:Hs .
 apply fst_same_sym_iff in Hs; simpl in Hs.
 destruct s as [j| ]; [ exfalso | idtac ].
  destruct (x + 0)%rm .[ j]; discriminate H.

  unfold rm_eq; intros i; simpl.
  rewrite Hs, negb_involutive; reflexivity.
Qed.

Theorem rm_compare_lt : ∀ x y, (x < y)%rm ↔ rm_compare x y = Lt.
Proof.
intros x y.
split; intros H; assumption.
Qed.

Theorem rm_compare_gt : ∀ x y, (x > y)%rm ↔ rm_compare x y = Gt.
Proof.
intros x y.
split; intros H; assumption.
Qed.

Theorem rm_compare_Gt_Lt_antisym : ∀ x y, (x ?= y)%rm = Gt ↔ (y ?= x)%rm = Lt.
Proof.
intros x y.
unfold rm_compare; simpl.
remember (fst_same (x + 0%rm) (- (y + 0)%rm) 0) as s1 eqn:Hs1 .
remember (fst_same (y + 0%rm) (- (x + 0)%rm) 0) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [j1| ].
 destruct Hs1 as (Hs1, Hn1).
 remember (rm_add_i x 0 j1) as x0 eqn:Hx0 .
 symmetry in Hx0; apply negb_sym in Hn1.
 destruct s2 as [j2| ].
  destruct Hs2 as (Hs2, Hn2).
  remember (rm_add_i y 0 j2) as y0 eqn:Hy0 .
  symmetry in Hy0; apply negb_sym in Hn2.
  destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
   apply Hs2 in H1.
   rewrite negb_involutive, Hn1 in H1.
   rewrite Hx0 in H1.
   exfalso; revert H1; apply no_fixpoint_negb.

   subst j2.
   destruct x0.
    split; intros H; [ clear H | reflexivity ].
    destruct y0; [ exfalso | reflexivity ].
    rewrite Hx0 in Hn2; discriminate Hn2.

    split; intros H; [ discriminate H | exfalso ].
    destruct y0; [ discriminate H | clear H ].
    rewrite Hx0 in Hn2; discriminate Hn2.

   apply Hs1 in H1.
   rewrite negb_involutive, Hn2 in H1.
   rewrite Hy0 in H1.
   exfalso; revert H1; apply no_fixpoint_negb.

  split; intros H; [ exfalso | discriminate H ].
  destruct x0; [ clear H | discriminate H ].
  rewrite Hs2, Hx0 in Hn1; discriminate Hn1.

 destruct s2 as [j2| ].
  destruct Hs2 as (Hs2, Hn2).
  split; intros H; [ discriminate H | exfalso ].
  rewrite Hs1, negb_involutive in Hn2.
  symmetry in Hn2; revert Hn2; apply no_fixpoint_negb.

  split; intros H; discriminate H.
Qed.

Theorem re_mant_norm_add_comm : ∀ x y,
  (re_mant (re_norm (x + y)) = re_mant (re_norm (y + x)))%rm.
Proof.
intros x y.
unfold re_add.
remember (re_power x - re_power y) as pxy eqn:Hpxy .
remember (re_power y - re_power x) as pyx eqn:Hpyx .
remember (rm_shift_r (max 0 pxy) false (re_mant y)) as sxy eqn:Hsxy .
remember (rm_shift_r (max 0 pyx) false (re_mant x)) as syx eqn:Hsyx .
rewrite rm_final_carry_comm.
remember (rm_final_carry sxy syx) as fc eqn:Hfc .
symmetry in Hfc.
rewrite Nat.max_comm.
destruct (bool_dec (re_sign x) (re_sign y)) as [H1| H1].
 destruct (bool_dec (re_sign y) (re_sign x)) as [H2| H2].
  destruct fc.
   unfold re_norm; simpl.
   rewrite fst_same_rm_shift_r_add_comm_l.
   remember (fst_same (rm_shift_r 1 true (sxy + syx)) rm_ones 0) as s.
   rename Heqs into Hs.
   symmetry in Hs.
   destruct s as [j| ]; [ simpl | reflexivity ].
   unfold rm_eq; intros i; simpl.
   apply rm_add_i_compat; [ idtac | reflexivity ].
   intros k; simpl.
   remember (max (re_power y) (re_power x) + 1) as m.
   destruct (lt_dec (k + min j m) 1) as [H3| H3]; [ reflexivity | idtac ].
   apply rm_add_i_comm.

   unfold rm_eq; intros i; simpl.
   unfold re_norm; simpl.
   rewrite fst_same_comm_l.
   remember (fst_same (sxy + syx) rm_ones 0) as s eqn:Hs .
   destruct s as [j| ]; [ simpl | reflexivity ].
   unfold rm_add_i; simpl.
   rewrite rm_add_i_comm; f_equal.
   apply carry_compat; [ idtac | reflexivity ].
   intros k; simpl.
   apply rm_add_i_comm.

  symmetry in H1; contradiction.

 destruct (bool_dec (re_sign y) (re_sign x)) as [H2| H2].
  symmetry in H2; contradiction.

  remember (rm_compare syx sxy) as cmp1 eqn:Hcmp1 .
  symmetry in Hcmp1.
  destruct cmp1.
   apply rm_compare_eq in Hcmp1; symmetry in Hcmp1.
   apply rm_compare_eq in Hcmp1; rewrite Hcmp1.
   reflexivity.

   apply rm_compare_Gt_Lt_antisym in Hcmp1; rewrite Hcmp1.
   reflexivity.

   apply rm_compare_Gt_Lt_antisym in Hcmp1; rewrite Hcmp1.
   reflexivity.
Qed.

Theorem re_power_add_comm : ∀ x y,
  re_power (x + y) = re_power (y + x).
Proof.
intros x y.
unfold re_add.
remember (re_power x - re_power y) as pxy eqn:Hpxy .
remember (re_power y - re_power x) as pyx eqn:Hpyx .
remember (rm_shift_r (max 0 pxy) false (re_mant y)) as sxy eqn:Hsxy .
remember (rm_shift_r (max 0 pyx) false (re_mant x)) as syx eqn:Hsyx .
rewrite rm_final_carry_comm.
remember (rm_final_carry sxy syx) as fc eqn:Hfc .
symmetry in Hfc.
rewrite Nat.max_comm.
destruct (bool_dec (re_sign x) (re_sign y)) as [H1| H1]; simpl.
 destruct (bool_dec (re_sign y) (re_sign x)) as [H2| H2]; simpl.
  reflexivity.

  symmetry in H1; contradiction.

 destruct (bool_dec (re_sign y) (re_sign x)) as [H2| H2]; simpl.
  symmetry in H2; contradiction.

  remember (syx ?= sxy)%rm as cmp eqn:Hcmp .
  symmetry in Hcmp.
  destruct cmp.
   apply rm_compare_eq in Hcmp; symmetry in Hcmp.
   apply rm_compare_eq in Hcmp; rewrite Hcmp.
   reflexivity.

   apply rm_compare_Gt_Lt_antisym in Hcmp; rewrite Hcmp.
   reflexivity.

   apply rm_compare_Gt_Lt_antisym in Hcmp; rewrite Hcmp.
   reflexivity.
Qed.

Theorem re_sign_add_comm : ∀ x y,
  re_sign (x + y) = re_sign (y + x).
Proof.
intros x y.
unfold re_add.
remember (re_power x - re_power y) as pxy eqn:Hpxy .
remember (re_power y - re_power x) as pyx eqn:Hpyx .
remember (rm_shift_r (max 0 pxy) false (re_mant y)) as sxy eqn:Hsxy .
remember (rm_shift_r (max 0 pyx) false (re_mant x)) as syx eqn:Hsyx .
rewrite rm_final_carry_comm.
remember (rm_final_carry sxy syx) as fc eqn:Hfc .
symmetry in Hfc.
rewrite Nat.max_comm.
destruct (bool_dec (re_sign x) (re_sign y)) as [H1| H1]; simpl.
 destruct (bool_dec (re_sign y) (re_sign x)) as [H2| H2]; simpl.
  assumption.

  symmetry in H1; contradiction.

 destruct (bool_dec (re_sign y) (re_sign x)) as [H2| H2]; simpl.
  symmetry in H2; contradiction.

  remember (syx ?= sxy)%rm as cmp eqn:Hcmp .
  symmetry in Hcmp.
  destruct cmp.
   apply rm_compare_eq in Hcmp; symmetry in Hcmp.
   apply rm_compare_eq in Hcmp; rewrite Hcmp.
   reflexivity.

   apply rm_compare_Gt_Lt_antisym in Hcmp; rewrite Hcmp.
   reflexivity.

   apply rm_compare_Gt_Lt_antisym in Hcmp; rewrite Hcmp.
   reflexivity.
Qed.

Theorem re_add_comm : ∀ x y, (x + y = y + x)%R.
Proof.
intros x y.
unfold re_eq.
split; [ apply re_mant_norm_add_comm | idtac ].
split; [ apply re_power_add_comm | idtac ].
apply re_sign_add_comm.
Qed.

Close Scope nat_scope.
