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
    {| re_mant :=
         match rm_compare xm ym with
         | Eq => rm_zero
         | Lt => rm_sub ym xm
         | Gt => rm_sub xm ym
         end;
       re_power := max (re_power x) (re_power y);
       re_sign :=
         match rm_compare xm ym with
         | Eq => true
         | Lt => re_sign y
         | Gt => re_sign x
         end |}.

Definition re_zero :=
  {| re_mant := rm_zero; re_power := 0; re_sign := true |}.

Notation "x + y" := (re_add x y) : R_scope.
Notation "0" := re_zero : R_scope.

Definition re_norm x :=
  match fst_same (re_mant x + 0%rm) rm_ones 0 with
  | Some j =>
      {| re_mant := rm_shift_l (min j (re_power x)) (re_mant x + 0%rm);
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

(* equality is equivalence relation *)

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

Theorem negb_negb : ∀ a b, negb a = negb b ↔ a = b.
Proof.
intros a b.
split; intros H; [ idtac | subst a; reflexivity ].
apply negb_sym in H; subst b.
rewrite negb_involutive; reflexivity.
Qed.

Theorem fst_same_rm_shift_r_add_comm_l : ∀ x y z n p,
  fst_same (rm_shift_r n p (x + y) + 0%rm) z 0 =
  fst_same (rm_shift_r n p (y + x) + 0%rm) z 0.
Proof.
(* à revoir : il y a du code répété *)
intros x y z n p.
remember (rm_shift_r n p (x + y)) as x1 eqn:Hx1 .
remember (rm_shift_r n p (y + x)) as x2 eqn:Hx2 .
apply fst_same_iff; simpl.
remember (fst_same (x2 + 0%rm) z 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Hs).
 split.
  intros dj Hdj.
  remember Hdj as H; clear HeqH.
  apply Hn in H.
  unfold rm_add_i in H; simpl in H.
  unfold rm_add_i; simpl.
  rewrite xorb_false_r in H.
  rewrite xorb_false_r.
  unfold carry in H; simpl in H.
  unfold carry; simpl.
  remember (fst_same x1 0 (S dj)) as s1 eqn:Hs1 .
  remember (fst_same x2 0 (S dj)) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s1 as [dj1| ].
   destruct Hs1 as (Hn1, Hs1); rewrite Hs1.
   rewrite xorb_false_r.
   destruct s2 as [dj2| ].
    destruct Hs2 as (Hn2, Hs2); rewrite Hs2 in H.
    rewrite xorb_false_r in H.
    rewrite Hx1; simpl.
    rewrite Hx2 in H; simpl in H.
    rewrite rm_add_i_comm; assumption.

    remember (S (dj + dj1)) as i.
    rewrite Hx1 in Hs1; simpl in Hs1.
    pose proof (Hs2 dj1) as HH.
    rewrite <- Heqi in HH.
    rewrite Hx2 in HH; simpl in HH.
    rewrite rm_add_i_comm, Hs1 in HH.
    discriminate HH.

   destruct s2 as [dj2| ].
    destruct Hs2 as (Hn2, Hs2).
    remember (S (dj + dj2)) as i.
    rewrite Hx2 in Hs2; simpl in Hs2.
    pose proof (Hs1 dj2) as HH.
    rewrite <- Heqi in HH.
    rewrite Hx1 in HH; simpl in HH.
    rewrite rm_add_i_comm, Hs2 in HH.
    discriminate HH.

    rewrite xorb_true in H.
    rewrite xorb_true.
    apply negb_negb with (a := x2 .[ dj]) in H.
    apply negb_negb.
    rewrite Hx2 in H; simpl in H.
    rewrite Hx1; simpl.
    rewrite rm_add_i_comm; assumption.

  remember Hs as H; clear HeqH.
  unfold rm_add_i in H; simpl in H.
  unfold rm_add_i; simpl.
  rewrite xorb_false_r in H.
  rewrite xorb_false_r.
  unfold carry in H; simpl in H.
  unfold carry; simpl.
  rename di into dj.
  remember (fst_same x1 0 (S dj)) as s1 eqn:Hs1 .
  remember (fst_same x2 0 (S dj)) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s1 as [dj1| ].
   destruct Hs1 as (Hn1, Hs1); rewrite Hs1.
   rewrite xorb_false_r.
   destruct s2 as [dj2| ].
    destruct Hs2 as (Hn2, Hs2); rewrite Hs2 in H.
    rewrite xorb_false_r in H.
    rewrite Hx1; simpl.
    rewrite Hx2 in H; simpl in H.
    rewrite rm_add_i_comm; assumption.

    remember (S (dj + dj1)) as i.
    rewrite Hx1 in Hs1; simpl in Hs1.
    pose proof (Hs2 dj1) as HH.
    rewrite <- Heqi in HH.
    rewrite Hx2 in HH; simpl in HH.
    rewrite rm_add_i_comm, Hs1 in HH.
    discriminate HH.

   destruct s2 as [dj2| ].
    destruct Hs2 as (Hn2, Hs2).
    remember (S (dj + dj2)) as i.
    rewrite Hx2 in Hs2; simpl in Hs2.
    pose proof (Hs1 dj2) as HH.
    rewrite <- Heqi in HH.
    rewrite Hx1 in HH; simpl in HH.
    rewrite rm_add_i_comm, Hs2 in HH.
    discriminate HH.

    rewrite xorb_true in H.
    rewrite xorb_true.
    rewrite Hx2 in H; simpl in H.
    rewrite Hx1; simpl.
    rewrite rm_add_i_comm; assumption.

 intros dj.
 unfold rm_add_i; simpl.
 pose proof (Hs dj) as H.
 unfold rm_add_i in H; simpl in H.
 rewrite xorb_false_r in H.
 rewrite xorb_false_r.
 unfold carry in H; simpl in H.
 unfold carry; simpl.
 remember (fst_same x1 0 (S dj)) as s1 eqn:Hs1 .
 remember (fst_same x2 0 (S dj)) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s1 as [dj1| ].
  destruct Hs1 as (Hn1, Hs1); rewrite Hs1.
  rewrite xorb_false_r.
  destruct s2 as [dj2| ].
   destruct Hs2 as (Hn2, Hs2); rewrite Hs2 in H.
   rewrite xorb_false_r in H.
   rewrite Hx1; simpl.
   rewrite Hx2 in H; simpl in H.
   rewrite rm_add_i_comm; assumption.

   remember (S (dj + dj1)) as i.
   rewrite Hx1 in Hs1; simpl in Hs1.
   pose proof (Hs2 dj1) as HH.
   rewrite <- Heqi in HH.
   rewrite Hx2 in HH; simpl in HH.
   rewrite rm_add_i_comm, Hs1 in HH.
   discriminate HH.

  rewrite xorb_true_r.
  apply negb_negb.
  destruct s2 as [dj2| ].
   destruct Hs2 as (Hn2, Hs2); rewrite Hs2 in H.
   rewrite xorb_false_r in H.
   remember (S (dj + dj2)) as i.
   rewrite Hx2 in Hs2; simpl in Hs2.
   pose proof (Hs1 dj2) as HH.
   rewrite <- Heqi in HH.
   rewrite Hx1 in HH; simpl in HH.
   rewrite rm_add_i_comm, Hs2 in HH.
   discriminate HH.

   rewrite xorb_true in H.
   apply negb_negb with (a := x2 .[ dj]) in H.
   rewrite Hx2 in H; simpl in H.
   rewrite Hx1; simpl.
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
   remember (fst_same (rm_shift_r 1 true (sxy + syx) + 0%rm) rm_ones 0) as s.
   rename Heqs into Hs.
   symmetry in Hs.
   destruct s as [j| ]; [ simpl | reflexivity ].
   unfold rm_eq; intros i; simpl.
   apply rm_add_i_compat; [ idtac | reflexivity ].
   intros k; simpl.
bbb.
   rewrite rm_add_i_comm.
   reflexivity.

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
rewrite rm_final_carry_comm.
destruct (bool_dec (re_sign x) (re_sign y)) as [H1| H1]; simpl.
 destruct (bool_dec (re_sign y) (re_sign x)) as [H2| H2]; simpl.
  rewrite Nat.max_comm; reflexivity.

  symmetry in H1; contradiction.

 destruct (bool_dec (re_sign y) (re_sign x)) as [H2| H2]; simpl.
  symmetry in H2; contradiction.

  rewrite Nat.max_comm; reflexivity.
Qed.

Theorem re_sign_add_comm : ∀ x y,
  re_sign (x + y) = re_sign (y + x).
Proof.
intros x y.
unfold re_add.
destruct (bool_dec (re_sign x) (re_sign y)) as [H1| H1]; simpl.
 destruct (bool_dec (re_sign y) (re_sign x)) as [H2| H2]; simpl.
  assumption.

  symmetry in H1; contradiction.

 destruct (bool_dec (re_sign y) (re_sign x)) as [H2| H2]; simpl.
  symmetry in H2; contradiction.

  remember (re_power x - re_power y) as pxy eqn:Hpxy .
  remember (re_power y - re_power x) as pyx eqn:Hpyx .
  remember (rm_shift_r pxy false (re_mant y)) as sxy eqn:Hsxy .
  remember (rm_shift_r pyx false (re_mant x)) as syx eqn:Hsyx .
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

(* neutral element *)

Theorem zzz : ∀ x i,
  (re_mant x).[i] = false
  → (re_mant (x + 0%R)).[i] = true
  → ∀ j, i < j → (re_mant x).[j] = true.
Proof.
Abort. (* à voir...
bbb.
*)

Theorem re_mant_norm_add_0_r : ∀ x,
  (re_mant (re_norm (x + 0%R)) = re_mant (re_norm x))%rm.
Proof.
intros x.
bbb.

unfold re_norm; simpl.
remember (fst_same (re_mant (x + 0%R)) rm_ones 0) as s1 eqn:Hs1 .
remember (fst_same (re_mant x) rm_ones 0) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [j1| ]; simpl.
 destruct Hs1 as (Hn1, Hs1).
 destruct s2 as [j2| ]; simpl.
  destruct Hs2 as (Hn2, Hs2).
  destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H.
bbb.
       0       j₁      j₂
  x+0  0   0   1   .   .
   x   0   0   0   0   1

  Hn1 : ∀ dj : nat, dj < j1 → (re_mant (x + 0%R)) .[ dj] = false
  Hs1 : (re_mant (x + 0%R)) .[ j1] = true
  j2 : nat
  Hn2 : ∀ dj : nat, dj < j2 → (re_mant x) .[ dj] = false
  Hs2 : (re_mant x) .[ j2] = true
  H1 : j1 < j2
  ============================
   (rm_shift_l (min j1 (re_power (x + 0%R))) (re_mant (x + 0%R)) =
    rm_shift_l (min j2 (re_power x)) (re_mant x))%rm


  unfold re_add; simpl.
  rewrite Nat.max_0_r.
  destruct (bool_dec (re_sign x) true) as [H1| H1]; simpl.
bbb.

intros x.
unfold re_add; simpl.
rewrite Nat.max_0_r.
destruct (bool_dec (re_sign x) true) as [H1| H1]; simpl.
 unfold re_norm; simpl.
 rewrite Nat.sub_0_r.
 remember (rm_shift_r 0 false (re_mant x)) as x1 eqn:Hx1 .
 remember (rm_shift_r (re_power x) false 0) as x2 eqn:Hx2 .
 remember (rm_final_carry x1 x2) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  remember (rm_shift_r 1 true (x1 + x2)) as x3 eqn:Hx3 .
  remember (fst_same x3 rm_ones 0) as s1 eqn:Hs1 .
  remember (fst_same (re_mant x) rm_ones 0) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s1 as [j1| ]; simpl.
   destruct Hs1 as (Hn1, Hs1).
   destruct s2 as [j2| ]; simpl.
    destruct Hs2 as (Hn2, Hs2).
    rewrite Hx3, Hx1, Hx2 in Hs1; simpl in Hs1.
    destruct (lt_dec j1 1) as [H3| H3].
     apply Nat.lt_1_r in H3; subst j1; simpl.
     clear Hs1 Hn1.
     unfold rm_final_carry in Hc; simpl in Hc.
     remember (fst_same x1 x2 0) as s3 eqn:Hs3 .
     apply fst_same_sym_iff in Hs3; simpl in Hs3.
     destruct s3 as [j3| ]; [ idtac | clear Hc ].
      destruct Hs3 as (Hn3, Hs3).
      rewrite Hc in Hs3; symmetry in Hs3.
bbb.

Theorem re_add_0_r : ∀ x, (x + 0 = x)%R.
Proof.
intros x.
unfold re_eq.
split.
bbb.

Close Scope nat_scope.
