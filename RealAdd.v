Require Import Utf8 QArith.
Require Import Real01Add.

Set Implicit Arguments.

Open Scope Z_scope.

Record real := mkre { re_int : Z; re_frac : real_mod_1 }.
Arguments mkre _%Z _%rm.

Delimit Scope R_scope with R.
Arguments re_int _%R.
Arguments re_frac _%R.

Definition rm_final_carry x y :=
  match fst_same x y 0 with
  | Some j => if x.[j] then 1 else 0
  | None => 1
  end.
Arguments rm_final_carry x%rm y%rm.

Definition re_add x y :=
  {| re_int := re_int x + re_int y + rm_final_carry (re_frac x) (re_frac y);
     re_frac := rm_add (re_frac x) (re_frac y) |}.
Arguments re_add x%R y%R.

Definition re_zero := {| re_int := 0; re_frac := rm_zero |}.

Notation "x + y" := (re_add x y) : R_scope.
Notation "0" := re_zero : R_scope.

Definition re_norm x :=
  {| re_int := re_int x + rm_final_carry (re_frac x) 0;
     re_frac := (re_frac x + 0)%rm |}.
Arguments re_norm x%R.

Definition re_eq x y :=
  re_int (re_norm x) = re_int (re_norm y) ∧
  (re_frac x = re_frac y)%rm.
Arguments re_eq x%R y%R.

Definition re_opp x :=
  if rm_zerop (re_frac x) then {| re_int := - re_int x; re_frac := 0%rm |}
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

Theorem rm_final_carry_comm : ∀ x y, rm_final_carry x y = rm_final_carry y x.
Proof.
intros x y.
unfold rm_final_carry.
rewrite fst_same_comm.
remember (fst_same y x (0)) as s eqn:Hs .
destruct s as [di| ]; [ idtac | reflexivity ].
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct Hs as (_, Hs).
rewrite Hs; reflexivity.
Qed.

Theorem rm_final_carry_comm_l : ∀ x y z,
  rm_final_carry (x + y) z = rm_final_carry (y + x) z.
Proof.
intros x y z.
unfold rm_final_carry; simpl.
remember (fst_same (x + y) z 0) as s1 eqn:Hs1 .
remember (fst_same (y + x) z 0) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [j1| ].
 destruct Hs1 as (Hn1, Hs1).
 destruct s2 as [j2| ].
  destruct Hs2 as (Hn2, Hs2).
  destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
   apply Hn2 in H1.
   rewrite rm_add_i_comm, Hs1 in H1; symmetry in H1.
   exfalso; revert H1; apply no_fixpoint_negb.

   subst j2.
   rewrite Hs1, Hs2; reflexivity.

   apply Hn1 in H1.
   rewrite rm_add_i_comm, Hs2 in H1; symmetry in H1.
   exfalso; revert H1; apply no_fixpoint_negb.

  rewrite rm_add_i_comm, Hs2 in Hs1.
  exfalso; revert Hs1; apply no_fixpoint_negb.

 destruct s2 as [j2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Hs2).
 rewrite rm_add_i_comm, Hs1 in Hs2.
 exfalso; revert Hs2; apply no_fixpoint_negb.
Qed.

Theorem re_add_comm : ∀ x y, (x + y = y + x)%R.
Proof.
intros x y.
unfold re_eq.
unfold re_add; simpl; split; [ idtac | apply rm_add_comm ].
f_equal; [ idtac | apply rm_final_carry_comm_l ].
rewrite rm_final_carry_comm; f_equal.
apply Z.add_comm.
Qed.

(* neutral element *)

Theorem rm_final_carry_norm_add_0_r : ∀ x, rm_final_carry (x + 0%rm) 0 = 0.
Proof.
intros x.
unfold rm_final_carry; simpl.
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
rewrite rm_final_carry_norm_add_0_r, Z.add_0_r.
reflexivity.
Qed.

(* opposite *)

Theorem re_sub_diag : ∀ x, (x - x = 0)%R.
Proof.
intros x.
unfold re_eq, re_sub, re_opp; simpl.
destruct (rm_zerop (re_frac x)) as [H1| H1].
 unfold re_add; simpl.
 rewrite Z.add_opp_r, Z.sub_diag, Z.add_0_l.
 split; [ idtac | rewrite rm_add_0_r; assumption ].
 rewrite rm_final_carry_norm_add_0_r, Z.add_0_r.
bbb.

Close Scope Z_scope.
