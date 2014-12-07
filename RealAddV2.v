Require Import Utf8 QArith NPeano.
Require Import Real01Add.

Set Implicit Arguments.

Open Scope Z_scope.

Record real := { re_int : Z; re_frac : real_mod_1 }.

Delimit Scope R_scope with R.
Arguments re_int _%R.
Arguments re_frac _%R.

Definition rm_final_carry x y :=
  match fst_same x y 0 with
  | Some j => if x.[j] then 1 else 0
  | None => 1
  end.

Definition re_add x y :=
  {| re_int := re_int x + re_int y + rm_final_carry (re_frac x) (re_frac y);
     re_frac := rm_add (re_frac x) (re_frac y) |}.
Arguments re_add x%R y%R.

Definition re_zero := {| re_int := 0; re_frac := rm_zero |}.

Notation "x + y" := (re_add x y) : R_scope.
Notation "0" := re_zero : R_scope.

Definition re_norm x :=
  {| re_int := re_int x; re_frac := (re_frac x + 0)%rm |}.
Arguments re_norm x%R.

Definition re_eq x y := re_int x = re_int y ∧ (re_frac x = re_frac y)%rm.
Arguments re_eq x%R y%R.

Notation "x = y" := (re_eq x y) : R_scope.

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

Theorem re_add_comm : ∀ x y, (x + y = y + x)%R.
Proof.
intros x y.
unfold re_eq.
unfold re_add; simpl; split; [ idtac | apply rm_add_comm ].
f_equal; [ apply Z.add_comm | idtac ].
apply rm_final_carry_comm.
Qed.

(* neutral element *)
(* TODO *)

Close Scope Z_scope.
