(* addition in ℝ *)

Require Import Utf8 QArith NPeano.
Require Import Real01 Real01Add.
Require Import Real.

Set Implicit Arguments.

Open Scope Z_scope.

Definition b2z (b : bool) := if b then 1 else 0.

Definition R_add x y :=
  {| R_int := R_int x + R_int y + b2z (carry (R_frac x) (R_frac y) 0);
     R_frac := I_add (R_frac x) (R_frac y) |}.
Arguments R_add x%R y%R.

Notation "x + y" := (R_add x y) : R_scope.

Definition R_norm x :=
  {| R_int := R_int x + b2z (carry (R_frac x) 0 0);
     R_frac := (R_frac x + 0)%I |}.
Arguments R_norm x%R.

Definition R_eq x y :=
  R_int (R_norm x) = R_int (R_norm y) ∧
  (R_frac x = R_frac y)%I.
Arguments R_eq x%R y%R.

Definition R_opp x := {| R_int := - R_int x - 1; R_frac := - R_frac x |}.
Definition R_sub x y := R_add x (R_opp y).
Arguments R_opp x%R.
Arguments R_sub x%R y%R.

Definition R_is_neg x := Z.ltb (R_int x) 0.
Definition R_abs x := if R_is_neg x then R_opp x else x.
Arguments R_abs x%R.
Arguments R_is_neg x%R.

Notation "x = y" := (R_eq x y) : R_scope.
Notation "x ≠ y" := (¬ R_eq x y) : R_scope.
Notation "- x" := (R_opp x) : R_scope.
Notation "x - y" := (R_sub x y) : R_scope.

Theorem fold_R_sub : ∀ x y, (x + - y)%R = (x - y)%R.
Proof. intros; reflexivity. Qed.

(* equality is equivalence relation *)

Theorem R_eq_refl : reflexive _ R_eq.
Proof.
intros x; split; reflexivity.
Qed.

Theorem R_eq_sym : symmetric _ R_eq.
Proof.
intros x y Hxy.
unfold R_eq in Hxy; unfold R_eq.
destruct Hxy; split; symmetry; assumption.
Qed.

Theorem R_eq_trans : transitive _ R_eq.
Proof.
intros x y z Hxy Hyz.
destruct Hxy, Hyz.
unfold R_eq.
split; etransitivity; eassumption.
Qed.

Add Parametric Relation : _ R_eq
 reflexivity proved by R_eq_refl
 symmetry proved by R_eq_sym
 transitivity proved by R_eq_trans
 as R_rel.

Close Scope Z_scope.
