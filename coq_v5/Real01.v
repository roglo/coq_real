Require Import Utf8 QArith.

(* I = interval [0..1] of ℝ *)
Record I := { rm : nat → bool }.

Definition I_zero := {| rm i := false |}.
Definition I_one := {| rm i := true |}.

Notation "s .[ i ]" := (rm s i) (at level 15, i at level 200).

Delimit Scope I_scope with I.
Notation "0" := I_zero : I_scope.
Notation "1" := I_one : I_scope.

Definition I_eq_ext x y := ∀ i, x.[i] = y.[i].
Arguments I_eq_ext x%I y%I.

(* actually, I think that I_eq_ext is equivalent to I_eqs in Real01Cmp.v
   something should be done to unify these definitions *)

Theorem I_eq_ext_refl : reflexive _ I_eq_ext.
Proof. intros x i; reflexivity. Qed.

Theorem I_eq_ext_sym : symmetric _ I_eq_ext.
Proof.
intros x y Hxy i.
rewrite Hxy; reflexivity.
Qed.

Theorem I_eq_ext_trans : transitive _ I_eq_ext.
Proof.
intros x y z Hxy Hyz i.
rewrite Hxy, Hyz; reflexivity.
Qed.

Add Parametric Relation : _ I_eq_ext
 reflexivity proved by I_eq_ext_refl
 symmetry proved by I_eq_ext_sym
 transitivity proved by I_eq_ext_trans
 as I_eq_ext_rel.
