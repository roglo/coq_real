(* definition ℝ *)

Require Import ZArith.

Require Import Real01.

Record ℝ := mkre { R_int : Z; R_frac : I }.
Arguments mkre _%Z _%I.

Definition R_zero := {| R_int := 0; R_frac := I_zero |}.
Definition R_one := {| R_int := 1; R_frac := I_zero |}.

Delimit Scope R_scope with R.
Arguments R_int _%R.
Arguments R_frac _%R.

Notation "0" := R_zero : R_scope.
Notation "1" := R_one : R_scope.
