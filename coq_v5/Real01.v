Require Import Utf8.

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
