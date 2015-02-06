Require Import Utf8 NPeano.

(* I = interval [0..1] of ℝ *)
Record I := { rm : nat → bool }.

Definition I_zero := {| rm i := false |}.
Definition I_one := {| rm i := true |}.

Notation "s .[ i ]" := (rm s i) (at level 15, i at level 200).

Delimit Scope I_scope with I.
Notation "0" := I_zero : I_scope.
Notation "1" := I_one : I_scope.

Definition d2n (d : bool) := if d then 1 else 0.
Definition n2d (n : nat) := Nat.eqb n 0.

Record SeqNat := { sn : nat → nat }.

Definition propag_carry_once s := {| sn i := sn s i mod 2 + sn s (S i) / 2 |}.

Fixpoint I_propag_carry n u :=
  match n with
  | 0 => u
  | S n1 => propag_carry_once (I_propag_carry n1 u)
  end.

Definition I_eq_ext x y := ∀ i, x.[i] = y.[i].
Arguments I_eq_ext x%I y%I.
