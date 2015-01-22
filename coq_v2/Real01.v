Require Import Utf8.

Set Implicit Arguments.

(* I = interval [0..1] of ℝ *)
(* representation by sequences of bits *)
Record I := { idig : nat → bool }.

(* represention by sequences of naturals *)
Record Iwn := { inat : nat → nat }.

Open Scope nat_scope.

Parameter fst_not_1 : Iwn → nat → option nat.
Axiom fst_not_1_iff : ∀ x i odi, odi = fst_not_1 x i ↔
  match odi with
  | Some di =>
      (∀ dj, dj < di → inat x (i + dj) = 1)
      ∧ inat x (i + di) ≠ 1
  | None =>
      ∀ dj, inat x (i + dj) = 1
  end.

Notation "x .[ i ]" := (idig x i) (at level 15, i at level 200).
Infix "⊕" := xorb (left associativity, at level 50) : bool_scope.

Delimit Scope I_scope with I.

Close Scope nat_scope.
