(* Oracle able to find the index of the first non-zero value of an integer
   sequence or None if not found *)

Require Import Utf8 Bool Arith.

Record Un := { u : nat → nat }.

Parameter fst_not_0 : Un → option nat.
Axiom fst_not_0_iff : ∀ x odi, odi = fst_not_0 x ↔
  match odi with
  | Some i => (∀ j, j < i → u x j = 0) ∧ u x i ≠ 0
  | None => (∀ j, u x j = 0)
  end.
