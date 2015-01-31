(* Oracle able to find the index of the first true of an boolean sequence
   or None if all falses *)

Require Import Utf8 Bool Arith.

Record Un := { u : nat → bool }.

Parameter fst_true : Un → option nat.
Axiom fst_true_iff : ∀ x odi, odi = fst_true x ↔
  match odi with
  | Some i => (∀ j, j < i → u x j = false) ∧ u x i = true
  | None => (∀ j, u x j = false)
  end.
