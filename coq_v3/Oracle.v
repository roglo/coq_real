(* Oracle able to find the index of the first true of an boolean sequence
   or None if all falses *)

Require Import Utf8.

Parameter fst_true : (nat → bool) → option nat.
Axiom fst_true_iff : ∀ u odi, odi = fst_true u ↔
  match odi with
  | Some i => (∀ j, j < i → u j = false) ∧ u i = true
  | None => (∀ j, u j = false)
  end.
