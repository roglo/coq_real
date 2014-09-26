Require Import Utf8 QArith.

Require Import Nbar.

Open Scope nat_scope.

(* reals modulo 1 *)
Record real_mod_1 := { rm : nat → bool }.

Axiom fst_00 x y i : real_mod_1 → real_mod_1 → nat → Nbar.

Axiom fst_00_iff : ∀ x y i di,
  fst_00 x y i = di ↔
  match di with
  | fin di =>
      (∀ dj, dj < di → rm x (i + dj) = true ∨ rm y (i + dj) = true)
      ∧ rm x (i + di) = false ∧ rm y (i + di) = false
  | ∞ =>
      ∀ dj, rm x (i + dj) = true ∨ rm y (i + dj) = true
  end.

Fixpoint sum_carry x y i di c :=
  match di with
  | O => c
  | S di' =>
      let xi := rm x (i + di') in
      let yi := rm y (i + di') in
      let c' := c && xi || xi && yi || yi && c in
      sum_carry x y i di' c'
  end.

Definition rm_add x y i :=
  match fst_00 x y i with
  | fin di => sum_carry x y i di false
  | ∞ => false (* à voir *)
  end.

Close Scope nat_scope.
