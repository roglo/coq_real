Require Import Utf8 Arith.

Notation "x < y <= z" := (x < y ∧ y <= z) (at level 70, y at next level).
Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y < z" := (x <= y ∧ y < z)%nat (at level 70, y at next level).

Theorem Nat_le_neq_lt : ∀ a b, a ≤ b → a ≠ b → a < b.
Proof.
intros a b Hab Hnab.
apply le_lt_eq_dec in Hab.
destruct Hab as [Hle| Heq]; [ assumption | idtac ].
exfalso; apply Hnab; assumption.
Qed.

Theorem list_Forall_inv : ∀ A (P : A → Prop) a l,
  List.Forall P (a :: l) → P a ∧ List.Forall P l.
Proof.
intros A P a l H.
inversion H; split; assumption.
Qed.
