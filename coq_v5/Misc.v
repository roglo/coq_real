Require Import Utf8 Arith NPeano.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).
Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y < z" := (x <= y ∧ y < z)%nat (at level 70, y at next level).

Theorem Nat_le_neq_lt : ∀ a b, a ≤ b → a ≠ b → a < b.
Proof.
intros a b Hab Hnab.
apply le_lt_eq_dec in Hab.
destruct Hab as [Hle| Heq]; [ assumption | idtac ].
exfalso; apply Hnab; assumption.
Qed.

Theorem Nat_sub_add_r : ∀ a b c,
  a < b
  → c = b - S a
  → b = a + S c.
Proof.
intros a b c Hab Hc; subst c.
rewrite <- Nat.sub_succ_l; [ simpl | assumption ].
rewrite Nat.add_sub_assoc; [ idtac | apply Nat.lt_le_incl; assumption ].
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Theorem Nat_le_sub_add_r : ∀ a b c,
  a ≤ b
  → c = b - a
  → b = a + c.
Proof.
intros a b c Hab Hc; subst c.
rewrite Nat.add_sub_assoc; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Theorem all_lt_all : ∀ P : nat → Prop,
  (∀ n, (∀ m, (m < n)%nat → P m) → P n)
  → ∀ n, P n.
Proof.
intros P Hm n.
apply Hm.
induction n; intros m Hmn.
 apply Nat.nle_gt in Hmn.
 exfalso; apply Hmn, Nat.le_0_l.

 destruct (eq_nat_dec m n) as [H1| H1].
  subst m; apply Hm; assumption.

  apply IHn.
  apply Nat_le_neq_lt; [ idtac | assumption ].
  apply Nat.succ_le_mono; assumption.
Qed.
