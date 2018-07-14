(* diff between two nats *)

Require Import Utf8 Arith.
Set Nested Proofs Allowed.

Fixpoint diff a b :=
  match a with
  | 0 => b
  | S a' =>
      match b with
      | 0 => a
      | S b' => diff a' b'
      end
  end.

Notation "a 'Δ' b" := (diff a b) (at level 50).

Theorem diff_comm : ∀ a b, a Δ b = b Δ a.
Proof.
intros.
revert b.
induction a; intros; [ now destruct b | ].
destruct b; [ easy | apply IHa ].
Qed.

Theorem diff_0_l : ∀ a, 0 Δ a = a.
Proof. easy. Qed.

Theorem diff_diag : ∀ a, a Δ a = 0.
Proof. now intros a; induction a. Qed.

Theorem diff_add_cancel_l : ∀ a b c, (a + b) Δ (a + c) = b Δ c.
Proof.
intros.
revert b c.
induction a; intros; [ easy | apply IHa ].
Qed.

Theorem mul_diff_distr_l : ∀ a b c, a * (b Δ c) = a * b Δ a * c.
Proof.
intros.
revert a c.
induction b; intros; [ now rewrite Nat.mul_0_r | ].
destruct c; simpl.
-rewrite Nat.mul_0_r.
 now rewrite diff_comm, diff_0_l.
-setoid_rewrite Nat.mul_comm; simpl.
 rewrite Nat.mul_comm, IHb.
 rewrite diff_add_cancel_l.
 f_equal; apply Nat.mul_comm.
Qed.
