(* Real between 0 and 1, i.e. fractional part of a real. *)

Require Import Utf8 Arith.

Class radix := { rad : nat; radi : rad ≥ 2 }.
Record digit {r : radix} := { dig : nat; digi : dig < rad }.
Record FracReal {r : radix} := { freal : nat → digit }.

Delimit Scope digit_scope with D.

Definition digit_eq {r : radix} (a b : digit) := dig a = dig b.
Notation "a = b" := (digit_eq a b) : digit_scope.

Theorem digit_eq_eq {r : radix} : ∀ a b, (a = b)%D ↔ a = b.
Proof.
intros.
split; intros H; [ | now subst ].
destruct a as (adig, adigi).
destruct b as (bdig, bdigi).
unfold digit_eq in H; simpl in H.
subst bdig.
f_equal.
apply le_unique.
Qed.
