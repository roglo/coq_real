(* Real between 0 and 1, i.e. fractional part of a real. *)

Require Import Utf8.

Class radix := { rad : nat; radi : rad ≥ 2 }.
Record digit {r : radix} := { dig : nat; digi : dig < rad }.
Record FracReal {r : radix} := { freal : nat → digit }.

Definition digit_cmp {r : radix} (a b : digit) := dig a = dig b.

Theorem digit_cmp_eq {r : radix} : ∀ a b, digit_cmp a b ↔ a = b.
Proof.
intros.
split; intros H; [ | now subst ].
destruct a as (adig, adigi).
destruct b as (bdig, bdigi).
unfold digit_cmp in H; simpl in H.
subst bdig.
f_equal.
