(* Real between 0 and 1, i.e. fractional part of a real. *)

Require Import Utf8 Arith.

(* Digits *)

Class radix := { rad : nat; radi : rad ≥ 2 }.
Record digit {r : radix} := { dig : nat; digi : dig < rad }.

Delimit Scope digit_scope with D.

Definition digit_eq {r : radix} (a b : digit) := dig a = dig b.
Notation "a = b" := (digit_eq a b) : digit_scope.
Notation "a ≠ b" := (¬ digit_eq a b) : digit_scope.

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

Theorem digit_eq_dec {r : radix} : ∀ a b, {(a = b)%D} + {(a ≠ b)%D}.
Proof.
intros.
destruct (Nat.eq_dec (dig a) (dig b)) as [Hab| Hab]; [ now left | right ].
intros H.
apply digit_eq_eq in H; subst b.
now apply Hab.
Qed.

(* Oracle Limited Principle of Omniscience *)

Axiom OLPO : ∀ (u : nat → nat), (∀ i, u i = O) + { i : nat | u i ≠ O }.

Fixpoint first_such_that (P : nat → bool) n i :=
  match n with
  | O => i
  | S n' => if P i then i else first_such_that P n' (S i)
  end.

...

(* Frac Real *)

Record FracReal {r : radix} := { freal : nat → digit }.

Definition frac_real_eq {r : radix} (a b : FracReal) :=
  match OLPO

  ∀ i, freal a i = freal b i.
