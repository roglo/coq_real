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
(* Borrowed from my proof of Puiseux's Theorem *)

Axiom O_LPO : ∀ (u : nat → nat), (∀ i, u i = O) + { i : nat | u i ≠ O }.

Fixpoint first_such_that (P : nat → bool) n i :=
  match n with
  | O => i
  | S n' => if P i then i else first_such_that P n' (S i)
  end.

Theorem O_LPO_fst : ∀ (u : nat → nat),
  (∀ i, u i = O) +
  { i : nat | (∀ j, j < i → u j = 0) ∧ u i ≠ O }.
Proof.
intros.
specialize (O_LPO u) as [H| (i, Hi)]; [ now left | right ].
remember (first_such_that (λ i, negb (Nat.eqb (u i) 0)) i 0) as j eqn:Hj.
exists j.
split.
 intros k Hk.
 revert u k Hi Hj Hk.
 induction i; intros; [ now subst j | ].
 simpl in Hj.
 remember (u 0 =? 0) as b eqn:Hb.
 symmetry in Hb.
 destruct b; [ | now subst j ].
 simpl in Hj.
 apply Nat.eqb_eq in Hb.
 destruct k; [ easy | ].
 apply IHi with (u := λ i, u (S i)); [ easy | | now apply Nat.lt_succ_l ].
 destruct i.
  rewrite Hj in Hk; simpl in Hk.
  now apply Nat.succ_lt_mono in Hk.

  simpl in Hj; simpl.
(* faut que je réfléchisse... *)
bbb.

 set (v i := u (S i)).
 specialize (IHi v k Hi).

bbb.

(* Frac Real *)

Record FracReal {r : radix} := { freal : nat → digit }.

Definition frac_real_eq {r : radix} (a b : FracReal) :=
  match OLPO
