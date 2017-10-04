(* Real between 0 and 1, i.e. fractional part of a real. *)

Require Import Utf8 Arith.
Require Import Misc.

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

Theorem first_such_that_has_prop : ∀ u n i k,
  u (n + i) ≠ 0
  → k = first_such_that (λ j, negb (Nat.eqb (u j) 0)) n i
  → u k ≠ 0 ∧ (∀ j, i ≤ j → j < k → u j = 0).
Proof.
intros * Hn Hk.
revert i k Hn Hk; induction n; intros.
 split; [ now subst k | simpl ].
 simpl in Hk; destruct Hk; intros j H1 H2.
 apply lt_not_le in H2; exfalso; apply H2, H1.

 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hn.
 simpl in Hk.
 remember (u i =? 0) as b eqn:Hb.
 symmetry in Hb.
 destruct b; simpl in Hk.
  apply Nat.eqb_eq in Hb.
  specialize (IHn (S i) k Hn Hk).
  destruct IHn as (H2, H3).
  split; [ apply H2 | intros j H4 H5 ].
  destruct (Nat.eq_dec i j) as [H6| H6]; [ now destruct H6 | ].
  apply H3; [ | easy ].
  apply Nat_le_neq_lt.
bbb.


 destruct (fld_zerop (u i)) as [H1| H1].
  pose proof IHn (S i) k Hn Hk as H2.
  destruct H2 as (H2, H3).
  split; [ apply H2 | intros j (H4, H5) ].
  destruct (eq_nat_dec i j) as [H6| H6]; [ destruct H6; assumption | ].
  apply H3; split; [ | assumption ].
  apply Nat_le_neq_lt; assumption.

  destruct Hk; split; [ assumption | ].
  intros j (H2, H3).
  apply lt_not_le in H3; exfalso; apply H3, H2.
Qed.

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
(**)
 destruct i; [ now subst j | ].
 simpl in Hj.
 remember (u 0 =? 0) as b eqn:Hb.
 symmetry in Hb.
 destruct b; simpl in Hj; [ | now subst j ].
 apply Nat.eqb_eq in Hb.
(**)
 remember 1 as n eqn:Hn in Hj.
 destruct i; simpl in Hj.
  subst j.
  destruct k; [ easy | ].
  now subst n; apply Nat.succ_lt_mono in Hk.

  remember (u n =? 0) as b1 eqn:Hb1.
  symmetry in Hb1.
  destruct b1; simpl in Hj.
   Focus 2.
   apply Nat.eqb_neq in Hb1.
   subst j.
   destruct k; [ easy | ].
   now subst n; apply Nat.succ_lt_mono in Hk.

   apply Nat.eqb_eq in Hb1.
(**)
   destruct i; simpl in Hj.
    subst j.
    destruct k; [ easy | ].
    apply Nat.succ_lt_mono in Hk.
    destruct k; [ easy | ].
    now apply Nat.succ_lt_mono in Hk.

    remember (u 2 =? 0) as b2 eqn:Hb2.
    symmetry in Hb2.
    destruct b2; simpl in Hj.
     Focus 2.
     apply Nat.eqb_neq in Hb2.
     subst j.
     destruct k; [ easy | ].
     apply Nat.succ_lt_mono in Hk.
     destruct k; [ easy | ].
     now apply Nat.succ_lt_mono in Hk.

     apply Nat.eqb_eq in Hb2.
(**)
     destruct i; simpl in Hj.
bbb.
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
 subst j.
 destruct i; simpl in Hk; simpl.
  now apply Nat.succ_lt_mono in Hk.

(* ouais, bon, faut generaliser le machin *)
bbb.


destruct i.
 simpl in Hj.
 rewrite Hj in Hk.
 now apply Nat.succ_lt_mono in Hk.

 destruct i.
  simpl in Hj.
  remember (u 1 =? 0) as b1 eqn:Hb1.
  symmetry in Hb1.
  destruct b1; simpl in Hj.
  apply Nat.eqb_eq in Hb1.
  subst j.
  apply Nat.succ_lt_mono in Hk.
  destruct k; [ easy | ].
  now apply Nat.succ_lt_mono in Hk.
  subst j.
  now apply Nat.succ_lt_mono in Hk.

  destruct i.
   simpl in Hj.
   remember (u 1 =? 0) as b1 eqn:Hb1.
   symmetry in Hb1.
   destruct b1; simpl in Hj.
    apply Nat.eqb_eq in Hb1.
    remember (u 2 =? 0) as b2 eqn:Hb2.
    symmetry in Hb2.
    destruct b2; simpl in Hj.
     apply Nat.eqb_eq in Hb2.
     subst j.
     apply Nat.succ_lt_mono in Hk.
     destruct k; [ easy | ].
     destruct k; [ easy | ].
     now do 2 apply Nat.succ_lt_mono in Hk.

     apply Nat.eqb_neq in Hb2.
     subst j.
     apply Nat.succ_lt_mono in Hk.
     destruct k; [ easy | ].
     now apply Nat.succ_lt_mono in Hk.

    apply Nat.eqb_neq in Hb1.
    subst j.
    now apply Nat.succ_lt_mono in Hk.

bbb.

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
*)
