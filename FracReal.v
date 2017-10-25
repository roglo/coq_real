(* Real between 0 and 1, i.e. fractional part of a real. *)

Require Import Utf8 Arith Psatz.
Require Import Misc Summation.

(* Radix *)

Class radix := { rad : nat; radi : rad ≥ 2 }.

Theorem radix_gt_0 {r : radix} : rad > 0.
Proof.
destruct r as (rad, radi); simpl; lia.
Qed.

Theorem radix_ne_0 {r : radix} : rad ≠ 0.
Proof.
destruct r as (rad, radi); simpl; lia.
Qed.

(* Digits *)

Record digit {r : radix} := mkdig { dig : nat; digi : dig < rad }.

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
 now apply lt_not_le in H2.

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
  now apply Nat_le_neq_lt.

  apply Nat.eqb_neq in Hb.
  subst k; split; [ easy | ].
  intros j H2 H3.
  now apply lt_not_le in H3.
Qed.

Theorem O_LPO_fst : ∀ (u : nat → nat),
  (∀ i, u i = O) +
  { i : nat | (∀ j, j < i → u j = 0) ∧ u i ≠ O }.
Proof.
intros.
specialize (O_LPO u) as [H| (i, Hi)]; [ now left | right ].
remember (first_such_that (λ i, negb (Nat.eqb (u i) 0)) i 0) as j eqn:Hj.
exists j.
assert (Hui : u (i + 0) ≠ 0) by now rewrite Nat.add_0_r.
specialize (first_such_that_has_prop u i 0 j Hui Hj) as (Huj, H).
split; [ | easy ].
intros k Hkj.
apply H; [ apply Nat.le_0_l | easy ].
Qed.

(* Frac Real *)

Delimit Scope freal_scope with F.

Record FracReal {r : radix} := { freal : nat → digit }.

Definition digit_sequence_normalize {r : radix} (u : nat → digit) i :=
  match O_LPO (λ j : nat, rad - 1 - dig (u (i + j + 1))) with
  | inl _ =>
      let s := lt_dec (S (dig (u i))) rad in
      match s with
      | left P => {| dig := S (dig (u i)); digi := P |}
      | right _ => {| dig := 0; digi := radix_gt_0 |}
      end
  | inr _ => u i
 end.

Definition freal_normalize {r : radix} x :=
  {| freal := digit_sequence_normalize (freal x) |}.

Arguments freal_normalize r x%F.

Definition freal_normalized_eq {r : radix} x y :=
  match O_LPO (λ i, dig (freal x i) - dig (freal y i)) with
  | inl _ => true
  | inr _ => false
  end.

Definition freal_eq {r : radix} x y :=
  freal_normalized_eq (freal_normalize x) (freal_normalize y).

Notation "a = b" := (freal_eq a b = true) : freal_scope.
Notation "a ≠ b" := (freal_eq a b = false) : freal_scope.

(* Addition, Multiplication *)

Definition sequence_add (a b : nat → nat) i := a i + b i.
Definition sequence_mul (a b : nat → nat) i := Σ (j = 0, i), a j * b (i - j).

Definition freal_add_series {r : radix} a b :=
  sequence_add (λ i, dig (freal a i)) (λ i, dig (freal b i)).

Definition freal_mul_series {r : radix} a b i :=
  match i with
  | 0 => 0
  | S i' => sequence_mul (λ i, dig (freal a i)) (λ i, dig (freal b i)) i'
  end.

Record rational := mkrat { num : nat; den : nat }.

Definition rint q := num q / den q.
Definition rfrac q := mkrat (num q mod den q) (den q).

Definition A {r : radix} i u n :=
  mkrat
    (Σ (j = i + 1, n - 1), u j * rad ^ (n - 1 - j))
    (rad ^ (n - 1 - i)).

Definition mul_test_seq {r : radix} i u k :=
  let n := rad * (i + k + 2) in
  if le_dec (pred (rad ^ k))
    (rad ^ k * num (rfrac (A i u n)) / den (rfrac (A i u n)))
  then 0
  else 1.

Definition freal_mul_to_seq {r : radix} (a b : FracReal) i :=
  let u := freal_mul_series a b in
  match O_LPO (mul_test_seq i u) with
  | inl _ =>
      let n := rad * (i + 2) in
      (u i + rint (A i u n) + 1) mod rad
  | inr (exist _ j _) =>
      let n := rad * (i + j + 2) in
      (u i + rint (A i u n)) mod rad
  end.

Theorem freal_mul_to_seq_lt_rad {r : radix} : ∀ a b i,
  freal_mul_to_seq a b i < rad.
Proof.
intros.
unfold freal_mul_to_seq.
remember (mul_test_seq i (freal_mul_series a b)) as v eqn:Hv.
destruct (O_LPO v) as [Hvi| (j, Hvj)].
1, 2: apply Nat.mod_upper_bound, radix_ne_0.
Qed.

Definition freal_mul {r : radix} (a b : FracReal) :=
  let u := freal_mul_to_seq a b in
  {| freal i := mkdig r (u i) (freal_mul_to_seq_lt_rad a b i) |}.

Notation "a * b" := (freal_mul a b) : freal_scope.

Theorem sequence_mul_comm : ∀ f g i, sequence_mul f g i = sequence_mul g f i.
Proof.
intros.
unfold sequence_mul.
revert f g.
induction i; intros.
 do 2 rewrite summation_only_one; simpl.
 apply Nat.mul_comm.

 rewrite summation_split_last; [ symmetry | lia ].
 rewrite summation_split_first; [ symmetry | lia ].
 rewrite Nat.sub_0_r, Nat.sub_diag.
 rewrite Nat.add_comm; f_equal; [ lia | ].
 rewrite summation_succ_succ.
 rewrite <- IHi.
 apply summation_eq_compat; intros j Hj.
 now rewrite <- Nat.sub_succ_l.
Qed.

Theorem freal_mul_series_comm {r : radix} : ∀ x y i,
  freal_mul_series x y i = freal_mul_series y x i.
Proof.
intros.
unfold freal_mul_series.
destruct i; [ easy | ].
apply sequence_mul_comm.
Qed.

Theorem normalize_freal_mul_comm {r : radix} : ∀ x y : FracReal,
  ∀ i, freal (freal_normalize (x * y)) i = freal (freal_normalize (y * x)) i.
Proof.
intros.
unfold freal_normalize.
remember (freal (x * y)%F) as xy.
remember (freal (y * x)%F) as yx.
simpl.
unfold digit_sequence_normalize.
destruct (O_LPO (λ j : nat, rad - 1 - dig (xy (i + j + 1)))) as [Hxy| Hxy].
 destruct (O_LPO (λ j : nat, rad - 1 - dig (yx (i + j + 1)))) as [Hyx| Hyx].
  destruct (lt_dec (S (dig (xy i))) rad) as [Hrxy| Hrxy].
   destruct (lt_dec (S (dig (yx i))) rad) as [Hryx| Hryx].
    apply digit_eq_eq; unfold digit_eq; simpl.
    subst xy yx.
    f_equal; f_equal.
    apply digit_eq_eq; unfold digit_eq; simpl.
    unfold freal_mul_to_seq.
    destruct (O_LPO (mul_test_seq i (freal_mul_series x y))) as [Hfxy| Hfxy].
     destruct (O_LPO (mul_test_seq i (freal_mul_series y x))) as [Hfyx| Hfyx].
      f_equal; f_equal.
      rewrite freal_mul_series_comm; f_equal; f_equal.
      unfold A; f_equal.
      apply summation_eq_compat; intros j Hji.
      f_equal; apply freal_mul_series_comm.

      destruct Hfyx as (h, Hfyx).
bbb.

Theorem freal_mul_comm {r : radix} : ∀ x y : FracReal, (x * y = y * x)%F.
Proof.
intros.
unfold freal_eq.
unfold freal_normalized_eq.
bbb.
