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

Definition digit_0 {r : radix} := mkdig _ 0 radix_gt_0.
Definition digit_eq {r : radix} (a b : digit) := dig a = dig b.

Notation "0" := (digit_0) : digit_scope.
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

Axiom LPO : ∀ (u : nat → nat), (∀ i, u i = O) + { i : nat | u i ≠ O }.

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

Theorem LPO_fst : ∀ (u : nat → nat),
  (∀ i, u i = O) +
  { i : nat | (∀ j, j < i → u j = 0) ∧ u i ≠ O }.
Proof.
intros.
specialize (LPO u) as [H| (i, Hi)]; [ now left | right ].
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
Arguments freal r _%F.

Definition digit_sequence_normalize {r : radix} (u : nat → digit) i :=
  match LPO_fst (λ j : nat, rad - 1 - dig (u (i + j + 1))) with
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

Definition eq_freal_seq {r : radix} x y i :=
  if Nat.eq_dec (dig (freal x i)) (dig (freal y i)) then 0 else 1.

Definition freal_normalized_eq {r : radix} x y :=
  match LPO_fst (eq_freal_seq x y) with
  | inl _ => true
  | inr _ => false
  end.

Definition freal_normalized_lt {r : radix} x y :=
  match LPO_fst (eq_freal_seq x y) with
  | inl _ => true
  | inr (exist _ i _) =>
      if lt_dec (dig (freal x i)) (dig (freal y i)) then true
      else false
  end.

Definition freal_eq {r : radix} x y :=
  freal_normalized_eq (freal_normalize x) (freal_normalize y).

Definition freal_lt {r : radix} x y :=
  freal_normalized_lt (freal_normalize x) (freal_normalize y).

Definition freal_0 {r : radix} := {| freal i := digit_0 |}.

Notation "0" := (freal_0) : freal_scope.
Notation "a = b" := (freal_eq a b = true) : freal_scope.
Notation "a ≠ b" := (freal_eq a b = false) : freal_scope.
Notation "a < b" := (freal_lt a b = true) : freal_scope.

(* Addition, Multiplication *)

Definition sequence_add (a b : nat → nat) i := a i + b i.
Definition sequence_mul (a b : nat → nat) i := Σ (j = 0, i), a j * b (i - j).

Definition freal_add_series {r : radix} a b :=
  sequence_add (λ i, dig (freal a i)) (λ i, dig (freal b i)).

Arguments freal_add_series _ a%F b%F.

Definition freal_mul_series {r : radix} a b i :=
  match i with
  | 0 => 0
  | S i' => sequence_mul (λ i, dig (freal a i)) (λ i, dig (freal b i)) i'
  end.

Record rational := mkrat { num : nat; den : nat }.

Definition rdiv q := num q / den q.
Definition rmod q := num q mod den q.

Definition A {r : radix} i n u :=
  mkrat
    (Σ (j = i + 1, n - 1), u j * rad ^ (n - 1 - j))
    (rad ^ (n - 1 - i)).

Definition test_seq {r : radix} i u k :=
  let n := rad * (i + k + 2) in
  if le_dec (pred (rad ^ k)) (rad ^ k * rmod (A i n u) / den (A i n u)) then 0
  else 1.

Definition numbers_to_digits {r : radix} u i :=
  match LPO_fst (test_seq i u) with
  | inl _ => (u i + rdiv (A i (rad * (i + 2)) u) + 1) mod rad
  | inr (exist _ j _) => (u i + rdiv (A i (rad * (i + j + 2)) u)) mod rad
  end.

Definition freal_add_to_seq {r : radix} (a b : FracReal) :=
  numbers_to_digits (freal_add_series a b).

Arguments freal_add_to_seq _ a%F b%F.

Definition freal_mul_to_seq {r : radix} (a b : FracReal) :=
  numbers_to_digits (freal_mul_series a b).

Theorem freal_add_to_seq_lt_rad {r : radix} : ∀ a b i,
  freal_add_to_seq a b i < rad.
Proof.
intros.
unfold freal_add_to_seq, numbers_to_digits.
remember (test_seq i (freal_add_series a b)) as v eqn:Hv.
destruct (LPO_fst v) as [Hvi| (j, Hvj)].
1, 2: apply Nat.mod_upper_bound, radix_ne_0.
Qed.

Theorem freal_mul_to_seq_lt_rad {r : radix} : ∀ a b i,
  freal_mul_to_seq a b i < rad.
Proof.
intros.
unfold freal_mul_to_seq, numbers_to_digits.
remember (test_seq i (freal_mul_series a b)) as v eqn:Hv.
destruct (LPO_fst v) as [Hvi| (j, Hvj)].
1, 2: apply Nat.mod_upper_bound, radix_ne_0.
Qed.

Definition freal_add {r : radix} (a b : FracReal) :=
  let u := freal_add_to_seq a b in
  {| freal i := mkdig r (u i) (freal_add_to_seq_lt_rad a b i) |}.

Arguments freal_add _ a%F b%F.

Definition freal_mul {r : radix} (a b : FracReal) :=
  let u := freal_mul_to_seq a b in
  {| freal i := mkdig r (u i) (freal_mul_to_seq_lt_rad a b i) |}.

Notation "a + b" := (freal_add a b) : freal_scope.
Notation "a * b" := (freal_mul a b) : freal_scope.

Theorem sequence_add_comm : ∀ f g i, sequence_add f g i = sequence_add g f i.
Proof.
intros.
unfold sequence_add.
apply Nat.add_comm.
Qed.

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

Theorem freal_add_series_comm {r : radix} : ∀ x y i,
  freal_add_series x y i = freal_add_series y x i.
Proof.
intros.
unfold freal_add_series.
apply sequence_add_comm.
Qed.

Theorem freal_mul_series_comm {r : radix} : ∀ x y i,
  freal_mul_series x y i = freal_mul_series y x i.
Proof.
intros.
unfold freal_mul_series.
destruct i; [ easy | ].
apply sequence_mul_comm.
Qed.

Theorem A_freal_add_series_comm {r : radix} : ∀ x y i n,
  A i n (freal_add_series x y) = A i n (freal_add_series y x).
Proof.
intros.
unfold A; simpl; f_equal.
apply summation_eq_compat; intros j Hj.
now rewrite freal_add_series_comm.
Qed.

Theorem A_freal_mul_series_comm {r : radix} : ∀ x y i n,
  A i n (freal_mul_series x y) = A i n (freal_mul_series y x).
Proof.
intros.
unfold A; simpl; f_equal.
apply summation_eq_compat; intros j Hj.
now rewrite freal_mul_series_comm.
Qed.

Theorem test_seq_freal_add_series_comm {r : radix} : ∀ x y i k,
  test_seq i (freal_add_series x y) k =
  test_seq i (freal_add_series y x) k.
Proof.
intros.
unfold test_seq.
now rewrite A_freal_add_series_comm.
Qed.

Theorem test_seq_freal_mul_series_comm {r : radix} : ∀ x y i k,
  test_seq i (freal_mul_series x y) k =
  test_seq i (freal_mul_series y x) k.
Proof.
intros.
unfold test_seq.
now rewrite A_freal_mul_series_comm.
Qed.

Theorem freal_add_to_seq_i_comm {r : radix} : ∀ x y i,
  freal_add_to_seq x y i = freal_add_to_seq y x i.
Proof.
intros.
unfold freal_add_to_seq, numbers_to_digits.
remember (freal_add_series x y) as xy.
remember (freal_add_series y x) as yx.
destruct (LPO_fst (test_seq i xy)) as [Hxy| Hxy].
 rewrite Heqxy, freal_add_series_comm, <- Heqyx.
 destruct (LPO_fst (test_seq i yx)) as [Hyx| Hyx].
  now rewrite A_freal_add_series_comm, <- Heqyx.

  destruct Hyx as (k & Hjk & Hk).
  rewrite Heqyx, test_seq_freal_add_series_comm, <- Heqxy in Hk.
  now rewrite Hxy in Hk.

 destruct Hxy as (k & Hjk & Hk).
 rewrite Heqxy, test_seq_freal_add_series_comm, <- Heqyx in Hk.
 destruct (LPO_fst (test_seq i yx)) as [Hyx| Hyx].
  now rewrite Hyx in Hk.

  destruct Hyx as (l & Hjl & Hl).
  destruct (lt_eq_lt_dec k l) as [ [ Hkl | Hkl ] | Hkl ].
   now apply Hjl in Hkl; subst xy.

   rewrite Heqxy, freal_add_series_comm, <- Heqyx.
   rewrite A_freal_add_series_comm, <- Heqyx.
   now subst k.

   apply Hjk in Hkl.
   now rewrite Heqxy, test_seq_freal_add_series_comm, <- Heqyx in Hkl.
Qed.

Theorem freal_mul_to_seq_i_comm {r : radix} : ∀ x y i,
  freal_mul_to_seq x y i = freal_mul_to_seq y x i.
Proof.
intros.
unfold freal_mul_to_seq, numbers_to_digits.
remember (freal_mul_series x y) as xy.
remember (freal_mul_series y x) as yx.
destruct (LPO_fst (test_seq i xy)) as [Hxy| Hxy].
 rewrite Heqxy, freal_mul_series_comm, <- Heqyx.
 destruct (LPO_fst (test_seq i yx)) as [Hyx| Hyx].
  now rewrite A_freal_mul_series_comm, <- Heqyx.

  destruct Hyx as (k & Hjk & Hk).
  rewrite Heqyx, test_seq_freal_mul_series_comm, <- Heqxy in Hk.
  now rewrite Hxy in Hk.

 destruct Hxy as (k & Hjk & Hk).
 rewrite Heqxy, test_seq_freal_mul_series_comm, <- Heqyx in Hk.
 destruct (LPO_fst (test_seq i yx)) as [Hyx| Hyx].
  now rewrite Hyx in Hk.

  destruct Hyx as (l & Hjl & Hl).
  destruct (lt_eq_lt_dec k l) as [ [ Hkl | Hkl ] | Hkl ].
   now apply Hjl in Hkl; subst xy.

   rewrite Heqxy, freal_mul_series_comm, <- Heqyx.
   rewrite A_freal_mul_series_comm, <- Heqyx.
   now subst k.

   apply Hjk in Hkl.
   now rewrite Heqxy, test_seq_freal_mul_series_comm, <- Heqyx in Hkl.
Qed.

Theorem dig_norm_add_comm {r : radix} : ∀ x y i,
  dig (freal (freal_normalize (x + y)) i) =
  dig (freal (freal_normalize (y + x)) i).
Proof.
intros.
unfold freal_normalize.
remember (freal (x + y)) as xy.
remember (freal (y + x)) as yx.
simpl.
unfold digit_sequence_normalize.
destruct (LPO_fst (λ j : nat, rad - 1 - dig (xy (i + j + 1)))) as [Hxy| Hxy].
 destruct (LPO_fst (λ j : nat, rad - 1 - dig (yx (i + j + 1)))) as [Hyx| Hyx].
  unfold freal_add in Heqxy; simpl in Heqxy.
  unfold freal_add in Heqyx; simpl in Heqyx.
  destruct (lt_dec (S (dig (xy i))) rad) as [Hrxy| Hrxy].
   subst xy; simpl in Hrxy; simpl.
   destruct (lt_dec (S (dig (yx i))) rad) as [Hryx| Hryx].
    unfold freal_add in Heqyx; simpl in Heqyx.
    subst yx; simpl in Hryx; simpl.
    now rewrite freal_add_to_seq_i_comm.

    subst yx; simpl in Hryx.
    now rewrite freal_add_to_seq_i_comm in Hryx.

   destruct (lt_dec (S (dig (yx i))) rad) as [Hryx| Hryx]; [ | easy ].
   exfalso.
   subst xy yx; simpl in Hrxy, Hryx.
   now rewrite freal_add_to_seq_i_comm in Hryx.

  destruct Hyx as (k & Hjk & Hk); clear Hjk.
  unfold freal_mul in Heqyx; simpl in Heqyx.
  subst yx; simpl in Hk; simpl.
  rewrite freal_add_to_seq_i_comm in Hk.
  unfold freal_add in Heqxy; simpl in Heqxy.
  subst xy; simpl in Hxy; simpl.
  now specialize (Hxy k).

 destruct Hxy as (k & Hjk & Hk).
 unfold freal_add in Heqxy; simpl in Heqxy.
 unfold freal_add in Heqyx; simpl in Heqyx.
 destruct (LPO_fst (λ j : nat, rad - 1 - dig (yx (i + j + 1)))) as [Hyx| Hyx].
  exfalso; clear Hjk.
  subst xy yx; simpl in Hk, Hyx; simpl.
  rewrite freal_add_to_seq_i_comm in Hk.
  now specialize (Hyx k).

  subst xy yx; simpl.
  apply freal_add_to_seq_i_comm.
Qed.

Theorem dig_norm_mul_comm {r : radix} : ∀ x y i,
  dig (freal (freal_normalize (x * y)) i) =
  dig (freal (freal_normalize (y * x)) i).
Proof.
intros.
unfold freal_normalize.
remember (freal (x * y)) as xy.
remember (freal (y * x)) as yx.
simpl.
unfold digit_sequence_normalize.
destruct (LPO_fst (λ j : nat, rad - 1 - dig (xy (i + j + 1)))) as [Hxy| Hxy].
 destruct (LPO_fst (λ j : nat, rad - 1 - dig (yx (i + j + 1)))) as [Hyx| Hyx].
  unfold freal_mul in Heqxy; simpl in Heqxy.
  unfold freal_mul in Heqyx; simpl in Heqyx.
  destruct (lt_dec (S (dig (xy i))) rad) as [Hrxy| Hrxy].
   subst xy; simpl in Hrxy; simpl.
   destruct (lt_dec (S (dig (yx i))) rad) as [Hryx| Hryx].
    unfold freal_mul in Heqyx; simpl in Heqyx.
    subst yx; simpl in Hryx; simpl.
    now rewrite freal_mul_to_seq_i_comm.

    subst yx; simpl in Hryx.
    now rewrite freal_mul_to_seq_i_comm in Hryx.

   destruct (lt_dec (S (dig (yx i))) rad) as [Hryx| Hryx]; [ | easy ].
   exfalso.
   subst xy yx; simpl in Hrxy, Hryx.
   now rewrite freal_mul_to_seq_i_comm in Hryx.

  destruct Hyx as (k & Hjk & Hk); clear Hjk.
  unfold freal_mul in Heqyx; simpl in Heqyx.
  subst yx; simpl in Hk; simpl.
  rewrite freal_mul_to_seq_i_comm in Hk.
  unfold freal_mul in Heqxy; simpl in Heqxy.
  subst xy; simpl in Hxy; simpl.
  now specialize (Hxy k).

 destruct Hxy as (k & Hjk & Hk).
 unfold freal_mul in Heqxy; simpl in Heqxy.
 unfold freal_mul in Heqyx; simpl in Heqyx.
 destruct (LPO_fst (λ j : nat, rad - 1 - dig (yx (i + j + 1)))) as [Hyx| Hyx].
  exfalso; clear Hjk.
  subst xy yx; simpl in Hk, Hyx; simpl.
  rewrite freal_mul_to_seq_i_comm in Hk.
  now specialize (Hyx k).

  subst xy yx; simpl.
  apply freal_mul_to_seq_i_comm.
Qed.

Theorem freal_add_comm {r : radix} : ∀ x y : FracReal, (x + y = y + x)%F.
Proof.
intros.
unfold freal_eq.
unfold freal_normalized_eq.
remember (freal_normalize (x + y)) as nxy eqn:Hnxy.
remember (freal_normalize (y + x)) as nyx eqn:Hnyx.
destruct (LPO_fst (eq_freal_seq nxy nyx)) as [H| H]; [ easy | ].
exfalso.
destruct H as (i & Hji & Hi).
apply Hi; clear Hi.
unfold eq_freal_seq.
destruct (Nat.eq_dec (dig (freal nxy i)) (dig (freal nyx i))) as [H| H].
 easy.

 exfalso; apply H; clear H.
 subst nxy nyx.
 apply dig_norm_add_comm.
Qed.

Theorem freal_mul_comm {r : radix} : ∀ x y : FracReal, (x * y = y * x)%F.
Proof.
intros.
unfold freal_eq.
unfold freal_normalized_eq.
remember (freal_normalize (x * y)) as nxy eqn:Hnxy.
remember (freal_normalize (y * x)) as nyx eqn:Hnyx.
destruct (LPO_fst (eq_freal_seq nxy nyx)) as [H| H]; [ easy | ].
exfalso.
destruct H as (i & Hji & Hi).
apply Hi; clear Hi.
unfold eq_freal_seq.
destruct (Nat.eq_dec (dig (freal nxy i)) (dig (freal nyx i))) as [H| H].
 easy.

 exfalso; apply H; clear H.
 subst nxy nyx.
 apply dig_norm_mul_comm.
Qed.

Theorem freal_add_series_0_x {r : radix} : ∀ x i,
  freal_add_series 0 x i = dig (freal x i).
Proof.
intros.
unfold freal_add_series; simpl.
unfold sequence_add.
apply Nat.add_0_l.
Qed.

Theorem A_freal_add_series_0_l {r : radix} : ∀ x i n,
  A i n (freal_add_series 0 x) = A i n (λ i, dig (freal x i)).
Proof.
intros.
unfold A; simpl.
unfold freal_add_series; simpl.
unfold sequence_add; simpl.
easy.
Qed.

Theorem freal_add_to_seq_0_l {r : radix} : ∀ x i,
  freal_add_to_seq 0 x i = dig (freal x i).
Proof.
intros.
unfold freal_add_to_seq, numbers_to_digits.
remember (freal_add_series 0 x) as n0x eqn:Hn0x.
destruct (LPO_fst (test_seq i n0x)) as [H0x| H0x].
 rewrite Hn0x, freal_add_series_0_x.
 rewrite A_freal_add_series_0_l.
 assert (∀ i, dig (freal x i) = 0).
  intros j; specialize (H0x j).
  unfold test_seq in H0x.
  subst n0x; simpl in H0x.
  rewrite A_freal_add_series_0_l in H0x.
  destruct
    (le_dec (Init.Nat.pred (rad ^ j))
       (rad ^ j *
        rmod (A i (rad * (i + j + 2)) (λ i : nat, dig (freal x i))) /
        rad ^ (rad * (i + j + 2) - 1 - i))) as [H| H]; [ | easy ].
  clear H0x.
Abort.

Theorem dig_norm_add_0_l {r : radix} : ∀ x i,
  dig (freal (freal_normalize (0 + x)) i) = dig (freal (freal_normalize x) i).
Proof.
intros.
unfold freal_normalize.
remember (freal (0%F + x)) as nx0 eqn:Hnx0.
remember (freal x) as nx eqn:Hnx.
simpl.
unfold digit_sequence_normalize.
destruct (LPO_fst (λ j : nat, rad - 1 - dig (nx0 (i + j + 1)))) as [Hx0| Hx0].
 destruct (LPO_fst (λ j : nat, rad - 1 - dig (nx (i + j + 1)))) as [Hx| Hx].
  unfold freal_add in Hnx0; simpl in Hnx0.
  destruct (lt_dec (S (dig (nx0 i))) rad) as [ Hrx0 | Hrx0 ].
   subst nx0; simpl in Hrx0; simpl.
   destruct (lt_dec (S (dig (nx i))) rad) as [Hrx| Hrx].
    subst nx; simpl in Hrx; simpl.
    simpl in Hx0.
    assert (∀ j, rad - 1 - numbers_to_digits (λ i, dig (freal x i)) (i + j + 1) = 0).
     unfold freal_add_to_seq in Hx0.
     intros j.
     now specialize (Hx0 j).
     clear Hx0; rename H into Hx0; move Hx0 after Hx.
bbb.
Print numbers_to_digits.
Print test_seq.
bbb.

Theorem freal_add_0_l {r : radix} : ∀ x, (0 + x = x)%F.
Proof.
intros.
unfold freal_eq, freal_normalized_eq.
remember (freal_normalize (0%F + x)) as n0x eqn:Hn0x.
remember (freal_normalize x) as nx eqn:Hnx.
destruct (LPO_fst (eq_freal_seq n0x nx)) as [H| H]; [ easy | ].
exfalso.
destruct H as (i & Hji & Hi).
apply Hi; clear Hi.
unfold eq_freal_seq.
destruct (Nat.eq_dec (dig (freal n0x i)) (dig (freal nx i))) as [H| H].
 easy.

 exfalso; apply H; clear H.
 subst n0x nx.
bbb.
 apply dig_norm_add_0_l.
Qed.
