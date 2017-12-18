(* Real between 0 and 1, i.e. fractional part of a real.
   Implemented as function of type nat → nat.
   Operations + and * implemented using LPO. *)

Require Import Utf8 Arith Psatz.
Require Import Misc Summation Xnat.

(* Limited Principle of Omniscience *)
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
  (∀ k, u k = O) +
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

Record FracReal {r : radix} := { freal : nat → nat }.
Arguments freal r _%F.

Definition digit_sequence_normalize {r : radix} (u : nat → nat) i :=
  match LPO_fst (λ j : nat, rad - 1 - u (i + j + 1)) with
  | inl _ => if lt_dec (S (u i)) rad then S (u i) else 0
  | inr _ => u i
 end.

Definition freal_normalize {r : radix} x :=
  {| freal := digit_sequence_normalize (freal x) |}.

Arguments freal_normalize r x%F.

Definition eq_freal_seq {r : radix} x y i :=
  if Nat.eq_dec (freal x i) (freal y i) then 0 else 1.

Definition freal_normalized_eq {r : radix} x y :=
  match LPO_fst (eq_freal_seq x y) with
  | inl _ => true
  | inr _ => false
  end.

Definition freal_normalized_lt {r : radix} x y :=
  match LPO_fst (eq_freal_seq x y) with
  | inl _ => true
  | inr (exist _ i _) =>
      if lt_dec (freal x i) (freal y i) then true else false
  end.

Definition freal_eq {r : radix} x y :=
  freal_normalized_eq (freal_normalize x) (freal_normalize y).

Definition freal_lt {r : radix} x y :=
  freal_normalized_lt (freal_normalize x) (freal_normalize y).

Definition freal_0 {r : radix} := {| freal i := 0 |}.

Notation "0" := (freal_0) : freal_scope.
Notation "a = b" := (freal_eq a b = true) : freal_scope.
Notation "a ≠ b" := (freal_eq a b = false) : freal_scope.
Notation "a < b" := (freal_lt a b = true) : freal_scope.

(* Addition, Multiplication *)

Definition sequence_add (a b : nat → nat) i := a i + b i.
Definition sequence_mul (rg := nat_ord_ring) (a b : nat → nat) i :=
  Σ (j = 0, i), a j * b (i - j).

Definition freal_add_series {r : radix} a b :=
  sequence_add (freal a) (freal b).

Arguments freal_add_series _ a%F b%F.

Definition freal_mul_series {r : radix} a b i :=
  match i with
  | 0 => 0
  | S i' => sequence_mul (freal a) (freal b) i'
  end.

Definition nA {r : radix} (rg := nat_ord_ring) i n u :=
  Σ (j = i + 1, n - 1), u j * rad ^ (n - 1 - j).

Definition test_seq {r : radix} i u k :=
  let n := rad * (i + k + 2) in
  let s := rad ^ (n - 1 - i) in
  if le_dec ((rad ^ k - 1) * s) (rad ^ k * (nA i n u mod s)) then 0
  else 1.

Definition numbers_to_digits {r : radix} u i :=
  match LPO_fst (test_seq i u) with
  | inl _ =>
      let n := rad * (i + 2) in
      let s := rad ^ (n - 1 - i) in
      (u i + nA i n u / s + 1) mod rad
  | inr (exist _ k _) =>
      let n := rad * (i + k + 2) in
      let s := rad ^ (n - 1 - i) in
      (u i + nA i n u / s) mod rad
  end.

Definition freal_add_to_seq {r : radix} (a b : FracReal) :=
  numbers_to_digits (freal_add_series a b).

Arguments freal_add_to_seq _ a%F b%F.

Definition freal_mul_to_seq {r : radix} (a b : FracReal) :=
  numbers_to_digits (freal_mul_series a b).

Definition freal_add {r : radix} (a b : FracReal) :=
  {| freal := freal_add_to_seq a b |}.

Arguments freal_add _ a%F b%F.

Definition freal_mul {r : radix} (a b : FracReal) :=
  {| freal := freal_mul_to_seq a b |}.

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
 rewrite Nat.add_comm.
 remember minus as x; simpl; subst x; f_equal; [ lia | ].
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

Theorem nA_freal_add_series_comm {r : radix} : ∀ x y i n,
  nA i n (freal_add_series x y) = nA i n (freal_add_series y x).
Proof.
intros.
unfold nA; simpl.
apply summation_eq_compat; intros j Hj.
now rewrite freal_add_series_comm.
Qed.

Theorem nA_freal_mul_series_comm {r : radix} : ∀ x y i n,
  nA i n (freal_mul_series x y) = nA i n (freal_mul_series y x).
Proof.
intros.
unfold nA; simpl.
apply summation_eq_compat; intros j Hj.
now rewrite freal_mul_series_comm.
Qed.

Theorem test_seq_freal_add_series_comm {r : radix} : ∀ x y i k,
  test_seq i (freal_add_series x y) k =
  test_seq i (freal_add_series y x) k.
Proof.
intros.
unfold test_seq.
now rewrite nA_freal_add_series_comm.
Qed.

Theorem test_seq_freal_mul_series_comm {r : radix} : ∀ x y i k,
  test_seq i (freal_mul_series x y) k =
  test_seq i (freal_mul_series y x) k.
Proof.
intros.
unfold test_seq.
now rewrite nA_freal_mul_series_comm.
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
  now rewrite nA_freal_add_series_comm, <- Heqyx.

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
   rewrite nA_freal_add_series_comm, <- Heqyx.
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
  now rewrite nA_freal_mul_series_comm, <- Heqyx.

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
   rewrite nA_freal_mul_series_comm, <- Heqyx.
   now subst k.

   apply Hjk in Hkl.
   now rewrite Heqxy, test_seq_freal_mul_series_comm, <- Heqyx in Hkl.
Qed.

Theorem dig_norm_add_comm {r : radix} : ∀ x y i,
  freal (freal_normalize (x + y)) i = freal (freal_normalize (y + x)) i.
Proof.
intros.
unfold freal_normalize.
remember (freal (x + y)) as xy.
remember (freal (y + x)) as yx.
simpl.
unfold digit_sequence_normalize.
destruct (LPO_fst (λ j : nat, rad - 1 - xy (i + j + 1))) as [Hxy| Hxy].
 destruct (LPO_fst (λ j : nat, rad - 1 - yx (i + j + 1))) as [Hyx| Hyx].
  unfold freal_add in Heqxy; simpl in Heqxy.
  unfold freal_add in Heqyx; simpl in Heqyx.
  destruct (lt_dec (S (xy i)) rad) as [Hrxy| Hrxy].
   subst xy; simpl in Hrxy; simpl.
   destruct (lt_dec (S (yx i)) rad) as [Hryx| Hryx].
    unfold freal_add in Heqyx; simpl in Heqyx.
    subst yx; simpl in Hryx; simpl.
    now rewrite freal_add_to_seq_i_comm.

    subst yx; simpl in Hryx.
    now rewrite freal_add_to_seq_i_comm in Hryx.

   destruct (lt_dec (S (yx i)) rad) as [Hryx| Hryx]; [ | easy ].
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
 destruct (LPO_fst (λ j : nat, rad - 1 - yx (i + j + 1))) as [Hyx| Hyx].
  exfalso; clear Hjk.
  subst xy yx; simpl in Hk, Hyx; simpl.
  rewrite freal_add_to_seq_i_comm in Hk.
  now specialize (Hyx k).

  subst xy yx; simpl.
  apply freal_add_to_seq_i_comm.
Qed.

Theorem dig_norm_mul_comm {r : radix} : ∀ x y i,
  freal (freal_normalize (x * y)) i = freal (freal_normalize (y * x)) i.
Proof.
intros.
unfold freal_normalize.
remember (freal (x * y)) as xy.
remember (freal (y * x)) as yx.
simpl.
unfold digit_sequence_normalize.
destruct (LPO_fst (λ j : nat, rad - 1 - xy (i + j + 1))) as [Hxy| Hxy].
 destruct (LPO_fst (λ j : nat, rad - 1 - yx (i + j + 1))) as [Hyx| Hyx].
  unfold freal_mul in Heqxy; simpl in Heqxy.
  unfold freal_mul in Heqyx; simpl in Heqyx.
  destruct (lt_dec (S (xy i)) rad) as [Hrxy| Hrxy].
   subst xy; simpl in Hrxy; simpl.
   destruct (lt_dec (S (yx i)) rad) as [Hryx| Hryx].
    unfold freal_mul in Heqyx; simpl in Heqyx.
    subst yx; simpl in Hryx; simpl.
    now rewrite freal_mul_to_seq_i_comm.

    subst yx; simpl in Hryx.
    now rewrite freal_mul_to_seq_i_comm in Hryx.

   destruct (lt_dec (S (yx i)) rad) as [Hryx| Hryx]; [ | easy ].
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
 destruct (LPO_fst (λ j : nat, rad - 1 - yx (i + j + 1))) as [Hyx| Hyx].
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
destruct (Nat.eq_dec (freal nxy i) (freal nyx i)) as [H| H]; [ easy | ].
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
destruct (Nat.eq_dec (freal nxy i) (freal nyx i)) as [H| H]; [ easy | ].
exfalso; apply H; clear H.
subst nxy nyx.
apply dig_norm_mul_comm.
Qed.

Theorem freal_add_series_0_x {r : radix} : ∀ x i,
  freal_add_series 0 x i = freal x i.
Proof.
intros.
unfold freal_add_series; simpl.
unfold sequence_add.
apply Nat.add_0_l.
Qed.

Theorem nA_freal_add_series_0_l {r : radix} : ∀ x i n,
  nA i n (freal_add_series 0 x) = nA i n (freal x).
Proof.
intros.
unfold nA; simpl.
unfold freal_add_series; simpl.
unfold sequence_add; simpl.
easy.
Qed.

Theorem Nat_pow_ge_1 : ∀ a b, 0 < a → 1 ≤ a ^ b.
Proof.
intros * Ha.
induction b; [ easy | simpl ].
replace 1 with (1 * 1) by lia.
apply Nat.mul_le_mono_nonneg; [ lia | easy | lia | easy ].
Qed.

Theorem power_summation (rg := nat_ord_ring) : ∀ a n,
  0 < a
  → a ^ S n = 1 + (a - 1) * Σ (i = 0, n), a ^ i.
Proof.
intros * Ha.
induction n.
 rewrite summation_only_one.
 rewrite Nat.pow_0_r, Nat.mul_1_r.
 rewrite Nat.pow_1_r; lia.

 rewrite summation_split_last; [ | lia ].
 rewrite Nat.mul_add_distr_l.
 rewrite Nat.add_assoc.
 rewrite <- IHn.
 rewrite Nat.mul_sub_distr_r.
 simpl; rewrite Nat.add_0_r.
 rewrite Nat.add_sub_assoc.
  now rewrite Nat.add_comm, Nat.add_sub.

  apply Nat.mul_le_mono; [ easy | ].
  replace (a ^ n) with (1 * a ^ n) at 1 by lia.
  apply Nat.mul_le_mono_nonneg_r; lia.
Qed.

Theorem nA_dig_seq_ub {r : radix} : 0 < rad → ∀ u,
  (∀ i, u i < rad) →
  ∀ n i,
  let s := rad ^ (n - 1 - i) in
  i + 1 ≤ n - 1
  → nA i n u < s.
Proof.
intros Hr u Hu * Hin.
unfold nA, s.
rewrite summation_rtl.
rewrite summation_shift; [ | easy ].
remember (n - 1 - i) as k eqn:Hk.
destruct k; [ lia | ].
rewrite power_summation; [ | easy ].
replace (n - 1 - (i + 1)) with k by lia.
unfold lt; simpl.
apply -> Nat.succ_le_mono.
rewrite summation_mul_distr_l.
apply (@summation_le_compat _ nat_ord_ring).
intros j Hj.
replace (n - 1 + (i + 1) - (i + 1 + j)) with (n - 1 - j) by lia.
replace (n - 1 - (n - 1 - j)) with j by lia.
apply Nat.mul_le_mono_nonneg_r; [ lia | ].
apply Nat.le_add_le_sub_l.
apply Hu.
Qed.

Theorem rad_pow_succ_gt_1 {r : radix} : 1 < rad → ∀ k, 1 < rad ^ S k.
Proof.
intros Hr *.
induction k; [ now rewrite Nat.pow_1_r | ].
simpl; replace 1 with (1 * 1) by lia.
apply Nat.mul_lt_mono_nonneg; [ lia | easy | lia | easy ].
Qed.

Theorem rad_expr {r : radix} : 1 < rad → ∀ i k, rad * (i + k + 2) - 1 - i ≠ 1.
Proof.
intros Hr * Hj.
replace (rad * (i + k + 2) - 1 - i)
with (rad * S i + rad * (k + 1) - S i) in Hj by lia.
rewrite Nat.add_sub_swap in Hj.
 destruct rad as [| n]; [ easy | ].
 replace (S n * S i - S i) with (n * S i) in Hj by lia.
 destruct n as [| n]; [ lia | simpl in Hj; lia ].

 destruct rad as [| n]; [ easy | ].
 rewrite Nat.mul_comm; simpl.
 rewrite Nat.mul_comm; simpl; lia.
Qed.

Theorem test_seq_all_0 {r : radix} : 1 < rad → ∀ u,
  (∀ i, u i < rad)
  → ∀ i,
  (∀ k, test_seq i u k = 0)
  → ∀ k, u (i + k + 1) = rad - 1.
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hur * Huk *.
specialize (Huk (S k)).
unfold test_seq in Huk.
set (n := rad * (i + S k + 2)) in Huk.
set (s := rad ^ (n - 1 - i)) in Huk.
destruct (le_dec ((rad ^ S k - 1) * s) (rad ^ S k * (nA i n u mod s)))
  as [H| H]; [ clear Huk | easy ].
remember (n - 1 - i) as j eqn:Hj.
symmetry in Hj.
rewrite Nat.mod_small in H.
-destruct j.
 +simpl in s; subst s.
  rewrite Nat.mul_1_r in H.
  unfold nA in H.
  rewrite summation_empty in H; [ | lia ].
  rewrite Nat.mul_0_r in H.
  apply Nat.le_0_r in H.
  apply Nat.sub_0_le in H.
  exfalso; apply Nat.le_ngt in H.
  apply H; clear H; clear - Hr.
  now apply rad_pow_succ_gt_1.

 +remember (rad ^ S k * nA i n u) as a eqn:Ha.
  rewrite Nat.mul_comm in Ha; subst a.
  unfold nA in H; subst s.
  revert i j n Hj H.
  induction k; intros.
  *rewrite Nat.add_0_r.
   simpl in H.
   rewrite Nat.mul_1_r in H.
   rewrite Nat.mul_assoc, Nat.mul_shuffle0 in H.
   apply Nat.mul_le_mono_pos_r in H; [ | lia ].
   rewrite summation_shift in H; [ | lia ].
   replace (n - 1 - (i + 1)) with j in H by lia.
   rewrite summation_eq_compat with (h := λ k, u (i + 1 + k) * rad ^ (j - k))
     in H.
   2: intros k Hk; f_equal; f_equal; lia.
   remember (λ k, u (i + 1 + k) * rad ^ (j - k)) as a; subst a.
   clear Hj n.
   revert u i H Hur.
   induction j; intros.
  --rewrite Nat.pow_0_r in H; simpl in H.
    rewrite summation_only_one in H.
    do 2 rewrite Nat.mul_1_r in H.
    rewrite Nat.add_0_r in H.
    specialize (Hur (i + 1)); lia.

  --apply IHj; clear IHj; [ | easy ].
    eapply Nat.div_le_mono in H; [ | apply Hrz ].
    remember minus as f; simpl in H; subst f.
    rewrite Nat.mul_assoc, Nat.mul_shuffle0 in H.
    rewrite Nat.div_mul in H; [ | easy ].
    eapply Nat.le_trans; [ eassumption | ].
    rewrite summation_split_last; [ | lia ].
    rewrite summation_eq_compat with
      (h := λ k, u (i + 1 + k) * rad ^ (j - k) * rad).
   ++rewrite <- summation_mul_distr_r.
     rewrite Nat.div_add_l; [ | easy ].
     rewrite Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r.
     rewrite Nat.div_small; [ | apply Hur ].
     now rewrite Nat.add_0_r.

   ++intros k Hk.
     rewrite Nat.sub_succ_l; [ simpl; lia | easy ].

  *destruct j.
    unfold n in Hj; clear -Hr Hj; exfalso.
    now revert Hj; apply rad_expr.

    replace (i + S k) with (S i + k) by lia.
    apply IHk with (j := j).
     replace (S i + S k) with (i + S (S k)) by lia.
     fold n; lia.

     replace (S i + S k + 2) with (i + S (S k) + 2) by lia; fold n.
     replace (rad ^ S (S j)) with (rad * rad ^ S j) in H by easy.
     replace (rad ^ S (S k)) with (rad * rad ^ S k) in H by easy.
     setoid_rewrite Nat.mul_comm in H.
     setoid_rewrite Nat.mul_comm.
     do 2 rewrite <- Nat.mul_assoc in H.
     apply Nat.mul_le_mono_pos_l in H; [ | lia ].
     rewrite summation_split_first in H; [ | lia ].
     rewrite summation_shift in H; [ | lia ].
     replace (n - 1 - S (i + 1)) with j in H by lia.
     rewrite summation_shift; [ | lia ].
     replace (n - 1 - (S i + 1)) with j by lia.
     replace (rad * rad ^ S k - 1)
     with (rad ^ S k - 1 + (rad - 1) * rad ^ S k) in H.
      rewrite Nat.mul_add_distr_l in H.
      rewrite Nat.mul_add_distr_l in H.
      replace (n - 1 - (i + 1)) with (S j) in H by lia.
      rewrite Nat.add_comm in H.
      setoid_rewrite Nat.add_comm in H.
      replace (rad ^ S j * ((rad - 1) * rad ^ S k))
      with (rad ^ S k * ((rad - 1) * rad ^ S j))
      in H by lia.
      apply Nat.le_le_add_le in H; [ easy | ].
      apply Nat.mul_le_mono_nonneg_l; [ lia | ].
      apply Nat.mul_le_mono_nonneg_r; [ lia | ].
      rewrite Nat.sub_1_r.
      apply Nat.lt_le_pred, Hur.

      rewrite Nat.mul_sub_distr_r.
      rewrite Nat.mul_1_l.
      rewrite Nat.add_sub_assoc.
       rewrite <- Nat.add_sub_swap.
        rewrite <- Nat.add_sub_assoc.
         now rewrite Nat.add_comm, Nat.add_sub.

         rewrite <- Nat.pow_succ_r; [ | lia ].
         replace 1 with (1 ^ S (S k)) by apply Nat.pow_1_l.
         apply Nat.pow_le_mono_l; lia.

        replace 1 with (1 ^ S k) by apply Nat.pow_1_l.
        apply Nat.pow_le_mono_l; lia.

       rewrite <- Nat.pow_succ_r; [ | lia ].
       replace (rad ^ S k) with (1 * rad ^ S k) at 1 by lia.
       apply Nat.mul_le_mono_nonneg_r; lia.

-unfold s; rewrite <- Hj.
 apply nA_dig_seq_ub; [ lia | easy | ].
 destruct j; [ | lia ].
 simpl in s; subst s.
 rewrite Nat.mod_1_r, Nat.mul_1_r, Nat.mul_0_r in H.
 apply Nat.le_0_r in H.
 apply Nat.sub_0_le in H.
 exfalso; apply Nat.le_ngt in H.
 apply H; clear H; clear -Hr.
 now apply rad_pow_succ_gt_1.
Qed.

Theorem nA_all_9 {r : radix} : 0 < rad → ∀ u i n,
  (∀ j, u (i + j + 1) = rad - 1)
  → nA i n u = rad ^ (n - i - 1) - 1.
Proof.
intros Hr * Hj.
unfold nA.
rewrite summation_eq_compat with (h := λ j, (rad - 1) * rad ^ (n - 1 - j)).
 Focus 2.
 intros j Hij.
 replace j with (i + (j - i - 1) + 1) at 1 by lia.
 now rewrite Hj.

 rewrite <- summation_mul_distr_l.
 destruct (le_dec (i + 1) (n - 1)) as [Hin| Hin].
  rewrite summation_shift; [ | easy ].
  rewrite summation_rtl.
  rewrite summation_eq_compat with (h := λ j, rad ^ j).
   apply Nat.succ_inj_wd.
   rewrite <- Nat.add_1_l.
   rewrite <- power_summation; [ symmetry | easy ].
   rewrite <- Nat.sub_succ_l; [ | now apply Nat_pow_ge_1 ].
   rewrite Nat.sub_succ, Nat.sub_0_r.
   f_equal; lia.

   intros; f_equal; lia.

  replace (n - i - 1) with 0 by lia.
  rewrite summation_empty; [ | lia ].
  rewrite Nat.mul_0_r; simpl; lia.
Qed.

(*
Theorem glop : ∀ r i j d, i ≤ j →
  (r ^ (i + d) - 1) * r ^ j ≤ r ^ i * (r ^ (j + d) - 1).
Proof.
intros * Hij.
destruct i.
 simpl; rewrite Nat.add_0_r; clear Hij.
 revert j.
 induction d; intros; [ simpl; lia | ].
bbb.

Theorem pow_pow_sub_1 : ∀ r i j, i ≤ j →
  (r ^ i - 1) * r ^ j ≤ r ^ i * (r ^ j - 1).
Proof.
intros * Hij.
destruct i; [ simpl; lia | ].
destruct j; [ lia | ].
rewrite Nat.mul_comm; simpl.
do 2 rewrite <- Nat.mul_assoc.
apply Nat.mul_le_mono_nonneg_l; [ lia | ].
rewrite <- Nat.pow_succ_r; [ | lia ].
rewrite <- Nat.pow_succ_r; [ | lia ].
bbb.

rewrite Nat.mul_comm.
rewrite power_summation.
 rewrite Nat.add_sub_swap; [ | easy ].
 rewrite Nat.sub_diag, Nat.add_0_l.
bbb.
*)

Theorem list_of_nat_pred_pow_pow {r : radix} : ∀ i j,
list_of_nat 0 ((rad ^ i - 1) * rad ^ j) =
List.repeat 0 j ++ List.repeat (rad - 1) i.
Proof.
intros.
...

Theorem nA_all_9_ge {r : radix} : 1 < rad → ∀ u i k,
  let n := rad * (i + k + 2) in
  let s := rad ^ (n - 1 - i) in
  (∀ j, u (i + j + 1) = rad - 1)
  → (rad ^ k - 1) * s ≤ rad ^ k * nA i n u.
Proof.
intros Hr * Hi.
replace (nA i n u) with (rad ^ (n - i - 1) - 1).
2: symmetry; apply nA_all_9; [ lia | easy ].
assert (Hk : k ≤ n - i - 1).
-subst n; clear -Hr.
 replace (rad * (i + k + 2) - i - 1)
 with (rad * (i + 1) + rad * (k + 1) - 1 * (i + 1)) by lia.
 rewrite Nat.add_sub_swap.
 +rewrite <- Nat.mul_sub_distr_r.
  apply le_trans with (m := rad * (k + 1)); [ | lia ].
  apply le_trans with (m := rad * k); [ | lia ].
  destruct rad as [| n]; [ lia | simpl; lia ].
 +apply Nat.mul_le_mono_nonneg_r; lia.

-subst s.
 rewrite <- Nat.sub_add_distr, Nat.add_comm, Nat.sub_add_distr.
 remember ((rad ^ k - 1) * rad ^ (n - i - 1)) as x eqn:Hx.
 remember (rad ^ k * (rad ^ (n - i - 1) - 1)) as y eqn:Hy.
 assert (H : (xnat_of_nat x ≤ xnat_of_nat y)%X).
 +subst x y.
  unfold xnat_of_nat, nat_of_xnat; simpl.
  rewrite list_of_nat_pred_pow_pow.
  rewrite Nat.mul_comm, list_of_nat_pred_pow_pow.
bbb.
  now apply pow_pow_sub_1.
Qed.

Theorem numbers_to_digits_is_norm {r : radix} : ∀ u i,
  numbers_to_digits (λ j, dig (u j)) i =
  dig (digit_sequence_normalize u i).
Proof.
intros.
unfold numbers_to_digits.
unfold digit_sequence_normalize.
destruct (LPO_fst (test_seq i (λ j : nat, dig (u j)))) as [Hi| Hi].
 rewrite Nat.div_small.
  rewrite Nat.add_0_r, Nat.add_1_r.
  destruct (LPO_fst (λ j : nat, rad - 1 - dig (u (i + j + 1)))) as [Hj| Hj].
   destruct (lt_dec (S (dig (u i))) rad) as [Hlt| Hge]; simpl.
    now rewrite Nat.mod_small.

    apply Nat.nlt_ge in Hge.
    specialize (dig_lt_rad (u i)) as Hd.
    assert (H : dig (u i) = rad - 1) by lia.
    rewrite H.
    rewrite <- Nat.sub_succ_l; [ | lia ].
    rewrite Nat.sub_succ, Nat.sub_0_r.
    rewrite Nat.mod_same; [ easy | lia ].

   exfalso.
   destruct Hj as (k & Hk & Hik).
   specialize (test_seq_all_0 u i Hi) as H.
   simpl in H.
   specialize (H k); lia.

  apply nA_dig_seq_ub.
  specialize rad_ge_2 as Hr.
  destruct rad as [| n]; [ lia | ].
  simpl; lia.

 destruct Hi as (k & Hk & Hik).
  destruct (LPO_fst (λ j : nat, rad - 1 - dig (u (i + j + 1)))) as [Hj| Hj].
   destruct (lt_dec (S (dig (u i))) rad) as [Hlt| Hge]; simpl.
    exfalso.
    unfold test_seq in Hik.
    set (n := rad * (i + k + 2)) in Hik.
    set (s := rad ^ (n - 1 - i)) in Hik.
    set (v j := dig (u j)) in Hik.
    destruct (le_dec ((rad ^ k - 1) * s) (rad ^ k * (nA i n v mod s)))
     as [H| H]; [ easy | clear Hik ].
    apply H; clear H.
    rewrite Nat.mod_small.
     apply nA_all_9_ge.
bbb.

Theorem numbers_to_digits_id {r : radix} : ∀ x i,
  numbers_to_digits (λ j, dig (freal x j)) i = dig (freal x i).
Proof.
intros.
unfold numbers_to_digits.
destruct (LPO_fst (test_seq i (λ j, dig (freal x j)))) as [H| H].
 remember (λ j, dig (freal x j)) as u eqn:Hu.
 remember (rad * (i + 2)) as n eqn:Hn.
 remember (rad ^ (n - 1 - i)) as s eqn:Hs.
bbb.
 assert (∀ k : nat, False).
  intros k.
  pose proof (H k) as Hk.
  unfold test_seq in Hk.
  remember (rad * (i + k + 2)) as n eqn:Hn.
  remember (rad ^ (n - 1 - i)) as s eqn:Hs.
  destruct (le_dec ((rad ^ k - 1) * s) (rad ^ k * (nA i n u mod s)))
   as [Hle| Hgt]; [ clear Hk | easy ].
bbb.
rad ^ k - 1 = 99...99
              -------
                 k
s = 100...00
     -------
    n - 1 - i

(rad ^ k - 1) * s = 99...9900...00
                    -------=======
                       k    n-1-i

rad ^ k = 100...00
           -------
              k
nA i n u = xx...xx        ... mod s = itself
           -------
            n-1-i

rad ^ k * (nA i n u mod s) = xx...xx00...00
                             =======-------
                              n-1-i    k


 remember (rad * (i + 2)) as n eqn:Hn.
 remember (rad ^ (n - 1 - i)) as s eqn:Hs.

(* probablement vrai mais inutile
 assert
   (Hk : ∀ k,
    let n := rad * (i + k + 2) in
    let s := rad ^ (n - 1 - i) in
    (rad ^ k - 1) * s ≤ rad ^ k * nA i n u).
   clear -H Hu.
   intros k n s.
   unfold test_seq in H.
   specialize (H k).
   fold n s in H.
   destruct (le_dec ((rad ^ k - 1) * s) (rad ^ k * (nA i n u mod s)))
    as [Hk| Hk]; [ clear H | easy ].
   eapply Nat.le_trans; [ eassumption | ].
   apply Nat.mul_le_mono_nonneg_l; [ lia | ].
   enough (nA i n u < s).
    apply Nat.mod_le; unfold s.
    apply Nat.pow_nonzero.
    easy.

    unfold nA.
    clear Hk.
*)
(* ouais mais nA i n u < s (à vérifier, mais je pense que c'est bon).
   du coup, c'est faux, crotte alors *)
(* peut-être que le numbers_to_digits en fait renvoit un nombre normalisé.
   faut voir... *)
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
    subst nx; simpl in Hrx, Hx0; simpl; f_equal.
    unfold freal_add_to_seq.
    unfold freal_add_to_seq in Hx0.
(*
    assert
      (∀ k, rad - 1 - numbers_to_digits (λ j, dig (freal x j)) (i + k + 1)= 0).
     intros.
     specialize (Hx0 k).
     unfold freal_add_series in Hx0.
     simpl in Hx0.
     now unfold sequence_add in Hx0.

     clear Hx0; rename H into Hx0; move Hx0 after Hx.
*)
    unfold freal_add_series; simpl.
    unfold sequence_add; simpl.
    unfold numbers_to_digits.
    simpl.
bbb.
    simpl in Hx0.
    assert (∀ j, rad - 1 - numbers_to_digits (λ i, dig (freal x i)) (i + j + 1) = 0).
     unfold freal_add_to_seq in Hx0.
     intros j.
     now specialize (Hx0 j).
     clear Hx0; rename H into Hx0; move Hx0 after Hx.
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
