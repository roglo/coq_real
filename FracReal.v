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

Definition mul_test_seq {r : radix} i u k :=
  let n := rad * (i + k + 2) in
  if le_dec (pred (rad ^ k)) (rad ^ k * rmod (A i n u) / den (A i n u)) then 0
  else 1.

Definition freal_mul_to_seq {r : radix} (a b : FracReal) i :=
  let u := freal_mul_series a b in
  match LPO_fst (mul_test_seq i u) with
  | inl _ => (u i + rdiv (A i (rad * (i + 2)) u) + 1) mod rad
  | inr (exist _ j _) => (u i + rdiv (A i (rad * (i + j + 2)) u)) mod rad
  end.

Theorem freal_mul_to_seq_lt_rad {r : radix} : ∀ a b i,
  freal_mul_to_seq a b i < rad.
Proof.
intros.
unfold freal_mul_to_seq.
remember (mul_test_seq i (freal_mul_series a b)) as v eqn:Hv.
destruct (LPO_fst v) as [Hvi| (j, Hvj)].
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

Print A.

Theorem A_freal_mul_series_comm {r : radix} : ∀ x y i n,
  A i n (freal_mul_series x y) = A i n (freal_mul_series y x).
Proof.
intros.
unfold A; simpl; f_equal.
apply summation_eq_compat; intros j Hj.
now rewrite freal_mul_series_comm.
Qed.

Theorem mul_test_seq_freal_mul_series_comm {r : radix} : ∀ x y i k,
  mul_test_seq i (freal_mul_series x y) k =
  mul_test_seq i (freal_mul_series y x) k.
Proof.
intros.
unfold mul_test_seq.
now rewrite A_freal_mul_series_comm.
Qed.

Theorem dig_norm_mul_com {r : radix} : ∀ x y i,
  dig (freal (freal_normalize (x * y)) i) =
  dig (freal (freal_normalize (y * x)) i).
Proof.
intros.
unfold freal_normalize.
remember (freal (x * y)%F) as xy.
remember (freal (y * x)%F) as yx.
simpl.
unfold digit_sequence_normalize.
destruct (LPO_fst (λ j : nat, rad - 1 - dig (xy (i + j + 1)))) as [Hxy| Hxy].
 assert (H : ∀ j, j ≥ i + 1 → freal_mul_to_seq x y j = rad - 1).
  intros j Hji; subst xy.
  specialize (Hxy (j - (i + 1))).
  replace (i + (j - (i + 1)) + 1) with j in Hxy by lia.
  assert (dig (freal (x * y) j) < rad) by apply digi.
  unfold freal_mul in Hxy, H; simpl in Hxy, H; lia.

  clear Hxy; rename H into Hxy.
  destruct (LPO_fst (λ j : nat, rad - 1 - dig (yx (i + j + 1)))) as [Hyx| Hyx].
   assert (H : ∀ j, j ≥ i + 1 → freal_mul_to_seq y x j = rad - 1).
   intros j Hji; subst yx.
   specialize (Hyx (j - (i + 1))).
   replace (i + (j - (i + 1)) + 1) with j in Hyx by lia.
   assert (dig (freal (y * x) j) < rad) by apply digi.
   unfold freal_mul in Hyx, H; simpl in Hyx, H; lia.

   clear Hyx; rename H into Hyx.
   destruct (lt_dec (S (dig (xy i))) rad) as [Hrxy| Hrxy].
    unfold freal_mul in Heqxy; simpl in Heqxy.
    subst xy; simpl in Hrxy; simpl.
    destruct (lt_dec (S (dig (yx i))) rad) as [Hryx| Hryx].
     unfold freal_mul in Heqyx; simpl in Heqyx.
     subst yx; simpl in Hryx; simpl.
     f_equal.
     unfold freal_mul_to_seq.
     destruct (LPO_fst (mul_test_seq i (freal_mul_series x y))) as [Hfxy| Hfxy].
      destruct (LPO_fst (mul_test_seq i (freal_mul_series y x))) as [Hfyx| Hfyx].
       f_equal; f_equal.
       rewrite freal_mul_series_comm; f_equal; f_equal.
       now rewrite A_freal_mul_series_comm.

       destruct Hfyx as (k, Hfyx).
       specialize (Hfxy k).
       now rewrite mul_test_seq_freal_mul_series_comm in Hfxy.

      destruct Hfxy as (k & Hlxy & Hfxy).
      rewrite mul_test_seq_freal_mul_series_comm in Hfxy.
      destruct (LPO_fst (mul_test_seq i (freal_mul_series y x))) as [Hfyx| Hfyx].
       now rewrite Hfyx in Hfxy.

       destruct Hfyx as (l & Hlyx & Hfyx).
       f_equal; f_equal; [ apply freal_mul_series_comm | ].
       rewrite A_freal_mul_series_comm.
       remember (freal_mul_series y x) as yx.
bbb.
       unfold mul_test_seq in Hfxy, Hfyx.
       remember (A i (rad * (i + k + 2)) yx) as a1.
       remember (A i (rad * (i + l + 2)) yx) as a2.
       remember (rad ^ k * rmod a1 / den a1) as r1.
       destruct (le_dec (pred (rad ^ k)) r1) as [H1| H1]; [ easy | ].
       remember (rad ^ l * rmod a2 / den a2) as r2.
       destruct (le_dec (pred (rad ^ l)) r2) as [H2| H2]; [ easy | clear Hfyx ].
       subst r1 a1 r2 a2.
       unfold rmod in H1, H2.
       unfold A in H1, H2.
       simpl in H1, H2.
bbb.

Theorem freal_mul_comm {r : radix} : ∀ x y : FracReal, (x * y = y * x)%F.
Proof.
intros.
unfold freal_eq.
remember (freal_normalize (x * y)) as nxy eqn:Hnxy.
remember (freal_normalize (y * x)) as nyx eqn:Hnyx.
unfold freal_normalized_eq.
destruct (LPO (eq_freal_seq nxy nyx)) as [H| H]; [ easy | ].
exfalso.
destruct H as (i, Hi).
apply Hi; clear Hi.
unfold eq_freal_seq.
destruct (Nat.eq_dec (dig (freal nxy i)) (dig (freal nyx i))) as [H| H].
 easy.

 exfalso; apply H; clear H.
 subst nxy nyx.
bbb.
