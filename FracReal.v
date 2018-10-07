(* Real between 0 and 1, i.e. fractional part of a real.
   Implemented as function of type nat → nat.
   Operations + and * implemented using LPO. *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz NPeano.
Require Import Misc Summation NQ.
Import Init.Nat PeanoNat.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

(* Limited Principle of Omniscience *)
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

Theorem LPO_fst : ∀ (u : nat → bool),
  (∀ k, u k = true) +
  { i : nat | (∀ j, j < i → u j = true) ∧ u i = false }.
Proof.
intros.
set (v i := if u i then 0 else 1).
specialize (LPO v) as [H| (i, Hi)]; [ left | right ].
-intros k; subst v; specialize (H k); simpl in H.
 now destruct (u k).
-remember (first_such_that (λ i, negb (Nat.eqb (v i) 0)) i 0) as j eqn:Hj.
 exists j.
 assert (Hui : v (i + 0) ≠ 0) by now rewrite Nat.add_0_r.
 specialize (first_such_that_has_prop v i 0 j Hui Hj) as (Huj, H).
 subst v; split.
 +intros k Hkj; simpl in H.
  specialize (H k (Nat.le_0_l k) Hkj).
  now destruct (u k).
 +simpl in Huj.
  now destruct (u j).
Qed.

(* Radix *)

Class radix := { rad : nat; radix_ge_2 : rad ≥ 2 }.

Theorem radix_gt_0 {r : radix} : 0 < rad.
Proof.
destruct r as (rad, radi); simpl; flia radi.
Qed.

Theorem radix_ge_1 {r : radix} : 1 ≤ rad.
Proof.
destruct r as (rad, radi); simpl; flia radi.
Qed.

Theorem radix_ne_0 {r : radix} : rad ≠ 0.
Proof.
destruct r as (rad, radi); simpl; flia radi.
Qed.

Hint Resolve radix_gt_0 radix_ge_1 radix_ne_0 radix_ge_2.

(* Digit *)

Record digit {r : radix} := mkdig { dig : nat; digit_lt_radix : dig < rad }.

Definition digit_0 {r : radix} := mkdig _ 0 radix_gt_0.

(* the proof that x≤y is unique; this is proved in Coq library, theorem
   "le_unique" *)
Theorem digit_eq_eq {r : radix} : ∀ a b, dig a = dig b ↔ a = b.
Proof.
intros.
split; intros H; [ | now subst ].
destruct a as (adig, adigi).
destruct b as (bdig, bdigi).
simpl in H.
subst bdig.
f_equal.
apply le_unique.
Qed.

Theorem digit_le_pred_radix {r : radix} : ∀ d, dig d ≤ rad - 1.
Proof.
intros.
specialize (digit_lt_radix d); flia.
Qed.

Definition d2n {r : radix} u (i : nat) := dig (u i).

Hint Resolve digit_lt_radix digit_le_pred_radix.

(* Frac Real *)

Delimit Scope freal_scope with F.

Record FracReal {r : radix} := { freal : nat → digit }.
Arguments freal r _%F.

Definition fd2n {r : radix} x (i : nat) := dig (freal x i).
Arguments fd2n _ x%F i%nat.

(* *)

Theorem fold_fd2n {r : radix} : ∀ x i, dig (freal x i) = fd2n x i.
Proof. easy. Qed.

Require Import PQ Nat_ggcd.

Theorem NQpower_summation (rg := NQ_ord_ring) : ∀ a n,
  a > 1
  → (Σ (i = 0, n), 1 // a ^ i = (a ^ S n - 1) // (a ^ n * (a - 1)))%NQ.
Proof.
intros * Ha.
induction n.
-rewrite summation_only_one.
 rewrite Nat.pow_0_r, Nat.pow_1_r, Nat.mul_1_l.
 apply NQeq_pair; [ easy | flia Ha | easy ].
-rewrite summation_split_last; [ | flia ].
 rewrite IHn.
 remember NQ_of_pair as f; remember S as g; simpl; subst f g.
 rewrite NQadd_pair; [ | | apply Nat.pow_nonzero; flia Ha ]; cycle 1. {
   intros H.
   apply Nat.eq_mul_0 in H.
   destruct H as [H| H]; [ | flia Ha H ].
   apply Nat.pow_nonzero in H; [ easy | flia Ha ].
 }
 rewrite Nat.mul_1_r.
 apply NQeq_pair. {
   intros H.
   apply Nat.eq_mul_0 in H.
   destruct H as [H| H].
   -apply Nat.eq_mul_0 in H.
    destruct H as [H| H]; [ | flia Ha H ].
    apply Nat.pow_nonzero in H; [ easy | flia Ha ].
   -apply Nat.pow_nonzero in H; [ easy | flia Ha ].
 } {
   intros H.
   apply Nat.eq_mul_0 in H.
   destruct H as [H| H]; [ | flia Ha H ].
   apply Nat.pow_nonzero in H; [ easy | flia Ha ].
 }
 rewrite Nat.mul_comm; symmetry.
 rewrite Nat.mul_shuffle0, Nat.mul_comm.
 do 2 rewrite <- Nat.mul_assoc; f_equal.
 rewrite Nat.mul_comm, <- Nat.mul_assoc; f_equal.
 rewrite Nat.mul_comm; symmetry.
 rewrite Nat.pow_succ_r' at 2.
 rewrite Nat.mul_assoc, Nat.mul_comm.
 rewrite <- Nat.mul_add_distr_l; f_equal.
 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
 rewrite Nat.add_sub_assoc; [ | flia Ha ].
 rewrite Nat.sub_add; [ now rewrite Nat.mul_comm | ].
 replace a with (1 * a) at 1 by flia.
 apply Nat.mul_le_mono_pos_r; [ flia Ha | ].
 apply Nat.neq_0_lt_0, Nat.pow_nonzero; flia Ha.
Qed.

Theorem power_summation (rg := nat_ord_ring) : ∀ a n,
  0 < a
  → a ^ S n = 1 + (a - 1) * Σ (i = 0, n), a ^ i.
Proof.
intros * Ha.
induction n.
 rewrite summation_only_one.
 rewrite Nat.pow_0_r, Nat.mul_1_r.
 rewrite Nat.pow_1_r; flia Ha.

 rewrite summation_split_last; [ | flia ].
 rewrite Nat.mul_add_distr_l.
 rewrite Nat.add_assoc.
 rewrite <- IHn.
 rewrite Nat.mul_sub_distr_r.
 simpl; rewrite Nat.add_0_r.
 rewrite Nat.add_sub_assoc.
  now rewrite Nat.add_comm, Nat.add_sub.

  apply Nat.mul_le_mono; [ easy | ].
  replace (a ^ n) with (1 * a ^ n) at 1 by flia.
  apply Nat.mul_le_mono_nonneg_r; flia Ha.
Qed.

Theorem power_summation_sub_1 (rg := nat_ord_ring) : ∀ a n,
  0 < a
  → a ^ S n - 1 = (a - 1) * Σ (i = 0, n), a ^ i.
Proof.
intros * Ha.
rewrite power_summation; [ | easy ].
rewrite Nat.add_comm.
now rewrite Nat.add_sub.
Qed.

(* In names, "9" actually means "rad-1" *)

Definition is_9_strict_after {r : radix} u i j :=
  if eq_nat_dec (d2n u (i + j + 1)) (rad - 1) then true else false.

Definition normalize {r : radix} (u : nat → digit) i :=
  match LPO_fst (is_9_strict_after u i) with
  | inl _ =>
     match lt_dec (S (d2n u i)) rad with
     | left P => mkdig _ (S (d2n u i)) P
     | right _ => digit_0
     end
  | inr _ => u i
 end.

Definition freal_normalize {r : radix} x :=
  {| freal i := normalize (freal x) i |}.

Arguments freal_normalize r x%F.

Definition has_same_digits {r : radix} x y i :=
  if Nat.eq_dec (fd2n x i) (fd2n y i) then true else false.

Definition freal_norm_eq {r : radix} x y := ∀ i, fd2n x i = fd2n y i.
Arguments freal_norm_eq _ x%F y%F.

Definition freal_norm_lt {r : radix} x y :=
  match LPO_fst (has_same_digits x y) with
  | inl _ => False
  | inr (exist _ i _) =>
      if lt_dec (fd2n x i) (fd2n y i) then True else False
  end.

Definition freal_norm_le {r : radix} x y :=
  match LPO_fst (has_same_digits x y) with
  | inl _ => True
  | inr (exist _ i _) =>
      if lt_dec (fd2n x i) (fd2n y i) then True else False
  end.

Definition freal_eq {r : radix} x y :=
  freal_norm_eq (freal_normalize x) (freal_normalize y).

Arguments freal_eq _ x%F y%F.

Definition freal_lt {r : radix} x y :=
  freal_norm_lt (freal_normalize x) (freal_normalize y).

Definition freal_le {r : radix} x y :=
  freal_norm_le (freal_normalize x) (freal_normalize y).

(*
Definition freal_0 {r : radix} := {| freal i := digit_0 |}.

Notation "0" := (freal_0) : freal_scope.
*)
Notation "a = b" := (freal_eq a b) : freal_scope.
(*
Notation "a ≠ b" := (¬ freal_eq a b) : freal_scope.
*)
Notation "a < b" := (freal_lt a b) : freal_scope.
Notation "a ≤ b" := (freal_le a b) : freal_scope.

Theorem is_9_strict_after_all_9 {r : radix} : ∀ u i,
  (∀ j, is_9_strict_after u i j = true)
  → (∀ k, d2n u (i + k + 1) = rad - 1).
Proof.
intros * Hm9 *.
specialize (Hm9 k); unfold is_9_strict_after in Hm9.
now destruct (Nat.eq_dec (d2n u (i + k + 1)) (rad - 1)).
Qed.

Theorem is_9_strict_after_true_iff {r : radix} : ∀ i j u,
  is_9_strict_after u i j = true ↔ d2n u (i + j + 1) = rad - 1.
Proof.
intros.
unfold is_9_strict_after.
now destruct (Nat.eq_dec (d2n u (i + j + 1)) (rad - 1)).
Qed.

Theorem is_9_strict_after_false_iff {r : radix} : ∀ i j u,
  is_9_strict_after u i j = false ↔ d2n u (i + j + 1) ≠ rad - 1.
Proof.
intros.
unfold is_9_strict_after.
now destruct (Nat.eq_dec (d2n u (i + j + 1)) (rad - 1)).
Qed.

(* Addition, Multiplication *)

Definition freal_add_series {r : radix} a b i := fd2n a i + fd2n b i.
Arguments freal_add_series _ a%F b%F.

Notation "x ⊕ y" := (freal_add_series x y) (at level 50).

(*
Definition sequence_mul (rg := nat_ord_ring) (a b : nat → nat) i :=
  Σ (j = 0, i), a j * b (i - j).

Definition freal_mul_series {r : radix} a b i :=
  match i with
  | 0 => 0
  | S i' => sequence_mul (fd2n a) (fd2n b) i'
  end.
*)

(**)
Definition A {r : radix} (rg := NQ_ord_ring) i n u :=
  (Σ (j = i + 1, n - 1), (u j // rad ^ (j - i))%NQ : NQ).
(**)

(*
Definition nA {r : radix} (rg := nat_ord_ring) i n u :=
  Σ (j = i + 1, n - 1), u j * rad ^ (n - 1 - j).
*)

Definition min_n {r : radix} i k := rad * (i + k + 3).

(**)
Definition fA_ge_1_ε {r : radix} u i k :=
  let n := min_n i k in
  let s := n - i - 1 in
  if NQlt_le_dec (NQfrac (A i n u)) (1 - 1 // rad ^ S k)%NQ then false else true.
(*
Definition A_ge_1 {r : radix} u i k :=
  let n := min_n i k in
  let s := n - i - 1 in
  if lt_dec (nA i n u mod rad ^ s) ((rad ^ S k - 1) * rad ^ (s - S k)) then
    false
  else
    true.
*)

(* Propagation of Carries *)

(**)
Definition nat_prop_carr {r : radix} u i :=
  match LPO_fst (fA_ge_1_ε u i) with
  | inl _ =>
      let n := min_n i 0 in
      NQintg (A i n u) + 1
  | inr (exist _ k _) =>
      let n := min_n i k in
      NQintg (A i n u)
  end.
(*
Definition nat_prop_carr {r : radix} u i :=
  match LPO_fst (A_ge_1 u i) with
  | inl _ =>
      let n := min_n i 0 in
      nA i n u / rad ^ (n - i - 1) + 1
  | inr (exist _ k _) =>
      let n := min_n i k in
      nA i n u / rad ^ (n - i - 1)
  end.
*)

Definition prop_carr {r : radix} u i :=
  let d := u i + nat_prop_carr u i in
  mkdig _ (d mod rad) (Nat.mod_upper_bound d rad radix_ne_0).

(*
Definition freal_mul_to_seq {r : radix} (a b : FracReal) :=
  prop_carr (freal_mul_series a b).
*)

Definition freal_add {r : radix} x y := {| freal := prop_carr (x ⊕ y) |}.
Arguments freal_add _ x%F y%F.

(*
Definition freal_mul {r : radix} (a b : FracReal) :=
  {| freal := freal_mul_to_seq a b |}.
*)

Notation "a + b" := (freal_add a b) : freal_scope.
(*
Notation "a * b" := (freal_mul a b) : freal_scope.
*)

Theorem freal_add_series_comm {r : radix} : ∀ x y i, (x ⊕ y) i = (y ⊕ x) i.
Proof.
intros.
unfold "⊕".
apply Nat.add_comm.
Qed.

(**)
Theorem A_freal_add_series_comm {r : radix} : ∀ x y i n,
  A i n (x ⊕ y) = A i n (y ⊕ x).
Proof.
intros.
unfold A; simpl.
apply summation_eq_compat; intros j Hj.
now rewrite freal_add_series_comm.
Qed.
(*
Theorem nA_freal_add_series_comm {r : radix} : ∀ x y i n,
  nA i n (x ⊕ y) = nA i n (y ⊕ x).
Proof.
intros.
unfold nA; simpl.
apply summation_eq_compat; intros j Hj.
now rewrite freal_add_series_comm.
Qed.
*)

(**)
Theorem A_ge_1_freal_add_series_comm {r : radix} : ∀ x y i k,
  fA_ge_1_ε (x ⊕ y) i k = fA_ge_1_ε (y ⊕ x) i k.
Proof.
intros.
unfold fA_ge_1_ε.
now rewrite A_freal_add_series_comm.
Qed.
(*
Theorem A_ge_1_freal_add_series_comm {r : radix} : ∀ x y i k,
  A_ge_1 (x ⊕ y) i k = A_ge_1 (y ⊕ x) i k.
Proof.
intros.
unfold A_ge_1.
now rewrite nA_freal_add_series_comm.
Qed.
*)

(**)
Theorem prop_carr_add_comm {r : radix} : ∀ x y i,
  prop_carr (x ⊕ y) i = prop_carr (y ⊕ x) i.
Proof.
intros.
apply digit_eq_eq; simpl.
unfold nat_prop_carr.
rewrite freal_add_series_comm.
destruct (LPO_fst (fA_ge_1_ε (x ⊕ y) i)) as [Hxy| Hxy].
-setoid_rewrite freal_add_series_comm.
 destruct (LPO_fst (fA_ge_1_ε (y ⊕ x) i)) as [Hyx| Hyx].
 +f_equal; f_equal; f_equal; f_equal.
  apply summation_eq_compat.
  intros k Hk; f_equal.
  apply freal_add_series_comm.
 +destruct Hyx as (k & Hjk & Hk).
  rewrite A_ge_1_freal_add_series_comm in Hk.
  now rewrite Hxy in Hk.
-destruct Hxy as (k & Hjk & Hk).
 rewrite A_ge_1_freal_add_series_comm in Hk.
 destruct (LPO_fst (fA_ge_1_ε (y ⊕ x) i)) as [Hyx| Hyx].
 +now rewrite Hyx in Hk.
 +destruct Hyx as (l & Hjl & Hl).
  destruct (lt_eq_lt_dec k l) as [ [ Hkl | Hkl ] | Hkl ].
  *apply Hjl in Hkl.
   now rewrite Hk in Hkl.
  *rewrite freal_add_series_comm, A_freal_add_series_comm.
   now subst k.
  *apply Hjk in Hkl.
   rewrite A_ge_1_freal_add_series_comm in Hkl.
   now rewrite Hl in Hkl.
Qed.
(*
Theorem prop_carr_add_comm {r : radix} : ∀ x y i,
  prop_carr (x ⊕ y) i = prop_carr (y ⊕ x) i.
Proof.
intros.
apply digit_eq_eq; simpl.
unfold nat_prop_carr.
rewrite freal_add_series_comm.
destruct (LPO_fst (A_ge_1 (x ⊕ y) i)) as [Hxy| Hxy].
-setoid_rewrite freal_add_series_comm.
 destruct (LPO_fst (A_ge_1 (y ⊕ x) i)) as [Hyx| Hyx].
 +f_equal; f_equal; f_equal; f_equal.
  apply summation_eq_compat.
  intros k Hk; f_equal.
  apply freal_add_series_comm.
 +destruct Hyx as (k & Hjk & Hk).
  rewrite A_ge_1_freal_add_series_comm in Hk.
  now rewrite Hxy in Hk.
-destruct Hxy as (k & Hjk & Hk).
 rewrite A_ge_1_freal_add_series_comm in Hk.
 destruct (LPO_fst (A_ge_1 (y ⊕ x) i)) as [Hyx| Hyx].
 +now rewrite Hyx in Hk.
 +destruct Hyx as (l & Hjl & Hl).
  destruct (lt_eq_lt_dec k l) as [ [ Hkl | Hkl ] | Hkl ].
  *apply Hjl in Hkl.
   now rewrite Hk in Hkl.
  *rewrite freal_add_series_comm, nA_freal_add_series_comm.
   now subst k.
  *apply Hjk in Hkl.
   rewrite A_ge_1_freal_add_series_comm in Hkl.
   now rewrite Hl in Hkl.
Qed.
*)

Theorem dig_unorm_add_comm {r : radix} : ∀ x y i,
  freal (x + y) i = freal (y + x) i.
Proof.
intros; simpl.
apply prop_carr_add_comm.
Qed.

Theorem has_same_digits_false_iff {r : radix} : ∀ x y i,
  has_same_digits x y i = false ↔ fd2n x i ≠ fd2n y i.
Proof.
intros.
unfold has_same_digits.
now destruct (Nat.eq_dec (fd2n x i) (fd2n y i)).
Qed.

Theorem has_same_digits_true_iff {r : radix} : ∀ x y i,
  has_same_digits x y i = true ↔ fd2n x i = fd2n y i.
Proof.
intros.
unfold has_same_digits.
now destruct (Nat.eq_dec (fd2n x i) (fd2n y i)).
Qed.

Theorem freal_add_comm {r : radix} : ∀ x y : FracReal,
  freal_norm_eq (x + y) (y + x).
Proof.
intros.
unfold freal_norm_eq.
remember (x + y)%F as nxy eqn:Hnxy.
remember (y + x)%F as nyx eqn:Hnyx.
intros i.
subst nxy nyx; unfold fd2n; f_equal.
apply dig_unorm_add_comm.
Qed.

Arguments freal_add_comm _ x%F y%F.

(**)
Theorem A_split_first {r : radix} : ∀ i n u,
  i + 1 ≤ n - 1
  → A i n u = (u (S i) // rad + A (S i) n u * 1 // rad)%NQ.
Proof.
intros * Hin.
unfold A.
rewrite summation_split_first; [ | easy ].
remember (1 // rad)%NQ as rr; simpl; subst rr.
rewrite Nat.add_1_r.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.sub_diag, Nat.pow_1_r.
f_equal.
rewrite summation_mul_distr_r.
apply summation_eq_compat.
intros j Hj.
rewrite NQmul_pair; [ | now apply Nat.pow_nonzero | easy ].
rewrite Nat.mul_1_r.
rewrite Nat.mul_comm, <- Nat.pow_succ_r'.
rewrite <- Nat.sub_succ_l; [ easy | flia Hj ].
Qed.
(*
Theorem nA_split_first {r : radix} : ∀ i n u,
  i + 1 ≤ n - 1
  → nA i n u = u (i + 1) * rad ^ (n - i - 2) + nA (S i) n u.
Proof.
intros * Hin.
unfold nA.
rewrite summation_split_first; [ | easy ].
simpl; f_equal; f_equal; f_equal; flia.
Qed.
*)

(**)
Theorem A_split_last {r : radix} : ∀ i n u,
  i + 1 ≤ n - 1
  → A i n u = (A i (n - 1) u + u (pred n) // rad ^ (n - i - 1))%NQ.
Proof.
intros * Hin.
unfold A.
replace (n - 1) with (S (n - 1 - 1)) at 1 by flia Hin.
rewrite summation_split_last; [ | flia Hin ].
simpl; f_equal.
replace (S (n - 1 - 1)) with (pred n) by flia Hin.
f_equal; f_equal.
destruct i; flia.
Qed.
(*
Theorem nA_split_last {r : radix} : ∀ i n u,
  i + 1 ≤ n - 1
  → nA i n u = rad * nA i (n - 1) u + u (n - 1).
Proof.
intros * Hin.
unfold nA.
replace (n - 1) with (S (n - 1 - 1)) at 1 by lia.
rewrite summation_split_last; [ | flia Hin ].
simpl; f_equal.
-rewrite summation_mul_distr_l; simpl.
 apply summation_eq_compat.
 intros j Hj.
 rewrite Nat.mul_assoc, Nat.mul_shuffle0, Nat.mul_comm.
 f_equal.
 replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
 rewrite <- Nat.pow_add_r; f_equal.
 flia Hj.
-replace (n - 1 - S (n - 1 - 1)) with 0 by flia Hin.
 rewrite Nat.pow_0_r, Nat.mul_1_r; f_equal.
 flia Hin.
Qed.
*)

(**)
Theorem A_split {r : radix} : ∀ e u i n,
  i + 1 ≤ e - 1 ≤ n - 1
  → A i n u = (A i e u + A (e - 1) n u * 1 // rad ^ (e - i - 1))%NQ.
Proof.
intros * Hin.
unfold A.
rewrite summation_split with (e0 := e - 1); [ | easy ].
remember (1 // rad ^ (e - i - 1))%NQ as rr; simpl; subst rr; f_equal.
rewrite summation_mul_distr_r.
replace (e - 1 + 1) with (S (e - 1)) by flia.
apply summation_eq_compat.
intros j Hj.
rewrite NQmul_pair; try now apply Nat.pow_nonzero.
rewrite Nat.mul_1_r; f_equal.
rewrite <- Nat.pow_add_r; f_equal.
flia Hj Hin.
Qed.
(*
Theorem nA_split {r : radix} : ∀ e u i n,
  i + 1 ≤ e - 1 ≤ n - 1
  → nA i n u = nA i e u * rad ^ (n - e) + nA (e - 1) n u.
Proof.
intros * Hin.
unfold nA.
rewrite summation_split with (e0 := e - 1); [ | easy ].
simpl; f_equal.
+rewrite summation_mul_distr_r.
 apply summation_eq_compat.
 intros j Hj; simpl.
 rewrite <- Nat.mul_assoc; f_equal.
 rewrite <- Nat.pow_add_r.
 now replace (e - 1 - j + (n - e)) with (n - 1 - j) by flia Hin Hj.
+now rewrite Nat.add_1_r.
Qed.
*)

Theorem Nat_pow_ge_1 : ∀ a b, 0 < a → 1 ≤ a ^ b.
Proof.
intros * Ha.
induction b; [ easy | simpl ].
replace 1 with (1 * 1) by flia.
apply Nat.mul_le_mono_nonneg; [ flia | easy | flia | easy ].
Qed.

(**)
Theorem A_dig_seq_ub {r : radix} : ∀ u n i,
  (∀ j, i < j < n → u j < rad)
  → i + 1 ≤ n - 1
  → (A i n u < 1)%NQ.
Proof.
intros * Hu Hin.
specialize radix_ge_2 as Hr.
apply (NQle_lt_trans _ (A i n (λ i, rad - 1))).
-apply summation_le_compat; intros j Hj; simpl.
 apply NQle_pair; [ now apply Nat.pow_nonzero | now apply Nat.pow_nonzero | ].
 rewrite Nat.mul_comm.
 apply Nat.mul_le_mono_l.
 specialize (Hu j).
 assert (H : i < j < n) by flia Hj.
 specialize (Hu H); clear H.
 flia Hu.
-unfold A.
 rewrite summation_shift; [ | easy ].
 replace (n - 1 - (i + 1)) with (n - i - 2) by flia.
 rewrite summation_eq_compat with
   (h := λ j, ((rad - 1) // rad * 1 // (rad ^ j))%NQ); cycle 1. {
   intros j Hj.
   rewrite NQmul_pair; [ | easy | now apply Nat.pow_nonzero ].
   rewrite Nat.mul_1_r.
   now replace (i + 1 + j - i) with (S j) by flia.
 }
 rewrite <- summation_mul_distr_l.
 remember 1%NQ as one; remember NQ_of_pair as f; simpl; subst f one.
 rewrite NQpower_summation; [ | easy ].
 rewrite NQmul_pair; [ | easy | ]; cycle 1. {
   intros H; apply Nat.eq_mul_0 in H.
   destruct H as [H| H]; [ now apply Nat.pow_nonzero in H | flia H Hr ].
 }
 rewrite Nat.mul_comm, Nat.mul_assoc.
 rewrite <- NQmul_pair; [ | | flia Hr ]; cycle 1. {
   intros H; apply Nat.eq_mul_0 in H.
   destruct H as [H| H]; [ flia H Hr | now apply Nat.pow_nonzero in H ].
 }
 rewrite NQpair_diag; [ rewrite NQmul_1_r | flia Hr ].
 rewrite <- Nat.pow_succ_r'.
 apply NQlt_pair; [ now apply Nat.pow_nonzero | easy | ].
 do 2 rewrite Nat.mul_1_r.
 apply Nat.sub_lt; [ | apply Nat.lt_0_1 ].
 now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.
(*
Theorem nA_dig_seq_ub {r : radix} : ∀ u n i,
  (∀ j, i < j < n → u j < rad) →
  i + 1 ≤ n - 1
  → nA i n u < rad ^ (n - i - 1).
Proof.
intros * Hu Hin.
unfold nA.
rewrite summation_rtl.
rewrite summation_shift; [ | easy ].
remember (n - i - 1) as k eqn:Hk.
destruct k; [ flia Hin Hk | ].
rewrite power_summation; [ | easy ].
replace (n - 1 - (i + 1)) with k by flia Hk.
unfold lt; simpl.
apply -> Nat.succ_le_mono.
rewrite summation_mul_distr_l.
apply (@summation_le_compat _ nat_ord_ring).
intros j Hj.
replace (n - 1 + (i + 1) - (i + 1 + j)) with (n - 1 - j) by flia.
replace (n - 1 - (n - 1 - j)) with j by flia Hk Hj.
apply Nat.mul_le_mono_nonneg_r; [ flia | ].
apply Nat.le_add_le_sub_l.
apply Hu; flia Hk Hj.
Qed.
*)

Theorem A_all_9 {r : radix} : ∀ u i n,
  (∀ j, i + j + 1 < n → u (i + j + 1) = rad - 1)
  → A i n u = (1 - 1 // rad ^ (n - i - 1))%NQ.
Proof.
intros * Hj.
specialize radix_ge_2 as Hr.
unfold A.
destruct (le_dec (i + 1) (n - 1)) as [Hin| Hin]; cycle 1. {
  replace (n - i - 1) with 0 by flia Hin.
  rewrite Nat.pow_0_r, NQsub_diag.
  now rewrite summation_empty; [ | flia Hin ].
}
rewrite summation_shift; [ | easy ].
rewrite summation_eq_compat with
    (h := λ j, ((rad - 1) // rad * 1 // rad ^ j)%NQ); cycle 1. {
  intros j Hij.
  rewrite NQmul_pair; [ | easy | now apply Nat.pow_nonzero ].
  rewrite Nat.mul_1_r, Nat.add_shuffle0, Nat.mul_comm.
  replace rad with (rad ^ 1) at 4 by apply Nat.pow_1_r.
  rewrite <- Nat.pow_add_r.
  replace (i + j + 1 - i) with (j + 1) by flia; f_equal.
  rewrite Hj; [ easy | flia Hin Hij ].
}
rewrite <- summation_mul_distr_l.
remember NQ_of_pair as f; remember 1%NQ as x; simpl; subst f x.
rewrite NQpower_summation; [ | flia Hr ].
replace (n - 1 - (i + 1)) with (n - i - 1 - 1) by flia Hin.
remember (n - i - 1) as s eqn:Hs.
replace (S (s - 1)) with s by flia Hs Hin.
rewrite NQsub_pair_pos; [ | easy | now apply Nat.pow_nonzero | ]; cycle 1. {
  apply Nat.mul_lt_mono_pos_l; [ apply Nat.lt_0_1 | ].
  apply lt_le_trans with (m := 2); [ apply Nat.lt_1_2 | ].
  destruct s; [ flia Hs Hin | ].
  simpl; replace 2 with (2 * 1) by easy.
  apply Nat.mul_le_mono; [ easy | ].
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
do 2 rewrite Nat.mul_1_l.
rewrite NQmul_pair; [ | easy | ]; cycle 1. {
  intros H; apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ now apply Nat.pow_nonzero in H | flia Hr H ].
}
rewrite Nat.mul_assoc, Nat.mul_comm.
rewrite <- NQmul_pair; [ | | flia Hr ]; cycle 1. {
  replace rad with (rad ^ 1) at 1 by apply Nat.pow_1_r.
  rewrite <- Nat.pow_add_r.
  now apply Nat.pow_nonzero.
}
rewrite NQpair_diag; [ | flia Hr ].
rewrite NQmul_1_r.
replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
rewrite <- Nat.pow_add_r.
now replace (1 + (s - 1)) with s by flia Hs Hin.
Qed.
(*
Theorem nA_all_9 {r : radix} : ∀ u i n,
  (∀ j, i + j + 1 < n → u (i + j + 1) = rad - 1)
  → nA i n u = rad ^ (n - i - 1) - 1.
Proof.
intros * Hj.
unfold nA.
rewrite summation_eq_compat with (h := λ j, (rad - 1) * rad ^ (n - 1 - j)).
-rewrite <- summation_mul_distr_l.
 destruct (le_dec (i + 1) (n - 1)) as [Hin| Hin].
 +rewrite summation_shift; [ | easy ].
  rewrite summation_rtl.
  rewrite summation_eq_compat with (h := λ j, rad ^ j).
  *apply Nat.succ_inj_wd.
   rewrite <- Nat.add_1_l.
   rewrite <- power_summation; [ symmetry | easy ].
   rewrite <- Nat.sub_succ_l; [ | now apply Nat_pow_ge_1 ].
   rewrite Nat.sub_succ, Nat.sub_0_r.
   f_equal; flia Hin.
  *intros k Hk; f_equal; flia Hk.
 +replace (n - i - 1) with 0 by flia Hin.
  rewrite summation_empty; [ | flia Hin ].
  rewrite Nat.mul_0_r; simpl; flia.
-intros j Hij.
 replace j with (i + (j - i - 1) + 1) at 1 by flia Hij.
 rewrite Hj; [ easy | flia Hij ].
Qed.
*)

(**)
Theorem A_all_18 {r : radix} : ∀ u i n,
  (∀ j, u (i + j + 1) = 2 * (rad - 1))
  → A i n u = (2 - 2 // rad ^ (n - i - 1))%NQ.
Proof.
intros * Hj.
specialize radix_ge_2 as Hr.
unfold A.
destruct (le_dec (i + 1) (n - 1)) as [Hin| Hin]; cycle 1. {
  replace (n - i - 1) with 0 by flia Hin.
  rewrite Nat.pow_0_r, NQsub_diag.
  now rewrite summation_empty; [ | flia Hin ].
}
rewrite summation_shift; [ | easy ].
rewrite summation_eq_compat with
    (h := λ j, (2 * (rad - 1) // rad * 1 // rad ^ j)%NQ); cycle 1. {
  intros j Hij.
  rewrite <- NQmul_assoc.
  rewrite NQmul_pair; [ | easy | now apply Nat.pow_nonzero ].
  rewrite Nat.mul_1_r, Nat.add_shuffle0, Nat.mul_comm.
  replace rad with (rad ^ 1) at 4 by apply Nat.pow_1_r.
  rewrite <- Nat.pow_add_r.
  replace (i + j + 1 - i) with (j + 1) by flia; f_equal.
  rewrite Hj.
  rewrite NQmul_pair; [ | easy | now apply Nat.pow_nonzero ].
  now rewrite Nat.mul_1_l.
}
rewrite <- summation_mul_distr_l.
remember NQ_of_pair as f; simpl; subst f.
rewrite NQpower_summation; [ | flia Hr ].
replace (n - 1 - (i + 1)) with (n - i - 1 - 1) by flia Hin.
remember (n - i - 1) as s eqn:Hs.
replace (S (s - 1)) with s by flia Hs Hin.
rewrite NQsub_pair_pos; [ | easy | now apply Nat.pow_nonzero | ]; cycle 1. {
  rewrite Nat.mul_comm.
  apply Nat.mul_lt_mono_pos_l; [ apply Nat.lt_0_2 | ].
  apply lt_le_trans with (m := 2); [ apply Nat.lt_1_2 | ].
  destruct s; [ flia Hs Hin | ].
  simpl; replace 2 with (2 * 1) by easy.
  apply Nat.mul_le_mono; [ easy | ].
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
do 2 rewrite Nat.mul_1_l.
rewrite NQmul_pair; [ | easy | easy ].
rewrite Nat.mul_1_l.
rewrite NQmul_pair; [ | easy | ]; cycle 1. {
  intros H; apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ | flia Hr H ].
  now apply Nat.pow_nonzero in H.
}
rewrite Nat.mul_shuffle0, Nat.mul_assoc.
rewrite <- NQmul_pair; [ | | flia Hr ]; cycle 1. {
  intros H; apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ flia Hr H | ].
  now apply Nat.pow_nonzero in H.
}
rewrite NQpair_diag; [ | flia Hr ].
rewrite NQmul_1_r.
replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
rewrite <- Nat.pow_add_r.
replace (1 + (s - 1)) with s by flia Hs Hin.
now rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
Qed.
(*
Theorem nA_all_18 {r : radix} : ∀ u i n,
  (∀ j, u (i + j + 1) = 2 * (rad - 1))
  → nA i n u = 2 * (rad ^ (n - i - 1) - 1).
Proof.
intros * Hj.
unfold nA.
rewrite summation_eq_compat with (h := λ j, 2 * (rad - 1) * rad ^ (n - 1 - j)).
-rewrite <- summation_mul_distr_l.
 destruct (le_dec (i + 1) (n - 1)) as [Hin| Hin].
 +rewrite summation_shift; [ | easy ].
  rewrite summation_rtl.
  rewrite summation_eq_compat with (h := λ j, rad ^ j).
  *rewrite <- Nat.mul_assoc.
   rewrite <- power_summation_sub_1; [ | easy ].
   f_equal; f_equal; f_equal; flia Hin.
  *intros k Hk; f_equal; flia Hk.
 +replace (n - i - 1) with 0 by flia Hin.
  rewrite summation_empty; [ | flia Hin ].
  rewrite Nat.mul_0_r; simpl; flia.
-intros j Hij.
 replace j with (i + (j - i - 1) + 1) at 1 by flia Hij.
 now rewrite Hj.
Qed.
*)

(**)
Theorem nA_9_8_all_18 {r : radix} : ∀ j u i n,
  (∀ k, k < j → u (i + k + 1) = rad - 1)
  → u (i + j + 1) = rad - 2
  → (∀ k, u (i + j + k + 2) = 2 * (rad - 1))
  → A i n u =
       (1 -
        (if le_dec (i + j + 1) (n - 1) then 2 else 1) //
        rad ^ (n - i - 1))%NQ.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hbef Hwhi Haft.
destruct (le_dec (i + j + 1) (n - 1)) as [Hin| Hin]; cycle 1. {
  apply A_all_9.
  intros k Hk.
  apply Hbef; flia Hin Hk.
}
rewrite A_split with (e := i + j + 2); [ | flia Hin ].
replace (i + j + 2 - 1) with (i + j + 1) by flia.
destruct (zerop j) as [Hj| Hj].
-subst j; clear Hbef.
 rewrite Nat.add_0_r in Hin, Haft, Hwhi |-*.
 unfold A at 1.
 replace (i + 2 - 1) with (i + 1) by flia.
 replace (i + 2 - i - 1) with 1 by flia.
 rewrite Nat.pow_1_r.
 rewrite summation_only_one, Hwhi.
 rewrite A_all_18; cycle 1. {
   intros j.
   replace (i + 1 + j + 1) with (i + j + 2) by flia.
   apply Haft.
 }
 replace (n - (i + 1) - 1) with (n - i - 2) by flia.
 replace (i + 1 - i) with 1 by flia.
 rewrite Nat.pow_1_r.
 rewrite NQmul_sub_distr_r.
 rewrite NQmul_pair; [ | easy | easy ].
 rewrite Nat.mul_1_r, Nat.mul_1_l.
 rewrite NQmul_pair; [ | now apply Nat.pow_nonzero | easy ].
 rewrite Nat.mul_1_r.
 replace rad with (rad ^ 1) at 5 by apply Nat.pow_1_r.
 rewrite <- Nat.pow_add_r.
 replace (n - i - 2 + 1) with (n - i - 1) by flia Hin.
 destruct (eq_nat_dec (n - i - 1) 1) as [H1| H1].
 +rewrite H1, Nat.pow_1_r.
  rewrite NQsub_diag, NQadd_0_r.
  destruct (eq_nat_dec rad 2) as [H2| H2]; [ now rewrite H2 | ].
  rewrite NQsub_pair_pos; [ | easy | easy | ]; cycle 1. {
    apply Nat.mul_lt_mono_pos_l; [ apply Nat.lt_0_1 | flia Hr H2 ].
  }
  now do 2 rewrite Nat.mul_1_l.
 +rewrite NQsub_pair_pos; [ | easy | now apply Nat.pow_nonzero | ]; cycle 1. {
    rewrite Nat.mul_comm.
    apply Nat.mul_lt_mono_pos_l; [ apply Nat.lt_0_2 | ].
    replace rad with (rad ^ 1) at 1 by apply Nat.pow_1_r.
    apply Nat.pow_lt_mono_r; [ easy | flia Hin H1 ].
  }
  replace rad with (rad ^ 1) at 5 by apply Nat.pow_1_r.
  rewrite <- Nat.pow_add_r.
  rewrite NQadd_pair; [ | easy | now apply Nat.pow_nonzero ].
  rewrite Nat.mul_sub_distr_l.
  rewrite Nat.mul_assoc, Nat.mul_shuffle0.
  replace rad with (rad ^ 1) at 3 by apply Nat.pow_1_r.
  rewrite <- Nat.pow_add_r.
  replace (1 + (n - i - 1)) with (n - i) by flia Hin.
  rewrite Nat.add_sub_assoc; cycle 1. {
    rewrite Nat.mul_assoc.
    apply Nat.mul_le_mono_r.
    replace (rad * rad) with (rad ^ 2) by now simpl; rewrite Nat.mul_1_r.
    apply Nat.pow_le_mono_r; [ easy | flia Hin H1 ].
  }
  rewrite Nat.mul_comm, Nat.mul_sub_distr_l.
  rewrite Nat.sub_add; [ | now apply Nat.mul_le_mono_l ].
  rewrite NQsub_pair_pos; [ | easy | now apply Nat.pow_nonzero | ]; cycle 1. {
    apply Nat.mul_lt_mono_pos_l; [ apply Nat.lt_0_1 | ].
    remember (n - i - 1) as m eqn:Hm; symmetry in Hm.
    destruct m; [ flia Hm Hin | ].
    destruct m; [ flia H1 | rewrite Nat.pow_succ_r' ].
...
    destruct rad as [| rr]; [ easy | ].
    destruct rr; [ flia Hr | ].
...
    replace 2 with (1 * 2) at 1 by flia.
    apply Nat.mul_lt_mono; [ easy | ].
...
    apply lt_le_trans with (m := 3).
...

 rewrite NQsub_pair_pos; [ | easy | now apply Nat.pow_nonzero | ]; cycle 1. {
   rewrite Nat.mul_comm.
   apply Nat.mul_lt_mono_pos_l; [ apply Nat.lt_0_2 | ].

...

 replace (n - (i + 2)) with (n - i - 2) by flia.
   rewrite Nat.mul_sub_distr_r, Nat.mul_sub_distr_l, Nat.mul_1_r.
   rewrite Nat.add_sub_assoc.
  --rewrite Nat.sub_add.
   ++rewrite <- Nat.pow_succ_r'; f_equal; f_equal; flia H1.
   ++apply Nat.mul_le_mono_r; flia Hr.
  --replace 2 with (2 * 1) at 1 by flia.
    apply Nat.mul_le_mono_l.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *intros j.
   replace (i + 1 + j + 1) with (i + j + 2) by flia.
   apply Haft.
 +rewrite nA_split with (e := i + j + 1); [ | flia H1 Hj ].
  replace (i + j + 1 - 1) with (i + j) by flia.
  replace (i + j + 2 - (i + j + 1)) with 1 by flia.
  rewrite Nat.pow_1_r.
  rewrite nA_all_9.
  *replace (i + j + 1 - i - 1) with j by flia.
   unfold nA at 1.
   replace (i + j + 2 - 1) with (i + j + 1) by flia.
   rewrite summation_only_one, Hwhi.
   rewrite Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r.
   rewrite nA_all_18.
  --replace (n - (i + j + 1) - 1) with (n - i - j - 2) by flia.
    replace (n - (i + j + 2)) with (n - i - j - 2) by flia.
    rewrite Nat.mul_sub_distr_r, Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.mul_1_l, Nat.sub_add.
   ++rewrite Nat.mul_sub_distr_r, Nat.mul_sub_distr_l, Nat.mul_1_r.
     rewrite Nat.add_sub_assoc.
    **rewrite Nat.sub_add.
    ---rewrite <- Nat.mul_assoc, <- Nat.pow_succ_r'.
       rewrite <- Nat.pow_add_r.
       f_equal; f_equal; flia H1.
    ---apply Nat.mul_le_mono_r.
       replace 2 with (1 * 2) at 1 by flia.
       apply Nat.mul_le_mono; [ | easy ].
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    **replace 2 with (2 * 1) at 1 by flia.
      apply Nat.mul_le_mono_l.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   ++replace rad with (1 * rad) at 1 by flia.
     apply Nat.mul_le_mono_r.
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  --intros k.
    replace (i + j + 1 + k + 1) with (i + j + k + 2) by flia.
    apply Haft.
  *intros k Hk.
   apply Hbef; flia Hk.
...
unfold A.
rewrite summation_shift; [ | flia Hin ].
...
rewrite summation_eq_compat with
    (h := λ j, (2 * (rad - 1) // rad * 1 // rad ^ j)%NQ); cycle 1. {
  intros k Hk.
  rewrite <- NQmul_assoc.
  rewrite NQmul_pair; [ | easy | now apply Nat.pow_nonzero ].
  rewrite Nat.mul_1_r, Nat.add_shuffle0, Nat.mul_comm.
  replace rad with (rad ^ 1) at 4 by apply Nat.pow_1_r.
  rewrite <- Nat.pow_add_r.
  replace (i + k + 1 - i) with (k + 1) by flia.

  rewrite Hbef.
  rewrite NQmul_pair; [ | easy | now apply Nat.pow_nonzero ].
  now rewrite Nat.mul_1_l.
}
rewrite <- summation_mul_distr_l.
remember NQ_of_pair as f; simpl; subst f.
rewrite NQpower_summation; [ | flia Hr ].
replace (n - 1 - (i + 1)) with (n - i - 1 - 1) by flia Hin.
remember (n - i - 1) as s eqn:Hs.
replace (S (s - 1)) with s by flia Hs Hin.
rewrite NQsub_pair_pos; [ | easy | now apply Nat.pow_nonzero | ]; cycle 1. {
  rewrite Nat.mul_comm.
  apply Nat.mul_lt_mono_pos_l; [ apply Nat.lt_0_2 | ].
  apply lt_le_trans with (m := 2); [ apply Nat.lt_1_2 | ].
  destruct s; [ flia Hs Hin | ].
  simpl; replace 2 with (2 * 1) by easy.
  apply Nat.mul_le_mono; [ easy | ].
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
do 2 rewrite Nat.mul_1_l.
rewrite NQmul_pair; [ | easy | easy ].
rewrite Nat.mul_1_l.
rewrite NQmul_pair; [ | easy | ]; cycle 1. {
  intros H; apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ | flia Hr H ].
  now apply Nat.pow_nonzero in H.
}
rewrite Nat.mul_shuffle0, Nat.mul_assoc.
rewrite <- NQmul_pair; [ | | flia Hr ]; cycle 1. {
  intros H; apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ flia Hr H | ].
  now apply Nat.pow_nonzero in H.
}
rewrite NQpair_diag; [ | flia Hr ].
rewrite NQmul_1_r.
replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
rewrite <- Nat.pow_add_r.
replace (1 + (s - 1)) with s by flia Hs Hin.
now rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
...

intros *.
specialize radix_ge_2 as Hr.
intros Hbef Hwhi Haft.
destruct (le_dec (i + j + 1) (n - 1)) as [H1| H1].
...
-rewrite nA_split with (e := i + j + 2); [ | flia H1 ].
 replace (i + j + 2 - 1) with (i + j + 1) by flia.
 destruct (zerop j) as [Hj| Hj].
 +subst j; clear Hbef.
  rewrite Nat.add_0_r in H1, Haft, Hwhi |-*.
  unfold nA at 1.
  replace (i + 2 - 1) with (i + 1) by flia.
  rewrite summation_only_one, Hwhi.
  rewrite Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r.
  rewrite nA_all_18.
  *replace (n - (i + 1) - 1) with (n - i - 2) by flia.
   replace (n - (i + 2)) with (n - i - 2) by flia.
   rewrite Nat.mul_sub_distr_r, Nat.mul_sub_distr_l, Nat.mul_1_r.
   rewrite Nat.add_sub_assoc.
  --rewrite Nat.sub_add.
   ++rewrite <- Nat.pow_succ_r'; f_equal; f_equal; flia H1.
   ++apply Nat.mul_le_mono_r; flia Hr.
  --replace 2 with (2 * 1) at 1 by flia.
    apply Nat.mul_le_mono_l.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *intros j.
   replace (i + 1 + j + 1) with (i + j + 2) by flia.
   apply Haft.
 +rewrite nA_split with (e := i + j + 1); [ | flia H1 Hj ].
  replace (i + j + 1 - 1) with (i + j) by flia.
  replace (i + j + 2 - (i + j + 1)) with 1 by flia.
  rewrite Nat.pow_1_r.
  rewrite nA_all_9.
  *replace (i + j + 1 - i - 1) with j by flia.
   unfold nA at 1.
   replace (i + j + 2 - 1) with (i + j + 1) by flia.
   rewrite summation_only_one, Hwhi.
   rewrite Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r.
   rewrite nA_all_18.
  --replace (n - (i + j + 1) - 1) with (n - i - j - 2) by flia.
    replace (n - (i + j + 2)) with (n - i - j - 2) by flia.
    rewrite Nat.mul_sub_distr_r, Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.mul_1_l, Nat.sub_add.
   ++rewrite Nat.mul_sub_distr_r, Nat.mul_sub_distr_l, Nat.mul_1_r.
     rewrite Nat.add_sub_assoc.
    **rewrite Nat.sub_add.
    ---rewrite <- Nat.mul_assoc, <- Nat.pow_succ_r'.
       rewrite <- Nat.pow_add_r.
       f_equal; f_equal; flia H1.
    ---apply Nat.mul_le_mono_r.
       replace 2 with (1 * 2) at 1 by flia.
       apply Nat.mul_le_mono; [ | easy ].
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    **replace 2 with (2 * 1) at 1 by flia.
      apply Nat.mul_le_mono_l.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   ++replace rad with (1 * rad) at 1 by flia.
     apply Nat.mul_le_mono_r.
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  --intros k.
    replace (i + j + 1 + k + 1) with (i + j + k + 2) by flia.
    apply Haft.
  *intros k Hk.
   apply Hbef; flia Hk.
-apply nA_all_9.
 intros k Hk.
 apply Hbef; flia H1 Hk.
Qed.
(*
Theorem nA_9_8_all_18 {r : radix} : ∀ j u i n,
  (∀ k, k < j → u (i + k + 1) = rad - 1)
  → u (i + j + 1) = rad - 2
  → (∀ k, u (i + j + k + 2) = 2 * (rad - 1))
  → nA i n u =
       rad ^ (n - i - 1) - if le_dec (i + j + 1) (n - 1) then 2 else 1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hbef Hwhi Haft.
destruct (le_dec (i + j + 1) (n - 1)) as [H1| H1].
-rewrite nA_split with (e := i + j + 2); [ | flia H1 ].
 replace (i + j + 2 - 1) with (i + j + 1) by flia.
 destruct (zerop j) as [Hj| Hj].
 +subst j; clear Hbef.
  rewrite Nat.add_0_r in H1, Haft, Hwhi |-*.
  unfold nA at 1.
  replace (i + 2 - 1) with (i + 1) by flia.
  rewrite summation_only_one, Hwhi.
  rewrite Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r.
  rewrite nA_all_18.
  *replace (n - (i + 1) - 1) with (n - i - 2) by flia.
   replace (n - (i + 2)) with (n - i - 2) by flia.
   rewrite Nat.mul_sub_distr_r, Nat.mul_sub_distr_l, Nat.mul_1_r.
   rewrite Nat.add_sub_assoc.
  --rewrite Nat.sub_add.
   ++rewrite <- Nat.pow_succ_r'; f_equal; f_equal; flia H1.
   ++apply Nat.mul_le_mono_r; flia Hr.
  --replace 2 with (2 * 1) at 1 by flia.
    apply Nat.mul_le_mono_l.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *intros j.
   replace (i + 1 + j + 1) with (i + j + 2) by flia.
   apply Haft.
 +rewrite nA_split with (e := i + j + 1); [ | flia H1 Hj ].
  replace (i + j + 1 - 1) with (i + j) by flia.
  replace (i + j + 2 - (i + j + 1)) with 1 by flia.
  rewrite Nat.pow_1_r.
  rewrite nA_all_9.
  *replace (i + j + 1 - i - 1) with j by flia.
   unfold nA at 1.
   replace (i + j + 2 - 1) with (i + j + 1) by flia.
   rewrite summation_only_one, Hwhi.
   rewrite Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r.
   rewrite nA_all_18.
  --replace (n - (i + j + 1) - 1) with (n - i - j - 2) by flia.
    replace (n - (i + j + 2)) with (n - i - j - 2) by flia.
    rewrite Nat.mul_sub_distr_r, Nat.add_sub_assoc; [ | easy ].
    rewrite Nat.mul_1_l, Nat.sub_add.
   ++rewrite Nat.mul_sub_distr_r, Nat.mul_sub_distr_l, Nat.mul_1_r.
     rewrite Nat.add_sub_assoc.
    **rewrite Nat.sub_add.
    ---rewrite <- Nat.mul_assoc, <- Nat.pow_succ_r'.
       rewrite <- Nat.pow_add_r.
       f_equal; f_equal; flia H1.
    ---apply Nat.mul_le_mono_r.
       replace 2 with (1 * 2) at 1 by flia.
       apply Nat.mul_le_mono; [ | easy ].
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    **replace 2 with (2 * 1) at 1 by flia.
      apply Nat.mul_le_mono_l.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   ++replace rad with (1 * rad) at 1 by flia.
     apply Nat.mul_le_mono_r.
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  --intros k.
    replace (i + j + 1 + k + 1) with (i + j + k + 2) by flia.
    apply Haft.
  *intros k Hk.
   apply Hbef; flia Hk.
-apply nA_all_9.
 intros k Hk.
 apply Hbef; flia H1 Hk.
Qed.
*)

Theorem A_ge_1_false_iff {r : radix} : ∀ i u k,
  let n := min_n i k in
  let s := n - i - 1 in
  A_ge_1 u i k = false ↔
  nA i n u mod rad ^ s < (rad ^ S k - 1) * rad ^ (s - S k).
Proof.
intros.
unfold A_ge_1.
fold n s.
set (t := rad ^ (s - S k)).
now destruct (lt_dec (nA i n u mod rad ^ s) ((rad ^ S k - 1) * t)).
Qed.

Theorem A_ge_1_true_iff {r : radix} : ∀ i u k,
  let n := min_n i k in
  let s := n - i - 1 in
  A_ge_1 u i k = true ↔
  nA i n u mod rad ^ s ≥ (rad ^ S k - 1) * rad ^ (s - S k).
Proof.
intros.
unfold A_ge_1.
fold n s.
set (t := rad ^ (s - S k)).
destruct (lt_dec (nA i n u mod rad ^ s) ((rad ^ S k - 1) * t)) as [H1| H1].
-now split; [ | apply Nat.nle_gt in H1 ].
-now split; [ apply Nat.nlt_ge in H1 | ].
Qed.

Theorem when_99000_le_uuu00 {r : radix} : ∀ u i j k n,
  (∀ k, u (S i + k) < rad)
  → (rad ^ S j - 1) * rad ^ (n - i - 1 - S j) ≤ nA i n u
  → S j ≤ n - i - 1
  → i + 1 ≤ k ≤ i + j + 1
  → u k = rad - 1.
Proof.
intros * Hu HnA Hj Hk.
apply Nat.mul_le_mono_pos_r with (p := rad ^ S j) in HnA.
2: now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
rewrite <- Nat.mul_assoc in HnA.
rewrite <- Nat.pow_add_r in HnA.
rewrite Nat.sub_add in HnA; [ | easy ].
remember (n - i - 1) as s eqn:Hs.
assert (Hsz : rad ^ s ≠ 0) by now subst s; apply Nat.pow_nonzero.
apply Nat.div_le_mono with (c := rad ^ s) in HnA; [ | easy ].
rewrite Nat.div_mul in HnA; [ | easy ].
assert (H : nA i n u * rad ^ S j / rad ^ s = nA i (i + j + 2) u). {
(**)
  replace s with (s - S j + S j) by flia Hj.
  rewrite Nat.pow_add_r.
  rewrite Nat.div_mul_cancel_r; try now apply Nat.pow_nonzero.
  replace (s - S j) with (n - i - j - 2) by flia Hs.
  unfold nA at 1.
  rewrite summation_split with (e := i + j + 1); [ | flia Hs Hj ].
  simpl; unfold nA.
  replace (i + j + 2 - 1) with (i + j + 1) by flia.
  rewrite summation_eq_compat with
      (h := λ k, u k * rad ^ (i + j + 1 - k) * rad ^ (n - i - j - 2)).
  -rewrite <- summation_mul_distr_r; simpl.
   rewrite Nat.add_comm.
   rewrite Nat.div_add; [ | now apply Nat.pow_nonzero ].
   rewrite Nat.div_small; [ easy | ].
   remember (n - i - j - 2) as m eqn:Hm.
   symmetry in Hm.
   destruct m.
   +rewrite summation_empty; [ | flia Hj Hm ].
    now apply Nat_pow_ge_1.
   +rewrite power_summation; [ | easy ].
    rewrite summation_mul_distr_l; simpl.
    rewrite summation_shift; [ | flia Hm ].
    replace (n - 1 - S (i + j + 1)) with m by flia Hm.
    apply -> Nat.succ_le_mono.
    rewrite summation_rtl.
    rewrite summation_eq_compat with
       (h := λ k, u (S (i + j + 1 + m - k)) * rad ^ k).
    *apply (@summation_le_compat nat_ord_ring_def).
     intros p Hp; simpl; unfold Nat.le.
     apply Nat.mul_le_mono_r.
     specialize (Hu (j + 1 + m - p)); simpl in Hu.
     rewrite Nat.add_sub_assoc in Hu; [ | flia Hp ].
     do 2 rewrite Nat.add_assoc in Hu.
     flia Hu.
    *intros p Hp.
     f_equal; f_equal; [ flia Hp | flia Hm Hp ].
  -intros p Hp.
   rewrite <- Nat.mul_assoc; f_equal.
   rewrite <- Nat.pow_add_r; f_equal.
   flia Hs Hj Hp.
}
rewrite H in HnA; clear H.
unfold nA at 1 in HnA.
rewrite summation_shift in HnA; [ | flia Hj ].
replace (i + j + 2 - 1 - (i + 1)) with j in HnA by flia Hj.
rewrite summation_eq_compat with (h := λ k, u (i + 1 + k) * rad ^ (j - k))
  in HnA.
-rewrite power_summation_sub_1 in HnA; [ | easy ].
 rewrite summation_mul_distr_l in HnA.
 remember (S j) as sj; simpl in HnA; subst sj.
 remember (Σ (i = 0, j), (rad - 1) * rad ^ i) as x.
 rewrite summation_rtl in Heqx.
 rewrite Nat.add_0_r in Heqx; subst x.
 clear s Hs Hsz Hj.
 set (rg := nat_ord_ring).
 assert
   (H :
    Σ (k = 0, j), u (i + 1 + k) * rad ^ (j - k) =
    Σ (k = 0, j), (rad - 1) * rad ^ (j - k)). {
   apply Nat.le_antisymm; [ | easy ].
   apply (@summation_le_compat nat_ord_ring_def); simpl; unfold Nat.le.
   intros p Hp.
   apply Nat.mul_le_mono_r.
   rewrite Nat.add_1_r.
   specialize (Hu p); flia Hu.
 }
 clear HnA; rename H into HnA.
 setoid_rewrite summation_rtl in HnA.
 rewrite summation_eq_compat with (h := λ k, u (i + j + 1 - k) * rad ^ k)
   in HnA.
 +symmetry in HnA.
  rewrite summation_eq_compat with (h := λ k, (rad - 1) * rad ^ k) in HnA.
  *clear n.
   revert i Hu HnA k Hk.
   induction j; intros.
  --do 2 rewrite summation_only_one in HnA.
    rewrite Nat.sub_0_r, Nat.add_0_r, Nat.pow_0_r in HnA.
    do 2 rewrite Nat.mul_1_r in HnA.
    now replace (i + 1) with k in HnA by flia Hk.
  --setoid_rewrite summation_split_last in HnA; [ | flia | flia ].
    remember (S j) as sj; simpl in HnA; subst sj.
    replace (i + S j + 1 - S j) with (S i) in HnA by flia.
    destruct (eq_nat_dec (u (S i)) (rad - 1)) as [H1| H1].
   ++rewrite H1 in HnA.
     apply Nat.add_cancel_r in HnA.
     destruct (eq_nat_dec k (S i)) as [H2| H2]; [ now subst k | ].
     apply IHj with (i := S i); [ | | flia Hk H2 ].
    **intros l; rewrite Nat.add_succ_l, <- Nat.add_succ_r; apply Hu.
    **rewrite HnA.
      apply summation_eq_compat.
      intros p Hp; f_equal; f_equal; flia.
   ++assert
       (H2 : Σ (i = 0, j), (rad - 1) * rad ^ i <
             Σ (i0 = 0, j), u (i + S j + 1 - i0) * rad ^ i0). {
       specialize (Hu (S i)) as Hui.
       assert (Hus : u (S i) < rad - 1). {
         specialize (Hu 0); rewrite Nat.add_0_r in Hu.
         flia Hu H1.
       }
       apply Nat.mul_lt_mono_pos_r with (p := rad ^ S j) in Hus.
       -flia HnA Hus.
       -now apply Nat_pow_ge_1.
     }
     apply Nat.nle_gt in H2.
     exfalso; apply H2.
     apply (@summation_le_compat nat_ord_ring_def); simpl; unfold Nat.le.
     intros p Hp.
     apply Nat.mul_le_mono_r.
     specialize (Hu (j + 1 - p)).
     replace (S i + (j + 1 - p)) with (i + S j + 1 - p) in Hu by flia Hp.
     flia Hu.
  *intros p Hp; f_equal; f_equal; flia Hp.
 +intros p Hp.
  replace (j - (j + 0 - p)) with p by flia Hp; f_equal.
  f_equal; flia Hp.
-intros p Hp.
 f_equal; f_equal; flia.
Qed.

Require Import Setoid.

Theorem freal_eq_refl {r : radix} : reflexive _ freal_eq.
Proof.
intros x.
unfold freal_eq, freal_norm_eq.
remember (freal_normalize x) as y eqn:Hy.
destruct (LPO_fst (has_same_digits y y)) as [Hs| Hs]; [ easy | exfalso ].
destruct Hs as (i & Hji & Hyy).
now apply has_same_digits_false_iff in Hyy.
Qed.

Theorem freal_eq_sym {r : radix} : symmetric _ freal_eq.
Proof.
intros x y Hxy.
unfold freal_eq, freal_norm_eq in Hxy |-*.
remember (freal_normalize x) as nx eqn:Hnx.
remember (freal_normalize y) as ny eqn:Hny.
intros i; symmetry; apply Hxy.
Qed.

Theorem freal_eq_trans {r : radix} : transitive _ freal_eq.
Proof.
intros x y z Hxy Hyz.
unfold freal_eq, freal_norm_eq in Hxy, Hyz |-*.
remember (freal_normalize x) as nx eqn:Hnx.
remember (freal_normalize y) as ny eqn:Hny.
remember (freal_normalize z) as nz eqn:Hnz.
intros i.
now rewrite Hxy, Hyz.
Qed.

Add Parametric Relation {r : radix} : (FracReal) freal_eq
 reflexivity proved by freal_eq_refl
 symmetry proved by freal_eq_sym
 transitivity proved by freal_eq_trans
 as freal_eq_rel.

Theorem all_eq_seq_all_eq {r : radix} : ∀ x y,
  (∀ k, has_same_digits x y k = true) → (∀ k, freal x k = freal y k).
Proof.
intros * Hk *.
specialize (Hk k).
apply has_same_digits_true_iff in Hk.
now apply digit_eq_eq.
Qed.

Theorem nA_eq_compat {r : radix} : ∀ i n u v,
  (∀ j, i < j < n → u j = v j)
  → nA i n u = nA i n v.
Proof.
intros * Hfg *.
unfold nA.
apply summation_eq_compat.
intros j Hj; f_equal.
apply Hfg; flia Hj.
Qed.

Theorem A_ge_1_eq_compat {r : radix} : ∀ i f g,
  (∀ i, f i = g i) → ∀ k, A_ge_1 f i k = A_ge_1 g i k.
Proof.
intros * Hfg *.
unfold A_ge_1.
now erewrite nA_eq_compat.
Qed.

Theorem prop_carr_eq_compat {r : radix} : ∀ f g,
  (∀ i, f i = g i) → ∀ i,
  prop_carr f i = prop_carr g i.
Proof.
intros * Hfg *.
unfold prop_carr.
apply digit_eq_eq; simpl.
unfold nat_prop_carr.
rewrite Hfg.
destruct (LPO_fst (A_ge_1 f i)) as [Hf| Hf].
-destruct (LPO_fst (A_ge_1 g i)) as [Hg| Hg].
 +rewrite (nA_eq_compat _ _ _ g); [ easy | intros; apply Hfg ].
 +exfalso.
  destruct Hg as (k & Hjk & H).
  specialize (Hf k).
  erewrite A_ge_1_eq_compat in Hf; [ | easy ].
  now rewrite H in Hf.
-destruct (LPO_fst (A_ge_1 g i)) as [Hg| Hg].
 +exfalso.
  destruct Hf as (k & Hjk & H).
  specialize (Hg k).
  erewrite A_ge_1_eq_compat in H; [ | easy ].
  now rewrite H in Hg.
 +destruct Hf as (k & Hjk & Hk).
  destruct Hg as (l & Hjl & Hl).
  destruct (lt_eq_lt_dec k l) as [[Hkl| Hkl]| Hkl].
  *specialize (Hjl _ Hkl).
   erewrite A_ge_1_eq_compat in Hk; [ | easy ].
   now rewrite Hjl in Hk.
  *subst l.
   f_equal; f_equal; f_equal.
   now apply nA_eq_compat.
  *specialize (Hjk _ Hkl).
   erewrite A_ge_1_eq_compat in Hjk; [ | easy ].
   now rewrite Hl in Hjk.
Qed.

Theorem freal_add_series_le_twice_pred {r : radix} : ∀ x y i,
  (x ⊕ y) i ≤ 2 * (rad - 1).
Proof.
intros *.
unfold "⊕".
replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
apply Nat.add_le_mono.
apply digit_le_pred_radix.
apply digit_le_pred_radix.
Qed.

Theorem nA_upper_bound_for_add {r : radix} (rg := nat_ord_ring) : ∀ u i n,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → nA i n u ≤ 2 * (rad ^ (n - i - 1) - 1).
Proof.
intros * Hur.
destruct (lt_dec (n - 1) (i + 1)) as [Hin| Hin].
-unfold nA.
 rewrite summation_empty; [ simpl; flia | easy ].
-remember (rad ^ (n - i - 1)) as s eqn:Hs.
 rewrite Hs.
 remember (n - i - 1) as m eqn:Hm.
 symmetry in Hm.
 destruct m; [ flia Hin Hm | ].
 rewrite power_summation_sub_1; [ | easy ].
 rewrite Nat.mul_assoc.
 rewrite summation_mul_distr_l.
 unfold nA.
 remember 2 as two; simpl; subst two.
 rewrite summation_rtl.
 rewrite summation_shift; [ | flia Hin ].
 replace (n - 1 - (i + 1)) with m by flia Hm.
 apply (@summation_le_compat nat_ord_ring_def).
 intros j Hj.
 remember 2 as two; simpl; subst two; unfold Nat.le.
 replace (n - 1 + (i + 1) - (i + 1 + j)) with (n - j - 1) by flia.
 replace (n - 1 - (n - j - 1)) with j by flia Hm Hj.
 apply Nat.mul_le_mono_r.
 specialize (Hur (n - j - i - 2)).
 replace (i + (n - j - i - 2) + 1) with (n - j - 1) in Hur by flia Hm Hj.
 easy.
Qed.

Theorem nA_upper_bound_for_add_3 {r : radix} : ∀ u i n,
  (∀ k, u (i + k + 2) ≤ 2 * (rad - 1))
  → u (i + 1) < rad - 2
  → i + 2 ≤ n - 1
  → nA i n u < (rad - 1) * rad ^ (n - i - 2).
Proof.
intros * Hur H1 His.
rewrite nA_split_first; [ | flia His ].
remember (n - i - 2) as s eqn:Hs.
apply le_lt_trans with (m := (rad - 3) * rad ^ s + 2 * (rad ^ s - 1)).
-apply Nat.add_le_mono.
 +apply Nat.mul_le_mono_pos_r; [ | flia H1 ].
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +destruct s; [ flia Hs His | ].
  rewrite power_summation_sub_1; [ | easy ].
  rewrite Nat.mul_assoc, summation_mul_distr_l.
  remember 2 as x; simpl; subst x.
  unfold nA.
  rewrite summation_rtl.
  rewrite summation_shift; [ | flia His ].
  replace (n - 1 - (S i + 1)) with s by flia Hs.
  apply (@summation_le_compat nat_ord_ring_def).
  intros j Hj.
  remember 2 as x; simpl; subst x; unfold Nat.le.
  replace (n - 1 + S (i + 1) - S (i + 1 + j)) with (n - j - 1) by flia.
  replace (n - 1 - (n - j - 1)) with j by flia Hs Hj.
  apply Nat.mul_le_mono_pos_r.
  *now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *specialize (Hur (n - j - 3 - i)).
   replace (i + (n - j - 3 - i) + 2) with (n - j - 1) in Hur by flia Hs Hj.
   easy.
-replace (rad - 3) with (rad - 1 - 2) by flia.
 rewrite Nat.mul_sub_distr_r.
 rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
 remember (2 * rad ^ s) as x eqn:Hx.
 rewrite Nat.add_sub_assoc.
 +rewrite Nat.sub_add.
  *apply Nat.sub_lt; [ | flia ].
   destruct s; [ flia Hs His | ].
   replace 2 with (1 * 2) by flia.
   apply Nat.mul_le_mono; [ flia H1 | ].
   replace 2 with (2 ^ 1) by apply Nat.pow_1_r.
   apply Nat.pow_le_mono; [ easy | apply radix_ge_2 | flia ].
  *subst x.
   destruct rad as [| rr]; [ easy | ].
   destruct rr; [ easy | ].
   destruct rr; [ easy | simpl; flia ].
 +replace 2 with (2 * 1) by flia.
  rewrite Hx.
  apply Nat.mul_le_mono_l.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

Theorem nA_upper_bound_for_add_4 {r : radix} : ∀ u i j n,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → u (i + 1) = rad - 1
  → (∀ k : nat, k < j → u (i + k + 1) = rad - 1)
  → u (i + j + 1) < rad - 2
  → i + j + 2 ≤ n - 1
  → nA i n u < (rad ^ (j + 2) - 1) * rad ^ (n - i - 1 - (j + 2)).
Proof.
intros * Hur H1 H2 H3 Hin.
rewrite nA_split with (e := i + j + 2); [ | flia Hin ].
replace (n - i - 1 - (j + 2)) with (n - (i + j + 2) - 1) by flia.
remember (i + j + 2) as k eqn:Hk.
move k before j.
(*
           k-1
 i+1      i+j+1
  9 9 9 9 9≤7 0 0 0 0 0            j+2      n-k-1
  <---------> <------->        <-----------> <----->
      j+1        n-k       <?  9 9 9 9 9 9 9 0 0 0 0

+            1818181818

                               9 9 9 9 9 7 0 0 0 0 0
                             +           2 9 0 0 0 0
*)
replace ((rad ^ (j + 2) - 1) * rad ^ (n - k - 1)) with
  ((rad ^ (j + 1) - 3) * rad ^ (n - k) + (3 * rad - 1) * rad ^ (n - k - 1)).
-apply Nat.add_le_lt_mono.
 +apply Nat.mul_le_mono_r.
  rewrite nA_split_last; [ | flia Hk Hin ].
  replace (k - 1) with (i + j + 1) by flia Hk.
  rewrite Nat.pow_add_r, Nat.pow_1_r.
  replace (rad ^ j) with (rad ^ j - 1 + 1).
  *rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
   rewrite <- Nat.add_sub_assoc; [ | flia H3 ].
   apply Nat.add_le_mono; [ | flia H3 ].
   rewrite Nat.mul_comm.
   apply Nat.mul_le_mono_r.
   replace j with (i + j + 1 - i - 1) at 2 by flia.
   specialize (nA_dig_seq_ub u (i + j + 1) i) as H4.
   assert (H5 : ∀ p, i < p < i + j + 1 → u p < rad). {
     intros p Hp.
     specialize (H2 (p - i - 1)).
     assert (H5 : p - i - 1 < j) by flia Hp.
     specialize (H2 H5).
     replace (i + (p - i - 1) + 1) with p in H2 by flia Hp.
     specialize radix_ge_2 as Hr.
     flia Hr H2.
   }
   specialize (H4 H5); clear H5.
   destruct j.
  --rewrite Nat.add_0_r in H3; flia H1 H3.
  --assert (H5 : i + 1 ≤ i + S j + 1 - 1) by lia.
    specialize (H4 H5).
    apply Nat.le_add_le_sub_r.
    now rewrite Nat.add_1_r.
  *rewrite Nat.sub_add; [ easy | ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +eapply Nat.le_lt_trans.
  *apply nA_upper_bound_for_add.
   intros l.
   replace (k - 1 + l + 1) with (i + (j + 1 + l) + 1) by flia Hk.
   apply Hur.
  *replace (n - (k - 1) - 1) with (n - k) by flia Hk Hin.
   rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
   replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
   rewrite <- Nat.mul_assoc.
   rewrite <- Nat.pow_add_r.
   replace (1 + (n - k - 1)) with (n - k) by flia Hk Hin.
   (* 2*999 < 3*1000-100 : 1998 < 2900 *)
   replace (n - k) with (n - k - 1 + 1) at 1 2 by flia Hk Hin.
   rewrite Nat.pow_add_r, Nat.pow_1_r.
   remember (rad ^ (n - k - 1)) as x eqn:Hx.
   rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   replace 3 with (2 + 1) by easy.
   rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
   specialize radix_ge_2 as Hr.
   rewrite <- Nat.add_sub_assoc.
  --apply Nat.lt_sub_lt_add_l.
    rewrite Nat_sub_sub_swap.
    rewrite Nat.sub_diag; simpl.
    replace x with (x * 1) at 2 by apply Nat.pow_1_r.
    rewrite <- Nat.mul_sub_distr_l.
    apply Nat.neq_0_lt_0.
    intros H.
    apply Nat.eq_mul_0 in H.
    destruct H as [H| H]; [ | flia H Hr ].
    revert H; subst x.
    now apply Nat.pow_nonzero.
  --destruct rad; [ easy | ].
    rewrite Nat.mul_comm; simpl; flia.
-replace (j + 2) with (j + 1 + 1) by flia.
 remember (j + 1) as jj; rewrite Nat.pow_add_r; subst jj.
 rewrite Nat.pow_1_r.
 remember (rad ^ (j + 1)) as x eqn:Hx.
 do 2 rewrite Nat.mul_sub_distr_r.
 rewrite Nat.mul_1_l.
 rewrite Nat.add_sub_assoc.
 +replace (3 * rad) with (3 * rad ^ 1) by now rewrite Nat.pow_1_r.
  rewrite <- Nat.mul_assoc, <- Nat.pow_add_r.
  assert (H4 : 1 + (n - k - 1) = n - k) by flia Hk Hin.
  rewrite H4, Nat.sub_add.
  *rewrite Nat.mul_sub_distr_r, Nat.mul_1_l; f_equal.
   replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
   now rewrite <- Nat.mul_assoc, <- Nat.pow_add_r, H4.
  *apply Nat.mul_le_mono_r.
   destruct j.
  --rewrite Nat.add_0_r in H3; flia H1 H3.
  --subst x.
    replace (S j + 1) with (S (S j)) by flia.
    assert (H5 : rad ^ j ≠ 0) by now apply Nat.pow_nonzero.
    destruct rad as [| rr]; [ easy | ].
    destruct rr; [ easy | simpl; flia H5 ].
 +remember (rad ^ (n - k - 1)) as y eqn:Hy.
  replace y with (1 * y) by flia.
  apply Nat.mul_le_mono; [ | flia ].
  flia H3.
Qed.

Theorem nA_upper_bound_for_add_5 {r : radix} : ∀ u i k n,
  (∀ k, u (i + k + 2) ≤ 2 * (rad - 1))
  → u (i + 1) = rad - 2
  → u (i + k + 2) < 2 * (rad - 1)
  → i + k + 3 ≤ n - 1
  → nA i n u < (rad ^ (k + 2) - 1) * rad ^ (n - i - 1 - (k + 2)).
Proof.
intros * Hur Hui H2 Hin.
remember (n - i - 1) as s eqn:Hs.
specialize radix_ge_2 as Hr.
rewrite nA_split with (e := i + k + 2); [ | flia Hin ].
remember (i + k + 2) as j eqn:Hj.
move j before i.
replace ((rad ^ (k + 2) - 1) * rad ^ (s - (k + 2))) with
   ((rad ^ (k + 1) - 2) * rad ^ (s - (k + 1)) +
    (2 * rad - 1) * rad ^ (s - (k + 2))).
-apply Nat.add_le_lt_mono.
 +replace (n - j) with (s - (k + 1)) by flia Hs Hj.
  apply Nat.mul_le_mono_r.
  rewrite nA_split_first; [ | flia Hj Hin ].
  replace (rad ^ (k + 1) - 2) with
    ((rad - 2) * rad ^ k + 2 * (rad ^ k - 1)).
  *replace (j - i - 2) with k by flia Hj.
   apply Nat.add_le_mono.
  --now apply Nat.mul_le_mono_r; rewrite Hui.
  --destruct k.
   ++unfold nA; rewrite summation_empty; [ easy | flia Hj ].
   ++replace (S k) with (j - S i - 1) by flia Hj.
     apply nA_upper_bound_for_add.
     intros l.
     replace (S i + l + 1) with (i + l + 2) by flia.
     apply Hur.
  *rewrite Nat.mul_sub_distr_r.
   replace rad with (rad ^ 1) at 1 by apply Nat.pow_1_r.
   rewrite <- Nat.pow_add_r.
   replace (1 + k) with (k + 1) by flia.
   rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   rewrite Nat.add_sub_assoc.
  --f_equal.
    rewrite Nat.sub_add; [ easy | ].
    replace (k + 1) with (1 + k) by flia.
    remember 2 as x; simpl; subst x.
    now apply Nat.mul_le_mono_r.
  --replace 2 with (2 * 1) at 1 by flia.
    apply Nat.mul_le_mono_l.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +replace (s - (k + 2)) with (n - j - 1) by flia Hs Hj.
  rewrite nA_split_first; [ | flia Hj Hin ].
  replace (j - 1 + 1) with j by flia Hj.
  replace (n - (j - 1) - 2) with (n - j - 1) by flia Hj.
  replace (S (j - 1)) with j by flia Hj.
  replace (2 * rad - 1) with (2 * rad - 3 + 2) by flia Hr.
  rewrite Nat.mul_add_distr_r.
  apply Nat.add_le_lt_mono.
  *apply Nat.mul_le_mono_r; flia H2.
  *eapply Nat.le_lt_trans.
  --apply nA_upper_bound_for_add.
    intros l.
    replace (j + l + 1) with (i + (k + l + 1) + 2) by flia Hj.
    apply Hur.
  --rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
    apply Nat.sub_lt; [ | flia ].
    replace 2 with (2 * 1) at 1 by flia.
    apply Nat.mul_le_mono_l.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
-replace (s - (k + 1)) with (s - (k + 2) + 1) by flia Hs Hj Hin.
 remember (s - (k + 2)) as t eqn:Ht.
 replace (k + 2) with (k + 1 + 1) by flia.
 remember (k + 1) as m eqn:Hm.
 do 2 rewrite Nat.pow_add_r.
 rewrite Nat.pow_1_r.
 rewrite Nat.mul_assoc, Nat.mul_shuffle0.
 rewrite <- Nat.mul_add_distr_r; f_equal.
 rewrite Nat.mul_sub_distr_r.
 rewrite Nat.add_sub_assoc; [ f_equal | flia Hr ].
 rewrite Nat.sub_add; [ easy | ].
 apply Nat.mul_le_mono_r.
 subst m.
 rewrite Nat.add_comm; simpl.
 replace 2 with (2 * 1) by flia.
 apply Nat.mul_le_mono; [ easy | ].
 now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

Theorem A_ge_1_add_first_ge {r : radix} : ∀ u i,
  (∀ k, u (i + k + 2) ≤ 2 * (rad - 1))
  → A_ge_1 u i 0 = true
  → u (i + 1) ≥ rad - 2.
Proof.
intros * Hur Hu.
revert Hu.
apply Decidable.contrapositive; [ apply Nat.le_decidable | ].
intros H1; apply Nat.nle_gt in H1.
apply Bool.not_true_iff_false.
apply A_ge_1_false_iff.
unfold min_n.
rewrite Nat.add_0_r, Nat.pow_1_r.
remember (rad * (i + 3)) as n eqn:Hn.
remember (n - i - 1) as s eqn:Hs.
move s before n.
assert (Hin : i + 2 ≤ n - 1). {
  rewrite Hn.
  specialize radix_ne_0 as H.
  destruct rad; [ easy | simpl; flia ].
}
specialize (nA_upper_bound_for_add_3 u i n Hur H1 Hin) as H2.
replace (n - i - 2) with (s - 1) in H2 by flia Hs.
rewrite Nat.mod_small; [ easy | ].
eapply lt_le_trans; [ apply H2 | ].
rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
replace rad with (rad ^ 1) at 1 by apply Nat.pow_1_r.
rewrite <- Nat.pow_add_r.
replace (1 + (s - 1)) with s by flia Hs Hin.
flia.
Qed.

Theorem A_ge_1_add_ge {r : radix} : ∀ u i j,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → (∀ k : nat, A_ge_1 u i k = true)
  → u (i + 1) = rad - 1
  → u (i + j + 1) ≠ rad - 1
  → (∀ k : nat, k < j → u (i + k + 1) = rad - 1)
  → u (i + j + 1) ≥ rad - 2.
Proof.
intros * Hur Hu H1 H2 H3.
specialize (Hu (j + 1)) as H4.
revert H4.
apply Decidable.contrapositive; [ apply Nat.le_decidable | ].
intros H4; apply Nat.nle_gt in H4.
apply Bool.not_true_iff_false.
apply A_ge_1_false_iff.
unfold min_n.
replace (i + (j + 1) + 3) with (i + j + 4) by flia.
replace (S (j + 1)) with (j + 2) by flia.
remember (rad * (i + j + 4)) as n eqn:Hn.
assert (Hin : i + j + 2 ≤ n - 1). {
  rewrite Hn.
  specialize radix_ne_0 as H.
  destruct rad; [ easy | simpl; flia ].
}
replace (n - i - (j + 1) - 2) with (n - i - 1 - (j + 2)) by flia.
remember (n - i - 1) as s eqn:Hs.
move s before n.
specialize (nA_upper_bound_for_add_4 u i j n Hur H1 H3 H4 Hin) as H5.
rewrite <- Hs in H5.
rewrite Nat.mod_small; [ easy | ].
eapply Nat.lt_le_trans; [ apply H5 | ].
rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
rewrite <- Nat.pow_add_r.
rewrite Nat.add_sub_assoc.
-rewrite Nat.add_comm, Nat.add_sub; flia.
-flia Hin Hs.
Qed.

Theorem A_ge_1_add_first_ge_rad {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → A_ge_1 u i 0 = true
  → u (i + 1) ≥ rad
  → u (i + 1) = 2 * (rad - 1).
Proof.
intros * Hur Hu Hui.
apply A_ge_1_true_iff in Hu.
unfold min_n in Hu.
rewrite Nat.add_0_r, Nat.pow_1_r in Hu.
remember (rad * (i + 3)) as n eqn:Hn.
remember (n - i - 1) as s eqn:Hs.
move s before n.
assert (Hin : i + 2 ≤ n - 1). {
  rewrite Hn.
  specialize radix_ne_0 as H.
  destruct rad; [ easy | simpl; flia ].
}
set (v j := if eq_nat_dec j (i + 1) then u j - rad else u j).
assert (H2 : nA i n u mod rad ^ s = nA i n v mod rad ^ s). {
  rewrite nA_split_first; [ symmetry | flia Hin ].
  rewrite nA_split_first; [ symmetry | flia Hin ].
  rewrite Nat.add_mod; [ symmetry | now apply Nat.pow_nonzero ].
  rewrite Nat.add_mod; [ symmetry | now apply Nat.pow_nonzero ].
  f_equal; f_equal.
  -replace (n - i - 2) with (s - 1) by flia Hs.
   replace (rad ^ s) with (rad ^ ((s - 1) + 1)).
   +rewrite Nat.pow_add_r, Nat.pow_1_r.
   rewrite Nat.mod_mul_r; [ symmetry | now apply Nat.pow_nonzero | easy ].
    rewrite Nat.mod_mul_r; [ symmetry | now apply Nat.pow_nonzero | easy ].
    rewrite Nat.mod_mul; [ | now apply Nat.pow_nonzero ].
    rewrite Nat.mod_mul; [ | now apply Nat.pow_nonzero ].
    rewrite Nat.div_mul; [ | now apply Nat.pow_nonzero ].
    rewrite Nat.div_mul; [ | now apply Nat.pow_nonzero ].
    do 2 rewrite Nat.add_0_l.
    f_equal; unfold v.
    destruct (Nat.eq_dec (i + 1) (i + 1)) as [H2| ]; [ | easy ].
    replace (u (i + 1)) with ((u (i + 1) - rad) + 1 * rad) at 1 by flia Hui.
    now apply Nat.mod_add.
   +f_equal; flia Hs Hin.
  -f_equal.
   apply nA_eq_compat.
   intros j Hj.
   unfold v.
   destruct (Nat.eq_dec j (i + 1)) as [H2| ]; [ | easy ].
   flia Hj H2.
}
rewrite H2 in Hu.
assert (H3 : ∀ k, v (i + k + 2) ≤ 2 * (rad - 1)). {
  intros k; unfold v.
  destruct (Nat.eq_dec (i + k + 2) (i + 1)) as [H4| H4].
  -eapply Nat.le_trans; [ apply Nat.le_sub_l | ].
   specialize (Hur (k + 1)).
   replace (i + (k + 1) + 1) with (i + k + 2) in Hur by flia.
   apply Hur.
  -specialize (Hur (k + 1)).
   replace (i + (k + 1) + 1) with (i + k + 2) in Hur by flia.
   apply Hur.
}
assert (H4 : A_ge_1 v i 0 = true). {
  apply A_ge_1_true_iff.
  unfold min_n.
  rewrite Nat.add_0_r, Nat.pow_1_r.
  now rewrite <- Hn, <- Hs.
}
specialize (A_ge_1_add_first_ge v i H3 H4) as H5.
unfold v in H5.
destruct (Nat.eq_dec (i + 1) (i + 1)) as [H6| ]; [ | easy ].
apply Nat.le_antisymm; [ | flia Hui H5 ].
now specialize (Hur 0); rewrite Nat.add_0_r in Hur.
Qed.

Theorem A_ge_1_add_first {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → A_ge_1 u i 0 = true
  → { u (i + 1) = rad - 2 } +
     { u (i + 1) = rad - 1 } +
     { u (i + 1) = 2 * (rad - 1) }.
Proof.
intros * Hur Hu.
assert (Hur2 : ∀ k, u (i + k + 2) ≤ 2 * (rad - 1)). {
  intros.
  specialize (Hur (k + 1)).
  now replace (i + (k + 1) + 1) with (i + k + 2) in Hur by flia.
}
specialize (A_ge_1_add_first_ge u i Hur2 Hu) as H1.
destruct (lt_dec (u (i + 1)) rad) as [H2| H2].
-left.
 destruct (lt_dec (u (i + 1)) (rad - 1)) as [H3| H3].
 +left; flia H1 H3.
 +right; flia H2 H3.
-right.
 apply Nat.nlt_ge in H2.
 now specialize (A_ge_1_add_first_ge_rad u i Hur Hu H2) as H3.
Qed.

Theorem A_ge_1_add_8_eq {r : radix} : ∀ u i,
  (∀ k, u (i + k + 2) ≤ 2 * (rad - 1))
  → u (i + 1) = rad - 2
  → ∀ k, A_ge_1 u i (k + 1) = true
  → u (i + k + 2) = 2 * (rad - 1).
Proof.
intros * Hur Hui * H2.
specialize radix_ge_2 as Hr; move Hr before i.
revert H2.
apply Decidable.contrapositive; [ apply Nat.eq_decidable | ].
intros H.
assert (H2 : u (i + k + 2) < 2 * (rad - 1)). {
  specialize (Hur k).
  flia Hur H.
}
clear H.
apply Bool.not_true_iff_false.
apply A_ge_1_false_iff.
unfold min_n.
remember (rad * (i + (k + 1) + 3)) as n eqn:Hn.
replace (n - i - (k + 1) - 2) with (n - i - 1 - (k + 2)) by flia.
remember (n - i - 1) as s eqn:Hs.
move s before n.
assert (Hin : i + k + 3 ≤ n - 1). {
  rewrite Hn.
  destruct rad; [ easy | simpl; flia ].
}
replace (S (k + 1)) with (k + 2) by flia.
specialize (nA_upper_bound_for_add_5 u i k n Hur Hui H2 Hin) as H3.
rewrite <- Hs in H3.
rewrite Nat.mod_small; [ easy | ].
eapply Nat.lt_le_trans; [ apply H3 | ].
rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
rewrite <- Nat.pow_add_r.
rewrite Nat.add_sub_assoc; [ | flia Hs Hin ].
rewrite Nat.add_comm, Nat.add_sub.
apply Nat.le_sub_l.
Qed.

Theorem nA_lower_bound_when_999_gt_9 {r : radix} : ∀ u i k n,
  i + k + 3 ≤ n - 1
  → (∀ j, j < k → u (i + j + 1) = rad - 1)
  → rad ≤ u (i + k + 1)
  → rad ^ (n - i - 1) ≤ nA i n u.
Proof.
intros * H6 H3 H5.
remember (n - i - 1) as s eqn:Hs.
enough (H : rad ^ s ≤ nA i (i + k + 2) u * rad ^ (n - (i + k + 2))). {
  rewrite nA_split with (e := i + k + 2); [ | flia H6 ].
  now apply le_plus_trans.
}
rewrite nA_split_last; [ | flia Hs ].
replace (i + k + 2 - 1) with (i + k + 1) by flia.
assert (HnA : nA i (i + k + 1) u ≥ rad ^ k - 1). {
  destruct k; [ apply Nat.le_0_l | ].
 unfold nA.
 rewrite summation_rtl.
 rewrite summation_shift; [ | flia H6 ].
 rewrite Nat.add_sub.
 replace (i + S k - (i + 1)) with k by flia.
 rewrite power_summation_sub_1; [ | easy ].
 rewrite summation_mul_distr_l.
 apply (@summation_le_compat nat_ord_ring_def).
 intros j Hj; simpl; unfold Nat.le.
 replace (i + S k + (i + 1) - (i + 1 + j)) with (i + (k - j) + 1) by flia Hj.
 replace (i + S k - (i + (k - j) + 1)) with j by flia Hj.
 apply Nat.mul_le_mono_r.
 rewrite H3; [ easy | flia ].
}
apply Nat.le_trans with
    (m := (rad * (rad ^ k - 1) + rad) * rad ^ (n - (i + k + 2))); cycle 1. {
  apply Nat.mul_le_mono_r.
  apply Nat.add_le_mono; [ | easy ].
  now apply Nat.mul_le_mono_l.
}
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
rewrite Nat.mul_sub_distr_r.
replace rad with (rad ^ 1) at 2 5 7 by apply Nat.pow_1_r.
do 3 rewrite <- Nat.pow_add_r.
replace (n - (i + k + 2)) with (s - (k + 1)) by flia Hs.
replace (1 + (s - (k + 1))) with (s - k) by flia H6 Hs.
replace (1 + k + (s - (k + 1))) with s by flia H6 Hs.
rewrite Nat.sub_add; [ easy | ].
apply Nat.pow_le_mono; [ easy | easy | ].
apply Nat.le_sub_l.
Qed.

Theorem nA_le_aft_999 {r : radix} : ∀ u i k,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → (∀ j, j < k → u (i + j + 1) = rad - 1)
  → nA i (i + k + 2) u ≤ rad ^ S k + (rad - 2).
Proof.
intros * Hur H3.
specialize radix_ge_2 as Hr.
rewrite nA_split_last; [ | flia ].
rewrite nA_all_9; [ | intros l Hl; apply H3; flia Hl ].
replace (i + k + 2 - 1) with (i + k + 1) by flia.
replace (i + k + 1 - i - 1) with k by flia.
rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
destruct (le_dec rad (u (i + k + 1))) as [H1| H1].
-rewrite <- Nat.add_sub_swap; cycle 1. {
   replace rad with (rad * 1) at 1 by flia.
   apply Nat.mul_le_mono_l.
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 }
 rewrite <- Nat.add_sub_assoc; [ | easy ].
 apply Nat.add_le_mono_l.
 specialize (Hur k); flia Hur.
-apply Nat.nle_gt in H1.
 apply Nat.le_trans with (m := rad ^ S k - rad + rad).
 +apply Nat.add_le_mono; [ easy | flia H1 ].
 +rewrite Nat.sub_add; [ flia | ].
  simpl; replace rad with (rad * 1) at 1 by flia.
  apply Nat.mul_le_mono_l.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

Theorem A_ge_1_add_9_eq {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → ∀ k, k ≠ 0
  → A_ge_1 u i k = true
  → (∀ j, j < k → u (i + j + 1) = rad - 1)
  → u (i + k + 1) < rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur * Hk H5 H3.
revert H5.
apply Decidable.contrapositive; [ apply Nat.le_decidable | ].
intros H5; apply Nat.nlt_ge in H5.
apply Bool.not_true_iff_false.
apply A_ge_1_false_iff.
remember (min_n i k) as n eqn:Hn.
remember (n - i - 1) as s eqn:Hs.
move n before k; move s before n.
assert (H6 : i + k + 3 ≤ n - 1). {
  rewrite Hn.
  unfold min_n.
  destruct rad as [| rr]; [ easy | ].
  destruct rr; [ flia Hr | simpl; flia ].
}
specialize (nA_lower_bound_when_999_gt_9 u i k n H6 H3 H5) as H7.
specialize (nA_upper_bound_for_add u i n Hur) as H8.
rewrite <- Hs in H7, H8.
rewrite Nat_mod_less_small; cycle 1. {
  split; [ easy | ].
  eapply Nat.le_lt_trans; [ apply H8 | ].
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
  apply Nat.sub_lt; [ | apply Nat.lt_0_2 ].
  replace 2 with (2 * 1) at 1 by flia.
  apply Nat.mul_le_mono_l.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
apply Nat.add_lt_mono_r with (p := rad ^ s).
rewrite Nat.sub_add; [ | easy ].
rewrite nA_split with (e := i + k + 2); [ | flia H6 ].
remember (i + k + 2) as t eqn:Ht.
move t before s.
unfold min_n in Hn.
replace (i + k + 3) with (i + k + 2 + 1) in Hn, H6 by flia.
rewrite <- Ht in Hn, H6.
replace (i + k + 1) with (t - 1) in H5 by flia Ht.
replace (s - S k) with (n - t) by flia Hs Ht.
apply Nat.le_lt_trans with
  (m := (rad ^ S k + (rad - 2)) * rad ^ (n - t) + nA (t - 1) n u).
-apply Nat.add_le_mono_r.
 apply Nat.mul_le_mono; [ | easy ].
 now subst; apply nA_le_aft_999.
-rewrite Nat.mul_sub_distr_r.
 rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
 rewrite <- Nat.add_sub_swap.
 +rewrite <- Nat.add_assoc.
  rewrite <- Nat.add_sub_assoc.
  *apply Nat.add_lt_mono_l.
   apply -> Nat.lt_add_lt_sub_l.
   rewrite Nat.add_assoc.
   replace (rad ^ (n - t)) with (1 * rad ^ (n - t)) at 1 by flia.
   rewrite <- Nat.mul_add_distr_r.
   replace (1 + (rad - 2)) with (rad - 1) by flia Hr.
   apply Nat.lt_add_lt_sub_l.
   eapply Nat.le_lt_trans.
  --apply nA_upper_bound_for_add.
    intros j.
    replace (t - 1 + j + 1) with (i + (k + j + 1) + 1) by flia Ht.
    apply Hur.
  --replace (n - (t - 1) - 1) with (n - t) by flia Ht.
    apply -> Nat.lt_add_lt_sub_l.
    rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
    rewrite Nat.add_sub_assoc.
   ++rewrite <- Nat.mul_add_distr_r.
     replace (rad - 1 + 2) with (rad + 1) by flia Hr.
     replace s with (k + 1 + (n - t)) by flia Hs H6 Ht.
     rewrite Nat.pow_add_r.
     apply Nat.lt_le_trans with (m := (rad + 1) * rad ^ (n - t)).
    **apply Nat.sub_lt; [ | flia ].
      specialize (Nat.pow_nonzero rad (n - t) radix_ne_0) as H10.
      destruct (rad ^ (n - t)); [ easy | ].
      destruct rad as [| rr]; [ easy | ].
      destruct rr; [ flia Hr | ].
      simpl; flia.
    **apply Nat.mul_le_mono_r.
      destruct k.
    ---rewrite Nat.add_0_r in Ht.
       rewrite Ht in H5.
       replace (i + 2 - 1) with (i + 1) in H5 by flia.
       flia Hr Hk H5.
    ---do 2 rewrite Nat.add_1_r; simpl.
       specialize (Nat.pow_nonzero rad k radix_ne_0) as H10.
       destruct (rad ^ k); [ easy | ].
       destruct rad as [| rr]; [ easy | ].
       rewrite Nat.mul_comm, <- Nat.mul_assoc.
       destruct rr; [ flia Hr | simpl; flia ].
   ++specialize (Nat.pow_nonzero rad (n - t) radix_ne_0) as H10.
     destruct (rad ^ (n - t)); [ easy | flia ].
  *apply Nat.pow_le_mono_r; [ easy | flia Hs Ht ].
 +replace (rad ^ (n - t)) with (1 * rad ^ (n - t)) at 1 by flia.
  apply Nat.mul_le_mono_r.
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

(* ... *)

Theorem add_pow_rad_mod : ∀ r a b c a₁ b₁,
  r ≠ 0
  → a < r ^ a₁
  → b < r ^ b₁
  → (a * r ^ b₁ + b) mod r ^ (a₁ + b₁) ≥ a * r ^ b₁ + c
  → b ≥ c.
Proof.
intros * Hr Ha Hb H1.
replace (a₁ + b₁) with (b₁ + a₁) in H1 by apply Nat.add_comm.
rewrite Nat.pow_add_r in H1.
rewrite Nat.mod_mul_r in H1; try now apply Nat.pow_nonzero.
replace (a * r ^ b₁ + b) with (b + a * r ^ b₁) in H1 by apply Nat.add_comm.
rewrite Nat.mod_add in H1; [ | now apply Nat.pow_nonzero ].
rewrite Nat.mod_small in H1; [ | easy ].
rewrite Nat.div_add in H1; [ | now apply Nat.pow_nonzero ].
rewrite Nat.div_small in H1; [ | easy ].
rewrite Nat.add_0_l in H1.
rewrite Nat.mod_small in H1; [ | easy ].
rewrite Nat.add_comm, Nat.mul_comm in H1.
now apply Nat.add_le_mono_l in H1.
Qed.

Theorem A_ge_1_add_all_true_if {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, A_ge_1 u i k = true)
  → (∀ k, u (i + k + 1) = rad - 1) ∨
     (∀ k, u (i + k + 1) = 2 * (rad - 1)) ∨
     (∃ j,
       (∀ k, k < j → u (i + k + 1) = rad - 1) ∧
       u (i + j + 1) = rad - 2 ∧
       (∀ k, u (i + j + k + 2) = 2 * (rad - 1))).
Proof.
intros * Hur.
intros Hu.
specialize radix_ge_2 as Hr; move Hr before i.
specialize (A_ge_1_add_first u i Hur (Hu 0)) as [[H1| H1]| H1].
-right; right.
 exists 0.
 rewrite Nat.add_0_r.
 split; [ easy | ].
 split; [ easy | ].
 intros j.
 assert (Hur2 : ∀ k, u (i + k + 2) ≤ 2 * (rad - 1)). {
   intros.
   replace (i + k + 2) with (i + (k + 1) + 1) by flia.
   apply Hur.
 }
 specialize (A_ge_1_add_8_eq u i Hur2 H1 j (Hu (j + 1))) as H2.
 easy.
-set (g j := if Nat.eq_dec (u (i + j + 1)) (rad - 1) then true else false).
 destruct (LPO_fst g) as [H2| H2]; subst g; simpl in H2.
 +left; intros k; specialize (H2 k).
  now destruct (Nat.eq_dec (u (i + k + 1)) (rad - 1)).
 +destruct H2 as (j & Hjj & H2).
  destruct (Nat.eq_dec (u (i + j + 1)) (rad - 1)) as [ | H]; [ easy | ].
  clear H2; rename H into H2.
  assert (H3 : ∀ k, k < j → u (i + k + 1) = rad - 1). {
    intros k Hk; specialize (Hjj k Hk).
    now destruct (Nat.eq_dec (u (i + k + 1)) (rad - 1)).
  }
  clear Hjj.
  right; right; exists j.
  split; [ easy | ].
  specialize (A_ge_1_add_ge u i j Hur Hu H1 H2 H3) as H4.
  assert (H5 : u (i + j + 1) < rad). {
    destruct j; [ rewrite Nat.add_0_r, H1; flia Hr | ].
    remember (S j) as k; assert (Hj : k ≠ 0) by flia Heqk.
    now apply A_ge_1_add_9_eq.
  }
  assert (H : u (i + j + 1) = rad - 2) by flia H2 H4 H5.
  clear H2 H4 H5; rename H into H4.
  move j before i.
  split; [ easy | ].
  intros k; move k before j.
  assert (Hur2 : ∀ k : nat, u (i + j + k + 2) ≤ 2 * (rad - 1)). {
    intros l.
    replace (i + j + l + 2) with (i + (j + l + 1) + 1) by flia.
    apply Hur.
  }
  specialize (A_ge_1_add_8_eq u (i + j) Hur2 H4 k) as H2.
  assert (H5 : A_ge_1 u (i + j) (k + 1) = true). {
    clear - Hr Hur Hu H1 H3 H4.
    specialize (Hu (j + k + 1)) as H5.
    apply A_ge_1_true_iff in H5.
    apply A_ge_1_true_iff.
    unfold min_n in H5 |-*.
    replace (i + (j + k + 1) + 3) with (i + j + k + 4) in H5 by flia.
    replace (i + j + (k + 1) + 3) with (i + j + k + 4) by flia.
    remember (rad * (i + j + k + 4)) as n eqn:Hn.
    assert (Hin : i + j + k + 2 ≤ n - 1). {
      rewrite Hn.
      destruct rad; [ easy | simpl; flia ].
    }
    replace (n - (i + j) - 1) with (n - i - 1 - j) by flia.
    replace (n - i - 1 - j - S (k + 1)) with (n - i - 1 - S (j + k + 1))
      by flia.
    remember (n - i - 1) as s eqn:Hs.
    remember (j + k + 1) as t eqn:Ht.
    move s before n; move t before s.
    specialize (add_pow_rad_mod rad (rad ^ j - 1) (nA (i + j) n u)) as H7.
    specialize (H7 ((rad ^ S (k + 1) - 1) * rad ^ (s - S t))).
    specialize (H7 j (s - j) radix_ne_0).
    assert (H : rad ^ j - 1 < rad ^ j). {
      apply Nat.sub_lt; [ | flia ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    specialize (H7 H); clear H.
    assert (H8 : nA (i + j) n u < rad ^ (s - j)). {
      rewrite Hs.
      replace (n - i - 1 - j) with (n - (i + j) - 1) by flia.
      (* 8/18/18/18 < 1/0/0/0/0 *)
      remember (n - (i + j) - 1) as p eqn:Hp.
      destruct p; [ flia Hin Hp | ].
      replace (rad ^ S p) with
        ((rad - 2) * rad ^ p + (rad ^ S p - (rad - 2) * rad ^ p)).
      -rewrite nA_split_first; [ | flia Hin ].
       apply Nat.add_le_lt_mono.
       +replace (n - (i + j) - 2) with p by flia Hp.
        apply Nat.mul_le_mono_r.
        now rewrite H4.
       +rewrite Nat.mul_sub_distr_r.
        replace (rad * rad ^ p) with (rad ^ S p) by easy.
        rewrite Nat_sub_sub_assoc.
        *remember (rad ^ S p + 2 * rad ^ p) as x eqn:Hx.
         rewrite Nat.add_comm in Hx; subst x.
         rewrite Nat.add_sub.
         assert (Hur2 : ∀ k, u (S (i + j) + k + 1) ≤ 2 * (rad - 1)). {
           intros l.
           replace (S (i + j) + l + 1) with (i + (S j + l) + 1) by flia.
           apply Hur.
         }
         specialize (nA_upper_bound_for_add u (S (i + j)) n Hur2) as H8.
         replace (n - S (i + j) - 1) with p in H8 by flia Hp.
         rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H8.
         eapply Nat.le_lt_trans; [ apply H8 | ].
         apply Nat.sub_lt; [ | flia ].
         replace 2 with (2 * 1) at 1 by flia.
         apply Nat.mul_le_mono_l.
         now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
        *split; [ | flia ].
         rewrite Nat.pow_succ_r; [ | flia ].
         now apply Nat.mul_le_mono_r.
      -rewrite Nat.add_sub_assoc.
       +now rewrite Nat.add_comm, Nat.add_sub.
       +rewrite Nat.pow_succ_r; [ | flia ].
        apply Nat.mul_le_mono_r; flia.
    }
    rewrite Nat.mod_small; [ | easy ].
    specialize (H7 H8).
    apply H7.
    replace (j + (s - j)) with s by flia Hs Hin.
    destruct j.
    -rewrite Nat.add_0_r in H4.
     rewrite H4 in H1.
     flia Hr H1.
    -rewrite nA_split with (e := i + j + 2) in H5; [ | flia Hin ].
     replace (n - (i + j + 2)) with (s - S j) in H5 by flia Hs.
     replace (i + j + 2 - 1) with (i + S j) in H5 by flia.
     assert (H9 : nA i (i + j + 2) u = rad ^ S j - 1). {
       rewrite power_summation_sub_1; [ | easy ].
       rewrite summation_mul_distr_l.
       unfold nA.
       rewrite summation_rtl.
       rewrite summation_shift; [ | flia ].
       replace (i + j + 2 - 1 - (i + 1)) with j by flia.
       apply summation_eq_compat.
       intros p Hp.
       replace (i + j + 2 - 1 + (i + 1) - (i + 1 + p)) with (i + (j - p) + 1)
         by flia Hp.
       rewrite H3; [ | flia Hp ].
       simpl; f_equal; f_equal.
       flia Hp.
     }
     rewrite H9 in H5.
     eapply Nat.le_trans; [ | apply H5 ].
     replace (S (k + 1)) with (t - j) by flia Ht.
     replace (s - S j) with ((t - j) + (s - S t)) by flia Hs Ht Hin.
     rewrite Nat.pow_add_r, Nat.mul_assoc.
     rewrite <- Nat.mul_add_distr_r.
     apply Nat.mul_le_mono_r.
     rewrite Nat.add_sub_assoc.
     +replace (rad ^ (t - j)) with (1 * rad ^ (t - j)) at 2 by flia.
      rewrite <- Nat.mul_add_distr_r.
      rewrite Nat.sub_add.
      *rewrite <- Nat.pow_add_r.
       now replace (S j + (t - j)) with (S t) by flia Ht.
      *now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
     +now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  }
  now specialize (H2 H5); clear H5.
-right; left.
 intros k.
 set (v := λ k, if Nat.eq_dec k (i + 1) then rad - 2 else u k).
 destruct k; [ now rewrite Nat.add_0_r | ].
 specialize (A_ge_1_add_8_eq v i) as H2.
 assert (H : ∀ k, v (i + k + 2) ≤ 2 * (rad - 1)). {
   intros j; unfold v.
   destruct (Nat.eq_dec (i + j + 2) (i + 1)); [ flia | ].
   replace (i + j + 2) with (i + (j + 1) + 1) by flia.
   apply Hur.
 }
 specialize (H2 H); clear H.
 assert (H : v (i + 1) = rad - 2). {
   unfold v.
   now destruct (Nat.eq_dec (i + 1) (i + 1)).
 }
 specialize (H2 H k); clear H.
 assert (H : A_ge_1 v i (k + 1) = true). {
   clear - Hr Hu H1.
   specialize (Hu (k + 1)) as H3.
   apply A_ge_1_true_iff in H3.
   apply A_ge_1_true_iff.
   unfold min_n in H3 |-*.
   replace (i + (k + 1) + 3) with (i + k + 4) in H3 |-* by flia.
   remember (rad * (i + k + 4)) as n eqn:Hn.
   replace (n - i - (k + 1) - 2) with (n - i - 1 - (k + 2)) in H3 |-* by flia.
   remember (n - i - 1) as s eqn:Hs.
   move s before n.
   eapply Nat.le_trans; [ apply H3 | ].
   assert (Hin : i + 1 ≤ n - 1). {
     rewrite Hn.
     destruct rad; [ easy | simpl; flia ].
   }
   setoid_rewrite nA_split_first; [ | easy | easy ].
   setoid_rewrite <- Nat.add_mod_idemp_l.
   2,3 : now apply Nat.pow_nonzero.
   rewrite H1.
   unfold v at 1.
   destruct (Nat.eq_dec (i + 1) (i + 1)) as [H| ]; [ clear H | easy ].
   replace (n - i - 2) with (s - 1) by flia Hs.
   rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   do 2 rewrite Nat.mul_sub_distr_r.
   replace rad with (rad ^ 1) at 1 6 by apply Nat.pow_1_r.
   rewrite <- Nat.mul_assoc.
   rewrite <- Nat.pow_add_r.
   replace (1 + (s - 1)) with s by flia Hs Hin.
   replace (2 * rad ^ s) with (rad ^ s + 1 * rad ^ s) by flia.
   rewrite Nat.add_sub_swap.
   -rewrite Nat.mod_add; [ | now apply Nat.pow_nonzero ].
    replace (nA (S i) n u) with (nA (S i) n v); [ easy | ].
    unfold nA.
    apply summation_eq_compat.
    intros j Hj; f_equal.
    unfold v.
    destruct (Nat.eq_dec j (i + 1)) as [H | ]; [ flia Hj H | easy ].
   -replace s with (1 + (s - 1)) at 2 by flia Hs Hin.
    rewrite Nat.pow_add_r, Nat.pow_1_r.
    now apply Nat.mul_le_mono_r.
 }
 specialize (H2 H); clear H.
 unfold v in H2.
 destruct (Nat.eq_dec (i + k + 2) (i + 1)) as [H3| H3]; [ flia H3 | ].
 now replace (i + k + 2) with (i + S k + 1) in H2 by flia.
Qed.

Theorem eq_nA_div_1 {r : radix} : ∀ i n u,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → nA i n u ≥ rad ^ (n - i - 1)
  → nA i n u / rad ^ (n - i - 1) = 1.
Proof.
intros * Hur Hn.
remember (n - i - 1) as s eqn:Hs.
remember (nA i n u) as x eqn:Hx.
replace x with (x - rad ^ s + 1 * rad ^ s).
-rewrite Nat.div_add; [ | now apply Nat.pow_nonzero ].
 rewrite Nat.div_small; [ easy | ].
 specialize (nA_upper_bound_for_add u i n Hur) as H1.
 rewrite <- Hx, <- Hs in H1.
 specialize (Nat.pow_nonzero rad s radix_ne_0) as H.
 flia H1 H.
-rewrite Nat.mul_1_l.
 now apply Nat.sub_add.
Qed.

Theorem A_ge_1_add_r_true_if {r : radix} : ∀ u i j k,
   A_ge_1 u i (j + k) = true
   → A_ge_1 u (i + j) k = true.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu.
apply A_ge_1_true_iff in Hu.
apply A_ge_1_true_iff.
unfold min_n in Hu |-*.
replace (i + (j + k) + 3) with (i + j + k + 3) in Hu by flia.
remember (rad * (i + j + k + 3)) as n eqn:Hn.
remember (n - (i + j) - 1) as s eqn:Hs.
move s before n.
assert (Hijn : i + j + 2 ≤ n - 1). {
  rewrite Hn.
  destruct rad; [ easy | simpl; flia ].
}
replace (n - i - 1) with (s + j) in Hu by flia Hs Hijn.
replace (s + j - S (j + k)) with (s - S k) in Hu by flia Hs.
move Hu at bottom.
revert Hu.
apply Decidable.contrapositive; [ apply Nat.le_decidable | ].
intros Hu.
apply Nat.nle_gt in Hu.
apply Nat.nle_gt.
rewrite Nat.pow_add_r.
rewrite Nat.mod_mul_r; try now apply Nat.pow_nonzero.
assert (H1 : nA (i + j) n u mod rad ^ s = nA i n u mod rad ^ s). {
  clear - Hs Hijn.
  destruct j; [ now rewrite Nat.add_0_r | ].
  symmetry.
  rewrite nA_split with (e := i + j + 2); [ | flia Hijn ].
  replace (i + j + 2 - 1) with (i + S j) by flia.
  replace (n - (i + j + 2)) with s by flia Hs.
  rewrite <- Nat.add_mod_idemp_l; [ | now apply Nat.pow_nonzero ].
  now rewrite Nat.mod_mul; [ | apply Nat.pow_nonzero ].
}
rewrite H1 in Hu.
replace (rad ^ S (j + k) - 1) with
  (rad ^ S k - 1 + (rad ^ j - 1) * rad ^ S k).
-rewrite Nat.mul_add_distr_r.
 apply Nat.add_lt_le_mono; [ easy | ].
 rewrite <- Nat.mul_assoc, Nat.mul_comm.
 rewrite <- Nat.pow_add_r.
 replace (S k + (s - S k)) with s.
 +apply Nat.mul_le_mono_pos_r.
  *now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *rewrite Nat.sub_1_r.
   apply Nat.lt_le_pred.
   apply Nat.mod_upper_bound.
   now apply Nat.pow_nonzero.
 +rewrite Nat.add_sub_assoc; [ flia | ].
  rewrite Hs, Hn.
  destruct rad; [ easy | simpl; flia ].
-rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
 rewrite Nat.add_comm.
 rewrite Nat.add_sub_assoc.
 +rewrite Nat.sub_add.
  *rewrite <- Nat.pow_add_r.
   now replace (j + S k) with (S (j + k)).
  *apply Nat_mul_le_pos_l.
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

Theorem freal_norm_eq_refl {r : radix} : reflexive _ freal_norm_eq.
Proof.
intros x.
unfold freal_norm_eq.
destruct (LPO_fst (has_same_digits x x)) as [Hs| Hs]; [ easy | exfalso ].
destruct Hs as (i & Hji & Hyy).
now apply has_same_digits_false_iff in Hyy.
Qed.

Theorem freal_norm_eq_sym {r : radix} : symmetric _ freal_norm_eq.
Proof.
intros x y Hxy.
unfold freal_norm_eq in Hxy |-*.
intros i; symmetry; apply Hxy.
Qed.

Theorem freal_norm_eq_trans {r : radix} : transitive _ freal_norm_eq.
Proof.
intros x y z Hxy Hyz.
unfold freal_norm_eq in Hxy, Hyz |-*.
intros i.
now rewrite Hxy, Hyz.
Qed.

Add Parametric Relation {r : radix} : (FracReal) freal_norm_eq
 reflexivity proved by freal_norm_eq_refl
 symmetry proved by freal_norm_eq_sym
 transitivity proved by freal_norm_eq_trans
 as freal_norm_eq_rel.

Add Parametric Morphism {r : radix} : freal_normalize
  with signature freal_norm_eq ==> freal_norm_eq
  as freal_norm_morph.
Proof.
intros x y Hxy.
unfold freal_norm_eq in Hxy |-*.
intros i.
unfold fd2n, freal_normalize; simpl.
unfold normalize.
unfold fd2n in Hxy.
destruct (LPO_fst (is_9_strict_after (freal x) i)) as [H2| H2].
-destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H3| H3].
 +destruct (lt_dec (S (d2n (freal x) i)) rad) as [H4| H4].
  *simpl.
   destruct (lt_dec (S (d2n (freal y) i)) rad) as [H5| H5].
  --simpl; unfold d2n.
    now rewrite Hxy.
  --unfold d2n in H4, H5.
    now rewrite Hxy in H4.
  *destruct (lt_dec (S (d2n (freal y) i)) rad) as [H5| ]; [ | easy ].
   unfold d2n in H4, H5.
   now rewrite Hxy in H4.
 +exfalso.
  destruct H3 as (j & Hjj & Hj).
  specialize (H2 j).
  apply is_9_strict_after_true_iff in H2.
  apply is_9_strict_after_false_iff in Hj.
  unfold d2n in H2, Hj.
  now rewrite Hxy in H2.
-destruct H2 as (j & Hjj & Hj).
 destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H2| H2].
 +specialize (H2 j).
  apply is_9_strict_after_true_iff in H2.
  apply is_9_strict_after_false_iff in Hj.
  unfold d2n in H2, Hj.
  now rewrite Hxy in Hj.
 +now rewrite Hxy.
Qed.

Add Parametric Morphism {r : radix} : freal_add
  with signature freal_norm_eq ==> freal_norm_eq ==> freal_norm_eq
  as freal_add_morph.
Proof.
intros x y Hxy x' y' Hxy'.
unfold freal_norm_eq in Hxy, Hxy'.
unfold freal_norm_eq.
intros i.
unfold fd2n, freal_add.
unfold fd2n in Hxy, Hxy'.
f_equal; simpl.
apply prop_carr_eq_compat.
intros j.
unfold "⊕", fd2n.
now rewrite Hxy, Hxy'.
Qed.

Theorem nA_ge_999000 {r : radix} : ∀ u i j,
  (∀ k, rad - 1 ≤ u (i + k + 1))
  → let n1 := rad * (i + j + 3) in
     let s1 := n1 - i - 1 in
     (rad ^ S j - 1) * rad ^ (s1 - S j) ≤ nA i n1 u.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur.
remember S as f; simpl; subst f.
set (n1 := rad * (i + j + 3)).
set (s1 := n1 - i - 1).
assert (Hin1 : i + j + 2 ≤ n1 - 1). {
  subst n1.
  destruct rad; [ easy | simpl; flia ].
}
rewrite nA_split with (e := j + i + 2); [ | flia Hin1 ].
apply le_plus_trans.
unfold nA.
rewrite summation_rtl.
rewrite summation_shift; [ | flia ].
rewrite power_summation_sub_1; [ | easy ].
rewrite summation_mul_distr_l.
replace (n1 - (j + i + 2)) with (s1 - S j) by (subst n1 s1; flia Hin1).
apply Nat.mul_le_mono_r.
replace (j + i + 2 - 1 - (i + 1)) with j by flia.
apply (@summation_le_compat nat_ord_ring_def).
intros k Hk; simpl; unfold Nat.le.
replace (j + i + 2 - 1 + (i + 1) - (i + 1 + k))
  with (j + i + 1 - k) by flia.
replace (j + i + 2 - 1 - (j + i + 1 - k)) with k by flia Hk.
apply Nat.mul_le_mono_r.
specialize (Hur (j - k)).
replace (i + (j - k) + 1) with (j + i + 1 - k) in Hur by flia Hk.
easy.
Qed.
