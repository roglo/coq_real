(* Real between 0 and 1, i.e. fractional part of a real.
   Implemented as function of type nat → nat.
   Operations + and * implemented using LPO. *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz NPeano.
Require Import Misc Summation NQ.
Import Init.Nat PeanoNat.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.
(* "pauto" = "auto" failing if not working *)
Tactic Notation "pauto" := progress auto.

Hint Resolve Nat.pow_nonzero.

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
 split; [ now subst k | cbn ].
 cbn in Hk; destruct Hk; intros j H1 H2.
 now apply lt_not_le in H2.

 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hn.
 cbn in Hk.
 remember (u i =? 0) as b eqn:Hb.
 symmetry in Hb.
 destruct b; cbn in Hk.
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
-intros k; subst v; specialize (H k); cbn in H.
 now destruct (u k).
-remember (first_such_that (λ i, negb (Nat.eqb (v i) 0)) i 0) as j eqn:Hj.
 exists j.
 assert (Hui : v (i + 0) ≠ 0) by now rewrite Nat.add_0_r.
 specialize (first_such_that_has_prop v i 0 j Hui Hj) as (Huj, H).
 subst v; split.
 +intros k Hkj; cbn in H.
  specialize (H k (Nat.le_0_l k) Hkj).
  now destruct (u k).
 +cbn in Huj.
  now destruct (u j).
Qed.

(* Radix *)

Class radix := { rad : nat; radix_ge_2 : rad ≥ 2 }.

Theorem radix_gt_0 {r : radix} : 0 < rad.
Proof.
destruct r as (rad, radi); cbn; flia radi.
Qed.

Theorem radix_ge_1 {r : radix} : 1 ≤ rad.
Proof.
destruct r as (rad, radi); cbn; flia radi.
Qed.

Theorem radix_ne_0 {r : radix} : rad ≠ 0.
Proof.
destruct r as (rad, radi); cbn; flia radi.
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
cbn in H.
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

Declare Scope freal_scope.
Delimit Scope freal_scope with F.

Record FracReal {r : radix} := { freal : nat → digit }.
Arguments freal r _%F.

Definition fd2n {r : radix} x (i : nat) := dig (freal x i).
Arguments fd2n _ x%F i%nat.

(* *)

Theorem fold_fd2n {r : radix} : ∀ x i, dig (freal x i) = fd2n x i.
Proof. easy. Qed.

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
 remember NQ_of_pair as f; remember S as g; cbn; subst f g.
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

Theorem NQpower_summation_inv (rg := NQ_ord_ring) : ∀ a n,
  a > 0
  → (1 - 1 // a ^ S n = (1 - 1 // a) * Σ (i = 0, n), 1 // a ^ i)%NQ.
Proof.
intros * Ha.
destruct (eq_nat_dec a 1) as [Ha1| Ha1]. {
  now subst a; rewrite Nat.pow_1_l, NQsub_diag.
}
assert (Haa : a ≠ 0 ∧ a ≠ 1) by flia Ha Ha1; clear Ha Ha1.
rewrite NQpower_summation; [ | flia Haa ].
symmetry.
rewrite NQsub_pair_pos; [ | easy | flia Haa | flia Haa ].
do 2 rewrite Nat.mul_1_l.
rewrite NQmul_pair; [ | flia Haa | ]; cycle 1. {
  intros H; apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ | flia Haa H ].
  apply Nat.pow_nonzero in H; [ easy | flia Haa ].
}
rewrite Nat.mul_comm, Nat.mul_assoc.
rewrite <- NQmul_pair; [ | | flia Haa ]; cycle 1. {
  intros H; apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ flia Haa H | ].
  apply Nat.pow_nonzero in H; [ easy | flia Haa ].
}
rewrite NQpair_diag; [ | flia Haa ].
rewrite NQmul_1_r, <- Nat.pow_succ_r'.
destruct Haa as (Ha, Ha1).
rewrite NQsub_pair_pos; [ | flia | pauto | ]; cycle 1. {
  apply Nat.mul_le_mono_l.
  apply (lt_le_trans _ 2); [ flia | cbn ].
  replace 2 with (2 * 1) by flia.
  apply Nat.mul_le_mono; [ flia Ha Ha1 | ].
  apply Nat.neq_0_lt_0; pauto.
}
now do 2 rewrite Nat.mul_1_l.
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
 cbn; rewrite Nat.add_0_r.
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

Notation "x ⊕ y" := (freal_add_series x y) (at level 50) : freal_scope.

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
Definition B {r : radix} (rg := NQ_ord_ring) i n u l :=
  (Σ (j = n, n + l - 1), (u j // rad ^ (j - i))%NQ : NQ).

(**)

Definition min_n {r : radix} i k := rad * (i + k + 3).

Definition fA_ge_1_ε {r : radix} u i k :=
  let n := min_n i k in
  let s := n - i - 1 in
  if NQlt_le_dec (NQfrac (A i n u)) (1 - 1 // rad ^ S k)%NQ then false else true.

(* Propagation of Carries *)

Definition carry {r : radix} u i :=
  match LPO_fst (fA_ge_1_ε u i) with
  | inl _ =>
      let n := min_n i 0 in
      NQintg (A i n u) + 1
  | inr (exist _ k _) =>
      let n := min_n i k in
      NQintg (A i n u)
  end.

Definition prop_carr {r : radix} u i :=
  let d := u i + carry u i in
  mkdig _ (d mod rad) (Nat.mod_upper_bound d rad radix_ne_0).

(*
Definition freal_mul_to_seq {r : radix} (a b : FracReal) :=
  prop_carr (freal_mul_series a b).
*)

Definition freal_add {r : radix} x y := {| freal := prop_carr (x ⊕ y)%F |}.
Arguments freal_add _ x%F y%F.

(*
Definition freal_mul {r : radix} (a b : FracReal) :=
  {| freal := freal_mul_to_seq a b |}.
*)

Notation "a + b" := (freal_add a b) : freal_scope.
(*
Notation "a * b" := (freal_mul a b) : freal_scope.
*)

Theorem A_freal_additive {r : radix} : ∀ i n x y,
  A i n (x ⊕ y)%F = (A i n (fd2n x) + A i n (fd2n y))%NQ.
Proof.
intros.
unfold A.
unfold "⊕"%F.
rewrite summation_eq_compat with
  (h := λ j, (fd2n x j // rad ^ (j - i) + fd2n y j // rad ^ (j - i))%NQ);
  cycle 1. {
  intros; apply NQpair_add_l.
}
now rewrite summation_add_distr.
Qed.

Theorem A_split {r : radix} : ∀ e u i n,
  i + 1 ≤ e ≤ n
  → A i n u = (A i e u + A (e - 1) n u * 1 // rad ^ (e - i - 1))%NQ.
Proof.
intros * Hin.
unfold A.
rewrite summation_split with (e0 := e - 1); [ | flia Hin ].
remember (1 // rad ^ (e - i - 1))%NQ as rr; simpl; subst rr; f_equal.
rewrite summation_mul_distr_r.
replace (e - 1 + 1) with (S (e - 1)) by flia.
apply summation_eq_compat.
intros j Hj.
rewrite NQmul_pair; [ | pauto | pauto ].
rewrite Nat.mul_1_r; f_equal.
rewrite <- Nat.pow_add_r; f_equal.
flia Hj Hin.
Qed.

Theorem A_ge_0 {r : radix} : ∀ i n u, (0 ≤ A i n u)%NQ.
Proof.
intros.
unfold A.
set (rg := NQ_ord_ring).
replace 0%NQ with (Σ (j = i + 1, n - 1), 0)%NQ.
-apply summation_le_compat.
 intros j Hj.
 replace 0%NQ with (0 // 1)%NQ by easy.
 apply NQle_pair; [ easy | pauto | ].
 apply Nat.le_0_l.
-now apply all_0_summation_0.
Qed.

Theorem B_of_A {r : radix} : ∀ u i n l,
  i + 1 ≤ n → (B i n u l = A (n - 1) (n + l) u * 1 // rad ^ (n - i - 1))%NQ.
Proof.
intros * Hin.
unfold B, A.
rewrite summation_mul_distr_r.
rewrite Nat.sub_add; [ | flia Hin ].
apply summation_eq_compat.
intros j Hj.
rewrite NQmul_pair; [ | pauto | pauto ].
rewrite Nat.mul_1_r, <- Nat.pow_add_r.
f_equal; f_equal.
flia Hin Hj.
Qed.

(*
Theorem summation_inv_pow (rg := NQ_ord_ring) : ∀ r b n,
  r ≥ 2
  → (Σ (j = b, b + n), (1 // r ^ j) =
      (r ^ S n - 1) // (r ^ (b + n) * (r - 1)))%NQ.
Proof.
intros * Hr.
revert b.
induction n; intros.
-rewrite Nat.add_0_r, Nat.pow_1_r, summation_only_one.
 replace (r - 1) with (1 * (r - 1)) at 1 by apply Nat.mul_1_l.
 destruct r; [ easy | ].
 rewrite <- NQmul_pair; [ | pauto | flia Hr ].
 rewrite NQpair_diag; [ | flia Hr ].
 now rewrite NQmul_1_r.
-replace (b + S n) with (S (b + n)) by flia.
 rewrite summation_split_last; [ | flia ].
 rewrite IHn.
 rewrite NQadd_pair; cycle 1. {
   intros H; apply Nat.eq_mul_0 in H.
   destruct H as [H| H]; [ | flia Hr H ].
   destruct r; [ easy | ].
   now apply Nat.pow_nonzero in H.
 } {
   destruct r; [ easy | pauto ].
 }
 rewrite Nat.mul_1_r.
 replace (S (b + n)) with (1 + (b + n)) by easy.
 rewrite Nat.pow_add_r, Nat.pow_1_r.
 rewrite Nat.mul_assoc, Nat.mul_comm.
 rewrite <- Nat.mul_add_distr_l.
 rewrite <- Nat.mul_assoc.
 rewrite <- NQmul_pair; cycle 1. {
   destruct r; [ easy | pauto ].
 } {
   intros H; apply Nat.eq_mul_0 in H.
   destruct H as [H| H]; [ flia Hr H | ].
   apply Nat.eq_mul_0 in H.
   destruct H as [H| H]; [ flia Hr H | ].
   destruct r; [ easy | ].
   now apply Nat.pow_nonzero in H.
 }
 rewrite NQpair_diag, NQmul_1_l; cycle 1. {
   destruct r; [ easy | pauto ].
 }
 f_equal; [ | apply Nat.mul_comm ].
 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
 rewrite Nat.add_sub_assoc; [ | flia Hr ].
 rewrite Nat.sub_add; cycle 1. {
   replace r with (1 * r) at 1 by flia.
   apply Nat.mul_le_mono_r.
   apply Nat_pow_ge_1; flia Hr.
 }
 now rewrite Nat.mul_comm.
Qed.
*)

Theorem summation_id_inv_pow (rg := NQ_ord_ring) : ∀ r b n,
  r ≥ 2
  → (Σ (i = b, b + n), (i // r ^ i) =
      (((b * (r - 1) + 1) * r ^ (n + 1) - (b + n + 1) * r + (b + n))
      // (r ^ (b + n) * (r - 1) ^ 2)))%NQ.
Proof.
intros * Hr.
revert b.
induction n; intros.
-rewrite Nat.add_0_r, Nat.add_0_l, Nat.pow_1_r, summation_only_one.
(*
 rewrite <- Nat.sub_add_distr.
*)
 destruct (zerop b) as [Hb| Hb].
 +subst b; cbn.
  do 2 rewrite Nat.add_0_r.
  now rewrite Nat.sub_diag.
 +rewrite <- Nat.mul_sub_distr_r.
  rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
  rewrite Nat.sub_add_distr, Nat_sub_sub_swap, Nat.add_sub.
  replace b with (b * 1) at 4 5 6 by flia.
  do 2 rewrite <- Nat.mul_sub_distr_l.
  rewrite <- Nat.mul_assoc, <- Nat.mul_add_distr_l.
  replace ((r - 1 - 1) * r + 1) with ((r - 1) ^ 2). 2: {
    cbn; rewrite Nat.mul_1_r.
    rewrite Nat.mul_sub_distr_l.
    do 4 rewrite Nat.mul_sub_distr_r.
    destruct r; [ easy | ].
    destruct r; [ flia Hr | cbn; flia ].
  }
  rewrite <- NQmul_pair by (apply Nat_pow_neq_0; flia Hr).
  rewrite NQpair_diag; [ now rewrite NQmul_1_r | ].
  apply Nat_pow_neq_0; flia Hr.
-replace (b + S n) with (S (b + n)) at 1 by flia.
 rewrite summation_split_last; [ | flia ].
 rewrite IHn.
 rewrite NQadd_pair; cycle 1. {
   apply Nat.neq_mul_0.
   split; apply Nat_pow_neq_0; flia Hr.
 } {
   apply Nat_pow_neq_0; flia Hr.
 }
 apply NQeq_pair. {
   apply Nat.neq_mul_0; split.
   -apply Nat.neq_mul_0; split; apply Nat_pow_neq_0; flia Hr.
   -apply Nat.pow_nonzero; flia Hr.
 } {
   apply Nat.neq_mul_0; split; apply Nat_pow_neq_0; flia Hr.
 }
 (* simplification (r-1)² *)
 symmetry.
 do 3 rewrite <- Nat.mul_assoc.
 rewrite Nat.mul_comm.
 do 2 rewrite <- Nat.mul_assoc.
 rewrite Nat.mul_comm.
 symmetry; rewrite Nat.mul_assoc.
 f_equal.
 (* simplification r^{b+n+1} *)
 symmetry; rewrite Nat.mul_comm.
 f_equal; [ | f_equal; flia ].
 (* simplification r^{b+n} *)
 remember (r ^ (b + n) * ((r - 1) ^ 2 * S (b + n))) as x eqn:Hx.
 rewrite Nat.mul_comm in Hx; subst x.
 remember (r ^ S (b + n)) as x eqn:Hx.
 cbn in Hx; subst x.
 rewrite Nat.mul_assoc.
 rewrite <- Nat.mul_add_distr_r; f_equal.
 (* *)
 symmetry.
 rewrite Nat.mul_add_distr_r, Nat.mul_sub_distr_r.
 do 2 rewrite <- Nat.mul_assoc.
 replace (r ^ (n + 1) * r) with (r ^ (S n + 1)) by (cbn; flia).
 remember ((b * (r - 1) + 1) * r ^ (S n + 1)) as XXX.
 replace (r * r) with (r ^ 2) by (cbn; flia).
 replace (S (b + n)) with (b + n + 1) by flia.
 rewrite Nat.add_shuffle0, Nat.mul_comm.
 rewrite <- Nat_sub_sub_distr. 2: {
   split.
   -apply Nat.mul_le_mono_r, Nat.pow_le_mono_l; flia Hr.
   -subst XXX.
    replace (S n + 1) with (n + 2) by flia.
    rewrite Nat.pow_add_r, Nat.mul_assoc, Nat.mul_comm.
    apply Nat.mul_le_mono_r.
    rewrite Nat.mul_add_distr_r, Nat.mul_1_l, <- Nat.add_assoc.
    apply Nat.add_le_mono.
    +replace b with (b * (1 * 1)) at 1 by flia.
     rewrite <- Nat.mul_assoc.
     apply Nat.mul_le_mono_l.
     apply Nat.mul_le_mono; [ flia Hr | ].
     apply Nat_pow_ge_1; flia Hr.
    +rewrite Nat.add_1_r.
     apply Nat.pow_gt_lin_r; flia Hr.
 }
 rewrite <- Nat.mul_sub_distr_r.
 rewrite Nat_sqr_sub_sqr.
 replace (r - (r - 1)) with 1 by flia Hr.
 rewrite Nat.mul_1_r.
 rewrite Nat.mul_add_distr_r.
 rewrite Nat.mul_add_distr_l, Nat.mul_1_r, Nat.mul_comm.
 rewrite <- Nat.add_assoc.
 rewrite Nat.sub_add_distr, Nat_sub_sub_swap.
 rewrite <- Nat.add_sub_swap. 2: {
   subst XXX.
   apply Nat.le_add_le_sub_r.
   rewrite Nat.add_assoc.
   replace (S n + 1) with (n + 2) by flia.
   rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
   rewrite Nat.add_shuffle0, Nat.add_assoc, Nat.mul_comm.
   rewrite <- Nat.mul_add_distr_r.
   rewrite Nat.add_shuffle0, <- Nat.add_assoc.
   replace (r + (r - 1)) with (2 * r - 1) by flia.
   replace (2 * r - 1) with ((2 * r - 1) * 1) at 2 by flia.
   rewrite <- Nat.mul_add_distr_l.
   rewrite Nat.pow_add_r, Nat.mul_assoc, Nat.mul_comm.
   apply Nat.mul_le_mono.
   -rewrite Nat.mul_add_distr_r, Nat.mul_1_l, <- Nat.add_assoc.
    apply Nat.add_le_mono.
    +replace b with (b * (1 * 1)) at 1 by flia.
     rewrite <- Nat.mul_assoc.
     apply Nat.mul_le_mono_l.
     apply Nat.mul_le_mono; [ flia Hr | ].
     apply Nat_pow_ge_1; flia Hr.
    +rewrite Nat.add_1_r.
     apply Nat.pow_gt_lin_r; flia Hr.
   -destruct r; [ easy | ].
    cbn; rewrite Nat.add_0_r, Nat.sub_0_r, Nat.mul_1_r.
    replace (r + S r) with (S (r + r * 1)) by flia.
    apply -> Nat.succ_le_mono.
    apply Nat.add_le_mono_l, Nat.mul_le_mono_l; flia Hr.
 }
 rewrite Nat.add_sub.
 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
 rewrite Nat.add_sub_assoc. 2: {
   replace (b + n + 1) with (1 * (b + n + 1)) at 1 by flia.
   apply Nat.mul_le_mono_r; flia Hr.
 }
 replace r with (r * 1) at 1 by flia.
 rewrite <- Nat.mul_add_distr_l.
 replace (1 + (b + n + 1)) with (b + S n + 1) by flia.
 rewrite Nat.mul_comm.
 replace (b + n + 1) with (b + S n) by flia.
 rewrite Nat_sub_sub_distr; [ easy | ].
 subst XXX.
 split.
 +rewrite Nat.mul_add_distr_r.
  apply (le_trans _ ((b + S n) * r)); [ | apply Nat.le_add_r ].
  replace (b + S n) with ((b + S n) * 1) at 1 by flia Hr.
  apply Nat.mul_le_mono_l; flia Hr.
 +rewrite Nat.pow_add_r, Nat.pow_1_r, Nat.mul_assoc.
  apply Nat.mul_le_mono_r.
  rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  rewrite <- Nat.add_assoc.
  apply Nat.add_le_mono.
  *replace b with (b * (1 * 1)) at 1 by flia.
   rewrite <- Nat.mul_assoc.
   apply Nat.mul_le_mono_l.
   apply Nat.mul_le_mono; [ flia Hr | ].
   apply Nat_pow_ge_1; flia Hr.
  *rewrite Nat.add_1_r.
   apply Nat.pow_gt_lin_r; flia Hr.
Qed.

Theorem summation_succ_inv_pow (rg := NQ_ord_ring) : ∀ r b n,
  r ≥ 2
  → (Σ (i = b, b + n), ((i + 1) // r ^ i) =
       (((b + 1) * (r - 1) + 1) * r ^ (n + 1) - (b + n + 2) * r + (b + n + 1))
       // (r ^ (b + n) * (r - 1) ^ 2))%NQ.
Proof.
intros * Hr.
apply (NQmul_cancel_l 1%NQ); [ easy | ].
replace 1%NQ with (r // 1 * 1 // r)%NQ at 1. 2: {
  now rewrite NQmul_inv_pair by flia Hr.
}
rewrite NQmul_1_l.
rewrite <- NQmul_assoc, summation_mul_distr_l.
set (g i := (i // r ^ i)%NQ).
rewrite summation_eq_compat with (h := λ i, g (S i)). 2: {
  intros i Hi.
  remember NQ_of_pair as f; cbn; subst f.
  rewrite NQmul_pair; [ | flia Hr | apply Nat_pow_neq_0; flia Hr ].
  unfold g.
  rewrite Nat.mul_1_l; f_equal.
  apply Nat.add_1_r.
}
rewrite <- summation_succ_succ; subst g.
replace (S (b + n)) with (S b + n) by easy.
rewrite summation_id_inv_pow; [ | easy ].
rewrite NQmul_pair; [ | easy | ]. 2: {
  apply Nat.neq_mul_0; split; apply Nat_pow_neq_0; flia Hr.
}
rewrite Nat.mul_1_l.
replace (r ^ (S b + n)) with (r * r ^ (b + n)) by easy.
rewrite <- Nat.mul_assoc.
rewrite <- NQmul_pair; [ | flia Hr | ]. 2: {
  apply Nat.neq_mul_0; split; apply Nat_pow_neq_0; flia Hr.
}
rewrite NQpair_diag; [ | flia Hr ].
rewrite NQmul_1_l.
replace (S b + n + 1) with (b + n + 2) by flia.
replace (S b + n) with (b + n + 1) at 1 by flia.
replace (S b) with (b + 1) by flia.
easy.
Qed.

Theorem B_gen_upper_bound {r : radix} : ∀ u i n l,
  n ≠ 0
  → i < n
  → (∀ j, u (n + j) ≤ (n + j + 1) * (rad - 1) ^ 2)
  → (B i n u l ≤ (n * (rad - 1) + rad) // rad ^ (n - i - 1))%NQ.
Proof.
intros * Hn Hi Hu.
specialize radix_ge_2 as Hr.
unfold B.
destruct (zerop l) as [Hl| Hl].
-subst l.
 rewrite Nat.add_0_r.
 rewrite summation_empty; [ | flia Hn ].
 replace 0%Rg with (0 // 1)%NQ by easy.
 apply NQle_pair; [ easy | pauto | flia ].
-eapply NQle_trans.
 +apply summation_le_compat with
    (g := λ j, (((rad - 1) ^ 2 * rad ^ i) // 1 * (j + 1) // rad ^ j)%NQ).
  intros k Hk.
  remember Nat.pow as f; cbn; subst f.
  rewrite <- NQpair_mul_r.
  apply NQle_pair; [ now apply Nat_pow_neq_0 | now apply Nat_pow_neq_0 | ].
  apply (Nat.mul_le_mono_pos_l _ _ (rad ^ i)). {
    now apply Nat.neq_0_lt_0, Nat_pow_neq_0.
  }
  do 2 rewrite Nat.mul_assoc.
  rewrite <- Nat.pow_add_r.
  replace (i + (k - i)) with k by flia Hi Hk.
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_l.
  rewrite Nat.mul_shuffle0, Nat.mul_comm.
  apply Nat.mul_le_mono_r.
  rewrite Nat.mul_comm.
  replace k with (n + (k - n)) by flia Hk.
  apply Hu.
 +replace (n + l - 1) with (n + (l - 1)) by flia Hl.
  rewrite <- summation_mul_distr_l.
  rewrite summation_succ_inv_pow; [ | easy ].
  remember Nat.pow as f; cbn; subst f.
  rewrite Nat.sub_add; [ | easy ].
  replace (n + (l - 1)) with (n + l - 1) by flia Hl.
  rewrite Nat.sub_add; [ | flia Hl ].
  replace (n + l - 1 + 2) with (n + l + 1) by flia Hl.
  rewrite <- NQpair_mul_r.
  apply NQle_pair; [ | now apply Nat_pow_neq_0 | ]. {
    apply Nat.neq_mul_0; split; apply Nat_pow_neq_0; flia Hr.
  }
  rewrite Nat.mul_shuffle0.
  do 2 rewrite <- Nat.mul_assoc.
  rewrite Nat.mul_comm, Nat.mul_assoc.
  rewrite <- Nat.pow_add_r.
  replace (i + (n - i - 1)) with (n - 1) by flia Hi.
  replace (n + l - 1) with (n - 1 + l) by flia Hn.
  rewrite Nat.pow_add_r.
  do 3 rewrite <- Nat.mul_assoc.
  apply Nat.mul_le_mono_l.
  rewrite Nat.mul_assoc.
  rewrite Nat.mul_shuffle0.
  apply Nat.mul_le_mono_r.
  do 2 rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
  rewrite Nat.mul_comm.
  rewrite Nat.sub_add. 2: {
    replace (rad ^ l) with (rad ^ l * 1) at 1 by flia.
    apply Nat.mul_le_mono_l; flia Hr.
  }
  rewrite <- Nat_sub_sub_distr.
  *apply Nat.lt_le_incl, Nat.sub_lt.
...
  rewrite <- NQpair_add_l, <- NQpair_mul_r.
  apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_shuffle0.
  remember (u k * rad ^ k) as x.
  rewrite Nat.mul_comm; subst x.
  rewrite <- Nat.mul_assoc, <- Nat.pow_add_r.
  apply Nat.mul_le_mono.
  *replace k with (n + (k - n)) by flia Hk.
   rewrite Nat.mul_comm; apply Hu.
  *apply Nat.pow_le_mono_r; [ easy | flia ].
 +rewrite <- summation_mul_distr_l.
...
  rewrite summation_add_distr.
  rewrite <- Nat.add_sub_assoc; [ | easy ].
  replace (n + l - 1) with (n + (l - 1)) by flia Hl.
...
  rewrite summation_inv_pow; [ | easy ].
...
  rewrite summation_id_div_pow.
...

Theorem B_upper_bound {r : radix} : ∀ u i k l,
  (B i (min_n i k) u l < 1 // rad ^ S k)%NQ.
Proof.
intros.
unfold B.
Search (1 // _ ^ _)%NQ.
...

Theorem frac_ge_if_all_fA_ge_1_ε {r : radix} : ∀ u i,
  (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k l, (NQfrac (A i (min_n i k + l) u) ≥ 1 - 1 // rad ^ S k)%NQ.
Proof.
intros u i H k l.
specialize radix_ge_2 as Hr.
specialize (H k).
unfold fA_ge_1_ε in H.
destruct
  (NQlt_le_dec (NQfrac (A i (min_n i k) u))
     (1 - 1 // rad ^ S k)%NQ) as [H1| H1]; [ easy | clear H ].
eapply NQle_trans; [ apply H1 | ].
-remember (A i (min_n i k) u) as a eqn:Ha.
 rewrite A_split with (e := min_n i k); subst a; cycle 1. {
   unfold min_n; split; [ | flia ].
   destruct rad; [ easy | cbn; flia ].
 }
 rewrite <- B_of_A; cycle 1. {
   unfold min_n; destruct rad; [ easy | cbn; flia ].
 }
...
 rewrite NQfrac_add; [ | apply A_ge_0 | ]; cycle 1. {
   replace 0%NQ with (0 * 0)%NQ by easy.
   apply NQmul_le_mono_nonneg; [ easy | | easy | easy ].
   apply A_ge_0.
 }
 remember (min_n i k) as n eqn:Hn.
Search (NQfrac (_ + _)%NQ).
...
Qed.

Theorem frac_ge_if_all_fA_ge_1_ε {r : radix} : ∀ u i,
  (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k, (NQfrac (A i (min_n i k) u) ≥ 1 - 1 // rad ^ S k)%NQ.
Proof.
intros u i H k.
specialize (H k).
unfold fA_ge_1_ε in H.
now destruct
  (NQlt_le_dec (NQfrac (A i (min_n i k) u)) (1 - 1 // rad ^ S k)%NQ).
Qed.

Theorem frac_eq_if_all_fA_ge_1_ε {r : radix} : ∀ u i,
  (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k, ∃ x, (x < 1 // rad ^ S k)%NQ ∧
     NQfrac (A i (min_n i k) u) = (1 - 1 // rad ^ S k + x)%NQ.
Proof.
intros u i H k.
specialize (H k).
unfold fA_ge_1_ε in H.
remember (A i (min_n i k) u) as x eqn:Hx.
destruct (NQlt_le_dec (NQfrac x) (1 - 1 // rad ^ S k)%NQ) as [H1| H1];
  [ easy | clear H ].
exists (NQfrac x - (1 - 1 // rad ^ S k))%NQ.
rewrite NQsub_sub_distr.
split.
-specialize (NQfrac_lt_1 x) as H2.
 replace (1 // rad ^ S k)%NQ with (0 + 1 // rad ^ S k)%NQ at 2 by easy.
 apply NQadd_lt_mono_r.
 now apply (NQadd_lt_mono_r _ 1%NQ).
-rewrite NQadd_assoc, NQadd_add_swap, NQsub_add.
 rewrite NQadd_sub_assoc, NQadd_comm.
 now rewrite NQadd_sub.
Qed.

Theorem freal_add_series_comm {r : radix} : ∀ x y i,
  (x ⊕ y)%F i = (y ⊕ x)%F i.
Proof.
intros.
unfold "⊕".
apply Nat.add_comm.
Qed.

Theorem A_freal_add_series_comm {r : radix} : ∀ x y i n,
  A i n (x ⊕ y)%F = A i n (y ⊕ x)%F.
Proof.
intros.
unfold A; cbn.
apply summation_eq_compat; intros j Hj.
now rewrite freal_add_series_comm.
Qed.

Theorem A_ge_1_freal_add_series_comm {r : radix} : ∀ x y i k,
  fA_ge_1_ε (x ⊕ y)%F i k = fA_ge_1_ε (y ⊕ x)%F i k.
Proof.
intros.
unfold fA_ge_1_ε.
now rewrite A_freal_add_series_comm.
Qed.

Theorem prop_carr_add_comm {r : radix} : ∀ x y i,
  prop_carr (x ⊕ y)%F i = prop_carr (y ⊕ x)%F i.
Proof.
intros.
apply digit_eq_eq; cbn.
unfold carry.
rewrite freal_add_series_comm.
destruct (LPO_fst (fA_ge_1_ε (x ⊕ y)%F i)) as [Hxy| Hxy].
-setoid_rewrite freal_add_series_comm.
 destruct (LPO_fst (fA_ge_1_ε (y ⊕ x)%F i)) as [Hyx| Hyx].
 +f_equal; f_equal; f_equal; f_equal.
  apply summation_eq_compat.
  intros k Hk; f_equal.
  apply freal_add_series_comm.
 +destruct Hyx as (k & Hjk & Hk).
  rewrite A_ge_1_freal_add_series_comm in Hk.
  now rewrite Hxy in Hk.
-destruct Hxy as (k & Hjk & Hk).
 rewrite A_ge_1_freal_add_series_comm in Hk.
 destruct (LPO_fst (fA_ge_1_ε (y ⊕ x)%F i)) as [Hyx| Hyx].
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

Theorem dig_unorm_add_comm {r : radix} : ∀ x y i,
  freal (x + y) i = freal (y + x) i.
Proof.
intros; cbn.
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
rewrite NQmul_pair; [ | pauto | easy ].
rewrite Nat.mul_1_r.
rewrite Nat.mul_comm, <- Nat.pow_succ_r'.
rewrite <- Nat.sub_succ_l; [ easy | flia Hj ].
Qed.

Theorem A_split_last {r : radix} : ∀ i n u,
  i + 1 ≤ n - 1
  → A i n u = (A i (n - 1) u + u (n - 1)%nat // rad ^ (n - i - 1))%NQ.
Proof.
intros * Hin.
unfold A.
replace (n - 1) with (S (n - 1 - 1)) at 1 by flia Hin.
rewrite summation_split_last; [ | flia Hin ].
cbn; f_equal.
replace (S (n - 1 - 1)) with (n - 1) by flia Hin.
f_equal; f_equal.
destruct i; flia.
Qed.

Theorem A_dig_seq_ub {r : radix} : ∀ u n i,
  (∀ j, i < j < n → u j < rad)
  → i + 1 ≤ n - 1
  → (A i n u ≤ 1 -  1 // rad ^ (n - i - 1))%NQ.
Proof.
intros * Hu Hin.
specialize radix_ge_2 as Hr.
apply (NQle_trans _ (A i n (λ i, rad - 1))).
-apply summation_le_compat; intros j Hj; cbn.
 apply NQle_pair; [ pauto | pauto | ].
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
   rewrite NQmul_pair; [ | easy | pauto ].
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
 rewrite NQsub_pair_pos; [ | easy | pauto | ]; cycle 1. {
   apply Nat.mul_le_mono_l, Nat.neq_0_lt_0; pauto.
 }
 do 2 rewrite Nat.mul_1_l.
 apply NQle_pair; [ pauto | pauto | ].
 replace (S (n - i - 2)) with (n - i - 1) by flia Hin.
 now rewrite Nat.mul_comm.
Qed.

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
  rewrite NQmul_pair; [ | easy | pauto ].
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
rewrite NQsub_pair_pos; [ | easy | pauto | ]; cycle 1. {
  apply Nat.mul_le_mono_l.
  apply lt_le_trans with (m := 2); [ apply Nat.lt_0_2 | ].
  destruct s; [ flia Hs Hin | ].
  cbn; replace 2 with (2 * 1) by easy.
  apply Nat.mul_le_mono; [ easy | ].
  apply Nat.neq_0_lt_0; pauto.
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
  pauto.
}
rewrite NQpair_diag; [ | flia Hr ].
rewrite NQmul_1_r.
replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
rewrite <- Nat.pow_add_r.
now replace (1 + (s - 1)) with s by flia Hs Hin.
Qed.

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
  rewrite NQmul_pair; [ | easy | pauto ].
  rewrite Nat.mul_1_r, Nat.add_shuffle0, Nat.mul_comm.
  replace rad with (rad ^ 1) at 4 by apply Nat.pow_1_r.
  rewrite <- Nat.pow_add_r.
  replace (i + j + 1 - i) with (j + 1) by flia; f_equal.
  rewrite Hj.
  rewrite NQmul_pair; [ | easy | pauto ].
  now rewrite Nat.mul_1_l.
}
rewrite <- summation_mul_distr_l.
remember NQ_of_pair as f; simpl; subst f.
rewrite NQpower_summation; [ | flia Hr ].
replace (n - 1 - (i + 1)) with (n - i - 1 - 1) by flia Hin.
remember (n - i - 1) as s eqn:Hs.
replace (S (s - 1)) with s by flia Hs Hin.
rewrite NQsub_pair_pos; [ | easy | pauto | ]; cycle 1. {
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_l.
  apply lt_le_trans with (m := 2); [ apply Nat.lt_0_2 | ].
  destruct s; [ flia Hs Hin | ].
  cbn; replace 2 with (2 * 1) by easy.
  apply Nat.mul_le_mono; [ easy | ].
  apply Nat.neq_0_lt_0; pauto.
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

Theorem A_9_8_all_18 {r : radix} : ∀ j u i n,
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
rewrite A_split with (e := i + j + 1); [ | flia Hin ].
rewrite A_all_9; [ | intros k Hk; apply Hbef; flia Hk ].
unfold A at 1.
rewrite Nat.add_sub.
replace (i + j + 2 - 1) with (i + j + 1) by flia.
rewrite summation_only_one, Hwhi.
rewrite A_all_18; cycle 1. {
  intros k.
  replace (i + j + 1 + k + 1) with (i + j + k + 2) by flia.
  apply Haft.
}
replace (i + j + 1 - i - 1) with j by flia.
replace (i + j + 1 - (i + j)) with 1 by flia.
rewrite Nat.pow_1_r.
replace (n - (i + j + 1) - 1) with (n - i - j - 2) by flia.
replace (i + j + 2 - i - 1) with (j + 1) by flia.
rewrite NQmul_pair; [ | easy | pauto ].
rewrite Nat.mul_1_r.
rewrite NQmul_sub_distr_r.
rewrite NQmul_pair; [ | easy | pauto ].
rewrite Nat.mul_1_r, Nat.mul_1_l.
rewrite <- Nat.pow_succ_r', Nat.add_1_r.
rewrite NQmul_pair; [ | pauto | pauto ].
rewrite Nat.mul_1_r.
rewrite <- Nat.pow_add_r.
replace (n - i - j - 2 + S j) with (n - i - 1) by flia Hin.
unfold NQsub.
rewrite NQadd_assoc; f_equal.
rewrite NQadd_opp_r.
destruct j.
-rewrite Nat.pow_0_r, NQsub_diag, NQadd_0_l, Nat.pow_1_r.
 rewrite <- NQpair_add_l.
 rewrite Nat.sub_add; [ | easy ].
 now apply NQpair_diag.
-rewrite <- NQadd_assoc.
 rewrite NQadd_pair; [ | pauto | pauto ].
 rewrite Nat.mul_comm, Nat.mul_sub_distr_l.
 rewrite Nat.sub_add; [ | now apply Nat.mul_le_mono_l ].
 rewrite <- NQmul_pair; [ | pauto | pauto ].
 remember 1%NQ as one; rewrite NQpair_diag; [ | pauto ].
 subst one; rewrite NQmul_1_l.
 remember (S j) as x; rewrite Nat.pow_succ_r'; subst x.
 replace rad with (rad * 1) at 2 by apply Nat.mul_1_r.
 rewrite <- NQmul_pair; [ | easy | pauto ].
 remember 1%NQ as one; rewrite NQpair_diag; [ subst one | easy ].
 now rewrite NQmul_1_l, NQsub_add.
Qed.

Theorem A_ge_1_false_iff {r : radix} : ∀ i u k,
  let n := min_n i k in
  let s := n - i - 1 in
  fA_ge_1_ε u i k = false ↔ (NQfrac (A i n u) < 1 - 1 // rad ^ S k)%NQ.
Proof.
intros.
unfold fA_ge_1_ε.
fold n s.
set (t := rad ^ (s - S k)).
destruct (NQlt_le_dec (NQfrac (A i n u)) (1 - 1 // rad ^ S k)%NQ) as [H1| H1].
-easy.
-split; [ easy | intros H; now apply NQnle_gt in H ].
Qed.

Theorem A_ge_1_true_iff {r : radix} : ∀ i u k,
  let n := min_n i k in
  let s := n - i - 1 in
  fA_ge_1_ε u i k = true ↔ (NQfrac (A i n u) ≥ 1 - 1 // rad ^ S k)%NQ.
Proof.
intros.
unfold fA_ge_1_ε.
fold n s.
set (t := rad ^ (s - S k)).
destruct (NQlt_le_dec (NQfrac (A i n u)) (1 - 1 // rad ^ S k)%NQ) as [H1| H1].
-split; [ easy | intros H; now apply NQnle_gt in H ].
-easy.
Qed.

(*
Theorem when_99000_le_uuu00 {r : radix} : ∀ u i j k n,
  (∀ k, u (S i + k) < rad)
  → (rad ^ S j - 1) * rad ^ (n - i - 1 - S j) ≤ nA i n u
  → S j ≤ n - i - 1
  → i + 1 ≤ k ≤ i + j + 1
  → u k = rad - 1.
Proof.
intros * Hu HnA Hj Hk.
apply Nat.mul_le_mono_pos_r with (p := rad ^ S j) in HnA.
2: apply Nat.neq_0_lt_0; pauto.
rewrite <- Nat.mul_assoc in HnA.
rewrite <- Nat.pow_add_r in HnA.
rewrite Nat.sub_add in HnA; [ | easy ].
remember (n - i - 1) as s eqn:Hs.
assert (Hsz : rad ^ s ≠ 0) by (subst s; pauto).
apply Nat.div_le_mono with (c := rad ^ s) in HnA; [ | easy ].
rewrite Nat.div_mul in HnA; [ | easy ].
assert (H : nA i n u * rad ^ S j / rad ^ s = nA i (i + j + 2) u). {
(**)
  replace s with (s - S j + S j) by flia Hj.
  rewrite Nat.pow_add_r.
  rewrite Nat.div_mul_cancel_r; [ | pauto | pauto ].
  replace (s - S j) with (n - i - j - 2) by flia Hs.
  unfold nA at 1.
  rewrite summation_split with (e := i + j + 1); [ | flia Hs Hj ].
  cbn; unfold nA.
  replace (i + j + 2 - 1) with (i + j + 1) by flia.
  rewrite summation_eq_compat with
      (h := λ k, u k * rad ^ (i + j + 1 - k) * rad ^ (n - i - j - 2)).
  -rewrite <- summation_mul_distr_r; cbn.
   rewrite Nat.add_comm.
   rewrite Nat.div_add; [ | pauto ].
   rewrite Nat.div_small; [ easy | ].
   remember (n - i - j - 2) as m eqn:Hm.
   symmetry in Hm.
   destruct m.
   +rewrite summation_empty; [ | flia Hj Hm ].
    now apply Nat_pow_ge_1.
   +rewrite power_summation; [ | easy ].
    rewrite summation_mul_distr_l; cbn.
    rewrite summation_shift; [ | flia Hm ].
    replace (n - 1 - S (i + j + 1)) with m by flia Hm.
    apply -> Nat.succ_le_mono.
    rewrite summation_rtl.
    rewrite summation_eq_compat with
       (h := λ k, u (S (i + j + 1 + m - k)) * rad ^ k).
    *apply (@summation_le_compat nat_ord_ring_def).
     intros p Hp; cbn; unfold Nat.le.
     apply Nat.mul_le_mono_r.
     specialize (Hu (j + 1 + m - p)); cbn in Hu.
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
 remember (S j) as sj; cbn in HnA; subst sj.
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
   apply (@summation_le_compat nat_ord_ring_def); cbn; unfold Nat.le.
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
    remember (S j) as sj; cbn in HnA; subst sj.
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
     apply (@summation_le_compat nat_ord_ring_def); cbn; unfold Nat.le.
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
*)

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

Theorem A_eq_compat {r : radix} : ∀ i n u v,
  (∀ j, i < j < n → u j = v j)
  → A i n u = A i n v.
Proof.
intros * Hfg *.
unfold A.
apply summation_eq_compat.
intros j Hj; f_equal.
apply Hfg; flia Hj.
Qed.

Theorem A_ge_1_eq_compat {r : radix} : ∀ i f g,
  (∀ i, f i = g i) → ∀ k, fA_ge_1_ε f i k = fA_ge_1_ε g i k.
Proof.
intros * Hfg *.
unfold fA_ge_1_ε.
now erewrite A_eq_compat.
Qed.

Theorem prop_carr_eq_compat {r : radix} : ∀ f g,
  (∀ i, f i = g i) → ∀ i,
  prop_carr f i = prop_carr g i.
Proof.
intros * Hfg *.
unfold prop_carr.
apply digit_eq_eq; cbn.
unfold carry.
rewrite Hfg.
destruct (LPO_fst (fA_ge_1_ε f i)) as [Hf| Hf].
-destruct (LPO_fst (fA_ge_1_ε g i)) as [Hg| Hg].
 +rewrite (A_eq_compat _ _ _ g); [ easy | intros; apply Hfg ].
 +exfalso.
  destruct Hg as (k & Hjk & H).
  specialize (Hf k).
  erewrite A_ge_1_eq_compat in Hf; [ | easy ].
  now rewrite H in Hf.
-destruct (LPO_fst (fA_ge_1_ε g i)) as [Hg| Hg].
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
   now apply A_eq_compat.
  *specialize (Hjk _ Hkl).
   erewrite A_ge_1_eq_compat in Hjk; [ | easy ].
   now rewrite Hl in Hjk.
Qed.

Theorem freal_add_series_le_twice_pred {r : radix} : ∀ x y i,
  (x ⊕ y)%F i ≤ 2 * (rad - 1).
Proof.
intros *.
unfold "⊕".
replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
apply Nat.add_le_mono.
apply digit_le_pred_radix.
apply digit_le_pred_radix.
Qed.

Theorem A_upper_bound_for_add {r : radix} (rg := nat_ord_ring) : ∀ u i n,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → (A i n u ≤ 2 * (1 - 1 // rad ^ (n - i - 1)))%NQ.
Proof.
intros * Hur.
specialize radix_ge_2 as Hr.
destruct (lt_dec (n - 1) (i + 1)) as [Hin| Hin].
-unfold A.
 rewrite summation_empty; [ | easy ].
 remember (rad ^ (n - i - 1)) as s eqn:Hs.
 change (0 ≤ 2 * (1 - 1 // s))%NQ.
 rewrite <- (NQmul_0_r 2%NQ).
 apply NQmul_le_mono_nonneg_l; [ easy | ].
 apply (NQadd_le_r _ _ (1 // s)).
 rewrite NQadd_0_l, NQsub_add.
 destruct s. {
   symmetry in Hs.
   now apply Nat.pow_nonzero in Hs.
 }
 apply NQle_pair; [ easy | easy | ].
 apply Nat.mul_le_mono_nonneg_r; [ apply Nat.le_0_1 | flia ].
-apply Nat.nlt_ge in Hin.
 remember (n - i - 1) as s eqn:Hs.
 destruct s; [ flia Hin Hs | ].
 rewrite NQpower_summation_inv; [ | flia Hr ].
 unfold A.
 rewrite summation_shift; [ | easy ].
 replace (n - 1 - (i + 1)) with s by flia Hs.
 do 2 rewrite summation_mul_distr_l.
 apply summation_le_compat.
 intros j Hj.
 replace (i + 1 + j - i) with (S j) by flia.
 apply (NQle_trans _ ((2 * (rad - 1)) // (rad ^ S j))).
 +apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_comm, Nat.add_shuffle0.
  apply Nat.mul_le_mono_l, Hur.
 +rewrite NQmul_assoc.
  rewrite NQsub_pair_pos; [ | easy | easy | now apply Nat.mul_le_mono_l].
  do 2 rewrite Nat.mul_1_l.
  rewrite NQmul_pair; [ | easy | easy ].
  rewrite Nat.mul_1_l.
  rewrite NQmul_pair; [ | easy | pauto ].
  rewrite Nat.mul_1_r.
  apply NQle_refl.
Qed.

Theorem A_upper_bound_for_add_3 {r : radix} : ∀ u i n,
  (∀ k, u (i + k + 2) ≤ 2 * (rad - 1))
  → u (i + 1) < rad - 2
  → i + 2 ≤ n - 1
  → (A i n u < 1 - 1 // rad)%NQ.
Proof.
intros * Hur H1 His.
specialize radix_ge_2 as Hr.
rewrite A_split_first; [ | flia His ].
remember (n - i - 2) as s eqn:Hs.
apply (NQle_lt_trans _ ((rad - 3) // rad + 2 // rad * (1 - 1 // rad ^ s))%NQ).
-apply NQadd_le_mono.
 +apply NQle_pair; [ easy | easy | ].
  rewrite Nat.mul_comm, <- Nat.add_1_r.
  apply Nat.mul_le_mono_pos_l; [ easy | flia H1 ].
 +destruct s; [ flia Hs His | ].
  rewrite NQpower_summation_inv; [ | flia Hr ].
  rewrite NQsub_pair_pos; [ | easy | easy | now apply Nat.mul_le_mono_l ].
  do 2 rewrite Nat.mul_1_l.
  rewrite NQmul_assoc, summation_mul_distr_l.
  unfold A.
  rewrite summation_shift; [ | flia His ].
  replace (n - 1 - (S i + 1)) with s by flia Hs.
  rewrite NQmul_pair; [ | easy | easy ].
  rewrite summation_mul_distr_r.
  apply (@summation_le_compat NQ_ord_ring_def).
  intros j Hj.
  remember 2 as x; remember 1 as y; cbn; subst x y.
  replace (i + 1 + j - i) with (S j) by flia.
  replace (S (i + 1 + j)) with (i + j + 2) by flia.
  rewrite NQmul_pair; [ | pauto | easy ].
  rewrite NQmul_pair; [ | | pauto ]; cycle 1. {
    now destruct rad.
  }
  do 2 rewrite Nat.mul_1_r.
  rewrite <- Nat.mul_assoc, <- Nat.pow_succ_r', Nat.mul_comm.
  rewrite <- Nat.pow_succ_r'.
  apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_l, Hur.
-rewrite NQmul_sub_distr_l, NQmul_1_r.
 rewrite NQadd_sub_assoc, <- NQpair_add_l.
 replace (rad - 3 + 2) with (rad - 1) by flia H1.
 rewrite NQsub_pair_pos; [ | easy | easy | now apply Nat.mul_le_mono_l ].
 do 2 rewrite Nat.mul_1_l.
 rewrite NQmul_pair; [ | easy | pauto ].
 rewrite Nat.mul_1_r, <- Nat.pow_succ_r'.
 apply NQsub_lt.
 replace 0%NQ with (0 // 1)%NQ by easy.
 apply NQlt_pair; [ easy | pauto | ].
 apply Nat.lt_0_2.
Qed.

Theorem A_upper_bound_for_add_4 {r : radix} : ∀ u i j n,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → u (i + 1) = rad - 1
  → (∀ k : nat, k < j → u (i + k + 1) = rad - 1)
  → u (i + j + 1) < rad - 2
  → i + j + 2 ≤ n - 1
  → (A i n u < 1 - 1 // rad ^ (j + 2))%NQ.
Proof.
intros * Hur H1 H2 H3 Hin.
specialize radix_ge_2 as Hr.
rewrite A_split with (e := i + j + 2); [ | flia Hin ].
replace (i + j + 2 - i - 1) with (j + 1) by flia.
remember (i + j + 2) as k eqn:Hk.
move k before j.
rewrite NQsub_pair_pos; [ | easy | pauto | ]; cycle 1. {
  apply Nat.mul_le_mono_l, Nat.neq_0_lt_0; pauto.
}
do 2 rewrite Nat.mul_1_l.
replace (rad ^ (j + 2) - 1) with
  ((rad ^ (j + 1) - 3) * rad + (3 * rad - 1)); cycle 1. {
  rewrite Nat.mul_sub_distr_r.
  rewrite Nat.add_sub_assoc; cycle 1. {
    apply (Nat.le_trans _ (3 * 1)); [ flia | ].
    apply Nat.mul_le_mono_l, Nat.neq_0_lt_0; pauto.
  }
  destruct j.
  -rewrite Nat.add_0_r in H3; flia H1 H3.
  -replace (S j + 1) with (S (S j)) by flia.
   rewrite Nat.sub_add; cycle 1. {
     apply Nat.mul_le_mono_r; cbn.
     apply (Nat.le_trans _ (2 * (2 * 1))); [ flia | ].
     apply Nat.mul_le_mono; [ easy | ].
     apply Nat.mul_le_mono; [ easy | ].
     apply Nat.neq_0_lt_0; pauto.
   }
   rewrite Nat.mul_comm, <- Nat.pow_succ_r'.
   now replace (S j + 2) with (S (S (S j))) by flia.
}
rewrite NQpair_add_l.
apply NQadd_le_lt_mono.
-rewrite A_split_last; [ | flia Hk ].
 replace (k - 1) with (i + j + 1) by flia Hk.
 rewrite Nat.pow_add_r, Nat.pow_1_r.
 replace (rad ^ j) with (rad ^ j - 1 + 1); cycle 1. {
   rewrite Nat.sub_add; [ easy | ].
   apply Nat.neq_0_lt_0; pauto.
 }
 rewrite Nat.mul_add_distr_r, Nat.mul_1_l.
 rewrite <- Nat.add_sub_assoc; [ | flia H3 ].
 rewrite Nat.mul_add_distr_r.
 rewrite NQpair_add_l.
 destruct j.
 +rewrite Nat.add_0_r in H3; flia H1 H3.
 +apply NQadd_le_mono.
  *rewrite Nat.pow_add_r.
   rewrite <- Nat.mul_assoc, <- NQmul_pair; [ | pauto | pauto ].
   replace (rad * rad) with (rad ^ 2) by (cbn; flia).
   rewrite NQpair_diag; [ | pauto ].
   rewrite NQmul_1_r, NQpair_sub_l; [ | apply Nat.neq_0_lt_0; pauto ].
   rewrite NQpair_diag; [ | pauto ].
   replace (S j) with (i + S j + 1 - i - 1) at 2 by flia.
   apply A_dig_seq_ub; [ | flia ].
   intros p Hp.
   replace p with (i + (p - i - 1) + 1) by flia Hp.
   rewrite H2; [ flia Hr | flia Hp ].
  *replace (S j + 2) with (k - i - 1 + 1) by flia Hk.
   rewrite Nat.pow_add_r, Nat.pow_1_r.
   rewrite <- NQmul_pair; [ | pauto | pauto ].
   rewrite NQpair_diag, NQmul_1_r; [ | pauto ].
   apply NQle_pair; [ pauto | pauto | ].
   rewrite Nat.mul_comm; apply Nat.mul_le_mono_l.
   flia H3.
-replace (j + 2) with (1 + (j + 1)) by flia.
 remember (j + 1) as jj; rewrite Nat.pow_add_r; subst jj.
 rewrite Nat.pow_1_r.
 apply (NQmul_lt_mono_pos_r (rad ^ (j + 1) // 1)%NQ). {
   replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | pauto | ].
   cbn; rewrite Nat.add_0_r.
   apply Nat.neq_0_lt_0; pauto.
 }
 rewrite <- NQmul_assoc.
 rewrite NQmul_pair; [ | pauto | easy ].
 rewrite Nat.mul_1_l, Nat.mul_1_r.
 rewrite NQpair_diag; [ rewrite NQmul_1_r | pauto ].
 rewrite NQmul_pair; [ | rewrite <- Nat.pow_succ_r'; pauto | easy ].
 rewrite Nat.mul_1_r.
 rewrite <- NQmul_pair; [ | easy | pauto ].
 rewrite NQpair_diag; [ | pauto ].
 rewrite NQmul_1_r.
 eapply NQle_lt_trans.
 +apply A_upper_bound_for_add.
  intros p; subst k.
  replace (i + j + 2 - 1 + p + 1) with (i + (j + 1 + p) + 1) by flia.
  apply Hur.
 +replace (n - (k - 1) - 1) with (n - k) by flia Hk.
  rewrite NQmul_sub_distr_l, NQmul_1_r.
  eapply NQlt_trans; [ now apply NQsub_lt | ].
  rewrite NQpair_sub_l; cycle 1. {
    apply (Nat.le_trans _ (3 * 1)); [ flia | ].
    apply Nat.mul_le_mono_l, Nat.neq_0_lt_0; pauto.
  }
  replace rad with (1 * rad) at 2 by flia.
  rewrite <- NQmul_pair; [ | easy | easy ].
  rewrite NQpair_diag, NQmul_1_r; [ | easy ].
  rewrite NQsub_pair_pos; [ | easy | easy | flia Hr ].
  do 2 rewrite Nat.mul_1_l.
  apply NQlt_pair; [ easy | easy | ].
  rewrite Nat.mul_1_l; flia Hr.
Qed.

Theorem A_upper_bound_for_add_5 {r : radix} : ∀ u i k n,
  (∀ k, u (i + k + 2) ≤ 2 * (rad - 1))
  → u (i + 1) = rad - 2
  → u (i + k + 2) < 2 * (rad - 1)
  → i + k + 3 ≤ n - 1
  → (A i n u < (1 - 1 // rad ^ (k + 2)))%NQ.
Proof.
intros * Hur Hui H2 Hin.
remember (n - i - 1) as s eqn:Hs.
specialize radix_ge_2 as Hr.
rewrite A_split with (e := i + k + 2); [ | flia Hin ].
remember (i + k + 2) as j eqn:Hj.
move j before i.
replace (1 - 1 // rad ^ (k + 2))%NQ with
   ((rad ^ (k + 1) - 2) // rad ^ (k + 1) +
    (2 * rad - 1) // rad ^ (k + 2))%NQ; cycle 1. {
  remember ((rad ^ (k + 1) - 2) // rad ^ (k + 1))%NQ as x.
  replace x with (x * 1)%NQ by apply NQmul_1_r.
  replace 1%NQ with (rad ^ 1 // rad ^ 1)%NQ at 1 by (apply NQpair_diag; pauto).
  subst x.
  rewrite NQmul_pair; [ | pauto | pauto ].
  rewrite <- Nat.pow_add_r.
  replace (k + 1 + 1) with (k + 2) by flia.
  rewrite <- NQpair_add_l.
  rewrite Nat.pow_1_r, Nat.mul_sub_distr_r.
  rewrite Nat.add_sub_assoc; cycle 1. {
    apply (Nat.le_trans _ (2 * 1)); [ flia | ].
    apply Nat.mul_le_mono_pos_l; [ flia | easy ].
  }
  rewrite Nat.sub_add; cycle 1. {
    apply Nat.mul_le_mono_pos_r; [ easy | ].
    rewrite Nat.add_1_r; cbn.
    replace 2 with (2 * 1) by easy.
    apply Nat.mul_le_mono; [ easy | apply Nat.neq_0_lt_0; pauto ].
  }
  rewrite NQsub_pair_pos; [ | easy | pauto | ]; cycle 1. {
    apply Nat.mul_le_mono_pos_l; [ flia | apply Nat.neq_0_lt_0; pauto ].
  }
  rewrite Nat.mul_1_l, Nat.mul_1_r.
  f_equal; f_equal; rewrite Nat.mul_comm.
  replace (k + 2) with (S (k + 1)); [ easy | flia ].
}
apply NQadd_le_lt_mono.
-replace (rad ^ (k + 1) - 2) with
     ((rad - 2) * rad ^ k + 2 * (rad ^ k - 1)); cycle 1. {
   rewrite Nat.mul_sub_distr_r.
   replace rad with (rad ^ 1) at 1 by apply Nat.pow_1_r.
   rewrite <- Nat.pow_add_r.
   replace (1 + k) with (k + 1) by flia.
   rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   rewrite Nat.add_sub_assoc.
   -f_equal.
    rewrite Nat.sub_add; [ easy | ].
    replace (k + 1) with (1 + k) by flia.
    remember 2 as x; simpl; subst x.
    now apply Nat.mul_le_mono_r.
   -replace 2 with (2 * 1) at 1 by flia.
    apply Nat.mul_le_mono_l.
    apply Nat.neq_0_lt_0; pauto.
 }
 rewrite A_split_first; [ | flia Hj ].
 rewrite NQpair_add_l.
 apply NQadd_le_mono.
 +rewrite Nat.add_comm; cbn.
  rewrite <- NQmul_pair; [ | pauto | pauto ].
  rewrite NQpair_diag; [ | pauto ].
  rewrite NQmul_1_r.
  apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_pos_l; [ easy | ].
  now rewrite <- Nat.add_1_r, Hui.
 +rewrite Nat.add_1_r, Nat.pow_succ_r; [ | apply Nat.le_0_l ].
  replace 2 with (1 * 2) by easy.
  rewrite <- Nat.mul_assoc.
  rewrite <- NQmul_pair; [ | pauto | pauto ].
  rewrite NQmul_comm.
  apply NQmul_le_mono_nonneg_l. {
    replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQle_pair; [ easy | pauto | apply Nat.le_0_l ].
  }
  rewrite Nat.mul_sub_distr_l.
  rewrite NQpair_sub_l; cycle 1. {
    apply Nat.mul_le_mono_pos_l; [ pauto | apply Nat.neq_0_lt_0; pauto ].
  }
  rewrite Nat.mul_1_r.
  replace (rad ^ k) with (1 * rad ^ k) at 2 by apply Nat.mul_1_l.
  rewrite <- NQmul_pair; [ | easy | pauto ].
  rewrite NQpair_diag, NQmul_1_r; [ | pauto ].
  replace (2 - 2 // rad ^ k)%NQ with (2 * (1 - 1 // rad ^ k))%NQ; cycle 1. {
    rewrite NQmul_sub_distr_l, NQmul_1_r.
    f_equal; f_equal.
    rewrite NQmul_pair; [ | easy | pauto ].
    now rewrite Nat.mul_1_l.
  }
  replace k with (j - S i - 1) by flia Hj.
  apply A_upper_bound_for_add.
  intros m.
  replace (S i + m + 1) with (i + m + 2) by flia.
  apply Hur.
-replace (j - i - 1) with (k + 1) by flia Hj.
 rewrite A_split_first; [ | flia Hj Hin ].
 replace (S (j - 1)) with j by flia Hj.
 replace (2 * rad - 1) with (2 * rad - 3 + 2) by flia Hr.
 rewrite NQpair_add_l.
 rewrite NQmul_add_distr_r.
 apply NQadd_le_lt_mono.
 +rewrite NQmul_pair; [ | easy | pauto ].
  rewrite Nat.mul_1_r, <- Nat.pow_succ_r; [ | flia ].
  replace (S (k + 1)) with (k + 2) by pauto.
  apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_comm.
  apply Nat.mul_le_mono_l; flia H2.
 +rewrite <- NQmul_assoc.
  rewrite NQmul_pair; [ | pauto | pauto ].
  rewrite Nat.mul_1_r, <- Nat.pow_succ_r; [ | flia ].
  replace (S (k + 1)) with (k + 2) by pauto.
  replace 2 with (2 * 1) at 2 by easy.
  replace (rad ^ (k + 2)) with (1 * rad ^ (k + 2)) at 2 by flia.
  rewrite <- NQmul_pair; [ | easy | pauto ].
  apply NQmul_lt_mono_pos_r.
  *replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | pauto | pauto ].
  *eapply NQle_lt_trans.
  --apply A_upper_bound_for_add.
    intros l.
    replace (j + l + 1) with (i + (k + l + 1) + 2) by flia Hj.
    apply Hur.
  --rewrite NQmul_sub_distr_l, NQmul_1_r.
    apply NQsub_lt.
    rewrite NQmul_pair; [ | easy | pauto ].
    rewrite Nat.mul_1_r, Nat.mul_1_l.
    replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQlt_pair; [ easy | pauto | flia ].
Qed.

Theorem A_ge_1_add_first_ge {r : radix} : ∀ u i,
  (∀ k, u (i + k + 2) ≤ 2 * (rad - 1))
  → fA_ge_1_ε u i 0 = true
  → u (i + 1) ≥ rad - 2.
Proof.
intros * Hur Hu.
specialize radix_ge_2 as Hr.
revert Hu.
apply Decidable.contrapositive; [ apply Nat.le_decidable | ].
intros H1; apply Nat.nle_gt in H1.
apply Bool.not_true_iff_false.
apply A_ge_1_false_iff.
unfold min_n.
rewrite Nat.add_0_r, Nat.pow_1_r.
remember (rad * (i + 3)) as n eqn:Hn.
remember (A i n u) as a eqn:Ha; symmetry in Ha.
unfold NQfrac.
assert (Hin : i + 2 ≤ n - 1). {
  rewrite Hn.
  specialize radix_ne_0 as H.
  destruct rad; [ easy | simpl; flia ].
}
specialize (A_upper_bound_for_add_3 u i n Hur H1 Hin) as H2.
rewrite Ha in H2.
replace a with (NQnum a // NQden a)%NQ in H2; cycle 1. {
  symmetry; apply NQnum_den.
  rewrite <- Ha; apply A_ge_0.
}
eapply NQle_lt_trans; [ | apply H2 ].
apply NQle_pair; [ pauto | pauto | ].
rewrite Nat.mul_comm.
apply Nat.mul_le_mono_l.
apply Nat.mod_le; pauto.
Qed.

Theorem A_ge_1_add_ge {r : radix} : ∀ u i j,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → (∀ k : nat, fA_ge_1_ε u i k = true)
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
specialize (A_upper_bound_for_add_4 u i j n Hur H1 H3 H4 Hin) as H5.
eapply NQle_lt_trans; [ | apply H5 ].
apply NQfrac_le, A_ge_0.
Qed.

Theorem A_num_den {r : radix} (rg := nat_ord_ring) : ∀ i n u,
  A i n u =
  ((Σ (j = i + 1, n - 1), (u j * rad ^ (n - 1 - j))%nat) //
   rad ^ (n - i - 1))%NQ.
Proof.
intros.
rewrite NQsummation_pair_distr_r.
apply summation_eq_compat.
intros j Hj.
replace (n - i - 1) with (j - i + (n - 1 - j)) by flia Hj.
rewrite Nat.pow_add_r.
rewrite <- NQmul_pair; [ | pauto | pauto ].
rewrite NQpair_diag; [ | pauto ].
now rewrite NQmul_1_r.
Qed.

Theorem A_ge_1_add_first_ge_rad {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → fA_ge_1_ε u i 0 = true
  → u (i + 1) ≥ rad
  → u (i + 1) = 2 * (rad - 1).
Proof.
intros * Hur Hu Hui.
specialize radix_ge_2 as Hr.
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
assert (H2 : NQfrac (A i n u) = NQfrac (A i n v)). {
  unfold NQfrac.
  do 2 rewrite A_num_den.
  remember (Σ (j = i + 1, n - 1), (u j * rad ^ (n - 1 - j))%nat) as x eqn:Hx.
  remember (Σ (j = i + 1, n - 1), (v j * rad ^ (n - 1 - j))%nat) as y eqn:Hy.
  move y before x.
  assert (Hxy : y = x - rad ^ (n - i - 1)). {
    rewrite summation_split_first in Hx, Hy; [ | flia Hin | flia Hin ].
    unfold v at 1 in Hy.
    destruct (Nat.eq_dec (i + 1) (i + 1)) as [H1| H1]; [ clear H1 | easy ].
    rewrite Nat.mul_sub_distr_r in Hy.
    replace rad with (rad ^ 1) in Hy at 2 by now apply Nat.pow_1_r.
    rewrite <- Nat.pow_add_r in Hy.
    replace (1 + (n - 1 - (i + 1))) with (n - i - 1) in Hy by flia Hin.
    rewrite Hx.
    rewrite Nat.add_sub_swap; cycle 1. {
      replace (n - i - 1) with (1 + (n - i - 2)) by flia Hin.
      replace (n - 1 - (i + 1)) with (n - i - 2) by flia.
      rewrite Nat.pow_add_r, Nat.pow_1_r.
      now apply Nat.mul_le_mono_r.
    }
    rewrite Hy.
    remember summation as f; cbn; subst f.
    f_equal.
    apply summation_eq_compat.
    intros j Hj; f_equal.
    unfold v.
    destruct (Nat.eq_dec j (i + 1)) as [H| H]; [ flia Hj H | easy ].
  }
  rewrite Hxy.
  remember (n - i - 1) as s1 eqn:Hs1.
  do 2 rewrite NQnum_pair.
  do 2 rewrite NQden_pair.
  rewrite Nat.max_r; [ | apply Nat.neq_0_lt_0; pauto ].
  remember (rad ^ s1) as z eqn:Hz.
  assert (Hzx : z ≤ x). {
    rewrite Hx.
    rewrite summation_split_first; [ | flia Hin ].
    rewrite Hz.
    replace (n - 1 - (i + 1)) with (s1 - 1) by flia Hs1.
    replace s1 with (1 + (s1 - 1)) at 1 by flia Hs1 Hin.
    rewrite Nat.pow_add_r, Nat.pow_1_r.
    apply le_plus_trans.
    apply Nat.mul_le_mono_pos_r; [ | easy ].
    apply Nat.neq_0_lt_0; pauto.
  }
  rewrite Nat.max_r.
  -rewrite Nat.max_r.
   +rewrite Nat_gcd_sub_diag_l; [ | easy ].
    rewrite <- Nat_ggcd.ggcd_fst_snd.
    rewrite <- Nat_ggcd.ggcd_snd_snd.
    rewrite <- Nat_ggcd.ggcd_gcd.
    remember (Nat_ggcd.ggcd x z) as g eqn:Hg.
    destruct g as (g, (aa, bb)); cbn.
    specialize (Nat_ggcd.ggcd_correct_divisors x z) as H.
    rewrite <- Hg in H.
    destruct H as (Hxg, Hzg).
    rewrite Hxg, Hzg.
    rewrite <- Nat.mul_sub_distr_l.
    rewrite Nat.mul_comm.
    assert (Hgz : g ≠ 0). {
      destruct g; [ | flia ].
      cbn in Hxg; move Hxg at top; subst x.
      symmetry in Hx.
      apply eq_nat_summation_0 with (i := i + 1) in Hx.
      apply Nat.eq_mul_0 in Hx.
      destruct Hx as [Hx| Hx].
      flia Hui Hx Hr.
      now apply Nat.pow_nonzero in Hx.
      flia Hin.
    }
    rewrite Nat.div_mul; [ | easy ].
    replace aa with ((aa - bb) + bb) at 1.
    *rewrite Nat_mod_add_same_r; [ easy | ].
     intros H; subst bb; rewrite Nat.mul_0_r in Hzg; subst z.
     now apply Nat.pow_nonzero in Hzg.
    *apply Nat.sub_add.
     eapply (Nat.mul_le_mono_pos_l _ _ g); [ flia Hgz | ].
     now rewrite <- Hxg, <- Hzg.
   +apply Nat.neq_0_lt_0.
    intros H; apply Nat.div_small_iff in H.
    *apply Nat.nle_gt in H; apply H, Nat_gcd_le_r.
     clear H; intros H; rewrite H in Hz.
     now symmetry in Hz; apply Nat.pow_nonzero in Hz.
    *intros H1.
     apply Nat.gcd_eq_0_r in H1.
     rewrite H1 in Hz.
     now symmetry in Hz; apply Nat.pow_nonzero in Hz.
  -apply Nat.neq_0_lt_0.
   intros H; apply Nat.div_small_iff in H.
   +apply Nat.nle_gt in H; apply H, Nat_gcd_le_r.
    clear H; intros H; rewrite H in Hz.
    now symmetry in Hz; apply Nat.pow_nonzero in Hz.
   +intros H1.
    apply Nat.gcd_eq_0_r in H1.
    rewrite H1 in Hz.
    now symmetry in Hz; apply Nat.pow_nonzero in Hz.
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
assert (H4 : fA_ge_1_ε v i 0 = true). {
  apply A_ge_1_true_iff.
  unfold min_n.
  rewrite Nat.add_0_r, Nat.pow_1_r.
  now rewrite <- Hn.
}
specialize (A_ge_1_add_first_ge v i H3 H4) as H5.
unfold v in H5.
destruct (Nat.eq_dec (i + 1) (i + 1)) as [H6| ]; [ | easy ].
apply Nat.le_antisymm; [ | flia Hui H5 ].
now specialize (Hur 0); rewrite Nat.add_0_r in Hur.
Qed.

Theorem A_ge_1_add_first {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → fA_ge_1_ε u i 0 = true
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
  → ∀ k, fA_ge_1_ε u i (k + 1) = true
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
specialize (A_upper_bound_for_add_5 u i k n Hur Hui H2 Hin) as H3.
eapply NQle_lt_trans; [ | apply H3 ].
apply NQfrac_le.
apply A_ge_0.
Qed.

Theorem A_lower_bound_when_999_gt_9 {r : radix} : ∀ u i k n,
  i + k + 3 ≤ n - 1
  → (∀ j, j < k → u (i + j + 1) = rad - 1)
  → rad ≤ u (i + k + 1)
  → (1 ≤ A i n u)%NQ.
Proof.
intros * H6 H3 H5.
specialize radix_ge_2 as Hr.
remember (n - i - 1) as s eqn:Hs.
enough (H : (1 ≤ A i (i + k + 2) u)%NQ). {
  rewrite A_split with (e := i + k + 2); [ | flia H6 ].
  eapply NQle_trans; [ apply H | ].
  apply NQle_add_r.
  replace 0%NQ with (0 // 1 * A (i + k + 2 - 1) n u)%NQ by easy.
  rewrite NQmul_comm.
  apply NQmul_le_mono_nonneg_l; [ apply A_ge_0 | ].
  apply NQle_pair; [ easy | pauto | flia ].
}
rewrite A_split_last; [ | flia Hs ].
replace (i + k + 2 - 1) with (i + k + 1) by flia.
assert (HA : (A i (i + k + 1) u ≥ 1 - 1 // rad ^ k)%NQ). {
  destruct k; [ rewrite Nat.pow_0_r, NQsub_diag; apply A_ge_0 | ].
  unfold A.
  rewrite summation_shift; [ | flia H6 ].
  rewrite Nat.add_sub.
  replace (i + S k - (i + 1)) with k by flia.
  rewrite NQpower_summation_inv; [ | flia Hr ].
  rewrite summation_mul_distr_l.
  apply (@summation_le_compat NQ_ord_ring_def).
  unfold "≤"%Rg, "*"%Rg, NQ_ord_ring_def.
  intros j Hj.
  replace (i + 1 + j - i) with (j + 1) by flia.
  rewrite Nat.add_shuffle0.
  rewrite H3; [ | flia Hj ].
  rewrite NQmul_sub_distr_r, NQmul_1_l.
  rewrite NQmul_pair; [ | easy | pauto ].
  rewrite Nat.mul_1_l.
  rewrite NQpair_sub_l; [ | easy ].
  apply NQsub_le_mono.
  -apply NQle_pair; [ pauto | pauto | ].
   rewrite Nat.mul_1_l, Nat.add_1_r; cbn.
   now rewrite Nat.mul_comm.
  -rewrite Nat.pow_add_r, Nat.pow_1_r, Nat.mul_comm.
   apply NQle_refl.
}
replace (i + k + 2 - i - 1) with (k + 1) by flia.
apply NQle_trans with
  (y := (1 - 1 // rad ^ k + rad // rad ^ (k + 1))%NQ).
-rewrite Nat.add_1_r, Nat.pow_succ_r'.
 replace rad with (rad * 1) at 2 by flia.
 rewrite <- NQmul_pair; [ | easy | pauto ].
 remember 1%NQ as x; rewrite NQpair_diag; subst x; [ | easy ].
 rewrite NQmul_1_l, NQsub_add; apply NQle_refl.
-apply NQadd_le_mono; [ easy | ].
 apply NQle_pair; [ pauto | pauto | ].
 rewrite Nat.mul_comm.
 now apply Nat.mul_le_mono_l.
Qed.

Theorem A_le_aft_999 {r : radix} : ∀ u i k,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → (∀ j, j < k → u (i + j + 1) = rad - 1)
  → (A i (i + k + 2) u ≤ 1 + (rad - 2) // rad ^ S k)%NQ.
Proof.
intros * Hur H3.
specialize radix_ge_2 as Hr.
rewrite A_split_last; [ | flia ].
rewrite A_all_9; [ | intros l Hl; apply H3; flia Hl ].
replace (i + k + 2 - 1) with (i + k + 1) by flia.
replace (i + k + 1 - i - 1) with k by flia.
replace (i + k + 2 - i - 1) with (S k) by flia.
rewrite NQpair_sub_l; [ | easy ].
rewrite Nat.pow_succ_r'.
replace rad with (rad * 1) at 4 by flia.
rewrite <- NQmul_pair; [ | easy | pauto ].
remember 1%NQ as x.
rewrite NQpair_diag; [ | easy ].
rewrite NQmul_1_l; subst x.
rewrite <- Nat.pow_succ_r'.
destruct (le_dec (u (i + k + 1)) rad) as [H1| H1].
-rewrite <- NQsub_sub_distr.
 apply NQadd_le_mono_l.
 rewrite NQopp_sub_distr.
 rewrite NQadd_opp_l.
 apply NQsub_le_mono.
 +apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_1_r, Nat.pow_succ_r'.
  now apply Nat.mul_le_mono_r.
 +apply NQle_pair; [ pauto | pauto | ].
  rewrite Nat.mul_1_r, Nat.pow_succ_r'.
  now apply Nat.mul_le_mono_r.
-apply Nat.nle_gt in H1.
 unfold NQsub.
 rewrite <- NQadd_assoc.
 apply NQadd_le_mono_l.
 apply (NQadd_le_mono_l _ _ (1 // rad ^ k)).
 rewrite NQadd_assoc, NQadd_opp_r, NQsub_diag, NQadd_0_l.
 rewrite NQadd_assoc, <- NQpair_add_l.
 replace (1 + 1) with 2 by easy.
 rewrite NQadd_opp_r.
 rewrite NQsub_pair_pos; [ | pauto | pauto | ]; cycle 1. {
   rewrite Nat.mul_comm; apply Nat.mul_le_mono_l.
   rewrite Nat.pow_succ_r'.
   replace (rad ^ k) with (1 * rad ^ k) at 1 by flia.
   apply Nat.mul_le_mono_r; flia Hr.
 }
 replace (rad ^ k) with (1 * rad ^ k) at 1 by flia.
 rewrite Nat.mul_comm, Nat.pow_succ_r'.
 do 2 rewrite <- Nat.mul_sub_distr_r.
 setoid_rewrite Nat.mul_comm.
 rewrite <- Nat.pow_succ_r'.
 rewrite Nat.mul_assoc.
 rewrite <- NQmul_pair; [ | pauto | pauto ].
 rewrite NQpair_diag; [ | pauto ].
 rewrite NQmul_1_r.
 rewrite Nat.mul_comm, <- Nat.pow_succ_r'.
 apply NQle_pair; [ pauto | pauto | ].
 rewrite Nat.mul_comm.
 apply Nat.mul_le_mono_l, Hur.
Qed.

Theorem A_ge_1_add_9_eq {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → ∀ k, k ≠ 0
  → fA_ge_1_ε u i k = true
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
specialize (A_lower_bound_when_999_gt_9 u i k n H6 H3 H5) as H7.
specialize (A_upper_bound_for_add u i n Hur) as H8.
rewrite <- Hs in H8.
unfold NQfrac.
rewrite Nat_mod_less_small; cycle 1. {
  split.
  -rewrite NQnum_den in H7; [ | apply A_ge_0 ].
   apply NQle_pair in H7; [ | easy | pauto ].
   now do 2 rewrite Nat.mul_1_l in H7.
  -remember (A i n u) as x in H8.
   rewrite NQnum_den in Heqx; [ subst x | apply A_ge_0 ].
   rewrite NQsub_pair_pos in H8; [ | easy | pauto | ]; cycle 1. {
    apply Nat.mul_le_mono_l, Nat.neq_0_lt_0; pauto.
   }
   do 2 rewrite Nat.mul_1_l in H8.
   rewrite NQmul_pair in H8; [ | easy | pauto ].
   rewrite Nat.mul_1_l in H8.
   apply NQle_pair in H8; [ | pauto | pauto ].
   apply (Nat.mul_lt_mono_pos_r (rad ^ s)); [ apply Nat.neq_0_lt_0; pauto | ].
   eapply Nat.le_lt_trans; [ apply H8 | ].
   rewrite Nat.mul_comm, Nat.mul_shuffle0.
   rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   apply Nat.sub_lt.
   +rewrite <- Nat.mul_assoc.
    apply Nat.mul_le_mono_l.
    apply Nat_mul_le_pos_r, Nat.neq_0_lt_0; pauto.
   +replace 0 with (2 * 0) at 1 by easy.
    apply Nat.mul_lt_mono_pos_l; [ pauto | ].
    apply Nat.neq_0_lt_0, NQden_neq_0.
}
rewrite NQpair_sub_l; cycle 1. {
  rewrite NQnum_den in H7; [ | apply A_ge_0 ].
  apply NQle_pair in H7; [ | easy | pauto ].
  now do 2 rewrite Nat.mul_1_l in H7.
}
rewrite <- NQnum_den; [ | apply A_ge_0 ].
rewrite NQpair_diag; [ | pauto ].
apply (NQadd_lt_mono_r _ _ 1).
rewrite NQsub_add, <- NQadd_sub_swap.
replace (1 + 1)%NQ with 2%NQ by easy.
rewrite A_split with (e := i + k + 2); [ | flia H6 ].
remember (i + k + 2) as t eqn:Ht.
move t before s.
unfold min_n in Hn.
replace (i + k + 3) with (i + k + 2 + 1) in Hn, H6 by flia.
rewrite <- Ht in Hn, H6.
replace (i + k + 1) with (t - 1) in H5 by flia Ht.
replace (t - i - 1) with (S k) by flia Ht.
apply NQle_lt_trans with
  (y := (1 + (rad - 2) // rad ^ S k + A (t - 1) n u * 1 // rad ^ (S k))%NQ).
-apply NQadd_le_mono_r.
 now rewrite Ht; apply A_le_aft_999.
-specialize (A_upper_bound_for_add u (t - 1) n) as H1.
 assert (H : ∀ j, u (t - 1 + j + 1) ≤ 2 * (rad - 1)). {
   intros j.
   replace (t - 1 + j + 1) with (i + (k + j + 1) + 1) by flia Ht.
   apply Hur.
 }
 specialize (H1 H); clear H.
 replace (n - (t - 1) - 1) with (s - S k) in H1 by flia Hs Ht.
 apply NQle_lt_trans with
   (y :=
      ((1 + (rad - 2) // rad ^ S k +
       2 * (1 - 1 // rad ^ (s - S k)) * 1 // rad ^ S k))%NQ).
 +apply NQadd_le_mono_l.
  apply NQmul_le_mono_nonneg_r; [ | easy ].
  replace 0%NQ with (0 // 1)%NQ by easy.
  apply NQle_pair; [ easy | pauto | cbn; flia ].
 +rewrite <- NQmul_assoc, NQmul_sub_distr_r, NQmul_1_l.
  rewrite NQmul_pair; [ | pauto | pauto ].
  rewrite Nat.mul_1_l, <- Nat.pow_add_r.
  rewrite Nat.sub_add; [ | flia Hs H6 Ht ].
  rewrite NQmul_sub_distr_l.
  rewrite NQmul_pair; [ rewrite Nat.mul_1_l, Nat.mul_1_r | easy | pauto ].
  rewrite NQmul_pair; [ rewrite Nat.mul_1_l, Nat.mul_1_r | easy | pauto ].
  rewrite NQpair_sub_l; [ | easy ].
  do 2 rewrite NQadd_sub_assoc.
  rewrite NQsub_add.
  apply NQlt_le_trans with (y := (1 + rad // rad ^ S k)%NQ).
  *apply NQsub_lt.
   replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | pauto | cbn; flia ].
  *apply (NQadd_le_mono_r _ _ (1 // rad ^ S k)%NQ).
   rewrite NQsub_add.
   replace 2%NQ with (1 + 1)%NQ by easy.
   rewrite <- NQadd_assoc.
   apply NQadd_le_mono_l.
   rewrite <- NQpair_add_l.
   apply NQle_pair; [ pauto | easy | ].
   do 2 rewrite Nat.mul_1_r.
   rewrite Nat.add_1_r.
   clear - Hr Hk.
   destruct k; [ easy | clear Hk ].
   induction k.
  --destruct rad as [| rr]; [ easy | ].
    destruct rr; [ flia Hr | cbn; flia ].
  --eapply le_trans; [ apply IHk | ].
    remember (S (S k)) as x; cbn; subst x.
    replace (rad ^ S (S k)) with (1 * rad ^ S (S k)) at 1 by flia.
    apply Nat.mul_le_mono_r; flia Hr.
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
rewrite Nat.mod_mul_r in H1; try pauto.
replace (a * r ^ b₁ + b) with (b + a * r ^ b₁) in H1 by apply Nat.add_comm.
rewrite Nat.mod_add in H1; [ | pauto ].
rewrite Nat.mod_small in H1; [ | easy ].
rewrite Nat.div_add in H1; [ | pauto ].
rewrite Nat.div_small in H1; [ | easy ].
rewrite Nat.add_0_l in H1.
rewrite Nat.mod_small in H1; [ | easy ].
rewrite Nat.add_comm, Nat.mul_comm in H1.
now apply Nat.add_le_mono_l in H1.
Qed.

Theorem A_ge_1_add_all_true_999_8 {r : radix} : ∀ u i j,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, k < j → u (i + k + 1) = rad - 1)
  → u (i + j + 1) = rad - 2
  → (∀ k, fA_ge_1_ε u i k = true)
  → ∀ k, fA_ge_1_ε u (i + j) (k + 1) = true.
Proof.
intros * Hur H3 H4 Hu *.
specialize radix_ge_2 as Hr.
destruct (zerop j) as [| Hj]; [ subst j; rewrite Nat.add_0_r; apply Hu | ].
apply Nat.neq_0_lt_0 in Hj.
specialize (Hu (j + k + 1)) as H5.
apply A_ge_1_true_iff in H5.
apply A_ge_1_true_iff.
unfold min_n in H5 |-*.
replace (i + (j + k + 1) + 3) with (i + j + k + 4) in H5 by flia.
replace (i + j + (k + 1) + 3) with (i + j + k + 4) by flia.
remember (rad * (i + j + k + 4)) as n eqn:Hn.
move n before k.
assert (Hin : i + j + k + 2 ≤ n - 1). {
  rewrite Hn.
  destruct rad; [ easy | simpl; flia ].
}
remember (n - i - 1) as s eqn:Hs.
remember (j + k + 1) as t eqn:Ht.
move s before n; move t before s.
replace (S (k + 1)) with (k + 2) by flia.
rewrite (A_split (i + j + 1)) in H5; [ | flia Hin ].
rewrite Nat.add_sub in H5.
replace (i + j + 1 - i - 1) with j in H5 by flia.
replace (S t) with (j + (k + 2)) in H5 by flia Ht.
clear t Ht.
rewrite Nat.pow_add_r in H5.
assert (HA : (A i (i + j + 1) u = 1 - 1 // rad ^ j)%NQ). {
  replace j with ((i + j + 1) - i - 1) at 2 by flia.
  apply A_all_9.
  intros m Hm.
  apply H3; flia Hm.
}
rewrite HA in H5.
unfold NQsub in H5.
rewrite NQadd_add_swap in H5.
rewrite <- NQadd_assoc in H5.
replace (1 // rad ^ j)%NQ with (1 * 1 // rad ^ j)%NQ in H5 at 2; cycle 1. {
  apply NQmul_1_l.
}
rewrite NQadd_opp_r in H5.
rewrite <- NQmul_sub_distr_r in H5.
destruct (NQeq_dec (A (i + j) n u) 0) as [HAz| HAz].
-exfalso; apply NQnlt_ge in H5; apply H5; clear H5.
 unfold NQsub.
 rewrite HAz, NQadd_0_l, NQmul_opp_l, NQmul_1_l.
 rewrite NQadd_opp_r.
 rewrite NQsub_pair_pos; [ | easy | pauto | ]; cycle 1. {
   now apply Nat.mul_le_mono_l, Nat_pow_ge_1.
 }
 do 2 rewrite Nat.mul_1_l.
 rewrite NQfrac_pair.
 rewrite Nat.mod_small; cycle 1. {
   apply Nat.sub_lt; [ | pauto ].
   now apply Nat_pow_ge_1.
 }
 rewrite NQadd_opp_r.
 rewrite NQsub_pair_pos; [ | easy | | ]; cycle 1. {
   intros H; apply Nat.eq_mul_0 in H.
   now destruct H; apply Nat.pow_nonzero in H.
 } {
   remember (1 * 1) as x; rewrite Nat.mul_1_l; subst x.
   apply Nat.mul_le_mono; now apply Nat_pow_ge_1.
 }
 do 2 rewrite Nat.mul_1_l.
 apply NQlt_pair; [ pauto | | ]. {
   intros H; apply Nat.eq_mul_0 in H.
   now destruct H; apply Nat.pow_nonzero in H.
 }
 rewrite Nat.mul_comm.
 rewrite <- Nat.mul_assoc.
 apply Nat.mul_lt_mono_pos_l; [ apply Nat.neq_0_lt_0; pauto | ].
 rewrite Nat.mul_sub_distr_l, Nat.mul_1_r, Nat.mul_comm.
 apply Nat_sub_lt_mono_l.
 split.
 +apply (lt_le_trans _ 2); [ flia | ].
  rewrite Nat.add_comm; cbn.
  replace 2 with (2 * (1 * 1)) by easy.
  apply Nat.mul_le_mono; [ easy | ].
  apply Nat.mul_le_mono; [ easy | ].
  now apply Nat_pow_ge_1.
 +replace (rad ^ (k + 2)) with (1 * rad ^ (k + 2)) at 1 by flia.
  apply Nat.mul_le_mono_r.
  now apply Nat_pow_ge_1.
-destruct (NQlt_le_dec (A (i + j) n u) 1) as [HAn| HAp].
 +apply NQnlt_ge; intros H1.
  rewrite NQfrac_eq_when_lt_1 in H1; cycle 1. {
    split; [ apply A_ge_0 | easy ].
  }
  apply NQnlt_ge in H5; apply H5; clear H5.
  rewrite <- NQsub_opp_r, <- NQmul_opp_l.
  rewrite NQopp_sub_distr.
  rewrite NQadd_opp_l.
  rewrite NQfrac_eq_when_lt_1; cycle 1. {
    split.
    -apply NQle_0_sub.
     rewrite NQmul_sub_distr_r, NQmul_1_l.
     replace 1%NQ with (1 - 0)%NQ by easy.
     apply NQsub_le_mono.
     +apply NQle_pair; [ pauto | easy | ].
      now apply Nat.mul_le_mono_r, Nat_pow_ge_1.
     +rewrite <- (NQmul_0_l (1 // rad ^ j)%NQ).
      apply NQmul_le_mono_pos_r; [ | apply A_ge_0 ].
      replace 0%NQ with (0 // 1)%NQ by easy.
      apply NQlt_pair; [ easy | pauto | pauto ].
    -apply NQsub_lt.
     replace 0%NQ with (0 * 1 // rad ^ j)%NQ by easy.
     apply NQmul_lt_mono_pos_r.
     +replace 0%NQ with (0 // 1)%NQ by easy.
      apply NQlt_pair; [ easy | pauto | pauto ].
     +now apply NQlt_0_sub.
  }
  rewrite NQadd_opp_r.
  apply NQsub_lt_mono_l.
  apply (NQmul_lt_mono_pos_r (rad ^ j // 1)%NQ). {
    replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQlt_pair; [ easy | easy | cbn ].
    rewrite Nat.add_0_r; apply Nat.neq_0_lt_0; pauto.
  }
  rewrite <- NQmul_assoc.
  rewrite NQmul_inv_pair; [ | easy | pauto ].
  rewrite NQmul_1_r.
  rewrite NQmul_comm, NQmul_pair_den_num; [ | easy ].
  replace (rad ^ j) with (rad ^ j * 1) at 1 by flia.
  rewrite <- NQmul_pair; [ | pauto | pauto ].
  rewrite NQpair_diag; [ | pauto ].
  rewrite NQmul_1_l.
  now apply NQlt_add_lt_sub_l, NQlt_add_lt_sub_r.
 +exfalso; apply NQnlt_ge in HAp; apply HAp; clear HAp.
  rewrite A_split_first; [ | flia Hin ].
  rewrite <- Nat.add_1_r, H4.
  specialize (A_upper_bound_for_add u (i + j + 1) n) as H1.
  assert (H : ∀ k, u (i + j + 1 + k + 1) ≤ 2 * (rad - 1)). {
    intros m.
    replace (i + j + 1 + m) with (i + (j + 1 + m)) by flia.
    apply Hur.
  }
  specialize (H1 H); clear H.
  remember (i + j + 1) as t.
  eapply NQle_lt_trans.
  *apply NQadd_le_mono_l.
   apply NQmul_le_mono_pos_r; [ | apply H1 ].
   replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | pauto | pauto ].
  *replace (n - t - 1) with (s - S j) by flia Heqt Hs.
   rewrite <- (NQmul_pair_den_num _ 1); [ | easy ].
   rewrite <- NQmul_add_distr_r, NQmul_sub_distr_l, NQmul_1_r.
   apply (NQmul_lt_mono_pos_r (rad // 1)%NQ). {
     replace 0%NQ with (0 // 1)%NQ by easy.
     apply NQlt_pair; [ easy | pauto | flia Hr ].
   }
   rewrite NQmul_1_l, <- NQmul_assoc.
   rewrite NQmul_inv_pair; [ | easy | easy ].
   rewrite NQmul_1_r, NQadd_sub_assoc.
   rewrite NQpair_sub_l; [ | easy ].
   rewrite NQsub_add.
   apply NQsub_lt.
   rewrite NQmul_pair_den_num; [ | easy ].
   replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | pauto | cbn; flia ].
Qed.

Theorem A_ge_1_add_all_true_if {r : radix} : ∀ u i,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, fA_ge_1_ε u i k = true)
  → (∀ k, u (i + k + 1) = rad - 1) ∨
     (∀ k, u (i + k + 1) = 2 * (rad - 1)) ∨
     (∃ j,
       (∀ k, k < j → u (i + k + 1) = rad - 1) ∧
       u (i + j + 1) = rad - 2 ∧
       (∀ k, u (i + j + k + 2) = 2 * (rad - 1))).
Proof.
intros * Hur Hu.
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
  assert (H4 : u (i + j + 1) = rad - 2). {
    specialize (A_ge_1_add_ge u i j Hur Hu H1 H2 H3) as H4.
    assert (H5 : u (i + j + 1) < rad). {
      destruct j; [ rewrite Nat.add_0_r, H1; flia Hr | ].
      remember (S j) as k; assert (Hj : k ≠ 0) by flia Heqk.
      now apply A_ge_1_add_9_eq.
    }
    flia H2 H4 H5.
  }
  clear H2; move j before i.
  split; [ easy | ].
  intros k; move k before j.
  assert (Hur2 : ∀ k : nat, u (i + j + k + 2) ≤ 2 * (rad - 1)). {
    intros l.
    replace (i + j + l + 2) with (i + (j + l + 1) + 1) by flia.
    apply Hur.
  }
  specialize (A_ge_1_add_8_eq u (i + j) Hur2 H4 k) as H2.
  assert (H5 : fA_ge_1_ε u (i + j) (k + 1) = true). {
    clear - Hur Hu H3 H4.
    move Hu at bottom.
    now apply A_ge_1_add_all_true_999_8.
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
 assert (H : fA_ge_1_ε v i (k + 1) = true). {
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
   eapply NQle_trans; [ apply H3 | ].
   assert (Hin : i + 1 ≤ n - 1). {
     rewrite Hn.
     destruct rad; [ easy | simpl; flia ].
   }
   setoid_rewrite A_split_first; [ | easy | easy ].
   rewrite <- Nat.add_1_r.
   rewrite H1.
   unfold v at 1.
   destruct (Nat.eq_dec (i + 1) (i + 1)) as [H| ]; [ clear H | easy ].
   assert (H : A (i + 1) n u = A (i + 1) n v). {
     apply summation_eq_compat.
     intros j Hj; f_equal.
     unfold v.
     destruct (Nat.eq_dec j (i + 1)) as [H2| H2]; [ flia Hj H2 | easy ].
   }
   rewrite H; clear H.
   replace (2 * (rad - 1)) with (rad + (rad - 2)) by flia Hr.
   rewrite NQpair_add_l, NQpair_diag; [ | easy ].
   rewrite <- NQadd_assoc, NQfrac_add_nat_l; [ apply NQle_refl | ].
   eapply NQle_trans; [ | apply NQle_add_r ].
   -replace 0%NQ with (0 // 1)%NQ by easy.
    apply NQle_pair; [ easy | pauto | flia Hr ].
   -apply (NQmul_le_mono_pos_r (rad // 1)%NQ).
    +replace 0%NQ with (0 // 1)%NQ by easy.
     apply NQlt_pair; [ easy | pauto | flia Hr ].
    +rewrite NQmul_0_l, <- NQmul_assoc.
     rewrite NQmul_pair_den_num; [ | easy ].
     rewrite NQmul_1_r.
     apply A_ge_0.
 }
 specialize (H2 H); clear H.
 unfold v in H2.
 destruct (Nat.eq_dec (i + k + 2) (i + 1)) as [H3| H3]; [ flia H3 | ].
 now replace (i + k + 2) with (i + S k + 1) in H2 by flia.
Qed.

Theorem eq_nA_div_1 {r : radix} : ∀ i n u,
  (∀ k, u (i + k + 1) ≤ 2 * (rad - 1))
  → NQintg (A i n u) ≥ 1
  → NQintg (A i n u) = 1.
Proof.
intros * Hur Hn.
specialize (A_upper_bound_for_add u i n Hur) as H1.
remember (n - i - 1) as s eqn:Hs.
remember (A i n u) as x eqn:Hx in H1.
rewrite NQintg_frac in Hx; [ subst x | apply A_ge_0 ].
remember (NQintg (A i n u)) as x eqn:Hx.
destruct x; [ easy | ].
destruct x; [ easy | exfalso ].
apply NQnlt_ge in H1; apply H1; clear H1.
replace (S (S x)) with (2 + x) by easy.
rewrite NQpair_add_l.
rewrite NQmul_sub_distr_l, NQmul_1_r.
rewrite NQmul_pair; [ | easy | pauto ].
rewrite Nat.mul_1_r, Nat.mul_1_l.
unfold NQsub.
rewrite <- NQadd_assoc.
apply NQadd_lt_mono_l.
apply (NQlt_le_trans _ 0); [ easy | ].
replace 0%NQ with (0 // 1 + 0)%NQ by easy.
apply NQadd_le_mono.
-apply NQle_pair; [ easy | easy | flia ].
-apply NQfrac_ge_0.
Qed.

(**)
Theorem A_ge_1_add_r_true_if {r : radix} : ∀ u i j k,
   fA_ge_1_ε u i (j + k) = true
   → fA_ge_1_ε u (i + j) k = true.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu.
apply A_ge_1_true_iff in Hu.
apply A_ge_1_true_iff.
unfold min_n in Hu |-*.
replace (i + (j + k) + 3) with (i + j + k + 3) in Hu by flia.
remember (rad * (i + j + k + 3)) as n eqn:Hn.
(*
remember (n - (i + j) - 1) as s eqn:Hs.
move s before n.
*)
assert (Hijn : i + j + 2 ≤ n - 1). {
  rewrite Hn.
  destruct rad; [ easy | simpl; flia ].
}
(*
replace (n - i - 1) with (s + j) in Hu by flia Hs Hijn.
replace (s + j - S (j + k)) with (s - S k) in Hu by flia Hs.
*)
move Hu at bottom.
revert Hu.
apply Decidable.contrapositive; [ apply NQle_decidable | ].
intros Hu.
apply NQnle_gt in Hu.
apply NQnle_gt.
(*
rewrite Nat.pow_add_r.
rewrite Nat.mod_mul_r; try pauto.
*)
unfold NQfrac in Hu; unfold NQfrac.
Abort. (* à terminer
...
assert (H1 : nA (i + j) n u mod rad ^ s = nA i n u mod rad ^ s). {
  clear - Hs Hijn.
  destruct j; [ now rewrite Nat.add_0_r | ].
  symmetry.
  rewrite nA_split with (e := i + j + 2); [ | flia Hijn ].
  replace (i + j + 2 - 1) with (i + S j) by flia.
  replace (n - (i + j + 2)) with s by flia Hs.
  rewrite <- Nat.add_mod_idemp_l; [ | pauto ].
  rewrite Nat.mod_mul; [ easy | pauto ].
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
  *apply Nat.neq_0_lt_0; pauto.
  *rewrite Nat.sub_1_r.
   apply Nat.lt_le_pred.
   apply Nat.mod_upper_bound.
   pauto.
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
   apply Nat.neq_0_lt_0; pauto.
 +apply Nat.neq_0_lt_0; pauto.
Qed.
*)
(*
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
rewrite Nat.mod_mul_r; try pauto.
assert (H1 : nA (i + j) n u mod rad ^ s = nA i n u mod rad ^ s). {
  clear - Hs Hijn.
  destruct j; [ now rewrite Nat.add_0_r | ].
  symmetry.
  rewrite nA_split with (e := i + j + 2); [ | flia Hijn ].
  replace (i + j + 2 - 1) with (i + S j) by flia.
  replace (n - (i + j + 2)) with s by flia Hs.
  rewrite <- Nat.add_mod_idemp_l; [ | pauto ].
  rewrite Nat.mod_mul; [ easy | pauto ].
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
  *apply Nat.neq_0_lt_0; pauto.
  *rewrite Nat.sub_1_r.
   apply Nat.lt_le_pred.
   apply Nat.mod_upper_bound.
   pauto.
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
   apply Nat.neq_0_lt_0; pauto.
 +apply Nat.neq_0_lt_0; pauto.
Qed.
*)

(*
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
*)

Theorem A_ge_999000 {r : radix} : ∀ u i j,
  (∀ k, rad - 1 ≤ u (i + k + 1))
  → let n1 := rad * (i + j + 3) in
     let s1 := n1 - i - 1 in
     (1 - 1 // rad ^ S j ≤ A i n1 u)%NQ.
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
rewrite A_split with (e := i + j + 2); [ | flia Hin1 ].
eapply NQle_trans; cycle 1. {
  apply NQle_add_r.
  replace (i + j + 2 - i - 1) with (S j) by flia.
  apply (NQmul_le_mono_pos_r (rad ^ S j // 1)%NQ).
  -replace 0%NQ with (0 // 1)%NQ by easy.
   apply NQlt_pair; [ easy | easy | ].
   rewrite Nat.mul_1_r, Nat.mul_1_l.
   apply Nat.neq_0_lt_0; pauto.
  -rewrite NQmul_0_l, <- NQmul_assoc.
   rewrite NQmul_inv_pair; [ | easy | pauto ].
   rewrite NQmul_1_r; apply A_ge_0.
}
unfold A.
rewrite summation_shift; [ | flia ].
rewrite NQpower_summation_inv; [ | flia Hr ].
rewrite summation_mul_distr_l.
replace (i + j + 2 - 1 - (i + 1)) with j by flia Hin1.
apply summation_le_compat.
intros k Hk.
replace (i + 1 + k - i) with (S k) by flia.
rewrite NQsub_pair_pos; [ | easy | easy | flia Hr ].
do 2 rewrite Nat.mul_1_l.
rewrite NQmul_pair; [ | easy | pauto ].
rewrite Nat.mul_1_r.
rewrite <- Nat.pow_succ_r; [ | easy ].
apply NQle_pair; [ pauto | pauto | ].
rewrite Nat.mul_comm.
apply Nat.mul_le_mono_l.
rewrite Nat.add_shuffle0; apply Hur.
Qed.
