(* Real between 0 and 1, i.e. fractional part of a real.
   Implemented as function of type nat → nat.
   Operations + and * implemented using LPO. *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz NPeano.
Require Import Misc Summation.
Import Init.Nat.

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

Definition is_0_after {r : radix} u i j :=
  if eq_nat_dec (d2n u (i + j)) 0 then true else false.
Definition is_9_after {r : radix} u i j :=
  if eq_nat_dec (d2n u (i + j)) (rad - 1) then true else false.
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

Theorem is_9_after_false_iff {r : radix} : ∀ i j u,
  is_9_after u i j = false ↔ d2n u (i + j) ≠ rad - 1.
Proof.
intros.
unfold is_9_after.
now destruct (Nat.eq_dec (d2n u (i + j)) (rad - 1)).
Qed.

Theorem is_9_after_true_iff {r : radix} : ∀ i j u,
  is_9_after u i j = true ↔ d2n u (i + j) = rad - 1.
Proof.
intros.
unfold is_9_after.
now destruct (Nat.eq_dec (d2n u (i + j)) (rad - 1)).
Qed.

Theorem is_0_after_false_iff {r : radix} : ∀ i j u,
  is_0_after u i j = false ↔ d2n u (i + j) ≠ 0.
Proof.
intros.
unfold is_0_after.
now destruct (Nat.eq_dec (d2n u (i + j)) 0).
Qed.

Theorem is_0_after_true_iff {r : radix} : ∀ i j u,
  is_0_after u i j = true ↔ d2n u (i + j) = 0.
Proof.
intros.
unfold is_0_after.
now destruct (Nat.eq_dec (d2n u (i + j)) 0).
Qed.

Theorem is_9_strict_after_all_9 {r : radix} : ∀ u i,
  (∀ j, is_9_strict_after u i j = true)
  → (∀ k, d2n u (i + k + 1) = rad - 1).
Proof.
intros * Hm9 *.
specialize (Hm9 k); unfold is_9_strict_after in Hm9.
now destruct (Nat.eq_dec (d2n u (i + k + 1)) (rad - 1)).
Qed.

Theorem is_9_strict_after_add {r : radix} : ∀ u i j,
  is_9_strict_after u 0 (i + j) = is_9_strict_after u i j.
Proof. easy. Qed.

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

Definition freal_norm_not_norm_eq {r : radix} x y :=
  ∃ k,
   (∀ i, i < k - 1 → freal x i = freal y i) ∧
   (k = 0 ∨ fd2n x (k - 1) = S (fd2n y (k - 1))) ∧
   (∀ i, fd2n x (k + i) = 0) ∧
   (∀ i, fd2n y (k + i) = rad - 1).

Theorem freal_normalized_iff {r : radix} : ∀ x y,
  (∀ i, freal (freal_normalize x) i = freal y i)
  ↔ (∀ k, ∃ i, k ≤ i ∧ S (fd2n x i) < rad) ∧
     (∀ i, freal x i = freal y i) ∨
     freal_norm_not_norm_eq y x.
Proof.
intros.
split; intros Hxy.
-destruct (LPO_fst (has_same_digits x y)) as [Hxsy| Hxsy].
 +left.
  split.
  *intros k.
   specialize (Hxy k).
   unfold freal_normalize, normalize in Hxy.
   simpl in Hxy.
   destruct (LPO_fst (is_9_strict_after (freal x) k)) as [Hxk| Hxk].
  --specialize (Hxsy k).
    unfold has_same_digits in Hxsy.
    destruct (Nat.eq_dec (fd2n x k) (fd2n y k)) as [H| ]; [ | easy ].
    clear Hxsy.
    apply digit_eq_eq in Hxy.
    unfold fd2n in H.
    destruct (lt_dec (S (d2n (freal x) k)) rad) as [Hsxk| Hsxk].
   ++simpl in Hxy; unfold d2n in Hxy; rewrite H in Hxy; flia Hxy.
   ++simpl in Hxy; unfold d2n in Hsxk.
     rewrite H, <- Hxy in Hsxk.
     now specialize radix_ge_2.
  --destruct Hxk as (i & Hij & Hi).
    exists (k + i + 1).
    split; [ flia | ].
    unfold is_9_strict_after in Hi.
    destruct (Nat.eq_dec (d2n (freal x) (k + i + 1)) (rad - 1)) as [H| H].
   ++easy.
   ++unfold d2n in H; unfold fd2n.
     specialize (digit_lt_radix (freal x (k + i + 1))) as Hr.
     flia H Hr.
  *intros k; specialize (Hxsy k).
   unfold has_same_digits in Hxsy.
   destruct (Nat.eq_dec (fd2n x k) (fd2n y k)) as [H| ];
     [ clear Hxsy | easy ].
   unfold fd2n in H.
   now apply digit_eq_eq.
 +right.
  destruct Hxsy as (k & Hjk & Hxyk).
  unfold freal_norm_not_norm_eq.
  *destruct (zerop k) as [Hzk| Hzk].
  --subst k; clear Hjk.
    unfold has_same_digits in Hxyk.
    destruct (Nat.eq_dec (fd2n x 0) (fd2n y 0)) as [H| H]; [ easy | ].
    clear Hxyk; rename H into Hxy0; unfold fd2n in Hxy0.
    specialize (Hxy 0) as Hxy1.
   **unfold freal_normalize, normalize in Hxy1; simpl in Hxy1.
     destruct (LPO_fst (is_9_strict_after (freal x) 0)) as [Hx0| Hx0].
   ---destruct (lt_dec (S (d2n (freal x) 0)) rad) as [Hsx0| Hsx0].
    +++exists 1.
       apply digit_eq_eq in Hxy1; simpl in Hxy1.
       split; [ now intros | ].
       split; [ now right | ].
       assert (Hxk : ∀ i, fd2n x (1 + i) = rad - 1). {
         intros i; specialize (Hx0 i) as H.
         unfold is_9_strict_after in H; unfold fd2n.
         simpl in H; rewrite Nat.add_comm in H.
         now destruct (Nat.eq_dec (d2n (freal x) (1 + i)) (rad - 1)).
       }
       split; [ | easy ].
       intros i.
       specialize (Hxy (S i)) as Hxy2.
       unfold freal_normalize, normalize in Hxy2.
       simpl in Hxy2.
       destruct (LPO_fst (is_9_strict_after (freal x) (S i))) as [Hx1| Hx1].
     ***destruct (lt_dec (S (d2n (freal x) (S i))) rad) as [Hsx1| Hsx1].
     ----specialize (Hx0 i).
         unfold is_9_strict_after, d2n in Hx0; unfold d2n in Hsx1.
         simpl in Hx0; rewrite Nat.add_1_r in Hx0.
         destruct (Nat.eq_dec (dig (freal x (S i))) (rad - 1)); [ | easy ].
         flia e Hsx1.
     ----now apply digit_eq_eq in Hxy2; simpl in Hxy2.
     ***destruct Hx1 as (j & Hjj & Hj).
        unfold is_9_strict_after in Hj; unfold d2n in Hj.
        destruct (Nat.eq_dec (dig (freal x (S i + j + 1))) (rad - 1)).
     ----easy.
     ----specialize (Hxk (S i + j)).
         rewrite Nat.add_comm in Hxk.
         now unfold fd2n in Hxk.
    +++exists 0.
       split; [ now intros | ].
       split; [ now left | simpl ].
       assert (Hxk : ∀ i, fd2n x i = rad - 1).
     ***intros i.
        destruct i.
     ----unfold d2n in Hsx0; unfold fd2n.
         specialize (digit_lt_radix (freal x 0)) as H; flia H Hsx0.
     ----specialize (Hxy i).
         unfold freal_normalize, normalize in Hxy.
         simpl in Hxy.
         destruct (LPO_fst (is_9_strict_after (freal x) i)) as [Hx1| Hx1].
      ++++specialize (Hx1 0).
          unfold is_9_strict_after, d2n in Hx1.
          rewrite Nat.add_0_r, Nat.add_1_r in Hx1.
          now destruct (Nat.eq_dec (dig (freal x (S i))) (rad - 1)).
      ++++destruct Hx1 as (j & Hjj & Hj).
          specialize (Hx0 (i + j)).
          rewrite is_9_strict_after_add in Hx0.
          now rewrite Hj in Hx0.
     ***split; [ | easy ].
        intros i.
        destruct i.
     ----now apply digit_eq_eq in Hxy1.
     ----specialize (Hxy (S i)).
         unfold freal_normalize, normalize in Hxy.
         simpl in Hxy.
         destruct (LPO_fst (is_9_strict_after (freal x) (S i))) as [Hx1| Hx1].
      ++++destruct (lt_dec (S (d2n (freal x) (S i))) rad) as [Hsx1| Hsx1].
       ****specialize (Hx0 i).
           apply is_9_strict_after_true_iff in Hx0; simpl in Hx0.
           rewrite Nat.add_1_r in Hx0.
           flia Hsx1 Hx0.
       ****now apply digit_eq_eq in Hxy.
      ++++destruct Hx1 as (j & Hjj & Hj).
          specialize (Hx0 (S (i + j))).
          apply is_9_strict_after_true_iff in Hx0; simpl in Hx0.
          apply is_9_strict_after_false_iff in Hj; simpl in Hj.
          easy.
   ---now rewrite Hxy1 in Hxy0.
  --exists (S k).
    assert (Hkxy : ∀ i, i < k → freal y i = freal x i). {
      intros i Hik.
      specialize (Hjk _ Hik).
      unfold has_same_digits in Hjk.
      destruct (Nat.eq_dec (fd2n x i) (fd2n y i)) as [H| ]; [ | easy ].
      clear Hjk; unfold fd2n in H.
      now symmetry; apply digit_eq_eq.
    }
    split; [ now simpl; rewrite Nat.sub_0_r | ].
    specialize (Hxy k) as Hk.
    apply digit_eq_eq in Hk.
    unfold freal_normalize in Hk; simpl in Hk.
    unfold normalize in Hk.
    destruct (LPO_fst (is_9_strict_after (freal x) k)) as [H| Hxk].
   ++assert (Hxk : ∀ i, fd2n x (S k + i) = rad - 1). {
       intros i; specialize (H i).
       apply is_9_strict_after_true_iff in H.
       now rewrite Nat.add_comm in H.
     }
     rewrite <- and_assoc, and_comm.
     split; [ easy | clear H ].
     simpl; rewrite Nat.sub_0_r.
     destruct (lt_dec (S (d2n (freal x) k))) as [Hsxk| Hsxk].
    **simpl in Hk.
      split; [ now right | ].
      intros i.
      specialize (Hxy (S k + i)) as Hxy1.
      unfold freal_normalize, normalize in Hxy1.
      simpl in Hxy1.
      destruct (LPO_fst (is_9_strict_after (freal x) (S (k + i)))) as [Hx1| Hx1].
    ---destruct (lt_dec (S (d2n (freal x) (S (k + i)))) rad) as [Hsx1| Hsx1].
     +++specialize (Hxk i); clear Hxy1.
        simpl in Hxk.
        unfold fd2n in Hxk; unfold d2n in Hsx1; flia Hxk Hsx1.
     +++now apply digit_eq_eq in Hxy1.
    ---destruct Hx1 as (j & Hjj & Hj).
       apply is_9_strict_after_false_iff in Hj.
       specialize (Hxk (S (i + j))).
       unfold fd2n in Hxk; unfold d2n in Hj.
       now replace (S (k + i) + j + 1) with (S k + S (i + j)) in Hj by flia.
    **simpl in Hk; unfold fd2n; symmetry in Hk; rewrite Hk.
      apply Nat.nlt_ge in Hsxk.
      specialize (digit_lt_radix (freal x k)) as H.
      unfold d2n in Hsxk.
      apply Nat.le_antisymm in Hsxk; [ clear H | easy ].
      rewrite Hsxk.
      destruct k; [ easy | ].
      specialize (Hxy k) as Hk'.
      unfold freal_normalize, normalize in Hk'.
      simpl in Hk'.
      destruct (LPO_fst (is_9_strict_after (freal x) k)) as [Hxk'| Hxk'].
    ---specialize (Hjk _ (Nat.lt_succ_diag_r k)).
       unfold has_same_digits in Hjk.
       destruct (Nat.eq_dec (fd2n x k) (fd2n y k)) as [H| H]; [ | easy ].
       apply digit_eq_eq in Hk'; unfold fd2n in H.
       destruct (lt_dec (S (d2n (freal x) k)) rad) as [Hsxk'| Hsxk'].
     +++simpl in Hk'; unfold d2n in Hk'; flia H Hsxk' Hk'.
     +++simpl in Hk'; unfold d2n in Hsxk'.
        specialize radix_ge_2 as Hr; flia H Hsxk' Hk' Hr.
    ---destruct Hxk' as (i & Hji & Hi).
       apply is_9_strict_after_false_iff in Hi.
       unfold d2n in Hi.
       destruct i.
     +++rewrite Nat.add_0_r, Nat.add_1_r in Hi; flia Hsxk Hi.
     +++specialize (Hxk i); unfold fd2n in Hxk.
        now replace (k + S i + 1) with (S (S k) + i) in Hi by flia.
   ++exfalso.
     unfold has_same_digits in Hxyk.
     destruct (Nat.eq_dec (fd2n x k) (fd2n y k)) as [H| H]; [ easy | ].
     now unfold fd2n in H.
-intros i.
 destruct Hxy as [Hxy | Hxy].
 +destruct Hxy as (Hki, Hxy).
  unfold freal_normalize, normalize; simpl.
  destruct (LPO_fst (is_9_strict_after (freal x) i)) as [Hxi| Hxi].
  *specialize (Hki (S i)) as (j & H1j & Hj); unfold fd2n in Hj.
   specialize (Hxi (j - i - 1)).
   apply is_9_strict_after_true_iff in Hxi; unfold d2n in Hxi.
   replace (i + (j - i - 1) + 1) with j in Hxi; flia Hxi Hj H1j.
  *apply Hxy.
 +unfold freal_norm_not_norm_eq in Hxy.
  destruct Hxy as (k & Hik & Hxy & Hx & Hy).
  unfold freal_normalize, normalize; simpl.
  destruct (LPO_fst (is_9_strict_after (freal x) i)) as [Hxi| Hxi].
  *destruct (lt_dec (S (d2n (freal x) i)) rad) as [Hsxi| Hsxi].
  --apply digit_eq_eq; simpl.
    destruct (le_dec k i) as [Hki| Hki].
   ++specialize (Hy (i - k)).
     replace (k + (i - k)) with i in Hy by flia Hki.
     unfold fd2n in Hy; unfold d2n in Hsxi; flia Hy Hsxi.
   ++apply Nat.nle_gt in Hki.
     destruct Hxy as [Hxy| Hxy]; [ flia Hxy Hki | ].
     destruct (Nat.eq_dec i (k - 1)) as [Hik1| Hik1]; [ now subst i | ].
     specialize (Hxi (k - i - 2)).
     apply is_9_strict_after_true_iff in Hxi.
     replace (i + (k - i - 2) + 1) with (k - 1) in Hxi by flia Hki Hik1.
     unfold fd2n in Hxy; unfold d2n in Hxi.
     specialize (digit_lt_radix (freal y (k - 1))) as H; flia Hxy Hxi H.
  --apply digit_eq_eq; simpl; symmetry.
    apply Nat.nlt_ge in Hsxi.
    destruct k.
   **now specialize (Hx i).
   **destruct Hxy as [Hxy| Hxy]; [ easy | ].
     simpl in Hik, Hxy; rewrite Nat.sub_0_r in Hik, Hxy.
     destruct (lt_eq_lt_dec i k) as [[Hki| Hki]| Hki].
   ---specialize (Hxi (k - i - 1)).
      apply is_9_strict_after_true_iff in Hxi; unfold d2n in Hxi.
      replace (i + (k - i - 1) + 1) with k in Hxi by flia Hki.
      unfold fd2n in Hxy.
      specialize (digit_lt_radix (freal y k)) as H1; flia Hxy Hxi H1.
   ---subst i.
      unfold fd2n in Hxy; unfold d2n in Hsxi.
      specialize (digit_lt_radix (freal y k)) as H1; flia Hxy Hsxi H1.
   ---specialize (Hx (i - S k)).
      now replace (S k + (i - S k)) with i in Hx by flia Hki.
  *destruct Hxi as (j & Hjj & Hj).
   apply is_9_strict_after_false_iff in Hj; unfold d2n in Hj.
   destruct k.
  --specialize (Hy (i + j + 1)); simpl in Hy.
    unfold fd2n in Hy; exfalso; flia Hy Hj.
  --destruct Hxy as [| Hxy]; [ easy | ].
    simpl in Hik, Hxy; rewrite Nat.sub_0_r in Hik, Hxy.
    destruct (lt_dec i k) as [Hki| Hki].
   **now symmetry; apply Hik.
   **specialize (Hy (i + j - k)).
     now replace (S k + (i + j - k)) with (i + j + 1) in Hy by flia Hki.
Qed.

Theorem freal_eq_normalize_eq {r : radix} : ∀ n x y,
  (∀ i, n ≤ i → freal x i = freal y i)
  → ∀ i, n ≤ i → freal (freal_normalize x) i = freal (freal_normalize y) i.
Proof.
intros * Hxy * Hni.
unfold freal_normalize, normalize; simpl.
unfold d2n; rewrite Hxy; [ | easy ].
destruct (LPO_fst (is_9_strict_after (freal x) i)) as [H1| H1].
-destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H2| H2]; [ easy | ].
 destruct H2 as (j & Hjj & Hj).
 specialize (H1 j).
 apply is_9_strict_after_true_iff in H1.
 apply is_9_strict_after_false_iff in Hj.
 unfold d2n in H1, Hj.
 rewrite Hxy in H1; [ easy | flia Hni ].
-destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H2| H2]; [ | easy ].
 destruct H1 as (j & Hjj & Hj).
 specialize (H2 j).
 apply is_9_strict_after_false_iff in Hj.
 apply is_9_strict_after_true_iff in H2.
 unfold d2n in H2, Hj.
 rewrite Hxy in Hj; [ easy | flia Hni ].
Qed.

Theorem freal_norm_not_norm_eq_normalize_eq {r : radix} : ∀ x y,
  freal_norm_not_norm_eq x y
  → ∀ i : nat, freal (freal_normalize x) i = freal (freal_normalize y) i.
Proof.
intros * Hxy *.
unfold freal_norm_not_norm_eq in Hxy.
destruct Hxy as (k & Hb & Hw & Hax & Hay).
unfold freal_normalize, normalize; simpl.
destruct (LPO_fst (is_9_strict_after (freal x) i)) as [H1| H1].
-specialize (H1 (max i k - i)).
 specialize (Hax (S (max i k) - k)).
 replace (k + (S (max i k) - k)) with (S (max i k)) in Hax by flia.
 unfold fd2n in Hax.
 apply is_9_strict_after_true_iff in H1.
 unfold d2n in H1.
 replace (i + (max i k - i) + 1) with (S (max i k)) in H1 by flia.
 rewrite Hax in H1.
 specialize radix_ge_2; flia H1.
-destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H2| H2].
 +destruct (lt_eq_lt_dec i (k - 1)) as [[H4| H4]| H4].
  *destruct k; [ easy | ].
   specialize (H2 (k - i - 1)).
   apply is_9_strict_after_true_iff in H2.
   unfold d2n in H2.
   replace (i + (k - i - 1) + 1) with k in H2 by flia H4.
   simpl in Hw; rewrite Nat.sub_0_r in Hw.
   unfold fd2n in Hw.
   specialize (digit_lt_radix (freal x k)) as H6; flia Hw H2 H6.
  *subst i.
   destruct k.
  --clear Hb Hw; simpl in H2; simpl.
    destruct (lt_dec (S (d2n (freal y) 0))) as [H3| H3].
   ++exfalso; unfold fd2n in Hay; unfold d2n in H3.
     simpl in Hay; rewrite Hay in H3; flia H3.
   ++apply digit_eq_eq; simpl.
     now simpl in Hax; unfold fd2n in Hax; rewrite Hax.
  --destruct Hw as [| Hw]; [ easy | ].
    simpl in Hw; rewrite Nat.sub_0_r in Hw.
    simpl; rewrite Nat.sub_0_r.
    destruct (lt_dec (S (d2n (freal y) k)) rad) as [H3| H3].
   ++now apply digit_eq_eq; simpl.
   ++unfold fd2n in Hw; unfold d2n in H3.
     specialize (digit_lt_radix (freal x k)); flia Hw H3.
  *destruct (lt_dec (S (d2n (freal y) i)) rad) as [H3| H3].
  --unfold fd2n in Hay; unfold d2n in H3.
    specialize (Hay (i - k)).
    replace (k + (i - k)) with i in Hay by flia H4.
    exfalso; rewrite Hay in H3; flia H3.
  --apply digit_eq_eq; simpl.
    unfold fd2n in Hax.
    specialize (Hax (i - k)).
    now replace (k + (i - k)) with i in Hax by flia H4.
 +destruct (lt_eq_lt_dec i (k - 1)) as [[H4| H4]| H4].
  *now rewrite Hb.
  *subst i.
   destruct H2 as (j & Hjj & Hj).
   apply is_9_strict_after_false_iff in Hj.
   unfold d2n in Hj; unfold fd2n in Hay.
   specialize (Hay (k - 1 + j + 1 - k)).
   now replace (k + (k - 1 + j + 1 - k)) with (k - 1 + j + 1) in Hay by flia.
  *destruct H2 as (j & Hjj & Hj).
   apply is_9_strict_after_false_iff in Hj.
   unfold d2n in Hj; unfold fd2n in Hay.
   specialize (Hay (i + j + 1 - k)).
   now replace (k + (i + j + 1 - k)) with (i + j + 1) in Hay by flia H4.
Qed.

Theorem freal_normalized_eq_iff {r : radix} : ∀ x y,
  (∀ i, freal (freal_normalize x) i = freal (freal_normalize y) i)
  ↔ (∀ i, freal x i = freal y i) ∨
     freal_norm_not_norm_eq x y ∨ freal_norm_not_norm_eq y x.
Proof.
intros.
split; intros Hxy.
-remember (freal_normalize x) as x' eqn:Hx'.
 remember (freal_normalize y) as y' eqn:Hy'.
 move y' before x'.
 generalize Hxy; intros Hx; symmetry in Hx.
 generalize Hxy; intros Hy; symmetry in Hy.
 rewrite Hx' in Hx.
 rewrite Hy' in Hy.
 assert (H : ∀ i, freal (freal_normalize x) i = freal x' i) by
   now intros; rewrite Hxy, Hx.
 clear Hx; rename H into Hx; move Hx after Hy.
 clear y' Hy' Hxy.
 rename x' into z; rename Hx' into Hz.
 apply freal_normalized_iff in Hx.
 apply freal_normalized_iff in Hy.
 destruct Hx as [Hx| Hx].
 +destruct Hx as (Hx, Hxz).
  destruct Hy as [Hy| Hy].
  *destruct Hy as (Hy, Hyz).
   now left; intros i; rewrite Hxz, Hyz.
  *destruct Hy as (k & Hbk & Hk & Hakz & Haky).
   right; left; exists k.
   split; [ now intros; rewrite Hxz; apply Hbk | ].
   split; [ now unfold fd2n; rewrite Hxz | ].
   now split; [ intros; unfold fd2n; rewrite Hxz; apply Hakz | ].
 +destruct Hx as (kx & Hbkx & Hkx & Hakxz & Hakx).
  destruct Hy as [Hy| Hy].
  *destruct Hy as (Hy, Hyz).
   right; right; exists kx.
   split; [ now intros; rewrite Hyz; apply Hbkx | ].
   split; [ now unfold fd2n; rewrite Hyz | ].
   now split; [ intros; unfold fd2n; rewrite Hyz; apply Hakxz | ].
  *destruct Hy as (ky & Hbky & Hky & Hakyz & Haky).
   left; intros i.
   destruct (lt_eq_lt_dec kx ky) as [[Hkk| Hkk]| Hkk].
  --destruct ky; [ easy | ].
    destruct Hky as [| Hky]; [ easy | ].
    simpl in Hbky, Hky; rewrite Nat.sub_0_r in Hbky, Hky.
    specialize (Hakxz (ky - kx)).
    replace (kx + (ky - kx)) with ky in Hakxz by flia Hkk.
    now rewrite Hakxz in Hky.
  --subst ky.
    destruct kx.
   ++apply digit_eq_eq; unfold fd2n in Hakx, Haky.
     simpl in Hakx, Haky.
     now rewrite Hakx, Haky.
   ++destruct Hkx as [| Hkx]; [ easy | ].
     destruct Hky as [| Hky]; [ easy | ].
     simpl in Hbkx, Hkx, Hky, Hbky.
     rewrite Nat.sub_0_r in Hbkx, Hkx, Hky, Hbky.
     destruct (lt_eq_lt_dec i kx) as [[Hikx| Hikx]| Hikx].
    **now rewrite <- Hbkx; [ rewrite <- Hbky | ].
    **apply digit_eq_eq; unfold fd2n in Hkx, Hky; subst i.
      now apply Nat.succ_inj; rewrite <- Hkx, <- Hky.
    **apply digit_eq_eq; unfold fd2n in Hakx, Haky.
      specialize (Hakx (i - S kx)).
      specialize (Haky (i - S kx)).
      replace (S kx + (i - S kx)) with i in Hakx, Haky by flia Hikx.
      now rewrite Haky.
  --destruct kx; [ easy | ].
    destruct Hkx as [| Hkx]; [ easy | ].
    simpl in Hbkx, Hkx; rewrite Nat.sub_0_r in Hbkx, Hkx.
    specialize (Hakyz (kx - ky)).
    replace (ky + (kx - ky)) with kx in Hakyz by flia Hkk.
    now rewrite Hakyz in Hkx.
-destruct Hxy as [Hxy| [Hxy| Hxy]].
 +intros i.
  apply (freal_eq_normalize_eq 0); [ | flia ].
  intros j Hj; apply Hxy.
 +now apply freal_norm_not_norm_eq_normalize_eq.
 +now intros; symmetry; apply freal_norm_not_norm_eq_normalize_eq.
Qed.

Definition has_not_9_after {r : radix} u i j :=
  match LPO_fst (is_9_after u (i + j)) with
  | inl _ => false
  | inr _ => true
  end.

Definition has_not_0_after {r : radix} u i j :=
  match LPO_fst (is_0_after u (i + j)) with
  | inl _ => false
  | inr _ => true
  end.

Definition ends_with_999 {r : radix} u i :=
  match LPO_fst (has_not_9_after u i) with
  | inl _ => false
  | inr _ => true
  end.

Theorem ends_with_999_true_iff {r : radix} : ∀ u i,
  ends_with_999 u i = true ↔
  ∃ j P, LPO_fst (has_not_9_after u i) = inr (exist _ j P).
Proof.
intros.
split.
-intros H9.
 unfold ends_with_999 in H9.
 destruct (LPO_fst (has_not_9_after u i)) as [H1| H1]; [ easy | clear H9 ].
 destruct H1 as (j & Hjj).
 now exists j, Hjj.
-intros (j & ((P & Q) & _)).
 unfold ends_with_999.
 destruct (LPO_fst (has_not_9_after u i)) as [H1| H1]; [ | easy ].
 specialize (H1 j).
 now rewrite H1 in Q.
Qed.

Theorem ends_with_999_false_iff {r : radix} : ∀ u i,
  ends_with_999 u i = false ↔
  ∃ P, LPO_fst (has_not_9_after u i) = inl P.
Proof.
intros.
split.
-intros H9.
 unfold ends_with_999 in H9.
 destruct (LPO_fst (has_not_9_after u i)) as [H1| H1]; [ clear H9 | easy ].
 now exists H1.
-intros (P & _).
 unfold ends_with_999.
 destruct (LPO_fst (has_not_9_after u i)) as [H1| H1]; [ easy | ].
 destruct H1 as (j & (_, Q)).
 now rewrite P in Q.
Qed.

Theorem has_not_9_after_true_iff {r : radix} : ∀ u i j,
  has_not_9_after u i j = true ↔
  ∃ k P, LPO_fst (is_9_after u (i + j)) = inr (exist _ k P).
Proof.
intros.
unfold has_not_9_after.
destruct (LPO_fst (is_9_after u (i + j))) as [H1| H1].
-split; [ easy | ].
 intros (k & (P & Q) & _).
 now rewrite H1 in Q.
-split; [ intros _ | easy ].
 destruct H1 as (k & Hk).
 now exists k, Hk.
Qed.

Theorem has_not_9_after_false_iff {r : radix} : ∀ u i j,
  has_not_9_after u i j = false ↔
  ∃ P, LPO_fst (is_9_after u (i + j)) = inl P.
Proof.
intros.
unfold has_not_9_after.
destruct (LPO_fst (is_9_after u (i + j))) as [H1| H1].
-split; [ intros _ | easy ].
 now exists H1.
-split; [ easy | ].
 intros (P & _).
 destruct H1 as (k & _ & Q).
 now rewrite P in Q.
Qed.

Theorem has_not_0_after_true_iff {r : radix} : ∀ u i j,
  has_not_0_after u i j = true ↔
  ∃ k P, LPO_fst (is_0_after u (i + j)) = inr (exist _ k P).
Proof.
intros.
unfold has_not_0_after.
destruct (LPO_fst (is_0_after u (i + j))) as [H1| H1].
-split; [ easy | ].
 intros (k & (P & Q) & _).
 now rewrite H1 in Q.
-split; [ intros _ | easy ].
 destruct H1 as (k & Hk).
 now exists k, Hk.
Qed.

Theorem has_not_0_after_false_iff {r : radix} : ∀ u i j,
  has_not_0_after u i j = false ↔
  ∃ P, LPO_fst (is_0_after u (i + j)) = inl P.
Proof.
intros.
unfold has_not_0_after.
destruct (LPO_fst (is_0_after u (i + j))) as [H1| H1].
-split; [ intros _ | easy ].
 now exists H1.
-split; [ easy | ].
 intros (P & _).
 destruct H1 as (k & _ & Q).
 now rewrite P in Q.
Qed.

Theorem normalized_999 {r : radix} : ∀ x i,
  (∀ j, fd2n x (i + j) = rad - 1)
  → (∀ j, fd2n (freal_normalize x) (i + j) = 0).
Proof.
intros * Hx *.
unfold freal_normalize; simpl.
unfold normalize.
unfold fd2n; simpl.
destruct (LPO_fst (is_9_strict_after (freal x) (i + j))) as [Hxi| Hxi].
-destruct (lt_dec (S (d2n (freal x) (i + j))) rad) as [Hsx| Hsx]; [ | easy ].
 exfalso.
 unfold fd2n in Hx; unfold d2n in Hsx.
 rewrite Hx in Hsx.
 rewrite <- Nat.sub_succ_l in Hsx; [ | easy ].
 rewrite Nat.sub_succ, Nat.sub_0_r in Hsx; flia Hsx.
-destruct Hxi as (k & Hjj & Hj).
 apply is_9_strict_after_false_iff in Hj.
 unfold fd2n in Hx; unfold d2n in Hj.
 specialize (Hx (j + k + 1)).
 replace (i + (j + k + 1)) with (i + j + k + 1) in Hx by flia.
 easy.
Qed.

Theorem normalized_not_999 {r : radix} : ∀ x,
  ¬ (∃ i, ∀ j, fd2n (freal_normalize x) (i + j) = rad - 1).
Proof.
intros x.
specialize radix_ge_2 as Hr.
intros (i & Hi).
assert (H1 : ∀ k, fd2n x (i + k) = rad - 1). {
  intros.
  specialize (Hi k) as H1.
  unfold fd2n, freal_normalize in H1; simpl in H1.
  unfold normalize in H1.
  destruct (LPO_fst (is_9_strict_after (freal x) (i + k))) as [H2| H2].
  -specialize (is_9_strict_after_all_9 (freal x) (i + k) H2) as H3.
   clear H2.
   destruct (lt_dec (S (d2n (freal x) (i + k))) rad) as [H2| H2].
   +simpl in H1.
    clear H2.
    assert (H2 : ∀ j, d2n (freal x) (i + k + 1 + j) = rad - 1). {
      intros j; specialize (H3 j).
      now replace (i + k + j + 1) with (i + k + 1 + j) in H3 by flia.
    }
    clear H3.
    specialize (normalized_999 x (i + k + 1) H2 0) as H3.
    rewrite Nat.add_0_r in H3.
    specialize (Hi (k + 1)).
    replace (i + (k + 1)) with (i + k + 1) in Hi by flia.
    rewrite Hi in H3.
    flia Hr H3.
   +simpl in H1; flia Hr H1.
  -easy.
}
specialize (normalized_999 x i H1) as H2.
specialize (Hi 0).
specialize (H2 0).
rewrite Hi in H2.
flia Hr H2.
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

Definition nA {r : radix} (rg := nat_ord_ring) i n u :=
  Σ (j = i + 1, n - 1), u j * rad ^ (n - 1 - j).

Definition A_ge_1 {r : radix} u i k :=
  let n := rad * (i + k + 3) in
  let s := n - i - 1 in
  if lt_dec (nA i n u mod rad ^ s) ((rad ^ S k - 1) * rad ^ (s - S k)) then
    false
  else
    true.

(* for addition, all A_ge_1 implies u i followed by either
   - 9/9/9/9...
   - 18/18/18/...
   - 9/9/9...9/8/18/18/18...
   for multiplication, to be determined...
 *)

(* Propagation of Carries *)

Definition nat_prop_carr {r : radix} u i :=
  match LPO_fst (A_ge_1 u i) with
  | inl _ =>
      let n := rad * (i + 3) in
      nA i n u / rad ^ (n - i - 1) + 1
  | inr (exist _ k _) =>
      let n := rad * (i + k + 3) in
      nA i n u / rad ^ (n - i - 1)
  end.

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

(*
Theorem sequence_mul_comm : ∀ f g i, sequence_mul f g i = sequence_mul g f i.
Proof.
intros.
unfold sequence_mul.
revert f g.
induction i; intros.
 do 2 rewrite summation_only_one; simpl.
 apply Nat.mul_comm.

 rewrite summation_split_last; [ symmetry | flia ].
 rewrite summation_split_first; [ symmetry | flia ].
 rewrite Nat.sub_0_r, Nat.sub_diag.
 rewrite Nat.add_comm.
 remember minus as x; simpl; subst x; f_equal; [ flia | ].
 rewrite summation_succ_succ.
 rewrite <- IHi.
 apply summation_eq_compat; intros j Hj.
 now rewrite <- Nat.sub_succ_l.
Qed.
*)

Theorem freal_add_series_comm {r : radix} : ∀ x y i, (x ⊕ y) i = (y ⊕ x) i.
Proof.
intros.
unfold "⊕".
apply Nat.add_comm.
Qed.

(*
Theorem freal_mul_series_comm {r : radix} : ∀ x y i,
  freal_mul_series x y i = freal_mul_series y x i.
Proof.
intros.
unfold freal_mul_series.
destruct i; [ easy | ].
apply sequence_mul_comm.
Qed.
*)

Theorem nA_freal_add_series_comm {r : radix} : ∀ x y i n,
  nA i n (x ⊕ y) = nA i n (y ⊕ x).
Proof.
intros.
unfold nA; simpl.
apply summation_eq_compat; intros j Hj.
now rewrite freal_add_series_comm.
Qed.

(*
Theorem nA_freal_mul_series_comm {r : radix} : ∀ x y i n,
  nA i n (freal_mul_series x y) = nA i n (freal_mul_series y x).
Proof.
intros.
unfold nA; simpl.
apply summation_eq_compat; intros j Hj.
now rewrite freal_mul_series_comm.
Qed.
*)

Theorem A_ge_1_freal_add_series_comm {r : radix} : ∀ x y i k,
  A_ge_1 (x ⊕ y) i k = A_ge_1 (y ⊕ x) i k.
Proof.
intros.
unfold A_ge_1.
now rewrite nA_freal_add_series_comm.
Qed.

(*
Theorem A_ge_1_freal_mul_series_comm {r : radix} : ∀ x y i k,
  A_ge_1 (freal_mul_series x y) i k =
  A_ge_1 (freal_mul_series y x) i k.
Proof.
intros.
unfold A_ge_1.
now rewrite nA_freal_mul_series_comm.
Qed.
*)

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

(*
Theorem freal_mul_to_seq_i_comm {r : radix} : ∀ x y i,
  freal_mul_to_seq x y i = freal_mul_to_seq y x i.
Proof.
intros.
unfold freal_mul_to_seq, prop_carr.
remember (freal_mul_series x y) as xy.
remember (freal_mul_series y x) as yx.
apply digit_eq_eq.
destruct (LPO_fst (A_ge_1 xy i)) as [Hxy| Hxy].
-rewrite Heqxy; simpl.
 setoid_rewrite freal_mul_series_comm.
 rewrite <- Heqyx.
 destruct (LPO_fst (A_ge_1 yx i)) as [Hyx| Hyx]; [ easy | ].
 destruct Hyx as (k & Hjk & Hk).
 rewrite Heqyx, A_ge_1_freal_mul_series_comm, <- Heqxy in Hk.
 now rewrite Hxy in Hk.
-destruct Hxy as (k & Hjk & Hk).
 rewrite Heqxy, A_ge_1_freal_mul_series_comm, <- Heqyx in Hk.
 destruct (LPO_fst (A_ge_1 yx i)) as [Hyx| Hyx].
 +now rewrite Hyx in Hk.
 +destruct Hyx as (l & Hjl & Hl).
  destruct (lt_eq_lt_dec k l) as [ [ Hkl | Hkl ] | Hkl ].
  *apply Hjl in Hkl; subst xy.
   now rewrite Hk in Hkl.
  *rewrite Heqxy, freal_mul_series_comm, <- Heqyx.
   rewrite nA_freal_mul_series_comm, <- Heqyx.
   now subst k.
  *apply Hjk in Hkl.
   rewrite Heqxy, A_ge_1_freal_mul_series_comm in Hkl.
   rewrite <- Heqyx in Hkl.
   now rewrite Hl in Hkl.
Qed.
*)

Theorem dig_unorm_add_comm {r : radix} : ∀ x y i,
  freal (x + y) i = freal (y + x) i.
Proof.
intros; simpl.
apply prop_carr_add_comm.
Qed.

(* normally useless *)
Theorem dig_norm_unorm_add_comm {r : radix} : ∀ x y i,
  freal (freal_normalize (x + y)) i =
  freal (freal_normalize (y + x)) i.
Proof.
intros.
unfold freal_normalize; simpl.
unfold normalize.
remember (prop_carr (x ⊕ y)) as xy.
remember (prop_carr (y ⊕ x)) as yx.
destruct (LPO_fst (is_9_strict_after xy i)) as [Hxy| Hxy].
-destruct (LPO_fst (is_9_strict_after yx i)) as [Hyx| Hyx].
 +destruct (lt_dec (S (d2n xy i)) rad) as [Hrxy| Hrxy].
  *subst xy; simpl in Hrxy; simpl.
   destruct (lt_dec (S (d2n yx i)) rad) as [Hryx| Hryx].
  --subst yx; simpl in Hryx; simpl.
    apply digit_eq_eq; unfold d2n.
    remember prop_carr as f; simpl; subst f.
    now rewrite prop_carr_add_comm.
  --subst yx; simpl in Hryx.
    unfold d2n in Hryx.
    now rewrite prop_carr_add_comm in Hryx.
  *destruct (lt_dec (S (d2n yx i)) rad) as [Hryx| Hryx]; [ | easy ].
   exfalso.
   subst xy yx; simpl in Hryx; unfold d2n in Hryx.
   now rewrite prop_carr_add_comm in Hryx.
 +destruct Hyx as (k & Hjk & Hk); clear Hjk.
  subst yx; simpl in Hk; simpl.
  subst xy; simpl in Hxy; simpl.
  apply is_9_strict_after_false_iff in Hk.
  unfold d2n in Hk.
  rewrite prop_carr_add_comm in Hk.
  specialize (Hxy k).
  apply is_9_strict_after_true_iff in Hxy.
  now unfold d2n in Hxy.
-destruct Hxy as (k & Hjk & Hk).
 destruct (LPO_fst (is_9_strict_after yx i)) as [Hyx| Hyx].
 +exfalso; clear Hjk.
  subst xy yx; simpl in Hk, Hyx; unfold d2n in Hk; simpl.
  apply is_9_strict_after_false_iff in Hk.
  unfold d2n in Hk.
  rewrite prop_carr_add_comm in Hk.
  specialize (Hyx k).
  apply is_9_strict_after_true_iff in Hyx.
  now unfold d2n in Hyx.
 +subst xy yx; simpl.
  apply prop_carr_add_comm.
Qed.

(*
Theorem dig_norm_add_comm {r : radix} : ∀ x y i,
  freal (freal_normalize (x + y)) i = freal (freal_normalize (y + x)) i.
Proof.
intros.
apply dig_norm_unorm_add_comm.
Qed.
*)

(*
Theorem dig_norm_mul_comm {r : radix} : ∀ x y i,
  freal (freal_normalize (x * y)) i = freal (freal_normalize (y * x)) i.
Proof.
intros.
unfold freal_normalize.
remember (freal (x * y)) as xy.
remember (freal (y * x)) as yx.
simpl.
unfold normalize.
destruct (LPO_fst (is_9_strict_after xy i)) as [Hxy| Hxy].
-destruct (LPO_fst (is_9_strict_after yx i)) as [Hyx| Hyx].
 +unfold freal_mul in Heqxy; simpl in Heqxy.
  unfold freal_mul in Heqyx; simpl in Heqyx.
  destruct (lt_dec (S (d2n xy i)) rad) as [Hrxy| Hrxy].
  *subst xy; simpl in Hrxy; simpl.
   destruct (lt_dec (S (d2n yx i)) rad) as [Hryx| Hryx].
  --unfold freal_mul in Heqyx; simpl in Heqyx.
    subst yx; simpl in Hryx; unfold d2n.
    apply digit_eq_eq.
    remember freal_mul_to_seq as f; simpl; subst f.
    now rewrite freal_mul_to_seq_i_comm.
  --subst yx; simpl in Hryx; unfold d2n in Hryx.
    now rewrite freal_mul_to_seq_i_comm in Hryx.
  *destruct (lt_dec (S (d2n yx i)) rad) as [Hryx| Hryx]; [ | easy ].
   exfalso.
   subst xy yx; simpl in Hryx; unfold d2n in Hryx.
   now rewrite freal_mul_to_seq_i_comm in Hryx.
 +destruct Hyx as (k & Hjk & Hk); clear Hjk.
  unfold freal_mul in Heqyx; simpl in Heqyx.
  subst yx; simpl in Hk; simpl; unfold d2n in Hk.
  apply is_9_strict_after_false_iff in Hk.
  unfold d2n in Hk.
  rewrite freal_mul_to_seq_i_comm in Hk.
  unfold freal_mul in Heqxy; simpl in Heqxy.
  subst xy; simpl in Hxy; simpl.
  specialize (Hxy k).
  now apply is_9_strict_after_true_iff in Hxy.
-destruct Hxy as (k & Hjk & Hk).
 unfold freal_mul in Heqxy; simpl in Heqxy.
 unfold freal_mul in Heqyx; simpl in Heqyx.
 destruct (LPO_fst (is_9_strict_after yx i)) as [Hyx| Hyx].
 +exfalso; clear Hjk.
  subst xy yx; simpl in Hk, Hyx; simpl; unfold d2n in Hk.
  apply is_9_strict_after_false_iff in Hk.
  unfold d2n in Hk.
  rewrite freal_mul_to_seq_i_comm in Hk.
  specialize (Hyx k).
  now apply is_9_strict_after_true_iff in Hyx.
 +subst xy yx; simpl.
  apply freal_mul_to_seq_i_comm.
Qed.
*)

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

(* perhaps useless *)
Theorem freal_norm_unorm_add_comm {r : radix} : ∀ x y : FracReal,
  freal_eq (x + y) (y + x).
Proof.
intros.
unfold freal_eq.
unfold freal_norm_eq.
remember (freal_normalize (x + y)) as nxy eqn:Hnxy.
remember (freal_normalize (y + x)) as nyx eqn:Hnyx.
intros i.
subst nxy nyx; unfold fd2n; f_equal.
apply dig_norm_unorm_add_comm.
Qed.

(*
Theorem freal_add_comm {r : radix} : ∀ x y : FracReal, (x + y = y + x)%F.
Proof.
intros.
apply freal_norm_unorm_add_comm.
Qed.
*)

(*
Theorem freal_mul_comm {r : radix} : ∀ x y : FracReal, (x * y = y * x)%F.
Proof.
intros.
unfold freal_eq.
unfold freal_norm_eq.
remember (freal_normalize (x * y)) as nxy eqn:Hnxy.
remember (freal_normalize (y * x)) as nyx eqn:Hnyx.
destruct (LPO_fst (has_same_digits nxy nyx)) as [H| H]; [ easy | ].
exfalso.
destruct H as (i & Hji & Hi).
apply has_same_digits_false_iff in Hi.
apply Hi; clear Hi.
subst nxy nyx; unfold fd2n; f_equal.
apply dig_norm_mul_comm.
Qed.

Theorem freal_add_series_0_l {r : radix} : ∀ x i,
  freal_add_series 0 x i = fd2n x i.
Proof.
intros.
unfold "⊕"; simpl.
unfold sequence_add.
apply Nat.add_0_l.
Qed.

Theorem nA_freal_add_series {r : radix} : ∀ x y i n,
  nA i n (x ⊕ y) = nA i n (fd2n x) + nA i n (fd2n y).
Proof.
intros.
unfold nA; simpl.
unfold "⊕".
rewrite <- summation_add_distr; simpl.
apply summation_eq_compat.
intros j Hj.
apply Nat.mul_add_distr_r.
Qed.

Theorem nA_freal_add_series_0_l {r : radix} : ∀ x i n,
  nA i n (freal_add_series 0 x) = nA i n (fd2n x).
Proof.
intros.
unfold nA; simpl.
unfold "⊕"; simpl.
unfold sequence_add; simpl.
easy.
Qed.
*)

Theorem nA_split_first {r : radix} : ∀ i n u,
  i + 1 ≤ n - 1
  → nA i n u = u (i + 1) * rad ^ (n - i - 2) + nA (S i) n u.
Proof.
intros * Hin.
unfold nA.
rewrite summation_split_first; [ | easy ].
simpl; f_equal; f_equal; f_equal; flia.
Qed.

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

Theorem Nat_pow_ge_1 : ∀ a b, 0 < a → 1 ≤ a ^ b.
Proof.
intros * Ha.
induction b; [ easy | simpl ].
replace 1 with (1 * 1) by flia.
apply Nat.mul_le_mono_nonneg; [ flia | easy | flia | easy ].
Qed.

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

(*
Theorem freal_normalize_0 {r : radix} : ∀ i,
  dig (freal (freal_normalize 0) i) = 0.
Proof.
intros.
unfold fd2n; simpl.
unfold normalize; simpl.
destruct (LPO_fst (is_9_strict_after (λ _ : nat, digit_0) i)) as [H| H].
-specialize (H 0).
 specialize radix_ge_2 as Hr2.
 unfold is_9_strict_after in H.
 exfalso.
 destruct rad as [| rr]; [ easy | ].
 destruct rr; [ flia Hr2 | easy ].
-easy.
Qed.
*)

Theorem A_ge_1_false_iff {r : radix} : ∀ i u k,
  let n := rad * (i + k + 3) in
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
  let n := rad * (i + k + 3) in
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

Theorem all_lt_rad_A_ge_1_true_if {r : radix} : ∀ i u,
  (∀ k, u (S i + k) < rad)
  → (∀ k, A_ge_1 u i k = true)
  → ∀ j, u (S i + j) = rad - 1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu Hk *.
specialize (Hk j).
apply A_ge_1_true_iff in Hk.
remember (rad * (i + j + 3)) as n eqn:Hn.
remember (n - i - 1) as s eqn:Hs.
remember (S j) as sj eqn:Hsj.
move s before n.
assert (Hsz : rad ^ s ≠ 0) by now subst s; apply Nat.pow_nonzero.
rename Hk into HnA.
rewrite Nat.mod_small in HnA.
+apply when_99000_le_uuu00 with (i0 := i) (j0 := j) (n0 := n).
 *easy.
 *now rewrite <- Hs, <- Hsj.
 *rewrite Hn.
  destruct rad; [ easy | simpl; flia ].
 *flia.
+rewrite Hs.
 apply nA_dig_seq_ub.
 *intros k Hk.
  specialize (Hu (k - S i)).
  now replace (S i + (k - S i)) with k in Hu by flia Hk.
 *rewrite Hn.
  destruct rad; [ flia Hr | simpl in Hn; flia Hn ].
Qed.

Theorem prop_carr_normalize {r : radix} : ∀ x i,
  prop_carr (fd2n x) i = freal (freal_normalize x) i.
Proof.
intros.
specialize radix_ge_2 as Hr.
unfold prop_carr, freal_normalize, normalize; simpl.
apply digit_eq_eq; simpl.
unfold nat_prop_carr.
destruct (LPO_fst (A_ge_1 (fd2n x) i)) as [H1| H1]; simpl.
-assert (H : ∀ k : nat, fd2n x (S i + k) < rad). {
   intros; apply digit_lt_radix.
 }
 specialize (all_lt_rad_A_ge_1_true_if _ _ H H1) as H2; clear H H1.
 destruct (LPO_fst (is_9_strict_after (freal x) i)) as [H1| H1]; simpl.
 +specialize (is_9_strict_after_all_9 _ _ H1) as H3; clear H1.
  rewrite Nat.div_small.
  *destruct (lt_dec (S (d2n (freal x) i)) rad) as [H1| H1]; simpl.
  --unfold d2n in H1; unfold fd2n, d2n.
    rewrite Nat.mod_small; flia H1.
  --assert (H : d2n (freal x) i < rad) by apply digit_lt_radix.
    unfold d2n in H1, H; unfold fd2n, d2n.
    replace (dig (freal x i)) with (rad - 1) by flia H1 H.
    rewrite Nat.sub_add; [ | easy ].
    now rewrite Nat.mod_same.
  *apply nA_dig_seq_ub; [ intros; apply digit_lt_radix | ].
   destruct rad; [ easy | simpl; flia ].
 +destruct H1 as (j & Hjj & Hj).
  apply is_9_strict_after_false_iff in Hj.
  replace (i + j + 1) with (S i + j) in Hj by flia.
  unfold fd2n in H2; unfold d2n in Hj.
  now rewrite H2 in Hj.
-destruct H1 as (j & Hjj & Hj); simpl.
 destruct (LPO_fst (is_9_strict_after (freal x) i)) as [H1| H1]; simpl.
 +specialize (is_9_strict_after_all_9 _ _ H1) as H3; clear H1.
  apply A_ge_1_false_iff in Hj.
  remember (rad * (i + j + 3)) as n eqn:Hn.
  remember (n - i - 1) as s eqn:Hs.
  move s before n.
  replace (n - i - j - 2) with (s - S j) in Hj by flia Hs.
  exfalso; apply Nat.nle_gt in Hj; apply Hj; clear Hj.
  assert (Hin : i + 1 ≤ n - 1). {
    rewrite Hn.
    destruct rad; [ easy | simpl; flia ].
  }
  rewrite Nat.mod_small.
  *assert (H : nA i n (fd2n x) = rad ^ s - 1). {
     destruct s.
     -rewrite Hn in Hs.
      destruct rad; [ easy | simpl in Hs; flia Hs ].
     -unfold nA.
      rewrite power_summation_sub_1; [ | easy ].
      rewrite summation_rtl.
      rewrite summation_shift; [ | easy ].
      replace (n - 1 - (i + 1)) with s by flia Hs.
      rewrite summation_mul_distr_l.
      apply summation_eq_compat.
      intros k Hk; simpl.
      replace (n - 1 + (i + 1) - (i + 1 + k)) with (n - k - 1) by flia.
      replace (n - 1 - (n - k - 1)) with k by flia Hk Hs.
      f_equal.
      specialize (H3 (n - k - i - 2)).
      now replace (i + (n - k - i - 2) + 1) with (n - k - 1) in H3
        by flia Hk Hs Hin.
   }
   rewrite H; clear H.
   destruct s.
  --rewrite Hn in Hs.
    destruct rad; [ easy | simpl in Hs; flia Hs ].
  --rewrite Nat.sub_succ.
    remember (S j) as sj.
    rewrite power_summation_sub_1; [ | easy ].
    rewrite (summation_split _ _ (s - j - 1)); [ | flia ].
    rewrite Nat.add_comm.
    rewrite Nat.mul_add_distr_l.
    apply le_plus_trans.
    assert (Hjs : j < s). {
      apply Nat.succ_lt_mono; rewrite Hs, Hn.
      destruct rad; [ easy | simpl; flia ].
    }
    rewrite summation_shift; [ | flia Hjs ].
    rewrite <- Nat.sub_succ_l; [ | flia Hjs ].
    rewrite Nat.sub_succ, Nat.sub_0_r.
    subst sj.
    rewrite power_summation_sub_1; [ | easy ].
    rewrite <- Nat.mul_assoc.
    apply Nat.mul_le_mono_l.
    replace (s - (s - j)) with j by flia Hjs.
    rewrite summation_mul_distr_r; simpl.
    apply (@summation_le_compat nat_ord_ring_def).
    intros k Hk; simpl; unfold Nat.le.
    rewrite <- Nat.pow_add_r.
    now replace (k + (s - j)) with (s - j + k) by flia.
  *rewrite Hs.
   apply nA_dig_seq_ub; [ | easy ].
   intros; apply digit_lt_radix.
 +rewrite Nat.div_small.
  *rewrite Nat.add_0_r, Nat.mod_small; [ easy | ].
   apply digit_lt_radix.
  *apply nA_dig_seq_ub; [ intros; apply digit_lt_radix | ].
   destruct rad; [ easy | simpl; flia ].
Qed.

(*
Theorem freal_normalize_0_all_0 {r : radix} : ∀ i,
  fd2n (freal_normalize 0) i = 0.
Proof.
intros.
unfold fd2n, freal_normalize; simpl.
unfold normalize.
remember (λ _ : nat, digit_0) as u eqn:Hu.
destruct (LPO_fst (is_9_strict_after u i)) as [H1| H1]; [ | easy ].
specialize (H1 0).
apply is_9_strict_after_true_iff in H1.
rewrite Hu in H1; unfold d2n in H1; simpl in H1.
specialize radix_ge_2; flia H1.
Qed.

Theorem freal_add_normalize_0_l {r : radix} : ∀ x i,
  freal_add_to_seq (freal_normalize 0) (freal_normalize x) i =
  freal (freal_normalize x) i.
Proof.
intros.
unfold freal_add_to_seq.
set (u := freal_add_series (freal_normalize 0) (freal_normalize x)).
unfold prop_carr.
destruct (LPO_fst (A_ge_1 u i)) as [Hku| (m & Hjm & Hm)].
-exfalso.
 assert (H1 : ∀ k, u k < rad). {
   intros k.
   unfold u.
   unfold "⊕".
   rewrite freal_normalize_0_all_0, Nat.add_0_l.
   apply digit_lt_radix.
 }
 specialize (all_lt_rad_A_ge_1_true_if i u H1 Hku) as H2.
 assert (H3 : ∀ j, i < j → fd2n (freal_normalize x) j = rad - 1). {
   intros j Hj.
   specialize (H2 j Hj).
   unfold u in H2.
   unfold "⊕" in H2.
   now rewrite freal_normalize_0_all_0 in H2.
 }
 remember (freal_normalize x) as y eqn:Hy.
 assert (H4 : ∀ i, freal (freal_normalize x) i = freal y i). {
   intros j.
   now rewrite Hy.
 }
 specialize (proj1 (freal_normalized_iff x y) H4) as H5.
 destruct H5 as [H5| H5].
 +destruct H5 as (H5, H6).
  specialize (H5 (i + 1)) as (j & Hij & Hj).
  unfold fd2n in Hj.
  rewrite H6 in Hj.
  unfold fd2n in H3.
  rewrite H3 in Hj; flia Hij Hj.
 +unfold freal_norm_not_norm_eq in H5.
  destruct H5 as (j & Hbef & Hwhi & Hyaft & Hxaft).
  assert (H5 : i < max i j + 1). {
    eapply Nat.le_lt_trans; [ apply Nat.le_max_l with (m := j) | flia ].
  }
  specialize (H3 (max i j + 1) H5) as H6.
  assert (H7 : j ≤ max i j + 1). {
    eapply Nat.le_trans; [ apply Nat.le_max_l with (m := i) | flia ].
  }
  specialize (Hyaft (max i j + 1 - j)) as H8.
  replace (j + (max i j + 1 - j)) with (max i j + 1) in H8 by flia.
  rewrite H6 in H8.
  specialize radix_ge_2; flia H8.
-apply digit_eq_eq; simpl.
 set (n := rad * (i + m + 3)).
 set (s := rad ^ (n - 1 - i)).
 remember (u i) as uk eqn:Huk.
 unfold u, freal_add_series in Huk.
 unfold fd2n in Huk.
 rewrite freal_normalize_0 in Huk.
 simpl in Huk; subst uk.
 rewrite Nat.div_small; [ now rewrite Nat.add_0_r, Nat.mod_small | ].
 unfold nA.
 eapply Nat.le_lt_trans
 with (m := Σ (j = i + 1, n - 1), (rad - 1) * rad ^ (n - 1 - j)).
 +apply (@summation_le_compat nat_ord_ring_def).
  intros p Hp; simpl.
  unfold NPeano.Nat.le.
  apply Nat.mul_le_mono_r.
  unfold u, freal_add_series, fd2n.
  rewrite freal_normalize_0; simpl.
  apply digit_le_pred_radix.
 +unfold s.
  rewrite <- summation_mul_distr_l; simpl.
  rewrite summation_rtl.
  enough (H : i + 1 ≤ n - 1).
  *rewrite summation_shift; [ | easy ].
   rewrite summation_eq_compat with (h := λ i, rad ^ i).
  --rewrite <- power_summation_sub_1; [ | easy ].
    replace (S (n - 1 - (i + 1))) with (n - i - 1) by flia H.
    rewrite Nat_sub_sub_swap.
    apply Nat.sub_lt; [ | flia ].
    now apply Nat_pow_ge_1.
  --intros p Hp; f_equal; flia Hp.
  *unfold n.
   specialize radix_ne_0 as H.
   destruct rad as [| rr]; [ easy | ].
   simpl; flia.
Qed.

Theorem dig_norm_add_0_l {r : radix} : ∀ x i,
  freal (freal_normalize (0 + x)) i = freal (freal_normalize x) i.
Proof.
intros.
apply freal_normalized_iff.
destruct (LPO_fst (ends_with_999 (freal (0 + x)))) as [H0x| H0x].
-exfalso.
 specialize (H0x 0).
 apply ends_with_999_true_iff in H0x.
 destruct H0x as (j & (Hjj & Hj) & _).
 apply has_not_9_after_false_iff in Hj.
 destruct Hj as (Hj & _).
 assert (Hnr : ∀ k, dig (freal (freal_normalize x) (j + k)) = rad - 1). {
   intros k.
   specialize (Hj k).
   apply is_9_after_true_iff in Hj.
   unfold "+"%F, fd2n in Hj; simpl in Hj.
   unfold d2n in Hj.
   now rewrite freal_add_normalize_0_l in Hj.
 }
 clear -Hnr.
 assert (Hr : ∀ k, dig (freal x (j + k)) = rad - 1). {
   intros k.
   specialize (Hnr k) as H1.
   unfold freal_normalize, normalize in H1; simpl in H1.
   destruct (LPO_fst (is_9_strict_after (freal x) (j + k))) as [H2| H2].
   -destruct (lt_dec (S (d2n (freal x) (j + k))) rad) as [H3| H3].
    +simpl in H1; clear H3; exfalso.
     specialize (is_9_strict_after_all_9 _ _ H2) as H3.
     clear H2; rename H3 into H2.
     specialize (Hnr (k + 1)) as H3.
     unfold freal_normalize, normalize in H3; simpl in H3.
     destruct (LPO_fst (is_9_strict_after (freal x) (j + (k + 1)))) as
         [H4| H4].
     *destruct (lt_dec (S (d2n (freal x) (j + (k + 1)))) rad) as [H5| H5].
     --simpl in H3; clear H5.
       specialize (H2 0).
       replace (j + k + 0 + 1) with (j + (k + 1)) in H2; flia H2 H3.
     --simpl in H3.
       specialize radix_ge_2; flia H3.
     *clear H3.
      destruct H4 as (m & Hjm & H3).
      apply is_9_strict_after_false_iff in H3.
      specialize (H2 (m + 1)).
      replace (j + k + (m + 1) + 1) with (j + (k + 1) + m + 1) in H2.
     --easy.
     --flia H2.
    +simpl in H1.
     specialize radix_ge_2; flia H1.
   -easy.
 }
 specialize (Hnr 0).
 rewrite Nat.add_0_r in Hnr.
 unfold freal_normalize, normalize in Hnr; simpl in Hnr.
 destruct (LPO_fst (is_9_strict_after (freal x) j)) as [H1| H1].
 +destruct (lt_dec (S (d2n (freal x) j)) rad) as [H2| H2].
  *simpl in Hnr.
   specialize (Hr 0).
   rewrite Nat.add_0_r in Hr.
   unfold d2n in Hnr; flia Hnr Hr.
  *simpl in Hnr.
   specialize radix_ge_2; flia Hnr.
 +clear Hnr.
  destruct H1 as (i & Hji & H2).
  apply is_9_strict_after_false_iff in H2.
  specialize (Hr (i + 1)).
  now replace (j + (i + 1)) with (j + i + 1) in Hr by flia.
-destruct H0x as (j & _ & Hj).
 left.
 apply ends_with_999_false_iff in Hj.
 destruct Hj as (Hj & _).
 split.
 +intros k.
  specialize (Hj k).
  apply has_not_9_after_true_iff in Hj.
  destruct Hj as (m & (Hjm & Hm) & _).
  apply is_9_after_false_iff in Hm.
  exists (j + k + m).
  split; [ flia | ].
  specialize (digit_lt_radix (freal (0 + x) (j + k + m))) as H.
  unfold d2n in Hm; unfold fd2n; flia Hm H.
 +intros k.
  unfold freal_add; simpl.
  apply freal_add_normalize_0_l.
Qed.

Theorem freal_add_0_l {r : radix} : ∀ x, (0 + x = x)%F.
Proof.
intros.
unfold freal_eq, freal_norm_eq.
remember (freal_normalize (0%F + x)) as n0x eqn:Hn0x.
remember (freal_normalize x) as nx eqn:Hnx.
destruct (LPO_fst (has_same_digits n0x nx)) as [H| H]; [ easy | ].
exfalso.
destruct H as (i & Hji & Hi).
apply has_same_digits_false_iff in Hi.
apply Hi; clear Hi.
subst n0x nx; simpl.
unfold fd2n; f_equal.
apply dig_norm_add_0_l.
Qed.
*)

Require Import (*Morphisms*) Setoid.

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

Theorem prop_carr_shift {r : radix} : ∀ u n i,
  (∀ k, u (n + k) < rad)
  → prop_carr u (n + i) = prop_carr (λ j, u (n + j)) i.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu.
unfold prop_carr.
apply digit_eq_eq; simpl.
unfold nat_prop_carr.
destruct (LPO_fst (A_ge_1 u (n + i))) as [H1| H1].
-destruct (LPO_fst (A_ge_1 (λ j, u (n + j)) i)) as [H2| H2]; simpl.
 +rewrite Nat.div_small.
  *rewrite Nat.div_small; [ easy | ].
   apply nA_dig_seq_ub; [ intros; apply Hu | ].
   destruct rad; [ easy | simpl; flia ].
  *apply nA_dig_seq_ub.
  --intros l Hl.
    specialize (Hu (l - n)).
    now replace (n + (l - n)) with l in Hu by flia Hl.
  --destruct rad; [ easy | simpl; flia ].
 +destruct H2 as (j & Hjj & Hj).
  exfalso.
  apply A_ge_1_false_iff in Hj.
  remember (rad * (i + j + 3)) as n2 eqn:Hn2.
  remember (n2 - i - 1) as s2 eqn:Hs2.
  move s2 before n2.
  replace (n2 - i - j - 2) with (s2 - S j) in Hj by flia Hs2.
  specialize (all_lt_rad_A_ge_1_true_if (n + i) u) as H2.
  assert (H : ∀ k : nat, u (S (n + i) + k) < rad). {
    intros k.
    replace (S (n + i) + k) with (n + (S i + k)) by flia.
    apply Hu.
  }
  specialize (H2 H H1); clear H.
  apply Nat.nle_gt in Hj.
  apply Hj; clear Hj.
  rewrite Nat.mod_small.
  *apply (le_trans _ (rad ^ s2 - 1)).
  --rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
    rewrite <- Nat.pow_add_r.
    rewrite Nat.add_sub_assoc.
   ++rewrite Nat.add_comm, Nat.add_sub.
     apply Nat.sub_le_mono_l.
     now apply Nat_pow_ge_1.
   ++rewrite Hs2, Hn2.
     destruct rad; [ easy | simpl; flia ].
  --destruct s2; [ simpl; flia | ].
    unfold nA.
    rewrite summation_rtl, summation_shift.
   ++replace (n2 - 1 - (i + 1)) with s2 by flia Hs2.
     rewrite power_summation_sub_1; [ | easy ].
     rewrite summation_mul_distr_l; simpl.
     apply (@summation_le_compat nat_ord_ring_def).
     intros k Hk; simpl; unfold Nat.le.
     replace (n2 - 1 + (i + 1) - (i + 1 + k)) with (n2 - 1 - k) by flia.
     apply Nat.mul_le_mono.
    **specialize (H2 (s2 - k)).
      replace (S (n + i) + (s2 - k)) with (n + (n2 - 1 - k)) in H2
        by flia Hs2 Hk.
      now rewrite H2.
    **replace (n2 - 1 - (n2 - 1 - k)) with k; [ easy | ].
      rewrite Nat_sub_sub_swap.
      rewrite <- Nat.sub_add_distr.
      rewrite Nat_sub_sub_swap.
      rewrite Nat.sub_add; flia Hs2 Hk.
   ++rewrite Hn2.
     destruct rad; [ easy | simpl; flia ].
  *rewrite Hs2; apply nA_dig_seq_ub; [ intros; apply Hu | ].
   rewrite Hn2.
   destruct rad; [ easy | simpl; flia ].
-destruct H1 as (j & Hjj & Hj); simpl.
 destruct (LPO_fst (A_ge_1 (λ j, u (n + j)) i)) as [H1| H1]; simpl.
 +exfalso.
  apply A_ge_1_false_iff in Hj.
  remember (rad * (n + i + j + 3)) as n2 eqn:Hn2.
  remember (n2 - (n + i) - 1) as s2 eqn:Hs2.
  move s2 before n2.
  replace (n2 - (n + i) - j - 2) with (s2 - S j) in Hj by flia Hs2.
  assert (H : ∀ k, (λ j, u (n + j)) (S i + k) < rad). {
    intros k; apply Hu.
  }
  specialize (all_lt_rad_A_ge_1_true_if _ _ H H1) as H2.
  simpl in H2; clear H.
  apply Nat.nle_gt in Hj.
  apply Hj; clear Hj.
  rewrite Nat.mod_small.
  *apply (le_trans _ (rad ^ s2 - 1)).
  --rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
    rewrite <- Nat.pow_add_r.
    rewrite Nat.add_sub_assoc.
   ++rewrite Nat.add_comm, Nat.add_sub.
     apply Nat.sub_le_mono_l.
     now apply Nat_pow_ge_1.
   ++rewrite Hs2, Hn2.
     destruct rad; [ easy | simpl; flia ].
  --destruct s2; [ simpl; flia | ].
    unfold nA.
    rewrite summation_rtl, summation_shift.
   ++replace (n2 - 1 - (n + i + 1)) with s2 by flia Hs2.
     rewrite power_summation_sub_1; [ | easy ].
     rewrite summation_mul_distr_l; simpl.
     apply (@summation_le_compat nat_ord_ring_def).
     intros k Hk; simpl; unfold Nat.le.
     replace (n2 - 1 + (n + i + 1) - (n + i + 1 + k)) with (n2 - 1 - k)
       by flia.
     apply Nat.mul_le_mono.
    **specialize (H2 (s2 - k)).
      replace (n + S (i + (s2 - k))) with (n2 - 1 - k) in H2 by flia Hs2 Hk.
      now rewrite H2.
    **replace (n2 - 1 - (n2 - 1 - k)) with k; [ easy | ].
      rewrite Nat_sub_sub_swap.
      rewrite <- Nat.sub_add_distr.
      rewrite Nat_sub_sub_swap.
      rewrite Nat.sub_add; flia Hs2 Hk.
   ++rewrite Hn2.
     destruct rad; [ easy | simpl; flia ].
  *rewrite Hs2; apply nA_dig_seq_ub.
  --intros k Hk.
    specialize (Hu (k - n)).
    now replace (n + (k - n)) with k in Hu by flia Hk.
  --rewrite Hn2.
    destruct rad; [ easy | simpl; flia ].
 +destruct H1 as (k & Hjk & Hk); simpl.
  rewrite Nat.div_small.
  *rewrite Nat.div_small; [ easy | ].
   apply nA_dig_seq_ub; [ intros; apply Hu | ].
   destruct rad; [ easy | simpl; flia ].
  *apply nA_dig_seq_ub.
  --intros l Hl.
    specialize (Hu (l - n)).
    now replace (n + (l - n)) with l in Hu by flia Hl.
  --destruct rad; [ easy | simpl; flia ].
Qed.

Theorem prop_carr_eq_compat_from {r : radix} : ∀ f g n,
  (∀ i, f (n + i) < rad)
  → (∀ i, f (n + i) = g (n + i))
  → ∀ i, prop_carr f (n + i) = prop_carr g (n + i).
Proof.
intros * Hf Hfg i.
set (fi i := f (n + i)).
set (gi i := g (n + i)).
assert (H : ∀ i, fi i = gi i) by (intros; apply Hfg).
specialize (prop_carr_eq_compat _ _ H) as H1.
specialize (H1 i).
unfold fi, gi in H1.
rewrite <- prop_carr_shift in H1; [ | easy ].
rewrite <- prop_carr_shift in H1; [ easy | ].
intros j; rewrite <- Hfg; apply Hf.
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
-set (g j := if eq_nat_dec (u (i + j + 1)) (rad - 1) then true else false).
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
    specialize (Hu j) as H5.
    revert H5.
    apply Decidable.contrapositive; [ apply Nat.le_decidable | ].
    intros H5; apply Nat.nlt_ge in H5; clear H4.
    apply Bool.not_true_iff_false.
    apply A_ge_1_false_iff.
    remember (rad * (i + j + 3)) as n eqn:Hn.
    replace (n - i - j - 2) with (n - i - 1 - S j) by flia.
    remember (n - i - 1) as s eqn:Hs.
    move n before j; move s before n.
    assert (H6 : i + j + 3 ≤ n - 1). {
      rewrite Hn.
      destruct rad as [| rr]; [ easy | ].
      destruct rr; [ flia Hr | simpl; flia ].
    }
    assert (H7 : rad ^ s ≤ nA i n u). {
      (* 1/0/0/0 = 9/9/10, therefore 1/0/0/0/0/0/0 ≤ 9/9/10/x/x/x *)
      remember (i + j + 1) as t eqn:Ht.
      rewrite nA_split with (e := t + 1); [ | flia H6 Ht ].
      replace (t + 1 - 1) with t by flia.
      apply le_plus_trans.
      replace (rad ^ s) with
        (((rad ^ j - 1) * rad + rad) * rad ^ (n - (t + 1))).
      -apply Nat.mul_le_mono_r.
       rewrite nA_split_last; [ | flia Ht ].
       rewrite Nat.mul_comm, Nat.add_sub.
       apply Nat.add_le_mono; [ | easy ].
       apply Nat.mul_le_mono_l.
       destruct j; [ simpl; flia | ].
       unfold nA.
       rewrite summation_rtl.
       rewrite summation_shift; [ | flia Ht H6 ].
       replace (t - 1 - (i + 1)) with j by flia Ht.
       rewrite power_summation_sub_1; [ | easy ].
       rewrite summation_mul_distr_l.
       apply (@summation_le_compat nat_ord_ring_def).
       intros k Hk; simpl; unfold Nat.le.
       replace (t - 1 + (i + 1) - (i + 1 + k)) with (i + (j - k) + 1)
         by flia Ht Hk.
       replace (t - 1 - (i + (j - k) + 1)) with k by flia Ht Hk.
       apply Nat.mul_le_mono_r.
       rewrite H3; [ easy | flia ].
      -rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
       rewrite Nat.sub_add.
       +replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
        do 2 rewrite <- Nat.pow_add_r; f_equal.
        flia Ht Hs H6.
       +replace rad with (1 * rad) at 1 by flia.
        apply Nat.mul_le_mono_r.
        now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    specialize (nA_upper_bound_for_add u i n Hur) as H8.
    rewrite <- Hs in H8.
    replace (nA i n u) with (nA i n u - rad ^ s + 1 * rad ^ s) by flia H7.
    rewrite Nat.mod_add; [ | now apply Nat.pow_nonzero ].
    rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H8.
    specialize (Nat.pow_nonzero rad s radix_ne_0) as H9.
    rewrite Nat.mod_small; [ | flia H8 H9 ].
    apply Nat.add_lt_mono_r with (p := rad ^ s).
    rewrite Nat.sub_add; [ | easy ].
    rewrite nA_split with (e := i + j + 2); [ | flia H6 ].
    remember (i + j + 2) as t eqn:Ht.
    move t before s.
    replace (i + j + 3) with (i + j + 2 + 1) in Hn, H6 by flia.
    rewrite <- Ht in Hn, H6.
    replace (i + j + 1) with (t - 1) in H2, H5 by flia Ht.
    replace (s - S j) with (n - t) by flia Hs Ht.
    assert (H4 : nA i t u ≤ rad ^ S j + (rad - 2)). {
      destruct (Nat.eq_dec (i + 1) (t - 1)) as [H4| H4].
      -unfold nA.
       rewrite H4, summation_only_one.
       rewrite Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r.
       specialize (Hur 0) as H.
       rewrite Nat.add_0_r, H4 in H.
       eapply Nat.le_trans; [ apply H | ]; clear H.
       rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
       rewrite Nat.add_sub_assoc; [ | easy ].
       apply Nat.sub_le_mono_r.
       replace rad with (rad * 1) at 3 by flia.
       rewrite Nat.pow_succ_r; [ | flia ].
       rewrite <- Nat.mul_add_distr_l.
       rewrite Nat.mul_comm.
       apply Nat.mul_le_mono_l.
       rewrite Nat.add_1_r.
       apply -> Nat.succ_le_mono.
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
      -rewrite nA_split_last; [ | flia H6 Ht ].
       specialize (nA_dig_seq_ub u (t - 1) i) as H10.
       assert (H : ∀ j, i < j < t - 1 → u j < rad). {
         intros k Hk.
         specialize (H3 (k - i - 1)).
         assert (H : k - i - 1 < j) by flia H6 Ht Hk.
         specialize (H3 H); clear H.
         replace (i + (k - i - 1) + 1) with k in H3 by flia Hk.
         flia Hr H3.
       }
       specialize (H10 H); clear H.
       assert (H : i + 1 ≤ t - 1 - 1) by flia Hs H6 Ht H4.
       specialize (H10 H); clear H.
       replace (t - 1 - i - 1) with j in H10 by flia Ht.
       replace (rad ^ S j + (rad - 2)) with (rad ^ S j - rad + 2 * (rad - 1)).
       +specialize (Hur (t - i - 2)) as H.
        replace (i + (t - i - 2) + 1) with (t - 1) in H by flia Ht.
        apply Nat.add_le_mono; [ | apply H ]; clear H.
        replace rad with (rad * 1) at 3 by flia.
        simpl; rewrite <- Nat.mul_sub_distr_l.
        apply Nat.mul_le_mono_l.
        flia H10.
       +rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
        replace (2 * rad) with (rad + rad) by flia.
        rewrite Nat.add_sub_assoc; [ | flia Hr ].
        rewrite Nat.add_assoc.
        rewrite Nat.sub_add.
        *now rewrite Nat.add_sub_assoc.
        *simpl.
         replace rad with (rad * 1) at 1 by flia.
         apply Nat.mul_le_mono_l.
         now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    apply Nat.le_lt_trans with
      (m := (rad ^ S j + (rad - 2)) * rad ^ (n - t) + nA (t - 1) n u).
    -apply Nat.add_le_mono_r.
     now apply Nat.mul_le_mono.
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
        intros k.
        replace (t - 1 + k + 1) with (i + (j + k + 1) + 1) by flia Ht.
        apply Hur.
      --replace (n - (t - 1) - 1) with (n - t) by flia Ht.
        apply -> Nat.lt_add_lt_sub_l.
        rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
        rewrite Nat.add_sub_assoc.
       ++rewrite <- Nat.mul_add_distr_r.
         replace (rad - 1 + 2) with (rad + 1) by flia Hr.
         replace s with (j + 1 + (n - t)) by flia Hs H6 Ht.
         rewrite Nat.pow_add_r.
         apply Nat.lt_le_trans with (m := (rad + 1) * rad ^ (n - t)).
        **apply Nat.sub_lt; [ | flia ].
          specialize (Nat.pow_nonzero rad (n - t) radix_ne_0) as H10.
          destruct (rad ^ (n - t)); [ easy | ].
          destruct rad as [| rr]; [ easy | ].
          destruct rr; [ flia Hr | ].
          simpl; flia.
        **apply Nat.mul_le_mono_r.
          destruct j.
        ---rewrite Nat.add_0_r in Ht.
           rewrite Ht in H2.
           now replace (i + 2 - 1) with (i + 1) in H2 by flia.
        ---do 2 rewrite Nat.add_1_r; simpl.
           specialize (Nat.pow_nonzero rad j radix_ne_0) as H10.
           destruct (rad ^ j); [ easy | ].
           destruct rad as [| rr]; [ easy | ].
           rewrite Nat.mul_comm, <- Nat.mul_assoc.
           destruct rr; [ flia Hr | simpl; flia ].
       ++specialize (Nat.pow_nonzero rad (n - t) radix_ne_0) as H10.
         destruct (rad ^ (n - t)); [ easy | flia ].
      *apply Nat.pow_le_mono_r; [ easy | flia Hs Ht ].
     +replace (rad ^ (n - t)) with (1 * rad ^ (n - t)) at 1 by flia.
      apply Nat.mul_le_mono_r.
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
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

Theorem add_norm_0_l {r : radix} : ∀ y n nx nxy,
  (∀ i : nat, fd2n nx (n + i) = 0)
  → (∀ i : nat, ∃ j : nat, fd2n y (i + j) ≠ rad - 1)
  → nxy = freal_add nx y
  → ∀ i, n ≤ i
  → fd2n (freal_normalize nxy) i = fd2n (freal_normalize y) i.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hnaft Hy Hnxy i Hni.
unfold fd2n; f_equal.
apply (freal_eq_normalize_eq n); [ | easy ].
intros j Hj.
rewrite Hnxy.
unfold freal_add; simpl.
unfold prop_carr.
apply digit_eq_eq; simpl.
unfold nat_prop_carr.
destruct (LPO_fst (A_ge_1 (nx ⊕ y) j)) as [H1| H1].
-exfalso.
 specialize (A_ge_1_add_all_true_if (nx ⊕ y) j) as H2.
 assert (H : ∀ k : nat, (nx ⊕ y) (j + k + 1) ≤ 2 * (rad - 1)). {
   intros k; apply freal_add_series_le_twice_pred.
 }
 specialize (H2 H H1); clear H.
 destruct H2 as [H2| [H2| H2]].
 +specialize (Hy (j + 1)) as H3; destruct H3 as (k & Hk).
  specialize (H2 k).
  unfold "⊕" in H2.
  specialize (Hnaft (j + k + 1 - n)) as H3.
  rewrite Nat.add_comm, Nat.sub_add in H3; [ | flia Hj ].
  rewrite Nat.add_shuffle0 in Hk.
  now rewrite H3, Nat.add_0_l in H2.
 +specialize (Hy (j + 1)) as H3; destruct H3 as (k & Hk).
  specialize (H2 k).
  unfold "⊕" in H2.
  specialize (Hnaft (j + k + 1 - n)) as H3.
  rewrite Nat.add_comm, Nat.sub_add in H3; [ | flia Hj ].
  rewrite Nat.add_shuffle0 in Hk.
  rewrite H3, Nat.add_0_l in H2.
  unfold fd2n in H2.
  specialize (digit_lt_radix (freal y (j + k + 1))) as H.
  flia Hr H H2.
 +destruct H2 as (m & Hmbef & Hmwhi & Hmaft).
  specialize (Hmaft i) as H2.
  unfold "⊕" in H2.
  specialize (Hnaft (j + m + i + 2 - n)) as H3.
  rewrite Nat.add_comm, Nat.sub_add in H3; [ | flia Hni ].
  rewrite H3, Nat.add_0_l in H2.
  unfold fd2n in H2.
  specialize (digit_lt_radix (freal y (j + m + i + 2))) as H.
  flia Hr H H2.
-destruct H1 as (k & Hjk & Hk).
 unfold "⊕" at 1.
 specialize (Hnaft (j - n)) as H1.
 replace (n + (j - n)) with j in H1 by flia Hj.
 rewrite H1, Nat.add_0_l; clear H1.
 remember (rad * (j + k + 3)) as n1 eqn:Hn1.
 remember (n1 - j - 1) as s1 eqn:Hs1.
 rewrite Nat.div_small.
 +rewrite Nat.add_0_r.
  rewrite Nat.mod_small; [ easy | ].
  apply digit_lt_radix.
 +subst s1.
  apply nA_dig_seq_ub.
  *intros m Hm.
   unfold "⊕".
   specialize (Hnaft (m - n)) as H1.
   replace (n + (m - n)) with m in H1 by flia Hm Hj.
   rewrite H1, Nat.add_0_l.
   apply digit_lt_radix.
  *rewrite Hn1.
   destruct rad; [ easy | simpl; flia ].
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
