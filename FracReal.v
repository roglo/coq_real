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

Definition digit_sequence_normalize {r : radix} (u : nat → digit) i :=
  match LPO_fst (is_9_strict_after u i) with
  | inl _ =>
     match lt_dec (S (d2n u i)) rad with
     | left P => mkdig _ (S (d2n u i)) P
     | right _ => digit_0
     end
  | inr _ => u i
 end.

Definition freal_normalize {r : radix} x :=
  {| freal i := digit_sequence_normalize (freal x) i |}.

Arguments freal_normalize r x%F.

Definition has_same_digits {r : radix} x y i :=
  if Nat.eq_dec (fd2n x i) (fd2n y i) then true else false.

Definition freal_norm_eq {r : radix} x y := ∀ i, fd2n x i = fd2n y i.
Arguments freal_norm_eq _ x%F y%F.

Definition freal_eq {r : radix} x y :=
  freal_norm_eq (freal_normalize x) (freal_normalize y).

Arguments freal_eq _ x%F y%F.

(*
Definition freal_lt {r : radix} x y :=
  freal_norm_lt (freal_normalize x) (freal_normalize y).

Definition freal_0 {r : radix} := {| freal i := digit_0 |}.

Notation "0" := (freal_0) : freal_scope.
*)
Notation "a = b" := (freal_eq a b) : freal_scope.
(*
Notation "a ≠ b" := (¬ freal_eq a b) : freal_scope.
Notation "a < b" := (freal_lt a b) : freal_scope.
*)

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
   unfold freal_normalize, digit_sequence_normalize in Hxy.
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
   **unfold freal_normalize, digit_sequence_normalize in Hxy1; simpl in Hxy1.
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
       unfold freal_normalize, digit_sequence_normalize in Hxy2.
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
         unfold freal_normalize, digit_sequence_normalize in Hxy.
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
         unfold freal_normalize, digit_sequence_normalize in Hxy.
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
    unfold digit_sequence_normalize in Hk.
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
      unfold freal_normalize, digit_sequence_normalize in Hxy1.
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
      unfold freal_normalize, digit_sequence_normalize in Hk'.
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
  unfold freal_normalize, digit_sequence_normalize; simpl.
  destruct (LPO_fst (is_9_strict_after (freal x) i)) as [Hxi| Hxi].
  *specialize (Hki (S i)) as (j & H1j & Hj); unfold fd2n in Hj.
   specialize (Hxi (j - i - 1)).
   apply is_9_strict_after_true_iff in Hxi; unfold d2n in Hxi.
   replace (i + (j - i - 1) + 1) with j in Hxi; flia Hxi Hj H1j.
  *apply Hxy.
 +unfold freal_norm_not_norm_eq in Hxy.
  destruct Hxy as (k & Hik & Hxy & Hx & Hy).
  unfold freal_normalize, digit_sequence_normalize; simpl.
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
unfold freal_normalize, digit_sequence_normalize; simpl.
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
unfold freal_normalize, digit_sequence_normalize; simpl.
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

Definition ends_with_000 {r : radix} u i :=
  match LPO_fst (has_not_0_after u i) with
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

Theorem ends_with_000_true_iff {r : radix} : ∀ u i,
  ends_with_000 u i = true ↔
  ∃ j P, LPO_fst (has_not_0_after u i) = inr (exist _ j P).
Proof.
intros.
split.
-intros H9.
 unfold ends_with_000 in H9.
 destruct (LPO_fst (has_not_0_after u i)) as [H1| H1]; [ easy | clear H9 ].
 destruct H1 as (j & Hjj).
 now exists j, Hjj.
-intros (j & ((P & Q) & _)).
 unfold ends_with_000.
 destruct (LPO_fst (has_not_0_after u i)) as [H1| H1]; [ | easy ].
 specialize (H1 j).
 now rewrite H1 in Q.
Qed.

Theorem ends_with_000_false_iff {r : radix} : ∀ u i,
  ends_with_000 u i = false ↔
  ∃ P, LPO_fst (has_not_0_after u i) = inl P.
Proof.
intros.
split.
-intros H9.
 unfold ends_with_000 in H9.
 destruct (LPO_fst (has_not_0_after u i)) as [H1| H1]; [ clear H9 | easy ].
 now exists H1.
-intros (P & _).
 unfold ends_with_000.
 destruct (LPO_fst (has_not_0_after u i)) as [H1| H1]; [ easy | ].
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
unfold digit_sequence_normalize.
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
  unfold digit_sequence_normalize in H1.
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
  let n := rad * (i + k + 2) in
  let s := n - i - 1 in
  if lt_dec (nA i n u mod rad ^ s) ((rad ^ S k - 1) * rad ^ (s - S k)) then
    false
  else
    true.

(* Propagation of Carries *)

(* for addition, all A_ge_1 implies u i followed by either
   - 9/9/9/9...
   - 18/18/18/...
   - 9/9/9...9/8/18/18/18...
   for multiplication, to be determined...
 *)

Definition nat_prop_carr {r : radix} u i :=
  match LPO_fst (A_ge_1 u i) with
  | inl _ =>
      let n := rad * (i + 2) in
      let s := rad ^ (n - i - 1) in
      u i + 1 + nA i n u / s
  | inr (exist _ l _) =>
      let n := rad * (i + l + 2) in
      let s := n - i - 1 in
      u i + nA i n u / rad ^ s
  end.

Definition prop_carr {r : radix} u i :=
  let d := nat_prop_carr u i in
  mkdig _ (d mod rad) (Nat.mod_upper_bound d rad radix_ne_0).

(*
Definition freal_mul_to_seq {r : radix} (a b : FracReal) :=
  prop_carr (freal_mul_series a b).
*)

Definition freal_add {r : radix} x y := {| freal := prop_carr (x ⊕ y) |}.
Arguments freal_add _ x%F y%F.

Print freal_add.

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
destruct (LPO_fst (A_ge_1 (x ⊕ y) i)) as [Hxy| Hxy].
-setoid_rewrite freal_add_series_comm.
 destruct (LPO_fst (A_ge_1 (y ⊕ x) i)) as [Hyx| Hyx].
 +f_equal; f_equal; f_equal.
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
unfold digit_sequence_normalize.
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
unfold digit_sequence_normalize.
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
unfold digit_sequence_normalize; simpl.
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
  let n := rad * (i + k + 2) in
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
  let n := rad * (i + k + 2) in
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

(*
Theorem Nat_pow_succ_pow : ∀ a b, a ^ S b = (a ^ b - 1) * a + a.
Proof.
intros; simpl.
destruct a; [ now rewrite Nat.mul_0_r; simpl | ].
rewrite Nat.mul_sub_distr_r.
rewrite Nat.mul_1_l.
rewrite Nat.sub_add; [ flia | ].
induction b; [ simpl; flia | ].
simpl.
eapply le_trans; [ apply IHb | ].
apply Nat.mul_le_mono_r; flia.
Qed.

Theorem all_A_ge_1_true_iff {r : radix} : ∀ i u,
  (∀ k, A_ge_1 u i k = true) ↔
  ∀ k,
  let n := rad * (i + k + 2) in
  let s := rad ^ (n - i - 1) in
  nA i n u mod s ≥ (rad ^ S k - 1) * rad ^ (n - i - k - 2).
Proof.
intros.
split.
-intros Hk *.
 specialize (Hk k).
 now apply A_ge_1_true_iff in Hk.
-intros Hk *.
 specialize (Hk k).
 now apply A_ge_1_true_iff.
Qed.
*)

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
remember (rad * (i + j + 2)) as n eqn:Hn.
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
unfold prop_carr, freal_normalize, digit_sequence_normalize; simpl.
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
  *rewrite Nat.add_0_r.
   destruct (lt_dec (S (d2n (freal x) i)) rad) as [H1| H1]; simpl.
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
  remember (rad * (i + j + 2)) as n eqn:Hn.
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
      destruct rad as [| rr]; [ easy | simpl ].
      destruct rr; [ flia Hr | simpl; flia ].
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
unfold digit_sequence_normalize.
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
 set (n := rad * (i + m + 2)).
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
   unfold freal_normalize, digit_sequence_normalize in H1; simpl in H1.
   destruct (LPO_fst (is_9_strict_after (freal x) (j + k))) as [H2| H2].
   -destruct (lt_dec (S (d2n (freal x) (j + k))) rad) as [H3| H3].
    +simpl in H1; clear H3; exfalso.
     specialize (is_9_strict_after_all_9 _ _ H2) as H3.
     clear H2; rename H3 into H2.
     specialize (Hnr (k + 1)) as H3.
     unfold freal_normalize, digit_sequence_normalize in H3; simpl in H3.
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
 unfold freal_normalize, digit_sequence_normalize in Hnr; simpl in Hnr.
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
  remember (rad * (i + j + 2)) as n2 eqn:Hn2.
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
  remember (rad * (n + i + j + 2)) as n2 eqn:Hn2.
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

Theorem freal_eq_normalized_eq {r : radix} : ∀ x y,
  (x = y)%F ↔
  (∀ i, freal (freal_normalize x) i = freal (freal_normalize y) i).
Proof.
intros.
unfold freal_eq, freal_norm_eq.
split; intros Hxy *; apply digit_eq_eq, Hxy.
Qed.

Theorem Nat_mul_pow_sub_1_pow : ∀ a b c,
  (a ^ S b - 1) * a ^ c = (a ^ b - 1) * a ^ c + (a - 1) * a ^ (b + c).
Proof.
intros.
destruct a; [ now destruct b | ].
do 3 rewrite Nat.mul_sub_distr_r.
do 2 rewrite Nat.mul_1_l.
symmetry.
rewrite <- Nat.pow_add_r.
rewrite Nat.add_sub_assoc.
-rewrite <- Nat.add_sub_swap.
 +rewrite Nat_sub_sub_swap.
  rewrite Nat.add_sub_swap; [ | easy ].
  rewrite Nat.sub_diag, Nat.add_0_l.
  now rewrite Nat.pow_add_r, Nat.mul_assoc.
 +replace (S a ^ c) with (1 * S a ^ c) by apply Nat.mul_1_l.
  rewrite Nat.pow_add_r.
  apply Nat.mul_le_mono_r.
  apply Nat.neq_0_lt_0.
  now apply Nat.pow_nonzero.
-replace (S a ^ (b + c)) with (1 * S a ^ (b + c)) at 1 by apply Nat.mul_1_l.
 apply Nat.mul_le_mono_r.
 apply -> Nat.succ_le_mono.
 apply Nat.le_0_l.
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

(*
Theorem all_le_nA_le {r : radix} : ∀ u a i n,
  (∀ j, i < j < n → u j ≤ a * (rad - 1))
  → nA i n u ≤ a * (rad ^ (n - i - 1) - 1).
Proof.
intros * Hur *.
remember (n - i - 1) as m eqn:Hm.
symmetry in Hm.
destruct m.
-unfold nA.
 rewrite summation_empty; [ simpl; flia | flia Hm ].
-rewrite power_summation; [ | easy ].
 rewrite Nat.add_comm, Nat.add_sub.
 rewrite summation_mul_distr_l.
 rewrite summation_mul_distr_l; simpl.
 unfold nA.
 rewrite summation_rtl.
 rewrite summation_shift; [ | flia Hm ].
 replace (n - 1 - (i + 1)) with m by flia Hm.
 apply (@summation_le_compat nat_ord_ring_def).
 simpl.
 unfold Nat.le.
 intros j Hj.
 replace (n - 1 + (i + 1) - (i + 1 + j)) with (n - 1 - j) by flia.
 replace (n - 1 - (n - 1 - j)) with j by flia Hm Hj.
 rewrite Nat.mul_assoc.
 apply Nat.mul_le_mono_r, Hur; flia Hm Hj.
Qed.

Theorem Nat_mul_succ_le_eucl_div : ∀ a b c r,
  b * c ≤ a < b * (c + 1)
  → r = a - b * c
  → r < b ∧ a = b * c + r.
Proof.
intros * Habc Hr.
flia Habc Hr.
Qed.

Theorem Nat_mul_succ_le_div : ∀ a b c,
  b * c ≤ a < b * (c + 1)
  → a / b = c.
Proof.
intros * Habc.
destruct b; [ easy | ].
assert (Hb : S b ≠ 0) by flia.
remember (S b) as b' eqn:Hb'.
clear b Hb'; rename b' into b.
move Hb after Habc.
remember (a - b * c) as r eqn:Hr.
specialize (Nat_mul_succ_le_eucl_div a b c r Habc Hr) as (H1, H2).
rewrite H2, Nat.add_comm, Nat.mul_comm.
rewrite Nat.div_add; [ | easy ].
now rewrite Nat.div_small.
Qed.

Theorem Nat_ge_mul_pred_pow_pow : ∀ r a b c t,
  a < r ^ (b + c)
  → a ≥ (r ^ b - 1) * r ^ c
  → t = a - (r ^ b - 1) * r ^ c
  → t < r ^ c ∧ a = (r ^ b - 1) * r ^ c + t.
Proof.
intros * Halt Hage Ht.
destruct b. {
  simpl in Halt, Hage, Ht |-*.
  flia Halt Ht.
}
destruct r. {
  rewrite Nat.pow_0_l in Halt; [ easy | flia ].
}
remember (S b) as b' eqn:Hb'.
assert (Hb : b' ≠ 0) by flia Hb'.
clear b Hb'; rename b' into b.
remember (S r) as r' eqn:Hr'.
assert (Hr : r' ≠ 0) by flia Hr'.
clear r Hr'; rename r' into r.
revert r a c t Hr Halt Hage Ht.
induction b; intros; [ easy | clear Hb ].
destruct b.
-rewrite Nat.pow_1_r in Hage |-*.
 simpl in Halt.
 specialize (Nat_mul_succ_le_eucl_div a (r ^ c) (r - 1)) as H.
 specialize (H t).
 rewrite Nat.sub_add in H; [ | flia Hr ].
 assert (H1 : r ^ c * (r - 1) ≤ a < r ^ c * r) by flia Halt Hage.
 rewrite Nat.mul_comm, Nat.pow_1_r in Ht.
 specialize (H H1 Ht); clear H1.
 split; [ easy | flia H ].
-specialize (IHb (Nat.neq_succ_0 b) r).
 specialize (Nat_mul_succ_le_eucl_div a (r ^ c)) as H.
 specialize (H (r ^ S (S b) - 1)).
 rewrite Nat.sub_add in H; [ | apply Nat_pow_ge_1; flia Hr ].
 rewrite Nat.mul_comm.
 rewrite Nat.pow_add_r in Halt.
 specialize (H t).
 apply H.
 +split; [ flia Hage | flia Halt ].
 +flia Ht.
Qed.

Theorem old_Nat_ge_mul_pred_pow_pow : ∀ r a b c,
  a < r ^ (b + c)
  → a ≥ (r ^ b - 1) * r ^ c
  → a / r ^ c = r ^ b - 1.
Proof.
intros * Halt Hage.
destruct b. {
  simpl in Halt, Hage |-*.
  now rewrite Nat.div_small.
}
destruct r. {
  rewrite Nat.pow_0_l in Halt; [ easy | flia ].
}
remember (S b) as b' eqn:Hb'.
assert (Hb : b' ≠ 0) by flia Hb'.
clear b Hb'; rename b' into b.
remember (S r) as r' eqn:Hr'.
assert (Hr : r' ≠ 0) by flia Hr'.
clear r Hr'; rename r' into r.
revert r a c Hr Halt Hage.
induction b; intros; [ easy | clear Hb ].
destruct b.
-rewrite Nat.pow_1_r in Hage |-*.
 simpl in Halt.
 specialize (Nat_mul_succ_le_div a (r ^ c) (r - 1)) as H.
 apply H.
 split; [ flia Hage | ].
 replace (r - 1 + 1) with r by flia Hr.
 flia Halt.
-specialize (IHb (Nat.neq_succ_0 b)).
 apply Nat_mul_succ_le_div.
 split; [ flia Hage | ].
 rewrite Nat.sub_add.
 +rewrite Nat.pow_add_r in Halt.
  flia Halt.
 +apply Nat_pow_ge_1; flia Hr.
Qed.

Theorem A_ge_1_all_true_if {r : radix} : ∀ u i,
  (∀ k, A_ge_1 u i k = true)
  → ∀ k,
     let n := rad * (i + k + 2) in
     let s := rad ^ (n - i- 1) in
     let t := rad ^ (n - i - k - 2) in
     let m := nA i n u mod s - (rad ^ S k - 1) * t in
     m < t ∧
     nA i n u mod s = (rad ^ S k - 1) * t + m.
Proof.
intros * H1 *.
specialize (proj1 (all_A_ge_1_true_iff i u) H1 k) as H2.
remember (S k) as x; simpl in H2; subst x.
fold n s t in H2.
apply Nat_ge_mul_pred_pow_pow; [ | easy | easy ].
replace (S k + (n - i - k - 2)) with (n - i - 1).
-apply Nat.mod_upper_bound.
 now apply Nat.pow_nonzero.
-unfold n.
 specialize radix_ge_2 as Hr.
 destruct rad; [ easy | simpl; flia ].
Qed.

Theorem old_A_ge_1_all_true_if {r : radix} : ∀ u i,
  (∀ k, A_ge_1 u i k = true)
  → ∀ k,
     let n := rad * (i + k + 2) in
     let s := rad ^ (n - i- 1) in
     let t := rad ^ (n - i - k - 2) in
     nA i n u mod s / t = rad ^ S k - 1.
Proof.
intros * H1 *.
specialize (proj1 (all_A_ge_1_true_iff i u) H1 k) as H2.
remember (S k) as x; simpl in H2; subst x.
fold n s t in H2.
assert (HnA : nA i n u mod s < rad ^ (S k + (n - i - k - 2))). {
  assert (Hsz : s ≠ 0) by now apply Nat.pow_nonzero.
  replace (S k + (n - i - k - 2)) with (n - i - 1).
  -now apply Nat.mod_upper_bound.
  -unfold n.
   specialize radix_ge_2 as Hr.
   destruct rad; [ easy | simpl; flia ].
}
specialize (old_Nat_ge_mul_pred_pow_pow rad (nA i n u mod s) (S k)) as H.
specialize (H (n - i - k - 2) HnA H2).
easy.
Qed.

Theorem nA_le_norm {r : radix} : ∀ x i n,
 fd2n x (i + 1) ≤ fd2n (freal_normalize x) (i + 1)
 → nA i n (fd2n x) ≤ nA i n (fd2n (freal_normalize x)).
Proof.
intros * Hin.
unfold nA, summation.
replace (S (n - 1) - (i + 1)) with (n - i - 1) by lia.
remember (n - i - 1) as m eqn:Hm.
revert i n Hin Hm.
induction m; intros; [ easy | ].
destruct (le_dec (fd2n x (S i + 1)) (fd2n (freal_normalize x) (S i + 1)))
  as [H1| H1].
-simpl.
 apply Nat.add_le_mono.
 +apply Nat.mul_le_mono_pos_r; [ | easy ].
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +replace (S (i + 1)) with (S i + 1) by flia.
  apply IHm; [ easy | flia Hm ].
-apply Nat.nle_gt in H1.
 assert (H2 : fd2n x (i + 1) < fd2n (freal_normalize x) (i + 1)). {
   apply Nat.nle_gt; intros H2.
   assert (H3 : fd2n x (i + 1) = fd2n (freal_normalize x) (i + 1)). {
     flia Hin H2.
   }
   clear Hin H2.
   unfold freal_normalize, fd2n in H3; simpl in H3.
   unfold digit_sequence_normalize in H3.
   destruct (LPO_fst (is_9_strict_after (freal x) (i + 1))) as [H4| H4].
   -destruct (lt_dec (S (d2n (freal x) (i + 1))) rad) as [H5| H5].
    +unfold d2n in H3; simpl in H3; flia H3.
    +apply Nat.nlt_ge in H5.
     unfold d2n in H5; simpl in H3.
     rewrite H3 in H5.
     specialize radix_ge_2; flia H5.
   -destruct H4 as (j & Hjj & Hj).
    apply is_9_strict_after_false_iff in Hj.
    clear H3.
    unfold freal_normalize, fd2n in H1; simpl in H1.
    unfold digit_sequence_normalize in H1.
    destruct (LPO_fst (is_9_strict_after (freal x) (S (i + 1)))) as [H2| H2].
    +destruct (lt_dec (S (d2n (freal x) (S (i + 1)))) rad) as [H4| H4].
     *unfold d2n in H1; simpl in H1; flia H1.
     *apply Nat.nlt_ge in H4.
      destruct j.
     --replace (i + 1 + 0 + 1) with (S (i + 1)) in Hj by flia.
       unfold d2n in H4, Hj.
       specialize (digit_lt_radix (freal x (S (i + 1)))) as H.
       flia H4 Hj H.
     --specialize (H2 j).
       apply is_9_strict_after_true_iff in H2.
       replace (i + 1 + S j + 1) with (S (i + 1) + j + 1) in Hj by flia.
       easy.
    +flia H1.
 }
 clear Hin.
 simpl.
 apply Nat.le_trans with
   (m := fd2n (freal_normalize x) (i + 1) * rad ^ (n - 1 - (i + 1))); [ | flia ].
 replace (n - 1 - (i + 1)) with (n - i - 2) by flia.
 remember (fd2n x (i + 1)) as a eqn:Ha.
 remember (fd2n (freal_normalize x) (i + 1)) as b eqn:Hb.
 move b before a.
 destruct b; [ easy | ].
 rewrite Nat.mul_succ_l.
 apply Nat.add_le_mono.
 +apply Nat.mul_le_mono_pos_r; [ | flia H2 ].
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +remember (n - i - 2) as k eqn:Hk.
  symmetry in Hk.
  destruct k.
  *rewrite Nat.pow_0_r.
   destruct m; [ simpl; flia H2 | flia Hm Hk ].
  *rewrite power_summation; [ | easy ].
   rewrite summation_mul_distr_l.
   rewrite summation_aux_shift.
   rewrite summation_aux_rtl.
   unfold summation.
   replace (S k - 0) with m by flia Hm Hk; simpl.
   apply Nat.le_le_succ_r.
   apply (@summation_aux_le_compat nat_ord_ring_def).
   intros j Hj; simpl; unfold Nat.le.
   rewrite Nat.add_0_r.
   replace (n - 1 - S (i + 1 + (m - 1 - j))) with j by flia Hm Hj.
   apply Nat.mul_le_mono_r.
   apply digit_le_pred_radix.
Qed.
*)

(*
Theorem nA_succ_r {r : radix} : ∀ i n u,
  i + 1 ≤ n - 1
  → nA i (S n) u = rad * nA i n u + u n.
Proof.
intros * Hin.
destruct n; [ flia Hin | ].
unfold nA.
replace (S (S n) - 1) with (S n) by flia.
rewrite summation_split_last; [ | flia Hin ].
replace (S n - 1) with n by flia.
rewrite Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r.
remember minus as f; simpl; subst f.
f_equal.
rewrite summation_mul_distr_l.
apply summation_eq_compat.
intros j Hj.
remember minus as f; simpl; subst f.
symmetry; rewrite Nat.mul_comm, <- Nat.mul_assoc.
f_equal.
replace (S n - j) with (n - j + 1) by flia Hj.
now rewrite Nat.pow_add_r, Nat.pow_1_r.
Qed.

Theorem nA_freal_normalize {r : radix} : ∀ x i n,
  nA i n (fd2n (freal_normalize x)) = nA i n (fd2n x)
  ∨ nA i n (fd2n (freal_normalize x)) = nA i n (fd2n x) + 1
  ∨ nA i n (fd2n (freal_normalize x)) = 0.
Proof.
intros.
destruct (lt_dec (n - 1) (i + 1)) as [Hin| Hin]. {
  left.
  unfold nA.
  now rewrite summation_empty; [ rewrite summation_empty | ].
}
apply Nat.nlt_ge in Hin.
destruct (LPO_fst (is_9_strict_after (freal x) i)) as [H1| H1].
-right; right.
 specialize (is_9_strict_after_all_9 (freal x) i H1) as H2.
 unfold nA.
 rewrite all_0_summation_0; [ easy | ].
 intros j Hj; simpl.
 apply Nat.eq_mul_0; left.
 unfold fd2n, freal_normalize; simpl.
 unfold digit_sequence_normalize.
 destruct (LPO_fst (is_9_strict_after (freal x) j)) as [H3| H3].
 +destruct (lt_dec (S (d2n (freal x) j)) rad) as [H4| H4]; [ | easy ].
  specialize (H2 (j - i - 1)).
  replace (i + (j - i - 1) + 1) with j in H2 by flia Hj.
  exfalso; flia H2 H4.
 +destruct H3 as (k & Hjk & Hk).
  specialize (H1 (j + k - i)).
  apply is_9_strict_after_true_iff in H1.
  apply is_9_strict_after_false_iff in Hk.
  now replace (i + (j + k - i) + 1) with (j + k + 1) in H1 by flia Hj.
-destruct H1 as (k & Hjk & Hk).
 move k before i.
 apply is_9_strict_after_false_iff in Hk.
 destruct (LPO_fst (is_9_strict_after (freal x) (n - 1))) as [H1| H1].
 +right; left.
  specialize (is_9_strict_after_all_9 (freal x) (n - 1) H1) as H2.
  clear H1 Hjk.
  assert (H3 : ∀ k, d2n (freal x) (n + k) = rad - 1). {
    intros j; specialize (H2 j).
    now replace (n - 1 + j + 1) with (n + j) in H2 by flia Hin.
  }
  clear H2; rename H3 into H2.
  assert (Hik : i + k + 1 ≤ n - 1). {
    destruct (lt_dec (n - 1) (i + k + 1)) as [H4| H4]; [ | flia H4 ].
    specialize (H2 (i + k + 1 - n)).
    now replace (n + (i + k + 1 - n)) with (i + k + 1) in H2 by lia.
  }
  move Hik before Hin.
  remember (n - i - k - 2) as m eqn:Hm.
  revert i k n Hin Hik Hk H2 Hm.
  induction m; intros.
  *unfold nA.
   destruct n; [ flia Hin | ].
   replace (S n - 1) with n in Hin, Hik |-* by flia.
   destruct n; [ flia Hin | ].
   rewrite summation_split_last; [ | easy ].
   rewrite summation_split_last; [ | easy ].
   rewrite Nat.sub_diag, Nat.pow_0_r.
   do 2 rewrite Nat.mul_1_r.
   rewrite <- Nat.add_assoc.
   remember minus as f; simpl; subst f.
   f_equal.
  --apply summation_eq_compat.
    intros j Hj; f_equal.
    move j before i.
    unfold fd2n; simpl.
    unfold digit_sequence_normalize.
    destruct (LPO_fst (is_9_strict_after (freal x) j)) as [H1| ]; [ | easy ].
    specialize (H1 (i + k - j)).
    apply is_9_strict_after_true_iff in H1.
    now replace (j + (i + k - j)) with (i + k) in H1 by flia Hm Hj.
  --unfold fd2n; simpl.
    unfold digit_sequence_normalize.
    destruct (LPO_fst (is_9_strict_after (freal x) (S n))) as [H1| H1].
   ++destruct (lt_dec (S (d2n (freal x) (S n))) rad) as [H4| H4].
    **unfold d2n; simpl; flia.
    **apply Nat.nlt_ge in H4.
      replace (i + k + 1) with (S n) in Hk by flia Hik Hm.
      specialize (digit_lt_radix (freal x (S n))) as H.
      unfold d2n in Hk, H4, H.
      flia Hk H4 H.
   ++destruct H1 as (j & Hjj & Hj).
     apply is_9_strict_after_false_iff in Hj.
     specialize (H2 j).
     now replace (S n + j + 1) with (S (S n) + j) in Hj by flia.
  *destruct (eq_nat_dec (fd2n x (n - 1)) (rad - 1)) as [H4| H4].
  --destruct n; [ easy | ].
    rewrite nA_succ_r; [ | flia Hm ].
    rewrite nA_succ_r; [ | flia Hm ].
    assert (H1 : i + 1 ≤ n - 1) by flia Hm.
    assert (H5 : i + k + 1 ≤ n - 1) by flia Hm.
    replace (S n - 1) with n in H4 by flia.
    assert (H6 : ∀ k, d2n (freal x) (n + k) = rad - 1). {
      intros j.
      destruct j; [ now rewrite Nat.add_0_r | ].
      specialize (H2 j).
      now replace (n + S j) with (S n + j) by flia.
    }
    clear H2; rename H5 into H2.
    assert (H7 : m = n - i - k - 2) by flia Hm.
    specialize (IHm i k n H1 H2 Hk H6 H7).
    rewrite IHm.
    rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
    do 2 rewrite <- Nat.add_assoc.
    f_equal.
    specialize (H6 0) as H; rewrite Nat.add_0_r in H.
    unfold d2n in H; unfold fd2n; rewrite H; clear H.
    unfold freal_normalize; simpl.
    unfold digit_sequence_normalize.
    destruct (LPO_fst (is_9_strict_after (freal x) n)) as [H3| H3].
   ++destruct (lt_dec (S (d2n (freal x) n)) rad) as [H5| H5].
    **specialize (H6 0); rewrite Nat.add_0_r in H6.
      exfalso; flia H6 H5.
    **simpl; specialize radix_ge_2; flia.
   ++idtac.
     destruct H3 as (j & Hjj & Hj).
     apply is_9_strict_after_false_iff in Hj.
     specialize (H6 (j + 1)).
     now rewrite Nat.add_assoc in H6.
  --destruct n; [ easy | ].
    replace (S n - 1) with n in Hin, Hik, H4 by flia.
    rewrite nA_succ_r; [ | flia Hm ].
    rewrite nA_succ_r; [ | flia Hm ].
    rewrite <- Nat.add_assoc.
    f_equal.
   ++f_equal.
     apply nA_eq_compat.
     intros j Hj.
     unfold fd2n, freal_normalize; simpl.
     unfold digit_sequence_normalize.
     destruct (LPO_fst (is_9_strict_after (freal x) j)) as [H1| H1].
    **specialize (H1 (n - j - 1)).
      apply is_9_strict_after_true_iff in H1.
      now replace (j + (n - j - 1) + 1) with n in H1 by flia Hj.
    **easy.
   ++unfold fd2n, freal_normalize; simpl.
     unfold digit_sequence_normalize.
     destruct (LPO_fst (is_9_strict_after (freal x) n)) as [H1| H1].
    **destruct (lt_dec (S (d2n (freal x) n)) rad) as [H3| H3].
    ---simpl; unfold d2n; flia.
    ---specialize (digit_lt_radix (freal x n)) as H.
       unfold fd2n in H4; unfold d2n in H3.
       flia H H3 H4.
    **destruct H1 as (j & Hjj & Hj).
      apply is_9_strict_after_false_iff in Hj.
      specialize (H2 j).
      now replace (n + j + 1) with (S n + j) in Hj by flia.
 +destruct H1 as (j & Hjj & Hj).
  apply is_9_strict_after_false_iff in Hj.
  replace (n - 1 + j + 1) with (n + j) in Hj by flia Hin.
  left.
  apply nA_eq_compat.
  intros m Hm.
  unfold fd2n, freal_normalize; simpl.
  unfold digit_sequence_normalize.
  destruct (LPO_fst (is_9_strict_after (freal x) m)) as [H1| H1]; [ | easy ].
  specialize (H1 (n - m + j - 1)).
  apply is_9_strict_after_true_iff in H1.
  now replace (m + (n - m + j - 1) + 1) with (n + j) in H1 by flia Hm.
Qed.

Theorem nA_freal_normalize_0 {r : radix} : ∀ i n x,
  (∀ k, d2n (freal x) (i + k + 1) = rad - 1)
  → nA i n (fd2n (freal_normalize x)) = 0.
Proof.
intros * Hx.
unfold nA.
rewrite all_0_summation_0; [ easy | ].
intros j Hj; simpl.
apply Nat.eq_mul_0; left.
unfold freal_normalize, fd2n; simpl.
unfold digit_sequence_normalize.
destruct (LPO_fst (is_9_strict_after (freal x) j)) as [H| H].
-destruct (lt_dec (S (d2n (freal x) j)) rad) as [H7| H7]; [ | easy ].
 exfalso.
 specialize (Hx (j - i - 1)).
 replace (i + (j - i - 1) + 1) with j in Hx by flia Hj.
 flia Hx H7.
-destruct H as (k & Hkj & Hk).
 apply is_9_strict_after_false_iff in Hk.
 specialize (Hx (j - i + k)).
 now replace (i + (j - i + k) + 1) with (j + k + 1) in Hx by flia Hj.
Qed.

Theorem all_9_nA {r : radix} : ∀ x i j
  (n := (rad * (i + j + 2))%nat) (s := rad ^ (n - i - 1)),
  (∀ k, fd2n x (i + k + 1) = rad - 1)
  → nA i n (fd2n x) = s - 1.
Proof.
intros * Hx.
specialize radix_ge_2 as Hr.
unfold s.
remember (n - i - 1) as m eqn:Hm.
destruct m.
-unfold n in Hm.
 destruct rad; [ easy | simpl in Hm; flia Hm ].
-rewrite power_summation; [ | easy ].
 rewrite Nat.add_comm, Nat.add_sub.
 rewrite summation_mul_distr_l; simpl.
 unfold nA.
 rewrite summation_rtl.
 rewrite summation_shift.
 +replace (n - 1 - (i + 1)) with m.
  *apply summation_eq_compat.
   intros k Hk.
   replace (n - 1 + (i + 1) - (i + 1 + k)) with (n - k - 1) by flia.
   f_equal; [ | f_equal; flia Hm Hk ].
   specialize (Hx (n - k - 1 - i - 1)).
   replace (i + (n - k - 1 - i - 1) + 1) with (n - k - 1) in Hx; [ easy | ].
   flia Hm Hk.
  *apply Nat.succ_inj.
   rewrite Hm; unfold n.
   destruct rad; [ easy | simpl; flia ].
 +unfold n.
  destruct rad; [ easy | simpl; flia ].
Qed.
*)

Theorem Nat_pow_sub_1_mul_pow : ∀ n a b,
  (n ^ a - 1) * n ^ b = n ^ (a + b) - n ^ b.
Proof.
intros.
rewrite Nat.mul_sub_distr_r.
now rewrite Nat.pow_add_r, Nat.mul_1_l.
Qed.

(*
Theorem nA_upper_bound_for_op {r : radix} (rg := nat_ord_ring) : ∀ u i k,
  let n := rad * (i + k + 2) in
  (∀ j, i < j < n → u j ≤ (j + 1) * (rad - 1) ^ 2)
  → nA i n u ≤ (rad - 1) ^ 2 * Σ (j = 0, n - i - 2), (n - j) * rad ^ j.
Proof.
intros * Hur *; subst n.
remember (rad * (i + k + 2)) as n eqn:Hn.
apply le_trans with
    (m := (rad - 1) ^ 2 * Σ (j = i + 1, n - 1), (j + 1) * rad ^ (n - 1 - j)).
-unfold nA.
 rewrite summation_mul_distr_l.
 apply (@summation_le_compat nat_ord_ring_def).
 intros j Hj.
 remember 2 as x; simpl; subst x.
 unfold Nat.le.
 rewrite Nat.mul_assoc.
 apply Nat.mul_le_mono_r.
 rewrite Nat.mul_comm.
 apply Hur; flia Hj.
-apply Nat.mul_le_mono_l.
 specialize radix_ge_2 as Hr.
 assert (Hin : i + 2 ≤ n - 1). {
   subst n.
   destruct rad; [ easy | simpl; flia ].
 }
 rewrite summation_rtl.
 rewrite summation_shift; [ | flia Hin ].
 replace (n - 1 - (i + 1)) with (n - i - 2) by flia.
 apply (@summation_le_compat nat_ord_ring_def).
 intros j Hj; simpl; unfold Nat.le.
 replace (n - 1 + (i + 1) - (i + 1 + j) + 1) with (n - j) by flia Hin Hj.
 replace (n - 1 - (n - 1 + (i + 1) - (i + 1 + j))) with j by flia Hj.
 easy.
Qed.
*)

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

(*
Theorem nA_upper_bound_for_add_2 {r : radix} : ∀ u i n,
  (∀ k, u k ≤ 2 * (rad - 1))
  → u (i + 1) = rad - 2
  → u (i + 2) < rad
  → i + 2 ≤ n - 1
  → nA i n u < (rad ^ 2 - 1) * rad ^ (n - i - 1 - 2).
Proof.
intros * Hur H1 H2 Hin.
specialize radix_ge_2 as Hr; move Hr before i.
remember (n - i - 1) as s eqn:Hs; move s before n.
rewrite nA_split_first; [ | flia Hin ].
rewrite H1.
replace (n - i - 2) with (s - 1) by flia Hs.
rewrite nA_split_first; [ | flia Hin ].
replace (S i + 1) with (i + 2) by flia.
replace (n - S i - 2) with (s - 2) by flia Hs.
rewrite Nat.add_assoc.
replace (rad ^ 2 - 1) with (rad ^ 2 - rad - 1 + rad ^ 1).
-rewrite Nat.mul_add_distr_r.
 rewrite <- Nat.pow_add_r.
 replace (1 + (s - 2)) with (s - 1) by flia Hs Hin.
 apply Nat.add_le_lt_mono.
 +replace (rad ^ 2 - rad - 1) with (rad ^ 2 - 2 * rad + (rad - 1)).
  *rewrite Nat.mul_add_distr_r.
   rewrite Nat.pow_2_r, <- Nat.mul_sub_distr_r.
   rewrite <- Nat.mul_assoc.
   replace (rad * rad ^ (s - 2)) with (rad ^ (s - 1)).
  --apply Nat.add_le_mono_l.
    apply Nat.mul_le_mono_r.
    flia H2.
  --replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
    rewrite <- Nat.pow_add_r.
    now replace (1 + (s - 2)) with (s - 1) by flia Hs Hin.
  *rewrite Nat.add_sub_assoc; [ f_equal | flia H2 ].
   replace (2 * rad) with (rad + rad) by flia.
   rewrite Nat.sub_add_distr.
   rewrite Nat.sub_add; [ easy | ].
   rewrite Nat.pow_2_r.
   destruct rad as [| rr]; [ easy | ].
   destruct rr; [ flia Hr | simpl; flia ].
 +specialize (nA_upper_bound_for_add u (i + 2) n Hur) as H4.
  remember 2 as x; simpl in H4; subst x.
  replace (n - (i + 2) - 1) with (s - 2) in H4 by flia Hs.
  replace (S (S i)) with (i + 2) by flia.
  eapply le_lt_trans; [ apply H4 | ].
  destruct s; [ flia Hs Hin | ].
  destruct s; [ flia Hs Hin | ].
  replace (S (S s) - 2) with s by flia.
  replace (S (S s) - 1) with (S s) by flia.
  apply lt_le_trans with (m := 2 * rad ^ s).
  *rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   apply Nat.sub_lt; [ | flia ].
   replace 2 with (2 * 1) at 1 by flia.
   apply Nat.mul_le_mono_l.
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *rewrite Nat.pow_succ_r; [ | flia ].
   apply Nat.mul_le_mono_r, radix_ge_2.
-rewrite Nat.pow_1_r, Nat_sub_sub_swap.
 rewrite Nat.sub_add; [ easy | ].
 destruct rad as [| rr]; [ easy | ].
 destruct rr; [ flia Hr | simpl; flia ].
Qed.
*)

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
  → i + k + 2 ≤ n - 1
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

(*
Theorem num_to_dig_9_ge_7 {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → (∀ k, d2n (prop_carr u) (i + k) = rad - 1)
  → u i ≥ rad - 3.
Proof.
intros * Hur Hu.
specialize radix_ge_2 as Hr.
specialize (Hu 0) as H1.
rewrite Nat.add_0_r in H1.
unfold d2n, prop_carr in H1.
destruct (LPO_fst (A_ge_1 u i)) as [H2| H2].
-simpl in H1.
 destruct (lt_dec (u (i + 1)) rad) as [H3| H3].
 +rewrite Nat.div_small in H1; [ | easy ].
  rewrite Nat.add_0_r in H1.
  destruct (lt_dec (u i + 1) rad) as [H4| H4].
  *rewrite Nat.mod_small in H1; [ flia H1 | easy ].
  *rewrite Nat_mod_less_small in H1; [ flia H1 | ].
   split; [ flia H4 | ].
   specialize (Hur i); rewrite Nat.mul_sub_distr_l in Hur.
   destruct rad; [ easy | flia Hur ].
 +rewrite Nat_div_less_small in H1.
  *rewrite <- Nat.add_assoc in H1; simpl in H1.
   destruct (lt_dec (u i + 2) rad) as [H4| H4]; [ | flia H4 ].
   rewrite Nat.mod_small in H1; [ flia H1 | easy ].
  *split; [ flia H3 | ].
   specialize (Hur (i + 1)); rewrite Nat.mul_sub_distr_l in Hur.
   destruct rad; [ easy | flia Hur ].
-destruct H2 as (k & Hjk & Hk).
 simpl in H1.
 apply A_ge_1_false_iff in Hk.
 remember (rad * (i + k + 2)) as n eqn:Hn.
 replace (n - i - k - 2) with (n - i - 1 - S k) in Hk by flia.
 remember (n - i - 1) as s eqn:Hs.
 move s before n.
 destruct (lt_dec (nA i n u) (rad ^ s)) as [H2| H2].
 +rewrite Nat.mod_small in Hk; [ | easy ].
  rewrite Nat.div_small in H1; [ | easy ].
  rewrite Nat.add_0_r in H1.
  destruct (lt_dec (u i) rad) as [H3| H3]; [ | flia H3].
  rewrite Nat.mod_small in H1; [ flia H1 | easy ].
 +remember (nA i n u) as x eqn:Hx.
  replace x with (x - rad ^ s + 1 * rad ^ s) in Hk, H1.
  *rewrite Nat.div_add in H1; [ | now apply Nat.pow_nonzero ].
   rewrite Nat.mod_add in Hk; [ | now apply Nat.pow_nonzero ].
   assert (H6 : x - rad ^ s < rad ^ s). {
     specialize (nA_upper_bound_for_add u i n Hur) as H5.
     rewrite <- Hx, <- Hs in H5.
     specialize (Nat.pow_nonzero rad s radix_ne_0) as H.
     flia H2 H5 H.
   }
   rewrite Nat.mod_small in Hk; [ | easy ].
   rewrite Nat.div_small in H1; [ | easy ].
   simpl in H1.
   destruct (lt_dec (u i + 1) rad) as [H7| H7]; [ | flia H7 ].
   rewrite Nat.mod_small in H1; [ | easy ].
   flia H1.
  *rewrite Nat.mul_1_l.
   apply Nat.sub_add.
   flia H2.
Qed.
*)

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
remember (rad * (i + 2)) as n eqn:Hn.
remember (n - i - 1) as s eqn:Hs.
move s before n.
assert (Hin : i + 2 ≤ n - 1). {
  rewrite Hn.
  specialize radix_ne_0 as H.
  destruct rad as [| rr]; [ easy | simpl ].
  destruct rr; [ flia H1 | simpl; flia ].
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
replace (i + (j + 1) + 2) with (i + j + 3) by flia.
replace (S (j + 1)) with (j + 2) by flia.
remember (rad * (i + j + 3)) as n eqn:Hn.
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
remember (rad * (i + 2)) as n eqn:Hn.
remember (n - i - 1) as s eqn:Hs.
move s before n.
assert (Hin : i + 1 ≤ n - 1). {
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

(*
Theorem A_ge_1_add_8_aft_ge_rad {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → A_ge_1 u i 1 = true
  → u (i + 1) = rad - 2
  → u (i + 2) ≥ rad.
Proof.
intros * Hur H2 H1.
specialize radix_ge_2 as Hr; move Hr before i.
revert H2.
apply Decidable.contrapositive; [ apply Nat.le_decidable | ].
intros H2; apply Nat.nle_gt in H2.
apply Bool.not_true_iff_false.
apply A_ge_1_false_iff.
replace (i + 1 + 2) with (i + 4) by flia.
remember (rad * (i + 4)) as n eqn:Hn.
remember (n - i - 1) as s eqn:Hs.
move s before n.
assert (Hin : i + 2 ≤ n - 1). {
  rewrite Hn.
  destruct rad as [| rr]; [ easy | ].
  destruct rr; [ flia Hr | simpl; flia ].
}
specialize (nA_upper_bound_for_add_2 u i n Hur H1 H2 Hin) as H3.
rewrite <- Hs in H3.
rewrite Nat.mod_small; [ easy | ].
eapply lt_le_trans; [ apply H3 | ].
rewrite Nat.mul_sub_distr_r.
rewrite Nat.mul_1_l, <- Nat.pow_add_r.
replace (2 + (s - 2)) with s by flia Hs Hin.
apply Nat.le_sub_l.
Qed.

Theorem A_ge_1_add_second_eq {r : radix} : ∀ u i,
  (∀ k, i + 1 < k < rad * (i + 4) → u k ≤ 2 * (rad - 1))
  → A_ge_1 u i 1 = true
  → u (i + 1) = rad - 2
  → u (i + 2) = 2 * (rad - 1).
Proof.
intros * Hur H2 Hui.
specialize radix_ge_2 as Hr; move Hr before i.
revert H2.
apply Decidable.contrapositive; [ apply Nat.eq_decidable | ].
intros H.
assert (H2 : u (i + 2) < 2 * (rad - 1)). {
  assert (H1 : i + 1 < i + 2 < rad * (i + 4)). {
    split; [ flia | ].
    destruct rad; [ easy | simpl; flia ].
  }
  specialize (Hur (i + 2) H1).
  flia Hur H.
}
clear H.
apply Bool.not_true_iff_false.
apply A_ge_1_false_iff.
remember (rad * (i + 1 + 2)) as n eqn:Hn.
remember (n - i - 1) as s eqn:Hs.
move s before n.
assert (Hin : i + 4 ≤ n - 1). {
  rewrite Hn.
  destruct rad as [| rr]; [ easy | ].
  destruct rr; [ flia Hr | simpl; flia ].
}
assert (H3 : nA i n u < (rad ^ 2 - 1) * rad ^ (s - 2)). {
  rewrite nA_split_first; [ | flia Hin ].
  rewrite nA_split_first; [ | flia Hin ].
  replace (S i + 1) with (i + 2) by flia.
  replace (n - S i - 2) with (s - 2) by flia Hs.
  replace (n - i - 2) with (s - 1) by flia Hs Hin.
  rewrite Nat.add_assoc.
  rewrite Hui.
  replace (rad ^ 2 - 1) with (rad ^ 2 - 3 + 2).
  -rewrite Nat.mul_add_distr_r.
   apply Nat.add_le_lt_mono.
   +replace (rad ^ 2 - 3) with (rad ^ 2 - 2 * rad + (2 * (rad - 1) - 1)).
    *rewrite Nat.mul_add_distr_r.
     apply Nat.add_le_mono.
    --rewrite Nat.pow_2_r.
      rewrite <- Nat.mul_sub_distr_r.
      rewrite <- Nat.mul_assoc.
      apply Nat.mul_le_mono_l.
      replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
      rewrite <- Nat.pow_add_r.
      now replace (1 + (s - 2)) with (s - 1) by flia Hs Hin.
    --apply Nat.mul_le_mono_r.
      specialize (Hur (i + 2)).
      flia Hur H2.
    *rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
     replace (2 * rad - 2 - 1) with (2 * rad - 3) by flia.
     rewrite Nat.add_sub_assoc; [ | flia Hr ].
     f_equal; rewrite Nat.sub_add ; [ easy | ].
     rewrite Nat.pow_2_r.
     now apply Nat.mul_le_mono_r.
   +rewrite nA_split_first; [ | flia Hin ].
    replace (S (S i) + 1) with (i + 2) by flia.
    replace (n - S (S i) - 2) with (s - 3) by flia Hs.
    replace (s - 2) with (s - 3 + 1) by flia Hs Hin.
    rewrite Nat.pow_add_r, Nat.mul_assoc.
    replace (rad ^ 1) with (rad - 1 + 1).
    *rewrite Nat.mul_add_distr_l.
     apply Nat.add_le_lt_mono.
    --rewrite Nat.mul_shuffle0.
      apply Nat.mul_le_mono_r, Hur; flia Hn Hin.
    --rewrite Nat.mul_1_r.
      destruct s; [ flia Hs Hin | ].
      destruct s; [ flia Hs Hin | ].
      destruct s; [ flia Hs Hin | ].
      destruct s; [ flia Hs Hin | ].
      replace (S (S (S (S s))) - 3) with (S s) by flia.
      rewrite power_summation; [ | easy ].
      rewrite Nat.mul_add_distr_l.
      rewrite Nat.mul_1_r.
      do 2 rewrite Nat.add_succ_l.
      rewrite Nat.add_0_l.
      apply Nat.le_le_succ_r.
      apply -> Nat.succ_le_mono.
      rewrite Nat.mul_assoc.
      rewrite summation_mul_distr_l.
      unfold nA.
      rewrite summation_rtl.
      rewrite summation_shift; [ | flia Hin ].
      replace (n - 1 - (S (S (S i)) + 1)) with s by flia Hs Hin.
      apply (@summation_le_compat nat_ord_ring_def).
      intros j Hj.
      remember 2 as x; simpl; subst x; unfold Nat.le.
      replace (n - 1 + S (S (S (i + 1))) - S (S (S (i + 1 + j))))
        with (n - j - 1) by flia.
      replace (n - 1 - (n - j - 1)) with j by flia Hs Hj.
      apply Nat.mul_le_mono_r, Hur; flia Hs Hn Hj.
    *rewrite Nat.pow_1_r; flia Hr.
  -destruct rad as [| rr]; [ easy | ].
   destruct rr; [ easy | simpl; flia ].
}
rewrite Nat.mod_small; [ easy | ].
eapply lt_le_trans; [ apply H3 | ].
rewrite Nat.mul_sub_distr_r.
rewrite Nat.mul_1_l, <- Nat.pow_add_r.
replace (2 + (s - 2)) with s by flia Hs Hin.
apply Nat.le_sub_l.
Qed.
*)

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
remember (rad * (i + (k + 1) + 2)) as n eqn:Hn.
replace (n - i - (k + 1) - 2) with (n - i - 1 - (k + 2)) by flia.
remember (n - i - 1) as s eqn:Hs.
move s before n.
assert (Hin : i + k + 2 ≤ n - 1). {
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
    remember (rad * (i + j + 2)) as n eqn:Hn.
    replace (n - i - j - 2) with (n - i - 1 - S j) by flia.
    remember (n - i - 1) as s eqn:Hs.
    move n before j; move s before n.
    assert (H6 : i + j + 2 ≤ n - 1). {
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
(*
    replace (i + j + 2) with (i + j + 2 + 1) in Hn, H6 by flia.
    rewrite <- Ht in Hn, H6.
*)
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
    replace (i + (j + k + 1) + 2) with (i + j + k + 3) in H5 by flia.
    replace (i + j + (k + 1) + 2) with (i + j + k + 3) by flia.
    remember (rad * (i + j + k + 3)) as n eqn:Hn.
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
   replace (i + (k + 1) + 2) with (i + k + 3) in H3 |-* by flia.
   remember (rad * (i + k + 3)) as n eqn:Hn.
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

(*
Theorem eq_mod_rad_add_pred_rad {r : radix} : ∀ u i n s,
  (∀ k, u k ≤ 2 * (rad - 1))
  → s = n - i - 1
  → (u i + nA i n u / rad ^ s) mod rad = rad - 1
  → u i = rad - 2 ∧ rad ^ s ≤ nA i n u < 2 * rad ^ s ∨
     u i = 2 * rad - 2 ∧ rad ^ s ≤ nA i n u < 2 * rad ^ s ∨
     u i = rad - 1 ∧ nA i n u < rad ^ s.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hs Hu.
destruct (lt_dec (nA i n u) (rad ^ s)) as [H1| H1].
-right; right.
 rewrite Nat.div_small in Hu; [ | easy ].
 rewrite Nat.add_0_r in Hu.
 split; [ | easy ].
 destruct (lt_dec (u i) rad) as [H2| H2].
 +now rewrite Nat.mod_small in Hu.
 +specialize (Hur i).
  rewrite Nat_mod_less_small in Hu; [ flia Hur Hu | ].
  split; [ flia H2 | flia Hur Hr ].
-rewrite Nat_div_less_small in Hu.
 +destruct (lt_dec (u i + 1) rad) as [H2| H2].
  *left.
   rewrite Nat.mod_small in Hu; [ | easy ].
   split; [ flia Hu | ].
   split; [ flia H1 | ].
   specialize (nA_upper_bound_for_add u i n Hur) as H3.
   rewrite <- Hs in H3.
   rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H3.
   specialize (Nat.pow_nonzero rad s radix_ne_0) as H4.
   flia H3 H4.
  *right; left.
   rewrite Nat_mod_less_small in Hu.
  --split; [ flia Hu | ].
    split; [ flia H1 | ].
    specialize (nA_upper_bound_for_add u i n Hur) as H3.
    rewrite <- Hs in H3.
    rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H3.
    specialize (Nat.pow_nonzero rad s radix_ne_0) as H4.
    flia H3 H4.
  --split; [ flia H2 | ].
    specialize (Hur i); flia Hr Hur.
 +split; [ flia H1 | ].
  specialize (nA_upper_bound_for_add u i n Hur) as H2.
  specialize (Nat.pow_nonzero rad s radix_ne_0) as H.
  rewrite <- Hs in H2.
  flia H2 H.
Qed.

Theorem eq_add_mod_rad_add_pred_rad {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → (u i + u (i + 1) / rad) mod rad = rad - 1
  → u i = rad - 2 ∨
     u i = 2 * rad - 2 ∨
     u i = rad - 1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hu.
destruct (lt_dec (u (i + 1)) rad) as [H1| H1].
-right; right.
 rewrite Nat.div_small in Hu; [ | easy ].
 rewrite Nat.add_0_r in Hu.
  destruct (lt_dec (u i) rad) as [H2| H2].
 +now rewrite Nat.mod_small in Hu.
 +specialize (Hur i).
  rewrite Nat_mod_less_small in Hu; [ flia Hur Hu | ].
  split; [ flia H2 | flia Hur Hr ].
-rewrite Nat_div_less_small in Hu.
 +destruct (lt_dec (u i + 1) rad) as [H2| H2].
  *left.
   rewrite Nat.mod_small in Hu; [ flia Hu | easy ].
  *right; left.
   rewrite Nat_mod_less_small in Hu; [ flia Hu | ].
   split; [ flia H2 | ].
   specialize (Hur i); flia Hr Hur.
 +split; [ flia H1 | ].
  specialize (Hur (i + 1)).
  flia Hr Hur.
Qed.

Theorem eq_add_succ_mod_rad_add_pred_rad {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → (u i + 1 + u (i + 1) / rad) mod rad = rad - 1
  → (u i = rad - 3 ∨
      u i = 2 * rad - 3) ∧ u (i + 1) ≥ rad ∨
     (u i = rad - 2 ∨
      u i = 2 * rad - 2) ∧ u (i + 1) < rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hu.
destruct (lt_dec (u (i + 1)) rad) as [H1| H1].
-rewrite Nat.div_small in Hu; [ | easy ].
 rewrite Nat.add_0_r in Hu.
 right; split; [ | easy ].
 destruct (lt_dec (u i + 1) rad) as [H2| H2].
 +rewrite Nat.mod_small in Hu; [ left; flia Hu | easy ].
 +rewrite Nat_mod_less_small in Hu; [ right; flia Hu | ].
  split; [ flia H2 | ].
  specialize (Hur i); flia Hr Hur.
-left; split; [ | flia H1 ].
 rewrite Nat_div_less_small in Hu.
 +destruct (lt_dec (u i + 1 + 1) rad) as [H2| H2].
  *rewrite Nat.mod_small in Hu; [ | easy ].
   left; flia Hu.
  *rewrite Nat_mod_less_small in Hu.
  --right; flia Hu.
  --split; [ flia H2 | ].
    specialize (Hur i).
    specialize (Nat.eq_dec (u i) (2 * (rad - 1))) as [H3| H3].
   ++rewrite H3 in Hu.
     rewrite <- Nat.add_assoc in Hu.
     remember mult as f; simpl in Hu; subst f.
     replace (2 * (rad - 1) + 2) with (2 * rad) in Hu by flia Hr.
     rewrite Nat.mod_mul in Hu; [ flia Hr Hu | easy ].
   ++flia Hur H3.
 +split; [ flia H1 | ].
  specialize (Hur (i + 1)); flia Hr Hur.
Qed.

Theorem eq_mod_rad_add_succ_pred_rad {r : radix} : ∀ u i n s,
  (∀ k, u k ≤ 2 * (rad - 1))
  → s = n - i - 1
  → (u i + nA i n u / rad ^ s + 1) mod rad = rad - 1
  → u i = rad - 3 ∧ rad ^ s ≤ nA i n u < 2 * rad ^ s ∨
     u i = 2 * rad - 3 ∧ rad ^ s ≤ nA i n u < 2 * rad ^ s ∨
     u i = rad - 2 ∧ nA i n u < rad ^ s ∨
     u i = 2 * rad - 2 ∧ nA i n u < rad ^ s.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hs Hu.
destruct (lt_dec (nA i n u) (rad ^ s)) as [H1| H1].
-rewrite Nat.div_small in Hu; [ | easy ].
 rewrite Nat.add_0_r in Hu.
 destruct (lt_dec (u i + 1) rad) as [H2| H2].
 +rewrite Nat.mod_small in Hu; [ | easy ].
  right; right; left.
  split; [ flia Hu | easy ].
 +rewrite Nat_mod_less_small in Hu.
  *right; right; right.
   split; [ flia Hu | easy ].
  *split; [ flia H2 | ].
   specialize (Hur i); flia Hur Hr.
-rewrite Nat_div_less_small in Hu.
 replace (u i + 1 + 1) with (u i + 2) in Hu by flia.
 +destruct (Nat.eq_dec rad 2) as [H2| H2].
  *rewrite H2.
   rewrite H2 in (*Hur,*) Hu.
   rewrite Nat_mod_add_same_r in Hu; [ | easy ].
   specialize (Hur i) as H3; simpl in H3.
   destruct (Nat.eq_dec (u i) 2) as [H4| H4].
  --now rewrite H4 in Hu; simpl in Hu.
  --rewrite Nat.mod_small in Hu; [ | flia H2 H3 H4 ].
    right; left.
    split; [ easy | ].
    rewrite H2 in H1.
    split; [ flia H1 | ].
    specialize (nA_upper_bound_for_add u i n Hur) as H5.
    rewrite <- Hs, H2 in H5.
    specialize (Nat.pow_nonzero rad s radix_ne_0) as H6.
    rewrite H2 in H6.
    flia H5 H6.
  *destruct (lt_dec (u i + 2) rad) as [H3| H3].
  --rewrite Nat.mod_small in Hu; [ | easy ].
    left.
    split; [ flia Hu | ].
    split; [ flia H1 | ].
    specialize (nA_upper_bound_for_add u i n Hur) as H5.
    rewrite <- Hs in H5.
    specialize (Nat.pow_nonzero rad s radix_ne_0) as H6.
    flia H5 H6.
  --rewrite Nat_mod_less_small in Hu.
   ++right; left; split; [ flia Hu | ].
     split; [ flia H1 | ].
     specialize (nA_upper_bound_for_add u i n Hur) as H5.
     rewrite <- Hs in H5.
     specialize (Nat.pow_nonzero rad s radix_ne_0) as H6.
     flia H5 H6.
   ++split; [ flia H3 | ].
     specialize (Hur i).
     apply Nat_le_neq_lt; [ flia Hr Hur | ].
     intros H; rewrite H in Hu.
     rewrite Nat.mod_mul in Hu; [ flia Hr Hu | easy ].
 +split; [ flia H1 | ].
  specialize (nA_upper_bound_for_add u i n Hur) as H2.
  specialize (Nat.pow_nonzero rad s radix_ne_0) as H.
  rewrite <- Hs in H2.
  flia H2 H.
Qed.
*)

Theorem A_ge_1_add_r_true_if {r : radix} : ∀ u i j k,
   A_ge_1 u i (j + k) = true
   → A_ge_1 u (i + j) k = true.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hu.
apply A_ge_1_true_iff in Hu.
apply A_ge_1_true_iff.
replace (i + (j + k) + 2) with (i + j + k + 2) in Hu by flia.
remember (rad * (i + j + k + 2)) as n eqn:Hn.
remember (n - (i + j) - 1) as s eqn:Hs.
move s before n.
assert (Hijn : i + j + 1 ≤ n - 1). {
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

Theorem A_ge_1_add_r_all_true_if {r : radix} : ∀ u i,
  (∀ k, A_ge_1 u i k = true)
  → ∀ j, (∀ k, A_ge_1 u (i + j) k = true).
Proof.
intros * Hu *.
apply A_ge_1_add_r_true_if, Hu.
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

Theorem freal_normalized_cases {r : radix} : ∀ x,
  freal_norm_eq (freal_normalize x) x ∨
  freal_norm_not_norm_eq (freal_normalize x) x.
Proof.
intros x.
remember (freal_normalize x) as nx eqn:Hnx.
assert (H1 : ∀ i, freal nx i = freal (freal_normalize nx) i). {
  intros i.
  unfold freal_normalize; simpl.
  unfold digit_sequence_normalize.
  destruct (LPO_fst (is_9_strict_after (freal nx) i)) as [H1| ]; [ | easy ].
  specialize (is_9_strict_after_all_9 (freal nx) _ H1) as H2.
  specialize (normalized_not_999 x) as H3.
  rewrite <- Hnx in H3.
  exfalso; apply H3; exists (i + 1).
  intros j; specialize (H2 j).
  now rewrite Nat.add_shuffle0 in H2.
}
remember (freal_normalize nx) as nnx.
rewrite Hnx in H1; subst nnx.
specialize (proj1 (freal_normalized_eq_iff x nx) H1) as H2.
destruct H2 as [H2| [H2| H2]]; [ | | now right ].
-left.
 unfold freal_norm_eq.
 now intros i; apply digit_eq_eq; rewrite H2.
-unfold freal_norm_not_norm_eq in H2.
 destruct H2 as (k & Hbef & Hwhi & Hxaft & Hnxaft).
 specialize (normalized_not_999 x) as H2.
 exfalso; apply H2; exists (k + 1).
 intros j.
 specialize (Hnxaft (1 + j)).
 rewrite Nat.add_assoc in Hnxaft.
 now rewrite <- Hnx.
Qed.

Theorem eq_freal_norm_eq_true_iff {r : radix} : ∀ x y,
  freal_norm_eq x y
  ↔ ∀ i, fd2n x i = fd2n y i.
Proof.
intros.
split; intros Hxy.
-intros i.
 unfold freal_norm_eq in Hxy.
 destruct (LPO_fst (has_same_digits x y)) as [H1| H1]; [ | easy ].
 specialize (H1 i).
 unfold has_same_digits in H1.
 now destruct (Nat.eq_dec (fd2n x i) (fd2n y i)).
-unfold freal_norm_eq.
 destruct (LPO_fst (has_same_digits x y)) as [H1| H1]; [ easy | ].
 destruct H1 as (i & Hji & Hi).
 unfold has_same_digits in Hi.
 destruct (Nat.eq_dec (fd2n x i) (fd2n y i)); [ easy | ].
 now specialize (Hxy i).
Qed.

Add Parametric Morphism {r : radix} : freal_normalize
  with signature freal_norm_eq ==> freal_norm_eq
  as freal_norm_morph.
Proof.
intros x y Hxy.
unfold freal_norm_eq in Hxy |-*.
intros i.
unfold fd2n, freal_normalize; simpl.
unfold digit_sequence_normalize.
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

Theorem ends_with_999_or_not {r : radix} : ∀ x,
  (∀ i, ∃ j, fd2n x (i + j) ≠ rad - 1)
  ∨ (∃ i, ∀ j, fd2n x (i + j) = rad - 1).
Proof.
intros.
destruct (LPO_fst (ends_with_999 (freal x))) as [H1| H1].
-right.
 specialize (H1 0) as H2.
 apply ends_with_999_true_iff in H2.
 destruct H2 as (j & (Hjj & Hj) & _).
 apply has_not_9_after_false_iff in Hj.
 simpl in Hj.
 destruct Hj as (Hj & _).
 exists j.
 intros k.
 specialize (Hj k) as H2.
 now apply is_9_after_true_iff in H2.
-left; intros i.
 destruct H1 as (j & Hjj & Hj).
 apply ends_with_999_false_iff in Hj.
 destruct Hj as (H1 & _).
 specialize (H1 i) as H2.
 apply has_not_9_after_true_iff in H2.
 destruct H2 as (k & (Hjk & Hk) & _).
 apply is_9_after_false_iff in Hk.
 exists (j + k).
 now replace (j + i + k) with (i + (j + k)) in Hk by flia.
Qed.

Theorem ends_with_000_or_not {r : radix} : ∀ x,
  (∀ i, ∃ j, fd2n x (i + j) ≠ 0)
  ∨ (∃ i, ∀ j, fd2n x (i + j) = 0).
Proof.
intros.
destruct (LPO_fst (ends_with_000 (freal x))) as [H1| H1].
-right.
 specialize (H1 0) as H2.
 apply ends_with_000_true_iff in H2.
 destruct H2 as (j & (Hjj & Hj) & _).
 apply has_not_0_after_false_iff in Hj.
 simpl in Hj.
 destruct Hj as (Hj & _).
 exists j.
 intros k.
 specialize (Hj k) as H2.
 now apply is_0_after_true_iff in H2.
-left; intros i.
 destruct H1 as (j & Hjj & Hj).
 apply ends_with_000_false_iff in Hj.
 destruct Hj as (H1 & _).
 specialize (H1 i) as H2.
 apply has_not_0_after_true_iff in H2.
 destruct H2 as (k & (Hjk & Hk) & _).
 apply is_0_after_false_iff in Hk.
 exists (j + k).
 now replace (j + i + k) with (i + (j + k)) in Hk by flia.
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
 remember (rad * (j + k + 2)) as n1 eqn:Hn1.
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
  → let n1 := rad * (i + j + 2) in
     let s1 := n1 - i - 1 in
     (rad ^ S j - 1) * rad ^ (s1 - S j) ≤ nA i n1 u.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur.
remember S as f; simpl; subst f.
set (n1 := rad * (i + j + 2)).
set (s1 := n1 - i - 1).
assert (Hin1 : i + j + 1 ≤ n1 - 1). {
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

Theorem unorm_add_inf_pred_rad {r : radix} : ∀ x y n,
  (∀ i, fd2n x (n + i) = rad - 1)
  → (∀ i, ∃ j : nat, fd2n y (i + j) ≠ rad - 1)
  → ∀ i : nat, n ≤ i → fd2n (x + y) i = fd2n y i.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Haft Hy i Hni.
unfold freal_add, fd2n; simpl.
unfold prop_carr, nat_prop_carr.
specialize (Haft (i - n)) as H4.
replace (n + (i - n)) with i in H4 by flia Hni.
destruct (LPO_fst (A_ge_1 (x ⊕ y) i)) as [H2| H2].
-simpl.
 unfold "⊕" at 1.
 rewrite H4; clear H4.
 replace (rad - 1 + fd2n y i + 1) with (rad + fd2n y i) by flia Hr.
 rewrite <- Nat.add_assoc.
 rewrite Nat_mod_add_same_l; [ | easy ].
 specialize (A_ge_1_add_all_true_if (x ⊕ y) i) as H3.
 assert (H : ∀ k : nat, (x ⊕ y) (i + k + 1) ≤ 2 * (rad - 1)). {
   intros k; apply freal_add_series_le_twice_pred.
 }
 specialize (H3 H H2); clear H H2.
 destruct H3 as [H3| [H3| H3]].
 +rewrite Nat.div_small.
  *rewrite Nat.add_0_r.
   rewrite Nat.mod_small; [ easy | ].
   apply digit_lt_radix.
  *apply nA_dig_seq_ub.
  --intros k Hk.
    specialize (H3 (k - i - 1)).
    replace (i + (k - i - 1) + 1) with k in H3 by flia Hk.
    rewrite H3; flia Hr.
  --destruct rad; [ easy | simpl; flia ].
 +specialize (Hy (i + 1)) as H4.
  destruct H4 as (k & Hk).
  rewrite Nat.add_shuffle0 in Hk.
  specialize (H3 k).
  unfold "⊕" in H3.
  specialize (Haft (i - n + k + 1)) as H4.
  replace (n + (i - n + k + 1)) with (i + k + 1) in H4 by flia Hni.
  flia H3 Hk H4.
 +destruct H3 as (j & Hjbef & Hjwhi & Hjaft).
  remember (rad * (i + 2)) as n1 eqn:Hn1.
  remember (n1 - i - 1) as s1 eqn:Hs1.
  move s1 before n1.
  destruct (lt_dec (nA i n1 (x ⊕ y)) (rad ^ s1)) as [H2| H2].
  *rewrite Nat.div_small; [ | easy ].
   rewrite Nat.add_0_r.
   rewrite Nat.mod_small; [ easy | apply digit_lt_radix ].
  *exfalso.
   specialize (Hy (i + j + 2)) as (k & Hk).
   specialize (Haft (i - n + j + 2 + k)).
   replace (n + (i - n + j + 2 + k)) with (i + j + 2 + k) in Haft by flia Hni.
   specialize (Hjaft k).
   rewrite Nat.add_shuffle0 in Hjaft.
   unfold "⊕" in Hjaft.
   rewrite Haft in Hjaft.
   flia Hjaft Hk.
-destruct H2 as (m & Hjm & Hm); simpl.
 apply A_ge_1_false_iff in Hm.
 remember (rad * (i + m + 2)) as n1 eqn:Hn1.
 remember (n1 - i - 1) as s1 eqn:Hs1.
 move s1 before n1.
 unfold "⊕" at 1.
 rewrite H4.
 destruct (lt_dec (nA i n1 (x ⊕ y)) (rad ^ s1)) as [H2| H2].
 +exfalso.
  rewrite Nat.mod_small in Hm; [ | easy ].
  apply Nat.nle_gt in Hm; apply Hm; clear Hm.
  clear - Hr Hn1 Hni Hs1 Haft.
  rewrite Hs1, Hn1.
  apply nA_ge_999000.
  intros k.
  unfold "⊕".
  specialize (Haft (i + k + 1 - n)).
  replace (n + (i + k + 1 - n)) with (i + k + 1) in Haft by flia Hni.
  rewrite Haft.
  flia.
 +apply Nat.nlt_ge in H2.
  rewrite Nat_div_less_small.
  *replace (rad - 1 + fd2n y i + 1) with (rad + fd2n y i) by flia Hr.
   rewrite Nat_mod_add_same_l; [ | easy ].
   rewrite Nat.mod_small; [ easy | ].
   apply digit_lt_radix.
  *split; [ easy | ].
   specialize (nA_upper_bound_for_add (x ⊕ y) i n1) as H3.
   rewrite <- Hs1 in H3.
   assert (H : ∀ k, (x ⊕ y) (i + k + 1) ≤ 2 * (rad - 1)). {
     intros k.
     unfold "⊕".
     replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
     apply Nat.add_le_mono; apply digit_le_pred_radix.
   }
   specialize (H3 H); clear H.
   eapply Nat.le_lt_trans; [ apply H3 | ].
   enough (H : 1 ≤ rad ^ s1) by flia H.
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

Theorem nA_9998 {r : radix} : ∀ u n n1 j,
  (∀ k : nat, k < j → u (n + k + 1) = rad - 1)
  → u (n + j + 1) = rad - 2
  → (∀ k : nat, u (n + j + k + 2) = 2 * (rad - 1))
  → j < n1 - n - 2
  → nA n n1 u = rad ^ (n1 - n - 1) - 2.
Proof.
intros * Hjbef Hjwhi Hjaft Hjs.
remember (n1 - n - 1) as s1 eqn:Hs1.
destruct s1; [ flia Hjs Hs1 | ].
replace (n1 - n - 1) with (S s1) by flia Hs1 Hjs.
replace (n1 - n - 2) with s1 in Hjs by flia Hs1.
specialize radix_ge_2 as Hr; move Hr before n.
unfold nA.
rewrite summation_shift; [ | flia Hs1 ].
replace (n1 - 1 - (n + 1)) with s1 by flia Hs1.
destruct j.
-rewrite summation_split_first; [ | apply Nat.le_0_l ].
 rewrite Nat.add_0_r in Hjwhi.
 rewrite Nat.add_0_r, Hjwhi.
 remember S as f; simpl; subst f.
 replace (n1 - 1 - (n + 1)) with s1 by flia Hs1.
 rewrite summation_rtl.
 rewrite summation_shift; [ | easy ].
 rewrite (summation_eq_compat _ (λ i, 2 * (rad - 1) * rad ^ i)).
 +rewrite <- summation_mul_distr_l.
  remember S as f; simpl; subst f.
  rewrite <- Nat.mul_assoc.
  rewrite <- power_summation_sub_1; [ | easy ].
  rewrite <- Nat.sub_succ_l; [ | easy ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  rewrite Nat.mul_sub_distr_r, Nat.mul_sub_distr_l, Nat.mul_1_r.
  rewrite Nat.add_sub_assoc.
  *rewrite Nat.sub_add; [ easy | ].
   now apply Nat.mul_le_mono_r.
  *replace 2 with (2 * 1) at 1 by apply Nat.mul_1_r.
   apply Nat.mul_le_mono_l.
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +intros i Hi.
  replace (n + 1 + (s1 + 1 - (1 + i))) with (n1 - i - 1) by flia Hs1 Hi.
  replace (n1 - 1 - (n1 - i - 1)) with i by flia Hs1 Hi.
  f_equal.
  replace (n1 - i - 1) with (n + (s1 - i - 1) + 2) by flia Hs1 Hi Hjs.
  rewrite Nat.add_0_r in Hjaft.
  apply Hjaft.
-rewrite (summation_split _ _ j); [ | flia Hjs ].
 rewrite summation_rtl, Nat.add_0_r.
 rewrite (summation_eq_compat _ (λ i, (rad - 1) * rad ^ (s1 - j + i))).
 +rewrite <- summation_mul_distr_l.
  remember S as f; simpl; subst f.
  rewrite (summation_eq_compat _ (λ i, rad ^ (s1 - j) * rad ^ i)).
  *rewrite <- summation_mul_distr_l.
   remember S as f; simpl; subst f.
   rewrite Nat.mul_assoc, Nat.mul_shuffle0.
   rewrite <- power_summation_sub_1; [ | easy ].
   rewrite summation_split_first; [ | flia Hjs ].
   remember S as f; simpl; subst f.
   rewrite Nat.add_shuffle0, Hjwhi.
   replace (n1 - 1 - (n + S j + 1)) with (s1 - j - 1) by flia Hs1.
   rewrite summation_shift; [ | flia Hjs ].
   rewrite summation_rtl.
   rewrite Nat.add_0_r.
   rewrite summation_eq_compat with (h := λ i, 2 * (rad - 1) * rad ^ i).
   --rewrite <- summation_mul_distr_l.
     remember S as f; simpl; subst f.
     rewrite <- Nat.mul_assoc.
     rewrite <- power_summation_sub_1; [ | easy ].
     rewrite <- Nat.sub_succ_l; [ | easy ].
     rewrite Nat.sub_succ.
     rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
     rewrite Nat.add_assoc.
     rewrite Nat.mul_sub_distr_r.
     replace (rad * rad ^ (s1 - j - 1)) with (rad ^ (s1 - j)).
     ++rewrite Nat.add_sub_assoc.
       **rewrite Nat.sub_add.
         ---rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
            rewrite Nat.add_sub_assoc.
            +++replace (s1 - j - 1) with (s1 - S j) by flia.
               rewrite <- Nat.pow_add_r.
               replace (S j + (s1 - j)) with (S s1) by flia Hjs.
               f_equal; apply Nat.sub_add.
               remember mult as f; simpl; subst f.
               apply Nat.mul_le_mono; [ easy | ].
               apply Nat.pow_le_mono_r; [ easy | flia ].
            +++replace 2 with (2 * 1) at 1 by apply Nat.mul_1_r.
               apply Nat.mul_le_mono_l.
               now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
         ---rewrite <- Nat.pow_add_r.
            apply Nat.pow_le_mono_r; [ easy | flia ].
       **rewrite Nat_sub_sub_swap.
         replace (s1 - j) with (1 + (s1 - j - 1)) by flia Hjs.
         rewrite Nat_sub_sub_swap.
         rewrite Nat.pow_add_r, Nat.pow_1_r.
         now apply Nat.mul_le_mono_r.
     ++replace (s1 - j) with (1 + (s1 - j - 1)) at 1 by flia Hjs.
       now rewrite Nat.pow_add_r, Nat.pow_1_r.
   --intros i Hi.
     replace (n + 1 + (S (S j) + (s1 - S (S j) - i)))
       with (n1 - i - 1) by flia Hs1 Hjs Hi.
     replace (n1 - 1 - (n1 - i - 1)) with i by flia Hs1 Hi.
     f_equal.
     replace (n1 - i - 1) with (n + S j + (s1 - j - i - 2) + 2)
       by flia Hs1 Hjs Hi.
     apply Hjaft.
  *intros; apply Nat.pow_add_r.
 +intros i Hi.
  rewrite Nat.add_shuffle0, Hjbef; [ | flia ].
  f_equal; f_equal; flia Hs1 Hi Hjs.
Qed.

Theorem not_prop_carr_all_9_all_ge_1 {r : radix} : ∀ u n,
  (∀ k : nat, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k : nat, A_ge_1 u n k = true)
  → (u n + 1 + nA n (rad * (n + 2)) u / rad ^ (rad * (n + 2) - n - 1))
       mod rad = rad - 1
  → ¬ (∀ k, d2n (prop_carr u) (n + k) = rad - 1).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur H2 H1 Hn.
specialize (A_ge_1_add_all_true_if _ _ Hur H2) as H3.
destruct H3 as [H3| [H3| H3]].
-rewrite Nat.div_small in H1.
 +rewrite Nat.add_0_r in H1.
  specialize (Hn 1) as H4.
  unfold prop_carr, d2n in H4; simpl in H4.
  unfold nat_prop_carr in H4.
  destruct (LPO_fst (A_ge_1 u (n + 1))) as [H5| H5].
  *rewrite Nat.div_small in H4.
   --rewrite Nat.add_0_r in H4.
     specialize (H3 0); rewrite Nat.add_0_r in H3.
     rewrite H3, Nat.sub_add in H4; [ | easy ].
     rewrite Nat.mod_same in H4; [ | easy ].
     flia Hr H4.
   --apply nA_dig_seq_ub.
     ++intros j Hj.
       specialize (H3 (j - n - 1)).
       replace (n + (j - n - 1) + 1) with j in H3 by flia Hj.
       flia Hr H3.
     ++destruct rad; [ easy | simpl; flia ].
  *destruct H5 as (j & Hjj & Hj); clear H4.
   apply A_ge_1_false_iff in Hj.
   apply Nat.nle_gt in Hj; apply Hj; clear Hj.
   rewrite Nat.mod_small.
   --apply nA_ge_999000.
     intros k.
     replace (n + 1 + k + 1) with (n + (1 + k) + 1) by flia.
     now rewrite H3.
   --apply nA_dig_seq_ub.
     ++intros k Hk.
       specialize (H3 (k - n - 1)).
       replace (n + (k - n - 1) + 1) with k in H3 by flia Hk.
       flia Hr H3.
     ++destruct rad; [ easy | simpl; flia ].
 +apply nA_dig_seq_ub.
  *intros k Hk.
   specialize (H3 (k - n - 1)).
   replace (n + (k - n - 1) + 1) with k in H3 by flia Hk.
   flia Hr H3.
  *destruct rad; [ easy | simpl; flia ].
-specialize (Hn 1) as H4.
 unfold prop_carr, d2n in H4; simpl in H4.
 unfold nat_prop_carr in H4.
 destruct (LPO_fst (A_ge_1 u (n + 1))) as [H5| H5]; simpl in H4.
 +specialize (H3 0) as H; rewrite Nat.add_0_r in H.
  rewrite H in H4; clear H.
  rewrite eq_nA_div_1 in H4.
  *rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H4.
   replace (2 * rad - 2 + 1 + 1) with (2 * rad) in H4 by flia Hr.
   rewrite Nat.mod_mul in H4; [ | easy ].
   flia Hr H4.
  *intros k.
   replace (n + 1 + k + 1) with (n + (1 + k) + 1) by flia.
   apply Hur.
  *remember (rad * (n + 1 + 2)) as n1 eqn:Hn1.
   remember (n1 - (n + 1) - 1) as s1 eqn:Hs1.
   move s1 before n1; symmetry in Hs1.
   unfold nA.
   rewrite (summation_eq_compat _ (λ i, 2 * (rad - 1) * rad ^ (n1 - 1 - i))).
   destruct s1.
   --apply Nat.sub_0_le in Hs1; apply Nat.nlt_ge in Hs1.
     exfalso; apply Hs1; clear Hs1; rewrite Hn1.
     destruct rad; [ easy | simpl; flia ].
   --rewrite <- summation_mul_distr_l.
     remember mult as f; remember S as g; simpl; subst f g.
     rewrite summation_rtl.
     rewrite summation_shift.
     ++replace (n1 - 1 - (n + 1 + 1)) with s1 by flia Hs1.
       rewrite (summation_eq_compat _ (λ i, rad ^ i)).
       **rewrite <- Nat.mul_assoc, <- power_summation_sub_1; [ | easy ].
         rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
         replace (2 * rad ^ S s1) with (rad ^ S s1 + rad ^ S s1) by flia.
         rewrite <- Nat.add_sub_assoc; [ flia | simpl ].
         replace 2 with (2 * 1) by apply Nat.mul_1_r.
         apply Nat.mul_le_mono; [ easy | ].
         now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
       **intros i Hi; f_equal; flia Hs1 Hi.
     ++rewrite Hn1.
       destruct rad; [ easy | simpl; flia ].
   --intros i Hi.
     specialize (H3 (i - n - 1)).
     replace (n + (i - n - 1) + 1) with i in H3 by flia Hi.
     now rewrite H3.
 +destruct H5 as (j & Hjj & Hj); simpl in H4.
  apply A_ge_1_false_iff in Hj.
  remember (rad * (n + 1 + j + 2)) as n1 eqn:Hn1.
  remember (n1 - (n + 1) - 1) as s1 eqn:Hs1.
  destruct s1.
  *symmetry in Hs1.
   apply Nat.sub_0_le in Hs1.
   rewrite Hn1 in Hs1.
   destruct rad; [ simpl in Hn1; now subst n1 | simpl in Hs1; flia Hs1 ].
  *assert (HnA : nA (n + 1) n1 u = rad ^ S s1 + (rad ^ S s1 - 2)). {
     unfold nA.
     rewrite summation_rtl.
     rewrite summation_shift; [ | flia Hs1 ].
     replace (n1 - 1 - (n + 1 + 1)) with s1 by flia Hs1.
     rewrite (summation_eq_compat _ (λ i, 2 * (rad - 1) * rad ^ i)).
     -rewrite <- summation_mul_distr_l.
      remember mult as f; remember S as g; simpl; subst f g.
      rewrite <- Nat.mul_assoc.
      rewrite <- power_summation_sub_1; [ | easy ].
      rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
      rewrite Nat.add_sub_assoc; [ flia | ].
      simpl; replace 2 with (2 * 1) by apply Nat.mul_1_r.
      apply Nat.mul_le_mono; [ easy | ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
     -intros i Hi.
      replace (n1 - 1 + (n + 1 + 1) - (n + 1 + 1 + i)) with (n1 - 1 - i)
        by flia.
      replace (n1 - 1 - (n1 - 1 - i)) with i by flia Hs1 Hi; f_equal.
      specialize (H3 (n1 - n - i - 2)).
      replace (n + (n1 - n - i - 2) + 1) with (n1 - 1 - i) in H3
        by flia Hs1 Hi.
      easy.
   }
   rewrite Nat_mod_less_small in Hj.
   --apply Nat.nle_gt in Hj; apply Hj; clear Hj.
     apply Nat.le_add_le_sub_l.
     (* 1/9/9/9/0/0/0/0 ≤ 18/18/18/18/18/18/18 (= 1/9/9/9/9/9/9/8) *)
     rewrite HnA.
     apply Nat.add_le_mono_l.
     rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
     rewrite <- Nat.pow_add_r.
     assert (Hjs : j < s1). {
       apply Nat.succ_lt_mono.
       rewrite Hs1, Hn1.
       destruct rad as [| rr]; [ easy | simpl ].
       destruct rr; [ flia Hr | simpl; flia ].
     }
     replace (S j + (S s1 - S j)) with (S s1); [ | flia Hjs ].
     apply Nat.sub_le_mono_l.
     rewrite Nat.sub_succ_l; [ simpl | easy ].
     replace 2 with (2 * 1) by apply Nat.mul_1_r.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   --rewrite HnA.
     split; [ flia | ].
     remember (S s1) as ss; simpl; subst ss.
     apply Nat.add_lt_mono_l.
     rewrite Nat.add_0_r.
     apply Nat.sub_lt; [ | flia ].
     simpl; replace 2 with (2 * 1) by apply Nat.mul_1_r.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
-destruct H3 as (j & Hjbef & Hjwhi & Hjaft).
 specialize (Hn (j + 1)) as H3.
 unfold d2n, prop_carr in H3; simpl in H3.
 unfold nat_prop_carr in H3.
 destruct (LPO_fst (A_ge_1 u (n + (j + 1)))) as [H4| H4].
 +simpl in H3.
  remember (rad * (n + (j + 1) + 2)) as n2 eqn:Hn2.
  remember (n2 - (n + (j + 1)) - 1) as s2 eqn:Hs2.
  move s2 before n2.
  rewrite Nat.add_assoc, Hjwhi in H3.
  specialize (nA_all_18 u (n + j + 1) n2) as H5.
  rewrite Nat.add_assoc in Hs2.
  rewrite <- Hs2 in H5.
  assert (H : ∀ k, u (n + j + 1 + k + 1) = 2 * (rad - 1)). {
    intros k.
    replace (n + j + 1 + k + 1) with (n + j + k + 2) by flia.
    apply Hjaft.
  }
  specialize (H5 H); clear H.
  rewrite H5 in H3.
  rewrite Nat_div_less_small in H3.
  *replace (rad - 2 + 1 + 1) with rad in H3 by flia Hr.
   rewrite Nat.mod_same in H3; [ flia Hr H3 | easy ].
  *specialize (Nat.pow_nonzero rad s2 radix_ne_0) as H.
   rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
   split; [ | flia H ].
   destruct s2.
   --exfalso.
     symmetry in Hs2.
     apply Nat.sub_0_le in Hs2.
     rewrite Hn2 in Hs2.
     destruct rad; [ easy | simpl in Hs2; flia Hs2 ].
   --enough (H6 : 2 ≤ rad ^ S s2) by flia H6; simpl.
     replace 2 with (2 * 1) by apply Nat.mul_1_r.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +destruct H4 as (k & Hjk & Hk); simpl in H3.
  specialize (H2 (j + 1 + k)).
  apply A_ge_1_add_r_true_if in H2.
  now rewrite H2 in Hk.
Qed.

Theorem eq_all_prop_carr_9_cond {r : radix} : ∀ u n,
  (∀ k, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, d2n (prop_carr u) (n + k) = rad - 1)
  → ∀ i, ∃ j,
  let n1 := rad * (n + i + j + 2) in
  let s1 := n1 - (n + i) - 1 in
  nA (n + i) n1 u mod rad ^ s1 < (rad ^ S j - 1) * rad ^ (s1 - S j) ∧
  (u (n + i) + nA (n + i) n1 u / rad ^ s1) mod rad = rad - 1.
Proof.
intros * Hur Hn *.
specialize (Hn i) as Huni.
unfold prop_carr, d2n in Huni; simpl in Huni.
unfold nat_prop_carr in Huni.
destruct (LPO_fst (A_ge_1 u (n + i))) as [H2| H2]; simpl in Huni.
-assert (Hn' : ∀ k, d2n (prop_carr u) ((n + i) + k) = rad - 1). {
   intros k.
   replace ((n + i) + k) with (n + (i + k)) by flia.
   apply Hn.
 }
 exfalso; revert Hn'.
 apply not_prop_carr_all_9_all_ge_1; [ | easy | easy ].
 intros k.
 replace (n + i + k + 1) with (n + (i + k) + 1) by flia.
 apply Hur.
-destruct H2 as (j & Hjj & Hj).
 simpl in Huni.
 apply A_ge_1_false_iff in Hj.
 exists j; easy.
Qed.

Theorem eq_all_prop_carr_9_cond1 {r : radix} : ∀ u i n s j,
  (∀ k, u (i + k) ≤ 2 * (rad - 1))
  → s = n - i - 1
  → j < s
  → nA i n u mod rad ^ s < (rad ^ S j - 1) * rad ^ (s - S j)
  → (u i + nA i n u / rad ^ s) mod rad = rad - 1
  → if lt_dec (nA i n u) (rad ^ s) then
       u i = rad - 1 ∧ u (i + 1) ≠ 2 * (rad - 1)
     else if lt_dec (u i) (rad - 1) then
       u i = rad - 2 ∧ u (i + 1) ≥ rad - 1
     else
       u i = 2 * (rad - 1) ∧ u (i + 1) ≥ rad - 1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hs1 Hs1z Hj1 Hun1.
destruct (lt_dec (nA i n u) (rad ^ s)) as [H4| H4].
-rewrite Nat.div_small in Hun1; [ | easy ].
 rewrite Nat.mod_small in Hj1; [ | easy ].
 clear H4.
 rewrite Nat.add_0_r in Hun1.
 destruct (lt_dec (u i) rad) as [H5| H5].
 +rewrite Nat.mod_small in Hun1; [ clear H5 | easy ].
  assert (Hur2 : u (i + 1) ≠ 2 * (rad - 1)). {
    intros H.
    apply Nat.nle_gt in Hj1; apply Hj1; clear Hj1.
    rewrite nA_split_first.
    -replace (n - i - 2) with (s - 1) by flia Hs1.
     rewrite H.
     apply le_plus_trans.
     rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
     rewrite <- Nat.pow_add_r.
     replace (S j + (s - S j)) with s.
     +rewrite <- Nat.mul_assoc, Nat.mul_sub_distr_r, Nat.mul_1_l.
      rewrite <- Nat.pow_succ_r'.
      rewrite <- Nat.sub_succ_l.
      *rewrite Nat.sub_succ, Nat.sub_0_r.
       rewrite Nat.mul_sub_distr_l.
       replace (2 * rad ^ s) with (rad ^ s + rad ^ s) by flia.
       rewrite <- Nat.add_sub_assoc; [ flia | ].
       destruct s; [ easy | ].
       rewrite Nat.sub_succ, Nat.sub_0_r.
       rewrite Nat.pow_succ_r'.
       now apply Nat.mul_le_mono_r.
      *flia Hs1z.
     +rewrite Nat.add_sub_assoc; [ flia | easy ].
    -flia Hs1 Hs1z.
  }
  easy.
 +apply Nat.nlt_ge in H5.
  specialize (Hur 0); rewrite Nat.add_0_r in Hur.
  rewrite Nat_mod_less_small in Hun1; [ flia Hur Hun1 Hr | ].
  split; [ easy | flia Hr Hur ].
-apply Nat.nlt_ge in H4.
 assert (H : rad ^ s ≤ nA i n u < 2 * rad ^ s). {
   split; [ easy | ].
   specialize (nA_upper_bound_for_add u i n) as H5.
   rewrite <- Hs1 in H5.
   assert (H : ∀ j, u (i + j + 1) ≤ 2 * (rad - 1)). {
     intros k; rewrite <- Nat.add_assoc; apply Hur.
   }
   specialize (H5 H); clear H.
   rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H5.
   specialize (Nat.pow_nonzero rad s radix_ne_0) as H6.
   flia Hr H5 H6.
 }
 rewrite Nat_div_less_small in Hun1; [ | easy ].
 rewrite Nat_mod_less_small in Hj1; [ clear H | easy ].
 assert (Hur1 : u (i + 1) ≥ rad - 1). {
   apply Nat.nlt_ge; intros H.
   apply Nat.nlt_ge in H4; apply H4; clear H4.
   clear - Hur Hs1 Hs1z H.
   specialize radix_ge_2 as Hr.
   replace (n - i - 2) with (s - 1) by flia Hs1.
   apply Nat.lt_le_pred in H.
   replace (pred (rad - 1)) with (rad - 2) in H by flia.
   rewrite nA_split_first.
   -eapply Nat.le_lt_trans.
    +apply Nat.add_le_mono_l.
     apply nA_upper_bound_for_add.
     intros k.
     replace (S i + k + 1) with (i + (k + 2)) by flia; apply Hur.
    +replace (n - S i - 1) with (s - 1) by flia Hs1.
     replace (n - i - 2) with (s - 1) by flia Hs1.
     eapply Nat.lt_le_trans.
     *apply Nat.add_lt_mono_r.
      eapply Nat.le_lt_trans.
     --apply Nat.mul_le_mono_pos_r; [ | apply H ].
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
     --apply Nat.lt_succ_diag_r.
     *destruct s; [ easy | ].
      rewrite Nat.sub_succ, Nat.sub_0_r.
      rewrite <- Nat.add_1_l, <- Nat.add_assoc.
      rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
      rewrite Nat.add_sub_assoc.
     --rewrite <- Nat.mul_add_distr_r.
       rewrite Nat.sub_add; [ | flia Hr ].
       rewrite <- Nat.pow_succ_r'.
       specialize (Nat.pow_nonzero rad (S s) radix_ne_0) as H1.
       flia H1.
     --replace 2 with (2 * 1) at 1 by flia.
       apply Nat.mul_le_mono_l.
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   -flia Hs1 Hs1z.
 }
 destruct (lt_dec (u i) (rad - 1)) as [H3| H3].
 +rewrite Nat.mod_small in Hun1; [ clear H3 | flia H3 ].
  assert (H : u i = rad - 2) by flia Hun1.
  clear Hun1; rename H into Hun1.
  easy.
 +apply Nat.nlt_ge in H3.
  specialize (Hur 0); rewrite Nat.add_0_r in Hur.
  rewrite Nat_mod_less_small in Hun1.
  *assert (H : u i = 2 * (rad - 1)) by flia Hun1.
   clear Hun1; rename H into Hun1.
   (* u(n+1)=18 *)
   easy.
  *split; [ flia H3 | flia Hr Hur ].
Qed.

Theorem A_ge_rad_pow {r : radix} : ∀ u i n,
  (∀ k, u (S i + k + 1) ≤ 2 * (rad - 1))
  → rad ^ (n - i - 1) ≤ nA i n u
  → ∃ j,
    j < n - i - 1 ∧
    (∀ k, k < j → u (i + k + 1) = rad - 1) ∧
    u (i + j + 1) ≥ rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hra.
remember (n - i - 1) as m eqn:Hm.
symmetry in Hm.
revert i n Hur Hm Hra.
induction m; intros.
-unfold nA in Hra.
 rewrite summation_empty in Hra; [ easy | flia Hm ].
-destruct n; [ easy | ].
 assert (Hm' : n - i - 1 = m) by flia Hm.
 destruct (le_dec (i + 1) n) as [Hin| Hin]; [ | flia Hin Hm ].
 rewrite nA_split_first in Hra; [ | flia Hin ].
 destruct (le_dec rad (u (i + 1))) as [H1| H1].
 +exists 0.
  split; [ apply Nat.lt_0_succ | ].
  split; [ now intros | ].
  now rewrite Nat.add_0_r.
 +apply Nat.nle_gt in H1.
  replace (S n - i - 2) with m in Hra by flia Hm.
  destruct (le_dec (u (i + 1)) (rad - 2)) as [H2| H2].
  *exfalso; apply Nat.nlt_ge in Hra.
   apply Hra; clear Hra.
   specialize (nA_upper_bound_for_add u (S i) (S n) Hur) as H3.
   replace (S n - S i - 1) with m in H3 by flia Hm'.
   apply le_lt_trans with (m := (rad - 2) * rad ^ m + 2 * (rad ^ m - 1)).
  --apply Nat.add_le_mono; [ | easy ].
    now apply Nat.mul_le_mono_r.
  --rewrite Nat.mul_sub_distr_r, Nat.mul_sub_distr_l, Nat.mul_1_r.
    rewrite Nat.add_sub_assoc.
   ++rewrite Nat.sub_add.
    **apply Nat.sub_lt; [ | flia ].
      simpl; replace 2 with (2 * 1) by flia.
      apply Nat.mul_le_mono; [ easy | ].
      now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    **now apply Nat.mul_le_mono_r.
   ++replace 2 with (2 * 1) at 1 by flia.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  *assert (H3 : u (i + 1) = rad - 1) by flia H1 H2.
    clear H1 H2.
    specialize (IHm (S i) (S n)) as H1.
    rewrite Nat.sub_succ in H1.
    assert (H : ∀ k, u (S (S i) + k + 1) ≤ 2 * (rad - 1)). {
      intros k.
      replace (S (S i) + k) with (S i + S k) by flia.
      apply Hur.
    }
    specialize (H1 H Hm'); clear H.
    rewrite H3 in Hra.
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l in Hra.
    rewrite <- Nat.add_sub_swap in Hra.
   --apply Nat.add_le_mono_r with (p := rad ^ m) in Hra.
     rewrite Nat.sub_add in Hra.
    ++apply Nat.add_le_mono_l in Hra.
      specialize (H1 Hra).
      destruct H1 as (j & Hjm & Hkj & Hj).
      exists (j + 1).
      split; [ flia Hjm | ].
      split.
     **intros k Hk.
       destruct k; [ now rewrite Nat.add_0_r | ].
       replace (i + S k) with (S i + k) by flia.
       apply Hkj; flia Hk.
     **now replace (i + (j + 1)) with (S i + j) by flia.
    ++apply le_plus_trans.
      rewrite <- Nat.pow_succ_r'.
      apply Nat.pow_le_mono_r; [ easy | apply Nat.le_succ_diag_r ].
   --rewrite <- Nat.pow_succ_r'.
     apply Nat.pow_le_mono_r; [ easy | apply Nat.le_succ_diag_r ].
Qed.

Theorem eq_all_prop_carr_9_cond2 {r : radix} : ∀ u n,
  (∀ k, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, d2n (prop_carr u) (n + k) = rad - 1)
  → ∀ k (i := n + k + 1),
     u i = rad - 1 ∧ u (i + 1) ≠ 2 * (rad - 1) ∨
     u i = rad - 2 ∧
       (∃ j, (∀ l, l < j → u (i + l + 1) = rad - 1) ∧ u (i + j + 1) ≥ rad) ∨
     u i = 2 * (rad - 1) ∧
       (∃ j, (∀ l, l < j → u (i + l + 1) = rad - 1) ∧ u (i + j + 1) ≥ rad).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hn k.
specialize (eq_all_prop_carr_9_cond u n Hur Hn) as HAF.
specialize (HAF (k + 1)) as Hun1.
destruct Hun1 as (j & Hj & Hun); simpl in Hun.
rewrite Nat.add_assoc in Hj, Hun.
remember (rad * (n + k + 1 + j + 2)) as n1 eqn:Hn1.
remember (n1 - (n + k + 1) - 1) as s1 eqn:Hs1.
move s1 before n1.
replace (n + k + 2) with (n + k + 1 + 1) by flia.
remember (n + k + 1) as i eqn:Hi.
specialize (eq_all_prop_carr_9_cond1 u i n1 s1 j) as H1.
assert (H : ∀ j, u (i + j) ≤ 2 * (rad - 1)). {
  intros l; subst i.
  replace (n + k + 1 + l) with (n + (k + l) + 1) by flia.
  apply Hur.
}
specialize (H1 H Hs1); clear H.
assert (H : j < s1). {
  rewrite Hs1, Hn1.
  destruct rad; [ easy | simpl; flia ].
}
specialize (H1 H Hj Hun); clear H.
destruct (lt_dec (nA i n1 u) (rad ^ s1)) as [H2| H2]; [ now left | right ].
apply Nat.nlt_ge in H2.
rewrite Hs1 in H2.
specialize (A_ge_rad_pow u i n1) as H3.
assert (H : ∀ k, u (S i + k + 1) ≤ 2 * (rad - 1)). {
  intros l; rewrite Hi.
  replace (S (n + k + 1) + l) with (n + (k + l + 2)) by flia.
  apply Hur.
}
specialize (H3 H H2); clear H.
rewrite <- Hs1 in H2.
destruct H3 as (j2 & Hj2 & Hkj2 & Hjr2).
destruct (lt_dec (u i) (rad - 1)) as [H3| H3].
-left; split; [ easy | now exists j2 ].
-right; split; [ easy | now exists j2 ].
Qed.

Theorem eq_all_prop_carr_9_cond3 {r : radix} : ∀ u n,
  (∀ k, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, d2n (prop_carr u) (n + k) = rad - 1)
  → ∀ k (i := n + k + 1),
     u i = rad - 1 ∧
       (u (i + 1) = rad - 2 ∨ u (i + 1) = rad - 1) ∨
     u i = rad - 2 ∧
       (∃ j,
           (∀ l, l < j → u (i + l + 1) = rad - 1) ∧
           u (i + j + 1) = 2 * (rad - 1)) ∨
     u i = 2 * (rad - 1) ∧
       (∃ j,
           (∀ l, l < j → u (i + l + 1) = rad - 1) ∧
           u (i + j + 1) = 2 * (rad - 1)).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hn k.
specialize (eq_all_prop_carr_9_cond2 u n Hur Hn k) as H.
remember (n + k + 1) as i eqn:Hi.
replace (n + k + 2) with (i + 1) by flia Hi.
destruct H as [H| [H| H]]; destruct H as (H1, H2).
-left; split; [ easy | ].
 specialize (eq_all_prop_carr_9_cond2 u n Hur Hn (k + 1)) as H.
 replace (n + (k + 1)) with i in H by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H3, H4).
 +now right.
 +now left.
 +easy.
-right; left; split; [ easy | ].
 destruct H2 as (j2 & Hlj2 & Hj2).
 exists j2.
 split; [ easy | ].
 specialize (eq_all_prop_carr_9_cond2 u n Hur Hn (i + j2 - n)) as H.
 replace (n + (i + j2 - n)) with (i + j2) in H by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H3, H4).
 +rewrite H3 in Hj2; flia Hr Hj2.
 +rewrite H3 in Hj2; flia Hr Hj2.
 +easy.
-right; right; split; [ easy | ].
 destruct H2 as (j2 & Hlj2 & Hj2).
 exists j2.
 specialize (eq_all_prop_carr_9_cond2 u n Hur Hn (i + j2 - n)) as H.
 replace (n + (i + j2 - n)) with (i + j2) in H by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H3, H4).
 +rewrite H3 in Hj2; flia Hr Hj2.
 +rewrite H3 in Hj2; flia Hr Hj2.
 +easy.
Qed.

Theorem eq_all_prop_carr_9_cond4 {r : radix} : ∀ u n,
  (∀ k, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, d2n (prop_carr u) (n + k) = rad - 1)
  → ∀ k (i := n + k + 1),
     u i = rad - 1 ∧ (u (i + 1) = rad - 2 ∨ u (i + 1) = rad - 1) ∨
     u i = rad - 2 ∧ u (i + 1) = 2 * (rad - 1) ∨
     u i = 2 * (rad - 1) ∧ u (i + 1) = 2 * (rad - 1).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hn k.
specialize (eq_all_prop_carr_9_cond3 u n Hur Hn k) as H.
remember (n + k + 1) as i eqn:Hi.
destruct H as [H| [H| H]]; [ now left | | ].
-right; left.
 destruct H as (Hui & j & Hlj & Hj).
 split; [ easy | ].
 destruct j; [ now rewrite Nat.add_0_r in Hj | ].
 specialize (Hlj j (Nat.lt_succ_diag_r j)) as H1.
 specialize (eq_all_prop_carr_9_cond3 u n Hur Hn (k + j + 1)) as H.
 rewrite Hi in Hj.
 replace (n + (k + j + 1) + 1) with (n + k + 1 + S j) in H by flia.
 replace (n + k + 1 + S j) with (i + j + 1) in H, Hj by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H2, H3).
 +exfalso.
  rewrite Hj in H3.
  destruct H3 as [H3| H3]; flia Hr H3.
 +rewrite H1 in H2; flia Hr H2.
 +rewrite H1 in H2; flia Hr H2.
-right; right.
 destruct H as (Hui & j & Hlj & Hj).
 split; [ easy | ].
 destruct j; [ now rewrite Nat.add_0_r in Hj | ].
 specialize (Hlj j (Nat.lt_succ_diag_r j)) as H1.
 specialize (eq_all_prop_carr_9_cond3 u n Hur Hn (k + j + 1)) as H.
 rewrite Hi in Hj.
 replace (n + (k + j + 1) + 1) with (n + k + 1 + S j) in H by flia.
 replace (n + k + 1 + S j) with (i + j + 1) in H, Hj by flia Hi.
 destruct H as [H| [H| H]]; destruct H as (H2, H3).
 +exfalso.
  rewrite Hj in H3.
  destruct H3 as [H3| H3]; flia Hr H3.
 +rewrite H1 in H2; flia Hr H2.
 +rewrite H1 in H2; flia Hr H2.
Qed.

Definition is_num_9_strict_after {r : radix} u i j :=
  if eq_nat_dec (u (i + j + 1)) (rad - 1) then true else false.

Theorem is_num_9_strict_after_all_9 {r : radix} : ∀ u i,
  (∀ j, is_num_9_strict_after u i j = true)
  → (∀ k, u (i + k + 1) = rad - 1).
Proof.
intros * Hm9 *.
specialize (Hm9 k); unfold is_num_9_strict_after in Hm9.
now destruct (Nat.eq_dec (u (i + k + 1)) (rad - 1)).
Qed.

Theorem is_num_9_strict_after_true_iff {r : radix} : ∀ i j u,
  is_num_9_strict_after u i j = true ↔ u (i + j + 1) = rad - 1.
Proof.
intros.
unfold is_num_9_strict_after.
now destruct (Nat.eq_dec (u (i + j + 1)) (rad - 1)).
Qed.

Theorem is_num_9_strict_after_false_iff {r : radix} : ∀ i j u,
  is_num_9_strict_after u i j = false ↔ u (i + j + 1) ≠ rad - 1.
Proof.
intros.
unfold is_num_9_strict_after.
now destruct (Nat.eq_dec (u (i + j + 1)) (rad - 1)).
Qed.

Theorem eq_all_prop_carr_9 {r : radix} : ∀ u n,
  (∀ k, u (n + k + 1) ≤ 2 * (rad - 1))
  → (∀ k, d2n (prop_carr u) (n + k) = rad - 1)
  → (∀ k, u (n + k + 1) = rad - 1) ∨
     (∀ k, u (n + k + 1) = 2 * (rad - 1)) ∨
     (∃ j,
       (∀ k, k < j → u (n + k + 1) = rad - 1) ∧
       u (n + j + 1) = rad - 2 ∧
       (∀ k, u (n + j + k + 2) = 2 * (rad - 1))).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hn.
specialize (eq_all_prop_carr_9_cond4 u n Hur Hn) as HAF.
destruct (LPO_fst (is_num_9_strict_after u n)) as [H1| H1].
-specialize (is_num_9_strict_after_all_9 u n H1) as H2.
 now left.
-destruct H1 as (i & Hji & Hi).
 apply is_num_9_strict_after_false_iff in Hi.
 destruct i.
 +specialize (HAF 0) as H1.
  rewrite Nat.add_0_r in Hi, H1.
  destruct H1 as [H1| [H1| H1]]; destruct H1 as (H1, H2).
  *easy.
  *right; right.
   exists 0.
   rewrite Nat.add_0_r.
   split; [ now intros | ].
   split; [ easy | ].
   replace (n + 1 + 1) with (n + 2) in H2 by flia.
   intros k.
   induction k; [ now rewrite Nat.add_0_r | ].
   specialize (HAF (k + 1)) as H3.
   replace (n + (k + 1) + 1) with (n + k + 2) in H3 by flia.
   destruct H3 as [H3| [H3| H3]]; destruct H3 as (H3, H4).
  --rewrite H3 in IHk; flia Hr IHk.
  --rewrite H3 in IHk; flia Hr IHk.
  --now replace (n + k + 2 + 1) with (n + S k + 2) in H4 by flia.
  *right; left.
   intros k.
   induction k; [ now rewrite Nat.add_0_r | ].
   specialize (HAF k) as H3.
   destruct H3 as [H3| [H3| H3]]; destruct H3 as (H3, H4).
  --rewrite H3 in IHk; flia Hr IHk.
  --rewrite H3 in IHk; flia Hr IHk.
  --now replace (n + k + 1 + 1) with (n + S k + 1) in H4 by flia.
 +specialize (Hji i (Nat.lt_succ_diag_r i)) as H1.
  apply is_num_9_strict_after_true_iff in H1.
  right; right.
  exists (S i).
  split.
  *intros k Hk.
   specialize (Hji _ Hk).
   now apply is_num_9_strict_after_true_iff in Hji.
  *replace (n + S i + 1) with (n + i + 2) in Hi |-* by flia.
   specialize (HAF i) as H2.
   destruct H2 as [H2| [H2| H2]]; destruct H2 as (H2, H3).
  --replace (n + i + 1 + 1) with (n + i + 2) in H3 by flia.
    destruct H3 as [H3| H3]; [ | easy ].
    split; [ easy | ].
    intros k.
    induction k.
   ++rewrite Nat.add_0_r.
     replace (n + S i + 2) with (n + i + 3) by flia.
     specialize (HAF (i + 1)) as H4.
     destruct H4 as [H4| [H4| H4]]; destruct H4 as (H4, H5).
    **replace (n + (i + 1) + 1) with (n + i + 2) in H4 by flia.
      rewrite H3 in H4; flia Hr H4.
    **now replace (n + (i + 1) + 1 + 1) with (n + i + 3) in H5 by flia.
    **now replace (n + (i + 1) + 1 + 1) with (n + i + 3) in H5 by flia.
   ++replace (n + S i + k + 2) with (n + i + k + 3) in IHk by flia.
     replace (n + S i + S k + 2) with (n + i + k + 4) by flia.
     specialize (HAF (i + k + 2)) as H4.
     replace (n + (i + k + 2) + 1) with (n + i + k + 3) in H4 by flia.
     destruct H4 as [H4| [H4| H4]]; destruct H4 as (H4, H5).
    **rewrite H4 in IHk; flia Hr IHk.
    **rewrite H4 in IHk; flia Hr IHk.
    **now replace (n + i + k + 3 + 1) with (n + i + k + 4) in H5 by flia.
  --rewrite H1 in H2; flia Hr H2.
  --rewrite H1 in H2; flia Hr H2.
Qed.

Theorem u_9_8_18_nA_ge_999000 {r : radix} : ∀ u n j j1 n1 s1,
  (∀ k, k < S j → u (n + k + 1) = rad - 1)
  → u (n + S j + 1) = rad - 2
  → (∀ k, u (n + S j + k + 2) = 2 * (rad - 1))
  → n1 = rad * (n + 1 + j1 + 2)
  → s1 = n1 - (n + 1) - 1
  → (rad ^ S j1 - 1) * rad ^ (s1 - S j1) ≤ nA (n + 1) n1 u.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hbef Hwhi Haft Hn1 Hs1.
unfold nA.
assert (Hsjs1 : S j1 + (s1 - S j1) = s1). {
  rewrite Hs1, Hn1.
  destruct rad; [ easy | simpl; flia ].
}
assert (Hs12 : 2 ≤ s1). {
  rewrite Hs1, Hn1.
  destruct rad as [| rr]; [ easy | simpl ].
  destruct rr; [ flia Hr | simpl; flia ].
}
assert (H2rsj : 2 ≤ rad ^ (s1 - S j1)). {
  destruct (zerop (s1 - S j1)) as [Hsj| Hsj].
  -rewrite Hs1, Hn1 in Hsj.
   destruct rad as [| rr]; [ easy | simpl in Hsj ].
   destruct rr; [ flia Hr | simpl in Hsj; flia Hsj ].
  -destruct (s1 - S j1) as [| x]; [ flia Hsj | simpl ].
   replace 2 with (2 * 1) by flia.
   apply Nat.mul_le_mono; [ easy | ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
rewrite summation_eq_compat with
    (h := λ k,
          (if le_dec k (n + j + 1) then rad - 1
           else if eq_nat_dec k (n + j + 2) then rad - 2
                else 2 * (rad - 1)) *
          rad ^ (n1 - 1 - k)).
-destruct (zerop j) as [Hj| Hj].
 +subst j; rewrite Nat.add_0_r.
  rewrite summation_split_first.
  *destruct (le_dec (n + 1 + 1) (n + 1)) as [H1| H1]; [ flia H1 | clear H1 ].
   destruct (Nat.eq_dec (n + 1 + 1) (n + 2)) as [H1| H1]; [ | flia H1 ].
   clear H1; remember S as f; simpl; subst f.
   replace (n1 - 1 - (n + 1 + 1)) with (s1 - 1) by flia Hs1.
   rewrite summation_eq_compat with
     (h := λ i, 2 * (rad - 1) * rad ^ (n1 - 1 - i)).
  --rewrite <- summation_mul_distr_l.
    remember S as f; simpl; subst f.
    rewrite summation_rtl.
    rewrite summation_shift.
   **rewrite summation_eq_compat with (h := λ k, rad ^ k).
   ---replace (n1 - 1 - S (n + 1 + 1)) with (s1 - 2) by flia Hs1.
      rewrite <- Nat.mul_assoc.
      rewrite <- power_summation_sub_1; [ | easy ].
      rewrite <- Nat.sub_succ_l; [ | easy ].
      rewrite Nat.sub_succ.
      rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
      rewrite Nat.add_sub_assoc.
    +++remember (rad ^ S j1 - 1) as x eqn:Hx.
       rewrite Nat.mul_sub_distr_r; subst x.
       rewrite Nat.sub_add; [ | now apply Nat.mul_le_mono_r ].
       rewrite <- Nat.pow_succ_r'.
       replace (S (s1 - 1)) with s1 by flia Hs12.
       rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
       rewrite <- Nat.pow_add_r, Hsjs1.
       now apply Nat.sub_le_mono_l.
    +++replace 2 with (2 * 1) at 1 by flia.
       apply Nat.mul_le_mono_l.
       now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   ---intros i Hi; f_equal; flia Hi.
   **rewrite Hn1.
     destruct rad as [| rr]; [ easy | simpl ].
     destruct rr; [ flia Hr | simpl; flia ].
  --intros i Hi; f_equal.
    destruct (le_dec i (n + 1)) as [H1| H1]; [ flia Hi H1 | ].
    destruct (Nat.eq_dec i (n + 2)) as [H2| H2]; [ flia Hi H2 | easy ].
  *rewrite Hn1.
   destruct rad; [ easy | simpl; flia ].
 +destruct (le_dec (n + j + 1) (n1 - 1)) as [Hnn| Hnn].
  *rewrite summation_split with (e := n + j + 1); [ | flia Hj Hnn ].
   remember S as f; simpl; subst f.
   rewrite summation_eq_compat with
       (h := λ k, (rad - 1) * rad ^ (n1 - 1 - k)).
  --rewrite <- summation_mul_distr_l.
    remember S as f; simpl; subst f.
    rewrite summation_rtl.
    rewrite summation_shift; [ | flia Hj ].
    replace (n + j + 1 - (n + 1 + 1)) with (j - 1) by flia.
    rewrite summation_eq_compat with (h := λ i, rad ^ i * rad ^ (s1 - j)).
   ++rewrite <- summation_mul_distr_r.
     rewrite Nat.mul_assoc.
     rewrite <- power_summation_sub_1; [ | easy ].
     replace (S (j - 1)) with j by flia Hj.
     destruct (eq_nat_dec (n + j + 1) (n1 - 1)) as [H1| H1].
    **rewrite H1, summation_empty; [ | apply Nat.lt_succ_diag_r ].
      rewrite Nat.add_0_r.
      remember S as f; simpl; subst f.
      do 2 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
      do 2 rewrite <- Nat.pow_add_r.
      rewrite Hsjs1.
      replace (j + (s1 - j)) with s1 by flia Hs1 H1.
      apply Nat.sub_le_mono_l.
      apply Nat.pow_le_mono_r; [ easy | ].
      apply Nat.sub_le_mono_l; flia Hsjs1 Hs1 H1.
    **rewrite summation_split_first; [ | flia Hnn H1 ].
      remember (n + j + 1) as x.
      replace (n + j + 2) with (x + 1) by flia Heqx.
      destruct (le_dec (S x) x) as [H2| H2]; [ flia H2 | clear H2 ].
      destruct (eq_nat_dec (S x) (x + 1)) as [H2| H2]; [ clear H2 | flia H2 ].
      destruct (le_dec (S (S x)) (n1 - 1)) as [H2| H2].
    ---rewrite summation_eq_compat with
         (h := λ i, 2 * (rad - 1) * (rad ^ (n1 - 1 - i))).
     +++rewrite <- summation_mul_distr_l.
        remember S as f; simpl; subst f.
        rewrite summation_rtl.
        rewrite summation_shift; [ | easy ].
        rewrite summation_eq_compat with (h := λ i, rad ^ i).
      ***rewrite <- Nat.mul_assoc.
         rewrite <- power_summation_sub_1; [ | easy ].
         replace (n1 - 1 - S x) with (s1 - j - 1) by flia Hs1 Heqx.
         replace (S (n1 - 1 - S (S x))) with (s1 - j - 1) by flia Hs1 H2 Heqx.
         subst x.
         do 2 rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r, Nat.mul_1_l.
         rewrite Hsjs1.
         replace (j + (s1 - j)) with s1 by flia Hs1 Hnn.
         rewrite Nat.mul_sub_distr_r.
         rewrite <- Nat.pow_succ_r'.
         replace (S (s1 - j - 1)) with (s1 - j) by flia Hs1 Hnn H1.
         rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
         rewrite Nat.add_sub_assoc.
      ----rewrite Nat.sub_add.
       ++++rewrite Nat.add_sub_assoc.
        ****rewrite Nat.sub_add; [ now apply Nat.sub_le_mono_l | ].
            apply Nat.pow_le_mono_r; [ easy | flia ].
        ****remember (s1 - j) as x eqn:Hx.
            destruct x; [ flia Hs1 H2 Hx | ].
            simpl; replace 2 with (2 * 1) by flia.
            apply Nat.mul_le_mono; [ easy | ].
            now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
       ++++replace (s1 - j) with (s1 - j - 1 + 1) by flia Hs1 Hnn H1.
           rewrite Nat.add_sub, Nat.pow_add_r, Nat.mul_comm, Nat.pow_1_r.
           now apply Nat.mul_le_mono_l.
      ----replace 2 with (2 * 1) by flia.
          apply Nat.mul_le_mono_l.
          now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
      ***intros i Hi; f_equal; flia Hi.
     +++intros i Hi.
        destruct (le_dec i x) as [H3| H3]; [ flia Hi H3 | ].
        destruct (eq_nat_dec i (x + 1)) as [H4| H4]; [ flia Hi H4 | easy ].
    ---apply Nat.nle_gt in H2; subst x.
       assert (Hnj : n + j + 1 = n1 - 2) by flia H1 H2 Hnn.
       assert (Hsjj : S j1 ≤ j). {
         rewrite Hn1 in Hnj.
         destruct rad as [| rr]; [ easy | simpl in Hnj ].
         destruct rr; [ flia Hr | simpl in Hnj; flia Hnj ].
       }
       apply le_plus_trans.
       do 2 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
       do 2 rewrite <- Nat.pow_add_r.
       rewrite Hsjs1.
       replace (j + (s1 - j)) with s1 by flia Hs1 Hnj.
       apply Nat.sub_le_mono_l.
       apply Nat.pow_le_mono_r; [ easy | ].
       now apply Nat.sub_le_mono_l.
   ++intros i Hi; rewrite <- Nat.pow_add_r; f_equal.
     rewrite Hs1; flia Hnn Hi.
  --intros i Hi.
    destruct (le_dec i (n + j + 1)) as [H1| H1]; [ easy | flia Hi H1 ].
  *apply Nat.nle_gt in Hnn.
   rewrite summation_eq_compat with
     (h := λ i, (rad - 1) * rad ^ (n1 - 1 - i)).
  --rewrite <- summation_mul_distr_l.
    rewrite summation_rtl.
    rewrite summation_shift; [ | flia Hs1 Hsjs1 ].
    replace (n1 - 1 - (n + 1 + 1)) with (s1 - 1) by flia Hs1.
    rewrite summation_eq_compat with (h := λ i, rad ^ i).
   ++rewrite <- power_summation_sub_1; [ | easy ].
     replace (S (s1 - 1)) with s1 by flia Hs12.
     rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
     rewrite <- Nat.pow_add_r, Hsjs1.
     apply Nat.sub_le_mono_l.
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   ++intros i Hi; f_equal; flia Hs1 Hi.
  --intros i Hi.
    destruct (le_dec i (n + j + 1)) as [H1| H1]; [ easy | flia Hnn Hi H1 ].
-intros k Hk; f_equal.
 destruct (le_dec k (n + j + 1)) as [H1| H1].
 +specialize (Hbef (k - n - 1)) as H2.
  replace (n + (k - n - 1) + 1) with k in H2 by flia Hk.
  apply H2; flia H1 Hk.
 +apply Nat.nle_gt in H1.
  destruct (eq_nat_dec k (n + j + 2)) as [H2| H2].
  **now replace (n + S j + 1) with k in Hwhi by flia H2.
  **specialize (Haft (k - n - j - 3)) as H3.
    replace (n + S j + (k - n - j - 3) + 2) with k in H3; [ easy | ].
    flia H1 H2.
Qed.

Theorem u_18_nA_mod_ge_999000 {r : radix} : ∀ u n1 s1 j1 n,
  (∀ k, u (n + k + 2) = 2 * (rad - 1))
  → n1 = rad * (n + 1 + j1 + 2)
  → s1 = n1 - (n + 1) - 1
  → rad ^ s1 ≤ nA (n + 1) n1 u
  → 0 < s1
  → (rad ^ S j1 - 1) * rad ^ (s1 - S j1) ≤ nA (n + 1) n1 u mod rad ^ s1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hall Hn1 Hs1 H1 Hjs.
rewrite Nat_mod_less_small.
-assert (Hjs1 : S j1 < s1). {
   rewrite Hs1, Hn1.
   destruct rad as [| rr]; [ easy | simpl ].
   destruct rr; [ flia Hr | simpl; flia ].
 }
 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
 rewrite <- Nat.pow_add_r.
 replace (S j1 + (s1 - S j1)) with s1 by flia Hjs1.
 rewrite nA_eq_compat with (v := λ k, 2 * (rad - 1)).
 +unfold nA.
  rewrite <- summation_mul_distr_l.
  rewrite summation_rtl.
  rewrite summation_shift.
  *remember S as f; simpl; subst f.
   replace (n1 - 1 - (n + 1 + 1)) with (s1 - 1) by flia Hs1.
   rewrite summation_eq_compat with (h := λ i, rad ^ i).
   --rewrite <- Nat.mul_assoc.
     rewrite <- power_summation_sub_1; [ | easy ].
     replace (S (s1 - 1)) with s1 by flia Hjs.
     rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
     rewrite Nat_sub_sub_swap.
     replace (2 * rad ^ s1 - rad ^ s1) with (rad ^ s1) by flia.
     apply Nat.sub_le_mono_l.
     destruct (zerop (s1 - S j1)) as [H2| H2]; [ flia Hjs1 H2 | ].
     destruct (s1 - S j1); [ easy | ].
     simpl; replace 2 with (2 * 1) by flia.
     apply Nat.mul_le_mono; [ easy | ].
     now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
   --intros i Hi; f_equal; flia Hs1 Hi.
  *rewrite Hn1.
   destruct rad; [ easy | simpl; flia ].
 +intros j Hj.
  specialize (Hall (j - n - 2)).
  now replace (n + (j - n - 2) + 2) with j in Hall by flia Hj.
-split; [ easy | ].
 specialize (nA_upper_bound_for_add u (n + 1) n1) as H2.
 rewrite <- Hs1 in H2.
 assert (H : ∀ k, u (n + 1 + k + 1) ≤ 2 * (rad - 1)). {
   intros k.
   replace (n + 1 + k + 1) with (n + k + 2) by flia.
   now rewrite Hall.
 }
 specialize (H2 H); clear H.
 rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H2.
 eapply le_lt_trans; [ apply H2 | ].
 specialize (Nat.pow_nonzero rad s1 radix_ne_0) as H.
 flia H2 H.
Qed.

Theorem not_prop_carr_all_9 {r : radix} : ∀ u n,
  (∀ k, u (n + k + 1) ≤ 2 * (rad - 1))
  → ¬ (∀ k, d2n (prop_carr u) (n + k) = rad - 1).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hn.
specialize (eq_all_prop_carr_9 u n Hur Hn) as Hall.
specialize (eq_all_prop_carr_9_cond u n Hur Hn) as HAF.
specialize (HAF 1) as Hun1.
destruct Hun1 as (j1 & Hj1 & Hun1); simpl in Hun1.
remember (rad * (n + 1 + j1 + 2)) as n1 eqn:Hn1.
remember (n1 - (n + 1) - 1) as s1 eqn:Hs1.
move s1 before n1.
destruct (lt_dec (nA (n + 1) n1 u) (rad ^ s1)) as [H1| H1].
-rewrite Nat.div_small in Hun1; [ | easy ].
 rewrite Nat.mod_small in Hj1; [ | easy ].
 clear H1.
 rewrite Nat.add_0_r in Hun1.
 destruct (lt_dec (u (n + 1)) rad) as [H1| H1].
 +rewrite Nat.mod_small in Hun1; [ clear H1 | easy ].
  (* u(n+1)=9 *)
  destruct Hall as [Hall| [Hall| Hall]].
  *apply Nat.nle_gt in Hj1.
   apply Hj1; clear Hj1.
   unfold nA.
   rewrite summation_eq_compat with
     (h := λ j, (rad - 1) * rad ^ (n1 - 1 - j)).
  --rewrite <- summation_mul_distr_l.
    remember S as f; simpl; subst f.
    rewrite summation_rtl, summation_shift.
   ++replace (n1 - 1 - (n + 1 + 1)) with (s1 - 1) by flia Hs1.
     rewrite summation_eq_compat with (h := λ i, rad ^ i).
    **rewrite <- power_summation_sub_1; [ | easy ].
      rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
      rewrite <- Nat.pow_add_r.
      replace (S j1 + (s1 - S j1)) with s1.
    ---rewrite <- Nat.sub_succ_l.
     +++rewrite Nat.sub_succ, Nat.sub_0_r.
        apply Nat.sub_le_mono_l.
        now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
     +++destruct s1; [ | flia ].
        rewrite Hn1 in Hs1.
        destruct rad; [ easy | simpl in Hs1; flia Hs1 ].
    ---rewrite Hs1, Hn1.
       destruct rad; [ easy | simpl; flia ].
    **intros i Hi; f_equal; flia Hs1 Hi.
   ++rewrite Hn1.
     destruct rad; [ easy | simpl; flia ].
  --intros i Hi; f_equal.
    specialize (Hall (i - n - 1)).
    now replace (n + (i - n - 1) + 1) with i in Hall by flia Hi.
  *specialize (Hall 0); rewrite Nat.add_0_r in Hall.
   flia Hr Hall Hun1.
  *destruct Hall as (j & Hkj & Huj & Hall).
   destruct j; [ rewrite Nat.add_0_r in Huj; flia Hr Huj Hun1 | ].
   apply Nat.nle_gt in Hj1.
   apply Hj1; clear Hj1.
   now apply (u_9_8_18_nA_ge_999000 _ _ j).
 +apply Nat.nlt_ge in H1.
  specialize (Hur 0); rewrite Nat.add_0_r in Hur.
  rewrite Nat_mod_less_small in Hun1; [ flia Hr Hur Hun1 | ].
  split; [ easy | flia Hr Hur ].
-apply Nat.nlt_ge in H1.
 specialize (A_ge_rad_pow u (n + 1) n1) as H2.
 rewrite <- Hs1 in H2.
 assert (H : ∀ k, u (S (n + 1) + k + 1) ≤ 2 * (rad - 1)). {
   intros k.
   replace (S (n + 1) + k) with (n + (k + 2)) by flia.
   apply Hur.
 }
 specialize (H2 H H1); clear H.
 destruct H2 as (j & Hjs & Hkj & Huj).
 destruct j.
 +rewrite Nat.add_0_r in Huj; clear Hkj.
  destruct Hall as [Hall| [Hall| Hall]].
  *specialize (Hall 1); rewrite Hall in Huj; flia Hr Huj.
  *assert (H : ∀ k, u (n + k + 2) = 2 * (rad - 1)). {
     intros k.
     replace (n + k + 2) with (n + (k + 1) + 1) by flia.
     apply Hall.
   }
   move H before Hall; clear Hall; rename H into Hall.
   apply Nat.nle_gt in Hj1; apply Hj1; clear Hj1.
   now apply (u_18_nA_mod_ge_999000 u n1 s1 j1 n).
  *destruct Hall as (j & Hbef & Hwhi & Haft).
   destruct j.
  --rewrite Nat.add_0_r in Hwhi, Haft; clear Hbef.
    apply Nat.nle_gt in Hj1; apply Hj1; clear Hj1.
    now apply (u_18_nA_mod_ge_999000 u n1 s1 j1 n).
  --destruct j; [ rewrite Hwhi in Huj; flia Hr Huj | ].
    rewrite Hbef in Huj; [ flia Hr Huj | flia ].
 +destruct Hall as [Hall| [Hall| Hall]].
  *replace (n + 1 + S j + 1) with (n + (j + 2) + 1) in Huj by flia.
   rewrite Hall in Huj; flia Hr Huj.
  *specialize (Hkj 0 (Nat.lt_0_succ j)).
   rewrite Nat.add_0_r in Hkj.
   rewrite Hall in Hkj.
   flia Hr Hkj.
  *destruct Hall as (i & Hbef & Hwhi & Haft).
   destruct (lt_dec i (S (S j))) as [H2| H2].
  --destruct i.
   ++specialize (Haft j).
     replace (n + 0 + j + 2) with (n + 1 + j + 1) in Haft by flia.
     specialize (Hkj j (Nat.lt_succ_diag_r j)).
     rewrite Haft in Hkj; flia Hr Hkj.
   ++apply Nat.succ_lt_mono in H2.
     specialize (Hkj i H2).
     replace (n + 1 + i) with (n + S i) in Hkj by flia.
     rewrite Hwhi in Hkj; flia Hr Hkj.
  --destruct (eq_nat_dec i (S (S j))) as [H3| H3].
   ++rewrite H3 in Hwhi.
     replace (n + S (S j)) with (n + 1 + S j) in Hwhi by flia.
     rewrite Hwhi in Huj; flia Hr Huj.
   ++assert (H4 : S (S j) < i) by flia H2 H3.
     specialize (Hbef _ H4).
     replace (n + S (S j)) with (n + 1 + S j) in Hbef by flia.
     rewrite Hbef in Huj; flia Hr Huj.
Qed.

(*
Theorem freal_eq_add_norm_l {r : radix} : ∀ x y,
  (freal_add (freal_normalize x) y = freal_add x y)%F.
Proof.
intros.
specialize radix_ge_2 as Hr.
specialize (freal_normalized_cases x) as [H1| H1].
-unfold freal_eq.
 now rewrite H1.
-destruct H1 as (n & Hbef & Hwhi & Hnaft & Haft).
 specialize (ends_with_999_or_not y) as [Hy9| Hy9].
 +unfold "="%F.
  apply eq_freal_norm_eq_true_iff.
  intros i.
  remember (freal_normalize x) as nx eqn:Hnx.
  remember (freal_add nx y) as nxy eqn:Hnxy.
  remember (freal_add x y) as xy eqn:Hxy.
  move xy before nxy.
  destruct (le_dec n i) as [Hni| Hni].
  *assert (H1 : fd2n (freal_normalize nxy) i = fd2n (freal_normalize y) i). {
     now eapply add_norm_0_l.
   }
   assert (H3 : fd2n (freal_normalize xy) i = fd2n (freal_normalize y) i). {
     unfold freal_normalize, fd2n; simpl.
     unfold digit_sequence_normalize.
     specialize (unorm_add_inf_pred_rad x y n Haft Hy9 i Hni) as H2i.
     unfold fd2n in H2i; unfold d2n; rewrite <- Hxy in H2i.
     apply digit_eq_eq in H2i.
     rewrite H2i.
     destruct (LPO_fst (is_9_strict_after (freal xy) i)) as [H3| H3].
     -specialize (is_9_strict_after_all_9 _ i H3) as H4; clear H3.
      destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H3| H3].
      +easy.
      +destruct H3 as (k & Hjk & Hk).
       apply is_9_strict_after_false_iff in Hk.
       exfalso.
       specialize (unorm_add_inf_pred_rad x y n Haft Hy9 (i + k + 1)) as H3.
       rewrite <- Hxy in H3; unfold fd2n in H3.
       assert (H : n ≤ i + k + 1) by flia Hni.
       specialize (H3 H); clear H.
       unfold d2n in H4.
       rewrite H4 in H3.
       now symmetry in H3.
     -destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H4| H4].
      +destruct H3 as (k & Hjk & Hk).
       apply is_9_strict_after_false_iff in Hk.
       specialize (is_9_strict_after_all_9 _ i H4) as H5; clear H4.
       specialize (unorm_add_inf_pred_rad x y n Haft Hy9 (i + k + 1)) as H3.
       rewrite <- Hxy in H3; unfold fd2n in H3.
       assert (H : n ≤ i + k + 1) by flia Hni.
       specialize (H3 H); clear H.
       unfold d2n in H5.
       now rewrite H5 in H3.
      +easy.
   }
   now rewrite H1, H3.
  *apply Nat.nle_gt in Hni.
   destruct Hwhi as [| Hwhi ]; [ now subst n | ].
   destruct n; [ easy | ].
   replace (S n - 1) with n in Hbef, Hwhi by flia.
   unfold freal_normalize, fd2n; simpl.
   unfold digit_sequence_normalize.
   destruct (LPO_fst (is_9_strict_after (freal nxy) i)) as [H1| H1].
  --specialize (is_9_strict_after_all_9 _ _ H1) as H2; clear H1.
    exfalso.
    assert (H1 : ∀ k, dig (prop_carr (fd2n y) (S n + k)) = rad - 1). {
      intros k.
      specialize (H2 (S n + k - S i)) as H1.
      replace (i + (S n + k - S i) + 1) with (S n + k) in H1 by flia Hni.
      rewrite Hnxy in H1.
      unfold freal_add in H1; remember S as f; simpl in H1; subst f.
      unfold freal_add_to_seq, d2n in H1.
      rewrite prop_carr_eq_compat_from with (g := fd2n y) in H1.
      -easy.
      -intros j.
       unfold "⊕".
       rewrite Hnaft; apply digit_lt_radix.
      -intros j.
       unfold "⊕".
       now rewrite Hnaft.
    }
    assert (H3 : ∀ k, fd2n (freal_normalize y) (S n + k) = rad - 1). {
      intros k.
      unfold fd2n.
      rewrite <- prop_carr_normalize.
      apply H1.
    }
    specialize (normalized_not_999 y) as H4.
    apply H4.
    exists (S n); easy.
  --destruct H1 as (j & Hjj & Hj).
    apply is_9_strict_after_false_iff in Hj.
    destruct (LPO_fst (is_9_strict_after (freal xy) i)) as [H1| H1].
   ++specialize (is_9_strict_after_all_9 _ _ H1) as H2; clear H1.
     assert (H3 : ∀ k, d2n (freal xy) (i + 1 + k) = rad - 1). {
       intros k.
       replace (i + 1 + k) with (i + k + 1) by flia.
       apply H2.
     }
     rewrite Hxy in H3.
     unfold freal_add in H3; simpl in H3.
     unfold freal_add_to_seq in H3.
     apply not_prop_carr_all_9 in H3; [ easy | ].
     intros k.
     unfold "⊕", fd2n.
     specialize (digit_lt_radix (freal x (i + 1 + k + 1))) as H4.
     specialize (digit_lt_radix (freal y (i + 1 + k + 1))) as H5.
     flia H4 H5.
   ++destruct H1 as (k & Hjk & Hk).
     apply is_9_strict_after_false_iff in Hk.
     destruct (eq_nat_dec i n) as [Hin| Hin].
    **clear Hni; subst i.
      rewrite Hnxy, Hxy.
      unfold freal_add; simpl.
      unfold freal_add_to_seq.
      set (u := x ⊕ y).
      set (v := freal_add_series nx y).
      unfold prop_carr.
      destruct (LPO_fst (A_ge_1 v n)) as [H1| H1].
    ---exfalso.
       specialize (A_ge_1_add_all_true_if v) as H2.
       specialize (H2 n).
       assert (H : ∀ k, v (n + k + 1) ≤ 2 * (rad - 1)). {
         intros l; unfold v.
         unfold "⊕", fd2n.
         specialize (digit_lt_radix (freal nx (n + l + 1))) as H4.
         specialize (digit_lt_radix (freal y (n + l + 1))) as H5.
         flia H4 H5.
       }
       specialize (H2 H H1); clear H.
       unfold v in H2.
       unfold "⊕" in H2.
       destruct H2 as [H2| [H2| H2]].
     +++specialize (Hy9 (n + 1)) as (i & Hi).
        specialize (H2 i).
        specialize (Hnaft i).
        replace (S n + i) with (n + i + 1) in Hnaft by flia.
        replace (n + 1 + i) with (n + i + 1) in Hi by flia.
        now rewrite Hnaft, Nat.add_0_l in H2.
     +++specialize (H2 0); rewrite Nat.add_0_r in H2.
        specialize (Hnaft 0); rewrite Nat.add_0_r, <- Nat.add_1_r in Hnaft.
        rewrite Hnaft, Nat.add_0_l in H2.
        specialize (digit_lt_radix (freal y (n + 1))) as H.
        unfold fd2n in H2; rewrite H2 in H; flia Hr H.
     +++destruct H2 as (i & Hibef & Hiwhi & Hiaft).
        specialize (Hnaft (i + 1)).
        specialize (Hiaft 0).
        replace (S n + (i + 1)) with (n + i + 2) in Hnaft by flia.
        rewrite Nat.add_0_r in Hiaft.
        rewrite Hnaft, Nat.add_0_l in Hiaft.
        specialize (digit_lt_radix (freal y (n + i + 2))) as H.
        unfold fd2n in Hiaft; rewrite Hiaft in H; flia Hr H.
    ---destruct H1 as (i & Hji & Hi); simpl.
       destruct (LPO_fst (A_ge_1 u n)) as [H1| H1].
     +++simpl.
        unfold u at 1.
        unfold v at 1.
        unfold "⊕".
        do 4 rewrite <- Nat.add_assoc.
        do 2 (rewrite Nat.add_comm; symmetry).
        do 3 rewrite <- Nat.add_assoc.
        rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
        rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
        f_equal; f_equal.
        do 2 rewrite Nat.add_assoc.
        do 2 (rewrite Nat.add_comm; symmetry).
        rewrite Hwhi, <- Nat.add_1_r.
        rewrite <- Nat.add_assoc.
        rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
        rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
        f_equal; f_equal.
        rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
        rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
        f_equal; f_equal.
        specialize (A_ge_1_add_all_true_if u) as H2.
        specialize (H2 n).
        assert (H : ∀ k, u (n + k + 1) ≤ 2 * (rad - 1)). {
          intros l; unfold u.
          unfold "⊕", fd2n.
          specialize (digit_lt_radix (freal x (n + l + 1))) as H5.
          specialize (digit_lt_radix (freal y (n + l + 1))) as H6.
          flia H5 H6.
        }
        specialize (H2 H H1); clear H.
        destruct H2 as [H2| [H2| H2]].
      ***assert (H3 : ∀ k, fd2n y (n + k + 1) = 0). {
           intros l.
           unfold u, freal_add_series in H2.
           specialize (H2 l).
           specialize (Haft l).
           replace (S n + l) with (n + l + 1) in Haft by flia.
           rewrite Haft in H2.
           flia H2.
         }
         rewrite Nat.div_small.
      ----rewrite Nat.div_small; [ easy | ].
          apply nA_dig_seq_ub.
       ++++intros l Hl.
           unfold u, freal_add_series.
           specialize (H3 (l - n - 1)).
           replace (n + (l - n - 1) + 1) with l in H3 by flia Hl.
           rewrite H3, Nat.add_0_r.
           apply digit_lt_radix.
       ++++destruct rad; [ easy | simpl; flia ].
      ----apply nA_dig_seq_ub.
       ++++intros l Hl.
           unfold v, freal_add_series.
           specialize (H3 (l - n - 1)).
           replace (n + (l - n - 1) + 1) with l in H3 by flia Hl.
           rewrite H3, Nat.add_0_r.
           apply digit_lt_radix.
       ++++destruct rad; [ easy | simpl; flia ].
      ***exfalso.
         (* according to H2 and Haft, y ends with 999...
            which is contradicted with Hy9 *)
         assert (H : ∀ k, fd2n y (n + k + 1) = rad - 1). {
           intros l.
           specialize (H2 l).
           specialize (Haft l).
           replace (S n + l) with (n + l + 1) in Haft by flia.
           unfold u, freal_add_series in H2.
           rewrite Haft in H2; flia H2.
         }
         specialize (Hy9 (n + 1)) as (l & Hl).
         replace (n + 1 + l) with (n + l + 1) in Hl by flia.
         now rewrite H in Hl.
      ***exfalso.
         destruct H2 as (m & Hmbef & Hmwhi & Hmaft).
         assert (H : ∀ k, fd2n y (n + m + k + 2) = rad - 1). {
           intros l.
           specialize (Hmaft l).
           specialize (Haft (m + l + 1)).
           replace (S n + (m + l + 1)) with (n + m + l + 2) in Haft by flia.
           unfold u, freal_add_series in Hmaft.
           rewrite Haft in Hmaft; flia Hmaft.
         }
         specialize (Hy9 (n + m + 2)) as (l & Hl).
         rewrite Nat.add_shuffle0 in Hl.
         now rewrite H in Hl.
     +++destruct H1 as (m & Hmi & Hm); simpl.
apply A_ge_1_false_iff in Hm.
(* either y=0 and Hm is contradicted because nA=999..999
   or y≠0 and nA≥1000..000 then nA/... in goal is 1 *)
Abort. (*
        ...
(*
        unfold u at 1.
        unfold v at 1.
        unfold "⊕".
        do 4 rewrite <- Nat.add_assoc.
        do 2 (rewrite Nat.add_comm; symmetry).
        do 2 rewrite <- Nat.add_assoc.
        rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
        rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
        f_equal; f_equal.
        do 2 rewrite Nat.add_assoc.
        do 2 (rewrite Nat.add_comm; symmetry).
        rewrite Hwhi, <- Nat.add_1_r.
        rewrite <- Nat.add_assoc.
        rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
        rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
        f_equal; f_equal.
*)
    **idtac.
      ...
 +idtac.
  ...
*)

Theorem freal_add_assoc {r : radix} : ∀ x y z,
  (x + (y + z) = (x + y) + z)%F.
Proof.
intros.
specialize (freal_add_comm (x + y)%F z) as H.
rewrite H; clear H.
specialize (freal_add_comm x y) as H.
rewrite H; clear H.
unfold freal_add; simpl.
...
rewrite freal_eq_add_norm_l; symmetry.
rewrite freal_eq_add_norm_l; symmetry.

...
apply freal_eq_prop_eq.
unfold freal_eq; simpl.
unfold freal_normalized_eq.
remember (freal_normalize (x + (y + z))) as xz eqn:Hxz.
remember (freal_normalize (z + (y + x))) as zx eqn:Hzx.
move zx before xz.
destruct (LPO_fst (has_same_digits xz zx)) as [H1| H1]; [ easy | exfalso ].
destruct H1 as (i & Hji & Hi).
assert (H : ∀ j, j < i → fd2n xz j = fd2n zx j). {
  intros j Hj.
  specialize (Hji _ Hj).
  now apply has_same_digits_true_iff in Hji.
}
clear Hji; rename H into Hji.
apply has_same_digits_false_iff in Hi.
move Hji after Hi.
apply Hi; clear Hi.
rewrite Hxz, Hzx.
unfold fd2n.
erewrite freal_eq_normalize_eq; [ easy | ].
intros j.
unfold freal_add; simpl.
rewrite glop.
...

remember (freal_normalize x) as nx eqn:Hnx.
remember (freal_normalize y) as ny eqn:Hny.
remember (freal_normalize z) as nz eqn:Hnz.
move ny before nx; move nz before ny.
unfold freal_add_to_seq at 1 3.
unfold prop_carr.
remember
  (freal_add_series nx
     (freal_normalize {| freal := freal_add_to_seq ny nz |})) as ayz eqn:Hayz.
remember
  (freal_add_series nz
     (freal_normalize {| freal := freal_add_to_seq ny nx |})) as ayx eqn:Hayx.
move ayx before ayz.
apply digit_eq_eq.
destruct (LPO_fst (A_ge_1 j ayz)) as [H1| H1].
-simpl.
 specialize (proj1 (all_A_ge_1_true_iff _ _) H1) as H2.
 clear H1; rename H2 into H1.
 specialize (H1 0) as H2.
 rewrite Nat.add_0_r in H2; simpl in H2.
 rewrite Nat.mul_1_r in H2.
 remember (rad * (j + 2)) as n eqn:Hn.
 remember (rad ^ (n - j - 1)) as s eqn:Hs.
 move s before n.
 destruct (LPO_fst (A_ge_1 j ayx)) as [H3| H3].
 +simpl.
  specialize (proj1 (all_A_ge_1_true_iff _ _) H3) as H4.
  clear H3; rename H4 into H3.
  move H3 before H1.
  specialize (H3 0) as H4.
  rewrite Nat.add_0_r in H4.
  simpl in H4; rewrite <- Hn, <- Hs in H4.
  rewrite Nat.mul_1_r in H4.
  rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
  rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
  f_equal; f_equal.
...
rewrite Hayz, Hayx.
unfold "⊕" at 1 3.
unfold sequence_add, fd2n; simpl.
unfold digit_sequence_normalize.
remember (freal_add_to_seq ny nz) as nyz eqn:Hnyz.
remember (freal_add_to_seq ny nx) as nyx eqn:Hnyx.
destruct (LPO_fst (is_9_strict_after nyz j)) as [H5| H5].
specialize (is_9_strict_after_all_9 nyz j H5) as H6.
clear H5; rename H6 into H5.
destruct (LPO_fst (is_9_strict_after nyx j)) as [H6| H6].
specialize (is_9_strict_after_all_9 nyx j H6) as H7.
clear H6; rename H7 into H6.
destruct (lt_dec (S (d2n nyz j)) rad) as [H7| H7].
simpl.
destruct (lt_dec (S (d2n nyx j)) rad) as [H8| H8].
simpl.
rewrite Hnyz at 1.
unfold freal_add_to_seq.
unfold prop_carr.
unfold d2n; simpl.

...
  assert (H5 : ∀ i, ayz i ≤ 2 * (rad - 1)). {
    intros.
    rewrite Hayz.
    apply freal_add_series_le_twice_pred.
  }
  assert (H6 : nA j n ayz ≤ 2 * (s - 1)). {
    rewrite Hs.
    apply all_le_nA_le, H5.
  }
  assert (Hsz : s ≠ 0) by (now rewrite Hs; apply Nat.pow_nonzero).
  specialize (Nat_mod_pred_le_twice_pred (nA j n ayz) s Hsz) as H.
...

(**)
specialize (H3 (n - j - 2)) as H5.
assert (Hjn : j + 1 < n). {
  rewrite Hn.
  specialize radix_ge_2 as Hr.
  destruct rad as [| rr]; [ easy | simpl; flia ].
}
replace (S (n - j - 2)) with (n - j - 1) in H5 by flia Hjn.
rewrite <- Hs in H5.
replace (j + (n - j - 2) + 2) with (n + 1) in H5 by flia Hjn.
remember (rad * (n + 1)) as n1 eqn:Hn1; simpl in H5.
remember (rad ^ (n1 - j -  1)) as s1 eqn:Hs1; simpl in H5.
move n1 before s; move s1 before n1.
move H5 before H4.
move Hn1 before Hs; move Hs1 before Hn1.

...
 assert (Hsz : s ≠ 0) by (now rewrite Hs; apply Nat.pow_nonzero).
 assert (H3 : ∀ i, ayz i ≤ 2 * (rad - 1)). {
   intros.
   rewrite Hayz.
   apply freal_add_series_le_twice_pred.
 }
 assert (H4 : nA j n ayz ≤ 2 * (s - 1)). {
   rewrite Hs.
   apply all_le_nA_le, H3.
 }
 specialize (Nat_mod_pred_le_twice_pred (nA j n ayz) s Hsz) as H.
...
 specialize (Nat_mod_pred_le_twice_pred _ _ Hsz H2 H4) as H.
 rewrite Nat.div_small; [ rewrite Nat.add_0_r | flia ].
 clear H2 H3 H4; rename H into H2.
 destruct (LPO_fst (A_ge_1 j ayx)) as [H3| H3].
 +simpl.
  specialize (proj1 (all_A_ge_1_true_iff _ _) H3) as H4.
  clear H3; rename H4 into H3.
  move H3 before H1.
  specialize (H3 0) as H4.
  rewrite Nat.add_0_r in H4.
  simpl in H4; rewrite <- Hn, <- Hs in H4.
  assert (H5 : ∀ i, ayx i ≤ 2 * (rad - 1)). {
    intros.
    rewrite Hayx.
    apply freal_add_series_le_twice_pred.
  }
  assert (H6 : nA j n ayx ≤ 2 * (s - 1)). {
    rewrite Hs.
    apply all_le_nA_le, H5.
  }
  specialize (Nat_mod_pred_le_twice_pred _ _ Hsz H4 H6) as H.
  rewrite Nat.div_small; [ rewrite Nat.add_0_r | flia ].
  clear H4 H5 H6; rename H into H4.
  setoid_rewrite Nat.add_mod; [ | easy | easy ].
  f_equal; f_equal.
  rewrite Hayz, Hayx.
  unfold "⊕".
  unfold freal_normalize; simpl.
  unfold fd2n at 2 4; simpl.
  unfold digit_sequence_normalize.
  destruct (LPO_fst (is_9_strict_after (freal_add_to_seq ny nz) j))
    as [H5| H5].
  *specialize (is_9_strict_after_all_9 _ _ H5) as H.
   clear H5; rename H into H5.
   destruct (LPO_fst (is_9_strict_after (freal_add_to_seq ny nx) j))
     as [H6| H6].
  --specialize (is_9_strict_after_all_9 _ _ H6) as H.
    clear H6; rename H into H6.
    destruct (lt_dec (S (d2n (freal_add_to_seq ny nz) j)) rad) as [H7| H7].
   ++simpl.
     destruct (lt_dec (S (d2n (freal_add_to_seq ny nx) j)) rad) as [H8| H8].
    **simpl.
      unfold freal_add_to_seq, d2n.
      remember (freal_add_series ny nz) as yz eqn:Hyz.
      remember (freal_add_series ny nx) as yx eqn:Hyx.
      move yx before yz.
      unfold prop_carr.
      unfold "⊕" in Hyz, Hyx.
      remember (yz j) as a eqn:Ha; rewrite Hyz in Ha.
      unfold sequence_add in Ha; subst a.
      remember (yx j) as a eqn:Ha; rewrite Hyx in Ha.
      unfold sequence_add in Ha; subst a.
      destruct (LPO_fst (A_ge_1 j yz)) as [H10| H10].
    ---simpl.
       specialize (proj1 (all_A_ge_1_true_iff _ _) H10) as H12.
       clear H10.
       specialize (H12 0) as H14.
       rewrite Nat.add_0_r in H14; simpl in H14.
       rewrite <- Hn, <- Hs in H14 |-*.
       assert (H10 : ∀ i, yz i ≤ 2 * (rad - 1)). {
         intros.
         rewrite Hyz.
         apply freal_add_series_le_twice_pred.
       }
       assert (H11 : nA j n yz ≤ 2 * (s - 1)). {
         rewrite Hs.
         apply all_le_nA_le, H10.
       }
       specialize (Nat_mod_pred_le_twice_pred _ _ Hsz H14 H11) as H.
       rewrite Nat.div_small; [ rewrite Nat.add_0_r | flia ].
       clear H14 H10 H11; rename H into H18.
       destruct (LPO_fst (A_ge_1 j yx)) as [H11| H11].
     +++simpl.
        specialize (proj1 (all_A_ge_1_true_iff _ _) H11) as H13.
        clear H11.
        specialize (H13 0) as H15.
        rewrite Nat.add_0_r in H15; simpl in H15.
        rewrite <- Hn, <- Hs in H15.
        move H13 before H12.
        assert (H10 : ∀ i, yx i ≤ 2 * (rad - 1)). {
          intros.
          rewrite Hyx.
          apply freal_add_series_le_twice_pred.
        }
        assert (H11 : nA j n yx ≤ 2 * (s - 1)). {
          rewrite Hs.
          apply all_le_nA_le, H10.
        }
        specialize (Nat_mod_pred_le_twice_pred _ _ Hsz H15 H11) as H.
        rewrite Nat.div_small; [ rewrite Nat.add_0_r | flia ].
        clear H15 H10 H11; rename H into H19.
        rewrite <- Nat.add_1_r, Nat.add_assoc; symmetry.
        rewrite <- Nat.add_1_r, Nat.add_assoc; symmetry.
        rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
        rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
        f_equal; f_equal.
        remember ((fd2n ny j + fd2n nz j + 1) mod rad) as a eqn:Ha.
        rewrite <- Nat.add_mod_idemp_l in Ha; [ subst a | easy ].
        rewrite Nat.add_mod_idemp_r; [ | easy ].
        symmetry.
        remember ((fd2n ny j + fd2n nx j + 1) mod rad) as a eqn:Ha.
        rewrite <- Nat.add_mod_idemp_l in Ha; [ subst a | easy ].
        rewrite Nat.add_mod_idemp_r; [ | easy ].
        symmetry.
        rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
        rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
        do 2 rewrite Nat.add_assoc.
        rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
        rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
        f_equal; f_equal.
        rewrite <- Nat.add_mod; [ | easy ].
        rewrite <- Nat.add_mod; [ | easy ].
        f_equal; clear; flia.
     +++destruct H11 as (k & Hki & Hkk); simpl.
        apply A_ge_1_false_iff in Hkk.
        remember (rad * (j + k + 2)) as nk eqn:Hnk.
        remember (rad ^ (nk - j - 1)) as sk eqn:Hsk.
        move sk before nk.
unfold freal_add_to_seq in H6.
unfold "⊕" in H6.
rewrite <- Hyx in H6.
unfold d2n, prop_carr in H6.
Print A_ge_1.
...
unfold nA in Hkk.
rewrite summation_eq_compat with (h := λ j, (rad - 1) * (rad ^ (nk - 1 - j)))
  in Hkk.
Focus 2.
clear i Hji; intros i Hjk.
f_equal.
specialize (H6 (i - j - 1)) as H.
replace (j + (i - j - 1) + 1) with i in H by flia Hjk.
unfold freal_add_to_seq in H.
unfold "⊕" in H.
rewrite <- Hyx in H.
unfold prop_carr, d2n in H.
destruct (LPO_fst (A_ge_1 i yx)) as [H9| H9].
simpl in H.
remember (rad * (i + 2)) as ni eqn:Hni.
remember (rad ^ (ni - i - 1)) as si eqn:Hsi.
move si before ni.
simpl in H.
specialize (proj1 (all_A_ge_1_true_iff _ _) H9 0) as H10.
simpl in H10.
rewrite Nat.add_0_r in H10.
rewrite <- Hni, <- Hsi in H10.
 assert (H11 : ∀ i, yx i ≤ 2 * (rad - 1)). {
   intros.
   rewrite Hyx.
   apply freal_add_series_le_twice_pred.
 }
 assert (H13 : nA i ni yx ≤ 2 * (si - 1)). {
   rewrite Hsi.
   apply all_le_nA_le, H11.
 }
enough (Hsiz : si ≠ 0).
 specialize (Nat_mod_pred_le_twice_pred _ _ Hsiz H10 H13) as H14.
rewrite Nat.div_small in H; [ | flia Hsiz H14 ].
clear H10 H13.
rewrite Nat.add_0_r in H.
specialize (proj1 (all_A_ge_1_true_iff _ _) H9) as H15.
...
*)
