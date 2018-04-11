(* Real between 0 and 1, i.e. fractional part of a real.
   Implemented as function of type nat → nat.
   Operations + and * implemented using LPO. *)

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

Theorem radix_gt_1 {r : radix} : 1 < rad.
Proof.
destruct r as (rad, radi); simpl; flia radi.
Qed.

Theorem radix_ne_0 {r : radix} : rad ≠ 0.
Proof.
destruct r as (rad, radi); simpl; flia radi.
Qed.

Hint Resolve radix_gt_0 radix_ge_1 radix_gt_1 radix_ne_0 radix_ge_2.

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

(* In names, "9" actually means "rad-1" *)

Definition is_9_after {r : radix} u i j :=
  if eq_nat_dec (d2n u (i + j)) (rad - 1) then true else false.
Definition is_9_strict_after {r : radix} u i j :=
  if eq_nat_dec (d2n u (i + j + 1)) (rad - 1) then true else false.
Definition is_0_strict_after {r : radix} u i j :=
  if eq_nat_dec (d2n u (i + j + 1)) 0 then true else false.

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

Definition freal_norm_eq {r : radix} x y :=
  match LPO_fst (has_same_digits x y) with
  | inl _ => True
  | inr _ => False
  end.

Definition freal_norm_lt {r : radix} x y :=
  match LPO_fst (has_same_digits x y) with
  | inl _ => True
  | inr (exist _ i _) =>
      if lt_dec (fd2n x i) (fd2n y i) then True else False
  end.

Definition freal_eq {r : radix} x y :=
  freal_norm_eq (freal_normalize x) (freal_normalize y).

Definition freal_lt {r : radix} x y :=
  freal_norm_lt (freal_normalize x) (freal_normalize y).

Definition freal_0 {r : radix} := {| freal i := digit_0 |}.

Notation "0" := (freal_0) : freal_scope.
Notation "a = b" := (freal_eq a b) : freal_scope.
Notation "a ≠ b" := (¬ freal_eq a b) : freal_scope.
Notation "a < b" := (freal_lt a b) : freal_scope.

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

Theorem is_9_strict_after_all_9 {r : radix} : ∀ u i,
  (∀ j, is_9_strict_after u i j = true)
  → (∀ k, d2n u (i + k + 1) = rad - 1).
Proof.
intros * Hm9 *.
specialize (Hm9 k); unfold is_9_strict_after in Hm9.
now destruct (Nat.eq_dec (d2n u (i + k + 1)) (rad - 1)).
Qed.

Theorem is_9_after_add {r : radix} : ∀ u i j,
  is_9_after u 0 (i + j) = is_9_after u i j.
Proof. easy. Qed.

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

Theorem freal_eq_normalize_eq {r : radix} : ∀ x y,
  (∀ i, freal x i = freal y i)
  → ∀ i : nat, freal (freal_normalize x) i = freal (freal_normalize y) i.
Proof.
intros * Hxy *.
unfold freal_normalize, digit_sequence_normalize; simpl.
unfold d2n; rewrite Hxy.
destruct (LPO_fst (is_9_strict_after (freal x) i)) as [H1| H1].
-destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H2| H2]; [ easy | ].
 destruct H2 as (j & Hjj & Hj).
 specialize (H1 j).
 apply is_9_strict_after_true_iff in H1.
 apply is_9_strict_after_false_iff in Hj.
 unfold d2n in H1, Hj.
 now rewrite Hxy in H1.
-destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H2| H2]; [ | easy ].
 destruct H1 as (j & Hjj & Hj).
 specialize (H2 j).
 apply is_9_strict_after_false_iff in Hj.
 apply is_9_strict_after_true_iff in H2.
 unfold d2n in H2, Hj.
 now rewrite Hxy in Hj.
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
 +now apply freal_eq_normalize_eq.
 +now apply freal_norm_not_norm_eq_normalize_eq.
 +now intros; symmetry; apply freal_norm_not_norm_eq_normalize_eq.
Qed.

Definition has_not_9_after {r : radix} u i j :=
  match LPO_fst (is_9_after u (i + j)) with
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

Definition sequence_add (a b : nat → nat) i := a i + b i.
Definition sequence_mul (rg := nat_ord_ring) (a b : nat → nat) i :=
  Σ (j = 0, i), a j * b (i - j).

Definition freal_add_series {r : radix} a b :=
  sequence_add (fd2n a) (fd2n b).

Arguments freal_add_series _ a%F b%F.

Definition freal_mul_series {r : radix} a b i :=
  match i with
  | 0 => 0
  | S i' => sequence_mul (fd2n a) (fd2n b) i'
  end.

Definition nA {r : radix} (rg := nat_ord_ring) i n u :=
  Σ (j = i + 1, n - 1), u j * rad ^ (n - 1 - j).

Definition A_ge_1 {r : radix} u i k :=
  let n := rad * (i + k + 3) in
  let s := rad ^ (n - i - 1) in
  if lt_dec (nA i n u mod s) ((rad ^ S k - 1) * rad ^ (n - i - k - 2)) then
    false
  else
    true.

Definition index_A_not_ge {r : radix} u i :=
  match LPO_fst (A_ge_1 u i) with
  | inl _ => 0
  | inr (exist _ l _) => l
  end.

Definition numbers_to_digits {r : radix} u i :=
  let l := index_A_not_ge u i in
  let n := rad * (i + l + 3) in
  let s := rad ^ (n - i - 1) in
  let d := u i + nA i n u / s in
  mkdig _ (d mod rad) (Nat.mod_upper_bound d rad radix_ne_0).

Definition freal_add_to_seq {r : radix} (a b : FracReal) :=
  numbers_to_digits (freal_add_series a b).

Arguments freal_add_to_seq _ a%F b%F.

Definition freal_mul_to_seq {r : radix} (a b : FracReal) :=
  numbers_to_digits (freal_mul_series a b).

Definition freal_unorm_add {r : radix} x y := {| freal := freal_add_to_seq x y |}.

Definition freal_add {r : radix} (a b : FracReal) :=
  freal_unorm_add (freal_normalize a) (freal_normalize b).

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

Theorem A_ge_1_freal_add_series_comm {r : radix} : ∀ x y i k,
  A_ge_1 (freal_add_series x y) i k =
  A_ge_1 (freal_add_series y x) i k.
Proof.
intros.
unfold A_ge_1.
now rewrite nA_freal_add_series_comm.
Qed.

Theorem A_ge_1_freal_mul_series_comm {r : radix} : ∀ x y i k,
  A_ge_1 (freal_mul_series x y) i k =
  A_ge_1 (freal_mul_series y x) i k.
Proof.
intros.
unfold A_ge_1.
now rewrite nA_freal_mul_series_comm.
Qed.

Theorem freal_add_to_seq_i_comm {r : radix} : ∀ x y i,
  freal_add_to_seq x y i = freal_add_to_seq y x i.
Proof.
intros.
unfold freal_add_to_seq, numbers_to_digits.
remember (freal_add_series x y) as xy.
remember (freal_add_series y x) as yx.
apply digit_eq_eq; simpl.
unfold index_A_not_ge.
destruct (LPO_fst (A_ge_1 xy i)) as [Hxy| Hxy].
-rewrite Heqxy, freal_add_series_comm, <- Heqyx.
 destruct (LPO_fst (A_ge_1 yx i)) as [Hyx| Hyx].
 +now rewrite nA_freal_add_series_comm, <- Heqyx.
 +destruct Hyx as (k & Hjk & Hk).
  rewrite Heqyx, A_ge_1_freal_add_series_comm, <- Heqxy in Hk.
  now rewrite Hxy in Hk.
-destruct Hxy as (k & Hjk & Hk).
 rewrite Heqxy, A_ge_1_freal_add_series_comm, <- Heqyx in Hk.
 destruct (LPO_fst (A_ge_1 yx i)) as [Hyx| Hyx].
 +now rewrite Hyx in Hk.
 +destruct Hyx as (l & Hjl & Hl).
  destruct (lt_eq_lt_dec k l) as [ [ Hkl | Hkl ] | Hkl ].
  *apply Hjl in Hkl.
   now rewrite Hk in Hkl.
  *rewrite Heqxy, freal_add_series_comm, <- Heqyx.
   rewrite nA_freal_add_series_comm, <- Heqyx.
   now subst k.
  *apply Hjk in Hkl.
   rewrite Heqxy, A_ge_1_freal_add_series_comm in Hkl.
   now rewrite <- Heqyx, Hl in Hkl.
Qed.

Theorem freal_mul_to_seq_i_comm {r : radix} : ∀ x y i,
  freal_mul_to_seq x y i = freal_mul_to_seq y x i.
Proof.
intros.
unfold freal_mul_to_seq, numbers_to_digits.
remember (freal_mul_series x y) as xy.
remember (freal_mul_series y x) as yx.
unfold index_A_not_ge.
destruct (LPO_fst (A_ge_1 xy i)) as [Hxy| Hxy].
-rewrite Heqxy, freal_mul_series_comm, <- Heqyx.
 destruct (LPO_fst (A_ge_1 yx i)) as [Hyx| Hyx].
 +now rewrite nA_freal_mul_series_comm, <- Heqyx.
 +destruct Hyx as (k & Hjk & Hk).
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

Theorem dig_norm_add_comm {r : radix} : ∀ x y i,
  freal (freal_normalize (x + y)) i = freal (freal_normalize (y + x)) i.
Proof.
intros.
unfold freal_normalize.
remember (freal (x + y)) as xy.
remember (freal (y + x)) as yx.
simpl.
unfold digit_sequence_normalize.
destruct (LPO_fst (is_9_strict_after xy i)) as [Hxy| Hxy].
-destruct (LPO_fst (is_9_strict_after yx i)) as [Hyx| Hyx].
 +unfold freal_add in Heqxy; simpl in Heqxy.
  unfold freal_add in Heqyx; simpl in Heqyx.
  destruct (lt_dec (S (d2n xy i)) rad) as [Hrxy| Hrxy].
  *subst xy; simpl in Hrxy; simpl.
   destruct (lt_dec (S (d2n yx i)) rad) as [Hryx| Hryx].
  --unfold freal_add in Heqyx; simpl in Heqyx.
    subst yx; simpl in Hryx; simpl.
    apply digit_eq_eq; unfold d2n.
    remember freal_add_to_seq as f; simpl; subst f.
    now rewrite freal_add_to_seq_i_comm.
  --subst yx; simpl in Hryx.
    unfold d2n in Hryx.
    now rewrite freal_add_to_seq_i_comm in Hryx.
  *destruct (lt_dec (S (d2n yx i)) rad) as [Hryx| Hryx]; [ | easy ].
   exfalso.
   subst xy yx; simpl in Hryx; unfold d2n in Hryx.
   now rewrite freal_add_to_seq_i_comm in Hryx.
 +destruct Hyx as (k & Hjk & Hk); clear Hjk.
  unfold freal_mul in Heqyx; simpl in Heqyx.
  subst yx; simpl in Hk; simpl.
  unfold freal_add in Heqxy; simpl in Heqxy.
  subst xy; simpl in Hxy; simpl.
  apply is_9_strict_after_false_iff in Hk.
  unfold d2n in Hk.
  rewrite freal_add_to_seq_i_comm in Hk.
  specialize (Hxy k).
  apply is_9_strict_after_true_iff in Hxy.
  now unfold d2n in Hxy.
-destruct Hxy as (k & Hjk & Hk).
 unfold freal_add in Heqxy; simpl in Heqxy.
 unfold freal_add in Heqyx; simpl in Heqyx.
 destruct (LPO_fst (is_9_strict_after yx i)) as [Hyx| Hyx].
 +exfalso; clear Hjk.
  subst xy yx; simpl in Hk, Hyx; unfold d2n in Hk; simpl.
  apply is_9_strict_after_false_iff in Hk.
  unfold d2n in Hk.
  rewrite freal_add_to_seq_i_comm in Hk.
  specialize (Hyx k).
  apply is_9_strict_after_true_iff in Hyx.
  now unfold d2n in Hyx.
 +subst xy yx; simpl.
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

Theorem freal_add_comm {r : radix} : ∀ x y : FracReal, (x + y = y + x)%F.
Proof.
intros.
unfold freal_eq.
unfold freal_norm_eq.
remember (freal_normalize (x + y)) as nxy eqn:Hnxy.
remember (freal_normalize (y + x)) as nyx eqn:Hnyx.
destruct (LPO_fst (has_same_digits nxy nyx)) as [H| H]; [ easy | ].
exfalso.
destruct H as (i & Hji & Hi).
apply has_same_digits_false_iff in Hi.
apply Hi; clear Hi.
subst nxy nyx; unfold fd2n; f_equal.
apply dig_norm_add_comm.
Qed.

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
unfold freal_add_series; simpl.
unfold sequence_add.
apply Nat.add_0_l.
Qed.

Theorem nA_freal_add_series {r : radix} : ∀ x y i n,
  nA i n (freal_add_series x y) = nA i n (fd2n x) + nA i n (fd2n y).
Proof.
intros.
unfold nA; simpl.
unfold freal_add_series, sequence_add.
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
unfold freal_add_series; simpl.
unfold sequence_add; simpl.
easy.
Qed.

Theorem Nat_pow_ge_1 : ∀ a b, 0 < a → 1 ≤ a ^ b.
Proof.
intros * Ha.
induction b; [ easy | simpl ].
replace 1 with (1 * 1) by flia.
apply Nat.mul_le_mono_nonneg; [ flia | easy | flia | easy ].
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

Theorem nA_upper_bound {r : radix} : ∀ x n i,
  nA i n (fd2n x) < rad ^ (n - i - 1).
Proof.
intros.
destruct (le_dec (i + 1) (n - 1)) as [H1| H1].
-apply nA_dig_seq_ub; [ | easy ].
 intros j Hj.
 now apply digit_lt_radix.
-unfold nA; rewrite summation_empty; [ | flia H1 ].
 now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
Qed.

Theorem rad_pow_succ_gt_1 {r : radix} : 1 < rad → ∀ k, 1 < rad ^ S k.
Proof.
intros Hr *.
induction k; [ now rewrite Nat.pow_1_r | ].
simpl; replace 1 with (1 * 1) by flia.
apply Nat.mul_lt_mono_nonneg; [ flia | easy | flia | easy ].
Qed.

Theorem rad_expr {r : radix} : 1 < rad → ∀ i k, rad * (i + k + 2) - 1 - i ≠ 1.
Proof.
intros Hr * Hj.
replace (rad * (i + k + 2) - 1 - i)
with (rad * S i + rad * (k + 1) - S i) in Hj by flia.
rewrite Nat.add_sub_swap in Hj.
 destruct rad as [| n]; [ easy | ].
 replace (S n * S i - S i) with (n * S i) in Hj by flia.
 destruct n as [| n]; [ flia Hr | simpl in Hj; flia Hj ].

 destruct rad as [| n]; [ easy | ].
 rewrite Nat.mul_comm; simpl.
 rewrite Nat.mul_comm; simpl; flia.
Qed.

Theorem nA_all_9 {r : radix} : 0 < rad → ∀ u i n,
  (∀ j, u (i + j + 1) = rad - 1)
  → nA i n u = rad ^ (n - i - 1) - 1.
Proof.
intros Hr * Hj.
unfold nA.
rewrite summation_eq_compat with (h := λ j, (rad - 1) * rad ^ (n - 1 - j)).
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
   f_equal; flia Hin.

   intros k Hk; f_equal; flia Hk.

  replace (n - i - 1) with 0 by flia Hin.
  rewrite summation_empty; [ | flia Hin ].
  rewrite Nat.mul_0_r; simpl; flia.

 intros j Hij.
 replace j with (i + (j - i - 1) + 1) at 1 by flia Hij.
 now rewrite Hj.
Qed.

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

Theorem A_ge_1_false_iff {r : radix} : ∀ i u k,
  let n := rad * (i + k + 3) in
  let s := rad ^ (n - i - 1) in
  A_ge_1 u i k = false ↔
  nA i n u mod s < (rad ^ S k - 1) * rad ^ (n - i - k - 2).
Proof.
intros.
unfold A_ge_1.
fold n s.
set (t := rad ^ (n - i - k - 2)).
now destruct (lt_dec (nA i n u mod s) ((rad ^ S k - 1) * t)).
Qed.

Theorem A_ge_1_true_iff {r : radix} : ∀ i u k,
  let n := rad * (i + k + 3) in
  let s := rad ^ (n - i - 1) in
  A_ge_1 u i k = true ↔
  nA i n u mod s ≥ (rad ^ S k - 1) * rad ^ (n - i - k - 2).
Proof.
intros.
unfold A_ge_1.
fold n s.
set (t := rad ^ (n - i - k - 2)).
destruct (lt_dec (nA i n u mod s) ((rad ^ S k - 1) * t)) as [H1| H1].
-now split; [ | apply Nat.nle_gt in H1 ].
-now split; [ apply Nat.nlt_ge in H1 | ].
Qed.

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
  let n := rad * (i + k + 3) in
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

Theorem when_99000_le_uuu00 {r : radix} : ∀ u i j k n,
  (∀ k, u k < rad)
  → (rad ^ S j - 1) * rad ^ (n - i - j - 2) ≤ nA i n u
  → S j ≤ n - i - 1
  → i + 1 ≤ k ≤ i + j + 1
  → u k = rad - 1.
Proof.
intros * Hu HnA Hj Hk.
apply Nat.mul_le_mono_pos_r with (p := rad ^ S j) in HnA.
2: now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
rewrite <- Nat.mul_assoc in HnA.
rewrite <- Nat.pow_add_r in HnA.
replace (n - i - j - 2 + S j) with (n - i - 1) in HnA by flia Hj.
remember (rad ^ (n - i - 1)) as s eqn:Hs.
assert (Hsz : s ≠ 0) by now subst s; apply Nat.pow_nonzero.
apply Nat.div_le_mono with (c := s) in HnA; [ | easy ].
rewrite Nat.div_mul in HnA; [ | easy ].
assert (H : nA i n u * rad ^ S j / s = nA i (i + j + 2) u). {
  rewrite Hs.
  replace (n - i - 1) with (n - i - 1 - S j + S j).
  -rewrite Nat.pow_add_r.
   rewrite Nat.div_mul_cancel_r; try now apply Nat.pow_nonzero.
   replace (n - i - 1 - S j) with (n - i - j - 2) by flia.
   unfold nA at 1.
   rewrite summation_split with (e := i + j + 1); [ | flia Hj ].
   simpl; unfold nA.
   replace (i + j + 2 - 1) with (i + j + 1) by flia.
   rewrite summation_eq_compat with
     (h := λ k, u k * rad ^ (i + j + 1 - k) * rad ^ (n - i - j - 2)).
   +rewrite <- summation_mul_distr_r; simpl.
    rewrite Nat.add_comm.
    rewrite Nat.div_add; [ | now apply Nat.pow_nonzero ].
    rewrite Nat.div_small; [ easy | ].
    remember (n - i - j - 2) as m eqn:Hm.
    symmetry in Hm.
    destruct m.
    *rewrite summation_empty; [ | flia Hj Hm ].
     now apply Nat_pow_ge_1.
    *rewrite power_summation; [ | easy ].
     rewrite summation_mul_distr_l; simpl.
     rewrite summation_shift; [ | flia Hm ].
     replace (n - 1 - S (i + j + 1)) with m by flia Hm.
     apply -> Nat.succ_le_mono.
     rewrite summation_rtl.
     rewrite summation_eq_compat with
       (h := λ k, u (S (i + j + 1 + m - k)) * rad ^ k).
     --apply (@summation_le_compat nat_ord_ring_def).
       intros p Hp; simpl; unfold Nat.le.
       apply Nat.mul_le_mono_r.
       specialize (Hu (S (i + j + 1 + m - p))); flia Hu.
     --intros p Hp.
       f_equal; f_equal; [ flia Hp | flia Hm Hp ].
   +intros p Hp.
    rewrite <- Nat.mul_assoc; f_equal.
    rewrite <- Nat.pow_add_r; f_equal.
    flia Hj Hp.
  -now apply Nat.sub_add.
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
 clear s Hs Hsz.
 set (rg := nat_ord_ring).
 assert
   (H :
    Σ (k = 0, j), u (i + 1 + k) * rad ^ (j - k) =
    Σ (k = 0, j), (rad - 1) * rad ^ (j - k)). {
   apply Nat.le_antisymm; [ | easy ].
   apply (@summation_le_compat nat_ord_ring_def); simpl; unfold Nat.le.
   intros p Hp.
   apply Nat.mul_le_mono_r.
   specialize (Hu (i + 1 + p)); flia Hu.
 }
 clear HnA; rename H into HnA.
 setoid_rewrite summation_rtl in HnA.
 rewrite summation_eq_compat with (h := λ k, u (i + j + 1 - k) * rad ^ k)
   in HnA.
 +symmetry in HnA.
  rewrite summation_eq_compat with (h := λ k, (rad - 1) * rad ^ k) in HnA.
  *clear n Hj.
   revert i HnA k Hk.
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
     apply IHj with (i := S i); [ | flia Hk H2 ].
     rewrite HnA.
     apply summation_eq_compat.
     intros p Hp; f_equal; f_equal; flia.
   ++assert
       (H2 : Σ (i = 0, j), (rad - 1) * rad ^ i <
             Σ (i0 = 0, j), u (i + S j + 1 - i0) * rad ^ i0). {
       specialize (Hu (S i)) as Hui.
       assert (Hus : u (S i) < rad - 1) by flia H1 Hui.
       apply Nat.mul_lt_mono_pos_r with (p := rad ^ S j) in Hus.
       -flia HnA Hus.
       -now apply Nat_pow_ge_1.
     }
     apply Nat.nle_gt in H2.
     exfalso; apply H2.
     apply (@summation_le_compat nat_ord_ring_def); simpl; unfold Nat.le.
     intros p Hp.
     apply Nat.mul_le_mono_r.
     specialize (Hu (i + S j + 1 - p)); flia Hu.
  *intros p Hp; f_equal; f_equal; flia Hp.
 +intros p Hp.
  replace (j - (j + 0 - p)) with p by flia Hp; f_equal.
  f_equal; flia Hp.
-intros p Hp.
 f_equal; f_equal; flia.
Qed.

Theorem all_lt_rad_A_ge_1_true_if {r : radix} : ∀ i u,
  (∀ k, u k < rad)
  → (∀ k, A_ge_1 u i k = true) → ∀ j, i < j → u j = rad - 1.
Proof.
intros * Hu.
intros Hk * Hij.
specialize (Hk j).
apply A_ge_1_true_iff in Hk.
remember (rad * (i + j + 3)) as n eqn:Hn.
remember (rad ^ (n - i - 1)) as s eqn:Hs.
remember (S j) as sj eqn:Hsj.
move s before n.
assert (Hsz : s ≠ 0) by now subst s; apply Nat.pow_nonzero.
rename Hk into HnA.
rewrite Nat.mod_small in HnA.
+apply when_99000_le_uuu00 with (i0 := i) (j0 := j) (n0 := n).
 *easy.
 *now rewrite <- Hsj.
 *rewrite Hn.
  specialize radix_ge_2 as Hr.
  destruct rad; [ easy | simpl; flia ].
 *flia Hij.
+rewrite Hs.
 apply nA_dig_seq_ub; [ intros; apply Hu | ].
 rewrite Hn.
 specialize radix_ge_2 as Hr.
 destruct rad; [ flia Hr | simpl in Hn; flia Hn ].
Qed.

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
unfold numbers_to_digits, index_A_not_ge.
destruct (LPO_fst (A_ge_1 u i)) as [Hku| (m & Hjm & Hm)].
-exfalso.
 assert (H1 : ∀ k, u k < rad). {
   intros k.
   unfold u.
   unfold freal_add_series, sequence_add.
   rewrite freal_normalize_0_all_0, Nat.add_0_l.
   apply digit_lt_radix.
 }
 specialize (all_lt_rad_A_ge_1_true_if i u H1 Hku) as H2.
 assert (H3 : ∀ j, i < j → fd2n (freal_normalize x) j = rad - 1). {
   intros j Hj.
   specialize (H2 j Hj).
   unfold u in H2.
   unfold freal_add_series, sequence_add in H2.
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
 unfold u, freal_add_series, sequence_add in Huk.
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
  unfold u, freal_add_series, sequence_add, fd2n.
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

Require Import Morphisms Setoid.

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
destruct (LPO_fst (has_same_digits ny nx)) as [Hs| Hs]; [ easy | exfalso ].
destruct (LPO_fst (has_same_digits nx ny)) as [Ht| Ht]; [ clear Hxy | easy ].
destruct Hs as (i & Hji & Hyx).
specialize (Ht i).
unfold has_same_digits in Ht, Hyx.
destruct (Nat.eq_dec (fd2n ny i) (fd2n nx i)) as [H1| H1]; [ easy | ].
destruct (Nat.eq_dec (fd2n nx i) (fd2n ny i)) as [H2| H2]; [ | easy ].
now symmetry in H2.
Qed.

Theorem freal_eq_trans {r : radix} : transitive _ freal_eq.
Proof.
intros x y z Hxy Hyz.
unfold freal_eq, freal_norm_eq in Hxy, Hyz |-*.
remember (freal_normalize x) as nx eqn:Hnx.
remember (freal_normalize y) as ny eqn:Hny.
remember (freal_normalize z) as nz eqn:Hnz.
destruct (LPO_fst (has_same_digits nx ny)) as [Hx| Hx]; [ clear Hxy | easy ].
destruct (LPO_fst (has_same_digits ny nz)) as [Hy| Hy]; [ clear Hyz | easy ].
destruct (LPO_fst (has_same_digits nx nz)) as [Hz| Hz]; [ easy | exfalso ].
destruct Hz as (i & Hji & Hz).
specialize (Hx i).
specialize (Hy i).
unfold has_same_digits in Hx, Hy, Hz.
destruct (Nat.eq_dec (fd2n nx i) (fd2n ny i)) as [H1| H1]; [ | easy ].
destruct (Nat.eq_dec (fd2n ny i) (fd2n nz i)) as [H2| H2]; [ | easy ].
destruct (Nat.eq_dec (fd2n nx i) (fd2n nz i)) as [H3| H3]; [ easy | ].
apply H3.
now transitivity (fd2n ny i).
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

Theorem numbers_to_digits_eq_compat {r : radix} : ∀ f g,
  (∀ i, f i = g i) → ∀ i,
  numbers_to_digits f i = numbers_to_digits g i.
Proof.
intros * Hfg *.
unfold numbers_to_digits, index_A_not_ge.
rewrite Hfg.
destruct (LPO_fst (A_ge_1 f i)) as [Hf| Hf].
-destruct (LPO_fst (A_ge_1 g i)) as [Hg| Hg].
 +f_equal; f_equal.
  unfold nA.
  erewrite summation_eq_compat; [ reflexivity | simpl ].
  intros j Hj.
  now rewrite Hfg.
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
  *subst l; apply digit_eq_eq; simpl.
   f_equal; f_equal; f_equal.
   now apply nA_eq_compat.
  *specialize (Hjk _ Hkl).
   apply digit_eq_eq; simpl.
   erewrite A_ge_1_eq_compat in Hjk; [ | easy ].
   now rewrite Hl in Hjk.
Qed.

Theorem Nat_div_succ_l_eq_div : ∀ p q, q ≠ 0 →
  (S p) / q = p / q ↔ p mod q ≠ q - 1.
Proof.
intros * Hq.
specialize (Nat.div_mod p q Hq) as Hp.
specialize (Nat.div_mod (S p) q Hq) as Hs.
split; intros Hpq.
-specialize (Nat.mod_upper_bound (S p) q Hq) as H.
 rewrite Hpq in Hs; flia Hp Hs H.
-remember (p / q) as a.
 remember (S p / q) as a'.
 rewrite <- Nat.add_1_r in Hs at 1.
 rewrite Hp in Hs at 1.
 assert (p mod q + 1 < q). {
  specialize (Nat.mod_upper_bound p q Hq) as H; flia Hpq H.
 }
 rewrite <- Nat.add_assoc in Hs.
 apply Nat.add_sub_eq_l in Hs.
 rewrite Nat.add_comm in Hs.
 rewrite <- Nat.add_sub_assoc in Hs.
 +rewrite <- Nat.mul_sub_distr_l in Hs.
  remember (a' - a) as aa eqn:Ha.
  symmetry in Ha.
  destruct aa.
  *apply Nat.sub_0_le in Ha.
   apply Nat.le_antisymm; [ easy | ].
   subst a a'.
   apply Nat.div_le_mono; [ easy | flia ].
  *exfalso.
   rewrite <- Hs in H.
   rewrite Nat.mul_comm in H; simpl in H; flia H.
 +apply Nat.mul_le_mono; [ easy | ].
  subst a a'.
  apply Nat.div_le_mono; [ easy | flia ].
Qed.

Theorem freal_eq_normalized_eq {r : radix} : ∀ x y,
  (x = y)%F ↔
  (∀ i, freal (freal_normalize x) i = freal (freal_normalize y) i).
Proof.
intros.
unfold freal_eq, freal_norm_eq.
remember (freal_normalize x) as nx eqn:Hnx.
remember (freal_normalize y) as ny eqn:Hny.
split; intros Hxy *.
-destruct (LPO_fst (has_same_digits nx ny)) as [H1| H1]; [ clear Hxy | easy ].
 specialize (H1 i).
 unfold has_same_digits in H1.
 destruct (Nat.eq_dec (fd2n nx i) (fd2n ny i)) as [H2| ]; [ clear H1 | easy ].
 now unfold fd2n in H2; apply digit_eq_eq.
-destruct (LPO_fst (has_same_digits nx ny)) as [H1| H1]; [ easy | ].
 destruct H1 as (i & Hji & Hi).
 apply has_same_digits_false_iff in Hi.
 exfalso; apply Hi; unfold has_same_digits.
 apply digit_eq_eq, Hxy.
Qed.

Add Parametric Morphism {r : radix} : freal_add
  with signature freal_eq ==> freal_eq ==> freal_eq
  as freal_add_morph.
Proof.
intros x y Hxy x' y' Hxy'.
rewrite freal_eq_normalized_eq in Hxy, Hxy'.
rewrite freal_eq_normalized_eq.
apply freal_normalized_eq_iff; left.
intros i.
unfold freal_add, freal_unorm_add.
unfold freal_add_to_seq, freal_add_series, sequence_add; simpl.
unfold freal_add, freal_add_to_seq, freal_add_series, sequence_add; simpl.
apply numbers_to_digits_eq_compat; clear i.
intros i.
unfold fd2n.
now rewrite Hxy, Hxy'.
Qed.

Theorem Nat_mod_pred_le_twice_pred : ∀ a b,
  b ≠ 0
  → a mod b = b - 1
  → a ≤ 2 * (b - 1)
  → a = b - 1.
Proof.
intros * Hb Ham Hal.
specialize (Nat.div_mod a b Hb) as H1.
rewrite Ham in H1.
rewrite H1 in Hal; simpl in Hal.
rewrite Nat.add_0_r in Hal.
apply Nat.add_le_mono_r in Hal.
remember (a / b) as c eqn:Hc; symmetry in Hc.
destruct c; [ flia H1 | ].
rewrite Nat.mul_comm in Hal; simpl in Hal; flia Hal H1.
Qed.

Theorem freal_add_series_le_twice_pred {r : radix} : ∀ x y i,
  freal_add_series x y i ≤ 2 * (rad - 1).
Proof.
intros *.
unfold freal_add_series, sequence_add.
replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
apply Nat.add_le_mono.
apply digit_le_pred_radix.
apply digit_le_pred_radix.
Qed.

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
     let n := rad * (i + k + 3) in
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
     let n := rad * (i + k + 3) in
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
  (n := (rad * (i + j + 3))%nat) (s := rad ^ (n - i - 1)),
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

Theorem Nat_pow_sub_1_mul_pow : ∀ n a b,
  (n ^ a - 1) * n ^ b = n ^ (a + b) - n ^ b.
Proof.
intros.
rewrite Nat.mul_sub_distr_r.
now rewrite Nat.pow_add_r, Nat.mul_1_l.
Qed.

Theorem nA_upper_bound_for_op {r : radix} (rg := nat_ord_ring) : ∀ u i k,
  let n := rad * (i + k + 3) in
  (∀ j, i < j < n → u j ≤ (j + 1) * (rad - 1) ^ 2)
  → nA i n u ≤ (rad - 1) ^ 2 * Σ (j = 0, n - i - 2), (n - j) * rad ^ j.
Proof.
intros * Hur *; subst n.
remember (rad * (i + k + 3)) as n eqn:Hn.
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

Theorem nA_split {r : radix} : ∀ u i n e,
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

Theorem nA_upper_bound_for_add {r : radix} (rg := nat_ord_ring) : ∀ u i n,
  (∀ k, u k ≤ 2 * (rad - 1))
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
 apply Nat.mul_le_mono_r, Hur.
Qed.

Theorem nA_upper_bound_for_add_2 {r : radix} : ∀ u i n,
  (∀ k, u k ≤ 2 * (rad - 1))
  → u (i + 1) = rad - 2
  → u (i + 2) < rad
  → i + 3 ≤ n - 1
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

Theorem nA_upper_bound_for_add_3 {r : radix} : ∀ u i n,
  (∀ k, u k ≤ 2 * (rad - 1))
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
  apply Nat.mul_le_mono_pos_r; [ | apply Hur; flia Hs Hj ].
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
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
  (∀ k, u k ≤ 2 * (rad - 1))
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
   intros; apply Hur.
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
  (∀ k, u k ≤ 2 * (rad - 1))
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
     now apply nA_upper_bound_for_add.
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
  --now apply nA_upper_bound_for_add.
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
Theorem glop {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → (∀ k, d2n (numbers_to_digits u) (i + k) = rad - 1)
  → A_ge_1 i u 0 = true.
Proof.
intros * Hur Hu.
specialize (Hu 0) as H1.
rewrite Nat.add_0_r in H1.
unfold d2n, numbers_to_digits in H1.
destruct (LPO_fst (A_ge_1 i u)) as [H2| H2]; [ apply H2 | ].
destruct H2 as (j & Hjj & Hj).
move j before i; simpl in H1.
apply A_ge_1_false_iff in Hj.
remember (rad * (i + j + 3)) as n eqn:Hn.
replace (n - i - j - 2) with (n - i - 1 - S j) in Hj by flia.
remember (n - i - 1) as s eqn:Hs.
move s before n.
destruct j; [ | apply Hjj; flia ].
exfalso; clear Hjj; rewrite Nat.add_0_r in Hn.
rewrite Nat.pow_1_r in Hj.
destruct (lt_dec (nA i n u) (rad ^ s)) as [H2| H2].
-rewrite Nat.mod_small in Hj; [ | easy ].
 rewrite Nat.div_small in H1; [ | easy ].
 rewrite Nat.add_0_r in H1.
 clear H2.
 destruct (lt_dec (u i) rad) as [H2| H2].
 +rewrite Nat.mod_small in H1; [ clear H2 | easy ].
  specialize (Hu 1) as H2.
  unfold d2n, numbers_to_digits in H2.
  destruct (LPO_fst (A_ge_1 (i + 1) u)) as [H3| H3].
  *simpl in H2.
   replace (i + 1 + 3) with (i + 4) in H2 by flia.
   remember (rad * (i + 4)) as n1 eqn:Hn1.
   remember (n1 - (i + 1) - 1) as s1 eqn:Hs1.
   move s1 before n1.
   destruct (lt_dec (nA (i + 1) n1 u) (rad ^ s1)) as [H4| H4].
  --rewrite Nat.div_small in H2; [ | easy ].
    rewrite Nat.add_0_r in H2.
    destruct (lt_dec (u (i + 1) + 1) rad) as [H5| H5].
   ++rewrite Nat.mod_small in H2; [ clear H5 | easy ].
     assert (H : u (i + 1) = rad - 2) by flia H2.
     clear H2; rename H into H2; move H2 before H1.
     specialize (H3 0) as H5.
     apply A_ge_1_true_iff in H5.
     rewrite Nat.add_0_r, Nat.sub_0_r, Nat.pow_1_r in H5.
     replace (i + 1 + 3) with (i + 4) in H5 by flia.
     rewrite <- Hn1 in H5.
     replace (n1 - (i + 1) - 2) with (n1 - (i + 1) - 1 - 1) in H5 by flia.
     rewrite <- Hs1 in H5.
     rewrite Nat.mod_small in H5; [ | easy ].
     specialize (Hu 2) as H6.
     unfold d2n, numbers_to_digits in H6.
     destruct (LPO_fst (A_ge_1 (i + 2) u)) as [H7| H7].
    **simpl in H6.
      replace (i + 2 + 3) with (i + 5) in H6 by flia.
      remember (rad * (i + 5)) as n2 eqn:Hn2.
      remember (n2 - (i + 2) - 1) as s2 eqn:Hs2.
      move s2 before n2.
      destruct (lt_dec (nA (i + 2) n2 u) (rad ^ s2)) as [H8| H8].
    ---rewrite Nat.div_small in H6; [ | easy ].
       rewrite Nat.add_0_r in H6.
       destruct (lt_dec (u (i + 2) + 1) rad) as [H9| H9].
     +++rewrite Nat.mod_small in H6; [ clear H9 | easy ].
        assert (H : u (i + 2) = rad - 2) by flia H6.
        clear H6; rename H into H6; move H6 before H2.
        specialize (H3 1) as H9.
        apply A_ge_1_true_iff in H9.
        replace (i + 1 + 1 + 3) with (i + 5) in H9 by flia.
        rewrite <- Hn2 in H9.
        replace (n2 - (i + 1) - 1 - 2) with (n2 - (i + 2) - 1 - 1) in H9 by flia.
        assert (H : i + 2 < n2). {
          rewrite Hn2.
          destruct rad as [| rr]; [ easy | simpl; flia ].
        }
        replace (n2 - (i + 1) - 1) with (n2 - (i + 2) - 1 + 1) in H9 by flia H.
        rewrite <- Hs2 in H9; clear H.
(* mmm... I think that I must prove that it cannot be 988 (from u(i) on)
   what is proved later, actually *)
*)

Theorem num_to_dig_9_ge_7 {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → (∀ k, d2n (numbers_to_digits u) (i + k) = rad - 1)
  → u i ≥ rad - 3.
Proof.
intros * Hur Hu.
specialize (Hu 0) as H1.
rewrite Nat.add_0_r in H1.
unfold d2n, numbers_to_digits in H1.
unfold index_A_not_ge in H1.
destruct (LPO_fst (A_ge_1 u i)) as [H2| H2].
-simpl in H1.
 rewrite Nat.add_0_r in H1.
 remember (rad * (i + 3)) as n eqn:Hn.
 remember (n - i - 1) as s eqn:Hs.
 move s before n.
 destruct (lt_dec (nA i n u) (rad ^ s)) as [H4| H4].
 +rewrite Nat.div_small in H1; [ | easy ].
  rewrite Nat.add_0_r in H1.
  destruct (lt_dec (u i + 1) rad) as [H5| H5]; [ | flia H5 ].
  rewrite Nat.mod_small in H1; [ flia H1 | flia H5 ].
 +specialize (nA_upper_bound_for_add u i n Hur) as H5.
  rewrite <- Hs in H5.
  remember (nA i n u) as x eqn:Hx.
  replace x with (x - rad ^ s + 1 * rad ^ s) in H1(*, H3*).
  *rewrite Nat.div_add in H1; [ | now apply Nat.pow_nonzero ].
   assert (H6 : x - rad ^ s < rad ^ s). {
     specialize (Nat.pow_nonzero rad s radix_ne_0) as H.
     flia H5 H.
   }
   rewrite Nat.div_small in H1; [ | easy ].
   rewrite Nat.add_0_l in H1.
   destruct (lt_dec (u i + 1) rad) as [H7| H7]; [ | flia H7 ].
   rewrite Nat.mod_small in H1; [ | easy ].
   flia H1.
  *rewrite Nat.mul_1_l.
   apply Nat.sub_add.
   flia H4.
-destruct H2 as (k & Hjk & Hk).
 simpl in H1.
 apply A_ge_1_false_iff in Hk.
 remember (rad * (i + k + 3)) as n eqn:Hn.
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

Theorem A_ge_1_add_first_ge {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → A_ge_1 u i 0 = true
  → u (i + 1) ≥ rad - 2.
Proof.
intros * Hur Hu.
revert Hu.
apply Decidable.contrapositive; [ apply Nat.le_decidable | ].
intros H1; apply Nat.nle_gt in H1.
apply Bool.not_true_iff_false.
apply A_ge_1_false_iff.
rewrite Nat.add_0_r, Nat.sub_0_r, Nat.pow_1_r.
remember (rad * (i + 3)) as n eqn:Hn.
remember (n - i - 1) as s eqn:Hs.
move s before n.
assert (Hin : i + 2 ≤ n - 1). {
  rewrite Hn.
  specialize radix_ne_0 as H.
  destruct rad; [ easy | simpl; flia ].
}
specialize (nA_upper_bound_for_add_3 u i n Hur H1 Hin) as H2.
rewrite Nat.mod_small; [ easy | ].
eapply lt_le_trans; [ apply H2 | ].
replace (n - i - 2) with (s - 1) by flia Hs.
rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
replace rad with (rad ^ 1) at 1 by apply Nat.pow_1_r.
rewrite <- Nat.pow_add_r.
replace (1 + (s - 1)) with s by flia Hs Hin.
flia.
Qed.

Theorem A_ge_1_add_ge {r : radix} : ∀ u i j,
  (∀ k, u k ≤ 2 * (rad - 1))
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
  (∀ k, u k ≤ 2 * (rad - 1))
  → A_ge_1 u i 0 = true
  → u (i + 1) ≥ rad
  → u (i + 1) = 2 * (rad - 1).
Proof.
intros * Hur Hu Hui.
apply A_ge_1_true_iff in Hu.
rewrite Nat.add_0_r, Nat.sub_0_r, Nat.pow_1_r in Hu.
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
assert (H3 : ∀ k, v k ≤ 2 * (rad - 1)). {
  intros k; unfold v.
  destruct (Nat.eq_dec k (i + 1)) as [H4| H4]; [ | apply Hur ].
  eapply Nat.le_trans; [ apply Nat.le_sub_l | ].
  apply Hur.
}
assert (H4 : A_ge_1 v i 0 = true). {
  apply A_ge_1_true_iff.
  rewrite Nat.add_0_r, Nat.pow_1_r, Nat.sub_0_r.
  now rewrite <- Hn, <- Hs.
}
specialize (A_ge_1_add_first_ge v i H3 H4) as H5.
unfold v in H5.
destruct (Nat.eq_dec (i + 1) (i + 1)) as [H6| ]; [ | easy ].
apply Nat.le_antisymm; [ | flia Hui H5 ].
apply Hur.
Qed.

Theorem A_ge_1_add_first {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → A_ge_1 u i 0 = true
  → { u (i + 1) = rad - 2 } +
     { u (i + 1) = rad - 1 } +
     { u (i + 1) = 2 * (rad - 1) }.
Proof.
intros * Hur Hu.
specialize (A_ge_1_add_first_ge u i Hur Hu) as H1.
destruct (lt_dec (u (i + 1)) rad) as [H2| H2].
-left.
 destruct (lt_dec (u (i + 1)) (rad - 1)) as [H3| H3].
 +left; flia H1 H3.
 +right; flia H2 H3.
-right.
 apply Nat.nlt_ge in H2.
 now specialize (A_ge_1_add_first_ge_rad u i Hur Hu H2) as H3.
Qed.

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
replace (i + 1 + 3) with (i + 4) by flia.
remember (rad * (i + 4)) as n eqn:Hn.
remember (n - i - 1) as s eqn:Hs.
move s before n.
assert (Hin : i + 3 ≤ n - 1). {
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
remember (rad * (i + 1 + 3)) as n eqn:Hn.
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
    replace (S (S i) + 1) with (i + 3) by flia.
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

Theorem A_ge_1_add_8_eq {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
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
  specialize (Hur (i + k + 2)).
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
  (∀ k, u k ≤ 2 * (rad - 1))
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
 specialize (A_ge_1_add_8_eq u i Hur H1 j (Hu (j + 1))) as H2.
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
       eapply Nat.le_trans; [ apply Hur | ].
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
       +apply Nat.add_le_mono; [ | apply Hur ].
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
      --now apply nA_upper_bound_for_add.
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
  specialize (A_ge_1_add_8_eq u (i + j) Hur H4 k) as H2.
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
    replace (n - i - (j + k + 1) - 2) with (n - i - 1 - S (j + k + 1)) in H5
      by flia.
    replace (n - (i + j) - 1) with (n - i - 1 - j) by flia.
    replace (n - (i + j) - (k + 1) - 2) with (n - i - 1 - S (j + k + 1))
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
         specialize (nA_upper_bound_for_add u (S (i + j)) n Hur) as H8.
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
 assert (H : ∀ k, v k ≤ 2 * (rad - 1)). {
   intros j; unfold v.
   destruct (Nat.eq_dec j (i + 1)); [ flia | ].
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
(*
-intros H1 k.
 apply A_ge_1_true_iff.
 remember (rad * (i + k + 3)) as n eqn:Hn.
 remember (n - i - 1) as s eqn:Hs.
 move s before n.
 replace (n - i - k - 2) with (s - S k) by flia Hs.
 destruct H1 as [H1| [H1| H1]].
 +idtac.
  (* ouais *)
  admit.
 +idtac.
  (* faut voir *)
  admit.
 +destruct H1 as (j & Hbef & Hwhi & Haft).
  (* à vérifier *)
*)
Qed.

Theorem eq_nA_div_1 {r : radix} : ∀ i n u,
  (∀ k, u k ≤ 2 * (rad - 1))
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
replace (n - (i + j) - k - 2) with (s - S k) by flia Hs.
replace (n - i - (j + k) - 2) with (s - S k) in Hu by flia Hs.
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

Theorem all_num_to_dig_eq_pred_rad_2 {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → (∀ k, d2n (numbers_to_digits u) (i + k) = rad - 1)
  → if LPO_fst (A_ge_1 u i) then
       ∀ k,
       u (i + k) = rad - 2 ∨
       u (i + k) = 2 * rad - 2 ∨
       u (i + k) = rad - 1
     else
       u i = rad - 2 ∨
       u i = 2 * rad - 2 ∨
       u i = rad - 1.
Proof.
intros *.
intros Hur Hu.
specialize (Hu 0) as H1.
rewrite Nat.add_0_r in H1.
unfold d2n, numbers_to_digits in H1.
unfold index_A_not_ge in H1.
destruct (LPO_fst (A_ge_1 u i)) as [H2| H2].
-intros k; simpl in H1.
 specialize (Hu k) as H3.
 unfold d2n, numbers_to_digits in H3.
 unfold index_A_not_ge in H3.
 destruct (LPO_fst (A_ge_1 u (i + k))) as [H4| H4].
 +simpl in H3.
  rewrite Nat.add_0_r in H3.
  remember (rad * (i + k + 3)) as n eqn:Hn.
  remember (n - (i + k) - 1) as s eqn:Hs.
  move s before n.
  specialize (eq_mod_rad_add_pred_rad u (i + k) n s Hur Hs H3) as H5.
  destruct H5 as [H5| H5]; [ now left | ].
  destruct H5 as [H5| H5]; [ now right; left | now right; right ].
 +destruct H4 as (j & Hjj & Hj).
  specialize (A_ge_1_add_r_all_true_if u i H2 k) as H5.
  now rewrite H5 in Hj.
-destruct H2 as (j & Hjj & Hj).
 simpl in H1.
 remember (rad * (i + j + 3)) as n eqn:Hn.
 remember (n - i - 1) as s eqn:Hs.
 move s before n.
 specialize (eq_mod_rad_add_pred_rad u i n s Hur Hs H1) as H3.
 destruct H3 as [H3| H3]; [ now left | ].
 destruct H3 as [H3| H3]; [ now right; left | now right; right ].
Qed.

Theorem all_num_to_dig_eq_pred_rad {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → (∀ k, d2n (numbers_to_digits u) (i + k) = rad - 1)
  → ∀ k,
     let j := index_A_not_ge u (i + k) in
     let n := rad * (i + k + j + 3) in
     let s := n - (i + k) - 1 in
     u (i + k) = rad - 2 ∧ rad ^ s ≤ nA (i + k) n u < 2 * rad ^ s ∨
     u (i + k) = 2 * rad - 2 ∧ rad ^ s ≤ nA (i + k) n u < 2 * rad ^ s ∨
     u (i + k) = rad - 1 ∧ nA (i + k) n u < rad ^ s.
Proof.
intros *.
intros Hur Hu *.
specialize (Hu k) as H1.
unfold d2n, numbers_to_digits in H1.
simpl in H1.
fold j n s in H1.
subst s.
remember (n - (i + k) - 1) as s eqn:Hs.
now specialize (eq_mod_rad_add_pred_rad u (i + k) n s Hur Hs H1) as H3.
Qed.

(*
Theorem num_to_dig_if {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → (∀ k, d2n (numbers_to_digits u) (i + k) = rad - 1)
  → if LPO_fst (A_ge_1 i u) then
       u i mod rad = rad - 2 ∧
         (∀ k, u (i + k + 1) = rad - 1) ∨
       u i mod rad = (2 * rad - 3) mod rad ∧
         (∀ k, u (i + k + 1) = 2 * (rad - 1)) ∨
       (∃ j,
         (∀ k, k < j → u (i + k + 1) = rad - 1) ∧
         u (i + j + 1) = rad - 2 ∧
         (∀ k, u (i + j + k + 2) = 2 * (rad - 1)))
     else
       False.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hu.
specialize (Hu 0) as H1.
rewrite Nat.add_0_r in H1.
unfold d2n, numbers_to_digits in H1.
unfold index_A_not_ge in H1.
destruct (LPO_fst (A_ge_1 i u)) as [H2| H2].
-simpl in H1.
 rewrite Nat.add_0_r in H1.
 remember (rad * (i + 3)) as n eqn:Hn.
 remember (n - i - 1) as s eqn:Hs.
 move s before n.
 assert (Hin : i + 1 ≤ n - 1). {
   rewrite Hn.
   destruct rad; [ easy | simpl; flia ].
 }
 specialize (A_ge_1_add_all_true_if u _ Hur H2) as H3.
 specialize (eq_mod_rad_add_pred_rad u i n s Hur Hs H1) as H4.
 destruct H3 as [H3| [H3| H3]].
 +left.
  split; [ | easy ].
  destruct H4 as [(H4, H5)| [(H4, H5)| H4]].
  *rewrite H4.
   rewrite Nat.mod_small; [ easy | flia Hr ].
  *rewrite H4.
   rewrite Nat_mod_less_small; [ flia | flia Hr ].
  *idtac.
...
  split; [ | easy ].
  rewrite Nat.div_small in H1.
...
  *now rewrite Nat.add_0_r in H1.
  *rewrite Hs.
   apply nA_dig_seq_ub; [ | easy ].
   intros j Hj.
   specialize (H3 (j - i - 1)).
   replace (i + (j - i - 1) + 1) with j in H3 by flia Hj.
   rewrite H3; flia Hr.
 +right; left.
  split; [ | easy ].
  rewrite Nat_div_less_small in H1.
  *destruct (lt_dec (u i + 1) rad) as [H4| H4].
  --rewrite Nat.mod_small in H1; [ | easy ].
    rewrite Nat.mod_small; [ | flia H4 ].
...

    destruct (Nat.eq_dec rad 2) as [Hr2| Hr2].
   ++rewrite Hr2 in H1; simpl in H1.
     rewrite Hr2; simpl; flia H1.
   ++rewrite Nat_mod_less_small; [ flia H1 | flia Hr Hr2 ].
  --rewrite Nat_mod_less_small in H1.
   ++f_equal; flia H1.
   ++split; [ flia H4 | ].
     specialize (Hur i).
     rewrite <- Nat.add_assoc.
     apply Nat.lt_add_lt_sub_r.
     remember mult as f; simpl; subst f.
     apply Nat_le_neq_lt; [ flia Hur | ].
     intros H; rewrite H in H1.
     rewrite <- Nat.add_assoc in H1.
     rewrite Nat.sub_add in H1; [ | flia Hr ].
     rewrite Nat.mod_mul in H1; [ flia Hr H1 | easy ].
  *split.
  --rewrite nA_split_first; [ | easy ].
    eapply Nat.le_trans; [ | apply Nat.le_add_r ].
    specialize (H3 0); rewrite Nat.add_0_r in H3; rewrite H3.
    replace (n - i - 2) with (s - 1) by flia Hs.
    rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
    rewrite Nat.mul_sub_distr_r.
    replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
    rewrite <- Nat.mul_assoc.
    rewrite <- Nat.pow_add_r.
    replace (1 + (s - 1)) with s by flia Hin Hs.
    replace (2 * rad ^ s) with (rad ^ s + rad ^ s) by flia.
    rewrite <- Nat.add_sub_assoc; [ flia | ].
    replace s with (1 + (s - 1)) at 2 by flia Hin Hs.
    rewrite Nat.pow_add_r, Nat.pow_1_r.
    now apply Nat.mul_le_mono_r.
  --specialize (all_le_nA_le u 2 i (rad * (i + 3))) as H4.
    assert (H : ∀ j, i < j < rad * (i + 3) → u j ≤ 2 * (rad - 1)). {
      intros j Hj.
      specialize (H3 (j - i - 1)).
      replace (i + (j - i - 1) + 1) with j in H3 by flia Hj.
      now rewrite H3.
    }
    specialize (H4 H); clear H.
    rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H4.
    rewrite <- Hn, <- Hs in H4.
    eapply Nat.le_lt_trans; [ apply H4 | ].
    apply Nat.sub_lt; [ | flia ].
    replace 2 with (2 * 1) at 1 by flia.
    apply Nat.mul_le_mono_l.
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 +right; right; apply H3.
-destruct H2 as (j & Hjj & Hj).
 simpl in H1.
 apply A_ge_1_false_iff in Hj.
 remember (rad * (i + j + 3)) as n eqn:Hn.
 remember (n - i - 1) as s eqn:Hs.
 move s before n.
 replace (n - i - j - 2) with (s - S j) in Hj by flia Hs.
 (* tout de même... je me demande si ce cas n'est pas une contradiction
    entre Hu et Hj *)
 exfalso.
 specialize (eq_mod_rad_add_pred_rad u i n s Hur Hs H1) as H2.
 destruct H2 as [H2| [H2| H2]].
 +destruct H2 as (H2, H3).
  rewrite Nat_mod_less_small in Hj; [ | easy ].
  assert (Hin : i + 2 ≤ n - 1). {
    rewrite Hn.
    destruct rad; [ easy | simpl; flia ].
  }
  specialize (Hu 1) as H4.
  unfold d2n, numbers_to_digits in H4.
  destruct (LPO_fst (A_ge_1 (i + 1) u)) as [H5| H5].
  *simpl in H4.
   remember (rad * (i + 1 + 3)) as n1 eqn:Hn1.
   remember (n1 - (i + 1) - 1) as s1 eqn:Hs1.
   move s1 before n1.
   specialize (eq_mod_rad_add_succ_pred_rad u (i + 1) n1 s1 Hur Hs1 H4) as H6.
   specialize (A_ge_1_add_all_true_if u _ Hur H5) as H7.
   move H2 before H6; move H1 before H4.
   destruct H6 as [(H6, H8)| [(H6, H8)| [(H6, H8)| (H6, H8)]]].
  --move H3 before H8.
    admit. (* contradiction between H6 and H3 *)
  --move H3 before H8.
...
    admit. (* chais pas *)
  --move H3 before H8.
    admit. (* chais pas non plus *)
  --move H3 before H8.
    admit. (* chais davantage *)
  *destruct H5 as (k & Hkj & Hk); simpl in H4.
   admit.
 +destruct H2 as (H2, H3).
  admit.
 +destruct H2 as (H2, H3).
  admit.
...
*)

(*
Theorem num_to_dig_9 {r : radix} : ∀ u i,
  (∀ k, u k ≤ 2 * (rad - 1))
  → (∀ k, d2n (numbers_to_digits u) (i + k) = rad - 1)
  → ∀ k, u (i + k + 1) = rad - 1.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hur Hu k.
specialize (Hu k) as H1.
unfold d2n, numbers_to_digits in H1.
destruct (LPO_fst (A_ge_1 (i + k) u)) as [H2| H2].
-simpl in H1.
 remember (rad * (i + k + 3)) as n eqn:Hn.
 remember (n - (i + k) - 1) as s eqn:Hs.
 move s before n.
 specialize (A_ge_1_add_all_true_if u (i + k) Hur H2) as H3.
 destruct H3 as [H3| [H3| H3]].
 +specialize (H3 0).
  now rewrite Nat.add_0_r in H3.
 +exfalso.
  specialize (Hu (k + 1)) as H4.
  unfold d2n, numbers_to_digits in H4.
  replace (i + (k + 1)) with (i + k + 1) in H4 by flia.
  destruct (LPO_fst (A_ge_1 (i + k + 1) u)) as [H5| H5].
  *simpl in H4.
   replace (i + k + 1 + 3) with (i + k + 4) in H4 by flia.
   remember (rad * (i + k + 4)) as n1 eqn:Hn1.
   remember (n1 - (i + k + 1) - 1) as s1 eqn:Hs1.
   move s1 before n1.
   destruct (lt_dec (nA (i + k + 1) n1 u) (rad ^ s1)) as [H6| H6].
  --apply Nat.nle_gt in H6; apply H6; clear H6.
    assert (Hin : i + k + 2 ≤ n1 - 1). {
      rewrite Hn1.
      destruct rad; [ easy | simpl; flia ].
    }
    rewrite nA_split_first; [ | flia Hin ].
    specialize (H3 1).
    rewrite H3.
    replace (n1 - (i + k + 1) - 2) with (s1 - 1) by flia Hs1.
    rewrite <- Nat.mul_assoc.
    rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
    replace rad with (rad ^ 1) at 2 by apply Nat.pow_1_r.
    rewrite <- Nat.pow_add_r.
    replace (1 + (s1 - 1)) with s1 by flia Hs1 Hin.
    rewrite Nat.mul_sub_distr_l.
    replace (2 * rad ^ s1) with (rad ^ s1 + rad ^ s1) by flia.
    rewrite <- Nat.add_sub_assoc; [ flia | ].
    destruct s1; [ flia Hs1 Hin | ].
    replace (S s1 - 1) with s1 by flia.
    rewrite Nat.pow_succ_r; [ | flia ].
    now apply Nat.mul_le_mono_r.
  --apply Nat.nlt_ge in H6; rewrite Hs1 in H6.
    specialize (eq_nA_div_1 (i + k + 1) n1 u Hur H6) as H7.
    rewrite <- Hs1 in H6, H7.
    rewrite H7 in H4.
    rewrite <- Nat.add_assoc in H4; simpl in H4.
    specialize (H3 0).
    rewrite Nat.add_0_r in H3.
    rewrite H3 in H4.
    replace (2 * (rad - 1) + 2) with (0 + 2 * rad) in H4.
   ++rewrite Nat.mod_add in H4; [ | easy ].
     rewrite Nat.mod_0_l in H4; [ | easy ].
     flia Hr H4.
   ++rewrite Nat.mul_sub_distr_l, Nat.mul_1_r.
     rewrite Nat.sub_add; [ easy | simpl; flia Hr ].
  *destruct H5 as (j & Hjj & Hj).
   simpl in H4.
   remember (rad * (i + k + 1 + j + 3)) as n1 eqn:Hn1.
   remember (n1 - (i + k + 1) - 1) as s1 eqn:Hs1.
   move s1 before n1.
   assert (Hin : i + k + 2 ≤ n1 - 1). {
     rewrite Hn1.
     destruct rad; [ easy | simpl; flia ].
   }
  --apply A_ge_1_false_iff in Hj.
    remember (rad * (i + k + 1 + j + 3)) as n2 eqn:Hn2.
    replace (n2 - (i + k + 1) - j - 2) with (n2 - (i + k + 1) - 1 - S j) in Hj
      by flia.
    remember (n2 - (i + k + 1) - 1) as s2 eqn:Hs2.
    move s2 before n2.
    apply Nat.nle_gt in Hj; apply Hj; clear Hj.
    (* 9990000 ≤ 9999998 *)
admit.
 +destruct H3 as (j & Hbef & Hwhi & Haft).
  *destruct j.
  --exfalso; clear Hbef.
    rewrite Nat.add_0_r in Hwhi, Haft.
    specialize (A_ge_1_all_true_if u (i + k) H2) as H3.
    admit.
  --specialize (Hbef 0 (Nat.lt_0_succ j)) as H3.
    now rewrite Nat.add_0_r in H3.
-destruct H2 as (j & Hjj & Hj).
 simpl in H1.
 apply A_ge_1_false_iff in Hj.
 remember (rad * (i + k + j + 3)) as n eqn:Hn.
 remember (n - (i + k) - 1) as s eqn:Hs.
 move s before n.
 replace (n - (i + k) - j - 2) with (s - S j) in Hj by flia Hs.
...
 specialize (Hu (k + 1)) as H2.
 unfold d2n, numbers_to_digits in H2.
 replace (i + (k + 1)) with (i + k + 1) in H2 by flia.
 destruct (LPO_fst (A_ge_1 (i + k + 1) u)) as [H3| H3].
 +simpl in H2.
  replace (i + k + 1 + 3) with (i + k + 4) in H2 by flia.
  remember (rad * (i + k + 4)) as n1 eqn:Hn1.
  remember (n1 - (i + k + 1) - 1) as s1 eqn:Hs1.
  move s1 before n1.
  specialize (A_ge_1_add_all_true_if u (i + k + 1) Hur H3) as H4.
  destruct H4 as [H4| H4].
  *specialize (Hu (k + 2)) as H5.
   unfold d2n, numbers_to_digits in H5.
   replace (i + (k + 2)) with (i + k + 2) in H5 by flia.
   replace (i + k + 2 + 3) with (i + k + 5) in H5 by flia.
   destruct (LPO_fst (A_ge_1 (i + k + 2) u)) as [H6| H6].
  --simpl in H5.
    remember (rad * (i + k + 5)) as n2 eqn:Hn2.
    remember (n2 - (i + k + 2) - 1) as s2 eqn:Hs2.
    move s2 before n2.
    specialize (H4 0) as H7.
    replace (i + k + 1 + 0 + 1) with (i + k + 2) in H7 by flia.
    rewrite H7 in H5.
    destruct (lt_dec (nA (i + k + 2) n2 u) (rad ^ s2)) as [H8| H8].
   ++rewrite Nat.div_small in H5; [ | easy ].
     rewrite Nat.add_0_r, Nat.sub_add in H5; [ | easy ].
     rewrite Nat.mod_same in H5; [ flia Hr H5 | easy ].
   ++exfalso; apply H8; clear H8.
     rewrite Hs2.
     apply nA_dig_seq_ub.
    **intros p Hp.
      specialize (H4 (p - i - k - 2)).
      replace (i + k + 1 + (p - i - k - 2) + 1) with p in H4 by flia Hp.
      rewrite H4; flia Hr.
    **rewrite Hn2.
      destruct rad; [ easy | simpl; flia ].
  --destruct H6 as (p & Hjp & Hp).
    simpl in H5.
...
*)

Theorem A_ge_1_add_series_all_true_if {r : radix} : ∀ x y i,
  (∀ k, A_ge_1 (freal_add_series x y) i k = true)
  → (∀ k, fd2n x (i + k + 1) + fd2n y (i + k + 1) = rad - 1) ∨
     ((∀ k, fd2n x (i + k + 1) = rad - 1) ∧
       (∀ k, fd2n y (i + k + 1) = rad - 1)) ∨
     (∃ j,
       (∀ k, k < j → fd2n x (i + k + 1) + fd2n y (i + k + 1) = rad - 1) ∧
       fd2n x (i + j + 1) + fd2n y (i + j + 1) = rad - 2 ∧
       (∀ k, fd2n x (i + j + k + 2) = rad - 1) ∧
       (∀ k, fd2n y (i + j + k + 2) = rad - 1)).
Proof.
intros * Hxy.
specialize (freal_add_series_le_twice_pred x y) as H1.
specialize (A_ge_1_add_all_true_if _ i H1 Hxy) as H2.
destruct H2 as [H2| [H2| H2]].
-left; apply H2.
-right; left.
 unfold freal_add_series, sequence_add in H2.
 split; intros k; specialize (H2 k).
 1,2: specialize (digit_lt_radix (freal x (i + k + 1))) as H3.
 1,2: specialize (digit_lt_radix (freal y (i + k + 1))) as H4.
 1,2: unfold fd2n in H2 |-*; flia H2 H3 H4.
-right; right.
 unfold freal_add_series, sequence_add in H2.
 destruct H2 as (j & Hbef & Hwhi & Haft).
 exists j.
 split; [ easy | ].
 split; [ easy | ].
 split; intros k; specialize (Haft k).
 1,2: specialize (digit_lt_radix (freal x (i + j + k + 2))) as H3.
 1,2: specialize (digit_lt_radix (freal y (i + j + k + 2))) as H4.
 1,2: unfold fd2n in Haft |-*; flia Haft H3 H4.
Qed.

Theorem A_ge_1_all_true_for_sum_and_sum_norm_l {r : radix} : ∀ x y i n s,
  let u := freal_add_series (freal_normalize x) y in
  let v := freal_add_series x y in
  n = rad * (i + 3)
  → s = n - i - 1
  → (∀ k : nat, A_ge_1 u i k = true)
  → (∀ k : nat, A_ge_1 v i k = true)
  → (u i + nA i n u / rad ^ s) mod rad = (v i + nA i n v / rad ^ s) mod rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hn Hs Hku Hkv.
assert (Hsz : rad ^ s ≠ 0) by (now rewrite Hs; apply Nat.pow_nonzero).
assert (Hin : i + 1 ≤ n - 1). {
  rewrite Hn.
  specialize radix_ne_0 as H.
  destruct rad; [ easy | simpl; flia ].
}
unfold u at 1.
unfold v at 1.
unfold freal_add_series, sequence_add.
rewrite Nat.add_shuffle0; symmetry.
rewrite Nat.add_shuffle0; symmetry.
rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
f_equal; f_equal.
unfold freal_normalize.
unfold fd2n; simpl.
unfold digit_sequence_normalize.
unfold u, v.
do 2 rewrite nA_freal_add_series.
destruct (LPO_fst (is_9_strict_after (freal x) i)) as [H5| H5].
-specialize (is_9_strict_after_all_9 (freal x) i H5) as H7.
 clear H5; rename H7 into H5.
 specialize (nA_freal_normalize_0 _ n _ H5) as HnAnx.
 rewrite HnAnx, Nat.add_0_l.
 assert (HnAx : nA i n (fd2n x) = rad ^ s - 1). {
   unfold nA.
   destruct s; [ flia Hs Hin | ].
   rewrite power_summation; [ | easy ]; symmetry.
   rewrite Nat.add_comm, Nat.add_sub; symmetry.
   rewrite summation_mul_distr_l; simpl.
   rewrite summation_rtl.
   rewrite summation_shift; [ | easy ].
   replace (n - 1 - (i + 1)) with s by flia Hs.
   apply summation_eq_compat.
   intros j Hj.
   replace (n - 1 + (i + 1) - (i + 1 + j)) with (n - 1 - j) by flia.
   f_equal; [ | f_equal; flia Hs Hj ].
   specialize (H5 (n - 2 - j - i)).
   now replace (i + (n - 2 - j - i) + 1) with (n - 1 - j) in H5
     by flia Hs Hj.
 }
 rewrite HnAx.
 assert (HnAy : nA i n (fd2n y) ≠ 0). {
   specialize (proj1 (all_A_ge_1_true_iff i u) Hku 0) as H7.
   simpl in H7.
   rewrite Nat.add_0_r, <- Hn, <- Hs, Nat.mul_1_r in H7.
   rewrite Nat.sub_0_r in H7.
   unfold u in H7.
   rewrite nA_freal_add_series in H7.
   rewrite HnAnx, Nat.add_0_l in H7.
   intros H; rewrite H in H7.
   rewrite Nat.mod_0_l in H7; [ | flia Hsz ].
   apply Nat.le_0_r in H7.
   apply Nat.eq_mul_0 in H7.
   destruct H7 as [H7| H7]; [ flia H7 Hr | ].
   now apply Nat.pow_nonzero in H7.
 }
 rewrite Nat.div_small.
 +rewrite Nat.add_0_r.
  destruct (lt_dec (S (d2n (freal x) i)) rad) as [H6| H6].
  *simpl.
   rewrite <- Nat.add_1_r.
   rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
   rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
   f_equal; f_equal.
   rewrite Nat.mod_1_l; [ | easy ].
   remember (nA i n (fd2n y)) as z eqn:Hz.
   destruct z; [ easy | ].
   rewrite Nat.add_succ_r.
   rewrite <- Nat.add_succ_l.
   rewrite <- Nat.sub_succ_l; [ | flia Hsz ].
   simpl; rewrite Nat.sub_0_r.
   rewrite Nat_div_add_same_l; [ | easy ].
   rewrite Nat.div_small; [ now rewrite Nat.mod_1_l | ].
   apply Nat.succ_lt_mono.
   rewrite Hz.
   apply -> Nat.succ_le_mono.
   apply Nat.lt_le_incl.
   rewrite Hs.
   apply nA_upper_bound.
  *simpl.
   rewrite Nat.mod_0_l; [ | easy ].
   apply Nat.nlt_ge in H6.
   unfold d2n in H6.
   assert (H7 : dig (freal x i) = rad - 1). {
     specialize (digit_lt_radix (freal x i)).
     flia H6.
   }
   clear H6; rename H7 into H6.
   rewrite H6.
   remember (nA i n (fd2n y)) as z eqn:Hz.
   destruct z; [ easy | ].
   rewrite Nat.add_succ_r.
   rewrite <- Nat.add_succ_l.
   rewrite <- Nat.sub_succ_l; [ | flia Hsz ].
   simpl; rewrite Nat.sub_0_r.
   rewrite Nat_div_add_same_l; [ | easy ].
   rewrite Nat.div_small.
  --simpl.
    rewrite Nat.sub_add; [ | easy ].
    now rewrite Nat.mod_same.
  --apply Nat.succ_lt_mono.
    rewrite Hz.
    apply -> Nat.succ_le_mono.
    apply Nat.lt_le_incl.
    rewrite Hs.
    apply nA_upper_bound.
 +rewrite Hs.
  apply nA_upper_bound.
-destruct H5 as (j & Hjj & Hj).
 rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
 rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
 f_equal; f_equal.
 apply is_9_strict_after_false_iff in Hj.
 destruct (le_dec n (i + j + 1)) as [Hjn| Hjn].
 +f_equal; f_equal; f_equal.
  apply nA_eq_compat.
  intros k Hk.
  unfold freal_normalize, fd2n; simpl.
  unfold digit_sequence_normalize.
  destruct (LPO_fst (is_9_strict_after (freal x) k)) as [H5| H5].
  *specialize (is_9_strict_after_all_9 (freal x) k H5) as H6.
   clear H5; rename H6 into H5.
   specialize (H5 (i + j - k)).
   replace (k + (i + j - k) + 1) with (i + j + 1) in H5 by flia Hjn Hk.
   easy.
  *easy.
 +apply Nat.nle_gt in Hjn.
  f_equal.
  remember (freal_normalize x) as nx eqn:Hnx.
  destruct (lt_dec (nA i n (fd2n nx) + nA i n (fd2n y)) (rad ^ s)) as [H7| H7].
  *rewrite Nat.div_small; [ | easy ].
   destruct (lt_dec (nA i n (fd2n x) + nA i n (fd2n y)) (rad ^ s)) as [H8| H8].
  --now rewrite Nat.div_small.
  --assert (H9 : nA i n (fd2n nx) < nA i n (fd2n x)) by flia H7 H8.
    apply Nat.nle_gt in H9; exfalso; apply H9; clear H9.
    rewrite Hnx; apply nA_le_norm.
    unfold freal_normalize, fd2n; simpl.
    unfold digit_sequence_normalize.
    destruct (LPO_fst (is_9_strict_after (freal x) (i + 1))) as [H9| ].
   ++destruct (lt_dec (S (d2n (freal x) (i + 1))) rad) as [H10| H10].
    **simpl; unfold d2n; flia.
    **apply Nat.nlt_ge in H10.
      unfold d2n in H10.
      specialize (digit_lt_radix (freal x (i + 1))) as H.
      assert (H11 : dig (freal x (i + 1)) = rad - 1) by flia H10 H.
      clear H10 H.
      destruct j.
    ---unfold d2n in Hj.
       rewrite Nat.add_0_r in Hj; flia Hj H11.
    ---specialize (H9 j).
       apply is_9_strict_after_true_iff in H9.
       now replace (i + 1 + j + 1) with (i + S j + 1) in H9 by flia.
   ++easy.
  *destruct (lt_dec (nA i n (fd2n x) + nA i n (fd2n y)) (rad ^ s)) as [H8| H8].
  --remember (rad ^ s - nA i n (fd2n y)) as z.
    assert (H9 : nA i n (fd2n x) < z ≤ nA i n (fd2n nx)) by flia H7 H8 Heqz.
    exfalso.
    (* H9 implies z = nA n (fd2n nx) *)
    (* therefore nA i n (fd2n nx) + nA i n (fd2n y) = r^s *)
    (* and nA i n (fd2n x) + nA i n (fd2n y) = r^s-1 *)
    (* it contradicts Hku, because it would mean that
       nA i n u mod r^s = 0 *)
    assert (H5 : nA i n u = rad ^ s). {
      unfold u.
      rewrite nA_freal_add_series.
      apply Nat.le_antisymm; [ | flia H7 ].
      rewrite Hnx.
      specialize (nA_freal_normalize x i n) as [H| [H| H]].
      -rewrite Hnx, H in H9; flia H9.
      -rewrite H; flia H8.
      -rewrite H; flia H8.
    }
    specialize (proj1 (all_A_ge_1_true_iff i u) Hku 0) as H10.
    simpl in H10.
    rewrite Nat.add_0_r, Nat.mul_1_r, Nat.sub_0_r in H10.
    rewrite <- Hn, <- Hs in H10.
    rewrite H5, Nat.mod_same in H10; [ | easy ].
    apply Nat.le_0_r in H10.
    apply Nat.eq_mul_0 in H10.
    destruct H10 as [H10| H10].
   ++specialize radix_ge_2; flia H10.
   ++now apply Nat.pow_nonzero in H10.
  --apply Nat.nlt_ge in H7.
    apply Nat.nlt_ge in H8.
    specialize (nA_upper_bound nx n i) as H9.
    specialize (nA_upper_bound x n i) as H10.
    specialize (nA_upper_bound y n i) as H11.
    rewrite <- Hs in H9, H10, H11.
    assert (H12 : (nA i n (fd2n x) + nA i n (fd2n y)) / rad ^ s = 1). {
      apply Nat_mul_succ_le_div.
      flia H8 H10 H11.
    }
    rewrite H12.
    apply Nat_mul_succ_le_div.
    flia H7 H9 H11.
Qed.

Theorem freal_normalize_normalize {r : radix} : ∀ x i,
  fd2n (freal_normalize (freal_normalize x)) i =
  fd2n (freal_normalize x) i.
Proof.
intros.
remember (freal_normalize x) as nx eqn:Hnx.
unfold fd2n, freal_normalize; simpl.
unfold digit_sequence_normalize.
destruct (LPO_fst (is_9_strict_after (freal nx) i)) as [H1| H1].
-specialize (is_9_strict_after_all_9 _ _ H1) as H2.
 specialize (normalized_not_999 x) as H3.
 rewrite <- Hnx in H3.
 exfalso; apply H3; clear H3.
 exists (i + 1).
 intros j.
 specialize (H2 j).
 now rewrite Nat.add_shuffle0 in H2.
-easy.
Qed.

Theorem freal_norm_idemp {r : radix} : ∀ x,
  freal_norm_eq
    (freal_normalize x)
    (freal_normalize (freal_normalize x)).
Proof.
intros.
unfold freal_norm_eq.
remember (freal_normalize x) as nx eqn:Hnx.
destruct (LPO_fst (has_same_digits nx (freal_normalize nx))) as [H1| H1].
-easy.
-exfalso.
 destruct H1 as (n & Hjn & Hn).
 apply has_same_digits_false_iff in Hn; apply Hn; clear Hn.
 unfold freal_normalize, fd2n; simpl.
 unfold digit_sequence_normalize; simpl.
 destruct (LPO_fst (is_9_strict_after (freal nx) n)) as [H1| H1].
 +specialize (is_9_strict_after_all_9 _ _ H1) as H2.
  specialize (normalized_not_999 x) as H3.
  rewrite <- Hnx in H3.
  exfalso; apply H3; clear H3.
  exists (n + 1).
  intros j.
  specialize (H2 j).
  now rewrite Nat.add_shuffle0 in H2.
 +easy.
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
destruct (LPO_fst (has_same_digits y x)) as [Hs| Hs]; [ easy | exfalso ].
destruct (LPO_fst (has_same_digits x y)) as [Ht| Ht]; [ clear Hxy | easy ].
destruct Hs as (i & Hji & Hyx).
specialize (Ht i).
unfold has_same_digits in Ht, Hyx.
destruct (Nat.eq_dec (fd2n y i) (fd2n x i)) as [H1| H1]; [ easy | ].
destruct (Nat.eq_dec (fd2n x i) (fd2n y i)) as [H2| H2]; [ | easy ].
now symmetry in H2.
Qed.

Theorem freal_norm_eq_trans {r : radix} : transitive _ freal_norm_eq.
Proof.
intros x y z Hxy Hyz.
unfold freal_norm_eq in Hxy, Hyz |-*.
destruct (LPO_fst (has_same_digits x y)) as [Hx| Hx]; [ clear Hxy | easy ].
destruct (LPO_fst (has_same_digits y z)) as [Hy| Hy]; [ clear Hyz | easy ].
destruct (LPO_fst (has_same_digits x z)) as [Hz| Hz]; [ easy | exfalso ].
destruct Hz as (i & Hji & Hz).
specialize (Hx i).
specialize (Hy i).
unfold has_same_digits in Hx, Hy, Hz.
destruct (Nat.eq_dec (fd2n x i) (fd2n y i)) as [H1| H1]; [ | easy ].
destruct (Nat.eq_dec (fd2n y i) (fd2n z i)) as [H2| H2]; [ | easy ].
destruct (Nat.eq_dec (fd2n x i) (fd2n z i)) as [H3| H3]; [ easy | ].
apply H3.
now transitivity (fd2n y i).
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
 destruct (LPO_fst (has_same_digits nx x)) as [| H3]; [ easy | ].
 destruct H3 as (i & Hji & Hi).
 apply has_same_digits_false_iff in Hi.
 unfold fd2n in Hi.
 specialize (H2 i).
 now rewrite H2 in Hi.
-unfold freal_norm_not_norm_eq in H2.
 destruct H2 as (k & Hbef & Hwhi & Hxaft & Hnxaft).
 specialize (normalized_not_999 x) as H2.
 exfalso; apply H2; exists (k + 1).
 intros j.
 specialize (Hnxaft (1 + j)).
 rewrite Nat.add_assoc in Hnxaft.
 now rewrite <- Hnx.
Qed.

Theorem old_freal_normalized_cases {r : radix} : ∀ x,
  freal_norm_eq x (freal_normalize x) ∨
  (∃ n, ∀ i, fd2n x (n + i) = rad - 1).
Proof.
intros x.
specialize (freal_normalized_cases x) as [H1| H1]; [ now left | right ].
destruct H1 as (k & Hbef & Hwhi & Hnxaft & Hxaft).
exists (k + 1); intros i.
specialize (Hxaft (1 + i)).
now rewrite Nat.add_assoc in Hxaft.
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
destruct (LPO_fst (has_same_digits x y)) as [H| ]; [ clear Hxy | easy ].
specialize (all_eq_seq_all_eq x y H) as H1; clear H.
remember (freal_normalize x) as nx eqn:Hnx.
remember (freal_normalize y) as ny eqn:Hny.
move ny before nx.
destruct (LPO_fst (has_same_digits nx ny)) as [| H2]; [ easy | ].
destruct H2 as (i & Hij & Hi).
apply has_same_digits_false_iff in Hi.
apply Hi; clear Hi.
subst nx ny.
unfold fd2n, freal_normalize; simpl.
unfold digit_sequence_normalize.
destruct (LPO_fst (is_9_strict_after (freal x) i)) as [H2| H2].
-destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H3| H3].
 +destruct (lt_dec (S (d2n (freal x) i)) rad) as [H4| H4].
  *simpl.
   destruct (lt_dec (S (d2n (freal y) i)) rad) as [H5| H5].
  --simpl; unfold d2n.
    now rewrite H1.
  --unfold d2n in H4, H5.
    now rewrite H1 in H4.
  *destruct (lt_dec (S (d2n (freal y) i)) rad) as [H5| ]; [ | easy ].
   unfold d2n in H4, H5.
   now rewrite H1 in H4.
 +exfalso.
  destruct H3 as (j & Hjj & Hj).
  specialize (H2 j).
  apply is_9_strict_after_true_iff in H2.
  apply is_9_strict_after_false_iff in Hj.
  unfold d2n in H2, Hj.
  now rewrite H1 in H2.
-destruct H2 as (j & Hjj & Hj).
 destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H2| H2].
 +specialize (H2 j).
  apply is_9_strict_after_true_iff in H2.
  apply is_9_strict_after_false_iff in Hj.
  unfold d2n in H2, Hj.
  now rewrite H1 in Hj.
 +now rewrite H1.
Qed.

Add Parametric Morphism {r : radix} : freal_unorm_add
  with signature freal_norm_eq ==> freal_norm_eq ==> freal_norm_eq
  as freal_unorm_add_morph.
Proof.
intros x y Hxy x' y' Hxy'.
unfold freal_norm_eq in Hxy, Hxy'.
destruct (LPO_fst (has_same_digits x y)) as [H1| ]; [ clear Hxy | easy ].
destruct (LPO_fst (has_same_digits x' y')) as [H2| ]; [ clear Hxy' | easy ].
specialize (all_eq_seq_all_eq x y H1) as H3; clear H1.
specialize (all_eq_seq_all_eq x' y' H2) as H4; clear H2.
unfold freal_norm_eq.
remember (freal_unorm_add x x') as xx' eqn:Hxx'.
remember (freal_unorm_add y y') as yy' eqn:Hyy'.
destruct (LPO_fst (has_same_digits xx' yy')) as [| H1]; [ easy | ].
destruct H1 as (i & Hij & Hi).
apply has_same_digits_false_iff in Hi; apply Hi; clear Hi.
subst xx' yy'.
unfold fd2n, freal_unorm_add.
f_equal; simpl.
unfold freal_add_to_seq.
apply numbers_to_digits_eq_compat.
intros j.
unfold freal_add_series, sequence_add, fd2n.
now rewrite H3, H4.
Qed.

Theorem freal_eq_add_norm_l {r : radix} : ∀ x y,
  (freal_unorm_add (freal_normalize x) y = freal_unorm_add x y)%F.
Proof.
intros.
specialize radix_ge_2 as Hr.
specialize (freal_normalized_cases x) as [H1| H1].
-unfold freal_eq.
 now rewrite H1.
-destruct H1 as (n & Hbef & Hwhi & Hnaft & Haft).
 unfold "="%F.
 remember (freal_normalize x) as nx eqn:Hnx.
 unfold freal_norm_eq.
 remember (freal_normalize (freal_unorm_add nx y)) as nxy eqn:Hnxy.
 remember (freal_normalize (freal_unorm_add x y)) as xy eqn:Hxy.
 move xy before nxy.
 destruct (LPO_fst (has_same_digits nxy xy)) as [| H1]; [ easy | ].
 destruct H1 as (i & Hji & Hi).
 apply has_same_digits_false_iff in Hi.
 apply Hi; clear Hi.
 subst nxy xy.
 remember (freal_unorm_add nx y) as nxy eqn:Hnxy.
 remember (freal_unorm_add x y) as xy eqn:Hxy.
 move xy before nxy.
 unfold freal_normalize, fd2n; simpl.
 unfold digit_sequence_normalize.
 destruct (LPO_fst (is_9_strict_after (freal nxy) i)) as [H1| H1].
 +specialize (is_9_strict_after_all_9 _ _ H1) as H2; clear H1.
  assert (H1 : ∀ k, fd2n y (max (n - 1) i + k + 1) = rad - 1). {
    intros k.
    specialize (H2 (k + max (n - 1) i - i)) as H1.
    replace (i + (k + max (n - 1) i - i)) with (max (n - 1) i + k) in H1
      by flia.
    rewrite Hnxy in H1.
    unfold freal_unorm_add in H1; simpl in H1.
    unfold freal_add_to_seq in H1.
    unfold d2n, numbers_to_digits in H1; simpl in H1.
    remember (freal_add_series nx y) as z eqn:Hz.
    remember (max (n - 1) i + k + 1) as j eqn:Hj.
    remember (rad * (j + index_A_not_ge z j + 3)) as m eqn:Hm.
    remember (m - j - 1) as s eqn:Hs.
    move s before m.
    assert (H : z j = fd2n y j). {
      rewrite Hz.
      unfold freal_add_series.
      unfold sequence_add.
      specialize (Hnaft (j - n)) as H3.
      replace (n + (j - n)) with j in H3 by flia Hj.
      now rewrite H3.
    }
    rewrite H in H1; clear H.
    assert (H : nA j m z < rad ^ s). {
      rewrite Hz.
      rewrite nA_freal_add_series.
      assert (H : nA j m (fd2n nx) = 0). {
        unfold nA.
        apply all_0_summation_0.
        intros p Hp.
        specialize (Hnaft (p - n)) as H3.
        replace (n + (p - n)) with p in H3 by flia Hp Hj.
        now rewrite H3.
      }
      rewrite H, Nat.add_0_l; clear H.
      rewrite Hs.
      apply nA_upper_bound.
    }
    rewrite Nat.div_small in H1; [ | easy ].
    rewrite Nat.add_0_r in H1.
    rewrite Nat.mod_small in H1; [ easy | ].
    apply digit_lt_radix.
  }
  remember (freal_add_series nx y) as u eqn:Hu.
  remember (freal_add_series x y) as v eqn:Hv.
  move v before u.
  assert (Hum : ∀ k, u (max (n - 1) i + 1 + k) = rad - 1). {
    intros k.
    rewrite Hu.
    unfold freal_add_series, sequence_add.
    specialize (Hnaft (k + max (n - 1) i + 1 - n)) as H16.
    specialize (H1 k) as H17.
    remember (max (n - 1) i) as m eqn:Hm.
    replace (n + (k + m + 1 - n)) with (m + 1 + k) in H16 by flia Hm.
    replace (m + k + 1) with (m + 1 + k) in H17 by flia.
    now rewrite H16, H17.
  }
  assert (Hvm : ∀ k, v (max (n - 1) i + 1 + k) = 2 * rad - 2). {
    intros k.
    rewrite Hv.
    unfold freal_add_series, sequence_add.
    specialize (Haft (k + max (n - 1) i + 1 - n)) as H17.
    specialize (H1 k) as H18.
    remember (max (n - 1) i) as m eqn:Hm.
    replace (n + (k + m + 1 - n)) with (m + 1 + k) in H17 by flia Hm.
    replace (m + k + 1) with (m + 1 + k) in H18 by flia.
    rewrite H17, H18; flia.
  }
  destruct (LPO_fst (is_9_strict_after (freal xy) i)) as
    [H3| H3].
  *specialize (is_9_strict_after_all_9 _ _ H3) as H4; clear H3.
   specialize (H2 (max (n - 1) i - i)) as H5.
   specialize (H4 (max (n - 1) i - i)) as H6.
   replace (i + (max (n - 1) i - i)) with (max (n - 1) i) in H5, H6 by flia.
   rewrite Hnxy in H5; rewrite Hxy in H6.
   unfold freal_unorm_add in H5, H6.
   simpl in H5, H6.
   unfold freal_add_to_seq in H5, H6.
   rewrite <- Hu in H5; rewrite <- Hv in H6.
   remember (max (n - 1) i + 1) as m eqn:Hm.
   assert (H : ∀ k, fd2n y (m + k) = rad - 1). {
     intros k.
     specialize (H1 k).
     now replace (max (n - 1) i + k + 1) with (m + k) in H1 by flia Hm.
   }
   clear H1; rename H into H1; move H1 before H4.
   move m before i.
   move H4 before H2.
...
   unfold d2n, numbers_to_digits in H5, H6.
   simpl in H5, H6.
   remember (rad * (m + index_A_not_ge u m + 3)) as np eqn:Hnp.
   remember (rad * (m + index_A_not_ge v m + 3)) as p eqn:Hp.
   move p before np; move Hp before Hnp.
   destruct (lt_dec (S (d2n (freal nxy) i)) rad) as [H7| H7].
  --simpl.
    destruct (lt_dec (S (d2n (freal xy) i)) rad) as [H8| H8].
   ++simpl; f_equal.
     rewrite Hnxy in H7; rewrite Hxy in H8.
     rewrite Hnxy, Hxy.
     unfold freal_unorm_add in H7, H8 |-*; simpl in H7, H8 |-*.
     unfold freal_add_to_seq in H7, H8 |-*.
     rewrite <- Hu in H7; rewrite <- Hv in H8.
     rewrite <- Hu, <- Hv.
     unfold d2n, numbers_to_digits in H7, H8 |-*; simpl in H7, H8 |-*.
     remember (rad * (i + index_A_not_ge u i + 3)) as nq eqn:Hnq.
     remember (rad * (i + index_A_not_ge v i + 3)) as q eqn:Hq.
     move q before nq; move Hq before Hnq.
     assert (Hiq : i + 2 ≤ q - 1). {
          rewrite Hq.
          destruct rad; [ easy | simpl; flia ].
     }
     assert (Hinq : i + 2 ≤ nq - 1). {
          rewrite Hnq.
          destruct rad; [ easy | simpl; flia ].
     }
     destruct (lt_dec (nA i nq u) (rad ^ (nq - i - 1))) as [H9| H9].
    **rewrite Nat.div_small in H7 |-*; [ | easy | easy ].
      rewrite Nat.add_0_r in H7 |-*.
      destruct (lt_dec (nA i q v) (rad ^ (q - i - 1))) as [H10| H10].
    ---rewrite Nat.div_small in H8 |-*; [ | easy | easy ].
       rewrite Nat.add_0_r in H8 |-*.
       rewrite Hu, Hv.
       unfold freal_add_series, sequence_add in H7, H8 |-*.
       rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
       rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
       f_equal; f_equal.
       destruct (lt_dec i (n - 1)) as [H11| H11].
     +++f_equal; unfold fd2n.
        now apply digit_eq_eq, Hbef.
     +++apply Nat.nlt_ge in H11.
        rewrite Nat.max_r in Hm; [ | easy ].
        specialize (Haft (i + 1 - n)) as H12.
        replace (n + (i + 1 - n)) with (i + 1) in H12 by flia H11.
        specialize (H1 0) as H13; rewrite Hm, Nat.add_0_r in H13.
        exfalso; apply Nat.nle_gt in H10; apply H10; clear H10.
        rewrite nA_split_first; [ | flia Hiq ].
        remember (v (i + 1)) as w eqn:Hw.
        rewrite Hv in Hw; subst w.
        unfold freal_add_series, sequence_add.
        rewrite H12, H13.
        replace (rad - 1 + (rad - 1)) with (2 * rad - 2) by flia.
        rewrite Nat.mul_sub_distr_r.
        rewrite <- Nat.mul_assoc, <- Nat.pow_succ_r; [ | flia ].
        replace (S (q - i - 2)) with (q - i - 1) by flia Hiq.
        simpl.
        do 2 rewrite Nat.add_0_r.
        rewrite <- Nat.add_sub_swap.
      ***rewrite <- Nat.add_assoc.
         rewrite <- Nat.add_sub_assoc; [ flia | ].
         apply Nat.add_le_mono.
      ----replace (q - i - 1) with (S (q - i - 2)) by flia Hiq.
          now simpl; apply Nat_mul_le_pos_l.
      ----rewrite nA_split_first; [ | flia Hiq ].
          rewrite Hv.
          unfold freal_add_series, sequence_add.
          specialize (Haft (i + 2 - n)) as H14.
          replace (n + (i + 2 - n)) with (S i + 1) in H14 by flia H11.
          specialize (H1 1) as H15; rewrite Hm in H15.
          replace (i + 1 + 1) with (S i + 1) in H15 by flia.
          rewrite H14, H15.
          replace (rad - 1 + (rad - 1)) with (2 * rad - 2) by flia.
          rewrite Nat.mul_sub_distr_r.
          rewrite <- Nat.mul_assoc, <- Nat.pow_succ_r; [ | flia ].
          replace (S (q - S i - 2)) with (q - i - 2) by flia Hiq.
          simpl.
          do 2 rewrite Nat.add_0_r.
          rewrite <- Nat.add_sub_swap.
       ++++rewrite <- Nat.add_assoc.
           rewrite <- Nat.add_sub_assoc; [ flia | ].
           replace (q - i - 2) with (S (q - S i - 2)) by flia Hiq.
           simpl.
           remember (rad ^ (q - S i - 2)) as z eqn:Hz.
           replace (z + z) with (2 * z) by flia.
           apply le_trans with (m := rad * z); [ | flia ].
           now apply Nat.mul_le_mono_r.
       ++++assert (H : rad ^ (q - S i - 2) ≤ rad ^ (q - i - 2)). {
             replace (q - i - 2) with (S (q - S i - 2)) by flia Hiq; simpl.
             now apply Nat_mul_le_pos_l.
           }
           apply Nat.add_le_mono; apply H.
      ***assert (H : rad ^ (q - i - 2) ≤ rad ^ (q - i - 1)). {
             replace (q - i - 1) with (S (q - i - 2)) by flia Hiq; simpl.
             now apply Nat_mul_le_pos_l.
           }
           apply Nat.add_le_mono; apply H.
    ---assert (H11 : nA i q v < 2 * rad ^ (q - i - 1)). {
         assert (H : ∀ k, v k ≤ 2 * (rad - 1)). {
           intros k.
           rewrite Hv.
           unfold freal_add_series, sequence_add.
           simpl; rewrite Nat.add_0_r.
           apply Nat.add_le_mono; apply digit_le_pred_radix.
         }
         specialize (nA_upper_bound_for_add v i q H) as H11.
         rewrite Nat.mul_sub_distr_l, Nat.mul_1_r in H11.
         specialize (Nat.pow_nonzero rad (q - i - 1) radix_ne_0) as H12.
         flia H11 H12.
       }
       rewrite Nat_div_less_small in H8 |-*; [ | flia H10 H11 | flia H10 H11 ].
       rewrite Hu, Hv.
       unfold freal_add_series, sequence_add in H7, H8 |-*.
       rewrite Nat.add_shuffle0.
       rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
       rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
       f_equal; f_equal.
       destruct (lt_dec (n - 1) i) as [H12| H12].
     +++specialize (Hnaft (i - n)) as H13.
        specialize (Haft (i - n)) as H14.
        replace (n + (i - n)) with i in H13, H14 by flia H12.
        rewrite H13, H14.
        rewrite Nat.sub_add; [ | easy ].
        rewrite Nat.mod_same; [ | easy ].
        now apply Nat.mod_0_l.
     +++apply Nat.nlt_ge in H12.
        destruct (Nat.eq_dec i (n - 1)) as [H13| H13].
      ***destruct Hwhi as [Hwhi| Hwhi].
      ----subst n; simpl in H13; subst i.
          simpl in Hm; subst m.
          simpl in Haft, Hnaft.
          rewrite Haft, Hnaft.
          rewrite Nat.sub_add; [ | easy ].
          rewrite Nat.mod_same; [ | easy ].
          now apply Nat.mod_0_l.
      ----rewrite <- H13 in Hwhi.
          rewrite Hwhi.
          now rewrite Nat.add_1_r.
      ***assert (H14 : i < n - 1) by flia H12 H13; clear H12 H13.
         rewrite Nat.max_l in Hm; [ | flia H14 ].
         destruct Hwhi as [Hwhi| Hwhi]; [ flia Hwhi H14 | ].
         destruct n; [ flia H14 | ].
         rewrite Nat.sub_add in Hm; [ | flia ].
         replace (S n - 1) with n in Hbef, Hwhi, H14 by flia.
         subst m.
         exfalso.
         destruct (lt_dec (i + 1) n) as [H12| H12].
      ----rewrite nA_split_first in H9, H10; [ | flia Hiq | flia Hinq ].
          assert (H13 : u (i + 1) = v (i + 1)). {
            rewrite Hu, Hv.
            unfold freal_add_series, sequence_add.
            now unfold fd2n; rewrite Hbef.
          }
          rewrite <- H13 in H10.
          destruct (le_dec rad (u (i + 1))) as [H15| H15].
       ++++apply Nat.nle_gt in H9; apply H9; clear H9.
           replace (nq - i - 1) with (S (nq - i - 2)) by flia Hinq.
           eapply le_trans; [ | apply Nat_add_le_pos_r ].
           now simpl; apply Nat.mul_le_mono_r.
       ++++apply Nat.nle_gt in H15.
...
           rewrite H13, Hv in H15.
           unfold freal_add_series, sequence_add in H15.
           apply H10; clear H10.
           rewrite H13.
           rewrite <- nA_split_first; [ | flia Hiq ].

...
    **idtac.
      ...
   ++exfalso.
     ...
  --destruct (lt_dec (S (d2n (freal xy) i)) rad) as [H8| ]; [ | easy ].
    exfalso.
    ...
  *destruct H3 as (j & Hjj & Hj).
   apply is_9_strict_after_false_iff in Hj.
   ...
 +destruct H1 as (j & Hjj & Hj).
  apply is_9_strict_after_false_iff in Hj.
  destruct (LPO_fst (is_9_strict_after (freal xy) i)) as [H1| H1].
  *specialize (is_9_strict_after_all_9 _ _ H1) as H2; clear H1.
   ...
  *destruct H1 as (k & Hjk & Hk).
   move k before j; move Hjk before Hjj.
   apply is_9_strict_after_false_iff in Hk.
   ...
...
intros.
unfold freal_eq.
unfold freal_norm_eq.
remember (freal_normalize x) as nx eqn:Hnx.
remember (freal_unorm_add nx y) as nxy eqn:Hnxy.
remember (freal_unorm_add x y) as xy eqn:Hxy.
move xy before nxy.
remember (freal_normalize nxy) as nnxy eqn:Hnnxy.
remember (freal_normalize xy) as n1xy eqn:Hn1xy.
move n1xy before nnxy.
destruct (LPO_fst (has_same_digits nnxy n1xy)) as [H1| H1]; [ easy | ].
destruct H1 as (i & Hji & Hi).
apply has_same_digits_false_iff in Hi.
apply Hi; clear Hi.
subst nnxy n1xy.
subst nxy xy.
unfold fd2n.
simpl.
unfold digit_sequence_normalize.
remember (freal_add_to_seq nx y) as nxy eqn:Hnxy.
remember (freal_add_to_seq x y) as xy eqn:Hxy.
move xy before nxy.
(*
remember (rad * (i + 3)) as n eqn:Hn.
remember (n - i - 1) as s eqn:Hs.
move s before n.
assert (Hsz : rad ^ s ≠ 0) by (now rewrite Hs; apply Nat.pow_nonzero).
assert (Hin : i + 1 ≤ n - 1). {
  rewrite Hn.
  specialize radix_ne_0 as H.
  destruct rad; [ easy | simpl; flia ].
}
*)
set (u := freal_add_series (freal_normalize x) y).
set (v := freal_add_series x y).
destruct (LPO_fst (is_9_strict_after nxy i)) as [H1| H1].
-specialize (is_9_strict_after_all_9 _ _ H1) as H2.
 clear H1; rename H2 into H1.
 rewrite Hnxy in H1.
 unfold freal_add_to_seq in H1.
 rewrite Hnx in H1.
 fold u in H1.
(*
 specialize (all_num_to_dig_eq_pred_rad u (i + 1)) as H2.
 specialize (freal_add_series_le_twice_pred nx y) as H.
 rewrite Hnx in H; fold u in H.
 specialize (H2 H); clear H.
 assert (H : ∀ k, d2n (numbers_to_digits u) (i + 1 + k) = rad - 1). {
   intros k; specialize (H1 k).
   now rewrite Nat.add_shuffle0 in H1.
 }
 specialize (H2 H); clear H.
 rename H2 into Hi2.
*)
 destruct (LPO_fst (is_9_strict_after xy i)) as [H2| H2].
 +specialize (is_9_strict_after_all_9 _ _ H2) as H3.
  clear H2; rename H3 into H2.
  rewrite Hxy in H2.
  unfold freal_add_to_seq in H2.
  fold v in H2.
(*
  specialize (all_num_to_dig_eq_pred_rad v (i + 1)) as H3.
  specialize (freal_add_series_le_twice_pred x y) as H.
  fold v in H.
  specialize (H3 H); clear H.
  assert (H : ∀ k, d2n (numbers_to_digits v) (i + 1 + k) = rad - 1). {
    intros k; specialize (H2 k).
    now rewrite Nat.add_shuffle0 in H2.
  }
  specialize (H3 H); clear H.
  rename H3 into Hi3.
*)
  destruct (lt_dec (S (d2n nxy i)) rad) as [H3| H3].
  *simpl.
   rewrite Hnxy, Hnx in H3.
   unfold freal_add_to_seq, d2n in H3.
   fold u in H3.
   destruct (lt_dec (S (d2n xy i)) rad) as [H4| H4].
  --simpl.
    rewrite Hxy in H4.
    unfold freal_add_to_seq, d2n in H4.
    fold v in H4.
    f_equal.
    unfold d2n.
    rewrite Hnxy, Hxy.
    rewrite Hnx.
...
    unfold freal_add_to_seq.
    fold u v.
    unfold numbers_to_digits in H3, H4 |-*.
    unfold index_A_not_ge in H3, H4.
    unfold index_A_not_ge.
    destruct (LPO_fst (A_ge_1 u i)) as [Hku| (m & Hjm & Hm)].
   ++simpl in H3 |-*.
     rewrite Nat.add_0_r in H3 |-*.
     rewrite <- Hn, <- Hs in H3 |-*.
     destruct (LPO_fst (A_ge_1 v i)) as [Hkv| (p & Hjp & Hp)].
    **simpl in H4 |-*.
      rewrite Nat.add_0_r, <- Hn, <- Hs.
      now apply A_ge_1_all_true_for_sum_and_sum_norm_l.
    **simpl in H4; simpl.
      remember (rad * (i + p + 3)) as n1 eqn:Hn1.
      remember (n1 - i - 1) as s1 eqn:Hs1.
      move s1 before n1.
      clear - H3 Hr Hsz Hn Hn1 Hnx Hs Hs1 Hin Hku Hjp Hp.
      move p before n.
      move H3 at bottom.
...
      assert (H : nA i n1 v / rad ^ s1 = nA i n v / rad ^ s). {
        destruct (lt_dec p (n - 1)) as [H1| H1].
        -assert (H : n1 - n = rad * p) by flia Hn Hn1.
         assert (Hnn : n ≤ n1). {
           destruct p; [ now rewrite Hn, Hn1, Nat.add_0_r | ].
           destruct rad; [ easy | simpl in H; flia H ].
         }
         apply A_ge_1_false_iff in Hp.
         rewrite <- Hn1, <- Hs1 in Hp.
         replace (n1 - i - p - 2) with (s1 - S p) in Hp by flia Hs1.
         replace s1 with (n1 - n + s) by flia Hs Hs1 Hin Hnn.
         rewrite Nat.pow_add_r.
         rewrite <- Nat.div_div; try now apply Nat.pow_nonzero.
         rewrite nA_split with (e := n); [ | flia Hin Hnn ].
         rewrite Nat.add_comm.
         rewrite Nat.div_add; [ | now apply Nat.pow_nonzero ].
         destruct (lt_dec (nA (n - 1) n1 v) (rad ^ (n1 - n))) as [H4| H4].
         +now rewrite Nat.div_small with (b := rad ^ (n1 - n)).
         +rewrite Nat_div_less_small with (b := rad ^ (n1 - n)).
          *apply Nat_div_add_div.
admit.
*admit.
        -apply Nat.nlt_ge in H1.

...

         exfalso; apply H4; clear H4.
         specialize (nA_upper_bound_for_add v (n - 1) n1) as H4.
         assert (Hv : ∀ k, v k ≤ 2 * (rad - 1)). {
           intros j; unfold v.
           unfold freal_add_series, sequence_add.
           replace (2 * (rad - 1)) with ((rad - 1) + (rad - 1)) by flia.
           apply Nat.add_le_mono; apply digit_le_pred_radix.
         }
         specialize (H4 Hv); clear Hv.
         replace (n1 - (n - 1) - 1) with (n1 - n) in H4 by flia Hs Hs1 Hin Hnn.
apply A_ge_1_false_iff in Hp.
rewrite <- Hn1, <- Hs1 in Hp.
...

     destruct (Nat.eq_dec j (i + 1)); [ flia | ].
     apply Hur.
   }
   specialize (H2 H); clear H.
...

rewrite H.
clear n1 s1 Hn1 Hs1 H.
...
      apply A_ge_1_false_iff in Hp.
      rewrite <- Hn1, <- Hs1 in Hp.
      replace (n1 - i - p - 2) with (s1 - S p) in Hp by flia Hs1.
      unfold u at 1.
      unfold v at 1.
      unfold freal_add_series, sequence_add.
      rewrite Nat.add_shuffle0; symmetry.
      rewrite Nat.add_shuffle0; symmetry.
      rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
      rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
      f_equal; f_equal.
      unfold freal_normalize.
      unfold fd2n; simpl.
      unfold digit_sequence_normalize.
      unfold u, v.
      do 2 rewrite nA_freal_add_series.
      destruct (LPO_fst (is_9_strict_after (freal x) i)) as [H5| H5].
    ---specialize (is_9_strict_after_all_9 (freal x) i H5) as H7.
       exfalso.
       clear H5; rename H7 into H5.
       specialize (nA_freal_normalize_0 _ n _ H5) as HnAnx.
       rewrite <- Hnx in HnAnx.
       assert (H7 : ∀ k, fd2n nx (i + k + 1) = 0). {
         intros j.
         assert (H : ∀ k, fd2n x (i + 1 + k) = rad - 1). {
           intros k.
           specialize (H5 k).
           unfold d2n in H5; unfold fd2n.
           now replace (i + 1 + k) with (i + k + 1) by flia.
         }
         specialize (normalized_999 x (i + 1) H) as H7.
         rewrite <- Hnx in H7.
         replace (i + j + 1) with (i + 1 + j) by flia.
         apply H7.
       }
       move H7 before H5.
       assert (H8 : ∀ k, fd2n y (i + k + 1) = rad - 1). {
         intros k.
         specialize (A_ge_1_add_series_all_true_if _ _ i Hku) as Hu.
         rewrite <- Hnx in Hu.
         destruct Hu as [Hu| [Hu| Hu]]; [ | easy | ].
         -specialize (Hu k).
          now rewrite H7 in Hu.
         -destruct Hu as (j & Hbef & Hwhi & Haftx & Hafty).
          specialize (Haftx 0).
          specialize (H7 (j + 1)).
          replace (i + j + 0 + 2) with (i + (j + 1) + 1) in Haftx by flia.
          rewrite Haftx in H7; flia Hr H7.
       }
       move H7 before H8; move H5 before H7.
       (* contradiction with Hp *)
       assert (H11 : rad ^ s1 ≠ 0) by now rewrite Hs1; apply Nat.pow_nonzero.
       specialize (all_9_nA x i p H5) as H9.
       specialize (all_9_nA y i p H8) as H10.
       rewrite <- Hn1, <- Hs1 in H9, H10.
       move Hp at bottom.
       unfold v in Hp.
       rewrite nA_freal_add_series in Hp.
       rewrite H9, H10 in Hp; clear H9 H10.
       replace (rad ^ s1 - 1 + (rad ^ s1 - 1)) with (rad ^ s1 - 2 + 1 * rad ^ s1) in Hp.
     +++rewrite Nat.mod_add in Hp; [ | easy ].
        rewrite Nat.mod_small in Hp; [ | flia H11 ].
        apply Nat.nle_gt in Hp; apply Hp; clear Hp.
        rewrite Nat_pow_sub_1_mul_pow.
        rewrite Nat.add_comm.
        rewrite Nat.sub_add.
      ***apply Nat.sub_le_mono_l.
         remember (s1 - S p) as a eqn:Ha.
         destruct a.
      ----rewrite Hs1, Hn1 in Ha.
          destruct rad; [ easy | simpl in Ha; flia Ha ].
      ----simpl; replace 2 with (2 * 1) by flia.
          apply Nat.mul_le_mono; [ apply radix_ge_2 | ].
          now apply Nat_pow_ge_1.
      ***rewrite Hs1, Hn1.
         destruct rad; [ easy | simpl; flia ].
     +++rewrite Nat.mul_1_l.
        enough (H : 2 ≤ rad ^ s1) by flia H.
        rewrite Hs1.
        destruct s1.
      ***rewrite Hn1 in Hs1.
         destruct rad; [ easy | simpl in Hs1; flia Hs1 ].
      ***rewrite <- Hs1; simpl.
         replace 2 with (2 * 1) by flia.
         apply Nat.mul_le_mono; [ apply radix_ge_2 | ].
         now apply Nat_pow_ge_1.
    ---rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
       rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
       f_equal; f_equal.
       destruct H5 as (j & Hjj & Hj); move j before i.
       apply is_9_strict_after_false_iff in Hj.
       do 2 rewrite <- nA_freal_add_series.
       fold u v.
       assert (H5 : ∀ k, fd2n nx (i + k + 1) + fd2n y (i + k + 1) = rad - 1). {
         intros k.
         specialize (A_ge_1_add_series_all_true_if _ _ i Hku) as Hu.
         rewrite <- Hnx in Hu.
         destruct Hu as [Hu| [(Hux, Huy)| Hu]].
         -now specialize (Hu k).
         -specialize (normalized_not_999 x) as H.
          exfalso; apply H; clear H; rewrite <- Hnx.
          exists (i + 1); intros l.
          replace (i + 1 + l) with (i + l + 1) by flia.
          apply Hux.
         -destruct Hu as (l & H10 & H11 & Hux & Huy).
          specialize (normalized_not_999 x) as H.
          exfalso; apply H; clear H; rewrite <- Hnx.
          exists (i + k + l + 2); intros q.
          replace (i + k + l + 2 + q) with (i + l + (k + q) + 2) by flia.
          apply Hux.
       }
       rename H5 into Hu.
       destruct (lt_dec (nA i n u) (rad ^ s)) as [H8| H8].
     +++rewrite Nat.div_small; [ | easy ].
        rewrite Nat.div_small in H3; [ | easy ].
        rewrite Nat.add_0_r in H3.
        destruct (lt_dec (nA i n1 u) (rad ^ s1)) as [H9| H9].
      ***destruct (lt_dec (nA i n1 v) (rad ^ s1)) as [H10| H10].
      ----now rewrite Nat.div_small.
      ----exfalso.
(*
  Hp : nA i n1 v < (rad ^ S p - 1) * rad ^ (n1 - i - p - 2)
i.e
  nA i n1 v < 999...999000...000
     with (p+1) 9s and (n1 - i - p - 2) 0s
*)
         unfold v in Hp.
         rewrite nA_freal_add_series in Hp.
         rewrite Nat_mod_less_small in Hp.
      ++++idtac.
... admit.
++++split.
 ****unfold v in H10.
     rewrite nA_freal_add_series in H10.
     flia H10.
 ****rewrite <- nA_freal_add_series.
     fold v.
     specialize (nA_upper_bound_for_add v i n1) as H11.
     rewrite <- Hs1 in H11.
...  admit.
***idtac.
...
         rewrite Nat.mod_small in Hp; [ | easy ].
         move Hp at bottom.
         replace (rad - 1) with (rad ^ 1 - 1) in H10 by (simpl; flia).
         rewrite Nat_pow_sub_1_mul_pow in H10.
         replace (1 + (n - i - 2)) with (n - i - 1) in H10 by flia His.
         rewrite <- Hs in H10.
         rewrite Nat_pow_sub_1_mul_pow in Hp.
         replace (S p + (n1 - i - p - 2)) with (n1 - i - 1) in Hp.
         Focus 2.
      ----rewrite Hn1.
          destruct rad; [ easy | simpl; flia ].
      ----rewrite <- Hs1 in Hp.
...

Theorem freal_add_assoc {r : radix} : ∀ x y z,
  (x + (y + z) = (x + y) + z)%F.
Proof.
intros.
apply -> freal_eq_prop_eq.
specialize (freal_add_comm (x + y)%F z) as H.
apply freal_eq_prop_eq in H.
rewrite H; clear H.
specialize (freal_add_comm x y) as H.
apply freal_eq_prop_eq in H.
rewrite H; clear H.
(**)
unfold freal_add.

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
unfold numbers_to_digits.
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
 remember (rad * (j + 3)) as n eqn:Hn.
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
unfold freal_add_series at 1 3.
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
unfold numbers_to_digits.
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
replace (j + (n - j - 2) + 3) with (n + 1) in H5 by flia Hjn.
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
  unfold freal_add_series, sequence_add.
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
      unfold numbers_to_digits.
      unfold freal_add_series in Hyz, Hyx.
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
unfold freal_add_series in H6.
rewrite <- Hyx in H6.
unfold d2n, numbers_to_digits in H6.
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
unfold freal_add_series in H.
rewrite <- Hyx in H.
unfold numbers_to_digits, d2n in H.
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
