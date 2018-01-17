(* Real between 0 and 1, i.e. fractional part of a real.
   Implemented as function of type nat → nat.
   Operations + and * implemented using LPO. *)

Require Import Utf8 Arith Psatz.
Require Import Misc Summation(*Xnat*).

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
destruct r as (rad, radi); simpl; lia.
Qed.

Theorem radix_ge_1 {r : radix} : 1 ≤ rad.
Proof.
destruct r as (rad, radi); simpl; lia.
Qed.

Theorem radix_gt_1 {r : radix} : 1 < rad.
Proof.
destruct r as (rad, radi); simpl; lia.
Qed.

Theorem radix_ne_0 {r : radix} : rad ≠ 0.
Proof.
destruct r as (rad, radi); simpl; lia.
Qed.

Hint Resolve radix_gt_0 radix_ge_1 radix_gt_1 radix_ne_0 radix_ge_2.

(* Digit *)

Record digit {r : radix} := mkdig { dig : nat; digit_lt_radix : dig < rad }.

Hint Resolve digit_lt_radix.

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

Check digit_lt_radix.

Theorem digit_le_pred_radix {r : radix} : ∀ d, dig d ≤ rad - 1.
Proof.
intros.
specialize (digit_lt_radix d); lia.
Qed.

Definition d2n {r : radix} u (i : nat) := dig (u i).

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

Definition freal_normalized_eq {r : radix} x y :=
  match LPO_fst (has_same_digits x y) with
  | inl _ => true
  | inr _ => false
  end.

Definition freal_normalized_lt {r : radix} x y :=
  match LPO_fst (has_same_digits x y) with
  | inl _ => true
  | inr (exist _ i _) =>
      if lt_dec (fd2n x i) (fd2n y i) then true else false
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
   (∀ i, k ≤ i → fd2n x i = 0) ∧
   (∀ i, k ≤ i → fd2n y i = rad - 1).

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
   ++simpl in Hxy; unfold d2n in Hxy; rewrite H in Hxy; lia.
   ++simpl in Hxy; unfold d2n in Hsxk.
     rewrite H, <- Hxy in Hsxk.
     now specialize radix_ge_2.
  --destruct Hxk as (i & Hij & Hi).
    exists (k + i + 1).
    split; [ lia | ].
    unfold is_9_strict_after in Hi.
    destruct (Nat.eq_dec (d2n (freal x) (k + i + 1)) (rad - 1)) as [H| H].
   ++easy.
   ++unfold d2n in H; unfold fd2n.
     specialize (digit_lt_radix (freal x (k + i + 1))) as Hr.
     lia.
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
       assert (Hxk : ∀ i, 1 ≤ i → fd2n x i = rad - 1).
     ***intros i Hki; specialize (Hx0 (i - 1)) as H.
        unfold is_9_strict_after in H; unfold fd2n.
        simpl in H; rewrite Nat.sub_add in H; [ | easy ].
        now destruct (Nat.eq_dec (d2n (freal x) i) (rad - 1)).
     ***split; [ | easy ].
        intros i Hi.
        destruct i; [ easy | ].
        specialize (Hxy (S i)) as Hxy2.
        unfold freal_normalize, digit_sequence_normalize in Hxy2.
        simpl in Hxy2.
        destruct (LPO_fst (is_9_strict_after (freal x) (S i))) as [Hx1| Hx1].
     ----destruct (lt_dec (S (d2n (freal x) (S i))) rad) as [Hsx1| Hsx1].
      ++++specialize (Hx0 i).
          unfold is_9_strict_after, d2n in Hx0; unfold d2n in Hsx1.
          simpl in Hx0; rewrite Nat.add_1_r in Hx0.
          destruct (Nat.eq_dec (dig (freal x (S i))) (rad - 1)); [ | easy ].
          clear Hxy2; lia.
      ++++now apply digit_eq_eq in Hxy2; simpl in Hxy2.
     ----destruct Hx1 as (j & Hjj & Hj).
         unfold is_9_strict_after in Hj; unfold d2n in Hj.
         destruct (Nat.eq_dec (dig (freal x (S i + j + 1))) (rad - 1)).
      ++++easy.
      ++++assert (Hksi : 1 ≤ S i + j + 1) by lia.
          specialize (Hxk _ Hksi).
          unfold fd2n in Hxk; lia.
    +++exists 0.
       split; [ now intros | ].
       split; [ now left | ].
       assert (Hxk : ∀ i, 0 ≤ i → fd2n x i = rad - 1).
     ***intros i Hki.
        destruct i.
     ----unfold d2n in Hsx0; unfold fd2n.
         specialize (digit_lt_radix (freal x 0)) as H; lia.
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
        intros i Hi.
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
           clear Hxy; lia.
       ****now apply digit_eq_eq in Hxy.
      ++++destruct Hx1 as (j & Hjj & Hj).
          specialize (Hx0 (S (i + j))).
          apply is_9_strict_after_true_iff in Hx0; simpl in Hx0.
          apply is_9_strict_after_false_iff in Hj; simpl in Hj.
          easy.
   ---now rewrite Hxy1 in Hxy0.
  --exists (S k).
    assert (Hkxy : ∀ i, i < k → freal y i = freal x i).
   ++intros i Hik.
     specialize (Hjk _ Hik).
     unfold has_same_digits in Hjk.
     destruct (Nat.eq_dec (fd2n x i) (fd2n y i)) as [H| ]; [ | easy ].
     clear Hjk; unfold fd2n in H.
     now symmetry; apply digit_eq_eq.
   ++split; [ now simpl; rewrite Nat.sub_0_r | ].
     specialize (Hxy k) as Hk.
     apply digit_eq_eq in Hk.
     unfold freal_normalize in Hk; simpl in Hk.
     unfold digit_sequence_normalize in Hk.
     destruct (LPO_fst (is_9_strict_after (freal x) k)) as [H| Hxk].
    **assert (Hxk : ∀ i, S k ≤ i → fd2n x i = rad - 1).
    ---intros i Hki; specialize (H (i - k - 1)).
       apply is_9_strict_after_true_iff in H.
       now replace (k + (i - k - 1) + 1) with i in H by lia.
    ---rewrite <- and_assoc, and_comm.
       split; [ easy | clear H ].
       simpl; rewrite Nat.sub_0_r.
       destruct (lt_dec (S (d2n (freal x) k))) as [Hsxk| Hsxk].
     +++simpl in Hk.
        split; [ now right | ].
        intros i Hki.
        destruct i; [ easy | ].
        specialize (Hxy (S i)) as Hxy1.
        unfold freal_normalize, digit_sequence_normalize in Hxy1.
        simpl in Hxy1.
        destruct (LPO_fst (is_9_strict_after (freal x) (S i))) as [Hx1| Hx1].
      ***destruct (lt_dec (S (d2n (freal x) (S i))) rad) as [Hsx1| Hsx1].
      ----specialize (Hxk (S i) Hki); clear Hxy1.
          unfold fd2n in Hxk; unfold d2n in Hsx1; lia.
      ----now apply digit_eq_eq in Hxy1.
      ***destruct Hx1 as (j & Hjj & Hj).
         apply is_9_strict_after_false_iff in Hj.
         assert (Hksi : k < S (S (i + j))) by lia.
         specialize (Hxk (S (S (i + j))) Hksi).
         unfold fd2n in Hxk; unfold d2n in Hj.
         replace (S i + j + 1) with (S (S (i + j))) in Hj; lia.
     +++simpl in Hk; unfold fd2n; symmetry in Hk; rewrite Hk.
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
      ***specialize (Hjk _ (Nat.lt_succ_diag_r k)).
         unfold has_same_digits in Hjk.
         destruct (Nat.eq_dec (fd2n x k) (fd2n y k)) as [H| H]; [ | easy ].
         apply digit_eq_eq in Hk'; unfold fd2n in H.
         destruct (lt_dec (S (d2n (freal x) k)) rad) as [Hsxk'| Hsxk'].
      ----simpl in Hk'; unfold d2n in Hk'; lia.
      ----simpl in Hk'; unfold d2n in Hsxk'.
          specialize radix_ge_2 as Hr; lia.
      ***destruct Hxk' as (i & Hji & Hi).
         apply is_9_strict_after_false_iff in Hi.
         unfold d2n in Hi.
         destruct i.
      ----rewrite Nat.add_0_r, Nat.add_1_r in Hi; lia.
      ----assert (H : S (S k) ≤ (k + S i + 1)) by lia.
          specialize (Hxk _ H); unfold fd2n in Hxk; lia.
    **exfalso.
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
   replace (i + (j - i - 1) + 1) with j in Hxi; lia.
  *apply Hxy.
 +unfold freal_norm_not_norm_eq in Hxy.
  destruct Hxy as (k & Hik & Hxy & Hx & Hy).
  unfold freal_normalize, digit_sequence_normalize; simpl.
  destruct (LPO_fst (is_9_strict_after (freal x) i)) as [Hxi| Hxi].
  *destruct (lt_dec (S (d2n (freal x) i)) rad) as [Hsxi| Hsxi].
  --apply digit_eq_eq; simpl.
    destruct (le_dec k i) as [Hki| Hki].
   ++specialize (Hy _ Hki).
     unfold fd2n in Hy; unfold d2n in Hsxi; lia.
   ++apply Nat.nle_gt in Hki.
     destruct Hxy as [Hxy| Hxy]; [ lia | ].
     destruct (Nat.eq_dec i (k - 1)) as [Hik1| Hik1]; [ now subst i | ].
     specialize (Hxi (k - i - 2)).
     apply is_9_strict_after_true_iff in Hxi.
     replace (i + (k - i - 2) + 1) with (k - 1) in Hxi by lia.
     unfold fd2n in Hxy; unfold d2n in Hxi.
     specialize (digit_lt_radix (freal y (k - 1))) as H; lia.
  --apply digit_eq_eq; simpl; symmetry.
    apply Nat.nlt_ge in Hsxi.
    destruct k.
   **now specialize (Hx _ (Nat.le_0_l i)).
   **destruct Hxy as [Hxy| Hxy]; [ easy | ].
     simpl in Hik, Hxy; rewrite Nat.sub_0_r in Hik, Hxy.
     destruct (lt_eq_lt_dec i k) as [[Hki| Hki]| Hki].
   ---specialize (Hxi (k - i - 1)).
      apply is_9_strict_after_true_iff in Hxi; unfold d2n in Hxi.
      replace (i + (k - i - 1) + 1) with k in Hxi by lia.
      unfold fd2n in Hxy.
      specialize (digit_lt_radix (freal y k)) as H1; lia.
   ---subst i.
      unfold fd2n in Hxy; unfold d2n in Hsxi.
      specialize (digit_lt_radix (freal y k)) as H1; lia.
   ---now specialize (Hx _ Hki).
  *destruct Hxi as (j & Hjj & Hj).
   apply is_9_strict_after_false_iff in Hj; unfold d2n in Hj.
   destruct k.
  --specialize (Hy (i + j + 1) (Nat.le_0_l _)).
    unfold fd2n in Hy; lia.
  --destruct Hxy as [| Hxy]; [ easy | ].
    simpl in Hik, Hxy; rewrite Nat.sub_0_r in Hik, Hxy.
    destruct (lt_dec i k) as [Hki| Hki].
   **now symmetry; apply Hik.
   **assert (H : S k ≤ i + j + 1) by lia.
     specialize (Hy _ H).
     unfold fd2n in Hy; lia.
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
 assert (H : k ≤ S (max i k)) by lia.
 specialize (Hax (S (max i k)) H).
 unfold fd2n in Hax.
 apply is_9_strict_after_true_iff in H1.
 unfold d2n in H1.
 replace (i + (max i k - i) + 1) with (S (max i k)) in H1 by lia.
 rewrite Hax in H1.
 specialize radix_ge_2; lia.
-destruct (LPO_fst (is_9_strict_after (freal y) i)) as [H2| H2].
 +destruct (lt_eq_lt_dec i (k - 1)) as [[H4| H4]| H4].
  *destruct k; [ easy | ].
   specialize (H2 (k - i - 1)).
   apply is_9_strict_after_true_iff in H2.
   unfold d2n in H2.
   replace (i + (k - i - 1) + 1) with k in H2 by lia.
   simpl in Hw; rewrite Nat.sub_0_r in Hw.
   unfold fd2n in Hw.
   specialize (digit_lt_radix (freal x k)) as H6; lia.
  *subst i.
   destruct k.
  --clear Hb Hw; simpl in H2; simpl.
    destruct (lt_dec (S (d2n (freal y) 0))) as [H3| H3].
   ++exfalso; unfold fd2n in Hay; unfold d2n in H3.
     rewrite Hay in H3; [ lia | easy ].
   ++apply digit_eq_eq; simpl.
     now unfold fd2n in Hax; rewrite Hax.
  --destruct Hw as [| Hw]; [ easy | ].
    simpl in Hw; rewrite Nat.sub_0_r in Hw.
    simpl; rewrite Nat.sub_0_r.
    destruct (lt_dec (S (d2n (freal y) k)) rad) as [H3| H3].
   ++now apply digit_eq_eq; simpl.
   ++unfold fd2n in Hw; unfold d2n in H3.
     specialize (digit_lt_radix (freal x k)); lia.
  *destruct (lt_dec (S (d2n (freal y) i)) rad) as [H3| H3].
  --unfold fd2n in Hay; unfold d2n in H3.
    exfalso; rewrite Hay in H3; lia.
  --apply digit_eq_eq; simpl.
    unfold fd2n in Hax.
    rewrite Hax; [ easy | lia ].
 +destruct (lt_eq_lt_dec i (k - 1)) as [[H4| H4]| H4].
  *now rewrite Hb.
  *subst i.
   destruct H2 as (j & Hjj & Hj).
   apply is_9_strict_after_false_iff in Hj.
   unfold d2n in Hj; unfold fd2n in Hay.
   assert (H : k ≤ k - 1 + j + 1) by lia.
   specialize (Hay _ H).
   rewrite Hay in Hj; lia.
  *destruct H2 as (j & Hjj & Hj).
   apply is_9_strict_after_false_iff in Hj.
   unfold d2n in Hj; unfold fd2n in Hay.
   assert (H : k ≤ i + j + 1) by lia.
   specialize (Hay _ H).
   rewrite Hay in Hj; lia.
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
    rewrite Hakxz in Hky; [ easy | lia ].
  --subst ky.
    destruct kx.
   ++apply digit_eq_eq; unfold fd2n in Hakx, Haky.
     rewrite Hakx; [ | lia ].
     rewrite Haky; [ easy | lia ].
   ++destruct Hkx as [| Hkx]; [ easy | ].
     destruct Hky as [| Hky]; [ easy | ].
     simpl in Hbkx, Hkx, Hky, Hbky.
     rewrite Nat.sub_0_r in Hbkx, Hkx, Hky, Hbky.
     destruct (lt_eq_lt_dec i kx) as [[Hikx| Hikx]| Hikx].
    **now rewrite <- Hbkx; [ rewrite <- Hbky | ].
    **apply digit_eq_eq; unfold fd2n in Hkx, Hky; subst i.
      now apply Nat.succ_inj; rewrite <- Hkx, <- Hky.
    **apply digit_eq_eq; unfold fd2n in Hakx, Haky.
      now rewrite Hakx; [ rewrite Haky | ].
  --destruct kx; [ easy | ].
    destruct Hkx as [| Hkx]; [ easy | ].
    simpl in Hbkx, Hkx; rewrite Nat.sub_0_r in Hbkx, Hkx.
    rewrite Hakyz in Hkx; [ easy | lia ].
-destruct Hxy as [Hxy| [Hxy| Hxy]].
 +now apply freal_eq_normalize_eq.
 +now apply freal_norm_not_norm_eq_normalize_eq.
 +now intros; symmetry; apply freal_norm_not_norm_eq_normalize_eq.
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

Definition nB {r : radix} (rg := nat_ord_ring) n l u :=
  Σ (j = n, n + l), u j * rad ^ (n + l - j).

Definition A_plus_B_ge_1 {r : radix} i u l :=
  let n := rad * (i + 2) in
  let s := rad ^ (n - 1 - i) in
  if lt_dec (nA i n u mod s * rad ^ (l + 1) + nB n l u) (rad ^ (n + l - i))
  then false else true.

Definition numbers_to_digits {r : radix} u i :=
  match LPO_fst (A_plus_B_ge_1 i u) with
  | inl _ =>
      let n := rad * (i + 2) in
      let s := rad ^ (n - 1 - i) in
      let d := u i + nA i n u / s in
      mkdig _ ((d + 1) mod rad) (Nat.mod_upper_bound (d + 1) rad radix_ne_0)
  | inr (exist _ l _) =>
      let n := rad * (i + l + 2) in
      let s := rad ^ (n - 1 - i) in
      let d := u i + nA i n u / s in
      mkdig _ (d mod rad) (Nat.mod_upper_bound d rad radix_ne_0)
  end.

Definition freal_add_to_seq {r : radix} (a b : FracReal) :=
  numbers_to_digits (freal_add_series a b).

Arguments freal_add_to_seq _ a%F b%F.

Definition freal_mul_to_seq {r : radix} (a b : FracReal) :=
  numbers_to_digits (freal_mul_series a b).

Definition freal_add {r : radix} (a b : FracReal) :=
  {| freal := freal_add_to_seq (freal_normalize a) (freal_normalize b) |}.

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

Theorem nB_freal_add_series_comm {r : radix} : ∀ x y n k,
  nB n k (freal_add_series x y) = nB n k (freal_add_series y x).
Proof.
intros.
unfold nB; simpl.
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

Theorem nB_freal_mul_series_comm {r : radix} : ∀ x y n k,
  nB n k (freal_mul_series x y) = nB n k (freal_mul_series y x).
Proof.
intros.
unfold nB; simpl.
apply summation_eq_compat; intros j Hj.
now rewrite freal_mul_series_comm.
Qed.

Theorem A_plus_B_ge_1_freal_add_series_comm {r : radix} : ∀ x y i k,
  A_plus_B_ge_1 i (freal_add_series x y) k =
  A_plus_B_ge_1 i (freal_add_series y x) k.
Proof.
intros.
unfold A_plus_B_ge_1.
now rewrite nA_freal_add_series_comm, nB_freal_add_series_comm.
Qed.

Theorem A_plus_B_ge_1_freal_mul_series_comm {r : radix} : ∀ x y i k,
  A_plus_B_ge_1 i (freal_mul_series x y) k =
  A_plus_B_ge_1 i (freal_mul_series y x) k.
Proof.
intros.
unfold A_plus_B_ge_1.
now rewrite nA_freal_mul_series_comm, nB_freal_mul_series_comm.
Qed.

Theorem freal_add_to_seq_i_comm {r : radix} : ∀ x y i,
  freal_add_to_seq x y i = freal_add_to_seq y x i.
Proof.
intros.
unfold freal_add_to_seq, numbers_to_digits.
remember (freal_add_series x y) as xy.
remember (freal_add_series y x) as yx.
destruct (LPO_fst (A_plus_B_ge_1 i xy)) as [Hxy| Hxy].
-rewrite Heqxy, freal_add_series_comm, <- Heqyx.
 destruct (LPO_fst (A_plus_B_ge_1 i yx)) as [Hyx| Hyx].
 +now rewrite nA_freal_add_series_comm, <- Heqyx.

 +destruct Hyx as (k & Hjk & Hk).
  rewrite Heqyx, A_plus_B_ge_1_freal_add_series_comm, <- Heqxy in Hk.
  now rewrite Hxy in Hk.

-destruct Hxy as (k & Hjk & Hk).
 rewrite Heqxy, A_plus_B_ge_1_freal_add_series_comm, <- Heqyx in Hk.
 destruct (LPO_fst (A_plus_B_ge_1 i yx)) as [Hyx| Hyx].
 +now rewrite Hyx in Hk.

 +destruct Hyx as (l & Hjl & Hl).
  destruct (lt_eq_lt_dec k l) as [ [ Hkl | Hkl ] | Hkl ].
  *apply Hjl in Hkl.
   now rewrite Hk in Hkl.
  *rewrite Heqxy, freal_add_series_comm, <- Heqyx.
   rewrite nA_freal_add_series_comm, <- Heqyx.
   now subst k.
  *apply Hjk in Hkl.
   rewrite Heqxy, A_plus_B_ge_1_freal_add_series_comm in Hkl.
   now rewrite <- Heqyx, Hl in Hkl.
Qed.

Theorem freal_mul_to_seq_i_comm {r : radix} : ∀ x y i,
  freal_mul_to_seq x y i = freal_mul_to_seq y x i.
Proof.
intros.
unfold freal_mul_to_seq, numbers_to_digits.
remember (freal_mul_series x y) as xy.
remember (freal_mul_series y x) as yx.
destruct (LPO_fst (A_plus_B_ge_1 i xy)) as [Hxy| Hxy].
-rewrite Heqxy, freal_mul_series_comm, <- Heqyx.
 destruct (LPO_fst (A_plus_B_ge_1 i yx)) as [Hyx| Hyx].
 +now rewrite nA_freal_mul_series_comm, <- Heqyx.
 +destruct Hyx as (k & Hjk & Hk).
  rewrite Heqyx, A_plus_B_ge_1_freal_mul_series_comm, <- Heqxy in Hk.
  now rewrite Hxy in Hk.
-destruct Hxy as (k & Hjk & Hk).
 rewrite Heqxy, A_plus_B_ge_1_freal_mul_series_comm, <- Heqyx in Hk.
 destruct (LPO_fst (A_plus_B_ge_1 i yx)) as [Hyx| Hyx].
 +now rewrite Hyx in Hk.
 +destruct Hyx as (l & Hjl & Hl).
  destruct (lt_eq_lt_dec k l) as [ [ Hkl | Hkl ] | Hkl ].
  *apply Hjl in Hkl; subst xy.
   now rewrite Hk in Hkl.
  *rewrite Heqxy, freal_mul_series_comm, <- Heqyx.
   rewrite nA_freal_mul_series_comm, <- Heqyx.
   now subst k.
  *apply Hjk in Hkl.
   rewrite Heqxy, A_plus_B_ge_1_freal_mul_series_comm in Hkl.
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
 destruct (LPO_fst (is_9_strict_after yx i)) as [Hyx| Hyx].
  unfold freal_add in Heqxy; simpl in Heqxy.
  unfold freal_add in Heqyx; simpl in Heqyx.
  destruct (lt_dec (S (d2n xy i)) rad) as [Hrxy| Hrxy].
   subst xy; simpl in Hrxy; simpl.
   destruct (lt_dec (S (d2n yx i)) rad) as [Hryx| Hryx].
    unfold freal_add in Heqyx; simpl in Heqyx.
    subst yx; simpl in Hryx; simpl.
    apply digit_eq_eq; unfold d2n; simpl.
    now rewrite freal_add_to_seq_i_comm.

    subst yx; simpl in Hryx.
    unfold d2n in Hryx.
    now rewrite freal_add_to_seq_i_comm in Hryx.

   destruct (lt_dec (S (d2n yx i)) rad) as [Hryx| Hryx]; [ | easy ].
   exfalso.
   subst xy yx; simpl in Hryx; unfold d2n in Hryx.
   now rewrite freal_add_to_seq_i_comm in Hryx.

  destruct Hyx as (k & Hjk & Hk); clear Hjk.
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

 destruct Hxy as (k & Hjk & Hk).
 unfold freal_add in Heqxy; simpl in Heqxy.
 unfold freal_add in Heqyx; simpl in Heqyx.
 destruct (LPO_fst (is_9_strict_after yx i)) as [Hyx| Hyx].
  exfalso; clear Hjk.
  subst xy yx; simpl in Hk, Hyx; unfold d2n in Hk; simpl.
  apply is_9_strict_after_false_iff in Hk.
  unfold d2n in Hk.
  rewrite freal_add_to_seq_i_comm in Hk.
  specialize (Hyx k).
  apply is_9_strict_after_true_iff in Hyx.
  now unfold d2n in Hyx.

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
destruct (LPO_fst (is_9_strict_after xy i)) as [Hxy| Hxy].
 destruct (LPO_fst (is_9_strict_after yx i)) as [Hyx| Hyx].
  unfold freal_mul in Heqxy; simpl in Heqxy.
  unfold freal_mul in Heqyx; simpl in Heqyx.
  destruct (lt_dec (S (d2n xy i)) rad) as [Hrxy| Hrxy].
   subst xy; simpl in Hrxy; simpl.
   destruct (lt_dec (S (d2n yx i)) rad) as [Hryx| Hryx].
    unfold freal_mul in Heqyx; simpl in Heqyx.
    subst yx; simpl in Hryx; unfold d2n; simpl.
    apply digit_eq_eq; simpl.
    now rewrite freal_mul_to_seq_i_comm.

    subst yx; simpl in Hryx; unfold d2n in Hryx.
    now rewrite freal_mul_to_seq_i_comm in Hryx.

   destruct (lt_dec (S (d2n yx i)) rad) as [Hryx| Hryx]; [ | easy ].
   exfalso.
   subst xy yx; simpl in Hryx; unfold d2n in Hryx.
   now rewrite freal_mul_to_seq_i_comm in Hryx.

  destruct Hyx as (k & Hjk & Hk); clear Hjk.
  unfold freal_mul in Heqyx; simpl in Heqyx.
  subst yx; simpl in Hk; simpl; unfold d2n in Hk.
  apply is_9_strict_after_false_iff in Hk.
  unfold d2n in Hk.
  rewrite freal_mul_to_seq_i_comm in Hk.
  unfold freal_mul in Heqxy; simpl in Heqxy.
  subst xy; simpl in Hxy; simpl.
  specialize (Hxy k).
  now apply is_9_strict_after_true_iff in Hxy.

 destruct Hxy as (k & Hjk & Hk).
 unfold freal_mul in Heqxy; simpl in Heqxy.
 unfold freal_mul in Heqyx; simpl in Heqyx.
 destruct (LPO_fst (is_9_strict_after yx i)) as [Hyx| Hyx].
  exfalso; clear Hjk.
  subst xy yx; simpl in Hk, Hyx; simpl; unfold d2n in Hk.
  apply is_9_strict_after_false_iff in Hk.
  unfold d2n in Hk.
  rewrite freal_mul_to_seq_i_comm in Hk.
  specialize (Hyx k).
  now apply is_9_strict_after_true_iff in Hyx.

  subst xy yx; simpl.
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
unfold freal_normalized_eq.
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
unfold freal_normalized_eq.
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

Theorem nB_freal_add_series {r : radix} : ∀ x y n k,
  nB n k (freal_add_series x y) = nB n k (fd2n x) + nB n k (fd2n y).
Proof.
intros.
unfold nB; simpl.
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

Theorem power_summation_sub_1 (rg := nat_ord_ring) : ∀ a n,
  0 < a
  → a ^ S n - 1 = (a - 1) * Σ (i = 0, n), a ^ i.
Proof.
intros * Ha.
rewrite power_summation; [ | easy ].
rewrite Nat.add_comm.
now rewrite Nat.add_sub.
Qed.

Theorem nA_dig_seq_ub {r : radix} : 0 < rad → ∀ u n i,
  (∀ j, i + 1 ≤ j ≤ n - 1 → u j < rad) →
  i + 1 ≤ n - 1
  → nA i n u < rad ^ (n - 1 - i).
Proof.
intros Hr * Hu Hin.
unfold nA.
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
apply Hu; lia.
Qed.

Theorem nB_dig_seq_ub {r : radix} : 0 < rad → ∀ u,
  (∀ i, u i < rad) → ∀ n k, nB n k u < rad ^ S k.
Proof.
intros Hr u Hu n k.
unfold nB.
rewrite summation_rtl.
rewrite summation_shift; [ | lia ].
rewrite Nat.add_comm, Nat.add_sub.
rewrite power_summation; [ | easy ].
unfold lt; simpl.
apply -> Nat.succ_le_mono.
rewrite summation_mul_distr_l.
apply (@summation_le_compat _ nat_ord_ring).
intros j Hj.
replace (k + n + n - (n + j)) with (k + n - j) by lia.
replace (k + n - (k + n - j)) with j by lia.
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

Theorem numbers_to_digits_id {r : radix} : ∀ u (Hur : ∀ j, u j < rad) i,
  numbers_to_digits u i = mkdig _ (u i) (Hur i).
Proof.
intros.
unfold numbers_to_digits.
destruct (LPO_fst (A_plus_B_ge_1 i u)) as [H| H].
-specialize (H 0) as HH.
 unfold A_plus_B_ge_1 in HH; simpl in HH.
 rewrite Nat.mul_1_r, Nat.add_0_r in HH.
 remember (rad * (i + 2)) as n eqn:Hn.
 remember (rad ^ (n - 1 - i)) as s eqn:Hs.
 destruct (lt_dec (nA i n u mod s * rad + nB n 0 u) (rad ^ (n - i)))
   as [| Hge]; [ easy | clear HH ].
 assert (Hin : i + 1 ≤ n - 1).
 +subst n; specialize radix_ge_2 as Hr.
  destruct rad as [| rd]; [ easy | simpl; lia ].
 +assert (Hir : ∀ j, i + 1 ≤ j ≤ n - 1 → u j < rad) by (intros; apply Hur).
  specialize radix_gt_0 as Hr.
  specialize (nA_dig_seq_ub Hr u n i Hir Hin) as HnA; clear Hir.
  rewrite <- Hs in HnA.
  rewrite Nat.mod_small in Hge; [ | easy ].
  exfalso; apply Hge; clear Hge.
  unfold nA, nB.
  rewrite summation_mul_distr_r; simpl.
  rewrite summation_eq_compat with (h := λ j, u j * rad ^ (n + 0 - j)).
  *set (rd := nat_ord_ring_def).
   set (rg := nat_ord_ring).
   replace (summation n) with (summation (S (n - 1))) by (f_equal; lia).
   rewrite <- summation_ub_add with (k₂ := 1); [ | lia | lia ].
   rewrite summation_shift; [ | lia ].
   apply le_lt_trans with
     (m := Σ (j = 0, n - (i + 1)), (rad - 1) * rad ^ (n - (i + 1 + j))).
  --rewrite Nat.add_0_r.
    apply (@summation_le_compat rd).
    intros j Hj; simpl.
    unfold NPeano.Nat.le.
    apply Nat.mul_le_mono_nonneg_r; [ lia | ].
    apply Nat.le_add_le_sub_r.
    rewrite Nat.add_1_r.
    apply Hur.
  --rewrite summation_rtl.
    rewrite <- summation_mul_distr_l; simpl.
    rewrite summation_eq_compat with (h := λ j, rad ^ j).
   ++apply Nat.add_lt_mono_l with (p := 1).
     rewrite <- power_summation; [ | easy ].
     replace (S (n - (i + 1))) with (n - i); lia.
   ++intros j Hj; f_equal; lia.
  *intros j Hj.
   rewrite <- Nat.mul_assoc; f_equal.
   remember (rad ^ (n - 1 - j)) as a.
   replace (a * rad) with (a * rad ^ 1) by now rewrite Nat.pow_1_r.
   subst a; rewrite <- Nat.pow_add_r; f_equal; lia.
-destruct H as (l & Hjk & Hts).
 unfold A_plus_B_ge_1 in Hts.
 remember (rad * (i + 2)) as n eqn:Hn.
 remember (rad ^ (n - 1 - i)) as s eqn:Hs.
 destruct
   (lt_dec (nA i n u mod s * rad ^ (l + 1) + nB n l u)
      (rad ^ (n + l - i)))
   as [Hlt| ]; [ clear Hts | easy ].
 apply digit_eq_eq; simpl.
 rewrite Nat.div_small.
 +rewrite Nat.mod_small; [ lia | ].
  rewrite Nat.add_0_r; apply Hur.
 +apply nA_dig_seq_ub; [ easy | easy | ].
  destruct rad; [ | simpl; lia ].
  now specialize (Hur 0).
Qed.

Theorem dig_numbers_to_digits_id {r : radix} : ∀ u i,
  (∀ j : nat, u j < rad)
  → dig (numbers_to_digits u i) = u i.
Proof.
intros * Hur.
specialize (numbers_to_digits_id u Hur i) as H.
now apply digit_eq_eq in H.
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
 destruct rr; [ lia | easy ].
-easy.
Qed.

Theorem normalized_999 {r : radix} : ∀ x,
  (∀ i, fd2n x i = rad - 1) → (∀ i, fd2n (freal_normalize x) i = 0).
Proof.
intros * Hx *.
unfold freal_normalize; simpl.
unfold digit_sequence_normalize.
unfold fd2n; simpl.
destruct (LPO_fst (is_9_strict_after (freal x) i)) as [Hxi| Hxi].
-destruct (lt_dec (S (d2n (freal x) i)) rad) as [Hsx| Hsx]; [ | easy ].
 exfalso.
 unfold fd2n in Hx; unfold d2n in Hsx.
 rewrite Hx in Hsx.
 rewrite <- Nat.sub_succ_l in Hsx; [ | easy ].
 rewrite Nat.sub_succ, Nat.sub_0_r in Hsx; lia.
-destruct Hxi as (j & Hjj & Hj).
 apply is_9_strict_after_false_iff in Hj.
 unfold fd2n in Hx; unfold d2n in Hj.
 now rewrite Hx in Hj.
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

Theorem freal_add_normalize_0_l {r : radix} : ∀ x i,
  freal_add_to_seq (freal_normalize 0) x i = freal x i.
Proof.
intros.
unfold freal_add_to_seq.
set (u := freal_add_series (freal_normalize 0) x).
unfold numbers_to_digits.
destruct (LPO_fst (A_plus_B_ge_1 i u)) as [Hku| (m & Hjm & Hm)].
-apply digit_eq_eq; simpl.
 +exfalso; specialize (Hku 0).
  unfold A_plus_B_ge_1 in Hku.
  set (n := rad * (i + 2)) in Hku.
  set (s := rad ^ (n - 1 - i)) in Hku.
  simpl in Hku.
  rewrite Nat.mul_1_r, Nat.add_0_r in Hku.
  destruct (lt_dec (nA i n u mod s * rad + nB n 0 u) (rad ^ (n - i)))
    as [Hnk| Hnk]; [ easy | clear Hku ].
  apply Hnk; clear Hnk.
  apply Nat.le_lt_trans with (m := (s - 1) * rad + nB n 0 u).
  *apply Nat.add_le_mono_r, Nat.mul_le_mono_pos_r; [ easy | ].
   apply Nat.le_add_le_sub_r.
   rewrite Nat.add_1_r.
   apply Nat.mod_upper_bound.
   now unfold s; apply Nat.pow_nonzero.
  *unfold nB; rewrite Nat.add_0_r.
   rewrite summation_only_one, Nat.sub_diag, Nat.pow_0_r, Nat.mul_1_r.
   unfold u, freal_add_series, sequence_add, fd2n.
   rewrite freal_normalize_0, Nat.add_0_l.
   apply Nat.le_lt_trans with (m := (s - 1) * rad + (rad - 1)).
  --apply Nat.add_le_mono_l.
    apply digit_le_pred_radix.
  --rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
    replace rad with (rad ^ 1) at 1 by apply Nat.pow_1_r.
    unfold s.
    rewrite <- Nat.pow_add_r.
    enough (1 ≤ n - i). {
     replace (n - 1 - i + 1) with (n - i) by lia.
     rewrite Nat.add_sub_assoc; [ | easy ].
     rewrite Nat.sub_add.
     -apply Nat.sub_lt; [ | lia ].
      now apply Nat_pow_ge_1.
     -replace rad with (rad ^ 1) at 1 by apply Nat.pow_1_r.
      now apply Nat.pow_le_mono_r.
    }
    unfold n.
    specialize radix_gt_0 as H.
    destruct rad; [ easy | simpl; lia ].
-apply digit_eq_eq; simpl.
 set (n := rad * (i + m + 2)).
 set (s := rad ^ (n - 1 - i)).
 remember (u i) as uk eqn:Huk.
 unfold u, freal_add_series, sequence_add in Huk.
 unfold fd2n in Huk.
 rewrite freal_normalize_0 in Huk.
 simpl in Huk; subst uk.
 rewrite Nat.div_small; [ now rewrite Nat.add_0_r, Nat.mod_small | ].
 unfold nA.
 eapply Nat.le_lt_trans with (m := Σ (j = i + 1, n - 1), (rad - 1) * rad ^ (n - 1 - j)).
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
    replace (S (n - 1 - (i + 1))) with (n - i - 1) by lia.
    rewrite Nat_sub_sub_swap.
    apply Nat.sub_lt; [ | lia ].
    now apply Nat_pow_ge_1.
  --intros p Hp; f_equal; lia.
  *unfold n.
   specialize radix_ne_0 as H.
   destruct rad as [| rr]; [ easy | ].
   simpl; lia.
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
     destruct (LPO_fst (is_9_strict_after (freal x) (j + (k + 1)))) as [H4| H4].
     *destruct (lt_dec (S (d2n (freal x) (j + (k + 1)))) rad) as [H5| H5].
     --simpl in H3; clear H5.
       specialize (H2 0).
       replace (j + k + 0 + 1) with (j + (k + 1)) in H2; lia.
     --simpl in H3.
       specialize radix_ge_2; lia.
     *clear H3.
      destruct H4 as (m & Hjm & H3).
      apply is_9_strict_after_false_iff in H3.
      specialize (H2 (m + 1)).
      replace (j + k + (m + 1) + 1) with (j + (k + 1) + m + 1) in H2; lia.
    +simpl in H1.
     specialize radix_ge_2; lia.
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
   unfold d2n in Hnr; lia.
  *simpl in Hnr.
   specialize radix_ge_2; lia.
 +clear Hnr.
  destruct H1 as (i & Hji & H2).
  apply is_9_strict_after_false_iff in H2.
  specialize (Hr (i + 1)).
  now replace (j + (i + 1)) with (j + i + 1) in Hr by lia.
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
  split; [ lia | ].
  specialize (digit_lt_radix (freal (0 + x) (j + k + m))) as H.
  unfold d2n in Hm; unfold fd2n; lia.
 +intros k.
  unfold freal_add; simpl.
  apply freal_add_normalize_0_l.
Qed.

Theorem freal_add_0_l {r : radix} : ∀ x, (0 + x = x)%F.
Proof.
intros.
unfold freal_eq, freal_normalized_eq.
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
Definition freal_eq_prop {r : radix} x y := freal_eq x y = true.

Theorem freal_eq_refl {r : radix} : reflexive _ freal_eq_prop.
Proof.
intros x.
unfold freal_eq_prop, freal_eq, freal_normalized_eq.
remember (freal_normalize x) as y eqn:Hy.
destruct (LPO_fst (has_same_digits y y)) as [Hs| Hs]; [ easy | exfalso ].
destruct Hs as (i & Hji & Hyy).
now apply has_same_digits_false_iff in Hyy.
Qed.

Theorem freal_eq_sym {r : radix} : symmetric _ freal_eq_prop.
Proof.
intros x y Hxy.
unfold freal_eq_prop, freal_eq, freal_normalized_eq in Hxy |-*.
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

Theorem freal_eq_trans {r : radix} : transitive _ freal_eq_prop.
Proof.
intros x y z Hxy Hyz.
unfold freal_eq_prop, freal_eq, freal_normalized_eq in Hxy, Hyz |-*.
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

Add Parametric Relation {r : radix} : (FracReal) freal_eq_prop
 reflexivity proved by freal_eq_refl
 symmetry proved by freal_eq_sym
 transitivity proved by freal_eq_trans
 as freal_eq_rel.

Theorem freal_eq_prop_eq {r : radix} : ∀ x y,
  freal_eq_prop x y ↔ freal_eq x y = true.
Proof. easy. Qed.

Theorem all_eq_seq_all_eq {r : radix} : ∀ x y,
  (∀ k, has_same_digits x y k = true) → (∀ k, freal x k = freal y k).
Proof.
intros * Hk *.
specialize (Hk k).
apply has_same_digits_true_iff in Hk.
now apply digit_eq_eq.
Qed.

Theorem nA_eq_compat {r : radix} : ∀ i n u v,
  (∀ j, i + 1 ≤ j ≤ n - 1 → u j = v j)
  → nA i n u = nA i n v.
Proof.
intros * Hfg *.
unfold nA.
apply summation_eq_compat.
intros j Hj.
now rewrite Hfg.
Qed.

Theorem nB_eq_compat {r : radix} : ∀ n k u v,
  (∀ i, u i = v i)
  → nB n k u = nB n k v.
Proof.
intros * Hfg *.
unfold nB.
apply summation_eq_compat.
intros j Hj.
now rewrite Hfg.
Qed.

Theorem A_plus_B_ge_1_eq_compat {r : radix} : ∀ i f g,
  (∀ i, f i = g i) → ∀ k, A_plus_B_ge_1 i f k = A_plus_B_ge_1 i g k.
Proof.
intros * Hfg *.
unfold A_plus_B_ge_1.
erewrite nA_eq_compat; [ | easy ].
erewrite nB_eq_compat; [ | easy ].
easy.
Qed.

Theorem A_plus_B_ge_1_false_iff {r : radix} : ∀ i u k,
  let n := rad * (i + 2) in
  let s := rad ^ (n - 1 - i) in
  A_plus_B_ge_1 i u k = false ↔
  nA i n u mod s * rad ^ (k + 1) + nB n k u < rad ^ (n + k - i).
Proof.
intros.
unfold A_plus_B_ge_1.
fold n s.
now destruct
  (lt_dec (nA i n u mod s * rad ^ (k + 1) + nB n k u) (rad ^ (n + k - i))).
Qed.

Theorem A_plus_B_ge_1_true_iff {r : radix} : ∀ i u k,
  let n := rad * (i + 2) in
  let s := rad ^ (n - 1 - i) in
  A_plus_B_ge_1 i u k = true ↔
  ¬ nA i n u mod s * rad ^ (k + 1) + nB n k u < rad ^ (n + k - i).
Proof.
intros.
unfold A_plus_B_ge_1.
fold n s.
now destruct
  (lt_dec (nA i n u mod s * rad ^ (k + 1) + nB n k u) (rad ^ (n + k - i))).
Qed.

Theorem numbers_to_digits_eq_compat {r : radix} : ∀ f g,
  (∀ i, f i = g i) → ∀ i,
  numbers_to_digits f i = numbers_to_digits g i.
Proof.
intros * Hfg *.
unfold numbers_to_digits.
rewrite Hfg.
destruct (LPO_fst (A_plus_B_ge_1 i f)) as [Hf| Hf].
-destruct (LPO_fst (A_plus_B_ge_1 i g)) as [Hg| Hg].
 +f_equal; f_equal.
  unfold nA.
  erewrite summation_eq_compat; [ reflexivity | simpl ].
  intros j Hj.
  now rewrite Hfg.
 +exfalso.
  destruct Hg as (k & Hjk & H).
  specialize (Hf k).
  erewrite A_plus_B_ge_1_eq_compat in Hf; [ | easy ].
  now rewrite H in Hf.
-destruct (LPO_fst (A_plus_B_ge_1 i g)) as [Hg| Hg].
 +exfalso.
  destruct Hf as (k & Hjk & H).
  specialize (Hg k).
  erewrite A_plus_B_ge_1_eq_compat in H; [ | easy ].
  now rewrite H in Hg.
 +destruct Hf as (k & Hjk & Hk).
  destruct Hg as (l & Hjl & Hl).
  destruct (lt_eq_lt_dec k l) as [[Hkl| Hkl]| Hkl].
  *specialize (Hjl _ Hkl).
   erewrite A_plus_B_ge_1_eq_compat in Hk; [ | easy ].
   now rewrite Hjl in Hk.
  *subst l; apply digit_eq_eq; simpl.
   f_equal; f_equal; f_equal.
   now apply nA_eq_compat.
  *specialize (Hjk _ Hkl).
   apply digit_eq_eq; simpl.
   erewrite A_plus_B_ge_1_eq_compat in Hjk; [ | easy ].
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
 rewrite Hpq in Hs; lia.
-remember (p / q) as a.
 remember (S p / q) as a'.
 rewrite <- Nat.add_1_r in Hs at 1.
 rewrite Hp in Hs at 1.
 assert (p mod q + 1 < q). {
  specialize (Nat.mod_upper_bound p q Hq) as H; lia.
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
   apply Nat.div_le_mono; [ easy | lia ].
  *exfalso.
   rewrite <- Hs in H.
   rewrite Nat.mul_comm in H; simpl in H; lia.
 +apply Nat.mul_le_mono; [ easy | ].
  subst a a'.
  apply Nat.div_le_mono; [ easy | lia ].
Qed.

Theorem freal_eq_normalized_eq {r : radix} : ∀ x y,
  (x = y)%F ↔
  (∀ i, freal (freal_normalize x) i = freal (freal_normalize y) i).
Proof.
intros.
unfold freal_eq, freal_normalized_eq.
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
  with signature freal_eq_prop ==> freal_eq_prop ==> freal_eq_prop
  as freal_add_morph.
Proof.
intros x y Hxy x' y' Hxy'.
unfold freal_eq_prop in Hxy, Hxy' |-*.
rewrite freal_eq_normalized_eq in Hxy, Hxy'.
rewrite freal_eq_normalized_eq.
apply freal_normalized_eq_iff; left.
intros i.
unfold freal_add, freal_add_to_seq, freal_add_series, sequence_add; simpl.
apply numbers_to_digits_eq_compat; clear i.
intros i.
unfold fd2n.
now rewrite Hxy, Hxy'.
Qed.

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
apply freal_eq_prop_eq.
unfold freal_eq; simpl.
unfold freal_normalized_eq.
remember (freal_normalize (x + (y + z))) as xz eqn:Hxz.
remember (freal_normalize (z + (y + x))) as zx eqn:Hzx.
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
...

rewrite Hxz, Hzx.
unfold freal_normalize, fd2n; simpl.
unfold digit_sequence_normalize.
remember (freal_normalize x) as nx eqn:Hnx.
remember (freal_normalize z) as nz eqn:Hnz.
remember (freal_normalize (y + z)) as nyz eqn:Hnyz.
remember (freal_normalize (y + x)) as nyx eqn:Hnyx.
remember (freal_add_to_seq nx nyz) as nxnyz eqn:Hnxnyz.
remember (freal_add_to_seq nz nyx) as nznyx eqn:Hnznyx.
move nz before nx.
move nyz before nz.
move nyx before nyz.
move nxnyz before nyx.
move nznyx before nxnyz.
destruct (LPO_fst (is_9_strict_after nxnyz i)) as [H1| H1].
-destruct (LPO_fst (is_9_strict_after nznyx i)) as [H2| H2].
 +destruct (lt_dec (S (d2n nxnyz i)) rad) as [H3| H3].
  *destruct (lt_dec (S (d2n nznyx i)) rad) as [H4| H4].
  --simpl; f_equal.
    subst nxnyz nznyx.
    rewrite Hnx, Hnz, Hnyz, Hnyx.
    unfold d2n.
    unfold freal_add_to_seq.
    f_equal.
    apply numbers_to_digits_eq_compat.
    intros j.
    unfold freal_add_series, sequence_add, fd2n.
    unfold "+"%F; simpl.
    unfold freal_add_to_seq.
    rewrite <- Hnx, <- Hnz.
    remember (freal_normalize y) as ny eqn:Hny.
    move ny before nx; move Hny before Hnx.
    unfold digit_sequence_normalize.
    remember (numbers_to_digits (freal_add_series ny nz)) as ayz eqn:Hayz.
    remember (numbers_to_digits (freal_add_series ny nx)) as ayx eqn:Hayx.
    move ayx before ayz.
    destruct (LPO_fst (is_9_strict_after ayz j)) as [H5| H5].
   ++specialize (is_9_strict_after_all_9 _ _ H5) as H.
     clear H5; rename H into H5.
     destruct (lt_dec (S (d2n ayz j)) rad) as [H6| H6].
    **simpl.
      destruct (LPO_fst (is_9_strict_after ayx j)) as [H7| H7].
    ---specialize (is_9_strict_after_all_9 _ _ H7) as H.
       clear H7; rename H into H7.
     +++destruct (lt_dec (S (d2n ayx j)) rad) as [H8| H8].
      ***simpl.
         do 2 rewrite Nat.add_succ_r; f_equal.
         subst ayz ayx.
         unfold d2n, numbers_to_digits.
         remember (freal_add_series ny nz) as ayz eqn:Hayz.
         remember (freal_add_series ny nx) as ayx eqn:Hayx.
         move ayx before ayz; move Hayx before Hayz.
         move H8 before H6.
         destruct (LPO_fst (A_plus_B_ge_1 j ayz)) as [H9| H9].
      ----destruct (LPO_fst (A_plus_B_ge_1 j ayx)) as [H10| H10].
       ++++simpl.
           destruct (LPO_fst (is_9_strict_after (freal x) j)) as [H11| H11].
        ****specialize (is_9_strict_after_all_9 _ _ H11) as H.
            clear H11; rename H into H11.
...
