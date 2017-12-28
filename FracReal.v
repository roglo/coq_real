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

Theorem radix_ne_0 {r : radix} : rad ≠ 0.
Proof.
destruct r as (rad, radi); simpl; lia.
Qed.

Hint Resolve radix_gt_0 radix_ge_1 radix_ne_0 radix_ge_2.

(* Digit *)

Record digit {r : radix} := mkdig { dig : nat; digit_lt_radix : dig < rad }.

Hint Resolve digit_lt_radix.

Definition digit_0 {r : radix} := mkdig _ 0 radix_gt_0.

(* the proof that x≤y is unique; this is proved in Coq library theorem
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

Definition d2n {r : radix} u (i : nat) := dig (u i).

(* Frac Real *)

Delimit Scope freal_scope with F.

Record FracReal {r : radix} := { freal : nat → digit }.
Arguments freal r _%F.

Definition fd2n {r : radix} u (i : nat) := dig (freal u i).

Definition mark_9 {r : radix} u i j := rad - 1 - d2n u (i + j + 1).

Definition digit_sequence_normalize {r : radix} (u : nat → digit) i :=
  match LPO_fst (mark_9 u i) with
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

Definition eq_freal_seq {r : radix} x y i :=
  if Nat.eq_dec (fd2n x i) (fd2n y i) then 0 else 1.

Definition freal_normalized_eq {r : radix} x y :=
  match LPO_fst (eq_freal_seq x y) with
  | inl _ => true
  | inr _ => false
  end.

Definition freal_normalized_lt {r : radix} x y :=
  match LPO_fst (eq_freal_seq x y) with
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

Theorem mark_9_all_9 {r : radix} : ∀ u i,
  (∀ j, mark_9 u i j = 0) → (∀ k, d2n u (i + k + 1) = rad - 1).
Proof.
intros * Hm9 *.
specialize (Hm9 k); unfold mark_9 in Hm9.
apply Nat.sub_0_le in Hm9.
specialize (digit_lt_radix (u (i + k + 1))) as H.
unfold d2n in Hm9 |-*.
lia.
Qed.

Definition freal_succ_eq {r : radix} x y :=
  ∃ k,
   (∀ i, i < k → freal x i = freal y i) ∧
   (fd2n x k = S (fd2n y k) mod rad) ∧
   (∀ i, k < i → fd2n x i = 0) ∧
   (∀ i, k < i → fd2n y i = rad - 1).

Theorem freal_normalized_iff {r : radix} : ∀ x y,
  (∀ i, freal (freal_normalize x) i = freal y i)
  ↔ (∀ k, ∃ i, k ≤ i ∧ S (fd2n x i) < rad) ∧
     (∀ i, freal x i = freal y i) ∨
     freal_succ_eq y x.
Proof.
intros.
split; intros Hxy.
-destruct (LPO_fst (eq_freal_seq x y)) as [Hxsy| Hxsy].
 +left.
  split.
  *intros k.
   specialize (Hxy k).
   unfold freal_normalize, digit_sequence_normalize in Hxy.
   simpl in Hxy.
   destruct (LPO_fst (mark_9 (freal x) k)) as [Hxk| Hxk].
  --specialize (Hxsy k).
    unfold eq_freal_seq in Hxsy.
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
    unfold mark_9 in Hi; unfold d2n in Hi.
    unfold fd2n; lia.
  *intros k; specialize (Hxsy k).
   unfold eq_freal_seq in Hxsy.
   destruct (Nat.eq_dec (fd2n x k) (fd2n y k)) as [H| ]; [ clear Hxsy | easy ].
   unfold fd2n in H.
   now apply digit_eq_eq.
 +right.
  destruct Hxsy as (k & Hjk & Hxyk).
  unfold freal_succ_eq.
  assert (Hkxy : ∀ i, i < k → freal y i = freal x i).
  *intros i Hik.
   destruct k; [ easy | ].
   specialize (Hjk _ Hik).
   unfold eq_freal_seq in Hjk.
   destruct (Nat.eq_dec (fd2n x i) (fd2n y i)) as [H| ]; [ | easy ].
   clear Hjk; unfold fd2n in H.
   now symmetry; apply digit_eq_eq.
  *exists k.
   split; [ easy | ].
   specialize (Hxy k) as Hk.
   apply digit_eq_eq in Hk.
   unfold freal_normalize in Hk; simpl in Hk.
   unfold digit_sequence_normalize in Hk.
   destruct (LPO_fst (mark_9 (freal x) k)) as [H| Hxk].
  --assert (Hxk : ∀ i, k < i → fd2n x i = rad - 1).
   ++intros i Hki; specialize (H (i - k - 1)).
     apply Nat.sub_0_le in H.
     unfold mark_9, d2n in H; unfold fd2n.
     specialize (digit_lt_radix (freal x i)).
     replace (k + (i - k - 1) + 1) with i in H; lia.
   ++rewrite <- and_assoc, and_comm.
     split; [ easy | clear H ].
     destruct (lt_dec (S (d2n (freal x) k))) as [Hsxk| Hsxk].
    **simpl in Hk.
      rewrite Nat.mod_small; [ | easy ].
      split; [ easy | ].
      intros i Hki.
      destruct i; [ easy | ].
      specialize (Hxy (S i)) as Hxy1.
      unfold freal_normalize, digit_sequence_normalize in Hxy1.
      simpl in Hxy1.
      destruct (LPO_fst (mark_9 (freal x) (S i))) as [Hx1| Hx1].
    ---destruct (lt_dec (S (d2n (freal x) (S i))) rad) as [Hsx1| Hsx1].
     +++specialize (Hxk (S i) Hki); clear Hxy1.
        unfold fd2n in Hxk; unfold d2n in Hsx1; lia.
     +++now apply digit_eq_eq in Hxy1.
    ---destruct Hx1 as (j & Hjj & Hj).
       unfold mark_9 in Hj.
       assert (Hksi : k < S (S (i + j))) by lia.
       specialize (Hxk (S (S (i + j))) Hksi).
       unfold fd2n in Hxk; unfold d2n in Hj.
       replace (S i + j + 1) with (S (S (i + j))) in Hj; lia.
    **simpl in Hk; unfold fd2n; symmetry in Hk; rewrite Hk.
      apply Nat.nlt_ge in Hsxk.
      specialize (digit_lt_radix (freal x k)) as H.
      unfold d2n in Hsxk.
      apply Nat.le_antisymm in Hsxk; [ clear H | easy ].
      rewrite Hsxk.
      split; [ now rewrite Nat.mod_same | ].
      intros i Hki.
      destruct k.
    ---clear Hjk Hkxy.
       specialize (Hxy i) as Hi.
       apply digit_eq_eq in Hi.
       unfold freal_normalize in Hi; simpl in Hi.
       unfold digit_sequence_normalize in Hi.
       destruct (LPO_fst (mark_9 (freal x) i)) as [H| Hxi].
     +++destruct (lt_dec (S (d2n (freal x) i))) as [Hsxi| Hsxi]; [ | easy ].
        destruct i; [ easy | ].
        specialize (Hxk (S i) (Nat.lt_0_succ i)).
        unfold fd2n in Hxk; unfold d2n in Hsxi.
        clear Hi; rewrite Hxk in Hsxi; lia.
     +++destruct Hxi as (j & Hjj & Hj).
        unfold mark_9, d2n in Hj; unfold fd2n in Hxk.
        specialize (Hxk (S (i + j)) (Nat.lt_0_succ _)).
        rewrite Nat.add_1_r in Hj; lia.
    ---exfalso.
       specialize (Hxy k) as Hxy1.
       unfold freal_normalize, digit_sequence_normalize in Hxy1.
       simpl in Hxy1.
       specialize (Hkxy k (Nat.lt_succ_diag_r k)).
       apply digit_eq_eq in Hxy1.
       destruct (LPO_fst (mark_9 (freal x) k)) as [Hx1| Hx1].
     +++destruct (lt_dec (S (d2n (freal x) k)) rad) as [Hsx1| Hsx1].
      ***unfold d2n in Hxy1; simpl in Hxy1.
         rewrite Hkxy in Hxy1; lia.
      ***unfold d2n in Hsx1; simpl in Hxy1.
         rewrite <- Hkxy, <- Hxy1 in Hsx1.
         specialize radix_ge_2 as H; lia.
     +++destruct Hx1 as (j & Hjj & Hj).
        unfold mark_9 in Hj.
        destruct j.
      ***rewrite Nat.add_0_r, Nat.add_1_r in Hj.
         unfold d2n in Hj; lia.
      ***assert (H : S k < S (S (k + j))) by lia.
         specialize (Hxk (S (S (k + j))) H).
         unfold fd2n in Hxk; unfold d2n in Hj.
         replace (k + S j + 1) with (S (S (k + j))) in Hj; lia.
  --unfold eq_freal_seq in Hxyk.
    now destruct (Nat.eq_dec (fd2n x k) (fd2n y k)).
-intros i.
 destruct Hxy as [Hxy | Hxy].
 +destruct Hxy as (Hki, Hxy).
  unfold freal_normalize, digit_sequence_normalize; simpl.
  destruct (LPO_fst (mark_9 (freal x) i)) as [Hxi| Hxi].
  *specialize (Hki (S i)) as (j & H1j & Hj); unfold fd2n in Hj.
   specialize (Hxi (j - i - 1)); unfold mark_9, d2n in Hxi.
   replace (i + (j - i - 1) + 1) with j in Hxi; lia.
  *apply Hxy.
 +unfold freal_succ_eq in Hxy.
  destruct Hxy as (k & Hik & Hxy & Hx & Hy).
  unfold freal_normalize, digit_sequence_normalize; simpl.
  destruct (LPO_fst (mark_9 (freal x) i)) as [Hxi| Hxi].
  *destruct (lt_dec (S (d2n (freal x) i)) rad) as [Hsxi| Hsxi].
  --apply digit_eq_eq; simpl.
    destruct (lt_dec k i) as [Hki| Hki].
   ++specialize (Hy _ Hki).
     unfold fd2n in Hy; unfold d2n in Hsxi; lia.
   ++destruct (Nat.eq_dec k i) as [Hk| Hk].
    **subst i.
      rewrite Nat.mod_small in Hxy; [ | easy ].
      now unfold fd2n in Hxy; unfold d2n.
    **apply nat_total_order in Hk.
    ---destruct Hk as [Hk| Hk]; [ easy | ].
       specialize (Hxi (k - i - 1)).
       unfold mark_9 in Hxi.
       replace (i + (k - i - 1) + 1) with k in Hxi by lia.
       unfold d2n in Hxi; unfold fd2n in Hxy.
...
       rewrite Nat.mod_small in Hxy; [ | ].

...

   0     i     k
x        . 9 9 9 9 9 9 9 9 9 ...
   = = = = = = -1
y          9 9 0 0 0 0 0 0 0 ...
...

Theorem freal_normalized_eq_iff {r : radix} : ∀ x y,
  (∀ i, freal (freal_normalize x) i = freal (freal_normalize y) i)
  ↔ (∀ i, freal x i = freal y i) ∨ freal_succ_eq x y ∨ freal_succ_eq y x.
Proof.
intros.
split; intros Hxy.
-destruct (LPO_fst (eq_freal_seq x y)) as [Hxsy| Hxsy].
 +left.
  intros k; specialize (Hxsy k).
  unfold eq_freal_seq in Hxsy.
  destruct (Nat.eq_dec (fd2n x k) (fd2n y k)) as [H| ]; [ clear Hxsy | easy ].
  unfold fd2n in H.
  now apply digit_eq_eq.
 +right.
  destruct Hxsy as (k & Hjk & H).
  unfold eq_freal_seq in H.
  destruct (Nat.eq_dec (fd2n x k) (fd2n y k)) as [| Hne]; [ easy | clear H ].
  apply nat_total_order in Hne.
  destruct Hne as [Hlt| Hgt].
  *right.
   unfold freal_succ_eq.
   exists k.
   assert (Hkxy : ∀ i, i < k → freal y i = freal x i).
  --intros i Hik.
    specialize (Hjk _ Hik).
    unfold eq_freal_seq in Hjk.
    destruct (Nat.eq_dec (fd2n x i) (fd2n y i)) as [H| ]; [ | easy ].
    clear Hjk; unfold fd2n in H.
    now symmetry; apply digit_eq_eq.
  --split; [ easy | clear Hjk ].
    specialize (Hxy k) as Hk.
    apply digit_eq_eq in Hk.
    unfold freal_normalize in Hk; simpl in Hk.
    unfold digit_sequence_normalize in Hk.
    destruct (LPO_fst (mark_9 (freal x) k)) as [H| Hxk].
   ++assert (Hxk : ∀ i, k < i → fd2n x i = rad - 1).
    **intros i Hki; specialize (H (i - k - 1)).
      apply Nat.sub_0_le in H.
      unfold mark_9, d2n in H; unfold fd2n.
      specialize (digit_lt_radix (freal x i)).
      replace (k + (i - k - 1) + 1) with i in H; lia.
    **rewrite <- and_assoc, and_comm; split; [ easy | clear H ].
destruct (lt_dec (S (d2n (freal x) k)) rad) as [H1| H1].
Focus 2.
unfold fd2n in Hlt; unfold d2n in H1.
specialize (digit_lt_radix (freal y k)); lia.
simpl in Hk.
aaa.
      move Hxk before Hkxy; unfold fd2n in Hxk.
      destruct (LPO_fst (mark_9 (freal y) k)) as [Hyk| Hyk].
    ---specialize (mark_9_all_9 _ _ Hyk) as H.
       clear Hyk; rename H into Hyk; move Hyk after Hk.
       simpl in Hyk.
       destruct (lt_dec (S (d2n (freal x) k)) rad) as [H1| H1].
     +++destruct (lt_dec (S (d2n (freal y) k)) rad) as [H2| H2]; [ | easy ].
        simpl in Hk.
        apply Nat.succ_inj in Hk.
        unfold d2n in Hk; unfold fd2n in Hlt; lia.
     +++unfold d2n in H1; unfold fd2n in Hlt.
        specialize (digit_lt_radix (freal y k)); lia.
    ---destruct (lt_dec (S (d2n (freal x) k)) rad) as [H2| H2].
     +++split; [ easy | simpl in Hk ].
intros i Hki.
clear Hlt.
destruct i; [ easy | ].
specialize (Hxy i) as Hi.
unfold freal_normalize in Hi.
unfold digit_sequence_normalize in Hi; simpl in Hi.
destruct (LPO_fst (mark_9 (freal x) i)).
destruct (LPO_fst (mark_9 (freal y) i)).
destruct Hyk.
destruct a.
bbb.

     +++admit. (* special case here: definitions to be changed *)
     +++specialize (Hxy k) as Hk1.
        unfold freal_normalize in Hk1; simpl in Hk1.
        unfold digit_sequence_normalize in Hk1.
        destruct (LPO_fst (mark_9 (freal x) k)) as [H1| H1].
      ***specialize (H1 0).
         unfold mark_9, d2n in H1.
         rewrite Nat.add_0_r, Nat.add_1_r in H1.
         unfold fd2n in Hlt.
         specialize (digit_lt_radix (freal y (S k))); lia.
      ***destruct H1 as (j & Hjj & Hj).
         destruct (lt_dec (S (d2n (freal x) (S k))) rad) as [H1| H1].
      ----simpl in Hk.
          destruct (lt_dec (S (d2n (freal y) (S k))) rad) as [H2| H2].
       ++++simpl in Hk.
           unfold d2n in Hk; unfold fd2n in Hlt; lia.
       ++++easy.
      ----unfold d2n in H1; unfold fd2n in Hlt.
          specialize (digit_lt_radix (freal y (S k))); lia.
    ---destruct (lt_dec (S (d2n (freal x) k)) rad) as [H1| H1].
     +++simpl in Hk.
        split; [ unfold fd2n; easy | ].
        intros i Hki.
        destruct k; [ admit | ].
        specialize (Hxy k) as Hk1.
        unfold freal_normalize in Hk1; simpl in Hk1.
        unfold digit_sequence_normalize in Hk1.
        destruct (LPO_fst (mark_9 (freal x) k)) as [H2| H2].
      ***specialize (H2 0).
         unfold mark_9, d2n in H2.
         rewrite Nat.add_0_r, Nat.add_1_r in H2.
         unfold fd2n in Hlt.
         specialize (digit_lt_radix (freal y (S k))); lia.
      ***destruct (LPO_fst (mark_9 (freal y) k)) as [H3| H3].
      ----destruct Hyk as (j & Hjj & Hj).
          specialize (H3 (S j)).
          unfold mark_9, d2n in Hj, H3.
          now replace (S k + j) with (k + S j) in Hj by lia.
      ----clear Hk1.

...


   split; [ | split; [ | split ] ].
  --intros i Hik.
    specialize (Hjk _ Hik).
    unfold eq_freal_seq in Hjk.
    destruct (Nat.eq_dec (fd2n x i) (fd2n y i)) as [H| ]; [ | easy ].
    clear Hjk; unfold fd2n in H.
    now symmetry; apply digit_eq_eq.
  --specialize (Hxy k) as Hk.
    unfold freal_normalize in Hk; simpl in Hk.
    unfold digit_sequence_normalize in Hk.
    destruct (LPO_fst (mark_9 (freal y) k)) as [Hyk| Hyk].
   ++exfalso.
     specialize (mark_9_all_9 _ _ Hyk) as H; clear Hyk; rename H into Hyk.
     destruct (LPO_fst (mark_9 (freal x) k)) as [Hxk| Hxk].
    **destruct (lt_dec (S (d2n (freal x) k))) as [Hxlt| Hxge].
    ---destruct (lt_dec (S (d2n (freal y) k))) as [Hylt| Hyge].
     +++apply digit_eq_eq in Hk; simpl in Hk.
        apply Nat.succ_inj in Hk.
        unfold fd2n in Hlt; unfold d2n in Hk.
        rewrite Hk in Hlt; lia.
     +++now apply digit_eq_eq in Hk.
    ---apply Nat.nlt_ge in Hxge.
       unfold d2n in Hxge.
       specialize (digit_lt_radix (freal x k)) as Hx.
       specialize (digit_lt_radix (freal y k)) as Hy.
       unfold fd2n in Hlt; lia.
    **destruct Hxk as (l & Hjl & Hl).
    ---destruct (lt_dec (S (d2n (freal y) k)) rad) as [Hylt| Hyge].
     +++apply digit_eq_eq in Hk; simpl in Hk.
        unfold fd2n in Hlt; unfold d2n in Hk; lia.
     +++apply Nat.nlt_ge in Hyge.
        unfold mark_9 in Hl.
unfold freal_normalize in Hxy; simpl in Hxy.
...

specialize (Hxy (k + l + 1)).
unfold freal_normalize in Hxy.
simpl in Hxy.
unfold digit_sequence_normalize in Hxy.
destruct (LPO_fst (mark_9 (freal x) (k + l + 1))) as [H1| H1].
 destruct (lt_dec (S (d2n (freal x) (k + l + 1))) rad) as [H2| ]; [ | lia ].
 apply digit_eq_eq in Hxy; simpl in Hxy.
  destruct (LPO_fst (mark_9 (freal y) (k + l + 1))) as [H3| H3].
   destruct (lt_dec (S (d2n (freal y) (k + l + 1))) rad) as [H4| H4].
    simpl in Hxy.
    specialize (Hyk l); lia.

    easy.

   destruct H3 as (m & Hjm & Hm).
   unfold mark_9 in Hm.
   specialize (Hyk (l + m + 1)).
   replace (k + (l + m + 1) + 1) with (k + l + 1 + m + 1) in Hyk; lia.

 destruct (LPO_fst (mark_9 (freal y) (k + l + 1))) as [H3| H3].
  destruct (lt_dec (S (d2n (freal y) (k + l + 1))) rad) as [H4| H4].
   apply digit_eq_eq in Hxy; simpl in Hxy.
   specialize (Hyk l); lia.

...
specialize (Hxy (k + l)).
unfold freal_normalize in Hxy.
simpl in Hxy.
unfold digit_sequence_normalize in Hxy.
destruct (LPO_fst (mark_9 (freal x) (k + l))) as [H1| H1].
 specialize (H1 0).
 unfold mark_9 in H1.
 now rewrite Nat.add_0_r in H1.

 destruct (LPO_fst (mark_9 (freal y) (k + l))) as [H2| H2].
  destruct (lt_dec (S (d2n (freal y) (k + l))) rad) as [H3| H3].
   apply digit_eq_eq in Hxy; simpl in Hxy.
   destruct l; [ rewrite Nat.add_0_r in H3; lia | ].
   specialize (Hyk l).
   replace (k + S l) with (k + l + 1) in H3; lia.

   apply Nat.nlt_ge in H3.
...

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

Definition nB {r : radix} (rg := nat_ord_ring) n k u :=
  Σ (j = n, n + k), u j * rad ^ (n + k - j).

Definition test_seq {r : radix} i u k :=
  let n := rad * (i + k + 2) in
  let s := rad ^ (n - 1 - i) in
  let t := rad ^ (n + k + 1) in
  if lt_dec (nA i n u mod s * rad ^ (k + 1) + nB n k u) t then 0 else 1.

Definition numbers_to_digits {r : radix} u i :=
  match LPO_fst (test_seq i u) with
  | inl _ =>
      let n := rad * (i + 2) in
      let s := rad ^ (n - 1 - i) in
      let d := u i + nA i n u / s in
      mkdig _ (d mod rad) (Nat.mod_upper_bound d rad radix_ne_0)
  | inr (exist _ k _) =>
      let n := rad * (i + k + 2) in
      let s := rad ^ (n - 1 - i) in
      let d := u i + nA i n u / s + 1 in
      mkdig _ ((d + 1) mod rad) (Nat.mod_upper_bound (d + 1) rad radix_ne_0)
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

Theorem test_seq_freal_add_series_comm {r : radix} : ∀ x y i k,
  test_seq i (freal_add_series x y) k =
  test_seq i (freal_add_series y x) k.
Proof.
intros.
unfold test_seq.
now rewrite nA_freal_add_series_comm, nB_freal_add_series_comm.
Qed.

Theorem test_seq_freal_mul_series_comm {r : radix} : ∀ x y i k,
  test_seq i (freal_mul_series x y) k =
  test_seq i (freal_mul_series y x) k.
Proof.
intros.
unfold test_seq.
now rewrite nA_freal_mul_series_comm, nB_freal_mul_series_comm.
Qed.

Theorem freal_add_to_seq_i_comm {r : radix} : ∀ x y i,
  freal_add_to_seq x y i = freal_add_to_seq y x i.
Proof.
intros.
unfold freal_add_to_seq, numbers_to_digits.
remember (freal_add_series x y) as xy.
remember (freal_add_series y x) as yx.
destruct (LPO_fst (test_seq i xy)) as [Hxy| Hxy].
-rewrite Heqxy, freal_add_series_comm, <- Heqyx.
 destruct (LPO_fst (test_seq i yx)) as [Hyx| Hyx].
 +now rewrite nA_freal_add_series_comm, <- Heqyx.

 +destruct Hyx as (k & Hjk & Hk).
  rewrite Heqyx, test_seq_freal_add_series_comm, <- Heqxy in Hk.
  now rewrite Hxy in Hk.

-destruct Hxy as (k & Hjk & Hk).
 rewrite Heqxy, test_seq_freal_add_series_comm, <- Heqyx in Hk.
 destruct (LPO_fst (test_seq i yx)) as [Hyx| Hyx].
 +now rewrite Hyx in Hk.

 +destruct Hyx as (l & Hjl & Hl).
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
destruct (LPO_fst (mark_9 xy i)) as [Hxy| Hxy].
 destruct (LPO_fst (mark_9 yx i)) as [Hyx| Hyx].
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
  unfold mark_9, d2n in Hk.
  rewrite freal_add_to_seq_i_comm in Hk.
  now specialize (Hxy k).

 destruct Hxy as (k & Hjk & Hk).
 unfold freal_add in Heqxy; simpl in Heqxy.
 unfold freal_add in Heqyx; simpl in Heqyx.
 destruct (LPO_fst (mark_9 yx i)) as [Hyx| Hyx].
  exfalso; clear Hjk.
  subst xy yx; simpl in Hk, Hyx; unfold d2n in Hk; simpl.
  unfold mark_9, d2n in Hk.
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
destruct (LPO_fst (mark_9 xy i)) as [Hxy| Hxy].
 destruct (LPO_fst (mark_9 yx i)) as [Hyx| Hyx].
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
  unfold mark_9, d2n in Hk.
  rewrite freal_mul_to_seq_i_comm in Hk.
  unfold freal_mul in Heqxy; simpl in Heqxy.
  subst xy; simpl in Hxy; simpl.
  now specialize (Hxy k).

 destruct Hxy as (k & Hjk & Hk).
 unfold freal_mul in Heqxy; simpl in Heqxy.
 unfold freal_mul in Heqyx; simpl in Heqyx.
 destruct (LPO_fst (mark_9 yx i)) as [Hyx| Hyx].
  exfalso; clear Hjk.
  subst xy yx; simpl in Hk, Hyx; simpl; unfold d2n in Hk.
  unfold mark_9, d2n in Hk.
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
destruct (Nat.eq_dec (fd2n nxy i) (fd2n nyx i)) as [H| H]; [ easy | ].
exfalso; apply H; clear H.
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
destruct (LPO_fst (eq_freal_seq nxy nyx)) as [H| H]; [ easy | ].
exfalso.
destruct H as (i & Hji & Hi).
apply Hi; clear Hi.
unfold eq_freal_seq.
destruct (Nat.eq_dec (fd2n nxy i) (fd2n nyx i)) as [H| H]; [ easy | ].
exfalso; apply H; clear H.
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

Theorem nA_dig_seq_ub {r : radix} : 0 < rad → ∀ u n,
  (∀ i, i ≤ n - 1 → u i < rad) → ∀ i,
  i + 1 ≤ n - 1
  → nA i n u < rad ^ (n - 1 - i).
Proof.
intros Hr * Hu * Hin.
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

(*
Theorem list_of_nat_pow_succ_sub_1 {r : radix} : 1 < rad → ∀ i,
  list_of_nat 0 (rad ^ S i - 1) = rad - 1 :: list_of_nat 0 (rad ^ i - 1).
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros *.
rewrite power_summation; [ | lia ].
rewrite Nat.add_comm, Nat.add_sub.
destruct i.
-rewrite summation_only_one; simpl.
 rewrite Nat.mul_1_r.
 unfold list_of_nat.
 remember move_carry as f; simpl; subst f.
 destruct (zerop (rad - 1)) as [Hzr1| Hzr1]; [ lia | simpl ].
 rewrite Nat.mod_small; [ f_equal | lia ].
 rewrite Nat.div_small; [ easy | lia ].
-rewrite power_summation; [ | lia ].
 rewrite summation_split_first; [ simpl | lia ].
 rewrite summation_shift; [ simpl | lia ].
 do 2 rewrite Nat.sub_0_r.
 rewrite <- summation_mul_distr_l; simpl.
 remember (Σ (j = 0, i), rad ^ j) as x eqn:Hx.
 rewrite Nat.mul_comm; simpl.
 replace (rad - 1 + rad * x * (rad - 1))
   with ((rad - 1) * S (rad * x)) by lia.
 unfold list_of_nat.
 destruct (zerop ((rad - 1) * S (rad * x))) as [Hrx| Hrx].
 +exfalso.
  apply Nat.eq_mul_0 in Hrx.
  destruct Hrx; [ lia | easy ].
 +destruct (zerop ((rad - 1) * x)) as [Hzr| Hzr].
  *apply Nat.eq_mul_0 in Hzr.
   destruct Hzr as [Hr0| Hx0]; [ lia | ].
   move Hx0 at top; subst x.
   rewrite Nat.mul_0_r, Nat.mul_1_r; simpl.
   rewrite Nat.mod_small; [ f_equal | easy ].
   now rewrite Nat.div_small.
  *simpl.
   replace ((rad - 1) * S (rad * x))
   with (rad - 1 + (rad - 1) * x * rad) by lia.
   rewrite Nat.mod_add; [ | easy ].
   rewrite Nat.mod_small; [ f_equal | lia ].
   rewrite Nat.div_add; [ | easy ].
   rewrite Nat.div_small; [ simpl | lia ].
   destruct (zerop ((rad - 1) * x)) as [H| H]; [ lia | clear H ].
   f_equal.
   destruct (zerop ((rad - 1) * x / rad)) as [Hrxr| Hrxr].
  --now rewrite Hrxr; destruct ((rad - 1) * x).
  --remember ((rad - 1) * x) as y eqn:Hy.
    symmetry in Hy.
    destruct y; [ easy | simpl ].
    destruct (zerop (S y / rad)) as [| H]; [ lia | clear H ].
    f_equal.
    apply move_carry_end_enough_iter; [ easy | | now apply Nat.div_lt ].
    apply Nat.div_lt_upper_bound; [ easy | ].
    apply Nat.div_lt_upper_bound; [ easy | ].
    destruct y; [ now rewrite Nat.div_1_l in Hrxr | ].
    destruct rad as [| s]; [ easy | ].
    destruct s; [ easy | simpl; lia ].
Qed.

Theorem list_of_nat_pow_sub_1 {r : radix} : 1 < rad → ∀ i,
  list_of_nat 0 (rad ^ i - 1) = List.repeat (rad - 1) i.
Proof.
intros Hr *.
destruct i; [ easy | ].
induction i.
-simpl; rewrite Nat.mul_1_r.
 remember rad as s eqn:Hs.
 destruct s; [ easy | ].
 destruct s; [ lia | clear Hr; simpl ].
 unfold list_of_nat; simpl.
 rewrite Nat.mod_small; [ f_equal | lia ].
 rewrite Nat.div_small; [ easy | lia ].
-remember (S i) as x; simpl; subst x.
 rewrite <- IHi; clear IHi.
 rewrite <- Nat.pow_succ_r; [ | apply Nat.le_0_l ].
 now apply list_of_nat_pow_succ_sub_1.
Qed.

Theorem list_of_nat_mul_rad_l {r : radix} : 1 < rad → ∀ n,
  0 < n → list_of_nat 0 (rad * n) = 0 :: list_of_nat 0 n.
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hn.
unfold list_of_nat.
destruct (zerop (rad * n)) as [Hrn| Hrn].
-apply Nat.eq_mul_0 in Hrn.
 now destruct Hrn; [ | subst n ].
-destruct (zerop n) as [| H]; [ now subst n | clear H; simpl ].
 rewrite Nat.mul_comm, Nat.mod_mul; [ f_equal | easy ].
 rewrite Nat.div_mul; [ | easy ].
 destruct (zerop n) as [| H]; [ now subst n | clear H; f_equal ].
 destruct (zerop (n / rad)) as [Hnr| Hnr].
 +now rewrite Hnr; destruct n.
 +destruct n; [ easy | simpl ].
  destruct (zerop (S n / rad)) as [| H]; [ lia | clear H; f_equal ].
  apply move_carry_end_enough_iter; [ easy | | now apply Nat.div_lt ].
  apply Nat.div_lt_upper_bound; [ easy | ].
  apply Nat.div_lt_upper_bound; [ easy | ].
  destruct n; [ now rewrite Nat.div_1_l in Hnr | ].
  destruct rad as [| s]; [ easy | ].
  destruct s; [ lia | simpl; lia ].
Qed.

Theorem list_of_nat_pred_pow_pow {r : radix} : 1 < rad → ∀ i j,
  0 < i
  → list_of_nat 0 ((rad ^ i - 1) * rad ^ j) =
     List.repeat 0 j ++ List.repeat (rad - 1) i.
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hi.
revert i Hi.
induction j; intros.
-simpl; rewrite Nat.mul_1_r.
 now apply list_of_nat_pow_sub_1.
-simpl.
 rewrite Nat.mul_comm, <- Nat.mul_assoc.
 rewrite list_of_nat_mul_rad_l; [ f_equal | easy | ].
 +now rewrite Nat.mul_comm; apply IHj.
 +destruct i; [ easy | ].
  apply Nat.mul_pos_pos.
  *clear -Hr; induction j; simpl; [ lia | ].
   apply Nat.mul_pos_pos; [ lia | easy ].
  *apply (Nat.le_lt_add_lt 1 1); [ easy | simpl ].
   rewrite Nat.sub_add; [ now apply rad_pow_succ_gt_1 | ].
   apply Nat.lt_le_incl.
   now apply rad_pow_succ_gt_1.
Qed.
*)

Theorem numbers_to_digits_id {r : radix} : ∀ u (Hur : ∀ j, u j < rad) i,
  numbers_to_digits u i = mkdig _ (u i) (Hur i).
Proof.
intros.
unfold numbers_to_digits.
destruct (LPO_fst (test_seq i u)) as [H| H].
-specialize (H 0) as HH.
 unfold test_seq in HH; simpl in HH.
 rewrite Nat.mul_1_r, Nat.add_0_r, Nat.add_0_r in HH.
 remember (rad * (i + 2)) as n eqn:Hn.
 remember (rad ^ (n - 1 - i)) as s eqn:Hs.
 destruct (lt_dec (nA i n u mod s * rad  + nB n 0 u) (rad ^ (n + 1)))
  as [Hlt| Hge]; [ clear HH | easy ].
 rewrite Nat.div_small.
 +apply digit_eq_eq; simpl.
  rewrite Nat.add_0_r, Nat.mod_small; [ easy | ].
  now apply Hur.
 +rewrite Hs.
  apply nA_dig_seq_ub; [ easy | easy | ].
  subst n; destruct rad as [| rd]; [ easy | simpl; lia ].
-destruct H as (k & Hjk & Hts).
 unfold test_seq in Hts.
 remember (rad * (i + k + 2)) as n eqn:Hn.
 remember (rad ^ (n - 1 - i)) as s eqn:Hs.
 destruct
   (lt_dec (nA i n u mod s * rad ^ (k + 1) + nB n k u) (rad ^ (n + k + 1)))
  as [Hlt| Hge]; [ easy | clear Hts ].
 exfalso; apply Hge; clear Hge.
 assert (Hin : i + 1 ≤ n - 1).
 +subst n; specialize radix_ge_2 as Hr.
  destruct rad as [| rd]; [ easy | simpl; lia ].
 +assert (H: ∀ i, i ≤ n - 1 → u i < rad) by (intros; apply Hur).
  specialize radix_gt_0 as Hr.
  specialize (nA_dig_seq_ub Hr u n H i Hin) as HnA; clear H.
  rewrite Nat.mod_small; [ | now subst s ].
  specialize (nB_dig_seq_ub Hr _ Hur n k) as HnB.
  subst s.
  unfold nA, nB.
  rewrite summation_mul_distr_r; simpl.
  rewrite summation_eq_compat with (h := λ j, u j * rad ^ (n + k - j)).
  *set (rd := nat_ord_ring_def).
   set (rg := nat_ord_ring).
   replace (summation n) with (summation (S (n - 1))) by (f_equal; lia).
   rewrite <- summation_ub_add with (k₂ := k + 1); [ | lia | lia ].
   replace (n + k + 1) with (S (n + k)) by lia.
   rewrite power_summation; [ | easy ].
   apply le_lt_trans with (m := Σ (j = 0, n + k), u j * rad ^ (n + k - j)).
  --remember (summation (i + 1) (n + k)) as f.
    rewrite summation_ub_add with (k₁ := i) (k₂ := n + k - i);
      [ subst f | lia | lia ].
    rewrite Nat.add_1_r; simpl.
    remember (n + k) as nk; rewrite Nat.add_comm; subst nk.
    apply Nat.le_add_r.
  --rewrite summation_rtl.
    rewrite summation_mul_distr_l; simpl.
    apply le_lt_trans with (m := Σ (j = 0, n + k), (rad - 1) * rad ^ j).
   ++apply (@summation_le_compat rd).
     intros j Hj; simpl.
     rewrite Nat.add_0_r.
     unfold NPeano.Nat.le.
     replace (n + k - (n + k - j)) with j by lia.
     apply Nat.mul_le_mono_nonneg_r; [ lia | ].
     apply Nat.le_add_le_sub_r.
     rewrite Nat.add_1_r.
     apply Hur.
   ++apply Nat.lt_succ_diag_r.
  *intros j Hj.
   rewrite <- Nat.mul_assoc; f_equal.
   rewrite <- Nat.pow_add_r; f_equal; lia.
Qed.

Theorem dig_norm_add_0_l {r : radix} : 0 < rad → ∀ x i,
  (∀ j, fd2n x j < rad)
  → freal (freal_normalize (0 + x)) i = freal (freal_normalize x) i.
Proof.
intros Hr * Hxr.
unfold freal_normalize.
remember (freal (0%F + x)) as nx0 eqn:Hnx0.
remember (freal x) as nx eqn:Hnx.
unfold digit_sequence_normalize; simpl.
destruct (LPO_fst (mark_9 nx0 i)) as [Hx0| Hx0].
-destruct (LPO_fst (mark_9 nx i)) as [Hx| Hx].
 +destruct (lt_dec (S (d2n nx0 i)) rad) as [Hnx0r| Hnx0r].
  *destruct (lt_dec (S (d2n nx i)) rad) as [Hnxr| Hnxr].
  --subst nx nx0; simpl.
    unfold freal_add_to_seq, d2n.
    apply digit_eq_eq; simpl.
    now rewrite (numbers_to_digits_id _ Hxr).
  --exfalso; apply Hnxr.
    subst nx nx0; simpl in Hnx0r; simpl.
    unfold freal_add_to_seq in Hnx0r.
    unfold d2n in Hnx0r.
    now rewrite (numbers_to_digits_id _ Hxr) in Hnx0r.
  *destruct (lt_dec (S (d2n nx i)) rad) as [Hnxr| Hnxr]; [ exfalso | easy ].
   apply Hnx0r.
   subst nx nx0; simpl.
   unfold freal_add_to_seq, d2n; simpl.
   now rewrite (numbers_to_digits_id _ Hxr).
 +destruct Hx as (k & Hjk & Hnk).
  specialize (Hx0 k).
  subst nx nx0; simpl in Hx0.
  unfold freal_add_to_seq in Hx0.
  unfold mark_9, d2n in Hx0.
  now rewrite (numbers_to_digits_id _ Hxr) in Hx0.
-destruct (LPO_fst (mark_9 nx i)) as [Hx| Hx].
 +destruct Hx0 as (k & Hjk & Hnk).
  specialize (Hx k).
  subst nx nx0; simpl in Hnk.
  unfold freal_add_to_seq, mark_9, d2n in Hnk.
  now rewrite (numbers_to_digits_id _ Hxr) in Hnk.
 +subst nx nx0; simpl.
  unfold freal_add_to_seq, d2n.
  rewrite (numbers_to_digits_id _ Hxr).
  now apply digit_eq_eq.
Qed.

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
destruct (Nat.eq_dec (fd2n n0x i) (fd2n nx i)) as [H| H]; [ easy | ].
exfalso; apply H; clear H.
subst n0x nx; simpl.
unfold fd2n; f_equal.
now apply dig_norm_add_0_l; [ | unfold fd2n ].
Qed.

Theorem dig_norm_add_assoc {r : radix} : ∀ x y z i,
  freal (freal_normalize (x + (y + z))) i = freal (freal_normalize (x + y + z)) i.
Proof.
intros.
unfold freal_normalize.
remember (freal (x + (y + z))) as xy.
remember (freal ((x + y) + z)) as yx.
simpl.
unfold digit_sequence_normalize.
destruct (LPO_fst (λ j : nat, rad - 1 - d2n xy (i + j + 1))) as [Hxy| Hxy].
-destruct (LPO_fst (λ j : nat, rad - 1 - d2n yx (i + j + 1))) as [Hyx| Hyx].
 +unfold freal_add in Heqxy; simpl in Heqxy.
  unfold freal_add in Heqyx; simpl in Heqyx.
  destruct (lt_dec (S (d2n xy i)) rad) as [Hrxy| Hrxy].
  *destruct (lt_dec (S (d2n yx i)) rad) as [Hryx| Hryx].
  --f_equal.
    subst xy yx; simpl.
    unfold freal_add_to_seq.
    apply digit_eq_eq; simpl; f_equal.
    unfold d2n.
(*
Theorem glop {r : radix} : ∀ x y,
  numbers_to_digits (freal_add_series {| freal := numbers_to_digits x |} y) =
  numbers_to_digits (freal_add_series {| freal := x |} y).
Admitted. Show.
    rewrite glop.
*)
Abort. (*
    rewrite freal_add_series_comm.
...

   subst xy; simpl in Hrxy; simpl.
   destruct (lt_dec (S (yx i)) rad) as [Hryx| Hryx].
    unfold freal_add in Heqyx; simpl in Heqyx.
    subst yx; simpl in Hryx; simpl.
unfold freal_add_to_seq.
Search numbers_to_digits.
...
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
*)

Require Import Morphisms Setoid.
Definition freal_eq_prop {r : radix} x y := freal_eq x y = true.

Theorem freal_eq_refl {r : radix} : reflexive _ freal_eq_prop.
Proof.
intros x.
unfold freal_eq_prop, freal_eq, freal_normalized_eq.
remember (freal_normalize x) as y eqn:Hy.
destruct (LPO_fst (eq_freal_seq y y)) as [Hs| Hs]; [ easy | exfalso ].
destruct Hs as (i & Hji & Hyy).
apply Hyy.
unfold eq_freal_seq.
now destruct (Nat.eq_dec (fd2n y i) (fd2n y i)).
Qed.

Theorem freal_eq_sym {r : radix} : symmetric _ freal_eq_prop.
Proof.
intros x y Hxy.
unfold freal_eq_prop, freal_eq, freal_normalized_eq in Hxy |-*.
remember (freal_normalize x) as nx eqn:Hnx.
remember (freal_normalize y) as ny eqn:Hny.
destruct (LPO_fst (eq_freal_seq ny nx)) as [Hs| Hs]; [ easy | exfalso ].
destruct (LPO_fst (eq_freal_seq nx ny)) as [Ht| Ht]; [ clear Hxy | easy ].
destruct Hs as (i & Hji & Hyx).
specialize (Ht i).
unfold eq_freal_seq in Ht, Hyx.
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
destruct (LPO_fst (eq_freal_seq nx ny)) as [Hx| Hx]; [ clear Hxy | easy ].
destruct (LPO_fst (eq_freal_seq ny nz)) as [Hy| Hy]; [ clear Hyz | easy ].
destruct (LPO_fst (eq_freal_seq nx nz)) as [Hz| Hz]; [ easy | exfalso ].
destruct Hz as (i & Hji & Hz).
specialize (Hx i).
specialize (Hy i).
unfold eq_freal_seq in Hx, Hy, Hz.
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
  (∀ k, eq_freal_seq x y k = 0) → (∀ k, freal x k = freal y k).
Proof.
intros * Hk *.
specialize (Hk k).
unfold eq_freal_seq in Hk.
apply digit_eq_eq.
now destruct (Nat.eq_dec (fd2n x k) (fd2n y k)).
Qed.

Theorem nA_eq_compat {r : radix} : ∀ i n u v,
  (∀ i, u i = v i)
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

Theorem test_seq_eq_compat {r : radix} : ∀ i f g,
  (∀ i, f i = g i) → ∀ k, test_seq i f k = test_seq i g k.
Proof.
intros * Hfg *.
unfold test_seq.
erewrite nA_eq_compat; [ | easy ].
erewrite nB_eq_compat; [ | easy ].
easy.
Qed.

Theorem numbers_to_digits_eq_compat {r : radix} : ∀ f g,
  (∀ i, f i = g i) → ∀ i,
  numbers_to_digits f i = numbers_to_digits g i.
Proof.
intros * Hfg *.
unfold numbers_to_digits.
rewrite Hfg.
destruct (LPO_fst (test_seq i f)) as [Hf| Hf].
-destruct (LPO_fst (test_seq i g)) as [Hg| Hg].
 +f_equal; f_equal.
  unfold nA.
  erewrite summation_eq_compat; [ reflexivity | simpl ].
  intros j Hj.
  now rewrite Hfg.
 +exfalso.
  destruct Hg as (k & Hjk & H); apply H; clear H.
  specialize (Hf k).
  erewrite test_seq_eq_compat in Hf; [ | easy ]; easy.
-destruct (LPO_fst (test_seq i g)) as [Hg| Hg].
 +exfalso.
  destruct Hf as (k & Hjk & H); apply H; clear H.
  specialize (Hg k).
  erewrite test_seq_eq_compat; [ | easy ]; easy.
 +destruct Hf as (k & Hjk & Hk).
  destruct Hg as (l & Hjl & Hl).
  f_equal; f_equal; f_equal.
  destruct (lt_eq_lt_dec k l) as [[Hkl| Hkl]| Hkl].
  *specialize (Hjl _ Hkl).
   exfalso; apply Hk.
   erewrite test_seq_eq_compat; [ | easy ]; easy.
  *subst l; apply digit_eq_eq; simpl.
   f_equal; f_equal; f_equal; f_equal; f_equal.
   now apply nA_eq_compat.
  *specialize (Hjk _ Hkl).
   apply digit_eq_eq; simpl.
   exfalso; apply Hl.
   erewrite test_seq_eq_compat in Hjk; [ | easy ]; easy.
Qed.

Add Parametric Morphism {r : radix} : freal_add
  with signature freal_eq_prop ==> freal_eq_prop ==> freal_eq_prop
  as freal_add_morph.
Proof.
intros x y Hxy x' y' Hxy'.
unfold freal_eq_prop in Hxy, Hxy' |-*.
unfold freal_eq in Hxy, Hxy' |-*.
remember (freal_normalize x) as nx eqn:Hnx.
remember (freal_normalize y) as ny eqn:Hny.
remember (freal_normalize x') as nx' eqn:Hnx'.
remember (freal_normalize y') as ny' eqn:Hny'.
unfold freal_normalized_eq in Hxy, Hxy'.
destruct (LPO_fst (eq_freal_seq nx ny)) as [Hx| Hx]; [ clear Hxy | easy ].
destruct (LPO_fst (eq_freal_seq nx' ny')) as [Hy| Hy]; [ clear Hxy' | easy ].
specialize (all_eq_seq_all_eq nx ny Hx) as H; clear Hx; rename H into Hx.
specialize (all_eq_seq_all_eq nx' ny' Hy) as H; clear Hy; rename H into Hy.
unfold freal_normalized_eq.
remember (freal_normalize (x + x')) as nxx' eqn:Hnxx'.
remember (freal_normalize (y + y')) as nyy' eqn:Hnyy'.
destruct (LPO_fst (eq_freal_seq nxx' nyy')) as [Hxy| Hxy]; [ easy | ].
destruct Hxy as (i & Hji & Hxy); exfalso; apply Hxy; clear Hxy.
unfold eq_freal_seq.
destruct (Nat.eq_dec (fd2n nxx' i) (fd2n nyy' i)) as [| Hxy]; [ easy | ].
exfalso; apply Hxy; clear Hxy.
rewrite Hnxx', Hnyy'; simpl.
move Hx at bottom; move Hy at bottom.
(*
Theorem freal_norm_norm {r : radix} : ∀ x y,
  (x + y = freal_normalize x + freal_normalize y)%F.
Proof.
intros.
unfold freal_eq.
unfold freal_normalized_eq.
Abort.
*)
(*
Theorem freal_norm_norm {r : radix} : ∀ x y,
  freal_normalize (x + y) =
  freal_normalize (freal_normalize x + freal_normalize y).
Proof.
intros.
unfold freal_normalize.
unfold freal_add_to_seq.
unfold freal_add_series; simpl.
...
*)
unfold fd2n; simpl.
unfold digit_sequence_normalize.
remember (freal_add_to_seq x x') as sxx' eqn:Hsxx'.
remember (freal_add_to_seq y y') as syy' eqn:Hsyy'.
destruct (LPO_fst (mark_9 sxx' i)) as [Hsx| Hsx].
-specialize (mark_9_all_9 _ _ Hsx) as H; clear Hsx; rename H into Hsx.
 destruct (LPO_fst (mark_9 syy' i)) as [Hsy| Hsy].
 +specialize (mark_9_all_9 _ _ Hsy) as H; clear Hsy; rename H into Hsy.
  destruct (lt_dec (S (d2n sxx' i)) rad) as [Hxr| Hxr].
  *simpl.
   destruct (lt_dec (S (d2n syy' i)) rad) as [Hyr| Hyr].
 --simpl.
   rewrite Hsxx' in Hxr; simpl in Hxr.
   rewrite Hsyy' in Hyr; simpl in Hyr.
   rewrite Hsxx', Hsyy'.
   f_equal.
   unfold freal_add_to_seq in Hxr, Hyr |-*.
   move Hx at bottom; move Hy at bottom.
   unfold d2n.
   assert (H : ∀ j, j < i → freal nxx' j = freal nyy' j).
  ++intros j Hj.
    specialize (Hji _ Hj).
    unfold eq_freal_seq in Hji.
    apply digit_eq_eq.
    now destruct (Nat.eq_dec (fd2n nxx' j) (fd2n nyy' j)).
  ++clear Hji; rename H into Hji.
    subst.
    move Hxr at bottom; move Hyr at bottom.
    move Hsx at bottom; move Hsy at bottom.
    unfold freal_normalize in Hji; simpl in Hji.
    unfold freal_add_to_seq in Hji, Hsx, Hsy.
    unfold d2n in Hxr, Hyr, Hsx, Hsy.
    remember (numbers_to_digits (freal_add_series x x')) as xx' eqn:Hxx'.
    remember (numbers_to_digits (freal_add_series y y')) as yy' eqn:Hyy'.
    assert (H : ∀ j, j < i → dig (xx' j) = dig (yy' j)).
   **intros j Hj.
     specialize (Hji _ Hj).
     unfold digit_sequence_normalize in Hji.
     destruct (LPO_fst (mark_9 xx' j)) as [H1| H1].
   ---specialize (mark_9_all_9 _ _ H1) as H; clear H1; rename H into H1.
      unfold d2n in H1.
      specialize (H1 (i - j - 1)).
      replace (j + (i - j - 1) + 1) with i in H1 by lia.
      rewrite H1 in Hxr.
      rewrite Nat.sub_1_r in Hxr.
      rewrite Nat.succ_pred_pos in Hxr; [ lia | easy ].
   ---destruct (LPO_fst (mark_9 yy' j)) as [H2| H2].
    +++specialize (mark_9_all_9 _ _ H2) as H; clear H2; rename H into H2.
       unfold d2n in H2.
       specialize (H2 (i - j - 1)).
       replace (j + (i - j - 1) + 1) with i in H2 by lia.
       rewrite H2 in Hyr.
       rewrite Nat.sub_1_r in Hyr.
       rewrite Nat.succ_pred_pos in Hyr; [ lia | easy ].
    +++now f_equal.
   **clear Hji; rename H into Hji; move Hji after Hxr.
Check freal_normalized_eq_iff.
...
     exfalso; specialize (H1 (i - j - 1)).
     unfold d2n in H1.
...
Search (rad - _).

     apply Nat.sub_0_le in H1.
Check Nat.sub_0_le.
Search (_ - _ = 0).

unfold digit_sequence_normalize in Hji.


Print digit_sequence_normalize.
(* en fait on devrait même avoir j < i → dig (xx' j) = dig (yy' j) *)
...
...
(*
unfold freal_add_series.
Print numbers_to_digits.
Print nA.
...
*)
unfold numbers_to_digits.
destruct (LPO_fst (test_seq i (freal_add_series x x'))) as [Htx| Htx].
destruct (LPO_fst (test_seq i (freal_add_series y y'))) as [Hty| Hty].
...
unfold sequence_add at 1 3.
...

(* numbers_to_digits vs digit_sequence_normalize ? *)
Check numbers_to_digits.
Check digit_sequence_normalize.
...
   apply numbers_to_digits_eq_compat.
   intros j.
   unfold freal_add_series, sequence_add.
(* freal_normalize (x + x') = freal_normalize (nx + nx') ? *)
...
   destruct (lt_eq_lt_dec j i) as [[Hij| Hij]| Hij].
  ++specialize (Hji _ Hij).
    rewrite Hnxx', Hnyy' in Hji; simpl in Hji.
    unfold freal_normalize in Hji; simpl in Hji.
    unfold eq_freal_seq in Hji.
    simpl in Hji.
    unfold freal_add_to_seq in Hji.
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
apply freal_eq_prop_eq.
...

Check freal_add_morph.
rewrite (@freal_add_comm r).
...
unfold freal_eq.
unfold freal_normalized_eq.
remember (freal_normalize (x + (y + z))) as nx_yz eqn:Hnx_yz.
remember (freal_normalize ((x + y) + z)) as nxy_z eqn:Hnxy_z.
destruct (LPO_fst (eq_freal_seq nx_yz nxy_z)) as [H| H]; [ easy | ].
exfalso.
destruct H as (i & Hji & Hi).
apply Hi; clear Hi.
unfold eq_freal_seq.
destruct (Nat.eq_dec (freal nx_yz i) (freal nxy_z i)) as [H| H]; [ easy | ].
exfalso; apply H; clear H.
subst nx_yz nxy_z.
rewrite dig_norm_add_assoc.
...
