(* addition modulo 1 in I *)

Require Import Utf8 QArith NPeano.
Require Import Oracle Real01.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).
Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).

Open Scope nat_scope.

Definition Isum2Un x y i j := eqb (x.[i+j]) (y.[i+j]).

Definition fst_same x y i :=
  match fst_true (Isum2Un x y i) with
  | Some di => Some di
  | None => None
  end.

Theorem fst_same_iff : ∀ x y i odi, fst_same x y i = odi ↔
  match odi with
  | Some di =>
      (∀ dj, dj < di → x.[i + dj] = negb (y.[i + dj]))
      ∧ x.[i + di] = y.[i + di]
  | None =>
      ∀ dj, x.[i + dj] = negb (y.[i + dj])
  end.
Proof.
intros x y i odi.
split; intros Hi.
 subst odi.
 unfold fst_same; simpl.
 remember (fst_true (Isum2Un x y i)) as s1 eqn:Hs1 .
 apply fst_true_iff in Hs1; simpl in Hs1.
 unfold Isum2Un in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Ht1).
  split; [ idtac | apply eqb_true_iff; assumption ].
  intros dj Hdj.
  remember Hdj as H; clear HeqH.
  apply Hn1 in H.
  apply eqb_false_iff in H.
  destruct (y .[ i + dj]); simpl.
   apply not_true_iff_false; assumption.

   apply not_false_iff_true; assumption.

  intros dj.
  pose proof (Hs1 dj) as H.
  apply eqb_false_iff in H.
  destruct (y .[ i + dj]); simpl.
   apply not_true_iff_false; assumption.

   apply not_false_iff_true; assumption.

 unfold fst_same; simpl.
 remember (fst_true (Isum2Un x y i)) as s1 eqn:Hs1 .
 apply fst_true_iff in Hs1; simpl in Hs1.
 unfold Isum2Un in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Ht1).
  destruct odi as [di| ].
   destruct Hi as (Hn, Ht).
   destruct (lt_eq_lt_dec di di1) as [[H1| H1]| H1].
    remember H1 as H; clear HeqH.
    apply Hn1 in H.
    rewrite Ht in H.
    destruct (y .[ i + di]); discriminate H.

    subst di; reflexivity.

    remember H1 as H; clear HeqH.
    apply Hn in H.
    apply eqb_prop in Ht1.
    rewrite H in Ht1.
    exfalso; revert Ht1; apply no_fixpoint_negb.

   apply eqb_prop in Ht1.
   rewrite Hi in Ht1.
   exfalso; revert Ht1; apply no_fixpoint_negb.

  destruct odi as [di| ]; [ idtac | reflexivity ].
  destruct Hi as (Hn, Ht).
  pose proof (Hs1 di) as H.
  apply eqb_false_iff in H.
  rewrite Ht in H.
  exfalso; apply H; reflexivity.
Qed.

Infix "⊕" := xorb (left associativity, at level 50) : bool_scope.

Definition carry x y i :=
  match fst_same x y i with
  | Some dj => x.[i + dj]
  | None => true
  end.

Definition I_add_i x y i := x.[i] ⊕ y.[i] ⊕ carry x y (S i).
Definition I_add x y := {| rm := I_add_i x y |}.
Definition I_eq x y := ∀ i, rm (I_add x I_zero) i = rm (I_add y I_zero) i.

Notation "x + y" := (I_add x y) : I_scope.
Notation "x = y" := (I_eq x y) : I_scope.
Notation "x ≠ y" := (¬ I_eq x y) : I_scope.

Arguments carry x%I y%I i%nat.
Arguments I_add_i x%I y%I i%nat.
Arguments I_add x%I y%I.
Arguments I_eq x%I y%I.
Arguments fst_same x%I y%I i%nat.

Definition I_opp x := {| rm i := negb (x.[i]) |}.
Definition I_sub x y := I_add x (I_opp y).

Notation "- x" := (I_opp x) : I_scope.
Notation "x - y" := (I_sub x y) : I_scope.

Theorem fold_I_sub : ∀ x y, (x + - y)%I = (x - y)%I.
Proof. intros; reflexivity. Qed.

Theorem fst_same_sym_iff : ∀ x y i odi,
  odi = fst_same x y i
  ↔ match odi with
    | Some di =>
        (∀ dj : nat, dj < di → x .[ i + dj] = negb (y.[i + dj]))
        ∧ x .[ i + di] = y .[ i + di]
    | None => ∀ dj : nat, x .[ i + dj] = negb (y.[i + dj])
    end.
Proof.
intros x y i odi.
split; intros H.
 apply fst_same_iff; symmetry; assumption.

 symmetry; apply fst_same_iff; assumption.
Qed.

Theorem carry_compat_r : ∀ x y z j,
  (∀ i, x .[ i] = y .[ i])
  → carry y z j = carry x z j.
Proof.
intros x y z j Hxy.
unfold carry; intros.
remember (fst_same y z j) as s1 eqn:Hs1 .
remember (fst_same x z j) as s2 eqn:Hs2 .
symmetry in Hs1, Hs2.
apply fst_same_iff in Hs1.
apply fst_same_iff in Hs2.
simpl in Hs1, Hs2; simpl.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hs1.
 destruct s2 as [di2| ].
  destruct Hs2 as (Hn2, Hs2).
  rewrite Hs2.
  destruct (lt_dec di1 di2) as [H1| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   rewrite Hxy, Hs1 in H.
   destruct (z.[j+di1]); discriminate H.

   apply Nat.nlt_ge in H1.
   destruct (lt_dec di2 di1) as [H2| H2].
    remember H2 as H; clear HeqH.
    apply Hn1 in H.
    rewrite <- Hxy, Hs2 in H.
    destruct (z.[j+di2]); discriminate H.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H1; auto.

  rewrite <- Hxy, Hs2 in Hs1.
  destruct (z.[j + di1]); discriminate Hs1.

 destruct s2 as [di2| ]; auto.
 destruct Hs2 as (Hn2, Hs2).
 rewrite Hxy, Hs1 in Hs2.
 destruct (z.[ j + di2]); discriminate Hs2.
Qed.

Theorem fst_same_diag : ∀ x n, fst_same x x n = Some 0%nat.
Proof.
intros x n.
apply fst_same_iff; simpl.
split; [ idtac | reflexivity ].
intros dj Hdj.
exfalso; revert Hdj; apply Nat.nlt_0_r.
Qed.

Theorem carry_diag : ∀ x i, carry x x i = x.[i].
Proof.
intros x i.
unfold carry; simpl.
rewrite fst_same_diag.
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem negb_xorb_diag_l : ∀ a, negb a ⊕ a = true.
Proof. intros a; destruct a; reflexivity. Qed.

Theorem negb_xorb_diag_r : ∀ a, a ⊕ negb a = true.
Proof. intros a; destruct a; reflexivity. Qed.

Theorem I_zero_iff : ∀ x,
  (x = 0)%I ↔
  (∀ i, x.[i] = false) ∨ (∀ i, x.[i] = true).
Proof.
intros x.
split.
 intros Hx.
 remember (x .[ 0]) as b eqn:Hb .
 symmetry in Hb.
 destruct b; [ right | left ]; intros i.
  induction i; [ assumption | idtac ].
  pose proof (Hx i) as Hi; simpl in Hi.
  unfold I_add_i in Hi; simpl in Hi.
  rewrite xorb_false_r, carry_diag in Hi; simpl in Hi.
  rewrite IHi, xorb_true_l in Hi.
  apply negb_false_iff in Hi.
  unfold carry in Hi; simpl in Hi.
  remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ]; [ idtac | clear Hi ].
   destruct Hs1 as (Hn1, Hs1).
   rewrite Hs1 in Hi; discriminate Hi.

   pose proof (Hs1 O) as H; rewrite Nat.add_0_r in H; assumption.

  induction i; [ assumption | idtac ].
  pose proof (Hx i) as Hi; simpl in Hi.
  unfold I_add_i in Hi; simpl in Hi.
  rewrite xorb_false_r, carry_diag in Hi; simpl in Hi.
  rewrite IHi, xorb_false_l in Hi.
  unfold carry in Hi; simpl in Hi.
  remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
  destruct s1 as [dj1| ]; [ idtac | discriminate Hi ].
  destruct Hs1 as (Hn1, Hs1).
  pose proof (Hx (S i)) as Hsi; simpl in Hsi.
  unfold I_add_i in Hsi; simpl in Hsi.
  rewrite xorb_false_r, carry_diag in Hsi; simpl in Hsi.
  unfold carry in Hsi; simpl in Hsi.
  remember (fst_same x 0 (S (S i))) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s2 as [dj2| ].
   destruct Hs2 as (Hn2, Ht2).
   rewrite Ht2, xorb_false_r in Hsi; assumption.

   destruct dj1.
    rewrite Nat.add_0_r in Hi; assumption.

    rewrite Nat.add_succ_r, Hs2 in Hi.
    discriminate Hi.

 intros [Hx| Hx].
  unfold I_eq; simpl; intros i.
  unfold I_add_i; simpl.
  rewrite xorb_false_r, carry_diag; simpl.
  rewrite Hx, xorb_false_l.
  unfold carry; simpl.
  remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ].
   destruct Hs1; assumption.

   pose proof (Hs1 O) as H.
   rewrite Hx in H; discriminate H.

  unfold I_eq; simpl; intros i.
  unfold I_add_i; simpl.
  rewrite xorb_false_r, carry_diag; simpl.
  rewrite Hx, xorb_true_l.
  apply negb_false_iff.
  unfold carry; simpl.
  remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
  destruct s1 as [dj1| ]; [ idtac | reflexivity ].
  apply Hx.
Qed.

(* equality is equivalence relation *)

Theorem I_eq_refl : reflexive _ I_eq.
Proof. intros x i; reflexivity. Qed.

Theorem I_eq_sym : symmetric _ I_eq.
Proof. intros x y Hxy i; symmetry; apply Hxy. Qed.

Theorem I_eq_trans : transitive _ I_eq.
Proof. intros x y z Hxy Hyz i; rewrite Hxy; apply Hyz. Qed.

Add Parametric Relation : _ I_eq
 reflexivity proved by I_eq_refl
 symmetry proved by I_eq_sym
 transitivity proved by I_eq_trans
 as I_rel.

Close Scope nat_scope.
