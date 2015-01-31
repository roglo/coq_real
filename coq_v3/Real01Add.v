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

Close Scope nat_scope.
