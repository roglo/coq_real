Require Import Utf8 QArith NPeano.
Require Import Real01.

Open Scope nat_scope.

Definition b2n (b : bool) := if b then 1 else 0.

Definition I_add_wn_i x y i := b2n (x.[i]) + b2n (y.[i]).
Arguments I_add_wn_i x%I y%I i%nat.

Definition I_add_wn x y := {| inat := I_add_wn_i x y |}.
Arguments I_add_wn x%I y%I.

Definition carry x i :=
  match fst_not_1 x i with
  | Some di => inat x (i + di)
  | None => 1
  end.

Definition Iwn2I x i := Nat.eqb (inat x i) 0 ⊕ Nat.eqb (carry x (S i)) 0.

Definition I_add x y := {| idig := Iwn2I (I_add_wn x y) |}.

Definition I_zero := {| idig i := false |}.

Notation "0" := I_zero : I_scope.
Notation "x + y" := (I_add x y) (at level 50, left associativity) : I_scope.

Definition I_eq_wn x y := ∀ i, inat x i = inat y i.
Definition I_eqs x y := ∀ i, x.[i] = y.[i].
Definition I_eq x y := ∀ i, (x + 0)%I.[i] = (y + 0)%I.[i].
Arguments I_eq_wn x%I y%I.
Arguments I_eqs x%I y%I.
Arguments I_eq x%I y%I.

Notation "x = y" := (I_eq x y) : I_scope.
Notation "x ≠ y" := (¬ I_eq x y) : I_scope.

(* *)

Theorem le_neq_lt : ∀ a b : nat, a ≤ b → a ≠ b → (a < b)%nat.
Proof.
intros a b Hab Hnab.
apply le_lt_eq_dec in Hab.
destruct Hab as [Hle| Heq]; [ assumption | idtac ].
exfalso; apply Hnab; assumption.
Qed.

Theorem all_lt_all : ∀ P : nat → Prop,
  (∀ n, (∀ m, (m < n)%nat → P m) → P n)
  → ∀ n, P n.
Proof.
intros P Hm n.
apply Hm.
induction n; intros m Hmn.
 apply Nat.nle_gt in Hmn.
 exfalso; apply Hmn, Nat.le_0_l.

 destruct (eq_nat_dec m n) as [H1| H1].
  subst m; apply Hm; assumption.

  apply IHn.
  apply le_neq_lt; [ idtac | assumption ].
  apply Nat.succ_le_mono; assumption.
Qed.

Theorem nat_sub_add_r : ∀ a b c,
  a < b
  → c = b - S a
  → b = a + S c.
Proof.
intros a b c Hab Hc; subst c.
rewrite <- Nat.sub_succ_l; [ simpl | assumption ].
rewrite Nat.add_sub_assoc; [ idtac | apply Nat.lt_le_incl; assumption ].
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Theorem neq_negb : ∀ b b', b ≠ b' ↔ b = negb b'.
Proof.
intros b b'.
split; intros H.
 destruct b'; simpl.
  apply not_true_iff_false; auto.

  apply not_false_iff_true; auto.

 subst b; intros H.
 destruct b'; discriminate H.
Qed.

(* I_eqs implies I_eq *)

Theorem fst_not_1_add_wn_eqs_compat : ∀ x y z i,
  I_eqs x y
  → fst_not_1 (I_add_wn x z) i = fst_not_1 (I_add_wn y z) i.
Proof.
intros x y z i Hxy.
unfold I_eqs in Hxy.
apply fst_not_1_iff; simpl.
remember (fst_not_1 (I_add_wn x z) i) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Ht1).
 split.
  intros dj Hdj.
  unfold I_add_wn_i; simpl.
  rewrite <- Hxy.
  apply Hn1; assumption.

  unfold I_add_wn_i.
  rewrite <- Hxy; assumption.

 intros dj.
 unfold I_add_wn_i.
 rewrite <- Hxy; apply Hs1.
Qed.

Theorem I_eqs_eq : ∀ x y, I_eqs x y → (x = y)%I.
Proof.
intros x y Hxy.
unfold I_eqs in Hxy; simpl in Hxy.
unfold I_eq; simpl; intros i.
unfold Iwn2I; simpl.
f_equal; f_equal.
 unfold I_add_wn_i.
 rewrite Hxy; reflexivity.

 unfold carry; simpl.
 erewrite fst_not_1_add_wn_eqs_compat; [ idtac | eassumption ].
 remember (fst_not_1 (I_add_wn y 0) (S i)) as s1 eqn:Hs1 .
 apply fst_not_1_iff in Hs1; simpl in Hs1.
 destruct s1 as [di1| ]; [ idtac | reflexivity ].
 destruct Hs1 as (Hn1, Ht1).
 unfold I_add_wn_i; simpl.
 rewrite Hxy; reflexivity.
Qed.

(* compatibilities with I_eq_wn *)

Theorem fst_not_1_eq_wn_compat : ∀ x y,
  I_eq_wn x y
  → (∀ i, fst_not_1 x i = fst_not_1 y i).
Proof.
intros x y Hxy i.
apply fst_not_1_iff; simpl.
remember (fst_not_1 x i) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 split.
  intros dj Hdj.
  rewrite <- Hxy.
  apply Hn1; assumption.

  rewrite <- Hxy; assumption.

 intros dj.
 rewrite <- Hxy; apply Hs1.
Qed.

Theorem carry_eq_wn_compat : ∀ x y,
  I_eq_wn x y
  → ∀ i, carry x i = carry y i.
Proof.
intros x y Hxy i.
unfold carry; simpl.
erewrite fst_not_1_eq_wn_compat; [ idtac | eassumption ].
remember (fst_not_1 y i) as s1 eqn:Hs1 .
destruct s1 as [di1| ]; [ idtac | reflexivity ].
rewrite Hxy; reflexivity.
Qed.

Theorem Iwn2I_eq_wn_compat : ∀ x y,
  I_eq_wn x y
  → ∀ i, Iwn2I x i = Iwn2I y i.
Proof.
intros x y Hxy i.
unfold Iwn2I.
rewrite Hxy; f_equal; f_equal.
apply carry_eq_wn_compat; assumption.
Qed.

(* commutativity *)

Theorem I_eqs_add_comm : ∀ x y, I_eqs (x + y) (y + x).
Proof.
intros x y.
unfold I_eqs; simpl; intros i.
apply Iwn2I_eq_wn_compat.
clear i; intros i.
unfold I_add_wn; simpl.
apply Nat.add_comm.
Qed.

Theorem I_add_comm : ∀ x y, (x + y = y + x)%I.
Proof.
intros x y.
apply I_eqs_eq, I_eqs_add_comm.
Qed.

(* compatibility *)

Definition I2Iwn x := {| inat i := b2n (x.[i]) |}.

Theorem fst_not_1_add_wn_0_r : ∀ x i,
  fst_not_1 (I_add_wn x 0) i = fst_not_1 (I2Iwn x) i.
Proof.
intros x i.
apply fst_not_1_iff; simpl.
remember (fst_not_1 (I_add_wn x 0) i) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Ht1).
 split.
  intros dj Hdj.
  apply Hn1 in Hdj; simpl in Hdj.
  unfold I_add_wn_i in Hdj; simpl in Hdj.
  rewrite Nat.add_0_r in Hdj; assumption.

  unfold I_add_wn_i in Ht1; simpl in Ht1.
  rewrite Nat.add_0_r in Ht1; assumption.

 intros dj.
 pose proof (Hs1 dj) as Hdj.
 unfold I_add_wn_i in Hdj; simpl in Hdj.
 rewrite Nat.add_0_r in Hdj; assumption.
Qed.

Theorem carry_add_wn_0_r : ∀ x i, carry (I_add_wn x 0) i = carry (I2Iwn x) i.
Proof.
intros x i.
unfold carry; simpl.
rewrite fst_not_1_add_wn_0_r.
remember (fst_not_1 (I2Iwn x) i) as s1 eqn:Hs1 .
destruct s1 as [di1| ]; [ idtac | reflexivity ].
unfold I_add_wn_i; simpl.
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem I_add_wn_0_r : ∀ x i, I_add_wn_i x 0 i = b2n (x.[i]).
Proof.
intros x i.
unfold I_add_wn_i; simpl.
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem b2n_0_iff : ∀ b, b2n b = 0 ↔ b = false.
Proof.
intros b; split; intros H; [ idtac | subst b; reflexivity ].
destruct b; [ discriminate H | reflexivity ].
Qed.

Theorem b2n_1_iff : ∀ b, b2n b = 1 ↔ b = true.
Proof.
intros b; split; intros H; [ idtac | subst b; reflexivity ].
destruct b; [ reflexivity | discriminate H ].
Qed.

Theorem b2n_not_1_iff : ∀ b, b2n b ≠ 1 ↔ b = false.
Proof.
intros b; split; intros H; [ idtac | subst b; intros H; discriminate H ].
destruct b; [ exfalso; apply H; reflexivity | reflexivity ].
Qed.

Theorem negb_inj : ∀ a b, negb a = negb b → a = b.
Proof.
intros a b H.
destruct a, b; try reflexivity; discriminate H.
Qed.

Theorem carry_before_relay : ∀ x i di,
  Some di = fst_not_1 (I2Iwn x) i
  → ∀ dj, dj ≤ di → carry (I2Iwn x) (i + dj) = b2n (x.[i + di]).
Proof.
intros x i di Hs dj Hdj.
unfold carry; simpl.
remember (fst_not_1 (I2Iwn x) (i + dj)) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs; simpl in Hs.
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct Hs as (Hn, Ht).
apply b2n_not_1_iff in Ht.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Ht1).
 apply b2n_not_1_iff in Ht1.
 rewrite Ht, Ht1; reflexivity.

 pose proof (Hs1 (di - dj)) as H.
 rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
 rewrite Nat.add_shuffle0, Nat.add_sub in H.
 rewrite Ht in H; discriminate H.
Qed.

Theorem carry_before_inf_relay : ∀ x i,
  None = fst_not_1 (I2Iwn x) i
  → ∀ dj, carry (I2Iwn x) (i + dj) = 1.
Proof.
intros x i Hs dj.
unfold carry; simpl.
remember (fst_not_1 (I2Iwn x) (i + dj)) as s1 eqn:Hs1 .
destruct s1 as [di1| ]; [ idtac | reflexivity ].
apply fst_not_1_iff in Hs; simpl in Hs.
rewrite <- Nat.add_assoc; apply Hs.
Qed.

Theorem I_eq_neq_if : ∀ x y i,
  (x = y)%I
  → x.[i] = true
  → y.[i] = false
  → (∀ di, x.[i+di] = true) ∧ (∀ di, y.[i+di] = false) ∨
    (∀ di, x.[i+S di] = false) ∧ (∀ di, y.[i+S di] = true).
Proof.
intros x y i Hxy Hx Hy.
remember Hxy as Heq; clear HeqHeq.
unfold I_eq in Hxy; simpl in Hxy.
pose proof (Hxy i) as H.
unfold Iwn2I, I_add_wn_i in H; simpl in H.
do 2 rewrite carry_add_wn_0_r in H.
unfold I_add_wn_i in H; simpl in H.
do 2 rewrite Nat.add_0_r in H; simpl in H.
rewrite Hx, Hy, xorb_true_l, xorb_false_l in H.
unfold carry in H; simpl in H.
remember (fst_not_1 (I2Iwn x) (S i)) as sx eqn:Hsx .
remember (fst_not_1 (I2Iwn y) (S i)) as sy eqn:Hsy .
destruct sx as [dx| ].
 remember Hsx as HH; clear HeqHH.
 apply fst_not_1_iff in HH; simpl in HH.
 destruct HH as (Hnx, Htx).
 apply b2n_not_1_iff in Htx; rewrite Htx in H.
 destruct sy as [dy| ]; [ idtac | clear H ].
  remember Hsy as HH; clear HeqHH.
  apply fst_not_1_iff in HH; simpl in HH.
  destruct HH as (Hny, Hty).
  apply b2n_not_1_iff in Hty; rewrite Hty in H.
  discriminate H.

  right.
  remember Hsy as Hny; clear HeqHny.
  apply fst_not_1_iff in Hny; simpl in Hny.
  split; intros di.
   destruct (lt_eq_lt_dec di dx) as [[H1| H1]| H1].
    pose proof (Hnx di H1) as H.
    rename H into Hdi.
    destruct dx; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
    apply b2n_1_iff in Hdi.
    pose proof (Hxy (S (i + dx))%nat) as H.
    unfold Iwn2I in H; simpl in H.
    do 2 rewrite I_add_wn_0_r in H.
    rewrite Hnx in H; [ idtac | apply Nat.lt_succ_diag_r ].
    rewrite Hny in H.
    do 2 rewrite xorb_false_l, carry_add_wn_0_r in H.
    rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H.
    erewrite carry_before_relay in H; [ idtac | eassumption | auto ].
    erewrite carry_before_inf_relay in H; [ idtac | eassumption ].
    simpl in H; rewrite Htx in H; discriminate H.

    subst di.
    rewrite Nat.add_succ_r; assumption.

    remember (di - S dx)%nat as n eqn:Hn .
    apply nat_sub_add_r in Hn; [ idtac | assumption ].
    subst di; clear H1.
    rewrite Nat.add_succ_r.
    induction n as (n, IHn) using all_lt_all.
    destruct n.
     rewrite Nat.add_succ_r.
     rewrite Nat.add_0_r.
     apply negb_inj, neq_negb; intros Hdi.
     apply negb_false_iff in Hdi.
     pose proof (Hxy (S (i + dx))) as H.
     unfold Iwn2I in H; simpl in H.
     do 2 rewrite I_add_wn_0_r, carry_add_wn_0_r in H.
     rewrite Htx, Hny in H.
     rewrite xorb_false_l, xorb_true_l in H.
     rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H.
     symmetry in H.
     erewrite carry_before_inf_relay in H; [ idtac | eassumption ].
     unfold carry in H; simpl in H.
     remember (fst_not_1 (I2Iwn x) (S (i + S dx))) as s1 eqn:Hs1 .
     destruct s1 as [di1| ]; [ idtac | discriminate H ].
     rename H into Hx1.
     destruct di1.
      rewrite Nat.add_0_r in Hx1.
      rewrite Hdi in Hx1; discriminate Hx1.

      remember Hs1 as H; clear HeqH.
      apply fst_not_1_iff in H; simpl in H.
      destruct H as (Hn1, _).
      pose proof (Hxy (S (S (i + dx)))) as H.
      unfold Iwn2I in H; simpl in H.
      do 2 rewrite I_add_wn_0_r, carry_add_wn_0_r in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hdi, Hny in H.
      do 2 rewrite xorb_false_l in H.
      rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H.
      symmetry in H.
      erewrite carry_before_inf_relay in H; [ idtac | eassumption ].
      symmetry in H.
      assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
      rewrite Nat.add_succ_l, Nat.add_succ_r, <- Nat.add_1_r in H.
      erewrite carry_before_relay in H; [ idtac | eassumption | auto ].
      simpl in H; rewrite H in Hx1; discriminate Hx1.

     rewrite Nat.add_succ_r.
     rewrite <- negb_involutive.
     apply neq_negb; simpl; intros Hdi.
     pose proof (Hxy (S (i + dx + S n))) as H.
     unfold Iwn2I in H; simpl in H.
     do 2 rewrite I_add_wn_0_r, carry_add_wn_0_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite IHn in H; [ idtac | apply Nat.lt_succ_diag_r ].
     rewrite Hny, xorb_false_l, xorb_true_l in H.
     symmetry in H.
     rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H.
     erewrite carry_before_inf_relay in H; [ idtac | eassumption ].
     unfold carry in H; simpl in H.
     remember (fst_not_1 (I2Iwn x) (S (i + S (dx + S n)))) as s1 eqn:Hs1 .
     destruct s1 as [di1| ]; [ idtac | discriminate H ].
     rename H into Hx1.
     destruct di1.
      rewrite Nat.add_0_r in Hx1.
      rewrite Hdi in Hx1; discriminate Hx1.

      remember Hs1 as H; clear HeqH.
      apply fst_not_1_iff in H; simpl in H.
      destruct H as (Hn1, _).
      pose proof (Hxy (S (S (i + dx + S n)))) as H.
      unfold Iwn2I in H; simpl in H.
      do 2 rewrite I_add_wn_0_r, carry_add_wn_0_r in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Nat.add_assoc in H.
      rewrite Nat.add_succ_r in H.
      rewrite Hdi, Hny in H.
      symmetry in H.
      rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H.
      erewrite carry_before_inf_relay in H; [ idtac | eassumption ].
      symmetry in H.
      rewrite Nat.add_succ_l, Nat.add_succ_r, <- Nat.add_1_r in H.
      assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
      erewrite carry_before_relay in H; [ idtac | eassumption | auto ].
      rewrite Nat.add_succ_l in H.
      apply negb_sym in Hx1.
      rewrite Hx1 in H; discriminate H.

   rewrite Nat.add_succ_r; simpl; apply b2n_1_iff, Hny.

 destruct sy as [dy| ]; [ idtac | discriminate H ].
 symmetry in H; simpl in H.
 remember Hsy as HH; clear HeqHH.
 apply fst_not_1_iff in HH; simpl in HH.
 destruct HH as (Hny, Hty); clear H.
 left.
 remember Hsx as Hnx; clear HeqHnx.
 apply fst_not_1_iff in Hnx; simpl in Hnx.
 split; intros di.
  destruct (lt_eq_lt_dec di dy) as [[H1| H1]| H1].
   pose proof (Hny di H1) as H.
   destruct dy; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
   rename H into Hdi.
   pose proof (Hxy (S (i + dy))%nat) as H.
   unfold Iwn2I in H; simpl in H.
   do 2 rewrite I_add_wn_0_r, carry_add_wn_0_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H.
   symmetry in H.
   erewrite carry_before_relay in H; [ idtac | eassumption | auto ].
   erewrite carry_before_inf_relay in H; [ idtac | eassumption ].
   apply b2n_not_1_iff in Hty.
   rewrite Nat.add_succ_l, Hty in H.
   discriminate H.

   subst di.
   destruct dy; [ rewrite Nat.add_0_r; assumption | idtac ].
   rewrite Nat.add_succ_r; apply b2n_1_iff, Hnx.

   destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
   rewrite Nat.add_succ_r; apply b2n_1_iff, Hnx.

  destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
  rewrite Nat.add_succ_r.
  destruct (lt_eq_lt_dec di dy) as [[H1| H1]| H1].
   pose proof (Hny di H1) as H.
   destruct dy; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
   rename H into Hdi.
   pose proof (Hxy (S (i + dy))%nat) as H.
   unfold Iwn2I in H; simpl in H.
   do 2 rewrite I_add_wn_0_r, carry_add_wn_0_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H.
   symmetry in H.
   erewrite carry_before_relay in H; [ idtac | eassumption | auto ].
   rewrite carry_before_inf_relay in H; [ idtac | assumption ].
   apply b2n_not_1_iff in Hty.
   simpl in H; rewrite Hty in H; discriminate H.

   apply b2n_not_1_iff in Hty.
   subst di; assumption.

   remember (di - S dy)%nat as n eqn:Hn .
   apply nat_sub_add_r in Hn; [ idtac | assumption ].
   subst di; clear H1.
   rewrite Nat.add_succ_r.
   induction n as (n, IHn) using all_lt_all.
   destruct n; [ clear IHn | idtac ].
    rewrite Nat.add_succ_r.
    rewrite <- negb_involutive.
    apply neq_negb; simpl; intros Hdi.
    rewrite Nat.add_0_r in Hdi.
    pose proof (Hxy (S (i + dy))) as H.
bbb.
    pose proof (Hxy (S (i + dy))) as H.
    unfold I_add_i in H; simpl in H.
    do 2 rewrite xorb_false_r in H.
    rewrite Hnx, Hty, xorb_false_l, xorb_true_l in H.
    symmetry in Hsx, Hsy.
    rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
    symmetry in H.
    unfold carry in H; simpl in H.
    remember (fst_same y 0 (S (S (i + dy)))) as s1 eqn:Hs1 .
    destruct s1 as [di1| ]; [ idtac | discriminate H ].
    rename H into Hx1.
    destruct di1.
     rewrite Nat.add_0_r in Hx1.
     rewrite Hdi in Hx1; discriminate Hx1.

     remember Hs1 as H; clear HeqH.
     apply fst_not_1_iff in H; simpl in H.
     destruct H as (Hn1, _).
     pose proof (Hxy (S (S (i + dy)))) as H.
     unfold I_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite <- Nat.add_succ_r in H.
     pose proof (Hn1 O (Nat.lt_0_succ di1)) as HH.
     rewrite Nat.add_0_r, <- Nat.add_succ_r in HH.
     rewrite HH, Hnx, xorb_true_l in H.
     apply negb_sym in H.
     rewrite negb_involutive in H.
     rewrite <- Nat.add_succ_l in H.
     symmetry in H.
     rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     symmetry in H, Hs1.
     replace dy with (dy + 0)%nat in H by apply Nat.add_0_r.
     simpl in H.
     rewrite Nat.add_succ_r, Nat.add_assoc in H.
     do 2 rewrite <- Nat.add_succ_l in H.
     clear HH.
     assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H.
     rewrite Hx1 in H; discriminate H.

    rewrite Nat.add_succ_r.
    rewrite <- negb_involutive.
    apply neq_negb; simpl; intros Hdi.
    pose proof (Hxy (S (i + dy + S n))) as H.
    unfold I_add_i in H; simpl in H.
    do 2 rewrite xorb_false_r in H.
    rewrite <- Nat.add_assoc in H.
    pose proof (IHn n (Nat.lt_succ_diag_r n)) as HH.
    rewrite <- Nat.add_succ_r in HH.
    rewrite <- Nat.add_succ_r in HH.
    rewrite Nat.add_succ_r in HH.
    rewrite Hnx, HH, xorb_false_l, xorb_true_l in H.
    symmetry in Hsx, Hsy.
    rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
    symmetry in H.
    unfold carry in H; simpl in H.
    remember (fst_same y 0 (S (S (i + (dy + S n))))) as s1 eqn:Hs1 .
    destruct s1 as [di1| ]; [ idtac | discriminate H ].
    rename H into Hx1.
    destruct di1.
     rewrite Nat.add_0_r in Hx1.
     rewrite Hdi in Hx1; discriminate Hx1.

     remember Hs1 as H; clear HeqH.
     apply fst_not_1_iff in H; simpl in H.
     destruct H as (Hn1, _).
     pose proof (Hxy (S (S (i + dy + S n)))) as H.
     unfold I_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite Hdi in H.
     rewrite <- Nat.add_succ_r in H.
     rewrite Hnx, xorb_true_l in H.
     rewrite <- Nat.add_succ_l in H.
     erewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     apply negb_sym in H; simpl in H.
     rewrite Nat.add_succ_r in H.
     remember (S (S (i + (dy + S n)))) as z.
     replace z with (z + 0)%nat in H by apply Nat.add_0_r.
     subst z.
     symmetry in Hs1.
     assert (0 < S di1)%nat as HHH by apply Nat.lt_0_succ.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H.
     rewrite Hx1 in H; discriminate H.
Qed.

Theorem I_add_compat_r : ∀ x y z, (x = y)%I → (x + z = y + z)%I.
Proof.
intros x y z Hxy.
remember Hxy as Heq; clear HeqHeq.
unfold I_eq.
apply Iwn2I_eq_wn_compat.
unfold I_eq_wn; simpl; intros i.
unfold I_add_wn_i; simpl.
f_equal; f_equal.
unfold Iwn2I; simpl.
unfold I_eq in Hxy; simpl in Hxy.
unfold Iwn2I in Hxy; simpl in Hxy.
pose proof (Hxy i) as Hi.
do 2 rewrite I_add_wn_0_r in Hi.
do 2 rewrite carry_add_wn_0_r in Hi.
unfold I_add_wn_i; simpl.
remember (Nat.eqb (b2n (x .[ i]) + b2n (z .[ i])) 0) as b1 eqn:Hb1 .
remember (Nat.eqb (b2n (y .[ i]) + b2n (z .[ i])) 0) as b2 eqn:Hb2 .
symmetry in Hb1, Hb2.
destruct b1.
 apply beq_nat_true_iff in Hb1.
 apply Nat.eq_add_0 in Hb1.
 destruct Hb1 as (Hx, Hz).
 rewrite Hz in Hb2; simpl in Hb2.
 rewrite Nat.add_0_r in Hb2.
 destruct b2.
  apply beq_nat_true_iff in Hb2; simpl in Hb2.
  rename Hb2 into Hy; f_equal.
  apply b2n_0_iff in Hx.
  apply b2n_0_iff in Hy.
  apply b2n_0_iff in Hz.
  rewrite Hx, Hy in Hi.
  rewrite xorb_true_l in Hi; symmetry in Hi.
  rewrite xorb_true_l in Hi; symmetry in Hi.
  apply negb_inj in Hi.
  f_equal.
  unfold carry; simpl.
  remember (fst_not_1 (I_add_wn x z) (S i)) as s1 eqn:Hs1 .
  remember (fst_not_1 (I_add_wn y z) (S i)) as s2 eqn:Hs2 .
  apply fst_not_1_iff in Hs1; simpl in Hs1.
  apply fst_not_1_iff in Hs2; simpl in Hs2.
  destruct s1 as [di1| ].
   destruct Hs1 as (Hn1, Ht1).
   unfold I_add_wn_i in Ht1; simpl in Ht1.
   destruct s2 as [di2| ].
    destruct Hs2 as (Hn2, Ht2).
    unfold I_add_wn_i in Ht2; simpl in Ht2.
    unfold I_add_wn_i; simpl.
    unfold carry in Hi; simpl in Hi.
    remember (fst_not_1 (I2Iwn x) (S i)) as s3 eqn:Hs3 .
    remember (fst_not_1 (I2Iwn y) (S i)) as s4 eqn:Hs4 .
    apply fst_not_1_iff in Hs3; simpl in Hs3.
    apply fst_not_1_iff in Hs4; simpl in Hs4.
    destruct s3 as [di3| ].
     destruct Hs3 as (Hn3, Ht3).
     apply b2n_not_1_iff in Ht3.
     destruct s4 as [di4| ].
      destruct Hs4 as (Hn4, Ht4).
      apply b2n_not_1_iff in Ht4.
      destruct (lt_eq_lt_dec di1 di2) as [[H1| H1]| H1].
       remember H1 as H; clear HeqH.
       apply Hn2 in H.
       unfold I_add_wn_i in H; simpl in H.
       apply Nat.eq_add_1 in H.
       destruct H as [(Hy1, Hz1)| (Hy1, Hz1)].
        rewrite Hz1, Nat.add_0_r in Ht1.
        apply b2n_not_1_iff in Ht1.
        rewrite Ht1, Hz1; simpl.
        symmetry.
        apply Nat.eq_add_0.
        unfold I_add_wn_i in Hxy; simpl in Hxy.
        destruct (lt_eq_lt_dec di2 di4) as [[H2| H2]| H2].
         remember H2 as H; clear HeqH.
         apply Hn4 in H.
         rewrite H in Ht2; simpl in Ht2.
         rename H into Hy2.
         apply b2n_1_iff in Hy1.
bbb.
  Ht1 : x .[ S (i + di1)] = false
  Hy1 : y .[ S (i + di1)] = true
  Heq : (x = y)%I

   i   -  di1  -  di2  -  di4
x  0   .   0   .   .   .   .
y  0   1   1   1   1   1   0
z  0   .   0   .   1   .   .

         pose proof (Hxy (S (i + di1))) as H.
         rewrite Ht1, xorb_true_l in H.
         rewrite Hy1, xorb_false_l in H.
bbb.

(* associativity *)

Definition Iwn_add_i x y i := inat x i + inat y i.
Definition Iwn_add x y := {| inat := Iwn_add_i x y |}.

Theorem I_eq_wn_I_add : ∀ x y,
  I_eq_wn (I_add_wn x y) (Iwn_add (I2Iwn x) (I2Iwn y)).
Proof. intros x y; unfold I_eq_wn; reflexivity. Qed.

Definition n2b n := negb (Nat.eqb n 0).

Theorem I_add_assoc : ∀ x y z, (x + (y + z) = (x + y) + z)%I.
Proof.
intros x y z.
unfold I_eq.
apply Iwn2I_eq_wn_compat.
unfold I_eq_wn; simpl; intros i.
unfold I_add_wn_i; simpl.
f_equal; f_equal.
apply Iwn2I_eq_wn_compat; clear i.
unfold I_eq_wn; intros i.
unfold I_add_wn; simpl.
unfold I_add_wn_i; simpl.
erewrite Iwn2I_eq_wn_compat; [ symmetry | apply I_eq_wn_I_add ].
erewrite Iwn2I_eq_wn_compat; [ symmetry | apply I_eq_wn_I_add ].
bbb.

Close Scope nat_scope.
