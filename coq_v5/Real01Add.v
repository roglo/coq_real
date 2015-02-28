(* addition modulo 1 in I *)

Require Import Utf8 QArith NPeano Misc.
Require Import Oracle Digit Real01.

Open Scope nat_scope.

Definition Isum2Un x y i j :=
  if digit_eq_dec (x.[i+j]) (y.[i+j]) then 1 else 0.

Definition fst_same x y i :=
  match first_nonzero (Isum2Un x y i) with
  | Some di => Some di
  | None => None
  end.

Theorem fst_same_iff : ∀ x y i odi, fst_same x y i = odi ↔
  match odi with
  | Some di =>
      (∀ dj, dj < di → (x.[i + dj] = oppd (y.[i + dj]))%D)
      ∧ (x.[i + di] = y.[i + di])%D
  | None =>
      ∀ dj, (x.[i + dj] = oppd (y.[i + dj]))%D
  end.
Proof.
intros x y i odi.
split; intros Hi.
 subst odi.
 unfold fst_same; simpl.
 remember (first_nonzero (Isum2Un x y i)) as s1 eqn:Hs1 .
 apply first_nonzero_iff in Hs1; simpl in Hs1.
 unfold Isum2Un in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Ht1).
  destruct (digit_eq_dec (x .[ i + di1]) (y .[ i + di1])) as [H1| H1].
   split; [ idtac | assumption ].
   intros dj Hdj.
   remember Hdj as H; clear HeqH.
   apply Hn1 in H.
   destruct (digit_eq_dec (x .[ i + dj]) (y .[ i + dj])) as [H2| H2].
    discriminate H.

    apply digit_neq_eq_opp; assumption.

   exfalso; apply Ht1; reflexivity.

  intros dj.
  pose proof (Hs1 dj) as H.
  destruct (digit_eq_dec (x .[ i + dj]) (y .[ i + dj])) as [H2| H2].
   discriminate H.

   apply digit_neq_eq_opp; assumption.

 unfold fst_same; simpl.
 remember (first_nonzero (Isum2Un x y i)) as s1 eqn:Hs1 .
 apply first_nonzero_iff in Hs1; simpl in Hs1.
 unfold Isum2Un in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Ht1).
  destruct odi as [di| ].
   destruct Hi as (Hn, Ht).
   destruct (digit_eq_dec (x .[ i + di1]) (y .[ i + di1])) as [H2| H2].
    destruct (lt_eq_lt_dec di di1) as [[H1| H1]| H1].
     remember H1 as H; clear HeqH.
     apply Hn1 in H.
     destruct (digit_eq_dec (x .[ i + di]) (y .[ i + di])) as [H3| H3].
      discriminate H.

      contradiction.

     subst di; reflexivity.

     remember H1 as H; clear HeqH.
     apply Hn in H.
     rewrite H in H2.
     exfalso; revert H2; apply no_fixpoint_oppd.

    exfalso; apply Ht1; reflexivity.

   destruct (digit_eq_dec (x .[ i + di1]) (y .[ i + di1])) as [H2| H2].
    rewrite Hi in H2.
    exfalso; revert H2; apply no_fixpoint_oppd.

    exfalso; apply Ht1; reflexivity.

  destruct odi as [di| ]; [ idtac | reflexivity ].
  destruct Hi as (Hn, Ht).
  pose proof (Hs1 di) as H.
  destruct (digit_eq_dec (x .[ i + di]) (y .[ i + di])) as [H2| H2].
   discriminate H.

   contradiction.
Qed.

Definition carry x y i :=
  match fst_same x y i with
  | Some dj => x.[i + dj]
  | None => 1%D
  end.

Definition I_add_i x y i := (x.[i] + y.[i] + carry x y (S i))%D.
Definition I_add x y := {| rm := I_add_i x y |}.

Notation "x + y" := (I_add x y) : I_scope.

Definition I_eq x y := I_eq_ext (x + 0%I) (y + 0%I).

Notation "x = y" := (I_eq x y) : I_scope.
Notation "x ≠ y" := (¬ I_eq x y) : I_scope.

Arguments carry x%I y%I i%nat.
Arguments I_add_i x%I y%I i%nat.
Arguments I_add x%I y%I.
Arguments I_eq x%I y%I.
Arguments fst_same x%I y%I i%nat.

Definition I_opp x := {| rm i := oppd (x.[i]) |}.
Definition I_sub x y := I_add x (I_opp y).

Notation "- x" := (I_opp x) : I_scope.
Notation "x - y" := (I_sub x y) : I_scope.

Theorem fold_I_sub : ∀ x y, (x + - y)%I = (x - y)%I.
Proof. intros; reflexivity. Qed.

Theorem fst_same_sym_iff : ∀ x y i odi,
  odi = fst_same x y i
  ↔ match odi with
    | Some di =>
        (∀ dj : nat, dj < di → (x .[ i + dj] = oppd (y.[i + dj]))%D)
        ∧ (x .[ i + di] = y .[ i + di])%D
    | None => ∀ dj : nat, (x .[ i + dj] = oppd (y.[i + dj]))%D
    end.
Proof.
intros x y i odi.
split; intros H.
 apply fst_same_iff; symmetry; assumption.

 symmetry; apply fst_same_iff; assumption.
Qed.

Theorem carry_compat_r : ∀ x y z j,
  I_eq_ext x y
  → (carry x z j = carry y z j)%D.
Proof.
intros x y z j Hxy; symmetry.
unfold I_eq_ext in Hxy.
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
   rewrite Hxy, Hs1 in H; symmetry in H.
   exfalso; revert H; apply no_fixpoint_oppd.

   apply Nat.nlt_ge in H1.
   destruct (lt_dec di2 di1) as [H2| H2].
    remember H2 as H; clear HeqH.
    apply Hn1 in H.
    rewrite <- Hxy, Hs2 in H; symmetry in H.
    exfalso; revert H; apply no_fixpoint_oppd.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H1; [ idtac | assumption ].
    subst di1; reflexivity.

  rewrite <- Hxy, Hs2 in Hs1.
  exfalso; revert Hs1; apply no_fixpoint_oppd.

 destruct s2 as [di2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Hs2).
 rewrite Hxy, Hs1 in Hs2.
 exfalso; revert Hs2; apply no_fixpoint_oppd.
Qed.

Theorem I_eq_ext_eq : ∀ x y, I_eq_ext x y → (x = y)%I.
Proof.
intros x y Hxy.
unfold I_eq_ext in Hxy.
unfold I_eq; intros i; simpl.
unfold I_add_i; simpl.
rewrite Hxy.
rewrite carry_compat_r; [ reflexivity | assumption ].
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

Theorem I_zero_iff : ∀ x,
  (x = 0)%I ↔
  (∀ i, (x.[i] = 0)%D) ∨ (∀ i, (x.[i] = 1)%D).
Proof.
intros x.
split.
 intros Hx.
 destruct (digit_eq_dec (x .[ 0]) 0%D) as [Hb| Hb].
  left; intros i.
  induction i; [ assumption | idtac ].
  pose proof (Hx i) as Hi; simpl in Hi.
  unfold I_add_i in Hi; simpl in Hi.
  rewrite carry_diag in Hi; simpl in Hi.
  do 3 rewrite digit_add_0_r in Hi.
  rewrite IHi, digit_add_0_l in Hi.
  unfold carry in Hi; simpl in Hi.
  remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
  destruct s1 as [dj1| ].
   pose proof (Hx (S i)) as Hsi; simpl in Hsi.
   unfold I_add_i in Hsi; simpl in Hsi.
   rewrite carry_diag in Hsi; simpl in Hsi.
   do 3 rewrite digit_add_0_r in Hsi.
   unfold carry in Hsi; simpl in Hsi.
   remember (fst_same x 0 (S (S i))) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s2 as [dj2| ].
    destruct Hs2 as (Hn2, Ht2).
    rewrite Ht2 in Hsi.
    rewrite digit_add_0_r in Hsi; assumption.

    destruct dj1; [ rewrite Nat.add_0_r in Hi; assumption | idtac ].
    pose proof (Hs2 dj1) as H.
    rewrite Nat.add_succ_r, H in Hi.
    exfalso; revert Hi; apply no_fixpoint_oppd.

   exfalso; revert Hi; apply digit_neq_1_0.

  right; intros i.
  induction i; [ apply digit_not_0_iff_1; assumption | idtac ].
  pose proof (Hx i) as Hi; simpl in Hi.
  unfold I_add_i in Hi; simpl in Hi.
  rewrite carry_diag in Hi; simpl in Hi.
  do 3 rewrite digit_add_0_r in Hi.
  rewrite IHi in Hi.
  unfold carry in Hi; simpl in Hi.
  remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ]; [ idtac | clear Hi ].
   destruct Hs1 as (Hn1, Hs1).
   rewrite Hs1, digit_add_0_r in Hi.
   exfalso; revert Hi; apply digit_neq_1_0.

   pose proof (Hs1 O) as H; rewrite Nat.add_0_r in H.
   assumption.

 intros [Hx| Hx].
  unfold I_eq; intros i; simpl.
  unfold I_add_i; simpl.
  rewrite digit_add_0_r, carry_diag; simpl.
  rewrite Hx, digit_add_0_l.
  do 2 rewrite digit_add_0_r.
  unfold carry; simpl.
  remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ].
   destruct Hs1; assumption.

   pose proof (Hs1 O) as H.
   rewrite Hx in H.
   exfalso; revert H; apply digit_neq_0_1.

  unfold I_eq; intros i; simpl.
  unfold I_add_i; simpl.
  rewrite digit_add_0_r, carry_diag; simpl.
  rewrite Hx, digit_add_1_l.
  do 2 rewrite digit_add_0_r.
  apply oppd_0_iff.
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
Proof.
intros x y z Hxy Hyz i.
unfold I_eq, I_eq_ext in Hxy.
rewrite Hxy; apply Hyz.
Qed.

Add Parametric Relation : _ I_eq
 reflexivity proved by I_eq_refl
 symmetry proved by I_eq_sym
 transitivity proved by I_eq_trans
 as I_rel.

(* *)

Theorem forall_and_distr : ∀ α (P Q : α → Prop),
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x).
Proof. intros; split; intros x; apply H. Qed.

Theorem lt_add_sub_lt_r : ∀ a b c d,
  a < b + c
  → d < c
  → a - b < c.
Proof.
intros a b c d Ha Hdc.
revert b c Ha Hdc.
induction a; intros.
 simpl.
 eapply le_lt_trans; [ apply Nat.le_0_l | eassumption ].

 destruct b; [ rewrite Nat.sub_0_r; assumption | simpl ].
 simpl in Ha.
 apply Nat.succ_lt_mono in Ha.
 apply IHa; assumption.
Qed.

Theorem lt_add_sub_lt_l : ∀ a b c,
  a < b + c
  → b < S a
  → a - b < c.
Proof.
intros a b c Ha Hb.
revert b c Ha Hb.
induction a; intros.
 apply Nat.lt_1_r in Hb; subst b; assumption.

 destruct b; [ rewrite Nat.sub_0_r; assumption | simpl ].
 simpl in Ha.
 apply Nat.succ_lt_mono in Ha.
 apply Nat.succ_lt_mono in Hb.
 apply IHa; assumption.
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

(* commutativity *)

Theorem fst_same_comm : ∀ x y i, fst_same x y i = fst_same y x i.
Proof.
intros x y i.
apply fst_same_iff.
remember (fst_same y x i) as syx eqn:Hsyx .
symmetry in Hsyx.
apply fst_same_iff in Hsyx.
destruct syx as [di| ].
 destruct Hsyx as (Hns, Hs).
 split; [ idtac | symmetry; assumption ].
 intros dj Hdjn.
 apply oppd_sym, Hns; assumption.

 intros dj.
 apply oppd_sym, Hsyx; assumption.
Qed.

Theorem carry_comm : ∀ x y i, (carry x y i = carry y x i)%D.
Proof.
intros x y i.
unfold carry; simpl.
rewrite fst_same_comm.
remember (fst_same y x i) as s eqn:Hs .
destruct s as [di| ]; [ idtac | reflexivity ].
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct Hs; symmetry; assumption.
Qed.

Theorem I_add_i_comm : ∀ x y i, (I_add_i x y i = I_add_i y x i)%D.
Proof.
intros x y i.
unfold I_add_i, carry.
rewrite fst_same_comm.
remember (fst_same y x (S i)) as s eqn:Hs .
symmetry in Hs.
apply fst_same_iff in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Ht); rewrite Ht.
 apply digit_add_compat; [ apply digit_add_comm | reflexivity ].

 apply digit_add_compat; [ apply digit_add_comm | reflexivity ].
Qed.

Theorem carry_compat : ∀ x y z t j,
  (∀ i, (x .[ i] = z .[ i])%D)
  → (∀ i, (y .[ i] = t .[ i])%D)
  → (carry x y j = carry z t j)%D.
Proof.
intros x y z t j Hxz Hzt.
erewrite carry_compat_r.
 rewrite carry_comm; symmetry.
 rewrite carry_comm; symmetry.
 apply carry_compat_r; intros i.
 rewrite Hzt; reflexivity.

 intros i.
 rewrite Hxz; reflexivity.
Qed.

Theorem carry_comm_l : ∀ x y z i,
  (carry (x + y) z i = carry (y + x) z i)%D.
Proof.
intros x y z i.
apply carry_compat; [ apply I_add_i_comm | reflexivity ].
Qed.

Theorem carry_comm_r : ∀ x y z i,
  (carry x (y + z) i = carry x (z + y) i)%D.
Proof.
intros x y z i.
apply carry_compat; [ reflexivity | apply I_add_i_comm ].
Qed.

Theorem I_add_comm : ∀ x y, (x + y = y + x)%I.
Proof.
intros x y.
unfold I_eq; intros i; simpl.
unfold I_add_i; simpl.
rewrite I_add_i_comm, carry_comm_l.
reflexivity.
Qed.

(* neutral element *)

Theorem I_add_0_inf_1 : ∀ x i,
  (∀ dj, (I_add_i x 0 (i + dj) = 1)%D)
  → id (∀ dk, (x .[i + dk] = 1)%D).
Proof.
intros x i Hs dk.
revert i Hs.
induction dk; intros.
 rewrite Nat.add_0_r.
 pose proof (Hs 0) as H; simpl in H.
 rewrite Nat.add_0_r in H.
 unfold I_add_i, carry in H; simpl in H.
 rewrite digit_add_0_r in H.
 remember (fst_same x 0 (S i)) as s2 eqn:Hs2 .
 symmetry in Hs2.
 apply fst_same_iff in Hs2; simpl in Hs2.
 destruct s2 as [di2| ].
  destruct Hs2 as (Hn2, Hs2).
  rewrite Hs2, digit_add_0_r in H.
  assumption.

  rewrite digit_add_1_r in H.
  apply oppd_1_iff in H.
  pose proof (Hs 1) as H1; simpl in H1.
  unfold I_add_i, carry in H1; simpl in H1.
  rewrite digit_add_0_r in H1.
  remember (fst_same x 0 (S (i + 1))) as s3 eqn:Hs3 .
  symmetry in Hs3.
  apply fst_same_iff in Hs3; simpl in Hs3.
  destruct s3 as [di3| ].
   destruct Hs3 as (Hn3, Hs3).
   rewrite Hs3 in H1.
   rewrite digit_add_0_r in H1.
   pose proof (Hs2 (S di3)) as H2.
   rewrite <- Nat.add_assoc in Hs3.
   simpl in Hs3.
   rewrite Hs3 in H2; exfalso; revert H2; apply digit_neq_0_1.

   rewrite digit_add_1_r in H1.
   apply oppd_1_iff in H1.
   pose proof (Hs2 0) as H2.
   rewrite Nat.add_0_r in H2.
   rewrite Nat.add_1_r in H1.
   rewrite H1 in H2; exfalso; revert H2; apply digit_neq_0_1.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 apply IHdk; intros dj.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hs.
Qed.

Theorem not_I_add_0_inf_1 : ∀ x i, ¬ (∀ dj, (I_add_i x 0 (i + dj) = 1)%D).
Proof.
intros x i Hs.
rename Hs into Hs1.
remember Hs1 as H; clear HeqH.
apply I_add_0_inf_1 in H; unfold id in H.
rename H into Hk.
pose proof (Hs1 0) as H; simpl in H.
rewrite Nat.add_0_r in H.
unfold I_add_i, carry in H.
remember (S i) as si.
simpl in H.
rewrite digit_add_0_r in H.
remember (fst_same x 0 si) as s2 eqn:Hs2 .
symmetry in Hs2.
apply fst_same_iff in Hs2; simpl in Hs2.
destruct s2 as [di2| ].
 destruct Hs2 as (Hn2, Hs2).
 subst si.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hs2.
 rewrite Hk in Hs2; revert Hs2; apply digit_neq_1_0.

 rewrite digit_add_1_r in H.
 apply oppd_1_iff in H.
 rename H into H1.
 pose proof (Hk 0) as H; simpl in H.
 rewrite Nat.add_0_r in H.
 rewrite H1 in H; revert H; apply digit_neq_0_1.
Qed.

Theorem not_I_add_0_inf_1_succ : ∀ x i,
  ¬ (∀ dj, (I_add_i x 0 (i + S dj) = 1)%D).
Proof.
intros x i H.
eapply not_I_add_0_inf_1 with (i := S i); intros dj.
rewrite Nat.add_succ_l, <- Nat.add_succ_r.
apply H.
Qed.

Theorem I_add_i_0_r : ∀ x i, (I_add_i (x + 0%I) 0 i = I_add_i x 0 i)%D.
Proof.
intros x i.
unfold I_add_i at 1.
unfold carry.
remember (S i) as si; simpl.
rewrite digit_add_0_r.
remember (fst_same (x + 0%I) 0 si) as s1 eqn:Hs1 .
symmetry in Hs1.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hs1, digit_add_0_r; reflexivity.

 exfalso; eapply not_I_add_0_inf_1; eauto .
Qed.

Theorem I_add_0_r : ∀ x, (x + 0 = x)%I.
Proof.
intros x.
unfold I_eq, I_eq_ext.
apply I_add_i_0_r.
Qed.

(* compatibility with equality *)

Theorem I_add_i_compat_r : ∀ x y z,
  I_eq_ext x y
  → I_eq_ext (x + z) (y + z).
Proof.
intros x y z Hxy j; simpl.
unfold I_add_i.
unfold I_eq_ext in Hxy; rewrite Hxy.
apply digit_add_compat; [ reflexivity | idtac ].
apply carry_compat_r; assumption.
Qed.

Theorem I_add_i_compat : ∀ x y z t j,
  (∀ i, (x .[ i] = z .[ i])%D)
  → (∀ i, (y .[ i] = t .[ i])%D)
  → (I_add_i x y j = I_add_i z t j)%D.
Proof.
intros x y z t j Hxz Hyt.
unfold I_add_i.
rewrite Hxz, Hyt.
apply digit_add_compat; [ reflexivity | idtac ].
apply carry_compat; assumption.
Qed.

Theorem I_noI_eq_eq : ∀ x0 y0 x y,
  x = (x0 + 0)%I
  → y = (y0 + 0)%I
  → (x = y)%I
  → I_eq_ext x y.
Proof.
intros x0 y0 x y Ha Hb Hxy i.
unfold I_eq, I_eq_ext in Hxy; simpl in Hxy.
pose proof (Hxy i) as Hi.
unfold I_add_i, carry in Hi.
remember (S i) as si; simpl in Hi.
do 2 rewrite digit_add_0_r in Hi.
remember (fst_same x 0 si) as s1 eqn:Hs1 .
remember (fst_same y 0 si) as s2 eqn:Hs2 .
symmetry in Hs1, Hs2.
apply fst_same_iff in Hs1.
apply fst_same_iff in Hs2.
simpl in Hs1, Hs2.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hs1, digit_add_0_r in Hi.
 destruct s2 as [di2| ].
  destruct Hs2 as (Hn2, Hs2).
  rewrite Hs2, digit_add_0_r in Hi; assumption.

  exfalso; revert Hs2; rewrite Hb; apply not_I_add_0_inf_1.

 exfalso; revert Hs1; rewrite Ha; apply not_I_add_0_inf_1.
Qed.

Theorem carry_noI_eq_compat_r : ∀ x0 y0 x y z n,
  x = (x0 + 0)%I
  → y = (y0 + 0)%I
  → (x = y)%I
  → (carry (x + z) 0 n = carry (y + z) 0 n)%D.
Proof.
intros x0 y0 x y z n Ha Hb Hxy.
apply carry_compat_r; simpl.
apply I_add_i_compat_r.
eapply I_noI_eq_eq; eassumption.
Qed.

Theorem I_noI_eq_compat_r : ∀ x0 y0 x y z,
  x = (x0 + 0)%I
  → y = (y0 + 0)%I
  → (x = y)%I
  → (x + z = y + z)%I.
Proof.
intros x0 y0 x y z Ha Hb Hxy.
unfold I_eq; intros i; simpl.
unfold I_add_i; simpl.
do 2 rewrite digit_add_0_r.
apply digit_add_compat.
 apply I_add_i_compat_r.
 eapply I_noI_eq_eq; eassumption.

 eapply carry_noI_eq_compat_r; eassumption.
Qed.

Fixpoint first_0_before x i :=
  match i with
  | 0 => None
  | S j => if digit_eq_dec (x.[j]) 0 then Some j else first_0_before x j
  end.

Theorem first_0_before_none_iff : ∀ x i,
  first_0_before x i = None
  ↔ (∀ k, k < i → (x.[k] = 1)%D).
Proof.
intros x i.
split.
 intros Hi k Hki.
 revert k Hki.
 induction i; intros.
  exfalso; revert Hki; apply Nat.nlt_0_r.

  simpl in Hi.
  destruct (digit_eq_dec (x .[ i]) 0) as [H1| H1].
   discriminate Hi.

   destruct (eq_nat_dec k i) as [H2| H2].
    subst i; apply digit_not_0_iff_1; assumption.

    apply IHi; auto.
    apply Nat.nle_gt; intros H.
    apply Nat.succ_le_mono in Hki.
    apply Nat.le_antisymm in H; auto.

 intros Hki.
 induction i; [ reflexivity | simpl ].
 destruct (digit_eq_dec (x .[ i]) 0) as [H1| H1].
  rewrite Hki in H1; auto.
  exfalso; revert H1; apply digit_neq_1_0.

  apply IHi; intros k Hk.
  apply Hki, Nat.lt_le_incl, lt_n_S.
  assumption.
Qed.

Theorem first_0_before_some_iff : ∀ x i j,
  first_0_before x i = Some j
  ↔ j < i ∧
    (x.[j] = 0)%D ∧
    (∀ k, j < k → k < i → (x.[k] = 1)%D).
Proof.
intros x i j.
split.
 intros Hij.
 revert j Hij.
 induction i; intros; [ discriminate Hij | idtac ].
 simpl in Hij.
 destruct (digit_eq_dec (x .[ i]) 0) as [Hai| Hai].
  injection Hij; clear Hij; intros; subst j.
  split; [ apply Nat.lt_succ_r; auto | idtac ].
  split; [ assumption | idtac ].
  intros k Hik Hki.
  apply Nat.succ_le_mono, Nat.nlt_ge in Hki.
  contradiction.

  apply IHi in Hij.
  destruct Hij as (Hji, (Hj, Hk)).
  split; [ apply Nat.lt_lt_succ_r; auto | idtac ].
  split; [ assumption | idtac ].
  intros k Hjk Hki.
  destruct (eq_nat_dec k i) as [H1| H1].
   subst k; apply digit_not_0_iff_1; assumption.

   apply Hk; auto.
   apply Nat.succ_le_mono in Hki.
   apply Nat.nle_gt; intros H.
   apply Nat.le_antisymm in H; auto.

 intros (Hji, (Haj, Hjk)).
 revert j Hji Haj Hjk.
 induction i; intros; [ exfalso; revert Hji; apply Nat.nlt_0_r | simpl ].
 destruct (digit_eq_dec (x .[ i]) 0) as [Hai| Hai].
  apply Nat.succ_le_mono in Hji.
  destruct (le_dec i j) as [H1| H1].
   apply Nat.le_antisymm in H1; auto.

   apply Nat.nle_gt in H1.
   apply Hjk in H1; [ idtac | apply Nat.lt_succ_r; auto ].
   rewrite Hai in H1.
   exfalso; revert H1; apply digit_neq_0_1.

  apply IHi; auto.
  destruct (eq_nat_dec i j) as [H1| H1].
   subst j; rewrite Haj in Hai.
   exfalso; apply Hai; reflexivity.

   apply Nat.succ_le_mono in Hji.
   apply Nat.nle_gt; intros H.
   apply Nat.le_antisymm in H; auto.
Qed.

Theorem no_room_for_infinite_carry : ∀ x y i di1 di2 di3,
  (∀ dj : nat, dj < di2 → (I_add_i x 0 (S i + dj) = oppd (y .[ S i + dj]))%D)
  → (∀ dj : nat, (x .[ S (S i) + di2 + dj] = 1)%D)
  → (∀ dj : nat, dj < di3 → (x .[ S i + dj] = oppd (y .[ S i + dj]))%D)
  → (x .[ S i + di2] = 1)%D
  → (x .[ S i + di1] = 0)%D
  → di1 < di2
  → di2 < di3
  → False.
Proof.
intros x y i di1 di2 di3 Hn1 Hs4 Hn2 Hs1 Hs3 H4 H3.
remember (S i) as si.
remember (S si) as ssi.
remember (first_0_before x (si + di2)) as j eqn:Hj .
symmetry in Hj.
destruct j as [j| ].
 apply first_0_before_some_iff in Hj.
 destruct Hj as (Hji, (Hjf, Hk)).
 assert (i < j) as Hij.
  apply Nat.nle_gt; intros H.
  rewrite Hk in Hs3; [ revert Hs3; apply digit_neq_1_0 | idtac | idtac ].
   eapply Nat.le_lt_trans; eauto .
   rewrite Heqsi, Nat.add_succ_l, <- Nat.add_succ_r.
   apply Nat.lt_sub_lt_add_l.
   rewrite Nat.sub_diag.
   apply Nat.lt_0_succ.

   apply Nat.add_lt_mono_l; assumption.

  assert (j - si < di2) as H.
   apply Nat.add_lt_mono_r with (p := si).
   unfold lt in Hij; rewrite <- Heqsi in Hij.
   rewrite <- Nat.add_sub_swap; auto.
   rewrite Nat.add_sub, Nat.add_comm; assumption.

   apply Hn1 in H.
   unfold lt in Hij; rewrite <- Heqsi in Hij.
   rewrite Nat.add_sub_assoc in H; auto.
   rewrite Nat.add_comm, Nat.add_sub in H.
   unfold I_add_i, carry in H.
   remember (S j) as sj; simpl in H.
   rewrite Hjf, digit_add_0_r, digit_add_0_l in H.
   remember (fst_same x 0 sj) as s7 eqn:Hs7 .
   symmetry in Hs7.
   apply fst_same_iff in Hs7; simpl in Hs7.
   destruct s7 as [di7| ].
    destruct Hs7 as (Hn7, Hs7).
    rewrite Hs7 in H.
    symmetry in H.
    apply oppd_0_iff in H.
    rewrite Hk in Hs7; [ revert Hs7; apply digit_neq_1_0 | idtac | idtac ].
     rewrite Heqsj, Nat.add_succ_l, <- Nat.add_succ_r.
     apply Nat.lt_sub_lt_add_l.
     rewrite Nat.sub_diag.
     apply Nat.lt_0_succ.

     apply Nat.nle_gt; intros Hcont.
     rename H into Hbt.
     destruct (lt_dec (si + di2) (sj + di7)) as [H5| H5].
      pose proof (Hs4 (sj + di7 - (ssi + di2))) as H.
      unfold lt in H5; rewrite <- Nat.add_succ_l, <- Heqssi in H5.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Nat.add_comm, Nat.add_sub in H.
      rewrite Hs7 in H; revert H; apply digit_neq_0_1.

      apply Nat.nlt_ge in H5.
      apply Nat.le_antisymm in H5; auto.
      rewrite <- H5, Hs1 in Hs7; revert Hs7; apply digit_neq_1_0.

    symmetry in H.
    apply oppd_1_iff in H.
    rename H into Hbt.
    assert (j - si < di3) as H.
     apply Nat.add_lt_mono_r with (p := si).
     rewrite <- Nat.add_sub_swap; auto.
     rewrite Nat.add_sub.
     rewrite Nat.add_comm.
     eapply Nat.lt_trans; [ eauto  | idtac ].
     apply Nat.add_lt_mono_l; assumption.

     apply Hn2 in H.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_comm, Nat.add_sub in H.
     rewrite Hjf, Hbt, digit_opp_0 in H.
     revert H; apply digit_neq_0_1.

 rewrite first_0_before_none_iff in Hj.
 rewrite Hj in Hs3; [ revert Hs3; apply digit_neq_1_0 | idtac ].
 apply Nat.add_lt_mono_l; assumption.
Qed.

Theorem I_add_inf_1_eq_if : ∀ x y i,
  (∀ di, (I_add_i x y (i + di) = 1)%D)
  → (x.[i] = y.[i])%D
  → (∀ di, (x.[i + S di] = 1)%D) ∧
    (∀ di, (y.[i + S di] = 1)%D).
Proof.
intros x y i Hdi Hxy.
apply forall_and_distr; intros di.
induction di.
 rewrite Nat.add_1_r.
 pose proof (Hdi 0) as H.
 unfold I_add_i, carry in H.
 rewrite Nat.add_0_r in H.
 remember (S i) as si.
 remember (fst_same x y si) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Hs1).
  rewrite Hxy in H.
  rewrite digit_add_nilpotent, digit_add_0_l in H.
  rewrite H in Hs1; symmetry in Hs1.
  rename H into Ha1.
  rename Hs1 into Hb1.
  destruct di1.
   rewrite Nat.add_0_r in Ha1, Hb1.
   split; assumption.

   rewrite Nat.add_succ_r, <- Nat.add_succ_l in Ha1.
   rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hb1.
   pose proof (Hdi 1) as H.
   rewrite Nat.add_1_r, <- Heqsi in H.
   unfold I_add_i, carry in H.
   pose proof (Hn1 0 (Nat.lt_0_succ di1)) as H1.
   rewrite Nat.add_0_r in H1.
   rewrite H1, digit_opp_add_diag_l, digit_add_1_l in H.
   apply oppd_1_iff in H.
   remember (S si) as ssi.
   remember (fst_same x y ssi) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs2.
   destruct s2 as [di2| ]; [ idtac | exfalso; revert H; apply digit_neq_1_0 ].
   destruct Hs2 as (Hn2, Hb2).
   rewrite H in Hb2.
   rename H into Ha2; symmetry in Hb2.
   destruct (lt_dec di1 di2) as [H2| H2].
    apply Hn2 in H2.
    rewrite Ha1, Hb1 in H2; exfalso; revert H2; apply digit_neq_1_0.

    apply Nat.nlt_ge in H2.
    destruct (lt_dec di2 di1) as [H3| H3].
     apply Nat.succ_lt_mono in H3.
     apply Hn1 in H3.
     rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H3.
     rewrite Ha2, Hb2 in H3; exfalso; revert H3; apply digit_neq_0_1.

     apply Nat.nlt_ge in H3.
     apply Nat.le_antisymm in H2; auto.
     subst di2; clear H3.
     rewrite Ha1 in Ha2; exfalso; revert Ha2; apply digit_neq_1_0.

  clear H.
  pose proof (Hdi 1) as H.
  rewrite Nat.add_1_r, <- Heqsi in H.
  unfold I_add_i, carry in H.
  pose proof (Hs1 0) as H1.
  rewrite Nat.add_0_r in H1.
  rewrite H1, digit_opp_add_diag_l, digit_add_1_l in H.
  apply oppd_1_iff in H.
  remember (S si) as ssi.
  remember (fst_same x y ssi) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2.
  destruct s2 as [di2| ]; [ idtac | exfalso; revert H; apply digit_neq_1_0 ].
  destruct Hs2 as (Hn2, Hb2).
  rewrite H in Hb2.
  rename H into Ha2; symmetry in Hb2.
  pose proof (Hs1 (S di2)) as H.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H.
  rewrite Ha2, Hb2 in H; exfalso; revert H; apply digit_neq_0_1.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l in IHdi.
 do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 remember (S i) as si.
 remember (S si) as ssi.
 pose proof (Hdi (S di)) as H.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqsi in H.
 unfold I_add_i, carry in H.
 destruct IHdi as (Ha, Hb).
 rewrite Ha, Hb in H.
 rewrite digit_add_1_l, digit_add_0_l in H.
 rewrite <- Nat.add_succ_l, <- Heqssi in H.
 remember (fst_same x y (ssi + di)) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Hb1).
  rewrite H in Hb1.
  rename H into Ha1; symmetry in Hb1.
  destruct di1.
   rewrite Nat.add_0_r in Ha1, Hb1.
   split; assumption.

   rewrite Nat.add_succ_r, <- Nat.add_succ_l in Ha1.
   rewrite <- Nat.add_succ_l in Ha1.
   rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hb1.
   rewrite <- Nat.add_succ_l in Hb1.
   pose proof (Hdi (S (S di))) as H.
   do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
   rewrite <- Heqsi, <- Heqssi in H.
   unfold I_add_i, carry in H.
   pose proof (Hn1 0 (Nat.lt_0_succ di1)) as H1.
   rewrite Nat.add_0_r in H1.
   rewrite H1, digit_opp_add_diag_l, digit_add_1_l in H.
   apply oppd_1_iff in H.
   rewrite <- Nat.add_succ_l in H.
   remember (S ssi) as sssi.
   remember (fst_same x y (sssi + di)) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs2.
   destruct s2 as [di2| ]; [ idtac | exfalso; revert H; apply digit_neq_1_0 ].
   destruct Hs2 as (Hn2, Hb2).
   rewrite H in Hb2.
   rename H into Ha2; symmetry in Hb2.
   destruct (lt_dec di1 di2) as [H2| H2].
    apply Hn2 in H2.
    rewrite Ha1, Hb1 in H2; exfalso; revert H2; apply digit_neq_1_0.

    apply Nat.nlt_ge in H2.
    destruct (lt_dec di2 di1) as [H3| H3].
     apply Nat.succ_lt_mono in H3.
     apply Hn1 in H3.
     rewrite Nat.add_succ_r, <- Nat.add_succ_l in H3.
     rewrite <- Nat.add_succ_l, <- Heqsssi in H3.
     rewrite Ha2, Hb2 in H3; exfalso; revert H3; apply digit_neq_0_1.

     apply Nat.nlt_ge in H3.
     apply Nat.le_antisymm in H2; auto.
     subst di2; clear H3.
     rewrite Ha1 in Ha2; exfalso; revert Ha2; apply digit_neq_1_0.

  clear H.
  pose proof (Hdi (S (S di))) as H.
  do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
  rewrite <- Heqsi, <- Heqssi in H.
  unfold I_add_i, carry in H.
  pose proof (Hs1 0) as H1.
  rewrite Nat.add_0_r in H1.
  rewrite H1, digit_opp_add_diag_l, digit_add_1_l in H.
  apply oppd_1_iff in H.
  rewrite <- Nat.add_succ_l in H.
  remember (S ssi) as sssi.
  remember (fst_same x y (sssi + di)) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2.
  destruct s2 as [di2| ]; [ idtac | exfalso; revert H; apply digit_neq_1_0 ].
  destruct Hs2 as (Hn2, Hb2).
  rewrite Heqsssi, Nat.add_succ_l in Hb2.
  rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hb2.
  clear H; pose proof Hs1 (S di2) as H.
  rewrite Hb2 in H; symmetry in H.
  exfalso; revert H; apply no_fixpoint_oppd.
Qed.

Theorem I_add_inf_1_neq_if : ∀ x y i,
  (∀ di, (I_add_i x y (i + di) = 1)%D)
  → (x.[i] = oppd (y.[i]))%D
  → ∃ j,
    i < j ∧
    (∀ di, i + di < j → (x.[i + di] = oppd (y.[i + di]))%D) ∧
    (x.[j] = 0)%D ∧ (y.[j] = 0)%D ∧
    (∀ di, (x.[j + S di] = 1)%D) ∧
    (∀ di, (y.[j + S di] = 1)%D).
Proof.
intros x y i Hdi Hxy.
pose proof (Hdi 0) as H.
rewrite Nat.add_0_r in H.
unfold I_add_i, carry in H.
remember (S i) as si.
remember (fst_same x y si) as s1 eqn:Hs1 .
symmetry in Hs1.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hxy in H.
 exists (si + di1).
 split.
  rewrite Heqsi; apply Nat.le_sub_le_add_l.
  rewrite Nat.sub_diag; apply Nat.le_0_l.

  rewrite digit_opp_add_diag_l, digit_add_1_l in H.
  apply oppd_1_iff in H.
  rewrite H in Hs1; symmetry in Hs1.
  split.
   intros di Hidi.
   rewrite Heqsi in Hidi; simpl in Hidi.
   rewrite <- Nat.add_succ_r in Hidi.
   apply Nat.add_lt_mono_l in Hidi.
   destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
   apply Nat.succ_lt_mono in Hidi.
   rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqsi.
   apply Hn1; assumption.

   split; auto.
   split; auto.
   apply forall_and_distr; intros di.
   rename H into Ha.
   pose proof (Hdi (S di1)) as H.
   unfold I_add_i, carry in H.
   rewrite Nat.add_succ_r in H.
   rewrite <- Nat.add_succ_l, <- Heqsi in H.
   rewrite <- Nat.add_succ_l in H; remember (S si) as ssi.
   rewrite Hs1, Ha, digit_add_0_r, digit_add_0_l in H.
   remember (fst_same x y (ssi + di1)) as s2 eqn:Hs2 .
   symmetry in Hs2.
   apply fst_same_iff in Hs2; simpl in Hs2.
   destruct s2 as [di2| ].
    destruct Hs2 as (Hn2, Hs2).
    destruct di2.
     rewrite Nat.add_0_r in Hs2, H.
     induction di.
      rewrite Nat.add_1_r, <- Nat.add_succ_l.
      rewrite <- Heqssi, <- Hs2.
      split; assumption.

      rename H into Hat.
      pose proof (Hdi (S (S (di1 + di)))) as H.
      do 2 rewrite Nat.add_succ_r in H.
      rewrite <- Nat.add_succ_l, <- Heqsi in H.
      rewrite <- Nat.add_succ_l, <- Heqssi in H.
      rewrite Nat.add_assoc in H.
      unfold I_add_i, carry in H.
      do 2 rewrite <- Nat.add_succ_l in H; remember (S ssi) as sssi.
      rewrite Nat.add_succ_r in IHdi.
      do 2 rewrite <- Nat.add_succ_l in IHdi.
      rewrite <- Heqssi in IHdi.
      destruct IHdi as (H1, H2).
      rewrite H1, H2, digit_add_1_r, digit_add_0_l in H.
      remember (fst_same x y (sssi + di1 + di)) as s3 eqn:Hs3 .
      symmetry in Hs3.
      apply fst_same_iff in Hs3; simpl in Hs3.
      destruct s3 as [di3| ].
       do 2 rewrite Nat.add_succ_r.
       do 4 rewrite <- Nat.add_succ_l.
       rewrite <- Heqssi, <- Heqsssi.
       destruct Hs3 as (Hn3, Hs3).
       rewrite H in Hs3; symmetry in Hs3.
       destruct di3.
        rewrite Nat.add_0_r in Hs3, H.
        split; assumption.

        rename H into Ha3.
        pose proof (Hn3 di3 (Nat.lt_succ_diag_r di3)) as H.
        rename H into Hxy3.
        pose proof (Hdi (S (S (S (di1 + di + di3))))) as H.
        do 3 rewrite Nat.add_succ_r in H.
        do 3 rewrite <- Nat.add_succ_l in H.
        rewrite <- Heqsi, <- Heqssi, <- Heqsssi in H.
        do 2 rewrite Nat.add_assoc in H.
        unfold I_add_i, carry in H.
        rewrite Hxy3, digit_opp_add_diag_l, digit_add_1_l in H.
        do 3 rewrite <- Nat.add_succ_l in H.
        remember (S sssi) as ssssi.
        remember (fst_same x y (ssssi + di1 + di + di3)) as s4 eqn:Hs4 .
        symmetry in Hs4.
        apply fst_same_iff in Hs4; simpl in Hs4.
        destruct s4 as [di4| ].
         destruct Hs4 as (Hn4, Hs4).
         destruct di4.
          rewrite Nat.add_0_r in H.
          apply oppd_1_iff in H.
          rewrite Nat.add_succ_r in Ha3.
          do 3 rewrite <- Nat.add_succ_l in Ha3.
          rewrite <- Heqssssi, H in Ha3.
          exfalso; revert Ha3; apply digit_neq_0_1.

          rename H into Ha4.
          pose proof (Hn4 0 (Nat.lt_0_succ di4)) as H.
          rewrite Nat.add_0_r in H.
          rewrite Nat.add_succ_r in Hs3, Ha3.
          do 3 rewrite <- Nat.add_succ_l in Hs3, Ha3.
          rewrite <- Heqssssi in Hs3, Ha3.
          rewrite Hs3, Ha3 in H.
          exfalso; revert H; apply digit_neq_1_0.

         exfalso; revert H; apply digit_neq_0_1.

       clear H.
       pose proof (Hdi (S (S (S (di1 + di))))) as H.
       do 3 rewrite Nat.add_succ_r in H.
       do 3 rewrite <- Nat.add_succ_l in H.
       rewrite <- Heqsi, <- Heqssi, <- Heqsssi in H.
       rewrite Nat.add_assoc in H.
       do 2 rewrite Nat.add_succ_r.
       do 4 rewrite <- Nat.add_succ_l.
       rewrite <- Heqssi, <- Heqsssi.
       unfold I_add_i, carry in H.
       do 2 rewrite <- Nat.add_succ_l in H.
       remember (S sssi) as ssssi.
       remember (fst_same x y (ssssi + di1 + di)) as s4 eqn:Hs4 .
       symmetry in Hs4.
       apply fst_same_iff in Hs4; simpl in Hs4.
       destruct s4 as [di4| ].
        destruct Hs4 as (Hn4, Hs4).
        clear H.
        pose proof (Hs3 (S di4)) as H.
        rewrite Nat.add_succ_r in H.
        do 3 rewrite <- Nat.add_succ_l in H.
        rewrite <- Heqssssi in H.
        rewrite Hs4 in H; symmetry in H.
        exfalso; revert H; apply no_fixpoint_oppd.

        rewrite digit_add_1_r in H.
        apply oppd_1_iff in H.
        rename H into Hxy1.
        pose proof (Hs3 0) as H.
        rewrite Nat.add_0_r in H.
        rewrite H in Hxy1.
        rewrite digit_opp_add_diag_l in Hxy1.
        exfalso; revert Hxy1; apply digit_neq_1_0.

     rename H into Ha2.
     rewrite Ha2 in Hs2; symmetry in Hs2.
     pose proof (Hn2 0 (Nat.lt_0_succ di2)) as H.
     rewrite Nat.add_0_r in H.
     rename H into Hxy1.
     pose proof (Hdi (S (S di1))) as H.
     do 2 rewrite Nat.add_succ_r in H.
     do 2 rewrite <- Nat.add_succ_l in H.
     rewrite <- Heqsi, <- Heqssi in H.
     unfold I_add_i, carry in H.
     rewrite Hxy1, digit_opp_add_diag_l, digit_add_1_l in H.
     apply oppd_1_iff in H.
     rewrite <- Nat.add_succ_l in H; remember (S ssi) as sssi.
     remember (fst_same x y (sssi + di1)) as s3 eqn:Hs3 .
     symmetry in Hs3.
     apply fst_same_iff in Hs3; simpl in Hs3.
     destruct s3 as [di3| ].
      destruct Hs3 as (Hn3, Hb3).
      rename H into Ha3.
      rewrite Ha3 in Hb3; symmetry in Hb3.
      rewrite Nat.add_succ_r in Hs2, Ha2.
      do 2 rewrite <- Nat.add_succ_l in Hs2, Ha2.
      rewrite <- Heqsssi in Hs2, Ha2.
      destruct (lt_dec di2 di3) as [H1| H1].
       apply Hn3 in H1.
       rewrite Hs2, Ha2 in H1; symmetry in H1.
       exfalso; revert H1; apply no_fixpoint_oppd.

       apply Nat.nlt_ge in H1.
       destruct (lt_dec di3 di2) as [H2| H2].
        apply Nat.succ_lt_mono in H2.
        apply Hn2 in H2.
        rewrite Nat.add_succ_r in H2.
        do 2 rewrite <- Nat.add_succ_l in H2.
        rewrite <- Heqsssi in H2.
        rewrite Ha3, Hb3 in H2; symmetry in H2.
        exfalso; revert H2; apply no_fixpoint_oppd.

        apply Nat.nlt_ge in H2.
        apply Nat.le_antisymm in H1; auto.
        subst di3; clear H2.
        rewrite Ha2 in Ha3.
        exfalso; revert Ha3; apply digit_neq_1_0.

      exfalso; revert H; apply digit_neq_1_0.

    clear H.
    pose proof (Hs2 0) as H.
    rewrite Nat.add_0_r in H.
    rename H into Ha1.
    pose proof (Hdi (S (S di1))) as H.
    do 2 rewrite Nat.add_succ_r in H.
    rewrite <- Nat.add_succ_l, <- Heqsi in H.
    rewrite <- Nat.add_succ_l, <- Heqssi in H.
    unfold I_add_i, carry in H.
    rewrite Ha1, digit_opp_add_diag_l, digit_add_1_l in H.
    apply oppd_1_iff in H.
    rewrite <- Nat.add_succ_l in H.
    remember (S ssi) as sssi.
    remember (fst_same x y (sssi + di1)) as s3 eqn:Hs3 .
    symmetry in Hs3.
    apply fst_same_iff in Hs3; simpl in Hs3.
    destruct s3 as [di3| ].
     destruct Hs3 as (Hn3, Hs3).
     rename H into Ha3; rename Hs3 into Hb3.
     rewrite Ha3 in Hb3; symmetry in Hb3.
     pose proof (Hs2 (S di3)) as H.
     rewrite Nat.add_succ_r in H.
     do 2 rewrite <- Nat.add_succ_l in H.
     rewrite <- Heqsssi in H.
     rewrite Ha3, Hb3 in H.
     exfalso; revert H; apply digit_neq_0_1.

    exfalso; revert H; apply digit_neq_1_0.

 rewrite Hxy, digit_opp_add_diag_l in H.
 exfalso; revert H; apply digit_neq_0_1.
Qed.

Theorem I_add_add_0_l_when_lhs_has_relay : ∀ x y i di1,
  fst_same (x + 0%I) y (S i) = Some di1
  → (I_add_i (x + 0%I) y i = I_add_i x y i)%D.
Proof.
intros x y i di1 Hs1.
unfold I_add_i, carry at 1; remember (S i) as si; simpl.
rewrite Hs1.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Hs1).
rewrite Hs1.
unfold I_add_i, carry; rewrite <- Heqsi; simpl.
rewrite digit_add_0_r.
remember (fst_same x y si) as s2 eqn:Hs2 .
symmetry in Hs2.
apply fst_same_iff in Hs2; simpl in Hs2.
remember (fst_same x 0 si) as s3 eqn:Hs3 .
symmetry in Hs3.
apply fst_same_iff in Hs3; simpl in Hs3.
destruct s2 as [di2| ].
 destruct Hs2 as (Hn2, Hs2).
 rewrite Hs2.
 destruct s3 as [di3| ].
  destruct Hs3 as (Hn3, Hs3).
  rewrite Hs3, digit_add_0_r; f_equal.
  unfold I_add_i, carry in Hs1.
  rewrite <- Nat.add_succ_l in Hs1.
  remember (S si) as ssi.
  move Heqssi before Heqsi.
  simpl in Hs1; rewrite digit_add_0_r in Hs1.
  remember (fst_same x 0 (ssi + di1)) as s4 eqn:Hs4 .
  symmetry in Hs4.
  apply fst_same_iff in Hs4; simpl in Hs4.
  destruct s4 as [di4| ].
   destruct Hs4 as (Hn4, Hs4).
   rewrite Hs4, digit_add_0_r in Hs1.
   destruct (lt_dec di1 di2) as [H1| H1].
    remember H1 as H; clear HeqH.
    apply Hn2 in H.
    rewrite Hs1 in H; symmetry in H.
    exfalso; revert H; apply no_fixpoint_oppd.

    apply Nat.nlt_ge in H1.
    destruct (lt_dec di2 di1) as [H2| H2].
     remember H2 as H; clear HeqH.
     apply Hn1 in H.
     unfold I_add_i, carry in H.
     rewrite <- Nat.add_succ_l, <- Heqssi in H.
     simpl in H.
     remember (fst_same x 0 (ssi + di2)) as s5 eqn:Hs5 .
     symmetry in Hs5.
     apply fst_same_iff in Hs5; simpl in Hs5.
     destruct s5 as [di5| ].
      destruct Hs5 as (Hn5, Hs5).
      rewrite digit_add_0_r, Hs2, Hs5, digit_add_0_r in H.
      symmetry in H.
      exfalso; revert H; apply no_fixpoint_oppd.

      clear H.
      pose proof (Hs5 (di1 - di2 + di4)) as H.
      do 2 rewrite Nat.add_comm, Nat.add_assoc in H.
      rewrite Nat.add_assoc in H.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Nat.add_sub_swap in H; auto.
      rewrite Nat.sub_diag, Nat.add_0_l in H.
      rewrite Nat.add_comm, Nat.add_assoc in H.
      rewrite Hs4 in H; symmetry in H.
      exfalso; revert H; apply no_fixpoint_oppd.

     apply Nat.nlt_ge in H2.
     apply Nat.le_antisymm in H1; [ idtac | assumption ].
     subst di1; reflexivity.

   rewrite digit_add_1_r in Hs1.
   destruct (lt_dec di2 di1) as [H2| H2].
    remember H2 as H; clear HeqH.
    apply Hn1 in H.
    unfold I_add_i, carry in H.
    rewrite <- Nat.add_succ_l, <- Heqssi in H.
    simpl in H.
    remember (fst_same x 0 (ssi + di2)) as s5 eqn:Hs5 .
    symmetry in Hs5.
    apply fst_same_iff in Hs5; simpl in Hs5.
    destruct s5 as [di5| ].
     destruct Hs5 as (Hn5, Hs5).
     rewrite digit_add_0_r, Hs2, Hs5, digit_add_0_r in H.
     symmetry in H.
     exfalso; revert H; apply no_fixpoint_oppd.

     clear H.
     rewrite <- Hs1, <- Hs2.
     destruct (lt_dec di2 di3) as [H3| H3].
      pose proof (Hs5 (di3 - S di2)) as H.
      rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in H.
      do 2 rewrite Nat.add_comm, Nat.add_assoc in H.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Nat.add_sub_swap in H; auto.
      rewrite Nat.sub_diag, Nat.add_0_l in H; simpl in H.
      rewrite Nat.add_comm, Hs3 in H.
      exfalso; revert H; apply digit_neq_0_1.

      apply Nat.nlt_ge in H3.
      destruct (digit_eq_dec (x .[ si + di2]) 0%D) as [H4| H4].
       rewrite H4.
       apply digit_add_compat; [ reflexivity | idtac ].
       apply oppd_0_iff.
       pose proof (Hs5 (di1 - S di2)) as H.
       rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in H.
       do 2 rewrite Nat.add_comm, Nat.add_assoc in H.
       rewrite Nat.add_sub_assoc in H; auto.
       rewrite Nat.add_sub_swap in H; auto.
       rewrite Nat.sub_diag, Nat.add_0_l in H; simpl in H.
       rewrite Nat.add_comm.
       assumption.

       apply digit_add_compat; [ reflexivity | idtac ].
       apply digit_not_0_iff_1 in H4.
       rewrite H4 in Hs2.
       symmetry in Hs2.
       exfalso.
       destruct (lt_dec di3 di2) as [H5| H5].
        remember H5 as H; clear HeqH.
        apply Hn2 in H.
        rewrite Hs3 in H; symmetry in H.
        apply oppd_0_iff in H.
        rename H into Hb.
        remember H2 as H; clear HeqH.
        eapply Nat.lt_trans in H; [ idtac | eauto  ].
        apply Hn1 in H.
        rewrite Hb in H; simpl in H.
        unfold I_add_i, carry in H.
        rewrite <- Nat.add_succ_l, <- Heqssi in H.
        simpl in H.
        rewrite Hs3, digit_add_0_r, digit_add_0_l in H.
        remember (fst_same x 0 (ssi + di3)) as s6 eqn:Hs6 .
        symmetry in Hs6.
        apply fst_same_iff in Hs6; simpl in Hs6.
        destruct s6 as [di6| ]; [ idtac | revert H; apply digit_neq_1_0 ].
        destruct Hs6 as (Hn6, Hs6).
        clear H.
        remember (first_0_before x (si + di2)) as j eqn:Hj .
        symmetry in Hj.
        destruct j as [j| ].
         apply first_0_before_some_iff in Hj.
         destruct Hj as (Hji, (Hjf, Hk)).
         assert (j - si < di1) as H.
          eapply Nat.le_lt_trans; [ idtac | eauto  ].
          rewrite Heqsi in Hji; simpl in Hji.
          apply Nat.succ_le_mono in Hji.
          apply Nat.le_sub_le_add_l.
          rewrite Heqsi.
          apply Nat.le_le_succ_r; assumption.

          apply Hn1 in H.
          rewrite Nat.add_sub_assoc in H.
           rewrite Nat.add_comm, Nat.add_sub in H.
           unfold I_add_i, carry in H.
           remember (S j) as sj; simpl in H.
           rewrite Hjf, digit_add_0_r, digit_add_0_l in H.
           remember (fst_same x 0 sj) as s7 eqn:Hs7 .
           symmetry in Hs7.
           apply fst_same_iff in Hs7; simpl in Hs7.
           destruct s7 as [di7| ].
            destruct Hs7 as (Hn7, Hs7).
            rewrite Hs7 in H.
            symmetry in H.
            apply oppd_0_iff in H.
            destruct (lt_dec (sj + di7) (si + di2)) as [H1| H1].
             rewrite Hk in Hs7; auto.
              revert Hs7; apply digit_neq_1_0.

              rewrite Heqsj, Nat.add_succ_l, <- Nat.add_succ_r.
              apply Nat.lt_sub_lt_add_l.
              rewrite Nat.sub_diag.
              apply Nat.lt_0_succ.

             apply Nat.nlt_ge in H1.
             rename H into Hbt.
             destruct (lt_dec (si + di2) (sj + di7)) as [H6| H6].
              pose proof (Hs5 (j + di7 - (si + di2))) as H.
              rewrite Heqsj in H6.
              simpl in H6.
              apply Nat.succ_le_mono in H6.
              rewrite Nat.add_sub_assoc in H; auto.
              rewrite Heqssi in H.
              do 2 rewrite Nat.add_succ_l in H.
              rewrite <- Nat.add_succ_r in H.
              rewrite Nat.add_comm, Nat.add_sub in H.
              rewrite <- Nat.add_succ_l, <- Heqsj in H.
              rewrite Hs7 in H.
              revert H; apply digit_neq_0_1.

              apply Nat.nlt_ge in H6.
              apply Nat.le_antisymm in H1; auto.
              rewrite H1, H4 in Hs7.
              revert Hs7; apply digit_neq_1_0.

            symmetry in H.
            apply oppd_1_iff in H.
            rename H into H6.
            assert (j - si < di2) as H by (eapply lt_add_sub_lt_r; eauto ).
            apply Hn2 in H.
            rewrite Nat.add_sub_assoc in H.
             rewrite Nat.add_comm, Nat.add_sub in H.
             rewrite Hjf, H6 in H.
             revert H; apply digit_neq_0_1.

             clear H.
             apply Nat.nlt_ge; intros Hcont.
             assert (j < si + di3) as H.
              rewrite Heqsi in Hcont.
              apply Nat.succ_le_mono in Hcont.
              eapply Nat.le_lt_trans; eauto .
              rewrite Heqsi; simpl.
              rewrite <- Nat.add_succ_r.
              apply Nat.lt_sub_lt_add_l.
              rewrite Nat.sub_diag; apply Nat.lt_0_succ.

              apply Hk in H.
               rewrite Hs3 in H; revert H; apply digit_neq_0_1.

               apply Nat.add_lt_mono_l; assumption.

           apply Nat.nlt_ge; intros Hcont.
           rewrite Heqsi in Hcont.
           apply Nat.succ_le_mono in Hcont.
           rewrite Hk in Hs3.
            revert Hs3; apply digit_neq_1_0.

            rewrite Heqsi.
            eapply Nat.le_lt_trans; [ eauto  | idtac ].
            rewrite Nat.add_succ_l, <- Nat.add_succ_r.
            apply Nat.lt_sub_lt_add_l.
            rewrite Nat.sub_diag.
            apply Nat.lt_0_succ.

            apply Nat.add_lt_mono_l; assumption.

         rewrite first_0_before_none_iff in Hj.
         rewrite Hj in Hs3; [ revert Hs3; apply digit_neq_1_0 | idtac ].
         apply Nat.add_lt_mono_l; assumption.

        apply Nat.nlt_ge in H5.
        apply Nat.le_antisymm in H5; [ subst di3 | auto ].
        rewrite H4 in Hs3; revert Hs3; apply digit_neq_1_0.

    apply Nat.nlt_ge in H2.
    destruct (lt_dec di1 di2) as [H3| H3].
     pose proof (Hs4 (di2 - S di1)) as H.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Heqssi in H; simpl in H.
     rewrite Nat.add_shuffle0, Nat.add_sub in H.
     rewrite H in Hs2; symmetry in Hs2.
     rename H into Ha; move Ha after Hs2; rewrite Hs2.
     apply digit_add_compat; [ reflexivity | idtac ].
     apply digit_neq_eq_opp; intros Hbi.
     rewrite <- Hs1 in Hbi.
     apply oppd_0_iff in Hbi.
     destruct (lt_dec di1 di3) as [H1| H1].
      pose proof (Hs4 (di3 - S di1)) as H.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Heqssi in H; simpl in H.
      rewrite Nat.add_shuffle0, Nat.add_sub in H.
      rewrite Hs3 in H; exfalso; revert H; apply digit_neq_0_1.

      apply Nat.nlt_ge in H1.
      destruct (eq_nat_dec di1 di3) as [H4| H4].
       subst di3.
       rewrite Hbi in Hs3; revert Hs3; apply digit_neq_1_0.

       assert (di3 < di1) as H.
        apply Nat.nle_gt; intros H.
        apply Nat.le_antisymm in H; auto; contradiction.

        subst si ssi.
        eapply no_room_for_infinite_carry in Hs3; eauto .

     apply Nat.nlt_ge in H3.
     apply Nat.le_antisymm in H3; [ idtac | assumption ].
     subst di1; reflexivity.

  do 3 rewrite <- digit_add_assoc.
  apply digit_add_compat; [ reflexivity | idtac ].
  rewrite digit_add_comm, <- digit_add_assoc.
  apply digit_add_compat; [ reflexivity | idtac ].
  rewrite <- Hs2, Hs3, <- Hs1.
  unfold I_add_i, carry; rewrite <- Nat.add_succ_l.
  rewrite Hs3, digit_add_0_r, digit_add_1_l, digit_add_1_r.
  apply digit_opp_compat, oppd_0_iff.
  remember (S si) as ssi; simpl.
  remember (fst_same x 0 (ssi + di1)) as s4 eqn:Hs4 .
  symmetry in Hs4.
  destruct s4 as [s4| ]; [ idtac | reflexivity ].
  rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r.
  rewrite <- Nat.add_assoc, Hs3; reflexivity.

 do 3 rewrite <- digit_add_assoc.
 apply digit_add_compat; [ reflexivity | idtac ].
 rewrite digit_add_comm, <- digit_add_assoc.
 apply digit_add_compat; [ reflexivity | idtac ].
 destruct s3 as [di3| ].
  destruct Hs3 as (Hn3, Hs3).
  rewrite Hs3, digit_add_0_r.
  rewrite <- Hs1.
  unfold I_add_i, carry.
  rewrite <- Nat.add_succ_l.
  remember (S si) as ssi; simpl.
  rewrite digit_add_0_r.
  remember (fst_same x 0 (ssi + di1)) as s4 eqn:Hs4 .
  symmetry in Hs4.
  apply fst_same_iff in Hs4; simpl in Hs4.
  destruct s4 as [di4| ].
   destruct Hs4 as (Hn4, Hs4); rewrite Hs4.
   rewrite digit_add_0_r.
   destruct (lt_dec di1 di3) as [H1| H1].
    remember H1 as H; clear HeqH.
    apply Hn3; assumption.

    apply Nat.nlt_ge in H1.
    destruct (lt_dec di3 di1) as [H2| H2].
     apply digit_not_0_iff_1.
     intros Ha.
     remember Ha as Hb; clear HeqHb.
     rewrite Hs2 in Hb.
     apply oppd_0_iff in Hb.
     rewrite <- Hs1 in Hb.
     unfold I_add_i, carry in Hb.
     rewrite <- Nat.add_succ_l in Hb.
     rewrite <- Heqssi in Hb; simpl in Hb.
     rewrite Ha, digit_add_0_r, digit_add_0_l in Hb.
     remember (fst_same x 0 (ssi + di1)) as s5 eqn:Hs5 .
     symmetry in Hs5.
     apply fst_same_iff in Hs5; simpl in Hs5.
     destruct s5 as [di5| ].
      destruct Hs5 as (Hn5, Hs5); rewrite Hs5 in Hb.
      revert Hb; apply digit_neq_0_1.

      rewrite Hs5 in Hs4.
      revert Hs4; apply digit_neq_1_0.

     apply Nat.nlt_ge, Nat.le_antisymm in H2; [ idtac | assumption ].
     subst di3; clear H1.
     rewrite Hs2 in Hs3.
     apply oppd_0_iff in Hs3.
     rewrite <- Hs1 in Hs3.
     unfold I_add_i, carry in Hs3.
     rewrite <- Nat.add_succ_l in Hs3.
     rewrite <- Heqssi in Hs3; simpl in Hs3.
     rewrite digit_add_0_r in Hs3.
     remember (fst_same x 0 (ssi + di1)) as s5 eqn:Hs5 .
     symmetry in Hs5.
     apply fst_same_iff in Hs5; simpl in Hs5.
     destruct s5 as [di5| ].
      destruct Hs5 as (Hn5, Hs5); rewrite Hs5 in Hs3.
      rewrite digit_add_0_r in Hs3; assumption.

      rewrite Hs5 in Hs4.
      exfalso; revert Hs4; apply digit_neq_1_0.

   rewrite digit_add_1_r.
   apply oppd_1_iff.
   unfold I_add_i, carry in Hs1.
   rewrite <- Nat.add_succ_l, <- Heqssi in Hs1.
   simpl in Hs1.
   rewrite digit_add_0_r in Hs1.
   rewrite Hs2 in Hs1.
   remember (fst_same x 0 (ssi + di1)) as s5 eqn:Hs5 .
   symmetry in Hs5.
   apply fst_same_iff in Hs5; simpl in Hs5.
   destruct s5 as [di5| ].
    destruct Hs5 as (Hn5, Hs5); rewrite Hs5 in Hs1.
    rewrite digit_add_0_r in Hs1.
    exfalso; revert Hs1; apply no_fixpoint_oppd.

    clear Hs1 Hs5.
    destruct (lt_dec di1 di3) as [H1| H1].
     pose proof (Hs4 (di3 - S di1)) as H.
     rewrite Heqssi in H.
     rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_shuffle0, Nat.add_sub in H.
     rewrite Hs3 in H.
     exfalso; revert H; apply digit_neq_0_1.

     apply Nat.nlt_ge in H1.
     destruct (lt_dec di3 di1) as [H2| H2].
      remember H2 as H; clear HeqH.
      apply Hn1 in H.
      unfold I_add_i, carry in H.
      rewrite <- Nat.add_succ_l, <- Heqssi in H; simpl in H.
      rewrite digit_add_0_r in H.
      remember (fst_same x 0 (ssi + di3)) as s5 eqn:Hs5 .
      symmetry in Hs5.
      apply fst_same_iff in Hs5; simpl in Hs5.
      destruct s5 as [di5| ].
       destruct Hs5 as (Hn5, Hs5); rewrite Hs5 in H.
       rewrite digit_add_0_r in H.
       apply digit_not_1_iff_0; intros Ha.
       subst si ssi.
       eapply no_room_for_infinite_carry in Hs3; eauto .

       rewrite digit_add_1_r, <- Hs2 in H.
       exfalso; revert H; apply no_fixpoint_oppd.

      apply Nat.nlt_ge in H2.
      apply Nat.le_antisymm in H2; auto.
      subst di3; assumption.

  rewrite digit_add_1_r, <- Hs2.
  apply Hs3.
Qed.

Theorem I_add_add_0_l_when_lhs_has_no_relay : ∀ x y i dj2 dj5,
  fst_same ((x + 0)%I + y) 0 (S i) = Some dj2
  → fst_same (x + y) 0 (S i) = Some dj5
  → fst_same (x + 0%I) y (S i) = None
  → (I_add_i (x + 0%I) y i = I_add_i x y i)%D.
Proof.
intros x y i dj2 dj5 Ps2 Ps5 Hs1.
remember (S i) as si.
unfold I_add_i, carry.
rewrite <- Heqsi; simpl.
rewrite Hs1.
unfold I_add_i, carry at 1; rewrite <- Heqsi; simpl.
apply fst_same_iff in Hs1; simpl in Hs1.
apply fst_same_iff in Ps2; simpl in Ps2.
destruct Ps2 as (Pn2, _).
apply fst_same_iff in Ps5; simpl in Ps5.
destruct Ps5 as (Pn5, Ps5).
rewrite digit_add_0_r.
do 3 rewrite <- digit_add_assoc.
apply digit_add_compat; [ reflexivity | idtac ].
rewrite digit_add_comm, <- digit_add_assoc.
apply digit_add_compat; [ reflexivity | idtac ].
rewrite digit_add_1_l.
remember (fst_same x y si) as s2 eqn:Hs2 .
symmetry in Hs2.
apply fst_same_iff in Hs2; simpl in Hs2.
remember (fst_same x 0 si) as s3 eqn:Hs3 .
symmetry in Hs3.
apply fst_same_iff in Hs3; simpl in Hs3.
destruct s2 as [di2| ].
 destruct Hs2 as (Hn2, Hs2).
 destruct s3 as [di3| ].
  destruct Hs3 as (Hn3, Hs3).
  rewrite Hs3; simpl; symmetry.
  destruct (lt_dec di2 di3) as [H1| H1].
   apply Hn3; assumption.

   apply Nat.nlt_ge in H1.
   pose proof (Hs1 di2) as H.
   unfold I_add_i, carry in H.
   rewrite <- Nat.add_succ_l in H.
   remember (S si) as ssi; simpl in H.
   rewrite digit_add_0_r in H.
   remember (fst_same x 0 (ssi + di2)) as s4 eqn:Hs4 .
   symmetry in Hs4.
   apply fst_same_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4); rewrite Hs4, digit_add_0_r in H.
    rewrite Hs2 in H; symmetry in H.
    exfalso; revert H; apply no_fixpoint_oppd.

    clear H.
    apply digit_not_0_iff_1.
    intros Ha.
    destruct dj5.
     rewrite Nat.add_0_r in Ps5.
     unfold I_add_i, carry in Ps5.
     rewrite <- Heqssi in Ps5.
     remember (fst_same x y ssi) as s6 eqn:Ps6 .
     symmetry in Ps6.
     apply fst_same_iff in Ps6; simpl in Ps6.
     destruct s6 as [dj6| ].
      destruct Ps6 as (Pn6, Ps6).
      assert (S dj6 = di2) as H.
       destruct (lt_dec (S dj6) di2) as [H2| H2].
        apply Hn2 in H2.
        rewrite Nat.add_succ_r, <- Nat.add_succ_l in H2.
        rewrite <- Heqssi in H2.
        rewrite Ps6 in H2; symmetry in H2.
        exfalso; revert H2; apply no_fixpoint_oppd.

        apply Nat.nlt_ge in H2.
        destruct (lt_dec di2 (S dj6)) as [H3| H3].
         destruct di2.
          rewrite Nat.add_0_r in Hs4.
          rewrite Nat.add_0_r in Hs2.
          rewrite <- Hs2, Hs4 in Ps5.
          rewrite digit_add_1_r in Ps5.
          apply oppd_0_iff in Ps5.
          rewrite digit_add_nilpotent in Ps5.
          exfalso; revert Ps5; apply digit_neq_0_1.

          apply Nat.succ_lt_mono in H3.
          apply Pn6 in H3.
          rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs2.
          rewrite <- Heqssi, H3 in Hs2.
          exfalso; revert Hs2; apply no_fixpoint_oppd.

         apply Nat.nlt_ge in H3.
         apply Nat.le_antisymm; auto.

       rewrite <- H, Nat.add_succ_r, <- Nat.add_succ_l in Ha.
       rewrite <- Heqssi in Ha.
       rewrite Ha, digit_add_0_r in Ps5.
       rewrite <- H in Hn2; clear H.
       assert (0 < S dj6) as H by apply Nat.lt_0_succ.
       apply Hn2 in H.
       rewrite Nat.add_0_r in H.
       rewrite H, digit_opp_add_diag_l in Ps5.
       revert Ps5; apply digit_neq_1_0.

      destruct di2.
       rewrite Nat.add_0_r in Hs2.
       rewrite <- Hs2, digit_add_nilpotent in Ps5.
       revert Ps5; apply digit_neq_1_0.

       rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs2.
       rewrite <- Heqssi in Hs2.
       rewrite Ps6 in Hs2.
       revert Hs2; apply no_fixpoint_oppd.

     assert (S dj5 = di2) as H.
      destruct (lt_dec (S dj5) di2) as [H2| H2].
       unfold I_add_i, carry in Ps5.
       rewrite <- Nat.add_succ_l, <- Heqssi in Ps5.
       remember (fst_same x y (ssi + S dj5)) as s6 eqn:Ps6 .
       symmetry in Ps6.
       apply fst_same_iff in Ps6; simpl in Ps6.
       destruct s6 as [di6| ].
        destruct Ps6 as (Pn6, Ps6).
        assert (S (S dj5 + di6) = di2) as H.
         destruct (lt_dec (S (S dj5 + di6)) di2) as [H3| H3].
          apply Hn2 in H3.
          rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H3.
          rewrite Nat.add_assoc in H3.
          rewrite Ps6 in H3; symmetry in H3.
          exfalso; revert H3; apply no_fixpoint_oppd.

          apply Nat.nlt_ge in H3.
          destruct (lt_dec di2 (S (S dj5 + di6))) as [H4| H4].
           remember H4 as H; clear HeqH.
           rewrite <- Nat.add_succ_l in H.
           apply Nat.succ_lt_mono in H2.
           apply lt_add_sub_lt_l with (a := di2) in H; auto.
           apply Nat.succ_lt_mono in H2.
           apply Pn6 in H.
           rewrite Heqssi in H.
           rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
           rewrite Nat.add_sub_assoc in H; auto.
           rewrite Nat.add_shuffle0, Nat.add_sub in H.
           rewrite Hs2 in H; symmetry in H.
           exfalso; revert H; apply no_fixpoint_oppd.

           apply Nat.nlt_ge in H4.
           apply Nat.le_antisymm; auto.

         rewrite <- H in Ha.
         rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in Ha.
         rewrite Nat.add_assoc in Ha.
         rewrite Ha, digit_add_0_r in Ps5.
         apply Hn2 in H2.
         rewrite H2, digit_opp_add_diag_l in Ps5.
         exfalso; revert Ps5; apply digit_neq_1_0.

        pose proof (Ps6 (di2 - S (S dj5))) as H.
        rewrite Nat.add_sub_assoc in H; auto.
        rewrite Heqssi in H.
        rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
        rewrite Nat.add_shuffle0, Nat.add_sub in H.
        rewrite Hs2 in H; symmetry in H.
        exfalso; revert H; apply no_fixpoint_oppd.

       apply Nat.nlt_ge in H2.
       destruct (lt_dec di2 (S dj5)) as [H3| H3].
        unfold I_add_i, carry in Ps5.
        rewrite <- Nat.add_succ_l, <- Heqssi in Ps5.
        remember (fst_same x y (ssi + S dj5)) as s6 eqn:Ps6 .
        symmetry in Ps6.
        apply fst_same_iff in Ps6; simpl in Ps6.
        destruct s6 as [dj6| ].
         destruct Ps6 as (Pn6, Ps6).
         pose proof (Hs1 (S dj5 + dj6)) as H.
         rewrite Nat.add_assoc in H.
         unfold I_add_i, carry in H.
         rewrite <- Nat.add_succ_l in H.
         rewrite <- Nat.add_succ_l in H.
         rewrite <- Heqssi in H; simpl in H.
         rewrite digit_add_0_r in H.
         remember (fst_same x 0 (ssi + S dj5 + dj6)) as s7 eqn:Ps7 .
         symmetry in Ps7.
         apply fst_same_iff in Ps7; simpl in Ps7.
         destruct s7 as [dj7| ].
          destruct Ps7 as (Pn7, Ps7); rewrite Ps7, digit_add_0_r in H.
          rename H into Hxy.
          pose proof (Hs1 (S (S dj5 + dj6))) as H.
          rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H.
          rewrite Nat.add_assoc in H.
          unfold I_add_i, carry in H.
          do 2 rewrite <- Nat.add_succ_l in H.
          remember (S ssi) as sssi; simpl in H.
          rewrite digit_add_0_r in H.
          remember (fst_same x 0 (sssi + S dj5 + dj6)) as s8 eqn:Ps8 .
          symmetry in Ps8.
          apply fst_same_iff in Ps8; simpl in Ps8.
          destruct s8 as [dj8| ].
           destruct Ps8 as (Pn8, Ps8); rewrite Ps8, digit_add_0_r in H.
           rewrite Ps6 in H; symmetry in H.
           exfalso; revert H; apply no_fixpoint_oppd.

           clear H.
           pose proof (Hs4 (S dj5 + dj6 + dj7 - di2)) as H.
           rewrite Nat.add_sub_assoc in H.
            rewrite Nat.add_shuffle0, Nat.add_sub in H.
            do 2 rewrite Nat.add_assoc in H.
            rewrite Ps7 in H.
            exfalso; revert H; apply digit_neq_0_1.

            eapply Nat.le_trans; eauto .
            rewrite <- Nat.add_assoc.
            apply Nat.le_sub_le_add_l.
            rewrite Nat.sub_diag.
            apply Nat.le_0_l.

          rewrite digit_add_1_r in H.
          apply oppd_inj in H.
          destruct dj6.
           rewrite Nat.add_0_r in H.
           rewrite H in Ps5.
           rewrite Nat.add_0_r in Ps7.
           rewrite Ps7 in Ps5.
           rewrite digit_add_1_r, digit_add_nilpotent in Ps5.
           exfalso; revert Ps5; apply digit_neq_1_0.

           rename H into Hyx.
           pose proof (Pn6 dj6 (Nat.lt_succ_diag_r dj6)) as H.
           rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hyx.
           rewrite <- Nat.add_succ_l in Hyx.
           rewrite <- Heqssi in Hyx.
           rewrite Hyx in H; symmetry in H.
           exfalso; revert H; apply no_fixpoint_oppd.

         pose proof (Hs1 (S dj5)) as H.
         unfold I_add_i, carry in H.
         rewrite <- Nat.add_succ_l, <- Heqssi in H; simpl in H.
         rewrite digit_add_0_r in H.
         remember (fst_same x 0 (ssi + S dj5)) as s7 eqn:Ps7 .
         symmetry in Ps7.
         apply fst_same_iff in Ps7; simpl in Ps7.
         destruct s7 as [dj7| ].
          destruct Ps7 as (Pn7, Ps7); rewrite Ps7, digit_add_0_r in H.
          clear H.
          pose proof (Hs4 (S dj5 + dj7 - di2)) as H.
          rewrite Nat.add_sub_swap in H; auto.
          rewrite Nat.add_assoc in H.
          rewrite Nat.add_sub_assoc in H; auto.
          rewrite Nat.add_shuffle0, Nat.add_sub in H.
          rewrite Ps7 in H.
          exfalso; revert H; apply digit_neq_0_1.

          rewrite digit_add_1_r in H.
          apply oppd_inj in H.
          rewrite H, digit_add_nilpotent in Ps5.
          exfalso; revert Ps5; apply digit_neq_1_0.

        apply Nat.nlt_ge in H3.
        apply Nat.le_antisymm; auto.

      rewrite H in Ps5.
      unfold I_add_i, carry in Ps5.
      rewrite <- Nat.add_succ_l, <- Heqssi in Ps5.
      remember (fst_same x y (ssi + di2)) as s6 eqn:Ps6 .
      symmetry in Ps6.
      apply fst_same_iff in Ps6; simpl in Ps6.
      destruct s6 as [dj6| ].
       rewrite Hs4, Hs2, digit_add_1_r in Ps5.
       rewrite digit_add_nilpotent in Ps5.
       revert Ps5; apply digit_neq_1_0.

       rewrite Hs2, digit_add_1_r in Ps5.
       rewrite digit_add_nilpotent in Ps5.
       revert Ps5; apply digit_neq_1_0.

  symmetry; simpl.
  assert (∀ dj, (y .[ si + dj] = 1)%D) as Hb.
   intros dj.
   apply oppd_0_iff.
   rewrite <- Hs1.
   unfold I_add_i, carry.
   rewrite <- Nat.add_succ_l; remember (S si) as ssi; simpl.
   rewrite digit_add_0_r.
   remember (fst_same x 0 (ssi + dj)) as s4 eqn:Hs4 .
   symmetry in Hs4.
   apply fst_same_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ]; [ idtac | rewrite Hs3; reflexivity ].
   destruct Hs4 as (Hn4, Hs4).
   rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Hs4.
   rewrite <- Nat.add_assoc, Hs3 in Hs4.
   exfalso; revert Hs4; apply digit_neq_1_0.

   destruct di2.
    rewrite Nat.add_0_r in Hs2; rewrite Nat.add_0_r.
    clear Hn2.
    unfold I_add_i, carry in Ps5.
    rewrite <- Nat.add_succ_l in Ps5; remember (S si) as ssi; simpl in Ps5.
    rewrite Hs3, Hb, digit_add_1_r in Ps5.
    rewrite digit_add_0_l in Ps5.
    remember (fst_same x y (ssi + dj5)) as s6 eqn:Ps6 .
    symmetry in Ps6.
    apply fst_same_iff in Ps6; simpl in Ps6.
    destruct s6 as [dj6| ].
     rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Ps5.
     rewrite <- Nat.add_assoc, Hs3 in Ps5.
     exfalso; revert Ps5; apply digit_neq_1_0.

     exfalso; revert Ps5; apply digit_neq_1_0.

    pose proof (Hn2 0 (Nat.lt_0_succ di2)) as H.
    rewrite Hs3, Hb in H.
    exfalso; revert H; apply digit_neq_1_0.

 destruct s3 as [di3| ].
  destruct Hs3 as (Hn3, Hs3); rewrite Hs3; reflexivity.

  pose proof (Hs1 0) as H.
  rewrite Nat.add_0_r in H.
  unfold I_add_i, carry in H.
  remember (S si) as ssi; simpl in H.
  rewrite digit_add_0_r in H.
  remember (fst_same x 0 ssi) as s4 eqn:Hs4 .
  symmetry in Hs4.
  apply fst_same_iff in Hs4; simpl in Hs4.
  destruct s4 as [di4| ].
   destruct Hs4 as (Hn4, Hs4).
   rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Hs4.
   rewrite Hs3 in Hs4.
   exfalso; revert Hs4; apply digit_neq_1_0.

   rewrite digit_add_1_r in H.
   apply oppd_inj in H.
   pose proof (Hs2 0) as H1.
   rewrite Nat.add_0_r, H in H1; symmetry in H1.
   exfalso; revert H1; apply no_fixpoint_oppd.
Qed.

Theorem I_add_add_0_l_when_both_hs_has_relay : ∀ x y i dj2 dj5,
  fst_same ((x + 0)%I + y) 0 (S i) = Some dj2
  → fst_same (x + y) 0 (S i) = Some dj5
  → (I_add_i ((x + 0)%I + y) 0 i = I_add_i (x + y) 0 i)%D.
Proof.
intros x y i dj2 dj5 Ps2 Ps5.
unfold I_add_i, carry.
remember (S i) as si; simpl.
do 2 rewrite digit_add_0_r.
rewrite Ps2, Ps5.
remember Ps2 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, H); rewrite H; clear H.
remember Ps5 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, H); rewrite H; clear H.
do 2 rewrite digit_add_0_r.
remember (fst_same (x + 0%I) y (S i)) as s1 eqn:Hs1 .
symmetry in Hs1.
subst si.
destruct s1 as [di1| ].
 eapply I_add_add_0_l_when_lhs_has_relay; eauto .

 eapply I_add_add_0_l_when_lhs_has_no_relay; eauto .
Qed.

Theorem I_add_add_0_l_when_relay : ∀ x y i di1,
  fst_same (x + 0%I) y (S i) = Some di1
  → fst_same (x + y) 0 (S i) ≠ None.
Proof.
intros x y i di1 Hs1 Hs5.
apply I_add_add_0_l_when_lhs_has_relay in Hs1.
remember (S i) as si.
unfold I_add_i, carry in Hs1.
rewrite <- Heqsi in Hs1; simpl in Hs1.
unfold I_add_i in Hs1 at 1.
unfold carry in Hs1.
rewrite <- Heqsi in Hs1; simpl in Hs1.
rewrite digit_add_0_r in Hs1.
apply fst_same_iff in Hs5; simpl in Hs5.
remember (fst_same x y si) as s8 eqn:Hs8 .
apply fst_same_sym_iff in Hs8.
destruct s8 as [di8| ].
 destruct Hs8 as (Hn8, Hs8).
 destruct di8.
  clear Hn8; rewrite Nat.add_0_r in Hs8, Hs1.
  apply I_add_inf_1_eq_if in Hs5; auto.
  destruct Hs5 as (Has, Hbs).
  remember (fst_same x 0 si) as s3 eqn:Hs3 .
  apply fst_same_sym_iff in Hs3; simpl in Hs3.
  destruct s3 as [di3| ].
   destruct Hs3 as (Hn3, Hs3).
   rewrite Hs3, digit_add_0_r in Hs1.
   remember (fst_same (x + 0%I) y si) as s4 eqn:Hs4 .
   apply fst_same_sym_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4).
    unfold I_add_i, carry in Hs1.
    rewrite <- Nat.add_succ_l in Hs1.
    remember (S si) as ssi; simpl in Hs1.
    rewrite digit_add_0_r in Hs1.
    remember (fst_same x 0 (ssi + di4)) as s5 eqn:Hs5 .
    apply fst_same_sym_iff in Hs5; simpl in Hs5.
    destruct s5 as [di5| ].
     destruct Hs5 as (Hn5, Hs5); rewrite Hs5, digit_add_0_r in Hs1.
     rewrite Heqssi, Nat.add_succ_l in Hs5.
     rewrite <- Nat.add_succ_r, <- Nat.add_assoc in Hs5.
     simpl in Hs5.
     rewrite Has in Hs5.
     exfalso; revert Hs5; apply digit_neq_1_0.

     rewrite digit_add_1_r in Hs1.
     unfold I_add_i, carry in Hs4.
     rewrite <- Nat.add_succ_l in Hs4.
     rewrite <- Heqssi in Hs4; simpl in Hs4.
     rewrite digit_add_0_r in Hs4.
     remember (fst_same x 0 (ssi + di4)) as s6 eqn:Hs6 .
     destruct s6 as [di6| ].
      rewrite Hs5, digit_add_1_r in Hs4.
      destruct di4.
       rewrite Nat.add_0_r, <- digit_opp_add_r in Hs1.
       exfalso; revert Hs1; apply no_fixpoint_oppd.

       rewrite Has, Hbs in Hs4.
       exfalso; revert Hs4; apply digit_neq_0_1.

      rewrite digit_add_1_r in Hs4.
      destruct di4.
       rewrite Nat.add_0_r, <- digit_opp_add_r in Hs1.
       exfalso; revert Hs1; apply no_fixpoint_oppd.

       rewrite Has, Hbs in Hs4.
       exfalso; revert Hs4; apply digit_neq_0_1.

    destruct di3.
     rewrite Nat.add_0_r in Hs3.
     rewrite Hs3 in Hs1.
     rewrite digit_add_1_r, digit_add_0_r in Hs1.
     exfalso; revert Hs1; apply no_fixpoint_oppd.

     rewrite Has in Hs3.
     exfalso; revert Hs3; apply digit_neq_1_0.

   remember (fst_same (x + 0%I) y si) as s4 eqn:Hs4 .
   apply fst_same_sym_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4); rewrite Hs4 in Hs1.
    unfold I_add_i, carry in Hs4.
    rewrite <- Nat.add_succ_l in Hs4.
    remember (S si) as ssi; simpl in Hs4.
    rewrite digit_add_0_r in Hs4.
    remember (fst_same x 0 (ssi + di4)) as s5 eqn:Hs5 .
    apply fst_same_sym_iff in Hs5; simpl in Hs5.
    destruct s5 as [di5| ].
     destruct Hs5 as (Hn5, Hs5).
     rewrite Heqssi, Nat.add_succ_l in Hs5.
     rewrite <- Nat.add_succ_r, <- Nat.add_assoc in Hs5.
     simpl in Hs5.
     rewrite Has in Hs5.
     exfalso; revert Hs5; apply digit_neq_1_0.

     clear Hs1.
     rewrite Hs3, digit_add_1_r in Hs4.
     symmetry in Hs4; simpl in Hs4.
     destruct di4.
      rewrite Nat.add_0_r in Hs4; clear Hs5.
      clear Hn4.
      pose proof (Hs3 0) as H; rewrite Nat.add_0_r in H.
      rewrite H, Hs4 in Hs8.
      revert Hs8; apply digit_neq_1_0.

      rewrite Hbs in Hs4.
      revert Hs4; apply digit_neq_1_0.

    pose proof (Hs3 0) as H; rewrite Nat.add_0_r in H.
    rewrite H, digit_add_1_r in Hs1.
    do 2 rewrite digit_add_1_r in Hs1.
    apply oppd_inj in Hs1.
    rewrite <- digit_opp_add_l in Hs1.
    revert Hs1; apply no_fixpoint_oppd.

  pose proof (Hn8 0 (Nat.lt_0_succ di8)) as H.
  rewrite Nat.add_0_r in H.
  apply I_add_inf_1_neq_if in Hs5; auto.
  destruct Hs5 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
  rename H into Hxy.
  destruct (lt_dec j (si + S di8)) as [H1| H1].
   remember H1 as H; clear HeqH.
   apply Nat.le_sub_le_add_l in H.
   rewrite Nat.sub_succ_l in H; [ idtac | apply Nat.lt_le_incl; auto ].
   apply Hn8 in H.
   rewrite Nat.add_sub_assoc in H; [ idtac | apply Nat.lt_le_incl; auto ].
   rewrite Nat.add_comm, Nat.add_sub in H.
   rewrite Ha, Hb in H.
   exfalso; revert H; apply digit_neq_0_1.

   apply Nat.nlt_ge in H1.
   destruct (lt_dec (si + S di8) j) as [H2| H2].
    remember H2 as H; clear HeqH.
    apply Hni in H.
    rewrite Hs8 in H; symmetry in H.
    revert H; apply no_fixpoint_oppd.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H1; auto; clear H2.
    rewrite <- H1, Ha, digit_add_0_r in Hs1.
    remember (fst_same x 0 si) as s3 eqn:Hs3 .
    apply fst_same_sym_iff in Hs3; simpl in Hs3.
    destruct s3 as [di3| ].
     destruct Hs3 as (Hn3, Hs3); rewrite Hs3, digit_add_0_r in Hs1.
     remember (fst_same (x + 0%I) y si) as s4 eqn:Hs4 .
     apply fst_same_sym_iff in Hs4; simpl in Hs4.
     destruct s4 as [di4| ].
      destruct Hs4 as (Hn4, Hs4); rewrite Hs4 in Hs1.
      unfold I_add_i, carry in Hs4.
      rewrite <- Nat.add_succ_l in Hs4.
      remember (S si) as ssi; simpl in Hs4.
      rewrite digit_add_0_r in Hs4.
      remember (fst_same x 0 (ssi + di4)) as s5 eqn:Hs5 .
      apply fst_same_sym_iff in Hs5; simpl in Hs5.
      destruct s5 as [di5| ].
       destruct Hs5 as (Hn5, Hs5); rewrite Hs5, digit_add_0_r in Hs4.
       destruct (lt_dec j (si + di4)) as [H2| H2].
        pose proof (Hat (si + di4 + di5 - j)) as H3.
        rewrite <- Nat.sub_succ_l in H3.
         rewrite Nat.add_sub_assoc in H3.
          rewrite Nat.add_comm, Nat.add_sub in H3.
          do 2 rewrite <- Nat.add_succ_l in H3.
          rewrite <- Heqssi, Hs5 in H3.
          exfalso; revert H3; apply digit_neq_0_1.

          apply Nat.lt_le_incl.
          eapply Nat.lt_le_trans; [ eauto  | idtac ].
          rewrite <- Nat.add_succ_r.
          apply Nat.le_sub_le_add_l.
          rewrite Nat.sub_diag; apply Nat.le_0_l.

         apply Nat.lt_le_incl.
         eapply Nat.lt_le_trans; eauto .
         apply Nat.le_sub_le_add_l.
         rewrite Nat.sub_diag; apply Nat.le_0_l.

        apply Nat.nlt_ge in H2.
        destruct (lt_dec (si + di4) j) as [H3| H3].
         remember H3 as H; clear HeqH.
         apply Hni in H.
         rewrite Hs4 in H; symmetry in H.
         revert H; apply no_fixpoint_oppd.

         apply Nat.nlt_ge in H3.
         apply Nat.le_antisymm in H2; auto.
         pose proof (Hat di5) as H.
         rewrite H2, Nat.add_succ_r in H.
         do 2 rewrite <- Nat.add_succ_l in H.
         rewrite <- Heqssi, Hs5 in H.
         exfalso; revert H; apply digit_neq_0_1.

       rewrite digit_add_1_r in Hs4.
       destruct (lt_dec (si + di4) j) as [H2| H2].
        pose proof (Hs5 (j - S (si + di4))) as H.
        rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
        rewrite <- Nat.add_succ_l, <- Heqssi in H.
        rewrite Nat.add_comm, Nat.add_sub, Ha in H.
        exfalso; revert H; apply digit_neq_0_1.

        apply Nat.nlt_ge in H2.
        destruct (lt_dec j (si + di4)) as [H3| H3].
         pose proof (Hat (si + di4 - S j)) as H4.
         pose proof (Hbt (si + di4 - S j)) as H5.
         rewrite <- Nat.sub_succ_l in H4; [ idtac | assumption ].
         rewrite <- Nat.sub_succ_l in H5; [ idtac | assumption ].
         simpl in H4, H5.
         rewrite Nat.add_sub_assoc in H4; [ idtac | assumption ].
         rewrite Nat.add_sub_assoc in H5; [ idtac | assumption ].
         rewrite Nat.add_comm, Nat.add_sub in H4.
         rewrite Nat.add_comm, Nat.add_sub in H5.
         rewrite H4, H5 in Hs4.
         exfalso; revert Hs4; apply digit_neq_0_1.

         apply Nat.nlt_ge in H3.
         apply Nat.le_antisymm in H3; auto.
         rewrite <- H3, Ha, Hb in Hs4.
         exfalso; revert Hs4; apply digit_neq_1_0.

      rewrite digit_add_1_r in Hs1.
      revert Hs1; apply no_fixpoint_oppd.

     pose proof (Hs3 (j - si)) as H.
     apply Nat.lt_le_incl in Hij.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_comm, Nat.add_sub in H.
     rewrite Ha in H.
     exfalso; revert H; apply digit_neq_0_1.

 pose proof (Hs8 0) as H; rewrite Nat.add_0_r in H.
 apply I_add_inf_1_neq_if in Hs5; auto; clear H.
 destruct Hs5 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 pose proof (Hs8 (j - si)) as H.
 apply Nat.lt_le_incl in Hij.
 rewrite Nat.add_sub_assoc in H; auto.
 rewrite Nat.add_comm, Nat.add_sub in H.
 rewrite Ha, Hb in H.
 exfalso; revert H; apply digit_neq_0_1.
Qed.

Theorem I_add_add_0_l_when_no_relay : ∀ x y i,
  fst_same (x + 0%I) y (S i) = None
  → fst_same (x + y) 0 (S i) = None
  → (I_add_i (x + 0%I) y i = oppd (I_add_i x y i))%D.
Proof.
intros x y i Hs1 Hs5.
unfold I_add_i, carry.
remember (S i) as si; simpl.
rewrite Hs1.
rewrite digit_opp_add_l, digit_opp_add_r.
rewrite digit_add_1_r, digit_opp_add_r.
unfold I_add_i, carry.
rewrite <- Heqsi; simpl.
rewrite digit_add_0_r.
do 2 rewrite <- digit_add_assoc.
apply digit_add_compat; [ reflexivity | idtac ].
rewrite digit_add_comm.
apply digit_add_compat; [ reflexivity | idtac ].
apply fst_same_iff in Hs1.
apply fst_same_iff in Hs5.
simpl in Hs1, Hs5.
remember (fst_same x 0 si) as s3 eqn:Hs3 .
apply fst_same_sym_iff in Hs3; simpl in Hs3.
destruct s3 as [di3| ].
 destruct Hs3 as (Hn3, Hs3); rewrite Hs3.
 remember (fst_same x y si) as s4 eqn:Hs4 .
 apply fst_same_sym_iff in Hs4; simpl in Hs4.
 destruct s4 as [di4| ].
  destruct Hs4 as (Hn4, Hs4).
  symmetry.
  pose proof (Hs1 0) as H; rewrite Nat.add_0_r in H.
  unfold I_add_i, carry in H.
  remember (S si) as ssi; simpl in H.
  rewrite digit_add_0_r in H.
  remember (fst_same x 0 ssi) as s6 eqn:Hs6 .
  apply fst_same_sym_iff in Hs6; simpl in Hs6.
  destruct s6 as [di6| ].
   destruct Hs6 as (Hn6, Hs6); rewrite Hs6, digit_add_0_r in H.
   apply I_add_inf_1_neq_if in Hs5; auto.
   destruct Hs5 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   rename H into Hxy.
   destruct (lt_dec (si + di4) j) as [H1| H1].
    remember H1 as H; clear HeqH.
    apply Hni in H.
    rewrite Hs4 in H; symmetry in H.
    exfalso; revert H; apply no_fixpoint_oppd.

    apply Nat.nlt_ge in H1.
    destruct (lt_dec j (si + di4)) as [H2| H2].
     assert (si < S j) as H by (eapply lt_le_trans; eauto ).
     apply lt_add_sub_lt_l in H2; auto; clear H.
     rename H2 into H.
     apply Hn4 in H.
     apply Nat.lt_le_incl in Hij.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_comm, Nat.add_sub in H.
     rewrite Ha, Hb in H.
     exfalso; revert H; apply digit_neq_0_1.

     apply Nat.nlt_ge in H2.
     apply Nat.le_antisymm in H2; auto.
     rewrite <- H2, Hb in Hs4.
     rewrite <- H2; assumption.

   rewrite digit_add_1_r in H.
   apply oppd_inj in H.
   apply I_add_inf_1_eq_if in Hs5; auto.
   destruct Hs5 as (Hat, Hbt).
   destruct di4.
    destruct di3; [ assumption | idtac ].
    rewrite Hat in Hs3.
    exfalso; revert Hs3; apply digit_neq_1_0.

    rename H into Hxy.
    pose proof (Hn4 0 (Nat.lt_0_succ di4)) as H.
    rewrite Nat.add_0_r, Hxy in H; symmetry in H.
    exfalso; revert H; apply no_fixpoint_oppd.

  pose proof (Hs5 0) as H.
  rewrite Nat.add_0_r in H.
  unfold I_add_i, carry in H.
  remember (S si) as ssi; simpl in H.
  remember (fst_same x y ssi) as s6 eqn:Hs6 .
  apply fst_same_sym_iff in Hs6; simpl in Hs6.
  destruct s6 as [di6| ].
   destruct Hs6 as (Hn6, Hs6).
   rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Hs6.
   rewrite Hs4 in Hs6.
   exfalso; revert Hs6; apply no_fixpoint_oppd.

   pose proof (Hs4 0) as H1.
   rewrite Nat.add_0_r in H1.
   rewrite H1 in H.
   rewrite digit_opp_add_diag_l in H.
   exfalso; revert H; apply digit_neq_0_1.

 destruct (fst_same x y si) as [di| ]; [ idtac | reflexivity ].
 rewrite Hs3; reflexivity.
Qed.

Theorem I_add_add_0_l_when_rhs_has_no_relay : ∀ x y i di2,
  fst_same ((x + 0)%I + y) 0 (S i) = Some di2
  → fst_same (x + y) 0 (S i) = None
  → (I_add_i ((x + 0)%I + y) 0 i = I_add_i (x + y) 0 i)%D.
Proof.
intros x y i di2 Hs2 Hs5.
unfold I_add_i, carry.
remember (S i) as si; simpl.
do 2 rewrite digit_add_0_r.
rewrite Hs2, Hs5.
remember Hs2 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, H); rewrite H; clear H.
rewrite digit_add_0_r, digit_add_1_r.
remember (fst_same (x + 0%I) y (S i)) as s1 eqn:Hs1 .
symmetry in Hs1; subst si.
destruct s1 as [di1| ].
 exfalso.
 eapply I_add_add_0_l_when_relay; eauto .

 eapply I_add_add_0_l_when_no_relay; eauto .
Qed.

Theorem I_add_add_0_r_not_without_relay : ∀ x y i,
  fst_same ((x + 0)%I + y) 0 i ≠ None.
Proof.
intros x y i Hs2.
apply fst_same_iff in Hs2; simpl in Hs2.
destruct (digit_eq_dec (((x + 0)%I) .[ i]) (y .[ i])) as [H1| H1].
 apply I_add_inf_1_eq_if in Hs2; auto.
 simpl in Hs2, H1.
 destruct Hs2 as (Hn2, Hs2).
 eapply not_I_add_0_inf_1_succ; eauto .

 apply digit_neq_eq_opp in H1.
 apply I_add_inf_1_neq_if in Hs2; auto.
 simpl in Hs2.
 destruct Hs2 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 eapply not_I_add_0_inf_1_succ; eauto .
Qed.

(* perhaps could be proved if associativity proved before;
   in that case, that would be very simple instead of these
   big lemmas before *)
Theorem I_add_add_0_r : ∀ x y, (x + 0 + y = x + y)%I.
Proof.
intros x y.
unfold I_eq; intros i; simpl.
remember (fst_same ((x + 0)%I + y) 0 (S i)) as s2 eqn:Hs2 .
remember (fst_same (x + y) 0 (S i)) as s5 eqn:Hs5 .
symmetry in Hs2, Hs5.
destruct s2 as [di2| ].
 destruct s5 as [di5| ].
  eapply I_add_add_0_l_when_both_hs_has_relay; eauto .

  eapply I_add_add_0_l_when_rhs_has_no_relay; eauto .

 exfalso; revert Hs2.
 eapply I_add_add_0_r_not_without_relay; eauto .
Qed.

Theorem I_add_compat_r : ∀ x y z, (x = y)%I → (x + z = y + z)%I.
Proof.
intros x y z Hxy.
remember (x + 0)%I as a1.
remember (y + 0)%I as b1.
remember Heqa1 as H; clear HeqH.
eapply I_noI_eq_compat_r with (y0 := y) (z := z) in H; eauto .
 subst a1 b1.
 do 2 rewrite I_add_add_0_r in H; assumption.

 subst a1 b1.
 do 2 rewrite I_add_0_r; assumption.
Qed.

Theorem I_add_compat : ∀ x y z t,
  (x = y)%I
  → (z = t)%I
  → (x + z = y + t)%I.
Proof.
intros x y z d Hxy Hcd.
transitivity (x + d)%I; [ idtac | apply I_add_compat_r; assumption ].
rewrite I_add_comm; symmetry.
rewrite I_add_comm; symmetry.
apply I_add_compat_r; assumption.
Qed.

Add Parametric Morphism : I_add
  with signature I_eq ==> I_eq ==> I_eq
  as I_add_morph.
Proof.
intros x y Hxy z d Hcd.
apply I_add_compat; assumption.
Qed.

(* *)

Theorem fst_same_in_range : ∀ x y i j di s,
  fst_same x y i = Some di
  → fst_same x y j = s
  → i ≤ j ≤ i + di
  → s = Some (i + di - j).
Proof.
intros x y i j di s Hi Hj (Hij, Hji).
apply fst_same_iff in Hi; simpl in Hi.
destruct Hi as (Hni, Hsi).
destruct s as [dj| ].
 apply fst_same_iff in Hj; simpl in Hj.
 destruct Hj as (Hnj, Hsj).
 destruct (lt_eq_lt_dec dj (i + di - j)) as [[H1| H1]| H1].
  apply Nat.lt_add_lt_sub_l in H1; rename H1 into H.
  apply lt_add_sub_lt_l in H.
   apply Hni in H; simpl in H.
   rewrite Nat.add_sub_assoc in H.
    rewrite Nat.add_comm, Nat.add_sub in H.
    rewrite Hsj in H; symmetry in H.
    exfalso; revert H; apply no_fixpoint_oppd.

    eapply le_trans; eauto; apply Nat.le_add_r.

   apply le_n_S.
   eapply le_trans; eauto; apply Nat.le_add_r.

  rewrite H1; reflexivity.

  apply Hnj in H1.
  rewrite Nat.add_sub_assoc in H1; [ idtac | assumption ].
  rewrite Nat.add_comm, Nat.add_sub in H1.
  rewrite Hsi in H1; symmetry in H1.
  exfalso; revert H1; apply no_fixpoint_oppd.

 apply fst_same_iff in Hj; simpl in Hj.
 pose proof (Hj (i + di - j)) as H.
 rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
 rewrite Nat.add_comm, Nat.add_sub in H.
 rewrite Hsi in H; symmetry in H.
 exfalso; revert H; apply no_fixpoint_oppd.
Qed.

Theorem carry_before_relay : ∀ x y i di,
  fst_same x y i = Some di
  → ∀ dj, dj ≤ di → (carry x y (i + dj) = x.[i + di])%D.
Proof.
intros x y i di Hs dj Hdj.
unfold carry; simpl.
remember (fst_same x y (i + dj)) as s1 eqn:Hs1 .
symmetry in Hs1.
eapply fst_same_in_range in Hs1; try eassumption.
 subst s1.
 rewrite Nat.add_sub_assoc.
  rewrite Nat.add_comm, Nat.add_sub; reflexivity.

  apply Nat.add_le_mono_l; assumption.

 split.
  apply Nat.le_sub_le_add_l.
  rewrite Nat.sub_diag.
  apply Nat.le_0_l.

  apply Nat.add_le_mono_l; assumption.
Qed.

(* old version that should be removed one day *)
Theorem carry_before_relay9 : ∀ x y i di,
  fst_same x y i = Some di
  → ∀ dj, dj < di → (carry x y (S (i + dj)) = x.[i + di])%D.
Proof.
intros x y i di Hs dj Hdj.
rewrite <- Nat.add_succ_r.
apply carry_before_relay; assumption.
Qed.

Theorem carry_before_inf_relay : ∀ x y i,
  fst_same x y i = None
  → ∀ dj, (carry x y (i + dj) = 1)%D.
Proof.
intros x y i Hs dj.
unfold carry; simpl.
remember (fst_same x y (i + dj)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ]; [ idtac | reflexivity ].
apply fst_same_iff in Hs; simpl in Hs.
destruct Hs1 as (_, Hs1).
rewrite <- Nat.add_assoc in Hs1.
rewrite Hs in Hs1.
exfalso; revert Hs1; apply no_fixpoint_oppd.
Qed.

(* old version that should be removed one day *)
Theorem carry_before_inf_relay9 : ∀ x y i,
  fst_same x y i = None
  → ∀ dj, (carry x y (S (i + dj)) = 1)%D.
Proof.
intros x y i Hs dj.
rewrite <- Nat.add_succ_r.
apply carry_before_inf_relay; assumption.
Qed.

Theorem I_eq_neq_prop : ∀ x y i,
  (x = y)%I
  → (x.[i] = 1)%D
  → (y.[i] = 0)%D
  → (∀ di, (x.[i+di] = 1)%D) ∧ (∀ di, (y.[i+di] = 0)%D) ∨
    (∀ di, (x.[i+S di] = 0)%D) ∧ (∀ di, (y.[i+S di] = 1)%D).
Proof.
intros x y i Hxy Hx Hy.
unfold I_eq, I_eq_ext in Hxy; simpl in Hxy.
pose proof (Hxy i) as H.
unfold I_add_i in H; simpl in H.
rewrite Hx, Hy, digit_add_1_l, digit_add_0_l in H.
unfold carry in H; simpl in H.
remember (fst_same x 0 (S i)) as sx eqn:Hsx .
remember (fst_same y 0 (S i)) as sy eqn:Hsy .
destruct sx as [dx| ].
 remember Hsx as HH; clear HeqHH.
 apply fst_same_sym_iff in HH; simpl in HH.
 destruct HH as (Hnx, Htx); rewrite Htx in H.
 destruct sy as [dy| ]; [ idtac | clear H ].
  remember Hsy as HH; clear HeqHH.
  apply fst_same_sym_iff in HH; simpl in HH.
  destruct HH as (Hny, Hty).
  rewrite Hty in H.
  exfalso;  revert H; apply digit_neq_1_0.

  right.
  remember Hsy as Hny; clear HeqHny.
  apply fst_same_sym_iff in Hny; simpl in Hny.
  split; intros di.
   destruct (lt_eq_lt_dec di dx) as [[H1| H1]| H1].
    pose proof (Hnx di H1) as H.
    rename H into Hdi.
    destruct dx; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
    pose proof (Hxy (S (i + dx))%nat) as H.
    unfold I_add_i in H; simpl in H.
    do 2 rewrite digit_add_0_r in H.
    rewrite Hnx in H; [ idtac | apply Nat.lt_succ_diag_r ].
    rewrite Hny in H.
    rewrite digit_add_1_l in H.
    symmetry in H.
    rewrite digit_add_1_l in H.
    apply oppd_inj in H.
    rewrite <- Nat.add_succ_l in H.
    symmetry in Hsx, H.
    erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
    symmetry in Hsy.
    simpl in H.
    do 2 rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
    simpl in H; rewrite Htx in H.
    exfalso; revert H; apply digit_neq_0_1.

    subst di.
    rewrite Nat.add_succ_r; assumption.

    remember (di - S dx)%nat as n eqn:Hn .
    apply Nat_sub_add_r in Hn; [ idtac | assumption ].
    subst di; clear H1.
    rewrite Nat.add_succ_r.
    induction n as (n, IHn) using all_lt_all.
    destruct n.
     rewrite Nat.add_1_r, Nat.add_succ_r.
     pose proof (Hxy (S (i + dx))) as H.
     unfold I_add_i in H; simpl in H.
     do 2 rewrite digit_add_0_r in H.
     rewrite Htx, Hny, digit_add_0_l, digit_add_1_l in H.
     symmetry in H, Hsx, Hsy.
     rewrite <- Nat.add_succ_l in H.
     rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
     symmetry in H.
     unfold carry in H; simpl in H.
     remember (fst_same x 0 (S (S (i + dx)))) as s1 eqn:Hs1 .
     destruct s1 as [di1| ].
      rename H into Hx1.
      destruct di1.
       rewrite Nat.add_0_r in Hx1; assumption.

       remember Hs1 as H; clear HeqH.
       apply fst_same_sym_iff in H; simpl in H.
       destruct H as (Hn1, _).
       pose proof (Hxy (S (S (i + dx)))) as H.
       unfold I_add_i in H; simpl in H.
       do 2 rewrite digit_add_0_r in H.
       rewrite <- Nat.add_succ_r in H.
       rewrite Hny, digit_add_1_l, Nat.add_succ_r in H.
       symmetry in H.
       rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H;
       rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
       symmetry in H, Hs1.
       replace dx with (dx + 0)%nat in H by apply Nat.add_0_r.
       simpl in H.
       rewrite Nat.add_succ_r, Nat.add_assoc in H.
       do 2 rewrite <- Nat.add_succ_l in H.
       assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
       erewrite carry_before_relay9 in H; try eassumption.
       simpl in H.
       rewrite Hx1, digit_add_0_r, Nat.add_0_r in H.
       assumption.

      exfalso; revert H; apply digit_neq_1_0.

     rewrite Nat.add_succ_r.
bbb.
     rewrite <- negb_involutive.
     apply digit_neq_eq_opp; simpl; intros Hdi.
     pose proof (Hxy (S (i + dx + S n))) as H.
     unfold I_add_i in H; simpl in H.
     do 2 rewrite digit_add_0_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite IHn in H; [ idtac | apply Nat.lt_succ_diag_r ].
     rewrite Hny, digit_add_0_l, digit_add_1_l in H.
     symmetry in H, Hsx, Hsy.
     rewrite <- Nat.add_succ_l in H.
     rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
     symmetry in H.
     unfold carry in H; simpl in H.
     remember (fst_same x 0 (S (S (i + (dx + S n))))) as s1 eqn:Hs1 .
     destruct s1 as [di1| ]; [ idtac | discriminate H ].
     rename H into Hx1.
     destruct di1.
      rewrite Nat.add_0_r, <- Nat.add_succ_r in Hx1.
      rewrite Hdi in Hx1; discriminate Hx1.

      remember Hs1 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn1, _).
      pose proof (Hxy (S (S (i + dx + S n)))) as H.
      unfold I_add_i in H; simpl in H.
      do 2 rewrite digit_add_0_r in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Nat.add_assoc in H.
      rewrite Nat.add_succ_r in H.
      rewrite Hdi, Hny, digit_add_1_l in H.
      apply oppd_inj in H.
      rewrite negb_involutive in H.
      rewrite <- Nat.add_succ_l in H.
      rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
      symmetry in H, Hs1.
      remember (S i + S (dx + S n))%nat as z.
      replace (S z) with (S z + 0)%nat in H by apply Nat.add_0_r.
      subst z.
      rewrite <- Nat.add_succ_l in H; simpl in H.
      rewrite <- Nat.add_succ_l in H.
      rewrite <- Nat.add_succ_r in Hs1.
      assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H.
      do 4 rewrite Nat.add_succ_r in H.
      do 3 rewrite Nat.add_succ_r in Hx1.
      simpl in H.
      rewrite Nat.add_assoc in Hx1.
      simpl in Hx1.
      rewrite Nat.add_assoc in H.
      rewrite Hx1 in H; discriminate H.

   rewrite Nat.add_succ_r; simpl; apply Hny.

 destruct sy as [dy| ]; [ idtac | discriminate H ].
 symmetry in H; simpl in H.
 remember Hsy as HH; clear HeqHH.
 apply fst_same_sym_iff in HH; simpl in HH.
 destruct HH as (Hny, Hty); clear H.
 left.
 remember Hsx as Hnx; clear HeqHnx.
 apply fst_same_sym_iff in Hnx; simpl in Hnx.
 split; intros di.
  destruct (lt_eq_lt_dec di dy) as [[H1| H1]| H1].
   pose proof (Hny di H1) as H.
   destruct dy; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
   rename H into Hdi.
   pose proof (Hxy (S (i + dy))%nat) as H.
   unfold I_add_i in H; simpl in H.
   do 2 rewrite digit_add_0_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite digit_add_1_l in H.
   apply oppd_inj in H.
   rewrite negb_involutive in H.
   rewrite <- Nat.add_succ_l in H.
   symmetry in Hsy.
   erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
   symmetry in Hsx.
   rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
   simpl in H; rewrite Hty in H; discriminate H.

   subst di.
   destruct dy; [ rewrite Nat.add_0_r; assumption | idtac ].
   rewrite Nat.add_succ_r; apply Hnx.

   destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
   rewrite Nat.add_succ_r; apply Hnx.

  destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
  rewrite Nat.add_succ_r.
  destruct (lt_eq_lt_dec di dy) as [[H1| H1]| H1].
   pose proof (Hny di H1) as H.
   destruct dy; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
   rename H into Hdi.
   pose proof (Hxy (S (i + dy))%nat) as H.
   unfold I_add_i in H; simpl in H.
   do 2 rewrite digit_add_0_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite digit_add_1_l in H.
   apply oppd_inj in H.
   rewrite negb_involutive in H.
   rewrite <- Nat.add_succ_l in H.
   symmetry in Hsy.
   erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
   symmetry in Hsx.
   rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
   simpl in H; rewrite Hty in H; discriminate H.

   subst di; assumption.

   remember (di - S dy)%nat as n eqn:Hn .
   apply Nat_sub_add_r in Hn; [ idtac | assumption ].
   subst di; clear H1.
   rewrite Nat.add_succ_r.
   induction n as (n, IHn) using all_lt_all.
   destruct n; [ clear IHn | idtac ].
    rewrite Nat.add_succ_r.
    rewrite <- negb_involutive.
    apply digit_neq_eq_opp; simpl; intros Hdi.
    rewrite Nat.add_0_r in Hdi.
    pose proof (Hxy (S (i + dy))) as H.
    unfold I_add_i in H; simpl in H.
    do 2 rewrite digit_add_0_r in H.
    rewrite Hnx, Hty, digit_add_0_l, digit_add_1_l in H.
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
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, _).
     pose proof (Hxy (S (S (i + dy)))) as H.
     unfold I_add_i in H; simpl in H.
     do 2 rewrite digit_add_0_r in H.
     rewrite <- Nat.add_succ_r in H.
     pose proof (Hn1 O (Nat.lt_0_succ di1)) as HH.
     rewrite Nat.add_0_r, <- Nat.add_succ_r in HH.
     rewrite HH, Hnx, digit_add_1_l in H.
     apply oppd_inj in H.
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
    apply digit_neq_eq_opp; simpl; intros Hdi.
    pose proof (Hxy (S (i + dy + S n))) as H.
    unfold I_add_i in H; simpl in H.
    do 2 rewrite digit_add_0_r in H.
    rewrite <- Nat.add_assoc in H.
    pose proof (IHn n (Nat.lt_succ_diag_r n)) as HH.
    rewrite <- Nat.add_succ_r in HH.
    rewrite <- Nat.add_succ_r in HH.
    rewrite Nat.add_succ_r in HH.
    rewrite Hnx, HH, digit_add_0_l, digit_add_1_l in H.
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
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, _).
     pose proof (Hxy (S (S (i + dy + S n)))) as H.
     unfold I_add_i in H; simpl in H.
     do 2 rewrite digit_add_0_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite Hdi in H.
     rewrite <- Nat.add_succ_r in H.
     rewrite Hnx, digit_add_1_l in H.
     rewrite <- Nat.add_succ_l in H.
     erewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     apply oppd_inj in H; simpl in H.
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

Theorem I_eq_prop : ∀ x y,
  (x = y)%I
  ↔ I_eq_ext x y ∨
    ∃ i,
    (∀ j, j < i → x.[j] = y.[j]) ∧
    x.[i] ≠ y.[i] ∧
    (i = 0 ∧ (∀ j, x.[j] = x.[0]) ∧ (∀ j, y.[j] = y.[0]) ∨
     (∀ di, x.[i+S di] = y.[i]) ∧ (∀ di, y.[i+S di] = x.[i])).
Proof.
(* à nettoyer (la 2ème partie) *)
intros x y.
split; intros Hxy.
 remember (fst_same x (- y) 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Ht1).
  right; exists di1.
  split.
   intros j Hdj.
   rewrite Hn1; [ idtac | assumption ].
   rewrite negb_involutive; reflexivity.

   split.
    intros H; rewrite Ht1 in H.
    revert H; apply no_fixpoint_oppd.

    remember (x .[ di1]) as b eqn:Hxi1 .
    symmetry in Hxi1.
    apply oppd_inj in Ht1; rewrite Ht1.
    destruct b.
     eapply I_eq_neq_prop in Hxi1; try eassumption.
     destruct Hxi1 as [(Hx, Hy)| (Hx, Hy)].
      destruct di1.
       left.
       split; [ reflexivity | idtac ].
       simpl in Hx, Hy.
       split; intros j; [ do 2 rewrite Hx | do 2 rewrite Hy ]; reflexivity.

       exfalso.
       clear Ht1.
       pose proof (Hn1 di1 (Nat.lt_succ_diag_r di1)) as H.
       rewrite negb_involutive in H.
       pose proof (Hxy di1) as HH; simpl in HH.
       unfold I_add_i in HH; simpl in HH.
       do 2 rewrite digit_add_0_r in HH.
       rewrite H in HH.
       apply xorb_move_l_r_1 in HH.
       rewrite digit_add_assoc, digit_add_nilpotent in HH.
       rewrite digit_add_0_l in HH.
       unfold carry in HH; simpl in HH.
       remember (fst_same x 0 (S di1)) as s2 eqn:Hs2 .
       remember (fst_same y 0 (S di1)) as s3 eqn:Hs3 .
       destruct s2 as [dj2| ].
        apply fst_same_sym_iff in Hs2; simpl in Hs2.
        destruct Hs2 as (Hn2, Ht2).
        rewrite <- Nat.add_succ_l, Hx in Ht2; discriminate Ht2.

        clear Hs2.
        apply fst_same_sym_iff in Hs3; simpl in Hs3.
        destruct s3 as [dj3| ]; [ idtac | clear HH ].
         rewrite <- Nat.add_succ_l, Hy in HH; discriminate HH.

         pose proof (Hy 0) as HH; simpl in HH.
         rewrite Hs3 in HH; discriminate HH.

      right; split; intros di; [ apply Hx | apply Hy ].

     simpl in Ht1; simpl.
     symmetry in Hxy.
     eapply I_eq_neq_prop in Hxi1; try eassumption.
     destruct Hxi1 as [(Hy, Hx)| (Hy, Hx)].
      destruct di1.
       left.
       split; [ reflexivity | idtac ].
       simpl in Hx, Hy.
       split; intros j; [ do 2 rewrite Hx | do 2 rewrite Hy ]; reflexivity.

       exfalso.
       clear Ht1.
       pose proof (Hn1 di1 (Nat.lt_succ_diag_r di1)) as H.
       rewrite negb_involutive in H.
       pose proof (Hxy di1) as HH; simpl in HH.
       unfold I_add_i in HH; simpl in HH.
       do 2 rewrite digit_add_0_r in HH.
       rewrite H in HH.
       apply xorb_move_l_r_1 in HH.
       rewrite digit_add_assoc, digit_add_nilpotent in HH.
       rewrite digit_add_0_l in HH.
       unfold carry in HH; simpl in HH.
       remember (fst_same x 0 (S di1)) as s2 eqn:Hs2 .
       remember (fst_same y 0 (S di1)) as s3 eqn:Hs3 .
       destruct s2 as [dj2| ].
        apply fst_same_sym_iff in Hs2; simpl in Hs2.
        destruct Hs2 as (Hn2, Ht2).
        rewrite Ht2 in HH.
        destruct s3 as [dj3| ]; [ idtac | discriminate HH ].
        simpl in Hy.
        rewrite Hy in HH; discriminate HH.

        apply fst_same_sym_iff in Hs2; simpl in Hs2.
        clear H.
        pose proof (Hx 0) as H; simpl in H.
        rewrite Hs2 in H; discriminate H.

      right; split; intros di; [ apply Hx | apply Hy ].

  left; intros i.
  rewrite Hs1, negb_involutive; reflexivity.

 destruct Hxy as [Hxy| Hxy].
  apply I_eq_ext_eq; assumption.

  destruct Hxy as (i, (Heq, (Hne, Hxy))).
  destruct Hxy as [(Hi, (Hx, Hy))| (Hx, Hy)].
   subst i.
   clear Heq.
   unfold I_eq; intros i; simpl.
   unfold I_add_i; simpl.
   do 2 rewrite digit_add_0_r.
   rewrite Hx, Hy.
   unfold carry; simpl.
   remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
   remember (fst_same y 0 (S i)) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s1 as [dj1| ].
    destruct Hs1 as (Hn1, Ht1).
    rewrite Ht1, digit_add_0_r.
    destruct s2 as [dj2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, digit_add_0_r.
     rewrite Hx in Ht1.
     rewrite Hy in Ht2.
     rewrite <- Ht2 in Ht1; contradiction.

     rewrite digit_add_1_r.
     apply digit_neq_eq_opp; assumption.

    rewrite digit_add_1_r.
    destruct s2 as [di2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, digit_add_0_r.
     apply digit_neq_eq_opp in Hne.
     rewrite Hne, negb_involutive; reflexivity.

     pose proof (Hs1 0) as H.
     rewrite <- Hs2 with (dj := 0) in H.
     rewrite Hx, Hy in H; contradiction.

   unfold I_eq; intros j; simpl.
   unfold I_add_i; simpl.
   do 2 rewrite digit_add_0_r.
   unfold carry; simpl.
   remember (fst_same x 0 (S j)) as s1 eqn:Hs1 .
   remember (fst_same y 0 (S j)) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s1 as [di1| ].
    destruct Hs1 as (Hn1, Ht1).
    rewrite Ht1, digit_add_0_r.
    destruct s2 as [di2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, digit_add_0_r.
     rewrite <- Nat.add_succ_r in Ht1, Ht2.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      apply Heq in H1; assumption.

      subst j.
      destruct (lt_eq_lt_dec di1 di2) as [[H1| H1]| H1].
       apply Hn2 in H1.
       rewrite Hx in Ht1.
       rewrite Hy in Ht2.
       rewrite <- Ht1 in Ht2; contradiction.

       subst di2.
       rewrite <- Ht2, Hx, Hy in Ht1.
       symmetry in Ht1; contradiction.

       apply Hn1 in H1.
       rewrite Hx in Ht1.
       rewrite Hy in Ht2.
       rewrite <- Ht1 in Ht2; contradiction.

      pose proof (Hx (j - i + di1)) as H.
      rewrite Nat.add_succ_r in H.
      rewrite Nat.add_assoc in H.
      apply Nat.lt_le_incl in H1.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      remember (i + j - i) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite H in Ht1; clear H.
      pose proof (Hy (j - i + di2)) as H.
      rewrite Nat.add_succ_r in H.
      rewrite Nat.add_assoc in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      remember (i + j - i) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Ht1, H in Ht2.
      contradiction.

     rewrite digit_add_1_r.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      pose proof (Hs2 (i - j + di1)) as H.
      rewrite Nat.add_assoc in H.
      remember H1 as HH; clear HeqHH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      remember (j + i - j) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hy in H.
      rewrite H in Hne; clear H.
      pose proof (Hs2 (i - S j)) as H.
      rewrite <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      symmetry in H; contradiction.

      subst j.
      apply digit_neq_eq_opp; assumption.

      pose proof (Hx (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hxy.
      pose proof (Hy (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hyx.
      rewrite <- Hxy, <- Hyx in Hne.
      apply digit_neq_eq_opp, not_eq_sym; assumption.

    rewrite digit_add_1_r.
    destruct s2 as [di2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, digit_add_0_r.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      pose proof (Hs1 (i - j + di2)) as H.
      rewrite Nat.add_assoc in H.
      remember H1 as HH; clear HeqHH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      remember (j + i - j) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hx in H.
      rewrite H in Hne; clear H.
      pose proof (Hs1 (i - S j)) as H.
      rewrite <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      contradiction.

      subst j; symmetry.
      apply digit_neq_eq_opp, not_eq_sym; assumption.

      pose proof (Hy (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hxy.
      pose proof (Hx (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hyx.
      rewrite <- Hxy, <- Hyx in Hne.
      symmetry.
      apply digit_neq_eq_opp; assumption.

     rewrite digit_add_1_r; f_equal.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      apply Heq; assumption.

      subst j.
      pose proof (Hs1 0) as H.
      rewrite <- Nat.add_succ_r, Hx in H.
      rewrite H in Hne; clear H.
      pose proof (Hs2 0) as H.
      rewrite <- Nat.add_succ_r, Hy in H.
      rewrite H in Hne; clear H.
      exfalso; apply Hne; reflexivity.

      pose proof (Hx (j - i)) as H.
      rewrite Nat.add_succ_r in H.
      remember H1 as HH; clear HeqHH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      rewrite Nat.add_comm, Nat.add_sub in H.
      replace j with (j + 0) in H by apply Nat.add_0_r.
      rewrite Hs1 in H.
      rewrite <- H in Hne; clear H.
      pose proof (Hy (j - i)) as H.
      rewrite Nat.add_succ_r in H.
      remember H1 as HH; clear HeqHH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      rewrite Nat.add_comm, Nat.add_sub in H.
      replace j with (j + 0) in H by apply Nat.add_0_r.
      rewrite Hs2 in H.
      symmetry in H; contradiction.
Qed.
