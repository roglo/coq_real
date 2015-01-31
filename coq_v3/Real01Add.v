(* addition module 1 in I: a commutative monoid *)

Require Import Utf8 QArith NPeano.
Require Import Oracle Real01.

Set Implicit Arguments.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).
Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).

Open Scope nat_scope.

(* using oracle to find the first identical digit between two numbers *)

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

Theorem forall_and_distr : ∀ α (P Q : α → Prop),
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x).
Proof. intros; split; intros x; apply H. Qed.

Theorem forall_add_succ_r : ∀ α i f (x : α),
  (∀ j, f (i + S j) = x)
  → id (∀ j, f (S i + j) = x).
Proof.
intros α i f x; unfold id; intros H j.
rewrite Nat.add_succ_l, <- Nat.add_succ_r; apply H.
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

Theorem nat_le_sub_add_r : ∀ a b c,
  a ≤ b
  → c = b - a
  → b = a + c.
Proof.
intros a b c Hab Hc; subst c.
rewrite Nat.add_sub_assoc; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

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

Theorem negb_xorb_diag_l : ∀ a, negb a ⊕ a = true.
Proof. intros a; destruct a; reflexivity. Qed.

Theorem negb_xorb_diag_r : ∀ a, a ⊕ negb a = true.
Proof. intros a; destruct a; reflexivity. Qed.

Theorem xorb_shuffle0 : ∀ a b c, a ⊕ b ⊕ c = a ⊕ c ⊕ b.
Proof.
intros a b c.
do 2 rewrite xorb_assoc; f_equal.
apply xorb_comm.
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

(* commutativity *)

Theorem fst_same_comm : ∀ x y i, fst_same x y i = fst_same y x i.
Proof.
intros x y i.
apply fst_same_iff.
remember (fst_same y x i) as syx eqn:Hsyx .
symmetry in Hsyx.
apply fst_same_iff in Hsyx.
destruct syx as [di| ]; [ idtac | intros dj; apply negb_sym, Hsyx ].
destruct Hsyx as (Hns, Hs).
split; auto.
intros dj Hdjn; apply negb_sym, Hns; assumption.
Qed.

Theorem carry_comm : ∀ x y i, carry x y i = carry y x i.
Proof.
intros x y i.
unfold carry; simpl.
rewrite fst_same_comm.
remember (fst_same y x i) as s eqn:Hs .
destruct s as [di| ]; [ idtac | reflexivity ].
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct Hs; symmetry; assumption.
Qed.

Theorem I_add_i_comm : ∀ x y i, I_add_i x y i = I_add_i y x i.
Proof.
intros x y i.
unfold I_add_i, carry.
rewrite fst_same_comm.
remember (fst_same y x (S i)) as s eqn:Hs .
symmetry in Hs.
apply fst_same_iff in Hs.
destruct s as [di| ]; [ idtac | f_equal; apply xorb_comm ].
f_equal; [ apply xorb_comm | destruct Hs; auto ].
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

Theorem carry_compat : ∀ x y z t j,
  (∀ i, x .[ i] = z .[ i])
  → (∀ i, y .[ i] = t .[ i])
  → carry x y j = carry z t j.
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
  carry (x + y) z i = carry (y + x) z i.
Proof.
intros x y z i.
apply carry_compat; [ apply I_add_i_comm | reflexivity ].
Qed.

Theorem carry_comm_r : ∀ x y z i,
  carry x (y + z) i = carry x (z + y) i.
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
  (∀ dj, I_add_i x 0 (i + dj) = true)
  → id (∀ dk, x .[i + dk] = true).
Proof.
intros x i Hs dk.
revert i Hs.
induction dk; intros.
 rewrite Nat.add_0_r.
 pose proof (Hs 0) as H; simpl in H.
 rewrite Nat.add_0_r in H.
 unfold I_add_i, carry in H; simpl in H.
 rewrite xorb_false_r in H.
 remember (fst_same x 0 (S i)) as s2 eqn:Hs2 .
 symmetry in Hs2.
 apply fst_same_iff in Hs2; simpl in Hs2.
 destruct s2 as [di2| ].
  destruct Hs2 as (Hn2, Hs2).
  rewrite Hs2, xorb_false_r in H.
  assumption.

  rewrite xorb_true_r in H.
  apply negb_true_iff in H.
  pose proof (Hs 1) as H1; simpl in H1.
  unfold I_add_i, carry in H1; simpl in H1.
  rewrite xorb_false_r in H1.
  remember (fst_same x 0 (S (i + 1))) as s3 eqn:Hs3 .
  symmetry in Hs3.
  apply fst_same_iff in Hs3; simpl in Hs3.
  destruct s3 as [di3| ].
   destruct Hs3 as (Hn3, Hs3).
   rewrite Hs3 in H1.
   rewrite xorb_false_r in H1.
   pose proof (Hs2 (S di3)) as H2.
   rewrite <- Nat.add_assoc in Hs3.
   simpl in Hs3.
   rewrite Hs3 in H2; discriminate H2.

   rewrite xorb_true_r in H1.
   apply negb_true_iff in H1.
   pose proof (Hs2 0) as H2.
   rewrite Nat.add_0_r in H2.
   rewrite Nat.add_1_r in H1.
   rewrite H1 in H2; discriminate H2.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 apply IHdk; intros dj.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hs.
Qed.

Theorem not_I_add_0_inf_1 : ∀ x i, ¬ (∀ dj, I_add_i x 0 (i + dj) = true).
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
rewrite xorb_false_r in H.
remember (fst_same x 0 si) as s2 eqn:Hs2 .
symmetry in Hs2.
apply fst_same_iff in Hs2; simpl in Hs2.
destruct s2 as [di2| ].
 destruct Hs2 as (Hn2, Hs2).
 subst si.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hs2.
 rewrite Hk in Hs2; discriminate Hs2.

 rewrite xorb_true_r in H.
 apply negb_true_iff in H.
 rename H into H1.
 pose proof (Hk 0) as H; simpl in H.
 rewrite Nat.add_0_r in H.
 rewrite H1 in H; discriminate H.
Qed.

Theorem not_I_add_0_inf_1_succ : ∀ x i,
  ¬ (∀ dj, I_add_i x 0 (i + S dj) = true).
Proof.
intros x i H.
eapply not_I_add_0_inf_1 with (i := S i); intros dj.
rewrite Nat.add_succ_l, <- Nat.add_succ_r.
apply H.
Qed.

Theorem I_add_i_0_r : ∀ x i, I_add_i (x + 0%I) 0 i = I_add_i x 0 i.
Proof.
intros x i.
unfold I_add_i at 1.
unfold carry.
remember (S i) as si; simpl.
rewrite xorb_false_r.
remember (fst_same (x + 0%I) 0 si) as s1 eqn:Hs1 .
symmetry in Hs1.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hs1, xorb_false_r; reflexivity.

 exfalso; eapply not_I_add_0_inf_1; eauto .
Qed.

Theorem I_add_0_r : ∀ x, (x + 0 = x)%I.
Proof.
intros x.
unfold I_eq.
apply I_add_i_0_r.
Qed.

(* compatibility with equality *)

Theorem I_add_i_compat_r : ∀ x y z j,
  (∀ i, x .[ i] = y .[ i])
  → I_add_i y z j = I_add_i x z j.
Proof.
intros x y z j Hxy.
unfold I_add_i.
rewrite Hxy; f_equal.
apply carry_compat_r; assumption.
Qed.

Theorem I_add_i_compat : ∀ x y z t j,
  (∀ i, x .[ i] = z .[ i])
  → (∀ i, y .[ i] = t .[ i])
  → I_add_i x y j = I_add_i z t j.
Proof.
intros x y z t j Hxz Hyt.
unfold I_add_i.
rewrite Hxz, Hyt; f_equal.
apply carry_compat; assumption.
Qed.

Theorem I_noI_eq_eq : ∀ x0 y0 x y,
  x = (x0 + 0)%I
  → y = (y0 + 0)%I
  → (x = y)%I
  → ∀ i, x .[ i] = y .[ i].
Proof.
intros x0 y0 x y Ha Hb Hxy i.
unfold I_eq in Hxy; simpl in Hxy.
pose proof (Hxy i) as Hi.
unfold I_add_i, carry in Hi.
remember (S i) as si; simpl in Hi.
do 2 rewrite xorb_false_r in Hi.
remember (fst_same x 0 si) as s1 eqn:Hs1 .
remember (fst_same y 0 si) as s2 eqn:Hs2 .
symmetry in Hs1, Hs2.
apply fst_same_iff in Hs1.
apply fst_same_iff in Hs2.
simpl in Hs1, Hs2.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hs1, xorb_false_r in Hi.
 destruct s2 as [di2| ].
  destruct Hs2 as (Hn2, Hs2).
  rewrite Hs2, xorb_false_r in Hi; assumption.

  exfalso; revert Hs2; rewrite Hb; apply not_I_add_0_inf_1.

 exfalso; revert Hs1; rewrite Ha; apply not_I_add_0_inf_1.
Qed.

Theorem carry_noI_eq_compat_r : ∀ x0 y0 x y z n,
  x = (x0 + 0)%I
  → y = (y0 + 0)%I
  → (x = y)%I
  → carry (x + z) 0 n = carry (y + z) 0 n.
Proof.
intros x0 y0 x y z n Ha Hb Hxy.
apply carry_compat_r; simpl.
intros; apply I_add_i_compat_r.
eapply I_noI_eq_eq; eassumption.
Qed.

Theorem I_noI_eq_compat_r : ∀ x0 y0 x y z,
  x = (x0 + 0)%I
  → y = (y0 + 0)%I
  → (x = y)%I
  → (x + z = y + z)%I.
Proof.
intros x0 y0 x y z Ha Hb Hxy.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
do 2 rewrite xorb_false_r; f_equal.
 apply I_add_i_compat_r.
 intros j; symmetry.
 eapply I_noI_eq_eq; eassumption.

 eapply carry_noI_eq_compat_r; eassumption.
Qed.

Fixpoint first_false_before x i :=
  match i with
  | 0 => None
  | S j => if x.[j] then first_false_before x j else Some j
  end.

Theorem first_false_before_none_iff : ∀ x i,
  first_false_before x i = None
  ↔ (∀ k, k < i → x.[k] = true).
Proof.
intros x i.
split.
 intros Hi k Hki.
 revert k Hki.
 induction i; intros.
  exfalso; revert Hki; apply Nat.nlt_0_r.

  simpl in Hi.
  remember (x .[ i]) as ai eqn:Hai .
  symmetry in Hai.
  destruct ai; [ idtac | discriminate Hi ].
  destruct (eq_nat_dec k i) as [H1| H1].
   subst k; assumption.

   apply IHi; auto.
   apply Nat.nle_gt; intros H.
   apply Nat.succ_le_mono in Hki.
   apply Nat.le_antisymm in H; auto.

 intros Hki.
 induction i; [ reflexivity | simpl ].
 remember (x .[ i]) as ai eqn:Hai .
 symmetry in Hai.
 destruct ai.
  apply IHi; intros k Hk.
  apply Hki.
  apply Nat.lt_lt_succ_r; assumption.

  apply not_true_iff_false in Hai.
  exfalso; apply Hai, Hki.
  apply Nat.lt_succ_r; reflexivity.
Qed.

Theorem first_false_before_some_iff : ∀ x i j,
  first_false_before x i = Some j
  ↔ j < i ∧
    x.[j] = false ∧
    (∀ k, j < k → k < i → x.[k] = true).
Proof.
intros x i j.
split.
 intros Hij.
 revert j Hij.
 induction i; intros; [ discriminate Hij | idtac ].
 simpl in Hij.
 remember (x .[ i]) as ai eqn:Hai .
 symmetry in Hai.
 destruct ai.
  apply IHi in Hij.
  destruct Hij as (Hji, (Hj, Hk)).
  split; [ apply Nat.lt_lt_succ_r; auto | idtac ].
  split; [ assumption | idtac ].
  intros k Hjk Hki.
  destruct (eq_nat_dec k i) as [H1| H1].
   subst k; assumption.

   apply Hk; auto.
   apply Nat.succ_le_mono in Hki.
   apply Nat.nle_gt; intros H.
   apply Nat.le_antisymm in H; auto.

  injection Hij; clear Hij; intros; subst j.
  split; [ apply Nat.lt_succ_r; auto | idtac ].
  split; [ assumption | idtac ].
  intros k Hik Hki.
  apply Nat.succ_le_mono, Nat.nlt_ge in Hki.
  contradiction.

 intros (Hji, (Haj, Hjk)).
 revert j Hji Haj Hjk.
 induction i; intros; [ exfalso; revert Hji; apply Nat.nlt_0_r | simpl ].
 remember (x .[ i]) as ai eqn:Hai .
 symmetry in Hai.
 destruct ai.
  apply IHi; auto.
  destruct (eq_nat_dec i j) as [H1| H1].
   subst j; rewrite Haj in Hai; discriminate Hai.

   apply Nat.succ_le_mono in Hji.
   apply Nat.nle_gt; intros H.
   apply Nat.le_antisymm in H; auto.

  apply Nat.succ_le_mono in Hji.
  destruct (le_dec i j) as [H1| H1].
   apply Nat.le_antisymm in H1; auto.

   apply Nat.nle_gt in H1.
   apply Hjk in H1; [ idtac | apply Nat.lt_succ_r; auto ].
   rewrite Hai in H1.
   discriminate H1.
Qed.

Theorem no_room_for_infinite_carry : ∀ x y i di1 di2 di3,
  (∀ dj : nat, dj < di2 → I_add_i x 0 (S i + dj) = negb (y .[ S i + dj]))
  → (∀ dj : nat, x .[ S (S i) + di2 + dj] = true)
  → (∀ dj : nat, dj < di3 → x .[ S i + dj] = negb (y .[ S i + dj]))
  → x .[ S i + di2] = true
  → x .[ S i + di1] = false
  → di1 < di2
  → di2 < di3
  → False.
Proof.
intros x y i di1 di2 di3 Hn1 Hs4 Hn2 Hs1 Hs3 H4 H3.
remember (S i) as si.
remember (S si) as ssi.
remember (first_false_before x (si + di2)) as j eqn:Hj .
symmetry in Hj.
destruct j as [j| ].
 apply first_false_before_some_iff in Hj.
 destruct Hj as (Hji, (Hjf, Hk)).
 assert (i < j) as Hij.
  apply Nat.nle_gt; intros H.
  rewrite Hk in Hs3; [ discriminate Hs3 | idtac | idtac ].
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
   rewrite Hjf, xorb_false_r, xorb_false_l in H.
   remember (fst_same x 0 sj) as s7 eqn:Hs7 .
   symmetry in Hs7.
   apply fst_same_iff in Hs7; simpl in Hs7.
   destruct s7 as [di7| ].
    destruct Hs7 as (Hn7, Hs7).
    rewrite Hs7 in H.
    symmetry in H.
    apply negb_false_iff in H.
    rewrite Hk in Hs7; [ discriminate Hs7 | idtac | idtac ].
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
      rewrite Hs7 in H; discriminate H.

      apply Nat.nlt_ge in H5.
      apply Nat.le_antisymm in H5; auto.
      rewrite <- H5, Hs1 in Hs7; discriminate Hs7.

    symmetry in H.
    apply negb_true_iff in H.
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
     rewrite Hjf, Hbt in H; discriminate H.

 rewrite first_false_before_none_iff in Hj.
 rewrite Hj in Hs3; [ discriminate Hs3 | idtac ].
 apply Nat.add_lt_mono_l; assumption.
Qed.

Theorem I_add_inf_true_eq_if : ∀ x y i,
  (∀ di, I_add_i x y (i + di) = true)
  → x.[i] = y.[i]
  → (∀ di, x.[i + S di] = true) ∧
    (∀ di, y.[i + S di] = true).
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
  rewrite xorb_nilpotent, xorb_false_l in H.
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
   rewrite H1, negb_xorb_diag_l, xorb_true_l in H.
   apply negb_true_iff in H.
   remember (S si) as ssi.
   remember (fst_same x y ssi) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs2.
   destruct s2 as [di2| ]; [ idtac | discriminate H ].
   destruct Hs2 as (Hn2, Hb2).
   rewrite H in Hb2.
   rename H into Ha2; symmetry in Hb2.
   destruct (lt_dec di1 di2) as [H2| H2].
    apply Hn2 in H2.
    rewrite Ha1, Hb1 in H2; discriminate H2.

    apply Nat.nlt_ge in H2.
    destruct (lt_dec di2 di1) as [H3| H3].
     apply Nat.succ_lt_mono in H3.
     apply Hn1 in H3.
     rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H3.
     rewrite Ha2, Hb2 in H3; discriminate H3.

     apply Nat.nlt_ge in H3.
     apply Nat.le_antisymm in H2; auto.
     subst di2; clear H3.
     rewrite Ha1 in Ha2; discriminate Ha2.

  clear H.
  pose proof (Hdi 1) as H.
  rewrite Nat.add_1_r, <- Heqsi in H.
  unfold I_add_i, carry in H.
  pose proof (Hs1 0) as H1.
  rewrite Nat.add_0_r in H1.
  rewrite H1, negb_xorb_diag_l, xorb_true_l in H.
  apply negb_true_iff in H.
  remember (S si) as ssi.
  remember (fst_same x y ssi) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2.
  destruct s2 as [di2| ]; [ idtac | discriminate H ].
  destruct Hs2 as (Hn2, Hb2).
  rewrite H in Hb2.
  rename H into Ha2; symmetry in Hb2.
  pose proof (Hs1 (S di2)) as H.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H.
  rewrite Ha2, Hb2 in H; discriminate H.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l in IHdi.
 do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 remember (S i) as si.
 remember (S si) as ssi.
 pose proof (Hdi (S di)) as H.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqsi in H.
 unfold I_add_i, carry in H.
 destruct IHdi as (Ha, Hb).
 rewrite Ha, Hb in H.
 rewrite xorb_true_l, xorb_false_l in H.
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
   rewrite H1, negb_xorb_diag_l, xorb_true_l in H.
   apply negb_true_iff in H.
   rewrite <- Nat.add_succ_l in H.
   remember (S ssi) as sssi.
   remember (fst_same x y (sssi + di)) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs2.
   destruct s2 as [di2| ]; [ idtac | discriminate H ].
   destruct Hs2 as (Hn2, Hb2).
   rewrite H in Hb2.
   rename H into Ha2; symmetry in Hb2.
   destruct (lt_dec di1 di2) as [H2| H2].
    apply Hn2 in H2.
    rewrite Ha1, Hb1 in H2; discriminate H2.

    apply Nat.nlt_ge in H2.
    destruct (lt_dec di2 di1) as [H3| H3].
     apply Nat.succ_lt_mono in H3.
     apply Hn1 in H3.
     rewrite Nat.add_succ_r, <- Nat.add_succ_l in H3.
     rewrite <- Nat.add_succ_l, <- Heqsssi in H3.
     rewrite Ha2, Hb2 in H3; discriminate H3.

     apply Nat.nlt_ge in H3.
     apply Nat.le_antisymm in H2; auto.
     subst di2; clear H3.
     rewrite Ha1 in Ha2; discriminate Ha2.

  clear H.
  pose proof (Hdi (S (S di))) as H.
  do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
  rewrite <- Heqsi, <- Heqssi in H.
  unfold I_add_i, carry in H.
  pose proof (Hs1 0) as H1.
  rewrite Nat.add_0_r in H1.
  rewrite H1, negb_xorb_diag_l, xorb_true_l in H.
  apply negb_true_iff in H.
  rewrite <- Nat.add_succ_l in H.
  remember (S ssi) as sssi.
  remember (fst_same x y (sssi + di)) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2.
  destruct s2 as [di2| ]; [ idtac | discriminate H ].
  destruct Hs2 as (Hn2, Hb2).
  rewrite Heqsssi, Nat.add_succ_l in Hb2.
  rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hb2.
  rewrite Hs1 in Hb2.
  destruct (y .[ ssi + di + S di2]); discriminate Hb2.
Qed.

Theorem I_add_inf_true_neq_if : ∀ x y i,
  (∀ di, I_add_i x y (i + di) = true)
  → x.[i] = negb (y.[i])
  → ∃ j,
    i < j ∧
    (∀ di, i + di < j → x.[i + di] = negb (y.[i + di])) ∧
    x.[j] = false ∧ y.[j] = false ∧
    (∀ di, x.[j + S di] = true) ∧
    (∀ di, y.[j + S di] = true).
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

  rewrite negb_xorb_diag_l, xorb_true_l in H.
  apply negb_true_iff in H.
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
   rewrite Hs1, Ha, xorb_false_r, xorb_false_l in H.
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
      rewrite H1, H2, xorb_true_r, xorb_false_l in H.
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
        rewrite Hxy3, negb_xorb_diag_l, xorb_true_l in H.
        do 3 rewrite <- Nat.add_succ_l in H.
        remember (S sssi) as ssssi.
        remember (fst_same x y (ssssi + di1 + di + di3)) as s4 eqn:Hs4 .
        symmetry in Hs4.
        apply fst_same_iff in Hs4; simpl in Hs4.
        destruct s4 as [di4| ]; [ idtac | discriminate H ].
        destruct Hs4 as (Hn4, Hs4).
        destruct di4.
         rewrite Nat.add_0_r in H.
         apply negb_true_iff in H.
         rewrite Nat.add_succ_r in Ha3.
         do 3 rewrite <- Nat.add_succ_l in Ha3.
         rewrite <- Heqssssi, H in Ha3.
         discriminate Ha3.

         rename H into Ha4.
         pose proof (Hn4 0 (Nat.lt_0_succ di4)) as H.
         rewrite Nat.add_0_r in H.
         rewrite Nat.add_succ_r in Hs3, Ha3.
         do 3 rewrite <- Nat.add_succ_l in Hs3, Ha3.
         rewrite <- Heqssssi in Hs3, Ha3.
         rewrite Hs3, Ha3 in H.
         discriminate H.

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
        rewrite Hs4 in H.
        destruct (y .[ ssssi + di1 + di + di4]); discriminate H.

        rewrite xorb_true_r in H.
        apply negb_true_iff in H.
        apply xorb_eq in H.
        rename H into Hxy1.
        pose proof (Hs3 0) as H.
        rewrite Nat.add_0_r in H.
        rewrite Hxy1 in H.
        destruct (y .[ sssi + di1 + di]); discriminate H.

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
     rewrite Hxy1, negb_xorb_diag_l, xorb_true_l in H.
     apply negb_true_iff in H.
     rewrite <- Nat.add_succ_l in H; remember (S ssi) as sssi.
     remember (fst_same x y (sssi + di1)) as s3 eqn:Hs3 .
     symmetry in Hs3.
     apply fst_same_iff in Hs3; simpl in Hs3.
     destruct s3 as [di3| ]; [ idtac | discriminate H ].
     destruct Hs3 as (Hn3, Hb3).
     rename H into Ha3.
     rewrite Ha3 in Hb3; symmetry in Hb3.
     rewrite Nat.add_succ_r in Hs2, Ha2.
     do 2 rewrite <- Nat.add_succ_l in Hs2, Ha2.
     rewrite <- Heqsssi in Hs2, Ha2.
     destruct (lt_dec di2 di3) as [H1| H1].
      apply Hn3 in H1.
      rewrite Hs2, Ha2 in H1; discriminate H1.

      apply Nat.nlt_ge in H1.
      destruct (lt_dec di3 di2) as [H2| H2].
       apply Nat.succ_lt_mono in H2.
       apply Hn2 in H2.
       rewrite Nat.add_succ_r in H2.
       do 2 rewrite <- Nat.add_succ_l in H2.
       rewrite <- Heqsssi in H2.
       rewrite Ha3, Hb3 in H2; discriminate H2.

       apply Nat.nlt_ge in H2.
       apply Nat.le_antisymm in H1; auto.
       subst di3; clear H2.
       rewrite Ha2 in Ha3; discriminate Ha3.

    clear H.
    pose proof (Hs2 0) as H.
    rewrite Nat.add_0_r in H.
    rename H into Ha1.
    pose proof (Hdi (S (S di1))) as H.
    do 2 rewrite Nat.add_succ_r in H.
    rewrite <- Nat.add_succ_l, <- Heqsi in H.
    rewrite <- Nat.add_succ_l, <- Heqssi in H.
    unfold I_add_i, carry in H.
    rewrite Ha1, negb_xorb_diag_l, xorb_true_l in H.
    apply negb_true_iff in H.
    rewrite <- Nat.add_succ_l in H.
    remember (S ssi) as sssi.
    remember (fst_same x y (sssi + di1)) as s3 eqn:Hs3 .
    symmetry in Hs3.
    apply fst_same_iff in Hs3; simpl in Hs3.
    destruct s3 as [di3| ]; [ idtac | discriminate H ].
    destruct Hs3 as (Hn3, Hs3).
    rename H into Ha3; rename Hs3 into Hb3.
    rewrite Ha3 in Hb3; symmetry in Hb3.
    pose proof (Hs2 (S di3)) as H.
    rewrite Nat.add_succ_r in H.
    do 2 rewrite <- Nat.add_succ_l in H.
    rewrite <- Heqsssi in H.
    rewrite Ha3, Hb3 in H; discriminate H.

 rewrite Hxy, negb_xorb_diag_l in H; discriminate H.
Qed.

Theorem I_add_add_0_l_when_lhs_has_relay : ∀ x y i di1,
  fst_same (x + 0%I) y (S i) = Some di1
  → I_add_i (x + 0%I) y i = I_add_i x y i.
Proof.
intros x y i di1 Hs1.
unfold I_add_i, carry at 1; remember (S i) as si; simpl.
rewrite Hs1.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Hs1).
rewrite Hs1.
unfold I_add_i, carry; rewrite <- Heqsi; simpl.
rewrite xorb_false_r.
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
  rewrite Hs3, xorb_false_r; f_equal.
  unfold I_add_i, carry in Hs1.
  rewrite <- Nat.add_succ_l in Hs1.
  remember (S si) as ssi.
  move Heqssi before Heqsi.
  simpl in Hs1; rewrite xorb_false_r in Hs1.
  remember (fst_same x 0 (ssi + di1)) as s4 eqn:Hs4 .
  symmetry in Hs4.
  apply fst_same_iff in Hs4; simpl in Hs4.
  destruct s4 as [di4| ].
   destruct Hs4 as (Hn4, Hs4).
   rewrite Hs4, xorb_false_r in Hs1.
   destruct (lt_dec di1 di2) as [H1| H1].
    remember H1 as H; clear HeqH.
    apply Hn2 in H.
    rewrite Hs1 in H.
    destruct (y .[ si + di1]); discriminate H.

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
      rewrite xorb_false_r, Hs2, Hs5, xorb_false_r in H.
      destruct (y .[ si + di2]); discriminate H.

      clear H.
      pose proof (Hs5 (di1 - di2 + di4)) as H.
      do 2 rewrite Nat.add_comm, Nat.add_assoc in H.
      rewrite Nat.add_assoc in H.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Nat.add_sub_swap in H; auto.
      rewrite Nat.sub_diag, Nat.add_0_l in H.
      rewrite Nat.add_comm, Nat.add_assoc in H.
      rewrite Hs4 in H; discriminate H.

     apply Nat.nlt_ge in H2.
     apply Nat.le_antisymm in H1; auto.

   rewrite xorb_true_r in Hs1.
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
     rewrite xorb_false_r, Hs2, Hs5, xorb_false_r in H.
     destruct (y .[ si + di2]); discriminate H.

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
      discriminate H.

      apply Nat.nlt_ge in H3.
      destruct (bool_dec (x .[ si + di2]) false) as [H4| H4].
       rewrite H4.
       apply negb_false_iff.
       pose proof (Hs5 (di1 - S di2)) as H.
       rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in H.
       do 2 rewrite Nat.add_comm, Nat.add_assoc in H.
       rewrite Nat.add_sub_assoc in H; auto.
       rewrite Nat.add_sub_swap in H; auto.
       rewrite Nat.sub_diag, Nat.add_0_l in H; simpl in H.
       rewrite Nat.add_comm.
       assumption.

       apply not_false_iff_true in H4.
       rewrite H4 in Hs2.
       symmetry in Hs2.
       exfalso.
       destruct (lt_dec di3 di2) as [H5| H5].
        remember H5 as H; clear HeqH.
        apply Hn2 in H.
        rewrite Hs3 in H; symmetry in H.
        apply negb_false_iff in H.
        rename H into Hb.
        remember H2 as H; clear HeqH.
        eapply Nat.lt_trans in H; [ idtac | eauto  ].
        apply Hn1 in H.
        rewrite Hb in H; simpl in H.
        unfold I_add_i, carry in H.
        rewrite <- Nat.add_succ_l, <- Heqssi in H.
        simpl in H.
        rewrite Hs3, xorb_false_r, xorb_false_l in H.
        remember (fst_same x 0 (ssi + di3)) as s6 eqn:Hs6 .
        symmetry in Hs6.
        apply fst_same_iff in Hs6; simpl in Hs6.
        destruct s6 as [di6| ]; [ idtac | discriminate H ].
        destruct Hs6 as (Hn6, Hs6).
        clear H.
        remember (first_false_before x (si + di2)) as j eqn:Hj .
        symmetry in Hj.
        destruct j as [j| ].
         apply first_false_before_some_iff in Hj.
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
           rewrite Hjf, xorb_false_r, xorb_false_l in H.
           remember (fst_same x 0 sj) as s7 eqn:Hs7 .
           symmetry in Hs7.
           apply fst_same_iff in Hs7; simpl in Hs7.
           destruct s7 as [di7| ].
            destruct Hs7 as (Hn7, Hs7).
            rewrite Hs7 in H.
            symmetry in H.
            apply negb_false_iff in H.
            destruct (lt_dec (sj + di7) (si + di2)) as [H1| H1].
             rewrite Hk in Hs7; auto; [ discriminate Hs7 | idtac ].
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
              rewrite Hs7 in H; discriminate H.

              apply Nat.nlt_ge in H6.
              apply Nat.le_antisymm in H1; auto.
              rewrite H1, H4 in Hs7; discriminate Hs7.

            symmetry in H.
            apply negb_true_iff in H.
            rename H into H6.
            assert (j - si < di2) as H by (eapply lt_add_sub_lt_r; eauto ).
            apply Hn2 in H.
            rewrite Nat.add_sub_assoc in H.
             rewrite Nat.add_comm, Nat.add_sub in H.
             rewrite Hjf, H6 in H; discriminate H.

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

              apply Hk in H; [ rewrite Hs3 in H; discriminate H | idtac ].
              apply Nat.add_lt_mono_l; assumption.

           apply Nat.nlt_ge; intros Hcont.
           rewrite Heqsi in Hcont.
           apply Nat.succ_le_mono in Hcont.
           rewrite Hk in Hs3; [ discriminate Hs3 | idtac | idtac ].
            rewrite Heqsi.
            eapply Nat.le_lt_trans; [ eauto  | idtac ].
            rewrite Nat.add_succ_l, <- Nat.add_succ_r.
            apply Nat.lt_sub_lt_add_l.
            rewrite Nat.sub_diag.
            apply Nat.lt_0_succ.

            apply Nat.add_lt_mono_l; assumption.

         rewrite first_false_before_none_iff in Hj.
         rewrite Hj in Hs3; [ discriminate Hs3 | idtac ].
         apply Nat.add_lt_mono_l; assumption.

        apply Nat.nlt_ge in H5.
        apply Nat.le_antisymm in H5; [ subst di3 | auto ].
        rewrite H4 in Hs3; discriminate Hs3.

    apply Nat.nlt_ge in H2.
    destruct (lt_dec di1 di2) as [H3| H3].
     pose proof (Hs4 (di2 - S di1)) as H.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Heqssi in H; simpl in H.
     rewrite Nat.add_shuffle0, Nat.add_sub in H.
     rewrite H in Hs2; symmetry in Hs2.
     rename H into Ha; move Ha after Hs2; rewrite Hs2.
     symmetry in Hs1; apply negb_sym in Hs1.
     remember (y .[ si + di1]) as bi eqn:Hbi .
     destruct bi; [ reflexivity | idtac ].
     symmetry in Hbi; simpl in Hs1.
     exfalso.
     destruct (lt_dec di1 di3) as [H1| H1].
      pose proof (Hs4 (di3 - S di1)) as H.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Heqssi in H; simpl in H.
      rewrite Nat.add_shuffle0, Nat.add_sub in H.
      rewrite Hs3 in H; discriminate H.

      apply Nat.nlt_ge in H1.
      destruct (eq_nat_dec di1 di3) as [H4| H4].
       subst di3.
       rewrite Hs1 in Hs3; discriminate Hs3.

       assert (di3 < di1) as H.
        apply Nat.nle_gt; intros H.
        apply Nat.le_antisymm in H; auto; contradiction.

        subst si ssi.
        eapply no_room_for_infinite_carry in Hs3; eauto .

     apply Nat.nlt_ge in H3.
     apply Nat.le_antisymm in H3; auto.

  do 3 rewrite xorb_assoc; f_equal.
  rewrite xorb_comm, xorb_assoc; f_equal.
  rewrite xorb_true_r.
  rewrite <- Hs2, Hs3, <- Hs1.
  apply negb_true_iff.
  unfold I_add_i, carry; rewrite <- Nat.add_succ_l.
  remember (S si) as ssi; simpl.
  rewrite Hs3, xorb_false_r, xorb_true_l.
  apply negb_false_iff.
  remember (fst_same x 0 (ssi + di1)) as s4 eqn:Hs4 .
  symmetry in Hs4.
  destruct s4 as [s4| ]; [ idtac | reflexivity ].
  rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r.
  rewrite <- Nat.add_assoc, Hs3; reflexivity.

 do 3 rewrite xorb_assoc; f_equal.
 rewrite xorb_comm, xorb_assoc; f_equal.
 destruct s3 as [di3| ].
  destruct Hs3 as (Hn3, Hs3).
  rewrite Hs3, xorb_false_r.
  rewrite <- Hs1.
  unfold I_add_i, carry.
  rewrite <- Nat.add_succ_l.
  remember (S si) as ssi; simpl.
  rewrite xorb_false_r.
  remember (fst_same x 0 (ssi + di1)) as s4 eqn:Hs4 .
  symmetry in Hs4.
  apply fst_same_iff in Hs4; simpl in Hs4.
  destruct s4 as [di4| ].
   destruct Hs4 as (Hn4, Hs4); rewrite Hs4.
   rewrite xorb_false_r.
   destruct (lt_dec di1 di3) as [H1| H1].
    remember H1 as H; clear HeqH.
    apply Hn3; assumption.

    apply Nat.nlt_ge in H1.
    destruct (lt_dec di3 di1) as [H2| H2].
     apply not_false_iff_true.
     intros Ha.
     remember Ha as Hb; clear HeqHb.
     rewrite Hs2 in Hb.
     apply negb_false_iff in Hb.
     rewrite <- Hs1 in Hb.
     unfold I_add_i, carry in Hb.
     rewrite <- Nat.add_succ_l in Hb.
     rewrite <- Heqssi in Hb; simpl in Hb.
     rewrite Ha, xorb_false_r, xorb_false_l in Hb.
     remember (fst_same x 0 (ssi + di1)) as s5 eqn:Hs5 .
     symmetry in Hs5.
     apply fst_same_iff in Hs5; simpl in Hs5.
     destruct s5 as [di5| ].
      destruct Hs5 as (Hn5, Hs5); rewrite Hs5 in Hb; discriminate Hb.

      rewrite Hs5 in Hs4; discriminate Hs4.

     apply Nat.nlt_ge, Nat.le_antisymm in H2; auto.
     subst di3; clear H1.
     rewrite Hs2 in Hs3.
     apply negb_false_iff in Hs3.
     rewrite <- Hs1 in Hs3.
     unfold I_add_i, carry in Hs3.
     rewrite <- Nat.add_succ_l in Hs3.
     rewrite <- Heqssi in Hs3; simpl in Hs3.
     rewrite xorb_false_r in Hs3.
     remember (fst_same x 0 (ssi + di1)) as s5 eqn:Hs5 .
     symmetry in Hs5.
     apply fst_same_iff in Hs5; simpl in Hs5.
     destruct s5 as [di5| ].
      destruct Hs5 as (Hn5, Hs5); rewrite Hs5 in Hs3.
      rewrite xorb_false_r in Hs3; assumption.

      rewrite Hs5 in Hs4; discriminate Hs4.

   rewrite xorb_true_r.
   apply negb_true_iff.
   unfold I_add_i, carry in Hs1.
   rewrite <- Nat.add_succ_l, <- Heqssi in Hs1.
   simpl in Hs1.
   rewrite xorb_false_r in Hs1.
   rewrite Hs2 in Hs1.
   remember (fst_same x 0 (ssi + di1)) as s5 eqn:Hs5 .
   symmetry in Hs5.
   apply fst_same_iff in Hs5; simpl in Hs5.
   destruct s5 as [di5| ].
    destruct Hs5 as (Hn5, Hs5); rewrite Hs5 in Hs1.
    rewrite xorb_false_r in Hs1.
    destruct (y .[ si + di1]); discriminate Hs1.

    clear Hs1 Hs5.
    destruct (lt_dec di1 di3) as [H1| H1].
     pose proof (Hs4 (di3 - S di1)) as H.
     rewrite Heqssi in H.
     rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_shuffle0, Nat.add_sub in H.
     rewrite Hs3 in H; discriminate H.

     apply Nat.nlt_ge in H1.
     destruct (lt_dec di3 di1) as [H2| H2].
      remember H2 as H; clear HeqH.
      apply Hn1 in H.
      unfold I_add_i, carry in H.
      rewrite <- Nat.add_succ_l, <- Heqssi in H; simpl in H.
      rewrite xorb_false_r in H.
      remember (fst_same x 0 (ssi + di3)) as s5 eqn:Hs5 .
      symmetry in Hs5.
      apply fst_same_iff in Hs5; simpl in Hs5.
      destruct s5 as [di5| ].
       destruct Hs5 as (Hn5, Hs5); rewrite Hs5 in H.
       rewrite xorb_false_r in H.
       apply not_true_iff_false; intros Ha.
       subst si ssi.
       eapply no_room_for_infinite_carry in Hs3; eauto .

       rewrite xorb_true_r, <- Hs2 in H.
       destruct (x .[ si + di3]); discriminate H.

      apply Nat.nlt_ge in H2.
      apply Nat.le_antisymm in H2; auto.
      subst di3; assumption.

  rewrite xorb_true_r, <- Hs2.
  apply Hs3.
Qed.

Theorem I_add_add_0_l_when_lhs_has_no_relay : ∀ x y i dj2 dj5,
  fst_same ((x + 0)%I + y) 0 (S i) = Some dj2
  → fst_same (x + y) 0 (S i) = Some dj5
  → fst_same (x + 0%I) y (S i) = None
  → I_add_i (x + 0%I) y i = I_add_i x y i.
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
rewrite xorb_false_r.
do 3 rewrite xorb_assoc; f_equal.
rewrite xorb_comm, xorb_assoc; f_equal.
rewrite xorb_true_l.
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
   rewrite xorb_false_r in H.
   remember (fst_same x 0 (ssi + di2)) as s4 eqn:Hs4 .
   symmetry in Hs4.
   apply fst_same_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4); rewrite Hs4, xorb_false_r in H.
    rewrite Hs2 in H.
    destruct (y .[ si + di2]); discriminate H.

    clear H.
    apply not_false_iff_true.
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
        rewrite Ps6 in H2.
        destruct (y .[ ssi + dj6]); discriminate H2.

        apply Nat.nlt_ge in H2.
        destruct (lt_dec di2 (S dj6)) as [H3| H3].
         destruct di2.
          rewrite Nat.add_0_r in Hs4.
          rewrite Nat.add_0_r in Hs2.
          rewrite <- Hs2, Hs4 in Ps5.
          rewrite xorb_true_r in Ps5.
          apply negb_false_iff in Ps5.
          destruct (x .[ si]); discriminate Ps5.

          apply Nat.succ_lt_mono in H3.
          apply Pn6 in H3.
          rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs2.
          rewrite <- Heqssi, H3 in Hs2.
          destruct (y .[ ssi + di2]); discriminate Hs2.

         apply Nat.nlt_ge in H3.
         apply Nat.le_antisymm; auto.

       rewrite <- H, Nat.add_succ_r, <- Nat.add_succ_l in Ha.
       rewrite <- Heqssi in Ha.
       rewrite Ha, xorb_false_r in Ps5.
       rewrite <- H in Hn2; clear H.
       assert (0 < S dj6) as H by apply Nat.lt_0_succ.
       apply Hn2 in H.
       rewrite Nat.add_0_r in H.
       rewrite H in Ps5.
       destruct (y .[ si]); discriminate Ps5.

      destruct di2.
       rewrite Nat.add_0_r in Hs2.
       rewrite <- Hs2 in Ps5.
       destruct (x .[ si]); discriminate Ps5.

       rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs2.
       rewrite <- Heqssi in Hs2.
       rewrite Ps6 in Hs2.
       destruct (y .[ ssi + di2]); discriminate Hs2.

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
          rewrite Ps6 in H3.
          destruct (y .[ ssi + S dj5 + di6]); discriminate H3.

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
           rewrite Hs2 in H.
           destruct (y .[ si + di2]); discriminate H.

           apply Nat.nlt_ge in H4.
           apply Nat.le_antisymm; auto.

         rewrite <- H in Ha.
         rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in Ha.
         rewrite Nat.add_assoc in Ha.
         rewrite Ha, xorb_false_r in Ps5.
         apply Hn2 in H2.
         rewrite H2 in Ps5.
         destruct (y .[ si + S dj5]); discriminate Ps5.

        pose proof (Ps6 (di2 - S (S dj5))) as H.
        rewrite Nat.add_sub_assoc in H; auto.
        rewrite Heqssi in H.
        rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
        rewrite Nat.add_shuffle0, Nat.add_sub in H.
        rewrite Hs2 in H.
        destruct (y .[ si + di2]); discriminate H.

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
         rewrite xorb_false_r in H.
         remember (fst_same x 0 (ssi + S dj5 + dj6)) as s7 eqn:Ps7 .
         symmetry in Ps7.
         apply fst_same_iff in Ps7; simpl in Ps7.
         destruct s7 as [dj7| ].
          destruct Ps7 as (Pn7, Ps7); rewrite Ps7, xorb_false_r in H.
          rename H into Hxy.
          pose proof (Hs1 (S (S dj5 + dj6))) as H.
          rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H.
          rewrite Nat.add_assoc in H.
          unfold I_add_i, carry in H.
          do 2 rewrite <- Nat.add_succ_l in H.
          remember (S ssi) as sssi; simpl in H.
          rewrite xorb_false_r in H.
          remember (fst_same x 0 (sssi + S dj5 + dj6)) as s8 eqn:Ps8 .
          symmetry in Ps8.
          apply fst_same_iff in Ps8; simpl in Ps8.
          destruct s8 as [dj8| ].
           destruct Ps8 as (Pn8, Ps8); rewrite Ps8, xorb_false_r in H.
           rewrite Ps6 in H.
           destruct (y .[ ssi + S dj5 + dj6]); discriminate H.

           clear H.
           pose proof (Hs4 (S dj5 + dj6 + dj7 - di2)) as H.
           rewrite Nat.add_sub_assoc in H.
            rewrite Nat.add_shuffle0, Nat.add_sub in H.
            do 2 rewrite Nat.add_assoc in H.
            rewrite Ps7 in H; discriminate H.

            eapply Nat.le_trans; eauto .
            rewrite <- Nat.add_assoc.
            apply Nat.le_sub_le_add_l.
            rewrite Nat.sub_diag.
            apply Nat.le_0_l.

          rewrite xorb_true_r in H.
          apply negb_sym in H.
          rewrite negb_involutive in H.
          destruct dj6.
           rewrite Nat.add_0_r in H.
           rewrite H in Ps5.
           rewrite Nat.add_0_r in Ps7.
           rewrite Ps7 in Ps5.
           rewrite xorb_true_r in Ps5.
           destruct (x .[ si + S dj5]); discriminate Ps5.

           rename H into Hyx.
           pose proof (Pn6 dj6 (Nat.lt_succ_diag_r dj6)) as H.
           rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hyx.
           rewrite <- Nat.add_succ_l in Hyx.
           rewrite <- Heqssi in Hyx.
           rewrite Hyx in H.
           destruct (x .[ ssi + S dj5 + dj6]); discriminate H.

         pose proof (Hs1 (S dj5)) as H.
         unfold I_add_i, carry in H.
         rewrite <- Nat.add_succ_l, <- Heqssi in H; simpl in H.
         rewrite xorb_false_r in H.
         remember (fst_same x 0 (ssi + S dj5)) as s7 eqn:Ps7 .
         symmetry in Ps7.
         apply fst_same_iff in Ps7; simpl in Ps7.
         destruct s7 as [dj7| ].
          destruct Ps7 as (Pn7, Ps7); rewrite Ps7, xorb_false_r in H.
          clear H.
          pose proof (Hs4 (S dj5 + dj7 - di2)) as H.
          rewrite Nat.add_sub_swap in H; auto.
          rewrite Nat.add_assoc in H.
          rewrite Nat.add_sub_assoc in H; auto.
          rewrite Nat.add_shuffle0, Nat.add_sub in H.
          rewrite Ps7 in H; discriminate H.

          rewrite xorb_true_r in H.
          apply negb_sym in H.
          rewrite negb_involutive in H.
          rewrite H in Ps5.
          destruct (x .[ si + S dj5]); discriminate Ps5.

        apply Nat.nlt_ge in H3.
        apply Nat.le_antisymm; auto.

      rewrite H in Ps5.
      unfold I_add_i, carry in Ps5.
      rewrite <- Nat.add_succ_l, <- Heqssi in Ps5.
      remember (fst_same x y (ssi + di2)) as s6 eqn:Ps6 .
      symmetry in Ps6.
      apply fst_same_iff in Ps6; simpl in Ps6.
      destruct s6 as [dj6| ].
       rewrite Hs4, Hs2, xorb_true_r in Ps5.
       destruct (y .[ si + di2]); discriminate Ps5.

       rewrite Hs2, xorb_true_r in Ps5.
       destruct (y .[ si + di2]); discriminate Ps5.

  symmetry; simpl.
  assert (∀ dj, (y .[ si + dj]) = true) as Hb.
   intros dj.
   apply negb_false_iff.
   rewrite <- Hs1.
   unfold I_add_i, carry.
   rewrite <- Nat.add_succ_l; remember (S si) as ssi; simpl.
   rewrite xorb_false_r.
   remember (fst_same x 0 (ssi + dj)) as s4 eqn:Hs4 .
   symmetry in Hs4.
   apply fst_same_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ]; [ idtac | rewrite Hs3; reflexivity ].
   destruct Hs4 as (Hn4, Hs4).
   rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Hs4.
   rewrite <- Nat.add_assoc, Hs3 in Hs4; discriminate Hs4.

   destruct di2.
    rewrite Nat.add_0_r in Hs2; rewrite Nat.add_0_r.
    clear Hn2.
    unfold I_add_i, carry in Ps5.
    rewrite <- Nat.add_succ_l in Ps5; remember (S si) as ssi; simpl in Ps5.
    rewrite Hs3, Hb, xorb_true_r in Ps5.
    rewrite xorb_false_l in Ps5.
    remember (fst_same x y (ssi + dj5)) as s6 eqn:Ps6 .
    symmetry in Ps6.
    apply fst_same_iff in Ps6; simpl in Ps6.
    destruct s6 as [dj6| ]; [ idtac | discriminate Ps5 ].
    rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Ps5.
    rewrite <- Nat.add_assoc, Hs3 in Ps5; discriminate Ps5.

    pose proof (Hn2 0 (Nat.lt_0_succ di2)) as H.
    rewrite Hs3, Hb in H; discriminate H.

 destruct s3 as [di3| ].
  destruct Hs3 as (Hn3, Hs3); rewrite Hs3; reflexivity.

  pose proof (Hs1 0) as H.
  rewrite Nat.add_0_r in H.
  unfold I_add_i, carry in H.
  remember (S si) as ssi; simpl in H.
  rewrite xorb_false_r in H.
  remember (fst_same x 0 ssi) as s4 eqn:Hs4 .
  symmetry in Hs4.
  apply fst_same_iff in Hs4; simpl in Hs4.
  destruct s4 as [di4| ].
   destruct Hs4 as (Hn4, Hs4).
   rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Hs4.
   rewrite Hs3 in Hs4; discriminate Hs4.

   rewrite xorb_true_r in H.
   apply negb_sym in H.
   rewrite negb_involutive in H.
   pose proof (Hs2 0) as H1.
   rewrite Nat.add_0_r, H in H1.
   destruct (x .[ si]); discriminate H1.
Qed.

Theorem I_add_add_0_l_when_both_hs_has_relay : ∀ x y i dj2 dj5,
  fst_same ((x + 0)%I + y) 0 (S i) = Some dj2
  → fst_same (x + y) 0 (S i) = Some dj5
  → I_add_i ((x + 0)%I + y) 0 i = I_add_i (x + y) 0 i.
Proof.
intros x y i dj2 dj5 Ps2 Ps5.
unfold I_add_i, carry.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
rewrite Ps2, Ps5.
remember Ps2 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, H); rewrite H; clear H.
remember Ps5 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, H); rewrite H; clear H.
do 2 rewrite xorb_false_r.
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
rewrite xorb_false_r in Hs1.
apply fst_same_iff in Hs5; simpl in Hs5.
remember (fst_same x y si) as s8 eqn:Hs8 .
apply fst_same_sym_iff in Hs8.
destruct s8 as [di8| ].
 destruct Hs8 as (Hn8, Hs8).
 destruct di8.
  clear Hn8; rewrite Nat.add_0_r in Hs8, Hs1.
  apply I_add_inf_true_eq_if in Hs5; auto.
  destruct Hs5 as (Has, Hbs).
  remember (fst_same x 0 si) as s3 eqn:Hs3 .
  apply fst_same_sym_iff in Hs3; simpl in Hs3.
  destruct s3 as [di3| ].
   destruct Hs3 as (Hn3, Hs3).
   rewrite Hs3, xorb_false_r in Hs1.
   remember (fst_same (x + 0%I) y si) as s4 eqn:Hs4 .
   apply fst_same_sym_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4).
    unfold I_add_i, carry in Hs1.
    rewrite <- Nat.add_succ_l in Hs1.
    remember (S si) as ssi; simpl in Hs1.
    rewrite xorb_false_r in Hs1.
    remember (fst_same x 0 (ssi + di4)) as s5 eqn:Hs5 .
    apply fst_same_sym_iff in Hs5; simpl in Hs5.
    destruct s5 as [di5| ].
     destruct Hs5 as (Hn5, Hs5); rewrite Hs5, xorb_false_r in Hs1.
     rewrite Heqssi, Nat.add_succ_l in Hs5.
     rewrite <- Nat.add_succ_r, <- Nat.add_assoc in Hs5.
     simpl in Hs5.
     rewrite Has in Hs5; discriminate Hs5.

     rewrite xorb_true_r in Hs1.
     unfold I_add_i, carry in Hs4.
     rewrite <- Nat.add_succ_l in Hs4.
     rewrite <- Heqssi in Hs4; simpl in Hs4.
     rewrite xorb_false_r in Hs4.
     remember (fst_same x 0 (ssi + di4)) as s6 eqn:Hs6 .
     destruct s6 as [di6| ].
      rewrite Hs5, xorb_true_r in Hs4.
      destruct di4.
       rewrite Nat.add_0_r in Hs1.
       rewrite <- negb_xorb_r in Hs1.
       destruct (x .[ i] ⊕ y .[ i] ⊕ x .[ si]); discriminate Hs1.

       rewrite Has, Hbs in Hs4; discriminate Hs4.

      rewrite xorb_true_r in Hs4.
      destruct di4.
       rewrite Nat.add_0_r in Hs1.
       rewrite <- negb_xorb_r in Hs1.
       destruct (x .[ i] ⊕ y .[ i] ⊕ x .[ si]); discriminate Hs1.

       rewrite Has, Hbs in Hs4; discriminate Hs4.

    destruct di3.
     rewrite Nat.add_0_r in Hs3.
     rewrite Hs3 in Hs1.
     destruct (x .[ i] ⊕ y .[ i]); discriminate Hs1.

     rewrite Has in Hs3; discriminate Hs3.

   remember (fst_same (x + 0%I) y si) as s4 eqn:Hs4 .
   apply fst_same_sym_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4); rewrite Hs4 in Hs1.
    unfold I_add_i, carry in Hs4.
    rewrite <- Nat.add_succ_l in Hs4.
    remember (S si) as ssi; simpl in Hs4.
    rewrite xorb_false_r in Hs4.
    remember (fst_same x 0 (ssi + di4)) as s5 eqn:Hs5 .
    apply fst_same_sym_iff in Hs5; simpl in Hs5.
    destruct s5 as [di5| ].
     destruct Hs5 as (Hn5, Hs5).
     rewrite Heqssi, Nat.add_succ_l in Hs5.
     rewrite <- Nat.add_succ_r, <- Nat.add_assoc in Hs5.
     simpl in Hs5.
     rewrite Has in Hs5; discriminate Hs5.

     clear Hs1.
     rewrite Hs3, xorb_true_r in Hs4.
     symmetry in Hs4; simpl in Hs4.
     destruct di4.
      rewrite Nat.add_0_r in Hs4; clear Hs5.
      clear Hn4.
      pose proof (Hs3 0) as H; rewrite Nat.add_0_r in H.
      rewrite H, Hs4 in Hs8; discriminate Hs8.

      rewrite Hbs in Hs4; discriminate Hs4.

    pose proof (Hs3 0) as H; rewrite Nat.add_0_r in H.
    rewrite H in Hs1.
    destruct (x .[ i]), (y .[ i]); discriminate Hs1.

  pose proof (Hn8 0 (Nat.lt_0_succ di8)) as H.
  rewrite Nat.add_0_r in H.
  apply I_add_inf_true_neq_if in Hs5; auto.
  destruct Hs5 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
  rename H into Hxy.
  destruct (lt_dec j (si + S di8)) as [H1| H1].
   remember H1 as H; clear HeqH.
   apply Nat.le_sub_le_add_l in H.
   rewrite Nat.sub_succ_l in H; [ idtac | apply Nat.lt_le_incl; auto ].
   apply Hn8 in H.
   rewrite Nat.add_sub_assoc in H; [ idtac | apply Nat.lt_le_incl; auto ].
   rewrite Nat.add_comm, Nat.add_sub in H.
   rewrite Ha, Hb in H; discriminate H.

   apply Nat.nlt_ge in H1.
   destruct (lt_dec (si + S di8) j) as [H2| H2].
    remember H2 as H; clear HeqH.
    apply Hni in H.
    rewrite Hs8 in H.
    destruct (y .[ si + S di8]); discriminate H.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H1; auto; clear H2.
    rewrite <- H1, Ha, xorb_false_r in Hs1.
    remember (fst_same x 0 si) as s3 eqn:Hs3 .
    apply fst_same_sym_iff in Hs3; simpl in Hs3.
    destruct s3 as [di3| ].
     destruct Hs3 as (Hn3, Hs3); rewrite Hs3, xorb_false_r in Hs1.
     remember (fst_same (x + 0%I) y si) as s4 eqn:Hs4 .
     apply fst_same_sym_iff in Hs4; simpl in Hs4.
     destruct s4 as [di4| ].
      destruct Hs4 as (Hn4, Hs4); rewrite Hs4 in Hs1.
      unfold I_add_i, carry in Hs4.
      rewrite <- Nat.add_succ_l in Hs4.
      remember (S si) as ssi; simpl in Hs4.
      rewrite xorb_false_r in Hs4.
      remember (fst_same x 0 (ssi + di4)) as s5 eqn:Hs5 .
      apply fst_same_sym_iff in Hs5; simpl in Hs5.
      destruct s5 as [di5| ].
       destruct Hs5 as (Hn5, Hs5); rewrite Hs5, xorb_false_r in Hs4.
       destruct (lt_dec j (si + di4)) as [H2| H2].
        pose proof (Hat (si + di4 + di5 - j)) as H3.
        rewrite <- Nat.sub_succ_l in H3.
         rewrite Nat.add_sub_assoc in H3.
          rewrite Nat.add_comm, Nat.add_sub in H3.
          do 2 rewrite <- Nat.add_succ_l in H3.
          rewrite <- Heqssi, Hs5 in H3; discriminate H3.

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
         rewrite Hs4 in H.
         destruct (y .[ si + di4]); discriminate H.

         apply Nat.nlt_ge in H3.
         apply Nat.le_antisymm in H2; auto.
         pose proof (Hat di5) as H.
         rewrite H2, Nat.add_succ_r in H.
         do 2 rewrite <- Nat.add_succ_l in H.
         rewrite <- Heqssi, Hs5 in H.
         discriminate H.

       rewrite xorb_true_r in Hs4.
       symmetry in Hs4.
       apply negb_sym in Hs4.
       destruct (lt_dec (si + di4) j) as [H2| H2].
        pose proof (Hs5 (j - S (si + di4))) as H.
        rewrite Nat.add_sub_assoc in H; auto.
        rewrite <- Nat.add_succ_l, <- Heqssi in H.
        rewrite Nat.add_comm, Nat.add_sub in H.
        rewrite Ha in H; discriminate H.

        apply Nat.nlt_ge in H2.
        destruct (lt_dec j (si + di4)) as [H3| H3].
         pose proof (Hat (si + di4 - S j)) as H4.
         pose proof (Hbt (si + di4 - S j)) as H5.
         rewrite <- Nat.sub_succ_l in H4; auto.
         rewrite <- Nat.sub_succ_l in H5; auto.
         simpl in H4, H5.
         rewrite Nat.add_sub_assoc in H4; auto.
         rewrite Nat.add_sub_assoc in H5; auto.
         rewrite Nat.add_comm, Nat.add_sub in H4.
         rewrite Nat.add_comm, Nat.add_sub in H5.
         rewrite H4, H5 in Hs4; discriminate Hs4.

         apply Nat.nlt_ge in H3.
         apply Nat.le_antisymm in H3; auto.
         rewrite <- H3, Ha, Hb in Hs4; discriminate Hs4.

      destruct (xorb (x .[ i]) (y .[ i])); discriminate Hs1.

     pose proof (Hs3 (j - si)) as H.
     apply Nat.lt_le_incl in Hij.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_comm, Nat.add_sub in H.
     rewrite Ha in H; discriminate H.

 pose proof (Hs8 0) as H; rewrite Nat.add_0_r in H.
 apply I_add_inf_true_neq_if in Hs5; auto; clear H.
 destruct Hs5 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 pose proof (Hs8 (j - si)) as H.
 apply Nat.lt_le_incl in Hij.
 rewrite Nat.add_sub_assoc in H; auto.
 rewrite Nat.add_comm, Nat.add_sub in H.
 rewrite Ha, Hb in H; discriminate H.
Qed.

Theorem I_add_add_0_l_when_no_relay : ∀ x y i,
  fst_same (x + 0%I) y (S i) = None
  → fst_same (x + y) 0 (S i) = None
  → I_add_i (x + 0%I) y i = negb (I_add_i x y i).
Proof.
intros x y i Hs1 Hs5.
unfold I_add_i, carry.
remember (S i) as si; simpl.
rewrite Hs1.
rewrite negb_xorb_l, negb_xorb_r.
rewrite xorb_true_r, negb_xorb_r.
unfold I_add_i, carry.
rewrite <- Heqsi; simpl.
rewrite xorb_false_r.
do 2 rewrite xorb_assoc; f_equal.
rewrite xorb_comm; f_equal.
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
  rewrite xorb_false_r in H.
  remember (fst_same x 0 ssi) as s6 eqn:Hs6 .
  apply fst_same_sym_iff in Hs6; simpl in Hs6.
  destruct s6 as [di6| ].
   destruct Hs6 as (Hn6, Hs6); rewrite Hs6, xorb_false_r in H.
   apply I_add_inf_true_neq_if in Hs5; auto.
   destruct Hs5 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   rename H into Hxy.
   destruct (lt_dec (si + di4) j) as [H1| H1].
    remember H1 as H; clear HeqH.
    apply Hni in H.
    rewrite Hs4 in H.
    destruct (y .[ si + di4]); discriminate H.

    apply Nat.nlt_ge in H1.
    destruct (lt_dec j (si + di4)) as [H2| H2].
     assert (si < S j) as H by (eapply lt_le_trans; eauto ).
     apply lt_add_sub_lt_l in H2; auto; clear H.
     rename H2 into H.
     apply Hn4 in H.
     apply Nat.lt_le_incl in Hij.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_comm, Nat.add_sub in H.
     rewrite Ha, Hb in H; discriminate H.

     apply Nat.nlt_ge in H2.
     apply Nat.le_antisymm in H2; auto.
     rewrite <- H2, Hb in Hs4.
     rewrite <- H2; assumption.

   rewrite xorb_true_r in H.
   apply negb_sym in H.
   rewrite negb_involutive in H.
   symmetry in H.
   apply I_add_inf_true_eq_if in Hs5; auto.
   destruct Hs5 as (Hat, Hbt).
   destruct di4.
    destruct di3; [ assumption | idtac ].
    rewrite Hat in Hs3; discriminate Hs3.

    rename H into Hxy.
    pose proof (Hn4 0 (Nat.lt_0_succ di4)) as H.
    rewrite Nat.add_0_r, Hxy in H.
    destruct (y .[ si]); discriminate H.

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
   destruct (y .[ si + S di6]); discriminate Hs6.

   pose proof (Hs4 0) as H1.
   rewrite Nat.add_0_r in H1.
   rewrite H1 in H.
   rewrite negb_xorb_diag_l in H.
   discriminate H.

 destruct (fst_same x y si) as [di| ]; [ idtac | reflexivity ].
 rewrite Hs3; reflexivity.
Qed.

Theorem I_add_add_0_l_when_rhs_has_no_relay : ∀ x y i di2,
  fst_same ((x + 0)%I + y) 0 (S i) = Some di2
  → fst_same (x + y) 0 (S i) = None
  → I_add_i ((x + 0)%I + y) 0 i = I_add_i (x + y) 0 i.
Proof.
intros x y i di2 Hs2 Hs5.
unfold I_add_i, carry.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
rewrite Hs2, Hs5.
remember Hs2 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, H); rewrite H; clear H.
rewrite xorb_false_r, xorb_true_r.
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
destruct (bool_dec (((x + 0)%I) .[ i]) (y .[ i])) as [H1| H1].
 apply I_add_inf_true_eq_if in Hs2; auto.
 simpl in Hs2, H1.
 destruct Hs2 as (Hn2, Hs2).
 eapply not_I_add_0_inf_1_succ; eauto .

 apply neq_negb in H1.
 apply I_add_inf_true_neq_if in Hs2; auto.
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

(* opposite *)

Theorem I_sub_diag : ∀ x, (x - x = 0)%I.
Proof.
intros x.
unfold I_eq; intros i; simpl.
unfold I_add_i, carry.
remember (S i) as si; simpl.
rewrite xorb_false_r.
rewrite fst_same_diag.
remember (fst_same (x - x) 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); rewrite Hs1, xorb_false_r.
 unfold I_add_i, carry.
 rewrite <- Heqsi; simpl.
 remember (fst_same x (- x) si) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 rewrite <- negb_xorb_r, negb_xorb_l, negb_xorb_diag_l.
 destruct s2 as [di2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Hs2).
 destruct (x .[ si + di2]); discriminate Hs2.

 destruct (bool_dec (x .[ si]) (negb (x .[ si]))) as [H1| H1].
  destruct (x .[ si]); discriminate H1.

  apply neq_negb in H1.
  apply I_add_inf_true_neq_if in Hs1; auto.
  simpl in Hs1.
  destruct Hs1 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
  rewrite Ha in Hb; discriminate Hb.
Qed.

(* associativity *)

Theorem fst_same_inf_after : ∀ x y i di,
  fst_same x y i = None
  → fst_same x y (i + di) = None.
Proof.
intros x y i di Hs.
apply fst_same_iff in Hs.
apply fst_same_iff; intros dj.
rewrite <- Nat.add_assoc.
apply Hs.
Qed.

Theorem I_add_inf_if : ∀ x y i,
  (∀ dj, I_add_i x y (i + dj) = true)
  → ∃ j,
    i < j ∧
    (∀ di, x.[j + S di] = true) ∧
    (∀ di, y.[j + S di] = true).
Proof.
intros x y i Hj.
destruct (bool_dec (x .[ i]) (y .[ i])) as [H1| H1].
 apply I_add_inf_true_eq_if in Hj; auto.
 destruct Hj as (Ha, Hb).
 exists (S i).
 split; [ apply Nat.lt_succ_diag_r | idtac ].
 split; intros di; rewrite Nat.add_succ_l, <- Nat.add_succ_r.
   apply Ha.

   apply Hb.

 apply neq_negb in H1.
 apply I_add_inf_true_neq_if in Hj; auto.
 destruct Hj as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 exists j.
 split; [ assumption | split; assumption ].
Qed.

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
    rewrite Hsj in H.
    exfalso; apply neq_negb in H; apply H; reflexivity.

    eapply le_trans; eauto; apply Nat.le_add_r.

   apply le_n_S.
   eapply le_trans; eauto; apply Nat.le_add_r.

  rewrite H1; reflexivity.

  apply Hnj in H1.
  rewrite Nat.add_sub_assoc in H1; [ idtac | assumption ].
  rewrite Nat.add_comm, Nat.add_sub in H1.
  rewrite Hsi in H1.
  exfalso; apply neq_negb in H1; apply H1; reflexivity.

 apply fst_same_iff in Hj; simpl in Hj.
 pose proof (Hj (i + di - j)) as H.
 rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
 rewrite Nat.add_comm, Nat.add_sub in H.
 rewrite Hsi in H.
 exfalso; apply neq_negb in H; apply H; reflexivity.
Qed.

Theorem carry_before_relay : ∀ x y i di,
  fst_same x y i = Some di
  → ∀ dj, dj ≤ di → carry x y (i + dj) = x.[i + di].
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
  → ∀ dj, dj < di → carry x y (S (i + dj)) = x.[i + di].
Proof.
intros x y i di Hs dj Hdj.
rewrite <- Nat.add_succ_r.
apply carry_before_relay; assumption.
Qed.

Theorem carry_before_inf_relay : ∀ x y i,
  fst_same x y i = None
  → ∀ dj, carry x y (i + dj) = true.
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
exfalso; revert Hs1; apply no_fixpoint_negb.
Qed.

(* old version that should be removed one day *)
Theorem carry_before_inf_relay9 : ∀ x y i,
  fst_same x y i = None
  → ∀ dj, carry x y (S (i + dj)) = true.
Proof.
intros x y i Hs dj.
rewrite <- Nat.add_succ_r.
apply carry_before_inf_relay; assumption.
Qed.

Theorem carry_sum_3_noI_assoc_l : ∀ z0 x y z i,
  z = (z0 + 0)%I
  → carry ((x + y) + z)%I 0 i = false.
Proof.
intros z0 x y z i Hc0.
unfold carry; simpl.
remember (fst_same ((x + y) + z)%I 0 i) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); assumption.

 apply I_add_inf_if in Hs1.
 destruct Hs1 as (j, (Hij, (Haj, Hbj))).
 rewrite Hc0 in Hbj; simpl in Hbj.
 apply forall_add_succ_r in Hbj.
 apply I_add_inf_if in Hbj.
 destruct Hbj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem carry_sum_3_noI_assoc_r : ∀ x0 x y z i,
  x = (x0 + 0)%I
  → carry (x + (y + z))%I 0 i = false.
Proof.
intros x0 x y z i Ha0.
unfold carry; simpl.
remember (fst_same (x + (y + z)%I) 0 i) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); assumption.

 apply I_add_inf_if in Hs1.
 destruct Hs1 as (j, (Hij, (Haj, Hbj))).
 rewrite Ha0 in Haj; simpl in Haj.
 apply forall_add_succ_r in Haj.
 apply I_add_inf_if in Haj.
 destruct Haj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem sum_x1_x_sum_0_0 : ∀ x y i,
  y.[i] = true
  → I_add_i x y i = x.[i]
  → x.[S i] = false
  → I_add_i x y (S i) = false.
Proof.
intros y z i Ht5 Hbd Ht6.
remember (y.[i]) as b eqn:Hb5; symmetry in Hb5.
apply not_true_iff_false; intros H.
unfold I_add_i in H; simpl in H.
rewrite Ht6, xorb_false_l in H.
rename H into Hcc.
remember Hbd as H; clear HeqH.
unfold I_add_i in H; simpl in H.
rewrite Hb5, Ht5, xorb_true_r in H.
apply xorb_move_l_r_1 in H.
rewrite negb_xorb_diag_l in H.
rename H into Hyz.
remember (S i) as x.
rewrite <- Nat.add_1_r in Hcc.
unfold carry in Hyz.
remember (fst_same y z x) as s1 eqn:Hs1 .
destruct s1 as [di1| ].
 symmetry in Hs1.
 destruct di1.
  rewrite Nat.add_0_r, Ht6 in Hyz; discriminate Hyz.

  assert (0 < S di1) as H by apply Nat.lt_0_succ.
  erewrite carry_before_relay in Hcc; try eassumption.
  rewrite Hyz, xorb_true_r in Hcc.
  apply negb_true_iff in Hcc.
  apply fst_same_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, _).
  apply Hn1 in H; rewrite Nat.add_0_r in H.
  rewrite Ht6, Hcc in H; discriminate H.

 symmetry in Hs1.
 rewrite carry_before_inf_relay in Hcc; [ idtac | assumption ].
 remember Hs1 as H; clear HeqH.
 apply fst_same_inf_after with (di := 1) in H.
 rewrite Nat.add_1_r in H.
 rename H into Hs2.
 apply fst_same_iff in Hs1.
 pose proof (Hs1 0) as H; apply negb_sym in H.
 rewrite Nat.add_0_r in H.
 rewrite H, Ht6, xorb_true_l in Hcc.
 discriminate Hcc.
Qed.

Theorem carry_succ_negb : ∀ x y i a,
  carry x y i = a
  → carry x y (S i) = negb a
  → x.[i] = a ∧ y.[i] = a.
Proof.
intros x y i a Hc1 Hc2.
unfold carry in Hc1; simpl in Hc1.
remember (fst_same x y i) as s1 eqn:Hs1 .
symmetry in Hs1.
replace (S i) with (S i + 0) in Hc2 by apply Nat.add_0_r.
destruct s1 as [di1| ].
 destruct di1.
  apply fst_same_iff in Hs1.
  destruct Hs1 as (_, Hs1).
  rewrite Nat.add_0_r in Hc1, Hs1.
  rewrite Hc1 in Hs1; symmetry in Hs1.
  split; assumption.

  assert (0 < S di1) as H by apply Nat.lt_0_succ.
  eapply carry_before_relay9 in H; try eassumption.
  rewrite <- Nat.add_succ_l in H.
  rewrite Hc2 in H; simpl in H.
  rewrite Hc1 in H.
  exfalso; revert H; apply no_fixpoint_negb.

 subst a; simpl in Hc2.
 rewrite Nat.add_0_r in Hc2.
 unfold carry in Hc2.
 apply fst_same_inf_after with (di := 1) in Hs1.
 rewrite <- Nat.add_1_r, Hs1 in Hc2.
 discriminate Hc2.
Qed.

Theorem sum_11_1_sum_x1 : ∀ x y i di,
  x .[ i] = true
  → y .[ i] = true
  → (∀ dj, dj ≤ di → I_add_i x y (i + dj) = x.[i + dj])
  → y.[i + di] = true.
Proof.
intros x y i di Ha Hy Hxy.
revert i Ha Hy Hxy.
induction di; intros; [ rewrite Nat.add_0_r; assumption | idtac ].
pose proof (Hxy (S di) (Nat.le_refl (S di))) as H.
unfold I_add_i in H; simpl in H.
rewrite xorb_assoc in H.
apply xorb_move_l_r_1 in H.
rewrite xorb_nilpotent in H.
remember (y .[ i + S di]) as b eqn:Hb .
destruct b; [ reflexivity | symmetry in Hb ].
rewrite xorb_false_l in H.
rename H into Hd.
pose proof (Hxy di (Nat.le_succ_diag_r di)) as H.
unfold I_add_i in H; simpl in H.
rewrite xorb_assoc in H.
apply xorb_move_l_r_1 in H.
rewrite xorb_nilpotent in H.
rewrite IHdi in H; try assumption.
 rewrite xorb_true_l in H.
 apply negb_false_iff in H.
 rewrite Nat.add_succ_r in Hd.
 apply carry_succ_negb in H; [ idtac | assumption ].
 rewrite <- Nat.add_succ_r, Hb in H.
 destruct H as (_, H); discriminate H.

 intros dj Hdj.
 apply Hxy, Nat.le_le_succ_r; assumption.
Qed.

Theorem case_1 : ∀ x y z i,
  carry x (y + z) i = true
  → carry y z i = true
  → carry x y i = false
  → False.
Proof.
intros x y z i Hc3 Hc5 Hc6.
remember Hc6 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x y i) as s6 eqn:Hs6 .
destruct s6 as [di6| ]; [ idtac | discriminate H ].
remember Hs6 as HH; clear HeqHH.
apply fst_same_sym_iff in HH; simpl in HH.
destruct HH as (Hn6, Ht6).
rewrite H in Ht6; symmetry in Ht6.
rename H into Ha6.
remember Hc5 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same y z i) as s5 eqn:Hs5 .
remember Hs5 as HH; clear HeqHH.
apply fst_same_sym_iff in HH; simpl in HH.
destruct s5 as [di5| ]; [ idtac | clear H ].
 destruct HH as (Hn5, Ht5); rewrite H in Ht5.
 symmetry in Ht5; rename H into Hb5.
 destruct (lt_eq_lt_dec di5 di6) as [[H1| H1]| H1].
  remember Hc3 as H; clear HeqH.
  unfold carry in H; simpl in H.
  remember (fst_same x (y + z) i) as s3 eqn:Hs3 .
  apply fst_same_sym_iff in Hs3; simpl in Hs3.
  destruct s3 as [di3| ]; [ idtac | clear H ].
   destruct Hs3 as (Hn3, Ht3).
   rewrite H in Ht3; symmetry in Ht3.
   rename H into Ha3.
   destruct (lt_eq_lt_dec di3 di5) as [[H2| H2]| H2].
    remember Ht3 as H; clear HeqH.
    unfold I_add_i in H; simpl in H.
    symmetry in Hs5.
    erewrite carry_before_relay9 in H; try eassumption; simpl in H.
    apply Hn5 in H2.
    rewrite H2, negb_xorb_diag_l, Hb5 in H; discriminate H.

    subst di3.
    remember H1 as H; clear HeqH.
    apply Hn6 in H.
    rewrite Ha3, Hb5 in H.
    discriminate H.

    remember H2 as H; clear HeqH.
    apply Hn3 in H.
    rewrite Hn6 in H; [ idtac | assumption ].
    rewrite Hb5 in H.
    apply negb_sym in H; simpl in H.
    rename H into Hbd.
    destruct (lt_eq_lt_dec di3 di6) as [[H4| H4]| H4].
     remember Ha3 as Hb3; clear HeqHb3.
     rewrite Hn6 in Hb3; [ idtac | assumption ].
     apply negb_true_iff in Hb3.
     remember (di3 - S di5) as n eqn:Hn .
     apply nat_sub_add_r in Hn; [ idtac | assumption ].
     rewrite Nat.add_comm in Hn; simpl in Hn.
     subst di3.
     rewrite Nat.add_succ_r in Hb3, Ht3.
     remember H4 as H; clear HeqH; simpl in H.
     apply Nat.lt_succ_l in H; apply Hn6 in H.
     assert (n + di5 < S n + di5) as HH by apply Nat.lt_succ_diag_r.
     rewrite Hn3 in H; [ idtac | assumption ].
     apply negb_sym in H.
     rewrite negb_involutive in H; symmetry in H; simpl in H.
     rename H into Hyz1.
     erewrite sum_x1_x_sum_0_0 in Ht3; try eassumption.
      discriminate Ht3.

      rewrite Nat.add_assoc, Nat.add_shuffle0.
      apply sum_11_1_sum_x1 with (x := y); try assumption.
      intros dj Hdj.
      simpl; rewrite <- Nat.add_assoc, <- negb_involutive.
      rewrite <- Hn6.
       rewrite Hn3; [ rewrite negb_involutive; reflexivity | idtac ].
       rewrite Nat.add_comm; simpl.
       apply le_n_S, Nat.add_le_mono_r; assumption.

       eapply lt_trans; [ idtac | eassumption ].
       rewrite Nat.add_comm.
       apply le_n_S, Nat.add_le_mono_r; assumption.

     subst di3.
     rewrite Ha6 in Ha3; discriminate Ha3.

     remember Ha6 as Hbe; clear HeqHbe.
     rewrite Hn3 in Hbe; [ idtac | assumption ].
     apply negb_false_iff in Hbe.
     remember (di6 - S di5) as n eqn:Hn .
     apply nat_sub_add_r in Hn; [ idtac | assumption ].
     rewrite Nat.add_comm in Hn; simpl in Hn; subst di6.
     rewrite Nat.add_succ_r in Hbe, Ht6.
     remember H1 as H; clear HeqH.
     apply Hn6 in H.
     rewrite Hb5 in H; simpl in H.
     rename H into Ha5.
     erewrite sum_x1_x_sum_0_0 in Hbe; try eassumption.
      discriminate Hbe.

      rewrite Nat.add_assoc, Nat.add_shuffle0.
      apply sum_11_1_sum_x1 with (x := y); try assumption.
      intros dj Hdj.
      simpl; rewrite <- Nat.add_assoc, <- negb_involutive.
      rewrite <- Hn6.
       rewrite Hn3; [ rewrite negb_involutive; reflexivity | idtac ].
       eapply lt_trans; [ idtac | eassumption ].
       rewrite Nat.add_comm.
       apply le_n_S, Nat.add_le_mono_r; assumption.

       rewrite Nat.add_comm.
       apply le_n_S, Nat.add_le_mono_r; assumption.

      remember H4 as H; clear HeqH.
      eapply lt_trans in H; [ idtac | apply Nat.lt_succ_diag_r ].
      apply Hn3 in H.
      rewrite Hn6 in H; [ idtac | apply Nat.lt_succ_diag_r ].
      apply negb_sym in H.
      rewrite negb_involutive in H.
      assumption.

   remember Ha6 as Hbe; clear HeqHbe.
   rewrite Hs3 in Hbe.
   apply negb_false_iff in Hbe.
   remember (di6 - S di5) as n eqn:Hn .
   apply nat_sub_add_r in Hn; [ idtac | assumption ].
   rewrite Nat.add_comm in Hn; simpl in Hn; subst di6.
   rewrite Nat.add_succ_r in Hbe, Ht6.
   remember H1 as H; clear HeqH.
   apply Hn6 in H.
   rewrite Hb5 in H; simpl in H.
   rename H into Ha5.
   rewrite sum_x1_x_sum_0_0 in Hbe; try assumption.
    discriminate Hbe.

    rewrite Nat.add_assoc, Nat.add_shuffle0.
    apply sum_11_1_sum_x1 with (x := y); try assumption.
    intros dj Hdj.
    simpl; rewrite <- Nat.add_assoc, <- negb_involutive.
    rewrite <- Hn6.
     rewrite Hs3; rewrite negb_involutive; reflexivity.

     rewrite Nat.add_comm.
     apply le_n_S, Nat.add_le_mono_r; assumption.

    rewrite <- negb_involutive.
    rewrite <- Hn6; [ idtac | apply Nat.lt_succ_diag_r ].
    apply negb_sym, Hs3.

  subst di5; rewrite Ht6 in Hb5; discriminate Hb5.

  remember Hc3 as H; clear HeqH.
  unfold carry in H; simpl in H.
  remember (fst_same x (y + z) i) as s3 eqn:Hs3 .
  destruct s3 as [di3| ]; [ idtac | clear H ].
   rename H into Ha3.
   remember Hs3 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn3, Ht3).
   destruct (lt_eq_lt_dec di3 di6) as [[H2| H2]| H2].
    remember H2 as H; clear HeqH.
    apply Hn6 in H.
    rewrite Ha3 in H; apply negb_sym in H.
    rename H into Hb3; simpl in Hb3.
    remember H1 as H; clear HeqH.
    eapply lt_trans in H; [ idtac | eassumption ].
    apply Hn5 in H.
    rewrite Hb3 in H; apply negb_sym in H.
    rename H into Hd3; simpl in Hd3.
    remember Ht3 as H; clear HeqH.
    unfold I_add_i in H; simpl in H.
    rewrite Ha3, Hb3, Hd3, xorb_true_r, xorb_true_l in H.
    apply negb_sym in H; simpl in H.
    symmetry in Hs5.
    remember H1 as HH; clear HeqHH.
    eapply lt_trans in HH; [ idtac | eassumption ].
    erewrite carry_before_relay9 in H; try eassumption.
    simpl in H; rewrite Hb5 in H; discriminate H.

    subst di3; rewrite Ha6 in Ha3; discriminate Ha3.

    remember H2 as H; clear HeqH.
    apply Hn3 in H.
    rewrite Ha6 in H; apply negb_sym in H; simpl in H.
    unfold I_add_i in H; simpl in H.
    rewrite Ht6, xorb_false_l in H.
    symmetry in Hs5.
    erewrite carry_before_relay9 in H; try eassumption; simpl in H.
    rewrite Hb5, xorb_true_r in H.
    rewrite <- Hn5 in H; [ idtac | assumption ].
    rewrite Ht6 in H; discriminate H.

   remember Hs3 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rename H into Ht3.
   pose proof (Ht3 di6) as H.
   rewrite Ha6 in H; apply negb_sym in H; simpl in H.
   unfold I_add_i in H; simpl in H.
   rewrite Ht6, xorb_false_l in H.
   symmetry in Hs5.
   erewrite carry_before_relay9 in H; try eassumption; simpl in H.
   rewrite Hb5, xorb_true_r in H.
   rewrite <- Hn5 in H; [ idtac | assumption ].
   rewrite Ht6 in H; discriminate H.

 rename HH into Ht5.
 remember Hc3 as H; clear HeqH.
 unfold carry in H; simpl in H.
 remember (fst_same x (y + z) i) as s3 eqn:Hs3 .
 destruct s3 as [di3| ]; [ idtac | clear H ].
  rename H into Ha3.
  remember Hs3 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn3, Ht3).
  rewrite Ha3 in Ht3; symmetry in Ht3.
  unfold I_add_i in Ht3; simpl in Ht3.
  rewrite Ht5, negb_xorb_diag_l, xorb_true_l in Ht3.
  apply negb_true_iff in Ht3.
  rewrite <- Nat.add_succ_l in Ht3.
  symmetry in Ht5.
  unfold carry in Ht3; simpl in Ht3.
  remember Hs5 as H; clear HeqH; symmetry in H.
  apply fst_same_inf_after with (di := S di3) in H.
  rewrite Nat.add_succ_r in H; simpl in H.
  rewrite H in Ht3; discriminate Ht3.

  remember Hs3 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  rename H into Ht3.
  rewrite Ht3 in Ha6.
  apply negb_false_iff in Ha6.
  unfold I_add_i in Ha6.
  rewrite Ht6, xorb_false_l in Ha6.
  unfold carry in Ha6.
  remember Hs5 as H; clear HeqH; symmetry in H.
  apply fst_same_inf_after with (di := S di6) in H.
  rewrite Nat.add_succ_r in H; simpl in H.
  rewrite H, xorb_true_r in Ha6.
  rewrite <- Ht5, Ht6 in Ha6; discriminate Ha6.
Qed.

Theorem min_neq_lt : ∀ x xl y m,
  m = List.fold_right min x xl
  → y ∈ [x … xl]
  → y ≠ m
  → m < y.
Proof.
intros x xl y m Hm Hy Hym.
subst m.
apply Nat.nle_gt; intros Hm; apply Hym; clear Hym.
revert x y Hy Hm.
induction xl as [| z]; intros.
 simpl in Hy, Hm; simpl.
 destruct Hy; auto; contradiction.

 simpl in Hy, Hm; simpl.
 destruct Hy as [Hy| [Hy| Hy]].
  subst y.
  apply Nat.min_glb_iff in Hm.
  clear IHxl.
  revert z x Hm.
  induction xl as [| y]; intros.
   simpl in Hm; simpl.
   apply Nat.min_unicity.
   right; split; [ idtac | reflexivity ].
   destruct Hm; assumption.

   simpl in Hm; simpl.
   rewrite <- IHxl.
    apply Nat.min_unicity.
    right; split; [ idtac | reflexivity ].
    destruct Hm; assumption.

    destruct Hm as (Hxz, Hm).
    apply Nat.min_glb_iff; assumption.

  subst z.
  symmetry; apply min_l.
  eapply Nat.min_glb_r; eassumption.

  erewrite <- IHxl; [ idtac | right; eassumption | idtac ].
   apply Nat.min_unicity.
   right; split; [ idtac | reflexivity ].
   eapply Nat.min_glb_l; eassumption.

   erewrite <- IHxl; [ reflexivity | right; eassumption | idtac ].
   eapply Nat.min_glb_r; eassumption.
Qed.

Theorem carry_repeat : ∀ x y z i,
  carry x y i = false
  → carry (x + y) z i = false
  → carry y z i = true
  → ∃ m,
    carry x y (S (i + m)) = false ∧
    carry (x + y) z (S (i + m)) = false ∧
    carry y z (S (i + m)) = true ∧
    (∀ dj, dj ≤ m → I_add_i x y (i + dj) = negb (z.[i + dj])).
Proof.
intros x y z i Rxy Rayz Ryz.
rename Rxy into Rxyn.
rename Rayz into Rxy_zn.
rename Ryz into Ryzn.
remember Rxyn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x y i) as sxyn eqn:Hsxyn .
destruct sxyn as [dxyn| ]; [ idtac | discriminate H ].
rename H into A_p.
symmetry in Hsxyn.
remember Rxy_zn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (x + y) z i) as sxy_zn.
rename Heqsxy_zn into Hsxy_zn.
destruct sxy_zn as [dxy_zn| ]; [ idtac | discriminate H ].
rename H into AB_p; symmetry in Hsxy_zn.
remember Ryzn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same y z i) as syzn eqn:Hsyzn .
symmetry in Hsyzn.
destruct syzn as [dyzn| ]; [ idtac | clear H ].
 rename H into B_p.
 remember (List.fold_right min dyzn [dxyn; dxy_zn … []]) as p.
 rename Heqp into Hp.
 destruct (eq_nat_dec dxyn p) as [H| H].
  move H at top; subst dxyn; rename A_p into Ap.
  remember Hsxyn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnxyn, Bp).
  rewrite Ap in Bp; symmetry in Bp.
  remember Hsyzn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnyzn, Htyzn).
  destruct (eq_nat_dec dyzn p) as [H| H].
   move H at top; subst dyzn.
   rewrite B_p in Bp; discriminate Bp.

   eapply min_neq_lt in H; eauto ; try (left; auto).
   rename H into Hpdyzn.
   remember Bp as Cp; clear HeqCp.
   rewrite Hnyzn in Cp; [ idtac | assumption ].
   apply negb_false_iff in Cp.
   remember Hsxy_zn as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hnxy_zn, Htxy_zn).
   destruct (eq_nat_dec dxy_zn p) as [H| H].
    move H at top; subst dxy_zn.
    rewrite Cp in Htxy_zn.
    rewrite AB_p in Htxy_zn; discriminate Htxy_zn.

    eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
    rename H into Hpdxy_zn.
    pose proof (Hnxy_zn p Hpdxy_zn) as H.
    rewrite Cp in H; simpl in H; rename H into ABp.
    remember ABp as H; clear HeqH.
    unfold I_add_i in H.
    rewrite Ap, Bp, xorb_false_l in H.
    rename H into Rxyp.
    remember Hsxy_zn as H; clear HeqH.
    eapply carry_before_relay9 in H; [ idtac | eassumption ].
    simpl in H.
    rewrite AB_p in H.
    rename H into Rxy_zp.
    remember Hsyzn as H; clear HeqH.
    eapply carry_before_relay9 in H; [ idtac | eassumption ].
    simpl in H.
    rewrite B_p in H.
    rename H into Ryzp.
    exists p.
    split; [ assumption | idtac ].
    split; [ assumption | idtac ].
    split; [ assumption | idtac ].
    intros dj Hdj.
    eapply Hnxy_zn, le_lt_trans; eassumption.

  exfalso.
  eapply min_neq_lt in H; eauto ; try (right; left; auto).
  rename H into Hpdan.
  remember Hsxyn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnxyn, Htxyn).
  remember Hsxy_zn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnxy_zn, Htxy_zn).
  remember Hsyzn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnyzn, Htyzn).
  rename Htyzn into C_p; rewrite B_p in C_p; symmetry in C_p.
  rename Htxy_zn into C_q; rewrite AB_p in C_q; symmetry in C_q.
  destruct (eq_nat_dec dyzn p) as [H| H].
   move H at top; subst dyzn.
   rename B_p into Bp; rename C_p into Cp.
   destruct (eq_nat_dec dxy_zn p) as [H| H].
    move H at top; subst dxy_zn.
    rewrite Cp in C_q; discriminate C_q.

    eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
    rename H into Hpdxy_zn.
    pose proof (Hnxy_zn p Hpdxy_zn) as H.
    rewrite Cp in H; rename H into ABp; simpl in ABp.
    remember ABp as H; clear HeqH.
    unfold I_add_i in H.
    rewrite Hnxyn in H; [ idtac | assumption ].
    rewrite negb_xorb_diag_l, xorb_true_l in H.
    erewrite carry_before_relay9 in H; try eassumption.
    simpl in H; rewrite A_p in H; discriminate H.

   eapply min_neq_lt in H; eauto ; try (left; auto).
   rename H into Hpdyzn.
   destruct (eq_nat_dec dxy_zn p) as [H| H].
    move H at top; subst dxy_zn.
    remember AB_p as H; clear HeqH.
    unfold I_add_i in H; simpl in H.
    rewrite Hnxyn in H; [ idtac | assumption ].
    rewrite negb_xorb_diag_l, xorb_true_l in H.
    apply negb_false_iff in H.
    erewrite carry_before_relay9 in H; try eassumption.
    simpl in H; rewrite A_p in H; discriminate H.

    eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
    rename H into Hpdxy_zn; simpl in Hp.
    revert Hp Hpdan Hpdyzn Hpdxy_zn; clear; intros Hp H1 H2 H3.
    destruct (Nat.min_dec dxy_zn dyzn) as [L1| L1].
     rewrite L1 in Hp.
     destruct (Nat.min_dec dxyn dxy_zn) as [L2| L2].
      rewrite L2 in Hp; subst p.
      revert H1; apply Nat.lt_irrefl.

      rewrite L2 in Hp; subst p.
      revert H3; apply Nat.lt_irrefl.

     rewrite L1 in Hp.
     destruct (Nat.min_dec dxyn dyzn) as [L2| L2].
      rewrite L2 in Hp; subst p.
      revert H1; apply Nat.lt_irrefl.

      rewrite L2 in Hp; subst p.
      revert H2; apply Nat.lt_irrefl.

 remember (List.fold_right min dxyn [dxy_zn]) as p eqn:Hp .
 destruct (eq_nat_dec dxyn p) as [H| H].
  move H at top; subst dxyn; rename A_p into Ap.
  remember Hsxyn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnxyn, Bp).
  rewrite Ap in Bp; symmetry in Bp.
  remember Hsyzn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  rename H into Hnyzn.
  remember Bp as Cp; clear HeqCp.
  rewrite Hnyzn in Cp.
  apply negb_false_iff in Cp.
  remember Hsxy_zn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnxy_zn, Htxy_zn).
  destruct (eq_nat_dec dxy_zn p) as [H| H].
   move H at top; subst dxy_zn.
   rewrite Cp in Htxy_zn.
   rewrite AB_p in Htxy_zn; discriminate Htxy_zn.

   eapply min_neq_lt in H; eauto ; try (right; left; auto).
   rename H into Hpdxy_zn.
   pose proof (Hnxy_zn p Hpdxy_zn) as H.
   rewrite Cp in H; simpl in H.
   unfold I_add_i in H.
   rewrite Ap, Bp, xorb_false_l in H.
   exists p.
   split; [ assumption | idtac ].
   erewrite carry_before_relay9; try eassumption; simpl.
   split; [ assumption | idtac ].
   erewrite carry_before_inf_relay9; [ idtac | assumption ].
   split; [ reflexivity | idtac ].
   intros dj Hdj; eapply Hnxy_zn, le_lt_trans; eassumption.

  eapply min_neq_lt in H; eauto ; try (left; auto).
  rename H into Hpdxyn.
  destruct (eq_nat_dec dxy_zn p) as [H| H].
   move H at top; subst dxy_zn.
   remember Hsxyn as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hnxyn, B_p).
   rewrite A_p in B_p; symmetry in B_p.
   remember AB_p as H; clear HeqH.
   unfold I_add_i in H.
   rewrite Hnxyn in H; [ idtac | assumption ].
   rewrite negb_xorb_diag_l, xorb_true_l in H.
   erewrite carry_before_relay9 in H; try eassumption.
   simpl in H; rewrite A_p in H; discriminate H.

   eapply min_neq_lt in H; eauto ; try (right; left; auto).
   simpl in Hp.
   destruct (Nat.min_dec dxy_zn dxyn) as [L1| L1].
    rewrite L1 in Hp; subst p.
    exfalso; revert H; apply Nat.lt_irrefl.

    rewrite L1 in Hp; subst p.
    exfalso; revert Hpdxyn; apply Nat.lt_irrefl.
Qed.

Definition I_shift_l n x := {| rm i := x.[i+n] |}.
Arguments I_shift_l n%nat x%I.

Theorem fst_same_shift : ∀ x y x' y' i di d,
  fst_same x y i = Some di
  → d ≤ di
  → x' = I_shift_l d x
  → y' = I_shift_l d y
  → fst_same x' y' i = Some (di - d).
Proof.
intros x y x' y' i di d Hs Hd Ha' Hb'.
subst x' y'; simpl.
apply fst_same_iff in Hs; simpl in Hs.
destruct Hs as (Hn, Hs).
apply fst_same_iff; simpl.
split.
 intros dj Hdj.
 rewrite <- Nat.add_assoc; apply Hn.
 eapply Nat.add_lt_le_mono with (p := d) in Hdj; [ idtac | reflexivity ].
 rewrite Nat.sub_add in Hdj; assumption.

 rewrite Nat.add_sub_assoc; [ idtac | assumption ].
 rewrite Nat.sub_add; [ assumption | idtac ].
 eapply le_trans; [ eassumption | idtac ].
 apply Nat.le_sub_le_add_r.
 rewrite Nat.sub_diag.
 apply Nat.le_0_l.
Qed.

Theorem carry_shift : ∀ x y n i,
  carry (I_shift_l n x) (I_shift_l n y) i = carry x y (i + n).
Proof.
intros x y n i.
unfold carry; simpl.
remember (fst_same x y (i + n)) as s1 eqn:Hs1 .
remember (fst_same (I_shift_l n x) (I_shift_l n y) i) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 destruct s2 as [di2| ].
  destruct Hs2 as (Hn2, Hs2).
  destruct (lt_eq_lt_dec di1 di2) as [[H1| H1]| H1].
   apply Hn2 in H1.
   rewrite Nat.add_shuffle0, Hs1 in H1.
   exfalso; symmetry in H1; revert H1; apply no_fixpoint_negb.

   subst di2; rewrite Nat.add_shuffle0; reflexivity.

   apply Hn1 in H1.
   rewrite Nat.add_shuffle0, Hs2 in H1.
   exfalso; symmetry in H1; revert H1; apply no_fixpoint_negb.

  rewrite Nat.add_shuffle0, Hs2 in Hs1.
  exfalso; revert Hs1; apply no_fixpoint_negb.

 destruct s2 as [di2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Hs2).
 rewrite Nat.add_shuffle0, Hs1 in Hs2.
 exfalso; revert Hs2; apply no_fixpoint_negb.
Qed.

Theorem I_add_i_shift : ∀ x y i n,
  I_add_i (I_shift_l n x) (I_shift_l n y) i = I_add_i x y (i + n).
Proof.
intros x y i n.
unfold I_add_i; simpl.
rewrite carry_shift; reflexivity.
Qed.

Theorem fst_same_shift_add_l : ∀ x y z n i,
  fst_same (I_shift_l n (x + y)) z i =
  fst_same (I_shift_l n x + I_shift_l n y) z i.
Proof.
intros x y z n i.
apply fst_same_iff; simpl.
remember (fst_same (I_shift_l n x + I_shift_l n y) z i) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Hs).
 split.
  intros dj Hdj.
  apply Hn in Hdj.
  rewrite I_add_i_shift in Hdj; assumption.

  rewrite I_add_i_shift in Hs; assumption.

 intros dj; rewrite <- I_add_i_shift; apply Hs.
Qed.

Theorem carry_shift_add_l : ∀ x y z n i,
  carry (I_shift_l n x + I_shift_l n y) (I_shift_l n z) i =
  carry (x + y) z (i + n).
Proof.
intros x y z n i.
rewrite <- carry_shift.
unfold carry; simpl.
rewrite <- fst_same_shift_add_l.
remember (I_shift_l n (x + y)) as xy'.
remember (I_shift_l n z) as z'.
remember (fst_same xy' z' i) as s eqn:Hs .
subst xy' z'.
destruct s as [di| ]; [ idtac | reflexivity ].
apply I_add_i_shift.
Qed.

Theorem case_2 : ∀ x y z i,
  carry (x + y) z i = false
  → carry y z i = true
  → carry x y i = false
  → False.
Proof.
intros x y z i Hc4 Hc5 Hc6.
remember Hc4 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (x + y) z i) as s eqn:Hs .
destruct s as [di| ]; [ idtac | discriminate H ].
symmetry in Hs; clear H.
revert x y z i Hc4 Hc5 Hc6 Hs.
induction di as (di, IHdi) using all_lt_all; intros.
remember Hc4 as H; clear HeqH.
apply carry_repeat in H; try assumption.
destruct H as (n, (Rxyn, (Rxy_zn, (Ryzn, Hnxy_z)))).
move Rxyn after Ryzn.
destruct (le_dec di n) as [H1| H1].
 remember Hs as H; clear HeqH.
 apply fst_same_iff in H; simpl in H.
 destruct H as (Hnxy_z2, Hxy_z).
 rewrite Hnxy_z in Hxy_z; [ idtac | assumption ].
 revert Hxy_z; apply no_fixpoint_negb.

 apply Nat.nle_gt in H1.
 remember (di - S n) as dj.
 apply nat_sub_add_r in Heqdj; [ idtac | assumption ].
 clear Hc4 Hc5 Hc6.
 rename Rxy_zn into Hc4; rename Ryzn into Hc5; rename Rxyn into Hc6.
 remember (I_shift_l (S n) (x + y)%I) as x'y' eqn:Hxy .
 remember (I_shift_l (S n) z) as z' eqn:Hc .
 eapply fst_same_shift in Hs; try eassumption.
 assert (0 < S n) as Hn by apply Nat.lt_0_succ.
 assert (di - S n < di) as H by (apply Nat.sub_lt; assumption).
 subst x'y'.
 rewrite fst_same_shift_add_l in Hs.
 remember (I_shift_l (S n) x) as x' eqn:Ha .
 remember (I_shift_l (S n) y) as y' eqn:Hb .
 eapply IHdi with (x := x') (y := y') (z := z'); try eassumption.
  subst x' y' z'.
  rewrite carry_shift_add_l, Nat.add_succ_r; assumption.

  subst y' z'.
  rewrite carry_shift.
  rewrite Nat.add_succ_r; assumption.

  subst x' y'.
  rewrite carry_shift.
  rewrite Nat.add_succ_r; assumption.
Qed.

Theorem carry_repeat2 : ∀ x y z i u,
  carry x (y + z) i = true
  → carry (x + y) z i = false
  → carry y z i = u
  → carry x y i = u
  → ∃ m t,
    carry x (y + z) (S (i + m)) = true ∧
    carry (x + y) z (S (i + m)) = false ∧
    carry y z (S (i + m)) = t ∧
    carry x y (S (i + m)) = t ∧
    (∀ dj, dj ≤ m → I_add_i x y (i + dj) = negb (z.[ i + dj])).
Proof.
intros x y z i u Hc3 Hc4 Hc5 Hc6.
remember Hc4 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (x + y) z i) as s4 eqn:Hs4 .
symmetry in Hs4; rename H into H4.
destruct s4 as [di4| ]; [ idtac | discriminate H4 ].
remember Hc3 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x (y + z) i) as s3 eqn:Hs3 .
symmetry in Hs3; rename H into H3.
remember Hc5 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same y z i) as s5 eqn:Hs5 .
symmetry in Hs5; rename H into H5.
remember Hc6 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x y i) as s6 eqn:Hs6 .
symmetry in Hs6; rename H into H6.
destruct s3 as [di3| ]; [ idtac | clear H3 ].
 destruct s5 as [di5| ].
  destruct s6 as [di6| ].
   remember (List.fold_right min di6 [di3; di4; di5 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn3, Ht3).
   rewrite H3 in Ht3; symmetry in Ht3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn5, Ht5).
   rewrite H5 in Ht5; symmetry in Ht5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn6, Ht6).
   rewrite H6 in Ht6; symmetry in Ht6.
   destruct (eq_nat_dec di3 m) as [M3| M3].
    move M3 at top; subst di3.
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     rewrite H3 in H6; move H6 at top; subst u.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       rewrite Ht4 in Ht5; discriminate Ht5.

       eapply min_neq_lt in M5; [ idtac | eauto  | do 3 right; left; auto ].
       remember Ht3 as H; clear HeqH.
       unfold I_add_i in H.
       rewrite Ht6, Ht4, xorb_true_l in H.
       apply negb_true_iff in H.
       erewrite carry_before_relay9 in H; try eassumption.
       simpl in H; rewrite H5 in H; discriminate H.

      eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       clear Hm Ht6.
       remember Ht5 as H; clear HeqH.
       rewrite <- negb_involutive in H.
       apply negb_sym in H; simpl in H.
       rewrite <- Hn4 in H; [ idtac | assumption ].
       symmetry in H; rename H into Hxym.
       remember Hxym as H; clear HeqH.
       unfold I_add_i in H; simpl in H.
       rewrite H3, H5, xorb_nilpotent, xorb_false_l in H.
       rename H into Hcxym.
       remember Ht3 as H; clear HeqH.
       unfold I_add_i in H.
       rewrite H5, Ht5, xorb_nilpotent, xorb_false_l in H.
       rename H into Hcyzm.
       remember Hcxym as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same x y (S (i + m))) as sxym eqn:Hsxym .
       destruct sxym as [djxym| ]; [ idtac | discriminate H ].
       symmetry in Hsxym.
       rename H into Haxym.
       remember Hs4 as H; clear HeqH.
       eapply carry_before_relay9 in H; [ idtac | eassumption ].
       simpl in H; rewrite H4 in H.
       rename H into Hxycm.
       exfalso; eapply case_2; eassumption.

       eapply min_neq_lt in M5; [ idtac | eauto  | do 3 right; left; auto ].
       remember Ht3 as H; clear HeqH.
       unfold I_add_i in H.
       rewrite Hn5 in H; [ idtac | assumption ].
       rewrite negb_xorb_diag_l, xorb_true_l in H.
       apply negb_true_iff in H.
       eapply carry_before_relay9 in Hs5; [ idtac | eassumption ].
       simpl in Hs5; rewrite Hs5, H5 in H; discriminate H.

     eapply min_neq_lt in M6; [ idtac | eauto  | left; auto ].
     destruct (eq_nat_dec di5 m) as [M5| M5].
      move M5 at top; subst di5.
      remember H3 as H; clear HeqH.
      rewrite Hn6 in H; [ idtac | assumption ].
      apply negb_true_iff in H.
      rewrite H5 in H; move H at top; subst u.
      remember Ht3 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite H5, Ht5, xorb_false_l in H.
      rename H into Ryzm.
      destruct (eq_nat_dec di4 m) as [M4| M4].
       move M4 at top; subst di4.
       remember H4 as H; clear HeqH.
       unfold I_add_i in H.
       rewrite H3, H5, xorb_true_l in H.
       apply negb_false_iff in H.
       erewrite carry_before_relay9 in H; try eassumption.
       simpl in H; rewrite H6 in H; discriminate H.

       eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
       pose proof (Hn4 m M4) as H.
       rewrite Ht5 in H; simpl in H.
       rename H into ABm.
       remember ABm as H; clear HeqH.
       unfold I_add_i in H.
       rewrite H3, H5, xorb_true_l in H.
       apply negb_true_iff in H.
       rename H into Rxym.
       remember Hs4 as H; clear HeqH.
       eapply carry_before_relay9 in H; [ idtac | eassumption ].
       simpl in H; rewrite H4 in H.
       rename H into Rxy_zm.
       exfalso; eapply case_2; try eassumption.

      eapply min_neq_lt in M5; [ idtac | eauto  | do 3 right; left; auto ].
      remember H3 as H; clear HeqH.
      rewrite Hn6 in H; [ idtac | assumption ].
      apply negb_true_iff in H.
      rename H into Bm.
      remember Bm as H; clear HeqH.
      rewrite Hn5 in H; [ idtac | assumption ].
      apply negb_false_iff in H.
      rename H into Cm.
      remember Hs5 as H; clear HeqH.
      eapply carry_before_relay9 in H; [ idtac | eassumption ].
      simpl in H; rewrite H5 in H.
      rename H into Ryzm.
      remember Ht3 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Bm, Cm, Ryzm, xorb_false_l, xorb_true_l in H.
      apply negb_true_iff in H; move H at top; subst u.
      destruct (eq_nat_dec di4 m) as [M4| M4].
       move M4 at top; subst di4.
       rewrite Ht4 in Cm; discriminate Cm.

       eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
       pose proof (Hn4 m M4) as H.
       rewrite Cm in H; simpl in H.
       rename H into ABm.
       remember ABm as H; clear HeqH.
       unfold I_add_i in H.
       rewrite H3, Bm, xorb_false_r, xorb_true_l in H.
       apply negb_false_iff in H.
       erewrite carry_before_relay9 in H; try eassumption.
       simpl in H; rewrite H6 in H; discriminate H.

    eapply min_neq_lt in M3; [ idtac | eauto  | right; left; auto ].
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_relay9 in H; [ idtac | eassumption ].
      simpl in H; rewrite H3 in H.
      rename H into A_BCm.
      pose proof (Hn3 m M3) as H.
      rewrite H6 in H.
      apply negb_sym in H.
      unfold I_add_i in H.
      rewrite Ht6, Ht4, xorb_false_r in H.
      apply xorb_move_l_r_1 in H.
      rewrite negb_xorb_diag_r in H.
      rename H into BCm.
      exfalso; eapply case_1; eassumption.

      eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       exists m, (negb u).
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split.
        pose proof (Hn3 m M3) as H.
        unfold I_add_i in H.
        rewrite H6, Ht6, Ht5, xorb_nilpotent, xorb_false_l in H.
        apply negb_sym; assumption.

        split.
         pose proof (Hn4 m M4) as H.
         unfold I_add_i in H.
         rewrite H6, Ht6, Ht5, xorb_nilpotent, xorb_false_l in H.
         assumption.

         intros dj Hdj; apply Hn4.
         eapply le_lt_trans; eassumption.

       eapply min_neq_lt in M5; [ idtac | eauto  | do 3 right; left; auto ].
       exists m, u.
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split.
        pose proof (Hn3 m M3) as H.
        unfold I_add_i in H.
        rewrite Hn5 in H; [ idtac | assumption ].
        rewrite negb_xorb_diag_l in H.
        rewrite H6, negb_involutive in H.
        symmetry; assumption.

        split.
         pose proof (Hn4 m M4) as H.
         unfold I_add_i in H.
         rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
         rewrite <- Hn5 in H; [ idtac | assumption ].
         rewrite Ht6 in H; assumption.

         intros dj Hdj; apply Hn4.
         eapply le_lt_trans; eassumption.

     eapply min_neq_lt in M6; [ idtac | eauto  | left; auto ].
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Hn6 in H; [ idtac | assumption ].
      rewrite negb_xorb_diag_l, xorb_true_l in H.
      apply negb_false_iff in H.
      rename H into Rxym.
      remember Hs6 as H; clear HeqH.
      eapply carry_before_relay9 in H; [ idtac | eassumption ].
      simpl in H; rewrite Rxym, H6 in H.
      move H at top; subst u.
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       rewrite Ht4 in Ht5; discriminate Ht5.

       eapply min_neq_lt in M5; eauto ; try (do 3 right; left; auto).
       pose proof (Hn5 m M5) as H.
       rewrite Ht4 in H; simpl in H.
       rename H into Bm.
       pose proof (Hn6 m M6) as H.
       rewrite Bm in H; simpl in H.
       rename H into Am.
       pose proof (Hn3 m M3) as H.
       rewrite Am in H; apply negb_sym in H; simpl in H.
       rename H into BCm.
       remember BCm as H; clear HeqH.
       unfold I_add_i in H.
       rewrite Bm, Ht4, xorb_true_l in H.
       apply negb_true_iff in H.
       erewrite carry_before_relay9 in H; try eassumption.
       simpl in H; rewrite H5 in H; discriminate H.

      eapply min_neq_lt in M4; eauto ; try (do 2 right; left; auto).
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       exists m, u.
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split.
        pose proof (Hn3 m M3) as H.
        unfold I_add_i in H.
        rewrite Hn6 in H; [ idtac | assumption ].
        rewrite H5, Ht5, xorb_nilpotent, xorb_false_l in H.
        apply negb_sym in H.
        rewrite negb_involutive in H; assumption.

        split.
         pose proof (Hn4 m M4) as H.
         unfold I_add_i in H.
         rewrite Hn6 in H; [ idtac | assumption ].
         rewrite negb_xorb_diag_l, xorb_true_l, Ht5 in H.
         apply negb_sym in H; symmetry in H.
         rewrite negb_involutive in H; assumption.

         intros dj Hdj; apply Hn4.
         eapply le_lt_trans; eassumption.

       eapply min_neq_lt in M5; eauto ; try (do 3 right; left; auto).
       simpl in Hm.
       destruct (Nat.min_dec di5 di6) as [L1| L1]; rewrite L1 in Hm.
        destruct (Nat.min_dec di4 di5) as [L2| L2]; rewrite L2 in Hm.
         destruct (Nat.min_dec di3 di4) as [L3| L3]; rewrite L3 in Hm.
          subst m; exfalso; revert M3; apply Nat.lt_irrefl.

          subst m; exfalso; revert M4; apply Nat.lt_irrefl.

         destruct (Nat.min_dec di3 di5) as [L3| L3]; rewrite L3 in Hm.
          subst m; exfalso; revert M3; apply Nat.lt_irrefl.

          subst m; exfalso; revert M5; apply Nat.lt_irrefl.

        destruct (Nat.min_dec di4 di6) as [L2| L2]; rewrite L2 in Hm.
         destruct (Nat.min_dec di3 di4) as [L3| L3]; rewrite L3 in Hm.
          subst m; exfalso; revert M3; apply Nat.lt_irrefl.

          subst m; exfalso; revert M4; apply Nat.lt_irrefl.

         destruct (Nat.min_dec di3 di6) as [L3| L3]; rewrite L3 in Hm.
          subst m; exfalso; revert M3; apply Nat.lt_irrefl.

          subst m; exfalso; revert M6; apply Nat.lt_irrefl.

   move H6 at top; subst u.
   remember (List.fold_right min di5 [di3; di4 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn3, Ht3).
   rewrite H3 in Ht3; symmetry in Ht3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn5, Ht5).
   rewrite H5 in Ht5; symmetry in Ht5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn6.
   destruct (eq_nat_dec di3 m) as [M3| M3].
    move M3 at top; subst di3.
    destruct (eq_nat_dec di5 m) as [M5| M5].
     move M5 at top; subst di5.
     rewrite Hn6, H5 in H3.
     discriminate H3.

     eapply min_neq_lt in M5; eauto ; try (left; auto).
     remember Ht3 as H; clear HeqH.
     unfold I_add_i in H.
     rewrite Hn5 in H; [ idtac | assumption ].
     rewrite negb_xorb_diag_l, xorb_true_l in H.
     apply negb_true_iff in H.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H; rewrite H5 in H; discriminate H.

    eapply min_neq_lt in M3; eauto ; try (right; left; auto).
    destruct (eq_nat_dec di5 m) as [M5| M5].
     move M5 at top; subst di5.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      rewrite Ht5 in Ht4; discriminate Ht4.

      eapply min_neq_lt in M4; eauto ; try (do 2 right; left; auto).
      exists m, true.
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split.
       pose proof (Hn3 m M3) as H.
       unfold I_add_i in H.
       rewrite Hn6, H5, Ht5, xorb_false_l in H.
       apply negb_sym in H; rewrite negb_involutive in H.
       assumption.

       split.
        pose proof (Hn4 m M4) as H.
        unfold I_add_i in H.
        rewrite Hn6, negb_xorb_diag_l, xorb_true_l, Ht5 in H.
        apply negb_sym in H; symmetry in H.
        rewrite negb_involutive in H; assumption.

        intros dj Hdj; apply Hn4.
        eapply le_lt_trans; eassumption.

     eapply min_neq_lt in M5; eauto ; try (left; auto).
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      pose proof (Hn5 m M5) as H.
      rewrite Ht4 in H; simpl in H; rename H into Bm.
      pose proof (Hn6 m) as H.
      rewrite Bm in H; simpl in H; rename H into Am.
      pose proof (Hn3 m M3) as H.
      rewrite Am in H; apply negb_sym in H; simpl in H.
      rename H into BCm.
      remember BCm as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Bm, Ht4, xorb_true_l in H.
      apply negb_true_iff in H.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H; rewrite H5 in H; discriminate H.

      eapply min_neq_lt in M4; eauto ; try (do 2 right; left; auto).
      simpl in Hm.
      destruct (Nat.min_dec di4 di5) as [L1| L1]; rewrite L1 in Hm.
       destruct (Nat.min_dec di3 di4) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M3; apply Nat.lt_irrefl.

        subst m; exfalso; revert M4; apply Nat.lt_irrefl.

       destruct (Nat.min_dec di3 di5) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M3; apply Nat.lt_irrefl.

        subst m; exfalso; revert M5; apply Nat.lt_irrefl.

  move H5 at top; subst u.
  destruct s6 as [di6| ]; [ idtac | clear H6 ].
   remember (List.fold_right min di6 [di3; di4 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn3, Ht3).
   rewrite H3 in Ht3; symmetry in Ht3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn6, Ht6).
   rewrite H6 in Ht6; symmetry in Ht6.
   destruct (eq_nat_dec di3 m) as [M3| M3].
    move M3 at top; subst di3.
    remember Ht3 as H; clear HeqH.
    unfold I_add_i in H.
    rewrite Hn5, negb_xorb_diag_l, xorb_true_l in H.
    apply negb_true_iff in H.
    rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
    discriminate H.

    eapply min_neq_lt in M3; eauto ; try (right; left; auto).
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_relay9 in H; [ idtac | eassumption ].
      simpl in H; rewrite H3 in H.
      rename H into A_BCm.
      pose proof (Hn3 m M3) as H.
      rewrite H6 in H.
      apply negb_sym in H.
      unfold I_add_i in H.
      rewrite Ht6, Ht4, xorb_false_r in H.
      apply xorb_move_l_r_1 in H.
      rewrite negb_xorb_diag_r in H.
      rename H into BCm.
      exfalso; eapply case_1; eassumption.

      eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
      exists m, true.
      move H6 at top.
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split.
       pose proof (Hn3 m M3) as H.
       unfold I_add_i in H.
       rewrite H6, Hn5, negb_xorb_diag_l, negb_involutive in H.
       symmetry; assumption.

       split.
        pose proof (Hn4 m M4) as H.
        unfold I_add_i in H.
        rewrite H6, Hn5, xorb_true_l in H.
        rewrite negb_involutive in H.
        apply xorb_move_l_r_1 in H.
        rewrite negb_xorb_diag_r in H.
        assumption.

        intros dj Hdj; apply Hn4.
        eapply le_lt_trans; eassumption.

     eapply min_neq_lt in M6; eauto ; try (left; auto).
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      pose proof (Hn5 m) as H.
      rewrite Ht4 in H; simpl in H.
      rename H into Bm.
      pose proof (Hn6 m M6) as H.
      rewrite Bm in H; simpl in H.
      rename H into Am.
      pose proof (Hn3 m M3) as H.
      rewrite Am in H.
      apply negb_sym in H; simpl in H.
      unfold I_add_i in H.
      rewrite Bm, Ht4, xorb_true_l in H.
      apply negb_true_iff in H.
      rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
      discriminate H.

      eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
      simpl in Hm.
      destruct (Nat.min_dec di4 di6) as [L1| L1]; rewrite L1 in Hm.
       destruct (Nat.min_dec di3 di4) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M3; apply Nat.lt_irrefl.

        subst m; exfalso; revert M4; apply Nat.lt_irrefl.

       destruct (Nat.min_dec di3 di6) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M3; apply Nat.lt_irrefl.

        subst m; exfalso; revert M6; apply Nat.lt_irrefl.

   remember (List.fold_right min di4 [di3 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn3, Ht3).
   rewrite H3 in Ht3; symmetry in Ht3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn6.
   destruct (eq_nat_dec di3 m) as [M3| M3].
    move M3 at top; subst di3.
    remember Ht3 as H; clear HeqH.
    unfold I_add_i in H.
    rewrite Hn5, negb_xorb_diag_l, xorb_true_l in H.
    apply negb_true_iff in H.
    rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
    discriminate H.

    eapply min_neq_lt in M3; eauto ; try (right; left; auto).
    destruct (eq_nat_dec di4 m) as [M4| M4].
     move M4 at top; subst di4.
     pose proof (Hn5 m) as H.
     rewrite Ht4 in H; simpl in H.
     rename H into Bm.
     pose proof (Hn6 m) as H.
     rewrite Bm in H; simpl in H.
     rename H into Am.
     pose proof (Hn3 m M3) as H.
     rewrite Am in H.
     apply negb_sym in H; simpl in H.
     unfold I_add_i in H.
     rewrite Bm, Ht4, xorb_true_l in H.
     apply negb_true_iff in H.
     rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     discriminate H.

     eapply min_neq_lt in M4; [ idtac | eauto  | left; auto ].
     simpl in Hm.
     destruct (Nat.min_dec di3 di4) as [L1| L1]; rewrite L1 in Hm.
      subst m; exfalso; revert M3; apply Nat.lt_irrefl.

      subst m; exfalso; revert M4; apply Nat.lt_irrefl.

 destruct s5 as [di5| ].
  destruct s6 as [di6| ].
   remember (List.fold_right min di6 [di4; di5 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn5, Ht5).
   rewrite H5 in Ht5; symmetry in Ht5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn6, Ht6).
   rewrite H6 in Ht6; symmetry in Ht6.
   destruct (eq_nat_dec di5 m) as [M5| M5].
    move M5 at top; subst di5.
    destruct (eq_nat_dec di4 m) as [M4| M4].
     move M4 at top; subst di4.
     rewrite Ht4 in Ht5.
     move Ht5 at top; subst u.
     destruct (eq_nat_dec di6 m) as [M6| M6].
      move M6 at top; subst di6.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_inf_relay9 in H; simpl in H.
      rename H into A_BCm.
      pose proof (Hn3 m) as H.
      rewrite H6 in H.
      apply negb_sym in H.
      unfold I_add_i in H.
      rewrite Ht6, Ht4, xorb_false_r in H.
      apply xorb_move_l_r_1 in H.
      rewrite negb_xorb_diag_r in H.
      rename H into BCm.
      exfalso; eapply case_1; eassumption.

      eapply min_neq_lt in M6; eauto ; try (left; auto).
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Hn6 in H; [ idtac | assumption ].
      rewrite negb_xorb_diag_l, xorb_true_l in H.
      apply negb_false_iff in H.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H; rewrite H6 in H; discriminate H.

     eapply min_neq_lt in M4; eauto ; try (right; left; auto).
     destruct (eq_nat_dec di6 m) as [M6| M6].
      move M6 at top; subst di6.
      exists m, (negb u).
      split; [ rewrite carry_before_inf_relay9; auto | idtac ].
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split.
       pose proof (Hn3 m) as H.
       unfold I_add_i in H.
       rewrite H6, H5, Ht5, xorb_nilpotent, xorb_false_l in H.
       apply negb_sym in H; assumption.

       split.
        pose proof (Hn4 m M4) as H.
        unfold I_add_i in H.
        rewrite H6, H5, Ht5, xorb_nilpotent, xorb_false_l in H.
        assumption.

        intros dj Hdj; apply Hn4.
        eapply le_lt_trans; eassumption.

      eapply min_neq_lt in M6; eauto ; try (left; auto).
      exists m, u.
      split; [ rewrite carry_before_inf_relay9; auto | idtac ].
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split.
       pose proof (Hn3 m) as H.
       unfold I_add_i in H.
       rewrite Hn6 in H; [ idtac | assumption ].
       rewrite H5, Ht5, xorb_nilpotent, xorb_false_l in H.
       apply negb_sym in H; rewrite negb_involutive in H.
       assumption.

       split.
        pose proof (Hn4 m M4) as H.
        unfold I_add_i in H.
        rewrite Hn6 in H; [ idtac | assumption ].
        rewrite negb_xorb_diag_l, Ht5 in H.
        apply xorb_move_l_r_1 in H.
        rewrite negb_involutive in H; assumption.

        intros dj Hdj; apply Hn4.
        eapply le_lt_trans; eassumption.

    eapply min_neq_lt in M5; eauto ; try (do 2 right; left; auto).
    destruct (eq_nat_dec di4 m) as [M4| M4].
     move M4 at top; subst di4.
     destruct (eq_nat_dec di6 m) as [M6| M6].
      move M6 at top; subst di6.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_inf_relay9 in H; simpl in H.
      rename H into A_BCm.
      pose proof (Hn3 m) as H.
      rewrite H6 in H.
      apply negb_sym in H.
      unfold I_add_i in H.
      rewrite Ht6, Ht4, xorb_false_r in H.
      apply xorb_move_l_r_1 in H.
      rewrite negb_xorb_diag_r in H.
      rename H into BCm.
      exfalso; eapply case_1; eassumption.

      eapply min_neq_lt in M6; eauto ; try (left; auto).
      pose proof (Hn5 m M5) as Bm.
      rewrite Ht4 in Bm; simpl in Bm.
      pose proof (Hn6 m M6) as Am.
      rewrite Bm in Am; simpl in Am.
      pose proof (Hn3 m) as BCm.
      rewrite Am in BCm; apply negb_sym in BCm; simpl in BCm.
      remember BCm as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Bm, Ht4, xorb_true_l in H.
      apply negb_true_iff in H.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H; rewrite H5 in H; move H at top; subst u.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Am, Bm, xorb_true_l in H.
      apply negb_false_iff in H.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H; rewrite H6 in H; discriminate H.

     eapply min_neq_lt in M4; eauto ; try (right; left; auto).
     destruct (eq_nat_dec di6 m) as [M6| M6].
      move M6 at top; subst di6.
      exists m, u.
      split; [ rewrite carry_before_inf_relay9; auto | idtac ].
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split.
       pose proof (Hn3 m) as H.
       unfold I_add_i in H.
       rewrite Hn5 in H; [ idtac | assumption ].
       rewrite H6, negb_xorb_diag_l, negb_involutive in H.
       symmetry; assumption.

       split.
        pose proof (Hn4 m M4) as H.
        unfold I_add_i in H.
        rewrite Hn5 in H; [ idtac | assumption ].
        rewrite H6, xorb_shuffle0, xorb_comm in H.
        apply xorb_move_l_r_1 in H.
        rewrite xorb_nilpotent in H.
        apply xorb_eq in H; symmetry; assumption.

        intros dj Hdj; apply Hn4.
        eapply le_lt_trans; eassumption.

      eapply min_neq_lt in M6; eauto ; try (left; auto).
      simpl in Hm.
      destruct (Nat.min_dec di5 di6) as [L1| L1]; rewrite L1 in Hm.
       destruct (Nat.min_dec di4 di5) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M4; apply Nat.lt_irrefl.

        subst m; exfalso; revert M5; apply Nat.lt_irrefl.

       destruct (Nat.min_dec di4 di6) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M4; apply Nat.lt_irrefl.

        subst m; exfalso; revert M6; apply Nat.lt_irrefl.

   move H6 at top; subst u.
   remember (List.fold_right min di5 [di4 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn5, Ht5).
   rewrite H5 in Ht5; symmetry in Ht5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn6.
   destruct (eq_nat_dec di5 m) as [M5| M5].
    move M5 at top; subst di5.
    destruct (eq_nat_dec di4 m) as [M4| M4].
     move M4 at top; subst di4.
     rewrite Ht5 in Ht4; discriminate Ht4.

     eapply min_neq_lt in M4; eauto ; try (right; left; auto).
     exists m, true.
     split; [ rewrite carry_before_inf_relay9; auto | idtac ].
     split; [ erewrite carry_before_relay9; eassumption | idtac ].
     split.
      pose proof (Hn3 m) as H.
      unfold I_add_i in H.
      rewrite Hn6, H5, Ht5, xorb_true_r, xorb_false_l in H.
      apply negb_sym in H; assumption.

      split.
       pose proof (Hn4 m M4) as H.
       unfold I_add_i in H.
       rewrite Hn6, H5, Ht5, xorb_true_r, negb_involutive in H.
       symmetry in H; apply negb_sym in H.
       assumption.

       intros dj Hdj; apply Hn4.
       eapply le_lt_trans; eassumption.

    eapply min_neq_lt in M5; eauto ; try (left; auto).
    destruct (eq_nat_dec di4 m) as [M4| M4].
     move M4 at top; subst di4.
     pose proof (Hn5 m M5) as Bm.
     rewrite Ht4 in Bm; simpl in Bm.
     pose proof (Hn6 m) as Am.
     rewrite Bm in Am; simpl in Am.
     pose proof (Hn3 m) as BCm.
     rewrite Am in BCm; apply negb_sym in BCm; simpl in BCm.
     remember BCm as H; clear HeqH.
     unfold I_add_i in H.
     rewrite Bm, Ht4, xorb_true_l in H.
     apply negb_true_iff in H.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H; rewrite H5 in H.
     discriminate H.

     eapply min_neq_lt in M4; eauto ; try (right; left; auto).
     simpl in Hm.
     destruct (Nat.min_dec di4 di5) as [L1| L1]; rewrite L1 in Hm.
      subst m; exfalso; revert M4; apply Nat.lt_irrefl.

      subst m; exfalso; revert M5; apply Nat.lt_irrefl.

  move H5 at top; subst u.
  destruct s6 as [di6| ]; [ idtac | clear H6 ].
   remember (List.fold_right min di6 [di4 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn6, Ht6).
   rewrite H6 in Ht6; symmetry in Ht6.
   destruct (eq_nat_dec di4 m) as [M4| M4].
    move M4 at top; subst di4.
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     remember H4 as H; clear HeqH.
     unfold I_add_i in H.
     rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
     rename H into ABm.
     remember Hs3 as H; clear HeqH.
     eapply carry_before_inf_relay9 in H; simpl in H.
     rename H into A_BCm.
     pose proof (Hn3 m) as H.
     rewrite H6 in H.
     apply negb_sym in H.
     unfold I_add_i in H.
     rewrite Ht6, Ht4, xorb_false_r in H.
     apply xorb_move_l_r_1 in H.
     rewrite negb_xorb_diag_r in H.
     rename H into BCm.
     exfalso; eapply case_1; eassumption.

     eapply min_neq_lt in M6; eauto ; try (left; auto).
     pose proof (Hn5 m) as Bm.
     rewrite Ht4 in Bm; simpl in Bm.
     pose proof (Hn6 m M6) as Am.
     rewrite Bm in Am; simpl in Am.
     pose proof (Hn3 m) as BCm; apply negb_sym in BCm.
     rewrite Am in BCm; simpl in BCm.
     remember BCm as H; clear HeqH.
     unfold I_add_i in H.
     rewrite Bm, Ht4, xorb_true_l in H.
     apply negb_true_iff in H.
     rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     discriminate H.

    eapply min_neq_lt in M4; eauto ; try (right; left; auto).
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     exists m, true.
     split; [ rewrite carry_before_inf_relay9; auto | idtac ].
     split; [ erewrite carry_before_relay9; eassumption | idtac ].
     split.
      pose proof (Hn3 m) as H.
      unfold I_add_i in H.
      rewrite H6, Hn5, negb_xorb_diag_l, negb_involutive in H.
      symmetry; assumption.

      split.
       pose proof (Hn4 m M4) as H.
       unfold I_add_i in H.
       rewrite H6, Hn5, xorb_true_l, negb_involutive in H.
       apply xorb_move_l_r_1 in H.
       rewrite negb_xorb_diag_r in H.
       assumption.

       intros dj Hdj; apply Hn4.
       eapply le_lt_trans; eassumption.

     eapply min_neq_lt in M6; eauto ; try (left; auto).
     simpl in Hm.
     destruct (Nat.min_dec di4 di6) as [L1| L1]; rewrite L1 in Hm.
      subst m; exfalso; revert M4; apply Nat.lt_irrefl.

      subst m; exfalso; revert M6; apply Nat.lt_irrefl.

   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn6.
   rename di4 into m.
   pose proof (Hn5 m) as Bm.
   rewrite Ht4 in Bm; simpl in Bm.
   pose proof (Hn6 m) as Am.
   rewrite Bm in Am; simpl in Am.
   pose proof (Hn3 m) as BCm; apply negb_sym in BCm.
   rewrite Am in BCm; simpl in BCm.
   remember BCm as H; clear HeqH.
   unfold I_add_i in H.
   rewrite Bm, Ht4, xorb_true_l in H.
   apply negb_true_iff in H.
   rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
   discriminate H.
Qed.

Theorem case_3 : ∀ x y z i u,
  carry x (y + z) i = true
  → carry (x + y) z i = false
  → carry y z i = u
  → carry x y i = u
  → False.
Proof.
intros x y z i u Hc3 Hc4 Hc5 Hc6.
remember Hc4 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (x + y) z i) as s eqn:Hs .
destruct s as [di| ]; [ idtac | discriminate H ].
symmetry in Hs; clear H.
revert x y z i u Hc3 Hc4 Hc5 Hc6 Hs.
induction di as (di, IHdi) using all_lt_all; intros.
remember Hc3 as H; clear HeqH.
eapply carry_repeat2 with (y := y) in H; try eassumption.
destruct H as (n, (t, (Rx_yzn, (Rxy_zn, (Ryzn, (Rxyn, Hnxy_z)))))).
remember Hs as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hnxy_z2, Hxy_z).
destruct (le_dec di n) as [H1| H1].
 rewrite Hnxy_z in Hxy_z; [ idtac | assumption ].
 revert Hxy_z; apply no_fixpoint_negb.

 apply Nat.nle_gt in H1.
 remember (di - S n) as dj.
 apply nat_sub_add_r in Heqdj; [ idtac | assumption ].
 remember (I_shift_l (S n) (x + y)%I) as x'y' eqn:Hxy .
 remember (I_shift_l (S n) z) as z' eqn:Hc .
 eapply fst_same_shift in Hs; try eassumption.
 assert (0 < S n) as Hn by apply Nat.lt_0_succ.
 assert (di - S n < di) as H by (apply Nat.sub_lt; assumption).
 subst x'y'.
 rewrite fst_same_shift_add_l in Hs.
 remember (I_shift_l (S n) x) as x' eqn:Ha .
 remember (I_shift_l (S n) y) as y' eqn:Hb .
 eapply IHdi with (x := x') (y := y') (z := z'); try eassumption.
  subst x' y' z'.
  rewrite carry_comm.
  rewrite carry_shift_add_l, Nat.add_succ_r.
  rewrite carry_comm; assumption.

  subst x' y' z'.
  rewrite carry_shift_add_l, Nat.add_succ_r; assumption.

  subst y' z'.
  rewrite carry_shift.
  rewrite Nat.add_succ_r; eassumption.

  subst x' y'.
  rewrite carry_shift.
  rewrite Nat.add_succ_r; assumption.
Qed.

Theorem I_add_assoc_norm : ∀ x y z,
  ((x + 0) + ((y + 0) + (z + 0)) = ((x + 0) + (y + 0)) + (z + 0))%I.
Proof.
intros x y z.
rename x into x0; rename y into y0; rename z into z0.
remember (x0 + 0)%I as x.
remember (y0 + 0)%I as y.
remember (z0 + 0)%I as z.
unfold I_eq; intros i; simpl.
unfold I_add_i; simpl.
do 2 rewrite xorb_false_r.
remember (carry (x + (y + z))%I 0%I (S i)) as c1 eqn:Hc1 .
remember (carry (x + y + z)%I 0%I (S i)) as c2 eqn:Hc2 .
unfold I_add_i; simpl.
remember (carry x (y + z)%I (S i)) as c3 eqn:Hc3 .
remember (carry (x + y)%I z (S i)) as c4 eqn:Hc4 .
unfold I_add_i; simpl.
remember (carry y z (S i)) as c5 eqn:Hc5 .
remember (carry x y (S i)) as c6 eqn:Hc6 .
do 8 rewrite xorb_assoc; f_equal; f_equal; symmetry.
rewrite xorb_comm, xorb_assoc; f_equal; symmetry.
rewrite <- xorb_assoc.
symmetry in Hc1, Hc2, Hc3, Hc4, Hc5, Hc6.
move c2 before c1; move c3 before c2.
move c4 before c3; move c5 before c4.
move c6 before c5.
remember Hc1 as H; clear HeqH.
erewrite carry_sum_3_noI_assoc_r in H; try eassumption.
move H at top; subst c1.
remember Hc2 as H; clear HeqH.
erewrite carry_sum_3_noI_assoc_l in H; try eassumption.
move H at top; subst c2.
do 2 rewrite xorb_false_r.
destruct c3, c4, c5, c6; try reflexivity; exfalso.
 eapply case_1; eassumption.

 rewrite carry_comm_l in Hc4.
 eapply case_1; rewrite carry_comm; eassumption.

 eapply case_3; eassumption.

 eapply case_3; eassumption.

 rewrite carry_comm_r in Hc3.
 rewrite carry_comm_l in Hc4.
 eapply case_3; rewrite carry_comm; eassumption.

 rewrite carry_comm_r in Hc3.
 rewrite carry_comm_l in Hc4.
 eapply case_3; rewrite carry_comm; eassumption.

 clear Hc1 Hc2.
 eapply case_2; eassumption.

 rewrite carry_comm_r in Hc3.
 eapply case_2; rewrite carry_comm; eassumption.
Qed.

Theorem I_add_assoc : ∀ x y z, (x + (y + z) = (x + y) + z)%I.
Proof.
intros x y z.
pose proof (I_add_assoc_norm x y z) as H.
do 3 rewrite I_add_0_r in H; assumption.
Qed.

(* decidability *)

Theorem I_zerop : ∀ x, {(x = 0)%I} + {(x ≠ 0)%I}.
Proof.
intros x.
remember (fst_same (x + 0%I) I_ones 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Hs).
 right; intros H.
 unfold I_eq in H; simpl in H.
 pose proof (H di) as HH.
 rewrite Hs in HH; symmetry in HH.
 unfold I_add_i in HH; simpl in HH.
 unfold carry in HH; simpl in HH.
 rewrite fst_same_diag in HH; discriminate HH.

 left.
 unfold I_eq; intros i; simpl.
 rewrite Hs.
 unfold I_add_i; simpl.
 unfold carry; simpl.
 rewrite fst_same_diag; reflexivity.
Qed.

Theorem I_eq_dec : ∀ x y, {(x = y)%I} + {(x ≠ y)%I}.
Proof.
intros x y.
destruct (I_zerop (x - y)%I) as [Hxy| Hxy].
 left; unfold I_sub in Hxy; rewrite I_add_comm in Hxy.
 eapply I_add_compat with (x := y) in Hxy; [ idtac | reflexivity ].
 rewrite I_add_assoc, fold_I_sub, I_sub_diag, I_add_comm in Hxy.
 do 2 rewrite I_add_0_r in Hxy.
 assumption.

 right; unfold I_sub in  Hxy; intros H; apply Hxy; rewrite H.
 apply I_sub_diag.
Qed.

Theorem I_decidable : ∀ x y, Decidable.decidable (x = y)%I.
Proof.
intros x y.
destruct (I_eq_dec x y); [ left | right ]; assumption.
Qed.

(* morphisms *)

Theorem I_eq_neq_if : ∀ x y i,
  (x = y)%I
  → x.[i] = true
  → y.[i] = false
  → (∀ di, x.[i+di] = true) ∧ (∀ di, y.[i+di] = false) ∨
    (∀ di, x.[i+S di] = false) ∧ (∀ di, y.[i+S di] = true).
Proof.
intros x y i Hxy Hx Hy.
unfold I_eq in Hxy; simpl in Hxy.
pose proof (Hxy i) as H.
unfold I_add_i in H; simpl in H.
rewrite Hx, Hy, xorb_true_l, xorb_false_l in H.
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
  rewrite Hty in H; discriminate H.

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
    do 2 rewrite xorb_false_r in H.
    rewrite Hnx in H; [ idtac | apply Nat.lt_succ_diag_r ].
    rewrite Hny in H.
    rewrite xorb_true_l in H.
    symmetry in H.
    rewrite xorb_true_l in H.
    apply negb_sym in H.
    rewrite negb_involutive in H.
    rewrite <- Nat.add_succ_l in H.
    symmetry in Hsx.
    erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
    symmetry in Hsy.
    simpl in H.
    do 2 rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
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
     rewrite <- negb_involutive.
     apply neq_negb; simpl; intros Hdi.
     rewrite Nat.add_0_r in Hdi.
     pose proof (Hxy (S (i + dx))) as H.
     unfold I_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite Htx, Hny, xorb_false_l, xorb_true_l in H.
     symmetry in H, Hsx, Hsy.
     rewrite <- Nat.add_succ_l in H.
     rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
     symmetry in H.
     unfold carry in H; simpl in H.
     remember (fst_same x 0 (S (S (i + dx)))) as s1 eqn:Hs1 .
     destruct s1 as [di1| ]; [ idtac | discriminate H ].
     rename H into Hx1.
     destruct di1.
      rewrite Nat.add_0_r, <- Nat.add_succ_r in Hx1.
      rewrite Hdi in Hx1; discriminate Hx1.

      remember Hs1 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn1, _).
      pose proof (Hxy (S (S (i + dx)))) as H.
      unfold I_add_i in H; simpl in H.
      do 2 rewrite xorb_false_r in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hdi, Hny, xorb_true_l in H.
      apply negb_sym in H.
      rewrite negb_involutive in H.
      rewrite <- Nat.add_succ_l in H.
      rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
      symmetry in H, Hs1.
      replace dx with (dx + 0)%nat in H by apply Nat.add_0_r.
      simpl in H.
      rewrite Nat.add_succ_r, Nat.add_assoc in H.
      do 2 rewrite <- Nat.add_succ_l in H.
      assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H.
      rewrite Hx1 in H; discriminate H.

     rewrite Nat.add_succ_r.
     rewrite <- negb_involutive.
     apply neq_negb; simpl; intros Hdi.
     pose proof (Hxy (S (i + dx + S n))) as H.
     unfold I_add_i in H; simpl in H.
     do 2 rewrite xorb_false_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite IHn in H; [ idtac | apply Nat.lt_succ_diag_r ].
     rewrite Hny, xorb_false_l, xorb_true_l in H.
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
      do 2 rewrite xorb_false_r in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Nat.add_assoc in H.
      rewrite Nat.add_succ_r in H.
      rewrite Hdi, Hny, xorb_true_l in H.
      apply negb_sym in H.
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
   do 2 rewrite xorb_false_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite xorb_true_l in H.
   apply negb_sym in H.
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
   do 2 rewrite xorb_false_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite xorb_true_l in H.
   apply negb_sym in H.
   rewrite negb_involutive in H.
   rewrite <- Nat.add_succ_l in H.
   symmetry in Hsy.
   erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
   symmetry in Hsx.
   rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
   simpl in H; rewrite Hty in H; discriminate H.

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
     apply fst_same_sym_iff in H; simpl in H.
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
     apply fst_same_sym_iff in H; simpl in H.
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

Theorem fst_same_opp_some_some : ∀ x y i dj,
  (x = y)%I
  → fst_same (- x) 0 (S i) = Some 0
  → fst_same (- y) 0 (S i) = Some (S dj)
  → x.[i] = y.[i].
Proof.
intros x y i dj4 Heq Hs3 Hs4.
remember Hs3 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, Ht3).
rewrite Nat.add_0_r in Ht3.
apply negb_false_iff in Ht3.
remember Hs4 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hn4, Ht4).
apply negb_false_iff in Ht4.
remember Heq as H; clear HeqH.
unfold I_eq in H; simpl in H.
rename H into Hxy.
pose proof (Hxy i) as Hi.
unfold I_add_i in Hi; simpl in Hi.
do 2 rewrite xorb_false_r in Hi.
unfold carry in Hi; simpl in Hi.
remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
remember (fst_same y 0 (S i)) as s2 eqn:Hs2 .
pose proof (Hn4 O (Nat.lt_0_succ dj4)) as H.
rewrite Nat.add_0_r in H.
apply negb_true_iff in H.
rename H into Hy4.
remember Ht3 as H; clear HeqH.
eapply I_eq_neq_if in H; try eassumption.
destruct H as [(Hxi, Hyi)| (Hxi, Hyi)]; simpl in Hxi, Hyi.
 rewrite Hyi in Ht4; discriminate Ht4.

 destruct s1 as [dj1| ].
  remember Hs1 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn1, Ht1).
  rewrite Ht1, xorb_false_r in Hi.
  destruct s2 as [dj2| ].
   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn2, Ht2).
   rewrite Ht2, xorb_false_r in Hi.
   rewrite Hi; reflexivity.

   exfalso.
   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rename H into Hn2.
   pose proof (Hn2 O) as H.
   rewrite Nat.add_0_r, Hy4 in H; discriminate H.

  remember Hs1 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  rename H into Hn1.
  pose proof (Hxi O) as H.
  rewrite Hn1 in H; discriminate H.
Qed.

Theorem fst_same_opp_some_0_none : ∀ x y i,
  (x = y)%I
  → fst_same (- x) 0 (S i) = Some 0
  → fst_same (- y) 0 (S i) = None
  → x.[i] ≠ y.[i].
Proof.
intros x y i Heq Hs1 Hs2.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
apply fst_same_iff in Hs2; simpl in Hs2.
rewrite Nat.add_0_r in Ht1.
apply negb_false_iff in Ht1.
clear Hn1.
intros Hxy.
pose proof (Heq i) as Hi; simpl in Hi.
unfold I_add_i in Hi; simpl in Hi.
do 2 rewrite xorb_false_r in Hi.
rewrite Hxy in Hi.
apply xorb_move_l_r_1 in Hi.
rewrite <- xorb_assoc in Hi.
rewrite xorb_nilpotent, xorb_false_l in Hi.
unfold carry in Hi; simpl in Hi.
remember (fst_same x 0 (S i)) as s3 eqn:Hs3 .
remember (fst_same y 0 (S i)) as s4 eqn:Hs4 .
apply fst_same_sym_iff in Hs3; simpl in Hs3.
apply fst_same_sym_iff in Hs4; simpl in Hs4.
destruct s3 as [dj3| ].
 destruct Hs3 as (Hn3, Ht3).
 rewrite Ht3 in Hi.
 destruct s4 as [dj4| ]; [ idtac | discriminate Hi ].
 destruct Hs4 as (Hn4, Ht4); clear Hi.
 destruct dj3.
  rewrite Nat.add_0_r, Ht1 in Ht3; discriminate Ht3.

  destruct dj4.
   clear Hn4; rewrite Nat.add_0_r in Ht4.
   remember Ht1 as H; clear HeqH.
   eapply I_eq_neq_if in H; try eassumption.
   destruct H as [(Hxi, Hyi)| (Hxi, Hyi)]; simpl in Hxi, Hyi.
    rewrite Hxi in Ht3; discriminate Ht3.

    pose proof (Hyi O) as H.
    apply negb_false_iff in H.
    rewrite Hs2 in H; discriminate H.

   pose proof (Hn4 O (Nat.lt_0_succ dj4)) as H.
   apply negb_false_iff in H.
   rewrite Hs2 in H; discriminate H.

 destruct s4 as [dj4| ].
  destruct Hs4 as (Hn4, Ht4).
  rewrite Ht4 in Hi; discriminate Hi.

  pose proof (Hs2 O) as H.
  rewrite Hs4 in H; discriminate H.
Qed.

Theorem fst_same_some_after : ∀ x y i di,
  fst_same x y i = Some di
  → fst_same x y (i + di) = Some 0.
Proof.
intros x y i di Hdi.
apply fst_same_iff in Hdi; simpl in Hdi.
destruct Hdi as (Hni, Hti).
apply fst_same_iff; simpl.
split; [ idtac | rewrite Nat.add_0_r; assumption ].
intros dj Hdj; exfalso; revert Hdj; apply Nat.nlt_0_r.
Qed.

Theorem fst_same_opp_some_none : ∀ x y i dj,
  (x = y)%I
  → fst_same (- x) 0 (S i) = Some dj
  → fst_same (- y) 0 (S i) = None
  → x.[i] ≠ y.[i].
Proof.
intros x y i dj3 Heq Hs3 Hs4.
remember Hs4 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
rename H into Hn4.
remember Hs3 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hn3, Ht3).
apply negb_false_iff in Ht3.
pose proof (Heq i) as Hi; simpl in Hi.
unfold I_add_i in Hi; simpl in Hi.
do 2 rewrite xorb_false_r in Hi.
unfold carry in Hi; simpl in Hi.
remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
remember (fst_same y 0 (S i)) as s2 eqn:Hs2 .
pose proof (Hn4 dj3) as H.
apply negb_true_iff in H.
rename H into Hy.
remember Ht3 as H; clear HeqH.
eapply I_eq_neq_if in H; try eassumption.
destruct H as [(Hxi, Hyi)| (Hxi, Hyi)]; simpl in Hxi, Hyi.
 destruct s1 as [dj1| ].
  remember Hs1 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn1, Ht1).
  rewrite Ht1, xorb_false_r in Hi.
  destruct s2 as [dj2| ].
   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn2, Ht2).
   rewrite Ht2, xorb_false_r in Hi.
   exfalso.
   destruct dj3.
    rewrite Nat.add_0_r in Hxi, Hyi.
    eapply fst_same_opp_some_0_none in Hs3; try eassumption.
    contradiction.

    remember Hs4 as H; clear HeqH.
    apply fst_same_inf_after with (di := S dj3) in H.
    simpl in H.
    eapply fst_same_opp_some_0_none in H; try eassumption.
     rewrite Nat.add_succ_r in H.
     apply H.
     rewrite <- negb_involutive; apply negb_sym.
     rewrite Hn3; [ idtac | apply Nat.lt_succ_diag_r ].
     apply Hn4.

     rewrite <- Nat.add_succ_l.
     apply fst_same_some_after; assumption.

   apply neq_negb; assumption.

  destruct s2 as [dj2| ].
   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn2, Ht2).
   rewrite Ht2, xorb_false_r, xorb_true_r in Hi.
   apply neq_negb, negb_sym; symmetry; assumption.

   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rewrite H in Hy; discriminate Hy.

 pose proof (Hyi O) as H.
 rewrite <- Nat.add_assoc in H.
 apply negb_false_iff in H.
 rewrite Hn4 in H; discriminate H.
Qed.

Add Parametric Morphism : I_opp
  with signature I_eq ==> I_eq
  as I_opp_morph.
Proof.
intros x y Hxy.
remember Hxy as Heq; clear HeqHeq.
unfold I_eq in Hxy; simpl in Hxy.
unfold I_eq; simpl; intros i.
pose proof (Hxy i) as Hi.
unfold I_add_i in Hi; simpl in Hi.
do 2 rewrite xorb_false_r in Hi.
unfold I_add_i; simpl.
do 2 rewrite xorb_false_r.
unfold carry in Hi; simpl in Hi.
unfold carry; simpl.
remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
remember (fst_same y 0 (S i)) as s2 eqn:Hs2 .
remember (fst_same (- x) 0 (S i)) as s3 eqn:Hs3 .
remember (fst_same (- y) 0 (S i)) as s4 eqn:Hs4 .
remember Hs3 as H; clear HeqH.
apply fst_same_sym_iff in H; simpl in H.
destruct s3 as [dj3| ].
 destruct H as (Hn3, Ht3).
 rewrite Ht3, xorb_false_r.
 apply negb_false_iff in Ht3.
 destruct s4 as [dj4| ].
  remember Hs4 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn4, Ht4).
  rewrite Ht4, xorb_false_r.
  apply negb_sym; symmetry.
  rewrite negb_involutive.
  apply negb_false_iff in Ht4.
  destruct dj3.
   clear Hn3; rewrite Nat.add_0_r in Ht3.
   destruct dj4.
    clear Hn4; rewrite Nat.add_0_r in Ht4.
    destruct s1 as [dj1| ].
     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, Ht1).
     rewrite Ht1, xorb_false_r in Hi.
     destruct s2 as [dj2| ].
      remember Hs2 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn2, Ht2).
      rewrite Ht2, xorb_false_r in Hi.
      rewrite Hi; reflexivity.

      exfalso.
      remember (y .[ i]) as b eqn:Hy .
      symmetry in Hy.
      destruct b; simpl in Hi.
       symmetry in Heq.
       remember Hy as H; clear HeqH.
       eapply I_eq_neq_if in H; try eassumption.
       destruct H as [(Hyi, Hxi)| (Hyi, Hxi)]; simpl in Hxi, Hyi.
        rewrite <- Nat.add_1_r, Hxi in Ht3; discriminate Ht3.

        pose proof (Hyi O) as H.
        rewrite Nat.add_1_r, Ht4 in H; discriminate H.

       remember Hi as H; clear HeqH.
       eapply I_eq_neq_if in H; try eassumption.
       destruct H as [(Hxi, Hyi)| (Hxi, Hyi)]; simpl in Hxi, Hyi.
        rewrite <- Nat.add_1_r, Hyi in Ht4; discriminate Ht4.

        pose proof (Hxi O) as H.
        rewrite Nat.add_1_r, Ht3 in H; discriminate H.

     destruct s2 as [dj2| ].
      remember Hs2 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn2, Ht2).
      rewrite Ht2, xorb_false_r in Hi.
      exfalso.
      remember (x .[ i]) as b eqn:Hx .
      symmetry in Hx, Hi.
      destruct b; simpl in Hi.
       remember Hx as H; clear HeqH.
       eapply I_eq_neq_if in H; try eassumption.
       destruct H as [(Hxi, Hyi)| (Hxi, Hyi)]; simpl in Hxi, Hyi.
        rewrite <- Nat.add_1_r, Hyi in Ht4; discriminate Ht4.

        pose proof (Hxi O) as H.
        rewrite Nat.add_1_r, Ht3 in H; discriminate H.

       symmetry in Heq.
       remember Hi as H; clear HeqH.
       eapply I_eq_neq_if in H; try eassumption.
       destruct H as [(Hyi, Hxi)| (Hyi, Hxi)]; simpl in Hxi, Hyi.
        rewrite <- Nat.add_1_r, Hxi in Ht3; discriminate Ht3.

        pose proof (Hyi O) as H.
        rewrite Nat.add_1_r, Ht4 in H; discriminate H.

      apply xorb_move_l_r_2 in Hi.
      rewrite Hi, xorb_true_r, xorb_true_r.
      apply negb_involutive.

    symmetry in Hs3, Hs4.
    eapply fst_same_opp_some_some; eassumption.

   destruct dj4.
    clear Hn4; rewrite Nat.add_0_r in Ht4.
    symmetry in Heq; symmetry.
    symmetry in Hs3, Hs4.
    eapply fst_same_opp_some_some; eassumption.

    destruct s1 as [dj1| ].
     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, Ht1).
     rewrite Ht1, xorb_false_r in Hi.
     destruct s2 as [dj2| ].
      remember Hs2 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn2, Ht2).
      rewrite Ht2, xorb_false_r in Hi; assumption.

      exfalso.
      remember Hs2 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      rename H into Hn2.
      pose proof (Hn4 O (Nat.lt_0_succ dj4)) as H.
      rewrite Hn2 in H; discriminate H.

     exfalso.
     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     rename H into Hn1.
     pose proof (Hn3 O (Nat.lt_0_succ dj3)) as H.
     rewrite Hn1 in H; discriminate H.

  remember Hs4 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  rename H into Hn4.
  rewrite xorb_true_r; f_equal.
  apply neq_negb.
  symmetry in Hs3, Hs4.
  eapply fst_same_opp_some_none; eassumption.

 rename H into Hn3.
 destruct s4 as [dj4| ].
  remember Hs4 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn4, Ht4).
  rewrite Ht4, xorb_false_r.
  apply negb_false_iff in Ht4.
  rewrite xorb_true_r; f_equal.
  symmetry; apply neq_negb.
  symmetry in Heq, Hs3, Hs4.
  eapply fst_same_opp_some_none; eassumption.

  remember Hs4 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  rename H into Hn4.
  destruct s1 as [dj1| ].
   remember Hs1 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn1, Ht1).
   rewrite Ht1, xorb_false_r in Hi.
   destruct s2 as [dj2| ].
    remember Hs2 as H; clear HeqH.
    apply fst_same_sym_iff in H; simpl in H.
    destruct H as (Hn2, Ht2).
    rewrite Ht2, xorb_false_r in Hi.
    rewrite Hi; reflexivity.

    remember Hs2 as H; clear HeqH.
    apply fst_same_sym_iff in H; simpl in H.
    rename H into Hn2.
    pose proof (Hn4 O) as H.
    rewrite Hn2 in H; discriminate H.

   remember Hs1 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rename H into Hn1.
   pose proof (Hn3 O) as H.
   rewrite Hn1 in H; discriminate H.
Qed.

Add Parametric Morphism : I_sub
  with signature I_eq ==> I_eq ==> I_eq
  as I_sub_morph.
Proof.
intros x y Hxy z d Hcd.
unfold I_sub.
rewrite Hxy, Hcd; reflexivity.
Qed.

Theorem I_opp_involutive : ∀ x, (- - x = x)%I.
Proof.
intros x.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
do 2 rewrite xorb_false_r.
rewrite negb_involutive; f_equal.
erewrite carry_compat; [ reflexivity | simpl | simpl ].
 intros j; apply negb_involutive.

 intros j; reflexivity.
Qed.

(* miscellaneous *)

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

Theorem I_opp_0 : (- 0 = 0)%I.
Proof.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
rewrite carry_diag; simpl.
unfold carry; simpl.
destruct (fst_same (- 0%I) 0 (S i)); reflexivity.
Qed.

Theorem I_add_shuffle0 : ∀ x y z, (x + y + z = x + z + y)%I.
Proof.
intros x y z.
do 2 rewrite <- I_add_assoc.
apply I_add_compat; [ reflexivity | apply I_add_comm ].
Qed.

Theorem I_sub_move_0_r : ∀ x y, (x - y = 0)%I ↔ (x = y)%I.
Proof.
intros x y.
split; intros Hxy.
 apply I_add_compat_r with (z := y) in Hxy.
 unfold I_sub in Hxy.
 rewrite I_add_shuffle0, <- I_add_assoc in Hxy.
 rewrite fold_I_sub, I_sub_diag in Hxy.
 rewrite I_add_0_r, I_add_comm, I_add_0_r in Hxy.
 assumption.

 rewrite Hxy; apply I_sub_diag.
Qed.

Close Scope nat_scope.
