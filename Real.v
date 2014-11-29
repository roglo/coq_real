Require Import Utf8 QArith NPeano.

Set Implicit Arguments.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).
Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).

Open Scope nat_scope.

(* reals modulo 1 *)
Record real_mod_1 := { rm : nat → bool }.

Definition rm_zero := {| rm i := false |}.
Definition rm_zero' := {| rm i := true |}.

Notation "s .[ i ]" := (rm s i) (at level 1).

Axiom fst_same : real_mod_1 → real_mod_1 → nat → option nat.
Axiom fst_same_iff : ∀ x y i odi, fst_same x y i = odi ↔
  match odi with
  | Some di =>
      (∀ dj, dj < di → x.[i + dj] = negb y.[i + dj])
      ∧ x.[i + di] = y.[i + di]
  | None =>
      ∀ dj, x.[i + dj] = negb y.[i + dj]
  end.

Infix "⊕" := xorb (left associativity, at level 50) : bool_scope.

Definition carry x y i :=
  match fst_same x y (S i) with
  | Some dj => x.[S i + dj]
  | None => true
  end.

Definition rm_add_i x y i := x.[i] ⊕ y.[i] ⊕ carry x y i.
Definition rm_add x y := {| rm := rm_add_i x y |}.
Definition rm_eq x y := ∀ i,
  rm (rm_add x rm_zero) i = rm (rm_add y rm_zero) i.

Delimit Scope rm_scope with rm.
Notation "x + y" := (rm_add x y) (at level 50, left associativity) : rm_scope.
Notation "x = y" := (rm_eq x y) : rm_scope.
Notation "x ≠ y" := (¬ rm_eq x y) : rm_scope.
Notation "0" := rm_zero : rm_scope.

Arguments rm r%rm i%nat.
Arguments carry x%rm y%rm i%nat.
Arguments rm_add_i x%rm y%rm i%nat.
Arguments fst_same x%rm y%rm i%nat.

Definition rm_opp x := {| rm i := negb x.[i] |}.
Definition rm_sub x y := (x + rm_opp y)%rm.

Notation "- x" := (rm_opp x) : rm_scope.
Notation "x - y" := (rm_add x (rm_opp y)) : rm_scope.

Theorem rm_eq_refl : reflexive _ rm_eq.
Proof. intros x i; reflexivity. Qed.

Theorem rm_eq_sym : symmetric _ rm_eq.
Proof. intros x y Hxy i; symmetry; apply Hxy. Qed.

Theorem rm_eq_trans : transitive _ rm_eq.
Proof. intros x y z Hxy Hyz i; rewrite Hxy; apply Hyz. Qed.

Add Parametric Relation : _ rm_eq
 reflexivity proved by rm_eq_refl
 symmetry proved by rm_eq_sym
 transitivity proved by rm_eq_trans
 as rm_rel.

Theorem fst_same_sym_iff : ∀ x y i odi,
  odi = fst_same x y i
  ↔ match odi with
    | Some di =>
        (∀ dj : nat, dj < di → x .[ i + dj] = negb y .[ i + dj])
        ∧ x .[ i + di] = y .[ i + di]
    | None => ∀ dj : nat, x .[ i + dj] = negb y .[ i + dj]
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

Theorem forall_compat : ∀ α (P Q : α → Prop),
  (∀ x, P x → Q x)
  → (∀ x, P x)
  → id (∀ x, Q x).
Proof.
intros α P Q HPQ HP x.
apply HPQ, HP.
Qed.

Theorem forall_add_succ_r : ∀ α i f (x : α),
  (∀ j, f (i + S j) = x)
  → id (∀ j, f (S i + j) = x).
Proof.
intros α i f x; unfold id; intros H j.
rewrite Nat.add_succ_l, <- Nat.add_succ_r; apply H.
Qed.

Theorem forall_add_succ_l : ∀ α i f (x : α),
  (∀ j : nat, f (S (i + j)) = x)
  → id (∀ j : nat, f (S i + j) = x).
Proof.
intros α i f x; unfold id; intros H j.
apply H.
Qed.

Theorem negb_xorb_diag_l : ∀ x, negb x ⊕ x = true.
Proof. intros x; destruct x; reflexivity. Qed.

Theorem negb_xorb_diag_r : ∀ x, x ⊕ negb x = true.
Proof. intros x; destruct x; reflexivity. Qed.

Theorem xorb_shuffle0 : ∀ x y z, x ⊕ y ⊕ z = x ⊕ z ⊕ y.
Proof.
intros x y z.
do 2 rewrite xorb_assoc; f_equal.
apply xorb_comm.
Qed.

Theorem neq_negb : ∀ y y', y ≠ y' ↔ y = negb y'.
Proof.
intros y y'.
split; intros H.
 destruct y'; simpl.
  apply not_true_iff_false; auto.

  apply not_false_iff_true; auto.

 subst y; intros H.
 destruct y'; discriminate H.
Qed.

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
remember (fst_same y x (S i)) as s eqn:Hs .
destruct s as [di| ]; [ idtac | reflexivity ].
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct Hs; symmetry; assumption.
Qed.

Theorem rm_add_i_comm : ∀ x y i, rm_add_i x y i = rm_add_i y x i.
Proof.
intros x y i.
unfold rm_add_i, carry.
rewrite fst_same_comm.
remember (fst_same y x (S i)) as s eqn:Hs .
symmetry in Hs.
apply fst_same_iff in Hs.
destruct s as [di| ]; [ idtac | f_equal; apply xorb_comm ].
f_equal; [ apply xorb_comm | destruct Hs; auto ].
Qed.

(* TODO: carry_comm to be used *)
Theorem rm_add_comm : ∀ x y, (x + y = y + x)%rm.
Proof.
intros x y.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry; simpl.
do 2 rewrite xorb_false_r.
remember (fst_same (x + y) 0 (S i)) as sxy eqn:Hsxy .
remember (fst_same (y + x) 0 (S i)) as syx eqn:Hsyx .
symmetry in Hsxy, Hsyx.
apply fst_same_iff in Hsxy.
apply fst_same_iff in Hsyx.
simpl in Hsxy, Hsyx.
destruct sxy as [dixy| ].
 destruct Hsxy as (Hnxy, Hsxy).
 destruct syx as [diyx| ].
  destruct Hsyx as (Hnyx, Hsyx).
  rewrite Hsxy, Hsyx.
  rewrite rm_add_i_comm; reflexivity.

  rewrite xorb_comm, rm_add_i_comm, Hsyx.
  rewrite xorb_comm, rm_add_i_comm; reflexivity.

 destruct syx as [diyx| ]; [ idtac | rewrite rm_add_i_comm; reflexivity ].
 destruct Hsyx as (Hnyx, Hsyx).
 symmetry; rewrite xorb_comm.
 rewrite rm_add_i_comm, Hsxy.
 rewrite rm_add_i_comm, rm_add_i_comm; reflexivity.
Qed.

Theorem rm_add_0_inf_1 : ∀ x i,
  (∀ dj, rm_add_i x 0 (i + dj) = true)
  → id (∀ dk, x .[i + dk] = true).
Proof.
intros x i Hs dk.
revert i Hs.
induction dk; intros.
 rewrite Nat.add_0_r.
 pose proof (Hs 0) as H; simpl in H.
 rewrite Nat.add_0_r in H.
 unfold rm_add_i, carry in H; simpl in H.
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
  unfold rm_add_i, carry in H1; simpl in H1.
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

Theorem not_rm_add_0_inf_1 : ∀ x i, ¬ (∀ dj, rm_add_i x 0 (i + dj) = true).
Proof.
intros x i Hs.
rename Hs into Hs1.
remember Hs1 as H; clear HeqH.
apply rm_add_0_inf_1 in H; unfold id in H.
rename H into Hk.
pose proof (Hs1 0) as H; simpl in H.
rewrite Nat.add_0_r in H.
unfold rm_add_i, carry in H.
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

Theorem not_rm_add_0_inf_1_succ : ∀ x i,
  ¬ (∀ dj, rm_add_i x 0 (i + S dj) = true).
Proof.
intros x i H.
eapply not_rm_add_0_inf_1 with (i := S i); intros dj.
rewrite Nat.add_succ_l, <- Nat.add_succ_r.
apply H.
Qed.

Theorem rm_add_i_0_r : ∀ x i, rm_add_i (x + 0%rm) 0 i = rm_add_i x 0 i.
Proof.
intros x i.
unfold rm_add_i, carry at 1.
remember (S i) as si; simpl.
rewrite xorb_false_r.
remember (fst_same (x + 0%rm) 0 si) as s1 eqn:Hs1 .
symmetry in Hs1.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hs1, xorb_false_r; reflexivity.

 exfalso; eapply not_rm_add_0_inf_1; eauto .
Qed.

Theorem rm_add_0_r : ∀ x, (x + 0 = x)%rm.
Proof.
intros x.
unfold rm_eq.
apply rm_add_i_0_r.
Qed.

Theorem carry_compat_r : ∀ x y z j,
  (∀ i, x .[ i] = y .[ i])
  → carry y z j = carry x z j.
Proof.
intros x y z j Hxy.
unfold carry; intros.
remember (fst_same y z (S j)) as s1 eqn:Hs1 .
remember (fst_same x z (S j)) as s2 eqn:Hs2 .
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
   destruct z .[ S (j + di1)]; discriminate H.

   apply Nat.nlt_ge in H1.
   destruct (lt_dec di2 di1) as [H2| H2].
    remember H2 as H; clear HeqH.
    apply Hn1 in H.
    rewrite <- Hxy, Hs2 in H.
    destruct z .[ S (j + di2)]; discriminate H.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H1; auto.

  rewrite <- Hxy, Hs2 in Hs1.
  destruct z .[ S (j + di1)]; discriminate Hs1.

 destruct s2 as [di2| ]; auto.
 destruct Hs2 as (Hn2, Hs2).
 rewrite Hxy, Hs1 in Hs2.
 destruct z .[ S (j + di2)]; discriminate Hs2.
Qed.

Theorem rm_add_i_compat_r : ∀ x y z j,
  (∀ i, x .[ i] = y .[ i])
  → rm_add_i y z j = rm_add_i x z j.
Proof.
intros x y z j Hxy.
unfold rm_add_i.
rewrite Hxy; f_equal.
apply carry_compat_r; assumption.
Qed.

Theorem rm_norm_eq_eq : ∀ x0 y0 x y,
  x = (x0 + 0)%rm
  → y = (y0 + 0)%rm
  → (x = y)%rm
  → ∀ i, x .[ i] = y .[ i].
Proof.
intros x0 y0 x y Ha Hb Hxy i.
unfold rm_eq in Hxy; simpl in Hxy.
pose proof (Hxy i) as Hi.
unfold rm_add_i, carry in Hi.
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

  exfalso; revert Hs2; rewrite Hb; apply not_rm_add_0_inf_1.

 exfalso; revert Hs1; rewrite Ha; apply not_rm_add_0_inf_1.
Qed.

Theorem carry_norm_eq_compat_r : ∀ x0 y0 x y z n,
  x = (x0 + 0)%rm
  → y = (y0 + 0)%rm
  → (x = y)%rm
  → carry (x + z) 0 n = carry (y + z) 0 n.
Proof.
intros x0 y0 x y z n Ha Hb Hxy.
apply carry_compat_r; simpl.
intros; apply rm_add_i_compat_r.
eapply rm_norm_eq_eq; eassumption.
Qed.

Theorem rm_norm_eq_compat_r : ∀ x0 y0 x y z,
  x = (x0 + 0)%rm
  → y = (y0 + 0)%rm
  → (x = y)%rm
  → (x + z = y + z)%rm.
Proof.
intros x0 y0 x y z Ha Hb Hxy.
unfold rm_eq; simpl; intros i.
unfold rm_add_i; simpl.
do 2 rewrite xorb_false_r; f_equal.
 apply rm_add_i_compat_r.
 intros j; symmetry.
 eapply rm_norm_eq_eq; eassumption.

 eapply carry_norm_eq_compat_r; eassumption.
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
  remember x .[ i] as ai eqn:Hai .
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
 remember x .[ i] as ai eqn:Hai .
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
 remember x .[ i] as ai eqn:Hai .
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
 remember x .[ i] as ai eqn:Hai .
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
  (∀ dj : nat, dj < di2 → rm_add_i x 0 (S i + dj) = negb y .[ S i + dj])
  → (∀ dj : nat, x .[ S (S i) + di2 + dj] = true)
  → (∀ dj : nat, dj < di3 → x .[ S i + dj] = negb y .[ S i + dj])
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
   unfold rm_add_i, carry in H.
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

Theorem rm_add_inf_true_eq_if : ∀ x y i,
  (∀ di, rm_add_i x y (i + di) = true)
  → x.[i] = y.[i]
  → (∀ di, x.[i + S di] = true) ∧
    (∀ di, y.[i + S di] = true).
Proof.
intros x y i Hdi Hxy.
apply forall_and_distr; intros di.
induction di.
 rewrite Nat.add_1_r.
 pose proof (Hdi 0) as H.
 unfold rm_add_i, carry in H.
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
   unfold rm_add_i, carry in H.
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
  unfold rm_add_i, carry in H.
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
 unfold rm_add_i, carry in H.
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
   unfold rm_add_i, carry in H.
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
  unfold rm_add_i, carry in H.
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
  destruct y .[ ssi + di + S di2]; discriminate Hb2.
Qed.

Theorem rm_add_inf_true_neq_if : ∀ x y i,
  (∀ di, rm_add_i x y (i + di) = true)
  → x.[i] = negb y.[i]
  → ∃ j,
    i < j ∧
    (∀ di, i + di < j → x.[i + di] = negb y.[i + di]) ∧
    x.[j] = false ∧ y.[j] = false ∧
    (∀ di, x.[j + S di] = true) ∧
    (∀ di, y.[j + S di] = true).
Proof.
intros x y i Hdi Hxy.
pose proof (Hdi 0) as H.
rewrite Nat.add_0_r in H.
unfold rm_add_i, carry in H.
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
   unfold rm_add_i, carry in H.
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
      unfold rm_add_i, carry in H.
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
        unfold rm_add_i, carry in H.
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
       unfold rm_add_i, carry in H.
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
        destruct y .[ ssssi + di1 + di + di4]; discriminate H.

        rewrite xorb_true_r in H.
        apply negb_true_iff in H.
        apply xorb_eq in H.
        rename H into Hxy1.
        pose proof (Hs3 0) as H.
        rewrite Nat.add_0_r in H.
        rewrite Hxy1 in H.
        destruct y .[ sssi + di1 + di]; discriminate H.

     rename H into Ha2.
     rewrite Ha2 in Hs2; symmetry in Hs2.
     pose proof (Hn2 0 (Nat.lt_0_succ di2)) as H.
     rewrite Nat.add_0_r in H.
     rename H into Hxy1.
     pose proof (Hdi (S (S di1))) as H.
     do 2 rewrite Nat.add_succ_r in H.
     do 2 rewrite <- Nat.add_succ_l in H.
     rewrite <- Heqsi, <- Heqssi in H.
     unfold rm_add_i, carry in H.
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
    unfold rm_add_i, carry in H.
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

Theorem nat_sub_add_r : ∀ x y z,
  x < y
  → z = y - S x
  → y = x + S z.
Proof.
intros x y z Hxy Hc; subst z.
rewrite <- Nat.sub_succ_l; [ simpl | assumption ].
rewrite Nat.add_sub_assoc; [ idtac | apply Nat.lt_le_incl; assumption ].
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Theorem rm_add_inf_true_if : ∀ x y i,
  (∀ di, rm_add_i x y (i + di) = true)
  → ∃ j,
    (∀ dj, x.[i+j+dj] = true) ∧
    (∀ dj, y.[i+j+dj] = true) ∧
    (0 < j → x.[i+pred j] = false) ∧
    (0 < j → y.[i+pred j] = false) ∧
    (fst_same x y i = Some (pred j)).
Proof.
intros x y i Hdi.
destruct (bool_dec x .[ i] y .[ i]) as [H1| H1].
 remember Hdi as H; clear HeqH.
 apply rm_add_inf_true_eq_if in H; auto.
 destruct H as (Ha, Hb).
 remember x .[ i] as a eqn:H2 .
 symmetry in H1, H2.
 destruct a.
  exists 0.
  rewrite Nat.add_0_r.
  split.
   intros dj; destruct dj; [ idtac | apply Ha ].
   rewrite Nat.add_0_r; assumption.

   split.
    intros dj; destruct dj; [ idtac | apply Hb ].
    rewrite Nat.add_0_r; assumption.

    split; [ intros H; exfalso; revert H; apply Nat.nlt_0_r | idtac ].
    split; [ intros H; exfalso; revert H; apply Nat.nlt_0_r | idtac ].
    apply fst_same_iff; simpl.
    rewrite Nat.add_0_r.
    split; [ idtac | rewrite H1, H2; reflexivity ].
    intros dj H; exfalso; revert H; apply Nat.nlt_0_r.

  exists 1.
  rewrite Nat.add_1_r; simpl.
  rewrite Nat.add_0_r.
  split; [ intros dj; rewrite <- Nat.add_succ_r; apply Ha | idtac ].
  split; [ intros dj; rewrite <- Nat.add_succ_r; apply Hb | idtac ].
  split; [ intros H; assumption | idtac ].
  split; [ intros H; assumption | idtac ].
  apply fst_same_iff; simpl.
  rewrite Nat.add_0_r.
  split; [ idtac | rewrite H1, H2; reflexivity ].
  intros dj H; exfalso; revert H; apply Nat.nlt_0_r.

 apply neq_negb in H1.
 remember Hdi as H; clear HeqH.
 apply rm_add_inf_true_neq_if in H; auto.
 destruct H as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 remember (j - S i) as k eqn:Hk .
 apply nat_sub_add_r in Hk; [ idtac | assumption ].
 subst j; clear Hij; rename k into j.
 exists (S (S j)).
 split; [ intros dj | idtac ].
  rewrite Nat.add_succ_r; simpl.
  rewrite <- Nat.add_assoc, <- Nat.add_succ_r.
  rewrite <- Nat.add_succ_r, Nat.add_assoc.
  apply Hat.

  split; [ intros dj | idtac ].
   rewrite Nat.add_succ_r; simpl.
   rewrite <- Nat.add_assoc, <- Nat.add_succ_r.
   rewrite <- Nat.add_succ_r, Nat.add_assoc.
   apply Hbt.

   split; [ intros H; simpl; assumption | idtac ].
   split; [ intros H; simpl; assumption | idtac ].
   apply fst_same_iff; simpl.
   split; [ intros dj Hdj | idtac ].
    apply Hni, Nat.add_lt_mono_l; assumption.

    rewrite Ha, Hb; reflexivity.
Qed.

Theorem lt_add_sub_lt_r : ∀ a y z d,
  a < y + z
  → d < z
  → a - y < z.
Proof.
intros a y z d Ha Hdc.
revert y z Ha Hdc.
induction a; intros.
 simpl.
 eapply le_lt_trans; [ apply Nat.le_0_l | eassumption ].

 destruct y; [ rewrite Nat.sub_0_r; assumption | simpl ].
 simpl in Ha.
 apply Nat.succ_lt_mono in Ha.
 apply IHa; assumption.
Qed.

Theorem lt_add_sub_lt_l : ∀ a y z,
  a < y + z
  → y < S a
  → a - y < z.
Proof.
intros a y z Ha Hb.
revert y z Ha Hb.
induction a; intros.
 apply Nat.lt_1_r in Hb; subst y; assumption.

 destruct y; [ rewrite Nat.sub_0_r; assumption | simpl ].
 simpl in Ha.
 apply Nat.succ_lt_mono in Ha.
 apply Nat.succ_lt_mono in Hb.
 apply IHa; assumption.
Qed.

Theorem rm_add_add_0_l_when_lhs_has_relay : ∀ x y i di1,
  fst_same (x + 0%rm) y (S i) = Some di1
  → rm_add_i (x + 0%rm) y i = rm_add_i x y i.
Proof.
intros x y i di1 Hs1.
unfold rm_add_i, carry at 1; remember (S i) as si; simpl.
rewrite Hs1.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Hs1).
rewrite Hs1.
unfold rm_add_i, carry; rewrite <- Heqsi; simpl.
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
  unfold rm_add_i, carry in Hs1.
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
    destruct y .[ si + di1]; discriminate H.

    apply Nat.nlt_ge in H1.
    destruct (lt_dec di2 di1) as [H2| H2].
     remember H2 as H; clear HeqH.
     apply Hn1 in H.
     unfold rm_add_i, carry in H.
     rewrite <- Nat.add_succ_l, <- Heqssi in H.
     simpl in H.
     remember (fst_same x 0 (ssi + di2)) as s5 eqn:Hs5 .
     symmetry in Hs5.
     apply fst_same_iff in Hs5; simpl in Hs5.
     destruct s5 as [di5| ].
      destruct Hs5 as (Hn5, Hs5).
      rewrite xorb_false_r, Hs2, Hs5, xorb_false_r in H.
      destruct y .[ si + di2]; discriminate H.

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
    unfold rm_add_i, carry in H.
    rewrite <- Nat.add_succ_l, <- Heqssi in H.
    simpl in H.
    remember (fst_same x 0 (ssi + di2)) as s5 eqn:Hs5 .
    symmetry in Hs5.
    apply fst_same_iff in Hs5; simpl in Hs5.
    destruct s5 as [di5| ].
     destruct Hs5 as (Hn5, Hs5).
     rewrite xorb_false_r, Hs2, Hs5, xorb_false_r in H.
     destruct y .[ si + di2]; discriminate H.

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
      destruct (bool_dec x .[ si + di2] false) as [H4| H4].
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
        unfold rm_add_i, carry in H.
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
           unfold rm_add_i, carry in H.
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
     remember y .[ si + di1] as bi eqn:Hbi .
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
  unfold rm_add_i, carry; rewrite <- Nat.add_succ_l.
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
  unfold rm_add_i, carry.
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
     unfold rm_add_i, carry in Hb.
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
     unfold rm_add_i, carry in Hs3.
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
   unfold rm_add_i, carry in Hs1.
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
    destruct y .[ si + di1]; discriminate Hs1.

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
      unfold rm_add_i, carry in H.
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
       destruct x .[ si + di3]; discriminate H.

      apply Nat.nlt_ge in H2.
      apply Nat.le_antisymm in H2; auto.
      subst di3; assumption.

  rewrite xorb_true_r, <- Hs2.
  apply Hs3.
Qed.

Theorem rm_add_add_0_l_when_lhs_has_no_relay : ∀ x y i dj2 dj5,
  fst_same ((x + 0)%rm + y) 0 (S i) = Some dj2
  → fst_same (x + y) 0 (S i) = Some dj5
  → fst_same (x + 0%rm) y (S i) = None
  → rm_add_i (x + 0%rm) y i = rm_add_i x y i.
Proof.
intros x y i dj2 dj5 Ps2 Ps5 Hs1.
remember (S i) as si.
unfold rm_add_i, carry.
rewrite <- Heqsi; simpl.
rewrite Hs1.
unfold rm_add_i, carry at 1; rewrite <- Heqsi; simpl.
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
   unfold rm_add_i, carry in H.
   rewrite <- Nat.add_succ_l in H.
   remember (S si) as ssi; simpl in H.
   rewrite xorb_false_r in H.
   remember (fst_same x 0 (ssi + di2)) as s4 eqn:Hs4 .
   symmetry in Hs4.
   apply fst_same_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4); rewrite Hs4, xorb_false_r in H.
    rewrite Hs2 in H.
    destruct y .[ si + di2]; discriminate H.

    clear H.
    apply not_false_iff_true.
    intros Ha.
    destruct dj5.
     rewrite Nat.add_0_r in Ps5.
     unfold rm_add_i, carry in Ps5.
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
        destruct y .[ ssi + dj6]; discriminate H2.

        apply Nat.nlt_ge in H2.
        destruct (lt_dec di2 (S dj6)) as [H3| H3].
         destruct di2.
          rewrite Nat.add_0_r in Hs4.
          rewrite Nat.add_0_r in Hs2.
          rewrite <- Hs2, Hs4 in Ps5.
          rewrite xorb_true_r in Ps5.
          apply negb_false_iff in Ps5.
          destruct x .[ si]; discriminate Ps5.

          apply Nat.succ_lt_mono in H3.
          apply Pn6 in H3.
          rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs2.
          rewrite <- Heqssi, H3 in Hs2.
          destruct y .[ ssi + di2]; discriminate Hs2.

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
       destruct y .[ si]; discriminate Ps5.

      destruct di2.
       rewrite Nat.add_0_r in Hs2.
       rewrite <- Hs2 in Ps5.
       destruct x .[ si]; discriminate Ps5.

       rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs2.
       rewrite <- Heqssi in Hs2.
       rewrite Ps6 in Hs2.
       destruct y .[ ssi + di2]; discriminate Hs2.

     assert (S dj5 = di2) as H.
      destruct (lt_dec (S dj5) di2) as [H2| H2].
       unfold rm_add_i, carry in Ps5.
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
          destruct y .[ ssi + S dj5 + di6]; discriminate H3.

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
           destruct y .[ si + di2]; discriminate H.

           apply Nat.nlt_ge in H4.
           apply Nat.le_antisymm; auto.

         rewrite <- H in Ha.
         rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in Ha.
         rewrite Nat.add_assoc in Ha.
         rewrite Ha, xorb_false_r in Ps5.
         apply Hn2 in H2.
         rewrite H2 in Ps5.
         destruct y .[ si + S dj5]; discriminate Ps5.

        pose proof (Ps6 (di2 - S (S dj5))) as H.
        rewrite Nat.add_sub_assoc in H; auto.
        rewrite Heqssi in H.
        rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
        rewrite Nat.add_shuffle0, Nat.add_sub in H.
        rewrite Hs2 in H.
        destruct y .[ si + di2]; discriminate H.

       apply Nat.nlt_ge in H2.
       destruct (lt_dec di2 (S dj5)) as [H3| H3].
        unfold rm_add_i, carry in Ps5.
        rewrite <- Nat.add_succ_l, <- Heqssi in Ps5.
        remember (fst_same x y (ssi + S dj5)) as s6 eqn:Ps6 .
        symmetry in Ps6.
        apply fst_same_iff in Ps6; simpl in Ps6.
        destruct s6 as [dj6| ].
         destruct Ps6 as (Pn6, Ps6).
         pose proof (Hs1 (S dj5 + dj6)) as H.
         rewrite Nat.add_assoc in H.
         unfold rm_add_i, carry in H.
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
          unfold rm_add_i, carry in H.
          do 2 rewrite <- Nat.add_succ_l in H.
          remember (S ssi) as sssi; simpl in H.
          rewrite xorb_false_r in H.
          remember (fst_same x 0 (sssi + S dj5 + dj6)) as s8 eqn:Ps8 .
          symmetry in Ps8.
          apply fst_same_iff in Ps8; simpl in Ps8.
          destruct s8 as [dj8| ].
           destruct Ps8 as (Pn8, Ps8); rewrite Ps8, xorb_false_r in H.
           rewrite Ps6 in H.
           destruct y .[ ssi + S dj5 + dj6]; discriminate H.

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
           destruct x .[ si + S dj5]; discriminate Ps5.

           rename H into Hyx.
           pose proof (Pn6 dj6 (Nat.lt_succ_diag_r dj6)) as H.
           rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hyx.
           rewrite <- Nat.add_succ_l in Hyx.
           rewrite <- Heqssi in Hyx.
           rewrite Hyx in H.
           destruct x .[ ssi + S dj5 + dj6]; discriminate H.

         pose proof (Hs1 (S dj5)) as H.
         unfold rm_add_i, carry in H.
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
          destruct x .[ si + S dj5]; discriminate Ps5.

        apply Nat.nlt_ge in H3.
        apply Nat.le_antisymm; auto.

      rewrite H in Ps5.
      unfold rm_add_i, carry in Ps5.
      rewrite <- Nat.add_succ_l, <- Heqssi in Ps5.
      remember (fst_same x y (ssi + di2)) as s6 eqn:Ps6 .
      symmetry in Ps6.
      apply fst_same_iff in Ps6; simpl in Ps6.
      destruct s6 as [dj6| ].
       rewrite Hs4, Hs2, xorb_true_r in Ps5.
       destruct y .[ si + di2]; discriminate Ps5.

       rewrite Hs2, xorb_true_r in Ps5.
       destruct y .[ si + di2]; discriminate Ps5.

  symmetry; simpl.
  assert (∀ dj, y .[ si + dj] = true) as Hb.
   intros dj.
   apply negb_false_iff.
   rewrite <- Hs1.
   unfold rm_add_i, carry.
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
    unfold rm_add_i, carry in Ps5.
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
  unfold rm_add_i, carry in H.
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
   destruct x .[ si]; discriminate H1.
Qed.

Theorem rm_add_add_0_l_when_both_hs_has_relay : ∀ x y i dj2 dj5,
  fst_same ((x + 0)%rm + y) 0 (S i) = Some dj2
  → fst_same (x + y) 0 (S i) = Some dj5
  → rm_add_i ((x + 0)%rm + y) 0 i = rm_add_i (x + y) 0 i.
Proof.
intros x y i dj2 dj5 Ps2 Ps5.
unfold rm_add_i, carry.
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
remember (fst_same (x + 0%rm) y (S i)) as s1 eqn:Hs1 .
symmetry in Hs1.
subst si.
destruct s1 as [di1| ].
 eapply rm_add_add_0_l_when_lhs_has_relay; eauto .

 eapply rm_add_add_0_l_when_lhs_has_no_relay; eauto .
Qed.

Theorem rm_add_add_0_l_when_relay : ∀ x y i di1,
  fst_same (x + 0%rm) y (S i) = Some di1
  → fst_same (x + y) 0 (S i) ≠ None.
Proof.
intros x y i di1 Hs1 Hs5.
apply rm_add_add_0_l_when_lhs_has_relay in Hs1.
remember (S i) as si.
unfold rm_add_i, carry in Hs1.
rewrite <- Heqsi in Hs1; simpl in Hs1.
unfold rm_add_i in Hs1 at 1.
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
  apply rm_add_inf_true_eq_if in Hs5; auto.
  destruct Hs5 as (Has, Hbs).
  remember (fst_same x 0 si) as s3 eqn:Hs3 .
  apply fst_same_sym_iff in Hs3; simpl in Hs3.
  destruct s3 as [di3| ].
   destruct Hs3 as (Hn3, Hs3).
   rewrite Hs3, xorb_false_r in Hs1.
   remember (fst_same (x + 0%rm) y si) as s4 eqn:Hs4 .
   apply fst_same_sym_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4).
    unfold rm_add_i, carry in Hs1.
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
     unfold rm_add_i, carry in Hs4.
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

   remember (fst_same (x + 0%rm) y si) as s4 eqn:Hs4 .
   apply fst_same_sym_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4); rewrite Hs4 in Hs1.
    unfold rm_add_i, carry in Hs4.
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
    destruct x .[ i], y .[ i]; discriminate Hs1.

  pose proof (Hn8 0 (Nat.lt_0_succ di8)) as H.
  rewrite Nat.add_0_r in H.
  apply rm_add_inf_true_neq_if in Hs5; auto.
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
    destruct y .[ si + S di8]; discriminate H.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H1; auto; clear H2.
    rewrite <- H1, Ha, xorb_false_r in Hs1.
    remember (fst_same x 0 si) as s3 eqn:Hs3 .
    apply fst_same_sym_iff in Hs3; simpl in Hs3.
    destruct s3 as [di3| ].
     destruct Hs3 as (Hn3, Hs3); rewrite Hs3, xorb_false_r in Hs1.
     remember (fst_same (x + 0%rm) y si) as s4 eqn:Hs4 .
     apply fst_same_sym_iff in Hs4; simpl in Hs4.
     destruct s4 as [di4| ].
      destruct Hs4 as (Hn4, Hs4); rewrite Hs4 in Hs1.
      unfold rm_add_i, carry in Hs4.
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
         destruct y .[ si + di4]; discriminate H.

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

      destruct (xorb x .[ i] y .[ i]); discriminate Hs1.

     pose proof (Hs3 (j - si)) as H.
     apply Nat.lt_le_incl in Hij.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_comm, Nat.add_sub in H.
     rewrite Ha in H; discriminate H.

 pose proof (Hs8 0) as H; rewrite Nat.add_0_r in H.
 apply rm_add_inf_true_neq_if in Hs5; auto; clear H.
 destruct Hs5 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 pose proof (Hs8 (j - si)) as H.
 apply Nat.lt_le_incl in Hij.
 rewrite Nat.add_sub_assoc in H; auto.
 rewrite Nat.add_comm, Nat.add_sub in H.
 rewrite Ha, Hb in H; discriminate H.
Qed.

Theorem rm_add_add_0_l_when_no_relay : ∀ x y i,
  fst_same (x + 0%rm) y (S i) = None
  → fst_same (x + y) 0 (S i) = None
  → rm_add_i (x + 0%rm) y i = negb (rm_add_i x y i).
Proof.
intros x y i Hs1 Hs5.
unfold rm_add_i, carry.
remember (S i) as si; simpl.
rewrite Hs1.
rewrite negb_xorb_l, negb_xorb_r.
rewrite xorb_true_r, negb_xorb_r.
unfold rm_add_i, carry.
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
  unfold rm_add_i, carry in H.
  remember (S si) as ssi; simpl in H.
  rewrite xorb_false_r in H.
  remember (fst_same x 0 ssi) as s6 eqn:Hs6 .
  apply fst_same_sym_iff in Hs6; simpl in Hs6.
  destruct s6 as [di6| ].
   destruct Hs6 as (Hn6, Hs6); rewrite Hs6, xorb_false_r in H.
   apply rm_add_inf_true_neq_if in Hs5; auto.
   destruct Hs5 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   rename H into Hxy.
   destruct (lt_dec (si + di4) j) as [H1| H1].
    remember H1 as H; clear HeqH.
    apply Hni in H.
    rewrite Hs4 in H.
    destruct y .[ si + di4]; discriminate H.

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
   apply rm_add_inf_true_eq_if in Hs5; auto.
   destruct Hs5 as (Hat, Hbt).
   destruct di4.
    destruct di3; [ assumption | idtac ].
    rewrite Hat in Hs3; discriminate Hs3.

    rename H into Hxy.
    pose proof (Hn4 0 (Nat.lt_0_succ di4)) as H.
    rewrite Nat.add_0_r, Hxy in H.
    destruct y .[ si]; discriminate H.

  pose proof (Hs5 0) as H.
  rewrite Nat.add_0_r in H.
  unfold rm_add_i, carry in H.
  remember (S si) as ssi; simpl in H.
  remember (fst_same x y ssi) as s6 eqn:Hs6 .
  apply fst_same_sym_iff in Hs6; simpl in Hs6.
  destruct s6 as [di6| ].
   destruct Hs6 as (Hn6, Hs6).
   rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Hs6.
   rewrite Hs4 in Hs6.
   destruct y .[ si + S di6]; discriminate Hs6.

   pose proof (Hs4 0) as H1.
   rewrite Nat.add_0_r in H1.
   rewrite H1 in H.
   rewrite negb_xorb_diag_l in H.
   discriminate H.

 destruct (fst_same x y si) as [di| ]; [ idtac | reflexivity ].
 rewrite Hs3; reflexivity.
Qed.

Theorem rm_add_add_0_l_when_rhs_has_no_relay : ∀ x y i di2,
  fst_same ((x + 0)%rm + y) 0 (S i) = Some di2
  → fst_same (x + y) 0 (S i) = None
  → rm_add_i ((x + 0)%rm + y) 0 i = rm_add_i (x + y) 0 i.
Proof.
intros x y i di2 Hs2 Hs5.
unfold rm_add_i, carry.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
rewrite Hs2, Hs5.
remember Hs2 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, H); rewrite H; clear H.
rewrite xorb_false_r, xorb_true_r.
remember (fst_same (x + 0%rm) y (S i)) as s1 eqn:Hs1 .
symmetry in Hs1; subst si.
destruct s1 as [di1| ].
 exfalso.
 eapply rm_add_add_0_l_when_relay; eauto .

 eapply rm_add_add_0_l_when_no_relay; eauto .
Qed.

Theorem rm_add_add_0_r_not_without_relay : ∀ x y i,
  fst_same ((x + 0)%rm + y) 0 (S i) ≠ None.
Proof.
intros x y i Hs2.
remember (S i) as si.
apply fst_same_iff in Hs2; simpl in Hs2.
destruct (bool_dec ((x + 0)%rm) .[ si] y .[ si]) as [H1| H1].
 apply rm_add_inf_true_eq_if in Hs2; auto.
 simpl in Hs2, H1.
 destruct Hs2 as (Hn2, Hs2).
 eapply not_rm_add_0_inf_1_succ; eauto .

 apply neq_negb in H1.
 apply rm_add_inf_true_neq_if in Hs2; auto.
 simpl in Hs2.
 destruct Hs2 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 eapply not_rm_add_0_inf_1_succ; eauto .
Qed.

(* perhaps could be proved if associativity proved before;
   in that case, that would be very simple instead of these
   big lemmas before *)
Theorem rm_add_add_0_r : ∀ x y, (x + 0 + y = x + y)%rm.
Proof.
intros x y.
unfold rm_eq; intros i; simpl.
remember (fst_same ((x + 0)%rm + y) 0 (S i)) as s2 eqn:Hs2 .
remember (fst_same (x + y) 0 (S i)) as s5 eqn:Hs5 .
symmetry in Hs2, Hs5.
destruct s2 as [di2| ].
 destruct s5 as [di5| ].
  eapply rm_add_add_0_l_when_both_hs_has_relay; eauto .

  eapply rm_add_add_0_l_when_rhs_has_no_relay; eauto .

 exfalso; revert Hs2.
 eapply rm_add_add_0_r_not_without_relay; eauto .
Qed.

Theorem rm_add_compat_r : ∀ x y z, (x = y)%rm → (x + z = y + z)%rm.
Proof.
intros x y z Hxy.
remember (x + 0)%rm as a1.
remember (y + 0)%rm as b1.
remember Heqa1 as H; clear HeqH.
eapply rm_norm_eq_compat_r with (y0 := y) (z := z) in H; eauto .
 subst a1 b1.
 do 2 rewrite rm_add_add_0_r in H; assumption.

 subst a1 b1.
 do 2 rewrite rm_add_0_r; assumption.
Qed.

Theorem rm_add_compat : ∀ x y z d,
  (x = y)%rm
  → (z = d)%rm
  → (x + z = y + d)%rm.
Proof.
intros x y z d Hxy Hcd.
transitivity (x + d)%rm; [ idtac | apply rm_add_compat_r; assumption ].
rewrite rm_add_comm; symmetry.
rewrite rm_add_comm; symmetry.
apply rm_add_compat_r; assumption.
Qed.

Add Parametric Morphism : rm_add
  with signature rm_eq ==> rm_eq ==> rm_eq
  as rm_add_morph.
Proof.
intros x y Hxy z d Hcd.
apply rm_add_compat; assumption.
Qed.

Theorem rm_add_opp_r : ∀ x, (x - x = 0)%rm.
Proof.
intros x.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry.
remember (S i) as si; simpl.
rewrite xorb_false_r.
remember (fst_same 0 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ]; [ clear di1 Hs1 | discriminate Hs1; auto ].
remember (fst_same (x - x) 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); rewrite Hs1, xorb_false_r.
 unfold rm_add_i, carry.
 rewrite <- Heqsi; simpl.
 remember (fst_same x (- x) si) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 rewrite <- negb_xorb_r, negb_xorb_l, negb_xorb_diag_l.
 destruct s2 as [di2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Hs2).
 destruct x .[ si + di2]; discriminate Hs2.

 destruct (bool_dec x .[ si] (negb x .[ si])) as [H1| H1].
  destruct x .[ si]; discriminate H1.

  apply neq_negb in H1.
  apply rm_add_inf_true_neq_if in Hs1; auto.
  simpl in Hs1.
  destruct Hs1 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
  rewrite Ha in Hb; discriminate Hb.
Qed.

Theorem rm_zerop : ∀ x, {(x = 0)%rm} + {(x ≠ 0)%rm}.
Proof.
intros x.
remember (fst_same (x + 0%rm) rm_zero' 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Hs).
 right; intros H.
 unfold rm_eq in H; simpl in H.
 pose proof (H di) as HH.
 rewrite Hs in HH; symmetry in HH.
 unfold rm_add_i in HH; simpl in HH.
 unfold carry in HH; simpl in HH.
 remember (fst_same 0%rm 0%rm (S di)) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [di1| ]; [ idtac | discriminate Hs1; assumption ].
 discriminate HH.

 left.
 unfold rm_eq; intros i; simpl.
 rewrite Hs.
 unfold rm_add_i; simpl.
 unfold carry; simpl.
 remember (fst_same 0 0 (S i)) as s1 eqn:Hs1 .
 destruct s1; [ reflexivity | idtac ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 discriminate Hs1; assumption.
Qed.

Theorem fst_same_diag : ∀ x i, fst_same x x i = Some 0.
Proof.
intros x i.
apply fst_same_iff; simpl.
split; [ idtac | reflexivity ].
intros dj Hdj; exfalso.
revert Hdj; apply Nat.nlt_0_r.
Qed.

Theorem carry_diag : ∀ x i, carry x x i = x.[S i].
Proof.
intros x i.
unfold carry; simpl.
rewrite fst_same_diag, Nat.add_0_r; reflexivity.
Qed.

(* requires associativity
Axiom rm_add_assoc : ∀ x y z, (x+(y+z) = (x+y)+z)%rm.
Theorem rm_dec : ∀ x y, {(x = y)%rm} + {(x ≠ y)%rm}.
Proof.
intros x y.
destruct (rm_zerop (x - y)%rm) as [Hxy| Hxy].
 left.
 rewrite rm_add_comm in Hxy.
 eapply rm_add_compat with (x := y) in Hxy; [ idtac | reflexivity ].
 rewrite rm_add_assoc in Hxy.
 rewrite rm_add_opp_r in Hxy.
 rewrite rm_add_comm in Hxy.
 do 2 rewrite rm_add_0_r in Hxy.
 assumption.

 right.
 intros H; apply Hxy; rewrite H.
 apply rm_add_opp_r.
Qed.

Theorem rm_decidxyle : ∀ x y, Decidxyle.decidxyle (x = y)%rm.
Proof.
intros x y.
destruct (rm_dec x y); [ left | right ]; assumption.
*)

(* associativity *)

Theorem fold_rm_add_i : ∀ x y i, rm_add_i x y i = ((x+y)%rm).[i].
Proof. reflexivity. Qed.

Theorem nat_compare_add_succ : ∀ i j, nat_compare i (i + S j) = Lt.
Proof.
intros i j.
apply nat_compare_lt.
apply Nat.lt_sub_lt_add_l.
rewrite Nat.sub_diag.
apply Nat.lt_0_succ.
Qed.

Theorem same_fst_same : ∀ x y i di dj,
  fst_same x y i = Some (di + dj)
  → fst_same x y (i + di) = Some dj.
Proof.
intros x y i di dj Hs.
apply fst_same_iff in Hs; simpl in Hs.
destruct Hs as (Hn, Hs).
apply fst_same_iff.
split.
 intros dk Hdk.
 apply Nat.add_lt_mono_l with (p := di) in Hdk.
 apply Hn in Hdk.
 rewrite Nat.add_assoc in Hdk; assumption.

 rewrite Nat.add_assoc in Hs; assumption.
Qed.

Lemma lt_add_r : ∀ x y,
  0 < y
  → x < x + y.
Proof.
intros x y Hb.
apply Nat.lt_sub_lt_add_l.
rewrite Nat.sub_diag.
assumption.
Qed.

Theorem fst_same_before : ∀ x y i dk dl di4,
  fst_same x y (S i) = Some dk
  → dl < dk
  → fst_same x y (S (S (i + dl))) = Some di4
  → di4 = dk - S dl.
Proof.
intros x y i dk dl di4 Hsk Hdl Hs4.
destruct (lt_dec di4 (dk - S dl)) as [H2| H2].
 apply Nat.lt_add_lt_sub_r in H2.
 apply fst_same_iff in Hsk; simpl in Hsk.
 destruct Hsk as (Hnk, Hsk).
 apply Hnk in H2.
 apply fst_same_iff in Hs4; simpl in Hs4.
 destruct Hs4 as (Hn4, Hs4).
 rewrite Nat.add_assoc, Nat.add_shuffle0 in H2.
 rewrite Nat.add_succ_r in H2; simpl in H2.
 rewrite Hs4 in H2.
 destruct y .[ S (S (i + dl + di4))]; discriminate H2.

 apply Nat.nlt_ge in H2.
 destruct (lt_dec (dk - S dl) di4) as [H3| H3].
  apply fst_same_iff in Hs4.
  destruct Hs4 as (Hn4, Hs4).
  apply Hn4 in H3.
  apply fst_same_iff in Hsk.
  destruct Hsk as (Hnk, Hsk).
  rewrite Nat.add_sub_assoc in H3; auto.
  rewrite <- Nat.add_succ_r in H3.
  rewrite <- Nat.add_succ_l in H3.
  rewrite Nat.add_shuffle0, Nat.add_sub in H3.
  rewrite Hsk in H3.
  destruct y .[ S i + dk]; discriminate H3.

  apply Nat.nlt_ge in H3.
  apply Nat.le_antisymm; assumption.
Qed.

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

Theorem not_add_norm_inf_1 : ∀ x y i,
  ¬ (∀ dj : nat, rm_add_i (x + 0%rm) (y + 0%rm) (i + dj) = true).
Proof.
intros x y i Hxy.
destruct (bool_dec ((x + 0)%rm) .[ i] ((y + 0)%rm) .[ i]) as [H1| H1].
 apply rm_add_inf_true_eq_if in Hxy; auto.
 destruct Hxy as (H, _); simpl in H.
 apply not_rm_add_0_inf_1_succ in H; auto.

 apply neq_negb in H1.
 apply rm_add_inf_true_neq_if in Hxy; auto.
 simpl in Hxy.
 destruct Hxy as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 apply not_rm_add_0_inf_1_succ in Hat; auto.
Qed.

Theorem rm_add_i_norm_norm : ∀ x y i,
  rm_add_i ((x + 0)%rm + (y + 0)%rm) 0 i = rm_add_i (x + 0%rm) (y + 0%rm) i.
Proof.
intros x y i.
unfold rm_add_i, carry at 1.
remember (S i) as si; simpl.
rewrite xorb_false_r.
remember (fst_same ((x + 0)%rm + (y + 0)%rm) 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); rewrite Hs1, xorb_false_r; reflexivity.

 apply not_add_norm_inf_1 in Hs1; contradiction.
Qed.

(* still proved as rm_add_inf_true_if!! *)
Theorem rm_add_inf_if : ∀ x y i,
  (∀ dj, rm_add_i x y (i + dj) = true)
  → ∃ j,
    i < j ∧
    (∀ di, x.[j + S di] = true) ∧
    (∀ di, y.[j + S di] = true).
Proof.
intros x y i Hj.
destruct (bool_dec x .[ i] y .[ i]) as [H1| H1].
 apply rm_add_inf_true_eq_if in Hj; auto.
 destruct Hj as (Ha, Hb).
 exists (S i).
 split; [ apply Nat.lt_succ_diag_r | idtac ].
 split; intros di; rewrite Nat.add_succ_l, <- Nat.add_succ_r.
   apply Ha.

   apply Hb.

 apply neq_negb in H1.
 apply rm_add_inf_true_neq_if in Hj; auto.
 destruct Hj as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 exists j.
 split; [ assumption | split; assumption ].
Qed.

Theorem carry_0_r_true_if : ∀ x i,
  carry x 0 i = true
  → id (∀ dj, x.[i + S dj] = true).
Proof.
intros x i H j.
unfold carry in H; simpl in H.
remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hs1 in H; discriminate H.

 rewrite Nat.add_succ_r; apply Hs1.
Qed.

(* trying to make x lemma for something used many times, but it does
   not seem to work properly *)
Theorem same_relays : ∀ di1 di2 f g,
  (∀ dj, dj < di1 → f dj = negb (g dj))
  → (∀ dj, dj < di2 → f dj = negb (g dj))
  → f di1 = g di1
  → f di2 = g di2
  → di1 = di2.
Proof.
intros di1 di2 f g Hdi1 Hdi2 Hf1 Hf2.
destruct (lt_dec di1 di2) as [H1| H1].
 apply Hdi2 in H1.
 rewrite Hf1 in H1.
 destruct (g di1); discriminate H1.

 apply Nat.nlt_ge in H1.
 destruct (lt_dec di2 di1) as [H2| H2].
  apply Hdi1 in H2.
  rewrite Hf2 in H2.
  destruct (g di2); discriminate H2.

  apply Nat.nlt_ge in H2.
  apply Nat.le_antisymm; assumption.
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

Theorem fst_same_in_range2 : ∀ x y i di dj s,
  fst_same x y i = Some dj
  → fst_same x y (i + di) = s
  → di ≤ dj
  → s = Some (dj - di).
Proof.
intros x y i di dj s Hdj Hdi Hdij.
eapply fst_same_in_range in Hdi; try eassumption.
 rewrite <- minus_plus_simpl_l_reverse in Hdi.
 assumption.

 split; [ apply Nat.le_add_r | idtac ].
 apply Nat.add_le_mono_l; assumption.
Qed.

Theorem carry_before_relay : ∀ x y i di,
  fst_same x y i = Some di
  → ∀ dj, dj < di → carry x y (i + dj) = x.[i + di].
Proof.
intros x y i di Hs dj Hdj.
remember x.[i+di] as a eqn:Ha; symmetry in Ha.
unfold carry; simpl.
remember (fst_same x y (S (i + dj))) as s2 eqn:Hs2 .
symmetry in Hs2.
assert (S (i + dj) ≤ i + di) as H by (apply Nat.add_lt_mono_l; auto).
eapply fst_same_in_range in Hs2; try eassumption; [ idtac | split; auto ].
 subst s2.
 rewrite <- Nat.add_succ_l, Nat.add_sub_assoc; auto.
 rewrite Nat.add_comm, Nat.add_sub; assumption.

 rewrite <- Nat.add_succ_r.
 apply Nat.le_add_r.
Qed.

Theorem carry_before_inf_relay : ∀ x y i,
  fst_same x y i = None
  → ∀ dj, carry x y (i + dj) = true.
Proof.
intros x y i Hs dj.
unfold carry; simpl.
remember (fst_same x y (S (i + dj))) as s2 eqn:Hs2 .
symmetry in Hs2.
apply fst_same_iff in Hs2; simpl in Hs2.
destruct s2 as [di2| ]; [ idtac | reflexivity ].
apply fst_same_iff in Hs; simpl in Hs.
destruct Hs2 as (_, Hs2).
rewrite <- Nat.add_assoc, <- Nat.add_succ_r in Hs2.
rewrite Hs in Hs2.
exfalso; revert Hs2; apply no_fixpoint_negb.
Qed.

Theorem sum_before_relay : ∀ x y i di a,
  fst_same x y i = Some di
  → x .[i + di] = a
  → ∀ dj, dj < di → rm_add_i x y (i + dj) = negb a.
Proof.
intros x y i di a Hs Ha dj Hdj.
unfold rm_add_i.
remember Hs as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hs1, Hn1).
remember Hdj as H; clear HeqH.
apply Hs1 in H.
rewrite H, negb_xorb_diag_l, xorb_true_l.
f_equal; erewrite carry_before_relay; try eassumption; reflexivity.
Qed.

Theorem carry_when_inf_1 : ∀ x y i j,
  (∀ di, x.[S (i + di)] = true)
  → i ≤ j
  → carry x y j = true.
Proof.
intros x y i j Hdi Hij.
unfold carry; simpl.
remember (fst_same x y (S j)) as s1 eqn:Hs1 .
destruct s1 as [di1| ]; [ idtac | reflexivity ].
apply Nat.sub_add in Hij.
rewrite Nat.add_comm in Hij.
rewrite <- Hij, <- Nat.add_assoc.
apply Hdi.
Qed.

Theorem carry_comm_l : ∀ x y z i,
  carry (x + y) z i = carry (y + x) z i.
Proof.
intros x y z i.
rewrite carry_compat_r with (x := (y + x)%rm); [ reflexivity | idtac ].
apply rm_add_i_comm.
Qed.

Theorem carry_assoc_l : ∀ x y z d i,
  carry ((x + y) + z)%rm d i = carry (z + (y + x))%rm d i.
Proof.
intros x y z d i.
apply carry_compat_r.
intros j; simpl.
rewrite rm_add_i_comm.
apply rm_add_i_compat_r, rm_add_i_comm.
Qed.

Theorem rm_add_assoc_norm : ∀ x y z,
  ((x + 0) + ((y + 0) + (z + 0)) = ((x + 0) + (y + 0)) + (z + 0))%rm
  → (x + (y + z) = (x + y) + z)%rm.
Proof.
intros x y z H.
do 3 rewrite rm_add_0_r in H; assumption.
Qed.

Theorem carry_sum_norm : ∀ x0 y0 x y i,
  x = (x0 + 0)%rm
  → y = (y0 + 0)%rm
  → carry (x + y)%rm 0 i = false.
Proof.
intros x0 y0 x y i Ha0 Hb0.
unfold carry; simpl.
remember (fst_same (x + y) 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); assumption.

 apply forall_add_succ_l in Hs1.
 apply rm_add_inf_if in Hs1.
 destruct Hs1 as (j, (Hij, (Haj, Hbj))).
 rewrite Ha0 in Haj; simpl in Haj.
 apply forall_add_succ_r in Haj.
 apply rm_add_inf_if in Haj.
 destruct Haj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem carry_sum_3_norm_assoc_l : ∀ z0 x y z i,
  z = (z0 + 0)%rm
  → carry ((x + y) + z)%rm 0 i = false.
Proof.
intros z0 x y z i Hc0.
unfold carry; simpl.
remember (fst_same ((x + y) + z)%rm 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); assumption.

 apply forall_add_succ_l in Hs1.
 apply rm_add_inf_if in Hs1.
 destruct Hs1 as (j, (Hij, (Haj, Hbj))).
 rewrite Hc0 in Hbj; simpl in Hbj.
 apply forall_add_succ_r in Hbj.
 apply rm_add_inf_if in Hbj.
 destruct Hbj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem carry_sum_3_norm_assoc_r : ∀ x0 x y z i,
  x = (x0 + 0)%rm
  → carry (x + (y + z))%rm 0 i = false.
Proof.
intros x0 x y z i Ha0.
unfold carry; simpl.
remember (fst_same (x + (y + z)%rm) 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); assumption.

 apply forall_add_succ_l in Hs1.
 apply rm_add_inf_if in Hs1.
 destruct Hs1 as (j, (Hij, (Haj, Hbj))).
 rewrite Ha0 in Haj; simpl in Haj.
 apply forall_add_succ_r in Haj.
 apply rm_add_inf_if in Haj.
 destruct Haj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem sum_x1_x_sum_0_0 : ∀ x y i,
  y.[i] = true
  → rm_add_i x y i = x.[i]
  → x.[S i] = false
  → rm_add_i x y (S i) = false.
Proof.
intros y z i Ht5 Hbd Ht6.
remember y.[i] as b eqn:Hb5; symmetry in Hb5.
apply not_true_iff_false; intros H.
unfold rm_add_i in H; simpl in H.
rewrite Ht6, xorb_false_l in H.
rename H into Hcc.
remember Hbd as H; clear HeqH.
unfold rm_add_i in H; simpl in H.
rewrite Hb5, Ht5, xorb_true_r in H.
apply xorb_move_l_r_1 in H.
rewrite negb_xorb_diag_l in H.
rename H into Hyz.
remember (S i) as x.
replace x with (x + 0) in Hcc by apply Nat.add_0_r.
unfold carry in Hyz.
rewrite <- Heqx in Hyz.
remember (fst_same y z x) as s1 eqn:Hs1 .
destruct s1 as [di1| ].
 symmetry in Hs1.
 destruct di1.
  rewrite Nat.add_0_r, Ht6 in Hyz; discriminate Hyz.

  assert (0 < S di1) as H by apply Nat.lt_0_succ.
  erewrite carry_before_relay in Hcc; try eassumption.
  rewrite Nat.add_0_r, Hyz, xorb_true_r in Hcc.
  apply negb_true_iff in Hcc.
  apply fst_same_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, _).
  apply Hn1 in H; rewrite Nat.add_0_r in H.
  rewrite Ht6, Hcc in H; discriminate H.

 symmetry in Hs1.
 remember Hs1 as H; clear HeqH.
 apply fst_same_inf_after with (di := 1) in H.
 rewrite Nat.add_1_r in H.
 rename H into Hs2.
 apply fst_same_iff in Hs1.
 pose proof (Hs1 0) as H; apply negb_sym in H.
 rewrite H, Nat.add_0_r, Ht6, xorb_true_l in Hcc.
 apply negb_true_iff in Hcc.
 unfold carry in Hcc.
 rewrite Hs2 in Hcc; discriminate Hcc.
Qed.

Theorem le_neq_lt : ∀ x y : nat, x ≤ y → x ≠ y → (x < y)%nat.
Proof.
intros x y Hxy Hnxy.
apply le_lt_eq_dec in Hxy.
destruct Hxy as [Hle| Heq]; [ assumption | idtac ].
exfalso; apply Hnxy; assumption.
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

Theorem carry_succ_negb : ∀ x y i a,
  carry x y i = a
  → carry x y (S i) = negb a
  → x.[S i] = a ∧ y.[S i] = a.
Proof.
intros x y i a Hc1 Hc2.
unfold carry in Hc1; simpl in Hc1.
remember (fst_same x y (S i)) as s1 eqn:Hs1 .
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
  eapply carry_before_relay in H; try eassumption.
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
  → (∀ dj, dj ≤ di → rm_add_i x y (i + dj) = x.[i + dj])
  → y.[i + di] = true.
Proof.
intros x y i di Ha Hy Hxy.
revert i Ha Hy Hxy.
induction di; intros; [ rewrite Nat.add_0_r; assumption | idtac ].
pose proof (Hxy (S di) (Nat.le_refl (S di))) as H.
unfold rm_add_i in H; simpl in H.
rewrite xorb_assoc in H.
apply xorb_move_l_r_1 in H.
rewrite xorb_nilpotent in H.
remember y .[ i + S di] as b eqn:Hb .
destruct b; [ reflexivity | symmetry in Hb ].
rewrite xorb_false_l in H.
rename H into Hd.
pose proof (Hxy di (Nat.le_succ_diag_r di)) as H.
unfold rm_add_i in H; simpl in H.
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
remember (fst_same x y (S i)) as s6 eqn:Hs6 .
destruct s6 as [di6| ]; [ idtac | discriminate H ].
remember Hs6 as HH; clear HeqHH.
apply fst_same_sym_iff in HH; simpl in HH.
destruct HH as (Hn6, Ht6).
rewrite H in Ht6; symmetry in Ht6.
rename H into Ha6.
remember Hc5 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same y z (S i)) as s5 eqn:Hs5 .
remember Hs5 as HH; clear HeqHH.
apply fst_same_sym_iff in HH; simpl in HH.
destruct s5 as [di5| ]; [ idtac | clear H ].
 destruct HH as (Hn5, Ht5); rewrite H in Ht5.
 symmetry in Ht5; rename H into Hb5.
 destruct (lt_eq_lt_dec di5 di6) as [[H1| H1]| H1].
  remember Hc3 as H; clear HeqH.
  unfold carry in H; simpl in H.
  remember (fst_same x (y + z) (S i)) as s3 eqn:Hs3 .
  apply fst_same_sym_iff in Hs3; simpl in Hs3.
  destruct s3 as [di3| ]; [ idtac | clear H ].
   destruct Hs3 as (Hn3, Ht3).
   rewrite H in Ht3; symmetry in Ht3.
   rename H into Ha3.
   destruct (lt_eq_lt_dec di3 di5) as [[H2| H2]| H2].
    remember Ht3 as H; clear HeqH.
    unfold rm_add_i in H; simpl in H.
    rewrite <- Nat.add_succ_l in H.
    symmetry in Hs5.
    erewrite carry_before_relay in H; try eassumption; simpl in H.
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
      rewrite <- Nat.add_succ_l.
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
      rewrite <- Nat.add_succ_l.
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
    rewrite <- Nat.add_succ_l.
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
  remember (fst_same x (y + z) (S i)) as s3 eqn:Hs3 .
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
    unfold rm_add_i in H; simpl in H.
    rewrite Ha3, Hb3, Hd3, xorb_true_r, xorb_true_l in H.
    apply negb_sym in H; simpl in H.
    symmetry in Hs5.
    rewrite <- Nat.add_succ_l in H.
    remember H1 as HH; clear HeqHH.
    eapply lt_trans in HH; [ idtac | eassumption ].
    erewrite carry_before_relay in H; try eassumption.
    simpl in H; rewrite Hb5 in H; discriminate H.

    subst di3; rewrite Ha6 in Ha3; discriminate Ha3.

    remember H2 as H; clear HeqH.
    apply Hn3 in H.
    rewrite Ha6 in H; apply negb_sym in H; simpl in H.
    unfold rm_add_i in H; simpl in H.
    rewrite Ht6, xorb_false_l in H.
    rewrite <- Nat.add_succ_l in H.
    symmetry in Hs5.
    erewrite carry_before_relay in H; try eassumption; simpl in H.
    rewrite Hb5, xorb_true_r in H.
    rewrite <- Hn5 in H; [ idtac | assumption ].
    rewrite Ht6 in H; discriminate H.

   remember Hs3 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rename H into Ht3.
   pose proof (Ht3 di6) as H.
   rewrite Ha6 in H; apply negb_sym in H; simpl in H.
   unfold rm_add_i in H; simpl in H.
   rewrite Ht6, xorb_false_l in H.
   rewrite <- Nat.add_succ_l in H.
   symmetry in Hs5.
   erewrite carry_before_relay in H; try eassumption; simpl in H.
   rewrite Hb5, xorb_true_r in H.
   rewrite <- Hn5 in H; [ idtac | assumption ].
   rewrite Ht6 in H; discriminate H.

 rename HH into Ht5.
 remember Hc3 as H; clear HeqH.
 unfold carry in H; simpl in H.
 remember (fst_same x (y + z) (S i)) as s3 eqn:Hs3 .
 destruct s3 as [di3| ]; [ idtac | clear H ].
  rename H into Ha3.
  remember Hs3 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn3, Ht3).
  rewrite Ha3 in Ht3; symmetry in Ht3.
  unfold rm_add_i in Ht3; simpl in Ht3.
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
  unfold rm_add_i in Ha6.
  rewrite Ht6, xorb_false_l in Ha6.
  unfold carry in Ha6.
  remember Hs5 as H; clear HeqH; symmetry in H.
  apply fst_same_inf_after with (di := S di6) in H.
  rewrite Nat.add_succ_r in H; simpl in H.
  rewrite H, xorb_true_r in Ha6.
  rewrite <- Ht5, Ht6 in Ha6; discriminate Ha6.
Qed.

(*
Theorem carry_x_before_xx : ∀ x y i x,
  x.[S i] = x
  → y.[S i] = x
  → carry x y i = x.
Proof.
intros x y i x Ha Hb; unfold carry.
remember (fst_same x y (S i)) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Hs).
 destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
 pose proof (Hn 0 (Nat.lt_0_succ di)) as H.
 rewrite Nat.add_0_r, Ha, Hb in H.
 symmetry in H.
 exfalso; revert H; apply no_fixpoint_negb.

 pose proof (Hs 0) as H.
 rewrite Nat.add_0_r, Ha, Hb in H.
 symmetry in H.
 exfalso; revert H; apply no_fixpoint_negb.
Qed.
*)

(*
Theorem carry_eq_l_add_eq_r : ∀ x y i,
  carry x y i = x.[i] ↔ rm_add_i x y i = y.[i].
Proof.
intros x y i.
split; intros H.
 unfold rm_add_i; rewrite xorb_shuffle0.
 rewrite H, xorb_nilpotent, xorb_false_l; reflexivity.

 unfold rm_add_i in H; rewrite xorb_shuffle0, xorb_comm in H.
 apply xorb_move_l_r_1 in H.
 rewrite xorb_nilpotent in H.
 apply xorb_eq.
 rewrite xorb_comm; assumption.
Qed.
*)

(*
Theorem sum_0x_x_not_sum_y1_0 : ∀ x y z i di1 di2 di4 y t,
  (∀ dj, dj < di1 → rm_add_i x y (S (i + dj)) = negb z .[ S (i + dj)])
  → (∀ dj, dj < di4 → y .[ S (i + di2 + dj)] = negb z .[ S (i + di2 + dj)])
  → carry x y (i + di2) = false
  → di2 + di4 < di1
  → x .[ S (i + di2)] = false
  → y .[ S (i + di2)] = y
  → rm_add_i x y (S (i + di2)) = y
  → carry x y (S (i + di2)) = false
  → x .[ S (i + di2 + di4)] = negb t
  → y .[ S (i + di2 + di4)] = true
  → rm_add_i x y (S (i + di2 + di4)) = false
  → carry x y (S (i + di2 + di4)) = t
  → False.
Proof.
intros x y z i di1 di2 di4 y t.
intros Hn1 Hn4 He5 H2 Ha6 Hb6 He6 Hf6 Ha4 Hb4 He4 Hf4.
destruct di4.
 rewrite Nat.add_0_r in H2, Ha4, Hb4, He4, Hf4.
 rewrite Hf6 in Hf4; subst t.
 rewrite Ha6 in Ha4; discriminate Ha4.

 rewrite Nat.add_succ_r in H2, Ha4, Hb4, He4, Hf4.
 revert di2 Hn4 He5 H2 y Ha6 Hb6 He6 Hf6 t Ha4 Hb4 He4 Hf4.
 induction di4; intros.
  rewrite Nat.add_0_r in H2, Ha4, Hb4, He4, Hf4.
  destruct t.
   rewrite <- negb_involutive in Hf4.
   apply carry_succ_negb in Hf4; [ idtac | assumption ].
   rewrite Hb4 in Hf4.
   destruct Hf4 as (_, H); discriminate H.

   simpl in Ha4.
   apply carry_x_before_xx with (y := y) in Ha4; try eassumption.
   rewrite Hf6 in Ha4; discriminate Ha4.

  rewrite Nat.add_succ_r in H2, Ha4, Hb4, He4, Hf4.
  clear He5 y Ha6 Hb6 He6.
  remember x .[ S (S (i + di2))] as x eqn:Ha6 .
  symmetry in Ha6.
  remember y .[ S (S (i + di2))] as y eqn:Hb6 .
  symmetry in Hb6.
  assert (0 < S di4) as H by apply Nat.lt_0_succ.
  apply Nat.succ_lt_mono, Hn4 in H.
  rewrite Nat.add_1_r, Hb6 in H.
  rewrite <- Nat.add_succ_r in H.
  rewrite <- Hn1 in H; [ idtac | omega ].
  rewrite Nat.add_succ_r in H; symmetry in H.
  rename H into He6; move y before x.
  remember He6 as H; clear HeqH.
  unfold rm_add_i in H.
  rewrite Ha6, Hb6 in H.
  rewrite xorb_shuffle0, xorb_comm in H.
  apply xorb_move_l_r_1 in H.
  rewrite xorb_nilpotent in H.
  apply xorb_eq in H; symmetry in H.
  destruct x.
   rewrite <- negb_involutive in H.
   apply carry_succ_negb in H; [ idtac | assumption ].
   rewrite Ha6 in H.
   destruct H as (H, _); discriminate H.

   move t after H2.
   move y after t; move Ha6 after t; move Hb6 after t.
   move He6 after t; move Hf6 after t.
   rewrite <- Nat.add_succ_r in Hf6, Ha6, Hb6, He6, H.
   remember (S (i + di2 + di4)) as x eqn:Hx .
   rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in Hx; subst x.
   eapply IHdi4; try eassumption.
   intros dj Hdj.
   rewrite Nat.add_succ_r; simpl.
   rewrite <- Nat.add_succ_r.
   apply Hn4.
   apply Nat.succ_lt_mono in Hdj.
   assumption.
Qed.
*)

(*
Theorem sum_x1_0_carry_not_x : ∀ x y z i di1 di2 di4 t,
  (∀ dj, dj < di1 → rm_add_i x y (S (i + dj)) = negb z .[ S (i + dj)])
  → (∀ dj, dj < S di4 →
     y .[ S (S (i + di2 + dj))] = negb z .[ S (S (i + di2 + dj))])
  → carry x y (S (i + di2)) = false
  → S (S (di2 + di4)) < di1
  → x .[ S (S (S (i + di2 + di4)))] = negb t
  → y .[ S (S (S (i + di2 + di4)))] = true
  → rm_add_i x y (S (S (S (i + di2 + di4)))) = false
  → carry x y (S (S (S (i + di2 + di4)))) = t
  → False.
Proof.
intros x y z i di1 di2 di4 t Hn1 Hn4 He5 H2 Ha4 Hb4 He4 Hf4.
simpl in Hn4, He5, H2, Ha4, Hb4, He4, Hf4.
remember x .[ S (S (i + di2))] as x eqn:Ha6 .
symmetry in Ha6.
remember y .[ S (S (i + di2))] as y eqn:Hb6 .
symmetry in Hb6.
assert (0 < S di4) as H by apply Nat.lt_0_succ.
apply Hn4 in H.
rewrite Nat.add_0_r, Hb6 in H.
rewrite <- Nat.add_succ_r in H.
rewrite <- Hn1 in H; [ idtac | omega ].
rewrite Nat.add_succ_r in H; symmetry in H.
rename H into He6; move y before x.
remember He6 as H; clear HeqH.
unfold rm_add_i in H.
rewrite Ha6, Hb6 in H.
rewrite xorb_shuffle0, xorb_comm in H.
apply xorb_move_l_r_1 in H.
rewrite xorb_nilpotent in H.
apply xorb_eq in H; symmetry in H.
rename H into Hf6.
destruct x.
 remember Hf6 as H; clear HeqH.
 rewrite <- negb_involutive in H.
 apply carry_succ_negb in H; [ idtac | assumption ].
 rewrite Ha6 in H.
 destruct H as (H, _); discriminate H.

 move t after H2.
 move y after t; move Ha6 after t; move Hb6 after t.
 move He6 after t; move Hf6 after t.
 rewrite <- Nat.add_succ_r in He5, Ha6, Hb6, He6, Hf6.
 remember (S (i + di2 + di4)) as x eqn:Hx .
 rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in Hx; subst x.
 rewrite <- Nat.add_succ_r, <- Nat.add_succ_l in H2, Ha4, Hb4, He4, Hf4.
 simpl in Ha4, Hb4, He4, Hf4.
 eapply sum_0x_x_not_sum_y1_0; try eassumption.
 intros dj Hdj.
 rewrite Nat.add_succ_r; simpl.
 apply Hn4; assumption.
Qed.
*)

(* TODO: compare with sum_x1_0_carry_not_x
Theorem sum_x1_carry_not_x2 : ∀ x y z i di2 di4 di x,
  (∀ dj,  dj < di2 + di
   → rm_add_i x y (S (i + dj)) = negb z .[ S (i + dj)])
  → (∀ dj, S dj < di4 →
     y .[ S (i + di2 + dj)] = negb z .[ S (i + di2 + dj)])
  → di < di4
  → x .[ S (i + di2 + di)] = x
  → y .[ S (i + di2 + di)] = true
  → z .[ S (i + di2 + di)] = false
  → carry x y (i + di2) = false
  → carry x y (S (i + di2 + di)) = negb x
  → False.
Proof.
intros x y z i di2 di4 di x Hn1 Hn4 H2 Ha2 Hb3 Hd1 Hf1 H.
revert di2 di4 Hn1 Hn4 Ha2 Hb3 Hd1 Hf1 H H2.
induction di; intros.
 rewrite Nat.add_0_r in Hd1, Hn1, Hb3, Ha2, H.
 destruct x.
  erewrite carry_x_before_xx in Hf1; try eassumption.
  discriminate Hf1.

  apply carry_succ_negb in H; [ idtac | assumption ].
  rewrite Hb3 in H.
  destruct H as (_, H); discriminate H.

 rewrite Nat.add_succ_r in Hd1, Hn1, Hb3, Ha2, H.
 rename H into Hf3.
 destruct di4; [ revert H2; apply Nat.nlt_0_r | idtac ].
 apply Nat.succ_lt_mono in H2.
 assert (0 < di4) as H by (eapply Nat.lt_lt_0; eauto ).
 apply Nat.succ_lt_mono in H.
 apply Hn4 in H.
 rewrite Nat.add_comm in H; simpl in H.
 rewrite <- Hn1 in H.
  rename H into Hb5.
  remember Hb5 as H; clear HeqH.
  symmetry in H.
  apply carry_eq_l_add_eq_r in H.
  remember x .[ S (i + di2)] as y eqn:Ha5 .
  symmetry in Ha5.
  destruct y.
   rewrite <- negb_involutive in H.
   apply carry_succ_negb in H; [ idtac | assumption ].
   rewrite Ha5 in H.
   destruct H as (H, _); discriminate H.

   move H after Hf3.
   remember (S (i + di2 + di)) as v.
   rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in Heqv; subst v.
   rewrite <- Nat.add_succ_r in H.
   apply IHdi with (di2 := S di2) (di4 := S di); try assumption.
    intros dj Hdj.
    rewrite Nat.add_succ_r, Nat.add_succ_l, <- Nat.add_succ_r.
    apply Hn4.
    eapply le_lt_trans; [ eassumption | idtac ].
    apply Nat.succ_lt_mono in H2; assumption.

    apply Nat.lt_succ_diag_r.

  rewrite <- Nat.add_succ_r.
  apply Nat.lt_sub_lt_add_l.
  rewrite Nat.sub_diag.
  apply Nat.lt_0_succ.
Qed.
*)

(*
Theorem old_subcase_2a : ∀ x y z i di3 di2 u,
  fst_same x (y + z) (S i) = Some di3
  → fst_same y z (S i) = Some di2
  → x .[ S (i + di3)] = u
  → y .[ S (i + di2)] = u
  → di3 < di2
  → False.
Proof.
intros x y z i di3 di2 u.
intros Hs3 Hs2 Ha3 Hb2 H2.
remember Hs2 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hn2, Hd2); rewrite Hb2 in Hd2; symmetry in Hd2.
remember Hs3 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hn3, He3); rewrite Ha3 in He3; symmetry in He3.
remember He3 as H; clear HeqH.
unfold rm_add_i in H; simpl in H.
rewrite Hn2 in H; [ idtac | assumption ].
rewrite negb_xorb_diag_l, xorb_true_l in H.
symmetry in H; apply negb_sym in H.
rewrite <- Nat.add_succ_l in H.
erewrite carry_before_relay in H; try eassumption; simpl in H.
rewrite Hb2 in H.
symmetry in H; revert H; apply no_fixpoint_negb.
Qed.

Theorem subcase_2a : ∀ x y z i di1 di3 di2,
  fst_same (x + y) z (S i) = Some di1
  → fst_same x (y + z) (S i) = Some di3
  → fst_same y z (S i) = Some di2
  → x .[ S (i + di3)] = true
  → di2 < di1
  → di3 < di2
  → False.
Proof.
intros x y z i di1 di3 di2.
intros Hs1 Hs3 Hs2 Ha3 H1 H2.
remember Hs2 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hn2, Hd2); symmetry in Hd2.
remember Hs3 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hn3, He3); rewrite Ha3 in He3; symmetry in He3.
remember He3 as H; clear HeqH.
unfold rm_add_i in H; simpl in H.
rewrite Hn2 in H; [ idtac | assumption ].
rewrite negb_xorb_diag_l, xorb_true_l in H.
symmetry in H; apply negb_sym in H.
rewrite <- Nat.add_succ_l in H.
erewrite carry_before_relay in H; try eassumption; simpl in H.
rewrite H in Hd2; rename H into Hb2.
remember H2 as H; clear HeqH.
apply Hn2 in H; rename H into Hb3.
remember Hs1 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hn1, Ht1).
remember H1 as H; clear HeqH.
eapply lt_trans in H; [ idtac | eassumption ].
apply Hn1 in H.
rewrite <- Hb3 in H.
apply carry_eq_l_add_eq_r in H.
rewrite Ha3 in H; rename H into Hf3.
pose proof (Hn1 di2 H1) as H.
rewrite Hd2 in H; simpl in H.
rename H into Hf2.
remember Hf2 as H; clear HeqH.
unfold rm_add_i in H; simpl in H.
rewrite Hb2, xorb_false_r in H.
apply negb_false_iff in H.
rewrite negb_xorb_l in H.
apply xorb_eq in H; symmetry in H; rename H into He2.
remember (di2 - S di3) as di.
apply nat_sub_add_r in Heqdi; [ idtac | assumption ].
subst di2; clear H2.
clear Hs3 Ha3 Hb3 Hn2 Hn3 Hd2 He3 Hf2; revert di3 Hs2 Hb2 He2 Hf3 H1.
induction di; intros.
 rewrite Nat.add_1_r, Nat.add_succ_r in Hb2, He2.
 remember x .[ S (S (i + di3))] as x eqn:Ha2 .
 symmetry in Ha2.
 destruct x.
  apply carry_succ_negb in He2; [ idtac | assumption ].
  rewrite Hb2 in He2.
  destruct He2 as (_, H); discriminate H.

  eapply carry_x_before_xx in Hb2; [ idtac | eassumption ].
  rewrite Hf3 in Hb2; discriminate Hb2.

 remember (carry x y (S (S (i + di3)))) as x eqn:Hx .
 symmetry in Hx.
 destruct x.
  rewrite <- Nat.add_succ_r in Hx.
  remember (di3 + S (S di)) as y.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Heqy; subst y.
  eapply IHdi; eassumption.

  rewrite <- negb_involutive in Hx.
  apply carry_succ_negb in Hx; [ idtac | assumption ].
  simpl in Hx; destruct Hx as (Ha3, Hb3).
  do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs2.
  remember Hs2 as H; clear HeqH.
  apply fst_same_iff in H.
  destruct H as (Hn2, Ht2).
  pose proof (Nat.lt_succ_diag_r (S di3)) as H.
  eapply Nat.lt_lt_add_r in H.
  apply Hn2 in H; simpl in H.
  rewrite Nat.add_succ_r, Hb3, <- Nat.add_succ_r in H.
  rewrite <- Hn1 in H; [ idtac | omega ].
  symmetry in H.
  rewrite Nat.add_succ_r in H.
  unfold rm_add_i in H.
  rewrite Ha3, Hb3, xorb_nilpotent, xorb_false_l in H.
  simpl in Hs2.
  rewrite <- Nat.add_succ_r in Hs2, H.
  rewrite <- Nat.add_succ_l in Hs2.
  remember (di3 + S (S di)) as y.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l in Heqy; subst y.
  eapply IHdi; eassumption.
Qed.
*)

(*
     i  i+1  -   i2  -   i1
  y  .   .   .   .   .   .
                  +t
  x  .   .   .   1   .   .
         ≠   ≠
y+z  .   .   .   .   .   .

x+y  .   .   .   .   .   .
         ≠   ≠   ≠   ≠
  z  .   .   .   .   .   0
         ≠   ≠    +t
  y  .   .   .   1   .   .

 *)
(*
Theorem subcase_2b : ∀ x y z i di1 di2,
  fst_same (x + y) z (S i) = Some di1
  → fst_same y z (S i) = Some di2
  → fst_same x (y + z) (S i) = Some di2
  → rm_add_i x y (S (i + di1)) = false
  → x .[ S (i + di2)] = true
  → di2 < di1
  → False.
Proof.
intros x y z i di1 di2.
intros Hs1 Hs2 Hs3 He1 Ha3 H1.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Hd1); rewrite He1 in Hd1; symmetry in Hd1.
apply fst_same_iff in Hs2; simpl in Hs2.
destruct Hs2 as (Hn2, Hd2); symmetry in Hd2.
apply fst_same_iff in Hs3; simpl in Hs3.
destruct Hs3 as (Hn3, He3); rewrite Ha3 in He3; symmetry in He3.
remember He3 as H; clear HeqH.
unfold rm_add_i in H; simpl in H.
rewrite Hd2, xorb_nilpotent, xorb_false_l in H.
unfold carry in H.
remember (fst_same y z (S (S (i + di2)))) as s4 eqn:Hs4 .
destruct s4 as [di4| ]; [ idtac | clear H ].
 rename H into Hb4; simpl in Hb4.
 remember Hs4 as H; clear HeqH.
 apply fst_same_sym_iff in H; simpl in H.
 destruct H as (Hn4, Hd4); rewrite Hb4 in Hd4; symmetry in Hd4.
 destruct (lt_eq_lt_dec (S (di2 + di4)) di1) as [[H2| H2]| H2].
  destruct di4.
   clear Hn4; rewrite Nat.add_0_r in Hb4, Hd4, H2.
   remember H2 as H; clear HeqH.
   apply Hn1 in H.
   rewrite Nat.add_succ_r, Hd4 in H; simpl in H.
   unfold rm_add_i in H; simpl in H.
   rewrite Hb4, xorb_shuffle0, xorb_comm in H.
   apply xorb_move_l_r_1 in H; simpl in H.
   apply xorb_move_l_r_1 in H; rewrite xorb_true_r in H.
   remember x .[ S (S (i + di2))] as x eqn:Ha4 .
   symmetry in Ha4; rename H into He4.
   remember Hd2 as H; clear HeqH.
   symmetry in H; rewrite <- negb_involutive in H.
   rewrite <- Hn1 in H; [ idtac | apply Nat.lt_le_incl; assumption ].
   apply negb_sym in H; simpl in H.
   unfold rm_add_i in H.
   rewrite Ha3, xorb_true_l in H.
   apply xorb_move_l_r_1 in H.
   rewrite xorb_nilpotent in H.
   rename H into He5.
   destruct x; simpl in He4.
    remember He5 as H; clear HeqH.
    unfold carry in H; simpl in H.
    remember (fst_same x y (S (S (i + di2)))) as s5 eqn:Hs5 .
    destruct s5 as [di5| ]; [ idtac | discriminate H ].
    apply fst_same_sym_iff in Hs5; simpl in Hs5.
    destruct Hs5 as (Hn5, Hb5); rewrite H in Hb5; symmetry in Hb5.
    destruct di5.
     rewrite Nat.add_0_r, Ha4 in H; discriminate H.

     clear H.
     pose proof (Hn5 0 (Nat.lt_0_succ di5)) as H.
     rewrite Nat.add_0_r, Ha4, Hb4 in H; discriminate H.

    rewrite <- negb_involutive in He4.
    apply carry_succ_negb in He4; [ simpl in He4 | assumption ].
    rewrite Hb4 in He4; destruct He4 as (_, H); discriminate H.

   remember Hd2 as H; clear HeqH.
   rewrite <- negb_involutive in H.
   apply negb_sym in H.
   rewrite <- Hn1 in H; [ idtac | assumption ].
   symmetry in H; simpl in H.
   unfold rm_add_i in H.
   rewrite Ha3, xorb_true_l in H.
   apply xorb_move_l_r_1 in H.
   rewrite xorb_nilpotent in H.
   rename H into He5.
   remember Hd4 as H; clear HeqH.
   rewrite Nat.add_succ_r in H.
   rewrite <- Nat.add_assoc in H.
   do 2 rewrite <- Nat.add_succ_r in H.
   rewrite <- negb_involutive in H.
   apply negb_sym in H; simpl in H.
   rewrite <- Hn1 in H; [ idtac | omega ].
   symmetry in H.
   do 2 rewrite Nat.add_succ_r in H.
   rewrite Nat.add_assoc in H.
   rename H into He4.
   remember He4 as H; clear HeqH.
   unfold rm_add_i in H.
   rewrite Nat.add_succ_r in Hb4.
   rewrite Hb4, xorb_true_r in H.
   apply xorb_eq in H.
   symmetry in H; apply negb_sym in H.
   remember (carry x y (S (S (S (i + di2 + di4))))) as t eqn:Hf4 .
   rename H into Ha4.
   move He5 at bottom; move t at bottom; move H2 at bottom.
   move Hb4 at bottom; move He4 at bottom; move Hf4 at bottom.
   symmetry in Hf4.
   rewrite Nat.add_succ_r in H2.
   eapply sum_x1_0_carry_not_x; eassumption.

  subst di1.
  rewrite Nat.add_succ_r, Nat.add_assoc, Hd4 in Hd1.
  discriminate Hd1.

  remember (di1 - S di2) as di.
  apply nat_sub_add_r in Heqdi; [ idtac | assumption ].
  subst di1; clear H1.
  rewrite Nat.add_succ_r in H2; simpl in H2.
  apply Nat.succ_lt_mono, Nat.add_lt_mono_l in H2.
  rewrite Nat.add_succ_r in Hd1, He1, Hn1.
  rewrite Nat.add_succ_r, Nat.add_assoc in Hd1, He1.
  assert (di2 < S di2) as H by apply Nat.lt_succ_diag_r.
  apply Nat.lt_lt_add_r with (p := di) in H; simpl in H.
  apply Hn1 in H.
  rewrite Hd2 in H; simpl in H.
  rename H into He2.
  remember He2 as H; clear HeqH.
  unfold rm_add_i in H.
  rewrite Ha3, xorb_true_l in H.
  apply xorb_move_l_r_1 in H.
  rewrite xorb_nilpotent in H.
  rename H into Hf2.
  remember He1 as H; clear HeqH.
  unfold rm_add_i in H.
  rewrite Hn4 in H; [ idtac | assumption ].
  rewrite Hd1 in H.
  rewrite xorb_true in H.
  rewrite <- negb_xorb_l in H.
  apply negb_false_iff, xorb_move_l_r_1 in H.
  rewrite xorb_true_r in H.
  rename H into Hf6.
  remember x .[ S (S (i + di2 + di))] as t eqn:Ha6 .
  symmetry in Ha6.
  remember Hd1 as H; clear HeqH.
  symmetry in H.
  rewrite <- negb_involutive in H.
  rewrite <- Hn4 in H; [ idtac | assumption ].
  apply negb_sym in H.
  remember (S (i + di2 + di)) as x eqn:Hx .
  rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in Hx; subst x.
  rewrite <- Nat.add_succ_r in Hf2.
  move H after Ha6.
  eapply sum_x1_carry_not_x2; try eassumption.
   intros dj Hdj; apply Hn1; assumption.

   intros dj Hdj; rewrite Nat.add_succ_r; simpl; apply Hn4.
   eapply lt_trans; [ idtac | eassumption ].
   apply Nat.lt_succ_diag_r.

 remember Hs4 as Hn4; clear HeqHn4.
 apply fst_same_sym_iff in Hn4; simpl in Hn4.
 remember (di1 - S di2) as di.
 apply nat_sub_add_r in Heqdi; [ idtac | assumption ].
 subst di1; clear H1.
 rewrite Nat.add_succ_r in Hd1, He1, Hn1.
 rewrite Nat.add_succ_r, Nat.add_assoc in Hd1, He1.
 assert (di2 < S di2) as H by apply Nat.lt_succ_diag_r.
 apply Nat.lt_lt_add_r with (p := di) in H; simpl in H.
 apply Hn1 in H.
 rewrite Hd2 in H; simpl in H.
 rename H into He2.
 remember He2 as H; clear HeqH.
 unfold rm_add_i in H.
 rewrite Ha3, xorb_true_l in H.
 apply xorb_move_l_r_1 in H.
 rewrite xorb_nilpotent in H.
 rename H into Hf2.
 remember He1 as H; clear HeqH.
 unfold rm_add_i in H.
 rewrite Hn4, Hd1 in H.
 rewrite xorb_true in H.
 rewrite <- negb_xorb_l in H.
 apply negb_false_iff, xorb_move_l_r_1 in H.
 rewrite xorb_true_r in H.
 rename H into Hf6.
 remember x .[ S (S (i + di2 + di))] as t eqn:Ha6 .
 symmetry in Ha6.
 remember Hd1 as H; clear HeqH.
 symmetry in H.
 rewrite <- negb_involutive in H.
 rewrite <- Hn4 in H.
 apply negb_sym in H.
 remember (S (i + di2 + di)) as x eqn:Hx .
 rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in Hx; subst x.
 rewrite <- Nat.add_succ_r in Hf2.
 move H after Ha6.
 eapply sum_x1_carry_not_x2 with (di4 := S di); try eassumption.
  intros dj Hdj; apply Hn1; assumption.

  intros dj Hdj; rewrite Nat.add_succ_r; simpl; apply Hn4.

  apply Nat.lt_succ_diag_r.
Qed.
*)

(*
Theorem after_carry_negb : ∀ x y i u,
  carry x y i = u
  → x .[ S i] = negb u
  → y .[ S i] = u.
Proof.
intros x y i u Hc Ha.
unfold carry in Hc; simpl in Hc.
remember (fst_same x y (S i)) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Hs).
 destruct di.
  rewrite Nat.add_0_r, Ha in Hc.
  exfalso; revert Hc; apply no_fixpoint_negb.

  pose proof (Hn 0 (Nat.lt_0_succ di)) as H.
  rewrite Nat.add_0_r, Ha in H; apply negb_sym in H.
  rewrite negb_involutive in H; assumption.

 subst u.
 pose proof (Hs 0) as H.
 rewrite Nat.add_0_r, Ha in H; apply negb_sym in H.
 rewrite negb_involutive in H; assumption.
Qed.
*)

(*
Theorem carry_succ_diff : ∀ x y i t u,
  carry x y i = t
  → x .[ S i] = u
  → y .[ S i] = negb u
  → carry x y (S i) = t.
Proof.
intros x y i t u Hc Ha Hb.
rewrite <- negb_involutive.
apply neq_negb.
intros H.
apply carry_succ_negb in H; [ idtac | assumption ].
rewrite Ha, Hb in H.
destruct H as (Hu, H); rewrite Hu in H.
revert H; apply no_fixpoint_negb.
Qed.
*)

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

(* perhaps conclution simplifixyle, see carry_repeat2 *)
Theorem carry_repeat : ∀ x y z i,
  carry x y i = false
  → carry (x + y) z i = false
  → carry y z i = true
  → ∃ m,
    carry x y (S (i + m)) = false ∧
    carry (x + y) z (S (i + m)) = false ∧
    carry y z (S (i + m)) = true ∧
    x.[S (i + m)] = false ∧
    y.[S (i + m)] = false ∧
    z.[S (i + m)] = true ∧
    (∀ dj, dj ≤ m → y.[S (i + dj)] = negb z.[S (i + dj)]) ∧
    (∀ dj, dj ≤ m → rm_add_i x y (S (i + dj)) = negb z.[S (i + dj)]).
Proof.
intros x y z i Rxy Rayz Ryz.
rename Rxy into Rxyn.
rename Rayz into Rxy_zn.
rename Ryz into Ryzn.
remember Rxyn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x y (S i)) as sxyn eqn:Hsxyn .
destruct sxyn as [dxyn| ]; [ idtac | discriminate H ].
rename H into A_p.
symmetry in Hsxyn.
remember Rxy_zn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (x + y) z (S i)) as sxy_zn.
rename Heqsxy_zn into Hsxy_zn.
destruct sxy_zn as [dxy_zn| ]; [ idtac | discriminate H ].
rename H into AB_p; symmetry in Hsxy_zn.
remember Ryzn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same y z (S i)) as syzn eqn:Hsyzn .
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
    unfold rm_add_i in H.
    rewrite Ap, Bp, xorb_false_l in H.
    rename H into Rxyp.
    remember Hsxy_zn as H; clear HeqH.
    eapply carry_before_relay in H; [ idtac | eassumption ].
    simpl in H.
    rewrite AB_p in H.
    rename H into Rxy_zp.
    remember Hsyzn as H; clear HeqH.
    eapply carry_before_relay in H; [ idtac | eassumption ].
    simpl in H.
    rewrite B_p in H.
    rename H into Ryzp.
    exists p.
    split; [ assumption | idtac ].
    split; [ assumption | idtac ].
    split; [ assumption | idtac ].
    split; [ assumption | idtac ].
    split; [ assumption | idtac ].
    split; [ assumption | idtac ].
    split; intros dj Hdj.
     eapply Hnyzn, le_lt_trans; eassumption.

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
    unfold rm_add_i in H.
    rewrite Hnxyn in H; [ idtac | assumption ].
    rewrite negb_xorb_diag_l, xorb_true_l in H.
    rewrite <- Nat.add_succ_l in H.
    erewrite carry_before_relay in H; try eassumption.
    simpl in H; rewrite A_p in H; discriminate H.

   eapply min_neq_lt in H; eauto ; try (left; auto).
   rename H into Hpdyzn.
   destruct (eq_nat_dec dxy_zn p) as [H| H].
    move H at top; subst dxy_zn.
    remember AB_p as H; clear HeqH.
    unfold rm_add_i in H; simpl in H.
    rewrite Hnxyn in H; [ idtac | assumption ].
    rewrite negb_xorb_diag_l, xorb_true_l in H.
    apply negb_false_iff in H.
    rewrite <- Nat.add_succ_l in H.
    erewrite carry_before_relay in H; try eassumption.
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
   unfold rm_add_i in H.
   rewrite Ap, Bp, xorb_false_l in H.
   exists p.
   split; [ assumption | idtac ].
   rewrite <- Nat.add_succ_l.
   erewrite carry_before_relay; try eassumption; simpl.
   split; [ assumption | idtac ].
   rewrite <- Nat.add_succ_l.
   erewrite carry_before_inf_relay; [ idtac | assumption ].
   split; [ reflexivity | idtac ].
   split; [ assumption | idtac ].
   split; [ assumption | idtac ].
   split; [ assumption | idtac ].
   split; intros dj Hdj.
    apply Hnyzn.

    eapply Hnxy_zn, le_lt_trans; eassumption.

  eapply min_neq_lt in H; eauto ; try (left; auto).
  rename H into Hpdxyn.
  destruct (eq_nat_dec dxy_zn p) as [H| H].
   move H at top; subst dxy_zn.
   remember Hsxyn as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hnxyn, B_p).
   rewrite A_p in B_p; symmetry in B_p.
   remember AB_p as H; clear HeqH.
   unfold rm_add_i in H.
   rewrite Hnxyn in H; [ idtac | assumption ].
   rewrite negb_xorb_diag_l, xorb_true_l in H.
   rewrite <- Nat.add_succ_l in H.
   erewrite carry_before_relay in H; try eassumption.
   simpl in H; rewrite A_p in H; discriminate H.

   eapply min_neq_lt in H; eauto ; try (right; left; auto).
   simpl in Hp.
   destruct (Nat.min_dec dxy_zn dxyn) as [L1| L1].
    rewrite L1 in Hp; subst p.
    exfalso; revert H; apply Nat.lt_irrefl.

    rewrite L1 in Hp; subst p.
    exfalso; revert Hpdxyn; apply Nat.lt_irrefl.
Qed.

Definition rm_shift n x := {| rm i := x.[i+n] |}.
Arguments rm_shift n%nat x%rm.

Theorem fst_same_shift : ∀ x y x' y' i di d,
  fst_same x y i = Some di
  → d ≤ di
  → x' = rm_shift d x
  → y' = rm_shift d y
  → fst_same x' y' i = Some (di - d).
Proof.
intros x y x' y' i di d Hs Hd Ha' Hb'.
subst x' y'; simpl.
apply fst_same_iff in Hs; simpl in Hs.
destruct Hs as (Hn, Hs).
apply fst_same_iff; simpl.
split.
 intros dj Hdj.
 rewrite <- Nat.add_assoc.
 apply Hn.
 omega.

 rewrite Nat.add_sub_assoc; [ idtac | assumption ].
 rewrite Nat.sub_add; [ idtac | omega ].
 assumption.
Qed.

Theorem carry_shift : ∀ x y n i,
  carry (rm_shift n x) (rm_shift n y) i = carry x y (i + n).
Proof.
intros x y n i.
unfold carry; simpl.
remember (fst_same x y (S (i + n))) as s1 eqn:Hs1 .
remember (fst_same (rm_shift n x) (rm_shift n y) (S i)) as s2 eqn:Hs2 .
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

Theorem rm_add_i_shift : ∀ x y i n,
  rm_add_i (rm_shift n x) (rm_shift n y) i = rm_add_i x y (i + n).
Proof.
intros x y i n.
unfold rm_add_i; simpl.
rewrite carry_shift; reflexivity.
Qed.

Theorem fst_same_shift_add_l : ∀ x y z n i,
  fst_same (rm_shift n (x + y)) z i =
  fst_same (rm_shift n x + rm_shift n y) z i.
Proof.
intros x y z n i.
apply fst_same_iff; simpl.
remember (fst_same (rm_shift n x + rm_shift n y) z i) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Hs).
 split.
  intros dj Hdj.
  apply Hn in Hdj.
  rewrite rm_add_i_shift in Hdj; assumption.

  rewrite rm_add_i_shift in Hs; assumption.

 intros dj; rewrite <- rm_add_i_shift; apply Hs.
Qed.

Theorem carry_shift_add_l : ∀ x y z n i,
  carry (rm_shift n x + rm_shift n y) (rm_shift n z) i =
  carry (x + y) z (i + n).
Proof.
intros x y z n i.
rewrite <- carry_shift.
unfold carry; simpl.
rewrite <- fst_same_shift_add_l.
remember (rm_shift n (x + y)) as xy'.
remember (rm_shift n z) as z'.
remember (fst_same xy' z' (S i)) as s eqn:Hs .
subst xy' z'.
destruct s as [di| ]; [ idtac | reflexivity ].
apply rm_add_i_shift.
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
remember (fst_same (x + y) z (S i)) as s eqn:Hs .
destruct s as [di| ]; [ idtac | discriminate H ].
symmetry in Hs; clear H.
revert x y z i Hc4 Hc5 Hc6 Hs.
induction di as (di, IHdi) using all_lt_all; intros.
remember Hc4 as H; clear HeqH.
apply carry_repeat in H; try assumption.
destruct H as (n, (Rxyn, (Rxy_zn, (Ryzn, H)))).
destruct H as (Xn, (Yn, (Zn, H))).
destruct H as (Hnyz, Hnxy_z).
move Rxyn after Ryzn.
destruct (lt_eq_lt_dec di n) as [[H1| H1]| H1].
 remember Hs as H; clear HeqH.
 apply fst_same_iff in H; simpl in H.
 destruct H as (Hnxy_z2, Hxy_z).
 rewrite Hnxy_z in Hxy_z; [ idtac | apply Nat.lt_le_incl; assumption ].
 exfalso; revert Hxy_z; apply no_fixpoint_negb.

 subst di.
 remember Hs as H; clear HeqH.
 apply fst_same_iff in H; simpl in H.
 destruct H as (Hnxy_z2, Hxy_z).
 remember Hc4 as H; clear HeqH.
 unfold carry in H; rewrite Hs in H; simpl in H.
 rewrite H, Zn in Hxy_z; discriminate Hxy_z.

 clear Xn Yn Zn Hnyz Hnxy_z.
 remember (di - S n) as dj.
 apply nat_sub_add_r in Heqdj; [ idtac | assumption ].
 clear Hc4 Hc5 Hc6.
 rename Rxy_zn into Hc4; rename Ryzn into Hc5; rename Rxyn into Hc6.
 remember (rm_shift (S n) (x + y)%rm) as x'y' eqn:Hxy .
 remember (rm_shift (S n) z) as z' eqn:Hc .
 eapply fst_same_shift in Hs; try eassumption.
 assert (di - S n < di) as H by omega.
 subst x'y'.
 rewrite fst_same_shift_add_l in Hs.
 remember (rm_shift (S n) x) as x' eqn:Ha .
 remember (rm_shift (S n) y) as y' eqn:Hb .
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
    (∀ dj, dj ≤ m → rm_add_i x y (S (i + dj)) = negb z.[S (i + dj)]).
Proof.
intros x y z i u Hc3 Hc4 Hc5 Hc6.
remember Hc4 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (x + y) z (S i)) as s4 eqn:Hs4 .
symmetry in Hs4; rename H into H4.
destruct s4 as [di4| ]; [ idtac | discriminate H4 ].
remember Hc3 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x (y + z) (S i)) as s3 eqn:Hs3 .
symmetry in Hs3; rename H into H3.
remember Hc5 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same y z (S i)) as s5 eqn:Hs5 .
symmetry in Hs5; rename H into H5.
remember Hc6 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x y (S i)) as s6 eqn:Hs6 .
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
       unfold rm_add_i in H.
       rewrite Ht6, Ht4, xorb_true_l in H.
       apply negb_true_iff in H.
       rewrite <- Nat.add_succ_l in H.
       erewrite carry_before_relay in H; try eassumption.
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
       unfold rm_add_i in H; simpl in H.
       rewrite H3, H5, xorb_nilpotent, xorb_false_l in H.
       rename H into Hcxym.
       remember Ht3 as H; clear HeqH.
       unfold rm_add_i in H.
       rewrite H5, Ht5, xorb_nilpotent, xorb_false_l in H.
       rename H into Hcyzm.
       remember Hcxym as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same x y (S (S (i + m)))) as sxym eqn:Hsxym .
       destruct sxym as [djxym| ]; [ idtac | discriminate H ].
       symmetry in Hsxym.
       rename H into Haxym.
       remember Hs4 as H; clear HeqH.
       eapply carry_before_relay in H; [ idtac | eassumption ].
       simpl in H; rewrite H4 in H.
       rename H into Hxycm.
       exfalso; eapply case_2; eassumption.

       eapply min_neq_lt in M5; [ idtac | eauto  | do 3 right; left; auto ].
       remember Ht3 as H; clear HeqH.
       unfold rm_add_i in H.
       rewrite Hn5 in H; [ idtac | assumption ].
       rewrite negb_xorb_diag_l, xorb_true_l in H.
       apply negb_true_iff in H.
       eapply carry_before_relay in Hs5; [ idtac | eassumption ].
       simpl in Hs5; rewrite Hs5, H5 in H; discriminate H.

     eapply min_neq_lt in M6; [ idtac | eauto  | left; auto ].
     destruct (eq_nat_dec di5 m) as [M5| M5].
      move M5 at top; subst di5.
      remember H3 as H; clear HeqH.
      rewrite Hn6 in H; [ idtac | assumption ].
      apply negb_true_iff in H.
      rewrite H5 in H; move H at top; subst u.
      remember Ht3 as H; clear HeqH.
      unfold rm_add_i in H.
      rewrite H5, Ht5, xorb_false_l in H.
      rename H into Ryzm.
      destruct (eq_nat_dec di4 m) as [M4| M4].
       move M4 at top; subst di4.
       remember H4 as H; clear HeqH.
       unfold rm_add_i in H.
       rewrite H3, H5, xorb_true_l in H.
       apply negb_false_iff in H.
       rewrite <- Nat.add_succ_l in H.
       erewrite carry_before_relay in H; try eassumption.
       simpl in H; rewrite H6 in H; discriminate H.

       eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
       pose proof (Hn4 m M4) as H.
       rewrite Ht5 in H; simpl in H.
       rename H into ABm.
       remember ABm as H; clear HeqH.
       unfold rm_add_i in H.
       rewrite H3, H5, xorb_true_l in H.
       apply negb_true_iff in H.
       rename H into Rxym.
       remember Hs4 as H; clear HeqH.
       eapply carry_before_relay in H; [ idtac | eassumption ].
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
      eapply carry_before_relay in H; [ idtac | eassumption ].
      simpl in H; rewrite H5 in H.
      rename H into Ryzm.
      remember Ht3 as H; clear HeqH.
      unfold rm_add_i in H.
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
       unfold rm_add_i in H.
       rewrite H3, Bm, xorb_false_r, xorb_true_l in H.
       apply negb_false_iff in H.
       rewrite <- Nat.add_succ_l in H.
       erewrite carry_before_relay in H; try eassumption.
       simpl in H; rewrite H6 in H; discriminate H.

    eapply min_neq_lt in M3; [ idtac | eauto  | right; left; auto ].
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      remember H4 as H; clear HeqH.
      unfold rm_add_i in H.
      rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_relay in H; [ idtac | eassumption ].
      simpl in H; rewrite H3 in H.
      rename H into A_BCm.
      pose proof (Hn3 m M3) as H.
      rewrite H6 in H.
      apply negb_sym in H.
      unfold rm_add_i in H.
      rewrite Ht6, Ht4, xorb_false_r in H.
      apply xorb_move_l_r_1 in H.
      rewrite negb_xorb_diag_r in H.
      rename H into BCm.
      exfalso; eapply case_1; eassumption.

      eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       exists m; exists (negb u).
       split.
        rewrite <- Nat.add_succ_l.
        erewrite carry_before_relay; eassumption.

        split.
         rewrite <- Nat.add_succ_l.
         erewrite carry_before_relay; eassumption.

         split.
          pose proof (Hn3 m M3) as H.
          unfold rm_add_i in H.
          rewrite H6, Ht6, Ht5, xorb_nilpotent, xorb_false_l in H.
          apply negb_sym; assumption.

          split.
           pose proof (Hn4 m M4) as H.
           unfold rm_add_i in H.
           rewrite H6, Ht6, Ht5, xorb_nilpotent, xorb_false_l in H.
           assumption.

           intros dj Hdj; apply Hn4.
           eapply le_lt_trans; eassumption.

       eapply min_neq_lt in M5; [ idtac | eauto  | do 3 right; left; auto ].
       exists m, u.
       split.
        rewrite <- Nat.add_succ_l.
        erewrite carry_before_relay; eassumption.

        split.
         rewrite <- Nat.add_succ_l.
         erewrite carry_before_relay; eassumption.

         split.
          pose proof (Hn3 m M3) as H.
          unfold rm_add_i in H.
          rewrite Hn5 in H; [ idtac | assumption ].
          rewrite negb_xorb_diag_l in H.
          rewrite H6, negb_involutive in H.
          symmetry; assumption.

          split.
           pose proof (Hn4 m M4) as H.
           unfold rm_add_i in H.
           rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
           rewrite <- Hn5 in H; [ idtac | assumption ].
           rewrite Ht6 in H; assumption.

           intros dj Hdj; apply Hn4.
           eapply le_lt_trans; eassumption.

     eapply min_neq_lt in M6; [ idtac | eauto  | left; auto ].
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      remember H4 as H; clear HeqH.
      unfold rm_add_i in H.
      rewrite Hn6 in H; [ idtac | assumption ].
      rewrite negb_xorb_diag_l, xorb_true_l in H.
      apply negb_false_iff in H.
      rename H into Rxym.
      remember Hs6 as H; clear HeqH.
      eapply carry_before_relay in H; [ idtac | eassumption ].
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
       unfold rm_add_i in H.
       rewrite Bm, Ht4, xorb_true_l in H.
       apply negb_true_iff in H.
       rewrite <- Nat.add_succ_l in H.
       erewrite carry_before_relay in H; try eassumption.
       simpl in H; rewrite H5 in H; discriminate H.

      eapply min_neq_lt in M4; eauto ; try (do 2 right; left; auto).
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       exists m, u.
       split.
        rewrite <- Nat.add_succ_l.
        erewrite carry_before_relay; eassumption.

        split.
         rewrite <- Nat.add_succ_l.
         erewrite carry_before_relay; eassumption.

         split.
          pose proof (Hn3 m M3) as H.
          unfold rm_add_i in H.
          rewrite Hn6 in H; [ idtac | assumption ].
          rewrite H5, Ht5, xorb_nilpotent, xorb_false_l in H.
          apply negb_sym in H.
          rewrite negb_involutive in H; assumption.

          split.
           pose proof (Hn4 m M4) as H.
           unfold rm_add_i in H.
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
     unfold rm_add_i in H.
     rewrite Hn5 in H; [ idtac | assumption ].
     rewrite negb_xorb_diag_l, xorb_true_l in H.
     apply negb_true_iff in H.
     rewrite <- Nat.add_succ_l in H.
     erewrite carry_before_relay in H; try eassumption.
     simpl in H; rewrite H5 in H; discriminate H.

    eapply min_neq_lt in M3; eauto ; try (right; left; auto).
    destruct (eq_nat_dec di5 m) as [M5| M5].
     move M5 at top; subst di5.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      rewrite Ht5 in Ht4; discriminate Ht4.

      eapply min_neq_lt in M4; eauto ; try (do 2 right; left; auto).
      exists m, true.
      split.
       rewrite <- Nat.add_succ_l.
       erewrite carry_before_relay; eassumption.

       split.
        rewrite <- Nat.add_succ_l.
        erewrite carry_before_relay; eassumption.

        split.
         pose proof (Hn3 m M3) as H.
         unfold rm_add_i in H.
         rewrite Hn6 in H.
         rewrite H5, Ht5, xorb_false_l in H.
         apply negb_sym in H; rewrite negb_involutive in H.
         assumption.

         split.
          pose proof (Hn4 m M4) as H.
          unfold rm_add_i in H.
          rewrite Hn6 in H.
          rewrite negb_xorb_diag_l, xorb_true_l, Ht5 in H.
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
      unfold rm_add_i in H.
      rewrite Bm, Ht4, xorb_true_l in H.
      apply negb_true_iff in H.
      rewrite <- Nat.add_succ_l in H.
      erewrite carry_before_relay in H; try eassumption.
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
    unfold rm_add_i in H.
    rewrite Hn5, negb_xorb_diag_l, xorb_true_l in H.
    apply negb_true_iff in H.
    rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay in H; [ idtac | assumption ].
    discriminate H.

    eapply min_neq_lt in M3; eauto ; try (right; left; auto).
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      remember H4 as H; clear HeqH.
      unfold rm_add_i in H.
      rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_relay in H; [ idtac | eassumption ].
      simpl in H; rewrite H3 in H.
      rename H into A_BCm.
      pose proof (Hn3 m M3) as H.
      rewrite H6 in H.
      apply negb_sym in H.
      unfold rm_add_i in H.
      rewrite Ht6, Ht4, xorb_false_r in H.
      apply xorb_move_l_r_1 in H.
      rewrite negb_xorb_diag_r in H.
      rename H into BCm.
      exfalso; eapply case_1; eassumption.

      eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
      exists m, true.
      split.
       rewrite <- Nat.add_succ_l.
       clear H6.
       erewrite carry_before_relay; eassumption.

       split.
        rewrite <- Nat.add_succ_l.
        erewrite carry_before_relay; eassumption.

        split.
         pose proof (Hn3 m M3) as H.
         unfold rm_add_i in H.
         rewrite H6, Hn5, negb_xorb_diag_l, negb_involutive in H.
         symmetry; assumption.

         split.
          pose proof (Hn4 m M4) as H.
          unfold rm_add_i in H.
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
      unfold rm_add_i in H.
      rewrite Bm, Ht4, xorb_true_l in H.
      apply negb_true_iff in H.
      rewrite <- Nat.add_succ_l in H.
      rewrite carry_before_inf_relay in H; [ idtac | assumption ].
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
    unfold rm_add_i in H.
    rewrite Hn5, negb_xorb_diag_l, xorb_true_l in H.
    apply negb_true_iff in H.
    rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay in H; [ idtac | assumption ].
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
     unfold rm_add_i in H.
     rewrite Bm, Ht4, xorb_true_l in H.
     apply negb_true_iff in H.
     rewrite <- Nat.add_succ_l in H.
     rewrite carry_before_inf_relay in H; [ idtac | assumption ].
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
      unfold rm_add_i in H.
      rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_inf_relay in H; simpl in H.
      rename H into A_BCm.
      pose proof (Hn3 m) as H.
      rewrite H6 in H.
      apply negb_sym in H.
      unfold rm_add_i in H.
      rewrite Ht6, Ht4, xorb_false_r in H.
      apply xorb_move_l_r_1 in H.
      rewrite negb_xorb_diag_r in H.
      rename H into BCm.
      exfalso; eapply case_1; eassumption.

      eapply min_neq_lt in M6; eauto ; try (left; auto).
      remember H4 as H; clear HeqH.
      unfold rm_add_i in H.
      rewrite Hn6 in H; [ idtac | assumption ].
      rewrite negb_xorb_diag_l, xorb_true_l in H.
      apply negb_false_iff in H.
      rewrite <- Nat.add_succ_l in H.
      erewrite carry_before_relay in H; try eassumption.
      simpl in H; rewrite H6 in H; discriminate H.

     eapply min_neq_lt in M4; eauto ; try (right; left; auto).
     destruct (eq_nat_dec di6 m) as [M6| M6].
      move M6 at top; subst di6.
      exists m, (negb u).
      split.
       rewrite <- Nat.add_succ_l.
       rewrite carry_before_inf_relay; [ idtac | assumption ].
       reflexivity.

       split.
        rewrite <- Nat.add_succ_l.
        erewrite carry_before_relay; eassumption.

        split.
         pose proof (Hn3 m) as H.
         unfold rm_add_i in H.
         rewrite H6, H5, Ht5, xorb_nilpotent, xorb_false_l in H.
         apply negb_sym in H; assumption.

         split.
          pose proof (Hn4 m M4) as H.
          unfold rm_add_i in H.
          rewrite H6, H5, Ht5, xorb_nilpotent, xorb_false_l in H.
          assumption.

          intros dj Hdj; apply Hn4.
          eapply le_lt_trans; eassumption.

      eapply min_neq_lt in M6; eauto ; try (left; auto).
      exists m, u.
      split.
       rewrite <- Nat.add_succ_l.
       rewrite carry_before_inf_relay; [ idtac | assumption ].
       reflexivity.

       split.
        rewrite <- Nat.add_succ_l.
        erewrite carry_before_relay; eassumption.

        split.
         pose proof (Hn3 m) as H.
         unfold rm_add_i in H.
         rewrite Hn6 in H; [ idtac | assumption ].
         rewrite H5, Ht5, xorb_nilpotent, xorb_false_l in H.
         apply negb_sym in H; rewrite negb_involutive in H.
         assumption.

         split.
          pose proof (Hn4 m M4) as H.
          unfold rm_add_i in H.
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
      unfold rm_add_i in H.
      rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_inf_relay in H; simpl in H.
      rename H into A_BCm.
      pose proof (Hn3 m) as H.
      rewrite H6 in H.
      apply negb_sym in H.
      unfold rm_add_i in H.
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
      unfold rm_add_i in H.
      rewrite Bm, Ht4, xorb_true_l in H.
      apply negb_true_iff in H.
      rewrite <- Nat.add_succ_l in H.
      erewrite carry_before_relay in H; try eassumption.
      simpl in H; rewrite H5 in H; move H at top; subst u.
      remember H4 as H; clear HeqH.
      unfold rm_add_i in H.
      rewrite Am, Bm, xorb_true_l in H.
      apply negb_false_iff in H.
      rewrite <- Nat.add_succ_l in H.
      erewrite carry_before_relay in H; try eassumption.
      simpl in H; rewrite H6 in H; discriminate H.

     eapply min_neq_lt in M4; eauto ; try (right; left; auto).
     destruct (eq_nat_dec di6 m) as [M6| M6].
      move M6 at top; subst di6.
      exists m, u.
      split.
       rewrite <- Nat.add_succ_l.
       rewrite carry_before_inf_relay; [ idtac | assumption ].
       reflexivity.

       split.
        rewrite <- Nat.add_succ_l.
        erewrite carry_before_relay; eassumption.

        split.
         pose proof (Hn3 m) as H.
         unfold rm_add_i in H.
         rewrite Hn5 in H; [ idtac | assumption ].
         rewrite H6, negb_xorb_diag_l, negb_involutive in H.
         symmetry; assumption.

         split.
          pose proof (Hn4 m M4) as H.
          unfold rm_add_i in H.
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
     split.
      rewrite <- Nat.add_succ_l.
      rewrite carry_before_inf_relay; [ idtac | assumption ].
      reflexivity.

      split.
       rewrite <- Nat.add_succ_l.
       erewrite carry_before_relay; eassumption.

       split.
        pose proof (Hn3 m) as H.
        unfold rm_add_i in H.
        rewrite Hn6, H5, Ht5, xorb_true_r, xorb_false_l in H.
        apply negb_sym in H; assumption.

        split.
         pose proof (Hn4 m M4) as H.
         unfold rm_add_i in H.
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
     unfold rm_add_i in H.
     rewrite Bm, Ht4, xorb_true_l in H.
     apply negb_true_iff in H.
     rewrite <- Nat.add_succ_l in H.
     erewrite carry_before_relay in H; try eassumption.
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
     unfold rm_add_i in H.
     rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
     rename H into ABm.
     remember Hs3 as H; clear HeqH.
     eapply carry_before_inf_relay in H; simpl in H.
     rename H into A_BCm.
     pose proof (Hn3 m) as H.
     rewrite H6 in H.
     apply negb_sym in H.
     unfold rm_add_i in H.
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
     unfold rm_add_i in H.
     rewrite Bm, Ht4, xorb_true_l in H.
     apply negb_true_iff in H.
     rewrite <- Nat.add_succ_l in H.
     rewrite carry_before_inf_relay in H; [ idtac | assumption ].
     discriminate H.

    eapply min_neq_lt in M4; eauto ; try (right; left; auto).
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     exists m, true.
     split.
      rewrite <- Nat.add_succ_l.
      rewrite carry_before_inf_relay; [ idtac | assumption ].
      reflexivity.

      split.
       rewrite <- Nat.add_succ_l.
       erewrite carry_before_relay; eassumption.

       split.
        pose proof (Hn3 m) as H.
        unfold rm_add_i in H.
        rewrite H6, Hn5, negb_xorb_diag_l, negb_involutive in H.
        symmetry; assumption.

        split.
         pose proof (Hn4 m M4) as H.
         unfold rm_add_i in H.
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
   unfold rm_add_i in H.
   rewrite Bm, Ht4, xorb_true_l in H.
   apply negb_true_iff in H.
   rewrite <- Nat.add_succ_l in H.
   rewrite carry_before_inf_relay in H; [ idtac | assumption ].
   discriminate H.
Qed.

Theorem case_3 : ∀ x0 y0 z0 x y z i u,
  x = (x0 + 0)%rm
  → y = (y0 + 0)%rm
  → z = (z0 + 0)%rm
  → carry (x + (y + z)%rm) 0 i = false
  → carry ((x + y)%rm + z) 0 i = false
  → carry x (y + z) i = true
  → carry (x + y) z i = false
  → carry y z i = u
  → carry x y i = u
  → False.
Proof.
intros x0 y0 z0 x y z i u Ha0 Hb0 Hc0 Hc1 Hc2 Hc3 Hc4 Hc5 Hc6.
clear Ha0 Hb0 Hc0 Hc1 Hc2.
remember Hc4 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (x + y) z (S i)) as s eqn:Hs .
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
bbb.

remember Hc4 as H; clear HeqH.
unfold carry in H; simpl in H.
rewrite Hs4 in H; rename H into H4.
remember Hc3 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x (y + z) (S i)) as s3 eqn:Hs3 .
symmetry in Hs3; rename H into H3.
remember Hc5 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same y z (S i)) as s5 eqn:Hs5 .
symmetry in Hs5; rename H into H5.
remember Hc6 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x y (S i)) as s6 eqn:Hs6 .
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
       unfold rm_add_i in H.
       rewrite Ht6, Ht4, xorb_true_l in H.
       apply negb_true_iff in H.
       rewrite <- Nat.add_succ_l in H.
       erewrite carry_before_relay in H; try eassumption.
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
       unfold rm_add_i in H; simpl in H.
       rewrite H3, H5, xorb_nilpotent, xorb_false_l in H.
       rename H into Hcxym.
       remember Ht3 as H; clear HeqH.
       unfold rm_add_i in H.
       rewrite H5, Ht5, xorb_nilpotent, xorb_false_l in H.
       rename H into Hcyzm.
       remember Hcxym as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same x y (S (S (i + m)))) as sxym eqn:Hsxym .
       destruct sxym as [djxym| ]; [ idtac | discriminate H ].
       symmetry in Hsxym.
       rename H into Haxym.
       remember Hs4 as H; clear HeqH.
       eapply carry_before_relay in H; [ idtac | eassumption ].
       simpl in H; rewrite H4 in H.
       rename H into Hxycm.
       eapply case_2; eassumption.

       eapply min_neq_lt in M5; [ idtac | eauto  | do 3 right; left; auto ].
       remember Ht3 as H; clear HeqH.
       unfold rm_add_i in H.
       rewrite Hn5 in H; [ idtac | assumption ].
       rewrite negb_xorb_diag_l, xorb_true_l in H.
       apply negb_true_iff in H.
       eapply carry_before_relay in Hs5; [ idtac | eassumption ].
       simpl in Hs5; rewrite Hs5, H5 in H; discriminate H.

     eapply min_neq_lt in M6; [ idtac | eauto  | left; auto ].
     destruct (eq_nat_dec di5 m) as [M5| M5].
      move M5 at top; subst di5.
      remember H3 as H; clear HeqH.
      rewrite Hn6 in H; [ idtac | assumption ].
      apply negb_true_iff in H.
      rewrite H5 in H; move H at top; subst u.
      remember Ht3 as H; clear HeqH.
      unfold rm_add_i in H.
      rewrite H5, Ht5, xorb_false_l in H.
      rename H into Ryzm.
      destruct (eq_nat_dec di4 m) as [M4| M4].
       move M4 at top; subst di4.
       remember H4 as H; clear HeqH.
       unfold rm_add_i in H.
       rewrite H3, H5, xorb_true_l in H.
       apply negb_false_iff in H.
       rewrite <- Nat.add_succ_l in H.
       erewrite carry_before_relay in H; try eassumption.
       simpl in H; rewrite H6 in H; discriminate H.

       eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
       pose proof (Hn4 m M4) as H.
       rewrite Ht5 in H; simpl in H.
       rename H into ABm.
       remember ABm as H; clear HeqH.
       unfold rm_add_i in H.
       rewrite H3, H5, xorb_true_l in H.
       apply negb_true_iff in H.
       rename H into Rxym.
       remember Hs4 as H; clear HeqH.
       eapply carry_before_relay in H; [ idtac | eassumption ].
       simpl in H; rewrite H4 in H.
       rename H into Rxy_zm.
       eapply case_2; try eassumption.

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
      eapply carry_before_relay in H; [ idtac | eassumption ].
      simpl in H; rewrite H5 in H.
      rename H into Ryzm.
      remember Ht3 as H; clear HeqH.
      unfold rm_add_i in H.
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
       unfold rm_add_i in H.
       rewrite H3, Bm, xorb_false_r, xorb_true_l in H.
       apply negb_false_iff in H.
       rewrite <- Nat.add_succ_l in H.
       erewrite carry_before_relay in H; try eassumption.
       simpl in H; rewrite H6 in H; discriminate H.

    eapply min_neq_lt in M3; [ idtac | eauto  | right; left; auto ].
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      remember H4 as H; clear HeqH.
      unfold rm_add_i in H.
      rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_relay in H; [ idtac | eassumption ].
      simpl in H; rewrite H3 in H.
      rename H into A_BCm.
      pose proof (Hn3 m M3) as H.
      rewrite H6 in H.
      apply negb_sym in H.
      unfold rm_add_i in H.
      rewrite Ht6, Ht4, xorb_false_r in H.
      apply xorb_move_l_r_1 in H.
      rewrite negb_xorb_diag_r in H.
      rename H into BCm.
      eapply case_1; eassumption.

      eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
bbb.

      i  i+1  -   m
   y  .   .   .   1
u         ≠   ≠   ≠+1
   x  .   u   u   0
1         ≠   ≠   ≠   ≠ …
 y+z  .   .   .   1

 x+y  .   .   .   0
0         ≠   ≠
   z  .   u   u   0
u         ≠   ≠   ≠+1
   y  .   .   .   1

*)

Theorem rm_add_assoc : ∀ x y z, (x + (y + z) = (x + y) + z)%rm.
Proof.
intros x y z.
apply rm_add_assoc_norm.
rename x into x0; rename y into y0; rename z into z0.
remember (x0 + 0)%rm as x.
remember (y0 + 0)%rm as y.
remember (z0 + 0)%rm as z.
unfold rm_eq; intros i; simpl.
unfold rm_add_i; simpl.
do 2 rewrite xorb_false_r.
remember (carry (x + (y + z))%rm 0%rm i) as c1 eqn:Hc1 .
remember (carry (x + y + z)%rm 0%rm i) as c2 eqn:Hc2 .
unfold rm_add_i; simpl.
remember (carry x (y + z)%rm i) as c3 eqn:Hc3 .
remember (carry (x + y)%rm z i) as c4 eqn:Hc4 .
unfold rm_add_i; simpl.
remember (carry y z i) as c5 eqn:Hc5 .
remember (carry x y i) as c6 eqn:Hc6 .
do 8 rewrite xorb_assoc; f_equal; f_equal; symmetry.
rewrite xorb_comm, xorb_assoc; f_equal; symmetry.
rewrite <- xorb_assoc.
symmetry in Hc1, Hc2, Hc3, Hc4, Hc5, Hc6.
move c2 before c1; move c3 before c2.
move c4 before c3; move c5 before c4.
move c6 before c5.
remember Hc1 as H; clear HeqH.
erewrite carry_sum_3_norm_assoc_r in H; try eassumption.
move H at top; subst c1.
remember Hc2 as H; clear HeqH.
erewrite carry_sum_3_norm_assoc_l in H; try eassumption.
move H at top; subst c2.
do 2 rewrite xorb_false_r.
destruct c3, c4, c5, c6; try reflexivity; exfalso.
 eapply case_1; eassumption.

 apply case_1 with (x := z) (y := y) (z := x) (i := i).
  rewrite carry_comm.
  rewrite carry_compat_r with (x := (x + y)%rm); [ assumption | idtac ].
  apply rm_add_i_comm.

  rewrite carry_comm; assumption.

  rewrite carry_comm; assumption.

 Focus 5.
 eapply case_2 with (x := x) (y := y); eassumption.

 Focus 5.
 apply case_2 with (x := z) (y := y) (z := x) (i := i).
  rewrite carry_compat_r with (x := (y + z)%rm).
   rewrite carry_comm; assumption.

   apply rm_add_i_comm.

  rewrite carry_comm; assumption.

  rewrite carry_comm; assumption.

 eapply case_3 with (x := x) (y := y); eassumption.

bbb.
 apply case_1 with (z := x) (y := y) (x := z) (i := i).
  rewrite carry_compat_r with (x := (x + y + z)%rm); [ assumption | idtac ].
  intros j; simpl; symmetry.
  rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_compat_r with (x := (x + (y + z))%rm); [ assumption | idtac ].
  intros j; simpl; rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_comm.
  rewrite carry_compat_r with (x := (x + y)%rm); [ assumption | idtac ].
  apply rm_add_i_comm.

  rewrite carry_comm; assumption.

  rewrite carry_comm; assumption.

 eapply case_2; eassumption.

 eapply case_3; eassumption.

 apply case_2 with (z := x) (y := y) (x := z) (i := i).
  rewrite carry_compat_r with (x := (x + y + z)%rm); [ assumption | idtac ].
  intros j; simpl; symmetry.
  rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_compat_r with (x := (x + (y + z))%rm); [ assumption | idtac ].
  intros j; simpl; rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_comm.
  rewrite carry_compat_r with (x := (x + y)%rm); [ assumption | idtac ].
  apply rm_add_i_comm.

  rewrite carry_compat_r with (x := (y + z)%rm).
   rewrite carry_comm; assumption.

   apply rm_add_i_comm.

  rewrite carry_comm; assumption.

  rewrite carry_comm; assumption.

 apply case_3 with (z := x) (y := y) (x := z) (i := i).
  rewrite carry_compat_r with (x := (x + y + z)%rm); [ assumption | idtac ].
  intros j; simpl; symmetry.
  rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_compat_r with (x := (x + (y + z))%rm); [ assumption | idtac ].
  intros j; simpl; rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_comm.
  rewrite carry_compat_r with (x := (x + y)%rm); [ assumption | idtac ].
  apply rm_add_i_comm.

  rewrite carry_compat_r with (x := (y + z)%rm).
   rewrite carry_comm; assumption.

   apply rm_add_i_comm.

  rewrite carry_comm; assumption.

  rewrite carry_comm; assumption.

 eapply case_4; eassumption.

 apply case_4 with (z := x) (y := y) (x := z) (i := i).
  rewrite carry_compat_r with (x := (x + y + z)%rm); [ assumption | idtac ].
  intros j; simpl; symmetry.
  rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_compat_r with (x := (x + (y + z))%rm); [ assumption | idtac ].
  intros j; simpl; rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_comm.
  rewrite carry_compat_r with (x := (x + y)%rm); [ assumption | idtac ].
  apply rm_add_i_comm.

  rewrite carry_compat_r with (x := (y + z)%rm).
   rewrite carry_comm; assumption.

   apply rm_add_i_comm.

  rewrite carry_comm; assumption.

  rewrite carry_comm; assumption.

 eapply case_5; eassumption.

 eapply case_5; eassumption.

 eapply case_5; eassumption.

 eapply case_5; eassumption.

 Focus 5.
 eapply case_6; eassumption.

 Focus 5.
 eapply case_6; eassumption.

 Focus 7.
 eapply case_6; eassumption.

 Focus 7.
 eapply case_6; eassumption.

 eapply case_7; eassumption.
bbb.

Theorem rm_add_assoc_hop : ∀ x y z, (x + (y + z) = (x + y) + z)%rm.
Proof.
intros x y z.
assert (∀ x, (x = x + 0)%rm) as Hx by (symmetry; apply rm_add_0_r).
setoid_replace (y + z)%rm with (y + z + 0)%rm by apply Hx.
setoid_replace (x + y)%rm with (x + y + 0)%rm by apply Hx.
setoid_replace x with (x + 0)%rm by apply Hx.
setoid_replace y with (y + 0)%rm by apply Hx.
setoid_replace z with (z + 0)%rm by apply Hx.
set (a1 := (x + 0)%rm).
set (b1 := (y + 0)%rm).
set (c1 := (z + 0)%rm).
rename x into x0; rename y into y0; rename z into z0.
rename a1 into x; rename b1 into y; rename c1 into z.
unfold rm_eq; intros i; simpl.
rewrite rm_add_add2_i; symmetry.
rewrite rm_add_add2_i; symmetry.
unfold rm_add2_i; simpl.
do 2 rewrite xorb_false_r.
remember (carry (x + (y + z + 0))%rm 0%rm i) as c1 eqn:Hc1 .
remember (carry (x + y + 0 + z)%rm 0%rm i) as c2 eqn:Hc2 .
rewrite rm_add_add2_i; symmetry.
rewrite rm_add_add2_i; symmetry.
unfold rm_add2_i; simpl.
remember (carry x (y + z + 0)%rm i) as c3 eqn:Hc3 .
remember (carry (x + y + 0)%rm z i) as c4 eqn:Hc4 .
rewrite rm_add_add2_i; symmetry.
rewrite rm_add_add2_i; symmetry.
unfold rm_add2_i; simpl.
do 2 rewrite xorb_false_r.
remember (carry x0 0%rm i) as c5 eqn:Hc5 .
bbb.

Theorem rm_add_assoc_ini : ∀ x y z, (x + (y + z) = (x + y) + z)%rm.
Proof.
intros x y z.
assert (∀ x, (x = x + 0)%rm) as Hx by (symmetry; apply rm_add_0_r).
setoid_replace (y + z)%rm with (y + z + 0)%rm by apply Hx.
setoid_replace (x + y)%rm with (x + y + 0)%rm by apply Hx.
setoid_replace x with (x + 0)%rm by apply Hx.
setoid_replace y with (y + 0)%rm by apply Hx.
setoid_replace z with (z + 0)%rm by apply Hx.
set (a1 := (x + 0)%rm).
set (b1 := (y + 0)%rm).
set (c1 := (z + 0)%rm).
rename x into x0; rename y into y0; rename z into z0.
rename a1 into x; rename b1 into y; rename c1 into z.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
remember (fst_same (x + (y + z + 0)%rm) 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 remember (fst_same ((x + y + 0)%rm + z) 0 si) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [di2| ].
  Focus 2.
  destruct (bool_dec ((x + y + 0)%rm) .[ si] z .[ si]) as [H1| H1].
   apply rm_add_inf_true_eq_if in Hs2; auto; simpl in Hs2.
   destruct Hs2 as (Hxy, Hc).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

   apply neq_negb in H1.
   apply rm_add_inf_true_neq_if in Hs2; auto; simpl in Hs2.
   destruct Hs2 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

  Focus 2.
  destruct (bool_dec x .[ si] ((y + z + 0)%rm) .[ si]) as [H1| H1].
   apply rm_add_inf_true_eq_if in Hs1; auto; simpl in Hs1.
   destruct Hs1 as (Ha, Hyz).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

   apply neq_negb in H1.
   apply rm_add_inf_true_neq_if in Hs1; auto; simpl in Hs1.
   destruct Hs1 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

 destruct Hs1 as (Hn1, Hs1); rewrite Hs1, xorb_false_r.
 destruct Hs2 as (Hn2, Hs2); rewrite Hs2, xorb_false_r.
 clear di1 Hn1 Hs1 di2 Hn2 Hs2.
 unfold rm_add_i, carry; rewrite <- Heqsi; simpl.
 remember (rm_add_i x0 0 i) as xai eqn:Hxai .
 remember (rm_add_i (y + z) 0 i) as xyzi eqn:Hxyzi .
 remember (rm_add_i (x + y) 0 i) as xxyi eqn:Hxxyi .
 remember (rm_add_i z0 0 i) as xci eqn:Hxci .
 remember y .[ i] as xbi eqn:Hxbi ; simpl in Hxbi.
 symmetry in Hxai, Hxyzi, Hxxyi, Hxci, Hxbi.
 remember (fst_same x (y + z + 0)%rm si) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Hxyzs).
  remember (rm_add_i x0 0 (si + di1)) as xas eqn:Hxas .
  symmetry in Hxas, Hxyzs.
  remember (fst_same (x + y + 0)%rm z si) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s2 as [di2| ].
   destruct Hs2 as (Hn2, Hxxys); rewrite Hxxys.
   remember (rm_add_i z0 0 (si + di2)) as xcs eqn:Hxcs .
   symmetry in Hxcs.
   move Hxai at bottom; move Hxas at bottom.
   move Hxci at bottom; move Hxcs at bottom.
   move Hxxyi at bottom; move Hxxys at bottom.
   move Hxyzi at bottom; move Hxyzs at bottom.
   move Hxbi at bottom.
(*1-*)
   remember Hxxyi as H; clear HeqH.
   subst x y.
   rewrite rm_add_i_norm_norm in H.
   set (x := (x0 + 0)%rm) in *.
   set (y := (y0 + 0)%rm) in *.
   move y before Hx; move x before Hx.
   rename H into Hxyi.
   remember Hxyi as H; clear HeqH.
   unfold rm_add_i, carry in H.
   rewrite <- Heqsi in H; simpl in H.
   rewrite Hxai, Hxbi in H.
   remember (fst_same x y si) as s3 eqn:Hs3 .
   apply fst_same_sym_iff in Hs3; simpl in Hs3.
   destruct s3 as [di3| ].
    destruct Hs3 as (Hn3, Hb3).
    symmetry in Hb3.
    apply xorb_move_l_r_1 in H.
    rewrite H in Hb3; rename H into Ha3.
    move Ha3 after Hb3; move Hn3 after Hxai.
    remember Hxyzi as H; clear HeqH.
    subst y z.
    rewrite rm_add_i_norm_norm in H.
    set (y := (y0 + 0)%rm) in *.
    set (z := (z0 + 0)%rm) in *.
    move z before Hx; move y before Hx.
    remember H as Hyzi; clear HeqHyzi.
    unfold rm_add_i, carry in H.
    rewrite <- Heqsi in H; simpl in H.
    rewrite Hxbi, Hxci in H.
    remember (fst_same y z si) as s4 eqn:Hs4 .
    apply fst_same_sym_iff in Hs4; simpl in Hs4.
    destruct s4 as [di4| ].
     destruct Hs4 as (Hn4, Hc4).
     symmetry in Hc4.
     apply xorb_move_l_r_1 in H.
     rewrite H in Hc4; rename H into Hb4.
     move Hb4 after Hc4; move Hn4 after Hxai.
     move Hyzi before Hxyi.
(*1-*)
     destruct (lt_dec di1 di3) as [H1| H1].
      remember H1 as H; clear HeqH.
      apply Hn3 in H.
      rewrite Hxas in H.
      apply negb_sym in H.
      destruct (lt_dec di3 di4) as [H4| H4].
       remember H4 as H40; clear HeqH40.
       apply Hn4 in H40.
       rewrite Hb3 in H40.
       apply negb_sym in H40.
       assert (di1 < di4) as H2 by omega.
       remember H2 as H20; clear HeqH20.
       apply Hn4 in H20.
       destruct (lt_dec di4 di2) as [H3| H3].
        remember H3 as H30; clear HeqH30.
        apply Hn2 in H30.
        rewrite Hc4 in H30.
        assert (di1 < di2) as H5 by omega.
        remember H5 as H50; clear HeqH50.
        apply Hn2 in H50.
        assert (di3 < di2) as H6 by omega.
        remember H6 as H60; clear HeqH60.
        apply Hn2 in H60.
        rewrite <- H20 in H50.
        rewrite H40 in H60.
        rewrite negb_involutive in H60.
(*
     assert (xas ⊕ xcs = xai ⊕ xxyi ⊕ xci ⊕ xyzi) as Hr.
*)
bbb.

     destruct xai, xas, xci, xcs, xxyi, xyzi; try reflexivity;
      try discriminate Hr.

bbb.
(*1-*)
     destruct xai, xas, xci, xcs, xxyi, xyzi; try reflexivity; exfalso;
      destruct xbi; simpl in Ha3, Hb3, Hb4, Hc4.
      destruct di4.
       clear Hn4.
       rewrite Nat.add_0_r in Hb4, Hc4.
       destruct di3.
        rewrite Nat.add_0_r, Hb4 in Hb3; discriminate Hb3.

        destruct di2.
         rewrite Nat.add_0_r, Hc4 in Hxcs; discriminate Hxcs.

         destruct (lt_dec di2 di3) as [H1| H1].
          remember H1 as H; clear HeqH.
          apply Nat.succ_lt_mono, Hn3 in H.
          unfold rm_add_i, carry in Hxxys.
          rewrite <- Nat.add_succ_l in Hxxys.
          remember (S si) as ssi; simpl in Hxxys.
          rewrite xorb_false_r in Hxxys.
bbb.

(*-1*)
   destruct xai, xas, xci, xcs, xxyi, xyzi; try reflexivity; exfalso;
    destruct xbi, xbs.
    Focus 1.
bbb.
    destruct di2.
     rewrite Nat.add_0_r in Hxcs.
     apply not_true_iff_false in Hxyzi.
     eapply Hxyzi, case_1; eassumption.

     (* cf theorem case_1 *)
bbb.
     apply not_true_iff_false in Hxyzi.
     apply Hxyzi; clear Hxyzi.
     apply eq_true_negb_classical; intros Hxyzi.
     apply negb_true_iff in Hxyzi.
     unfold rm_add_i, carry in Hxyzi.
     rewrite <- Heqsi in Hxyzi; simpl in Hxyzi.
     rewrite xorb_false_r in Hxyzi.
     unfold rm_add_i, carry in Hxyzi at 1.
     rewrite <- Heqsi in Hxyzi; simpl in Hxyzi.
     rewrite Hxbi, Hxci, xorb_true_r in Hxyzi.
     rewrite xorb_false_l in Hxyzi.
     remember (fst_same y z si) as s1 eqn:Hs1 .
     apply fst_same_sym_iff in Hs1; simpl in Hs1.
     destruct s1 as [di3| ].
      destruct Hs1 as (Hn3, Hs3).
      destruct di3.
       rewrite Nat.add_0_r, Hxbs, xorb_true_l in Hxyzi.
       apply negb_false_iff in Hxyzi.
       remember (fst_same (y + z) 0 si) as s2 eqn:Hs2 .
       apply fst_same_sym_iff in Hs2; simpl in Hs2.
       destruct s2 as [di4| ].
        destruct Hs2 as (Hn4, Hs4); rewrite Hs4 in Hxyzi.
        discriminate Hxyzi.

        apply rm_add_inf_true_eq_if in Hs2.
         destruct Hs2 as (Hs2, Hs4); simpl in Hs2, Hs4.
         exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

         rewrite Nat.add_0_r in Hs3; assumption.

       pose proof (Hn3 0 (Nat.lt_0_succ di3)) as H.
       rewrite Nat.add_0_r, Hxbs in H.
       symmetry in H; apply negb_true_iff in H.
       pose proof (Hn2 0 (Nat.lt_0_succ di2)) as H1.
       rewrite Nat.add_0_r, H in H1; simpl in H1.
bbb.
       remember (fst_same (y + z) 0 si) as s4 eqn:Hs4 .
       apply fst_same_sym_iff in Hs4; simpl in Hs4.
       destruct s4 as [di4| ].
        destruct Hs4 as (Hn4, Hs4); rewrite Hs4, xorb_false_r in Hxyzi.
        rewrite Hxyzi in Hs3; symmetry in Hs3.

bbb.
   destruct di1.
    clear Hn1.
    rewrite Nat.add_0_r in Hxas, Hxyzs.
    destruct di2.
     clear Hn2.
     rewrite Nat.add_0_r in Hxcs, Hxxys.
     destruct xai, xas, xci, xcs, xxyi, xyzi; try reflexivity; exfalso;
      destruct bi, bs.
      apply not_true_iff_false in Hxyzi.
      eapply Hxyzi, case_1; eassumption.

      Focus 4.
      apply not_true_iff_false in Hxxyi.
      eapply Hxxyi, case_1; eassumption.
bbb.

Theorem rm_add_assoc : ∀ x y z, (x + (y + z) = (x + y) + z)%rm.
Proof.
intros x y z.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
remember (fst_same (x + (y + z)%rm) 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); rewrite Hs1, xorb_false_r.
 remember (fst_same ((x + y)%rm + z) 0 si) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [di2| ].
  destruct Hs2 as (Hn2, Hs2); rewrite Hs2, xorb_false_r.
bbb.
  unfold rm_add_i, carry.
  rewrite <- Heqsi; simpl.
  remember (fst_same x (y + z) si) as s3 eqn:Hs3 .
  apply fst_same_sym_iff in Hs3; simpl in Hs3.
  destruct s3 as [di3| ].
   destruct Hs3 as (Hn3, Hs3).
   remember (fst_same (x + y) z si) as s4 eqn:Hs4 .
   apply fst_same_sym_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4); rewrite Hs4.
    unfold rm_add_i, carry; rewrite <- Heqsi.
    do 6 rewrite xorb_assoc; f_equal; f_equal.
    symmetry; rewrite xorb_comm.
    rewrite xorb_assoc; f_equal; symmetry.
(*
bbb.
    destruct (lt_dec di3 di4) as [H1| H1].
     remember H1 as H; clear HeqH.
     apply Hn4 in H.
     unfold rm_add_i, carry in Hs3.
     rewrite <- Nat.add_succ_l in Hs3.
     remember (S si) as ssi; simpl in Hs3.
     unfold rm_add_i, carry in H.
     rewrite <- Nat.add_succ_l in H.
     rewrite <- Heqssi in H; simpl in H.
     apply xorb_move_l_r_2 in H.
     rewrite <- negb_xorb_l in H.
     rewrite negb_xorb_r in H.
     apply xorb_move_r_l_1 in H.
     rewrite xorb_comm in H.
     apply xorb_move_r_l_1 in Hs3.
     rewrite xorb_comm in Hs3.
     rewrite <- xorb_assoc in Hs3.
     rewrite Hs3 in H.
bbb.
*)
    remember (fst_same y z si) as s5 eqn:Hs5 .
    apply fst_same_sym_iff in Hs5; simpl in Hs5.
    destruct s5 as [di5| ].
     destruct Hs5 as (Hn5, Hs5).
     remember (fst_same x y si) as s6 eqn:Hs6 .
     apply fst_same_sym_iff in Hs6; simpl in Hs6.
     destruct s6 as [di6| ].
      destruct Hs6 as (Hn6, Hs6).
bbb.

intros x y z.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry.
remember (fst_same x (y + z) (S i)) as s1 eqn:Hs1 .
symmetry in Hs1.
remember (fst_same (x + y) z (S i)) as s2 eqn:Hs2 .
symmetry in Hs2.
apply fst_same_iff in Hs1.
apply fst_same_iff in Hs2.
simpl in Hs1, Hs2; simpl.
destruct s1 as [di1| ].
 destruct Hs1 as (Hs1n, Hs1).
 destruct s2 as [di2| ].
  destruct Hs2 as (Hs2n, Hs2).
  rewrite Hs2.
  unfold rm_add, rm_add_i; simpl.
  remember (fst_same x y (S i)) as s3 eqn:Hs3 .
  remember (fst_same y z (S i)) as s4 eqn:Hs4 .
  symmetry in Hs3, Hs4.
  apply fst_same_iff in Hs3.
  apply fst_same_iff in Hs4.
  simpl in Hs3, Hs4.
  destruct s3 as [di3| ].
   destruct Hs3 as (Hs3n, Hs3).
   destruct s4 as [di4| ].
    destruct Hs4 as (Hs4n, Hs4).
    do 6 rewrite xorb_assoc.
    do 2 f_equal; symmetry.
    rewrite xorb_comm, xorb_assoc; f_equal.
    symmetry in Hs2, Hs4.
    unfold rm_add_i, carry in Hs1, Hs2; simpl in Hs1, Hs2.
    remember (fst_same x y (S (si + di2)))) as s5 eqn:Hs5 .
    remember (fst_same y z (S (si + di1)))) as s6 eqn:Hs6 .
    symmetry in Hs5, Hs6.
    apply fst_same_iff in Hs5.
    apply fst_same_iff in Hs6.
    simpl in Hs5, Hs6.
    destruct s5 as [di5| ].
     destruct s6 as [di6| ].
      destruct Hs5 as (Hs5n, Hs5).
      destruct Hs6 as (Hs6n, Hs6).
      symmetry in Hs6.
      move Hs1 at bottom; move Hs2 at bottom; move Hs3 at bottom.
      move Hs4 at bottom; move Hs5 at bottom; move Hs6 at bottom.
      move di6 before di1; move di5 before di1.
      move di4 before di1; move di3 before di1.
      move di2 before di1.
      move Hs2n after Hs6n; move Hs3n after Hs6n.
      move Hs4n after Hs6n; move Hs5n after Hs6n.
      rewrite xorb_comm.
bbb.
      destruct (lt_dec di3 di4) as [H1| H1].
       remember H1 as H; clear HeqH.
       apply Hs4n in H.
       rewrite <- Hs3 in H.
       Focus 1.
      rewrite Hs1, Hs2.
      rewrite <- Hs4, <- Hs6.
      rewrite Hs3, Hs5.
bbb.
      destruct (lt_dec di1 di2) as [H1| H1].
       remember H1 as H; clear HeqH.
       apply Hs2n in H.
       unfold rm_add_i, carry in H; simpl in H.
       remember (fst_same x y (S (si + di1)))) as s7 eqn:Hs7 .
       symmetry in Hs7.
       apply fst_same_iff in Hs7.
       destruct s7 as [di7| ].
        simpl in Hs7.
        destruct Hs7 as (Hs7n, Hs7).
bbb.
*)

Theorem neq_xorb : ∀ y y', y ≠ y' → y ⊕ y' = true.
Proof.
intros y y' H.
apply not_false_iff_true.
intros H1; apply H.
apply xorb_eq; assumption.
Qed.

Close Scope nat_scope.
