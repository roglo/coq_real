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
Axiom fst_same_iff : ∀ a b i odi, fst_same a b i = odi ↔
  match odi with
  | Some di =>
      (∀ dj, dj < di → a.[i + dj] = negb b.[i + dj])
      ∧ a.[i + di] = b.[i + di]
  | None =>
      ∀ dj, a.[i + dj] = negb b.[i + dj]
  end.

Infix "⊕" := xorb (left associativity, at level 50) : bool_scope.

Definition carry a b i :=
  match fst_same a b (S i) with
  | Some dj => a.[S i + dj]
  | None => true
  end.

Definition rm_add_i a b i := a.[i] ⊕ b.[i] ⊕ carry a b i.
Definition rm_add a b := {| rm := rm_add_i a b |}.
Definition rm_eq a b := ∀ i,
  rm (rm_add a rm_zero) i = rm (rm_add b rm_zero) i.

Delimit Scope rm_scope with rm.
Notation "a + b" := (rm_add a b) (at level 50, left associativity) : rm_scope.
Notation "a = b" := (rm_eq a b) : rm_scope.
Notation "a ≠ b" := (¬ rm_eq a b) : rm_scope.
Notation "0" := rm_zero : rm_scope.

Arguments rm r%rm i%nat.
Arguments carry a%rm b%rm i%nat.
Arguments rm_add_i a%rm b%rm i%nat.
Arguments fst_same a%rm b%rm i%nat.

Definition rm_opp a := {| rm i := negb a.[i] |}.
Definition rm_sub a b := (a + rm_opp b)%rm.

Notation "- a" := (rm_opp a) : rm_scope.
Notation "a - b" := (rm_add a (rm_opp b)) : rm_scope.

Theorem rm_eq_refl : reflexive _ rm_eq.
Proof. intros a i; reflexivity. Qed.

Theorem rm_eq_sym : symmetric _ rm_eq.
Proof. intros a b Hab i; symmetry; apply Hab. Qed.

Theorem rm_eq_trans : transitive _ rm_eq.
Proof. intros a b c Hab Hbc i; rewrite Hab; apply Hbc. Qed.

Add Parametric Relation : _ rm_eq
 reflexivity proved by rm_eq_refl
 symmetry proved by rm_eq_sym
 transitivity proved by rm_eq_trans
 as rm_rel.

Theorem fst_same_sym_iff : ∀ a b i odi,
  odi = fst_same a b i
  ↔ match odi with
    | Some di =>
        (∀ dj : nat, dj < di → a .[ i + dj] = negb b .[ i + dj])
        ∧ a .[ i + di] = b .[ i + di]
    | None => ∀ dj : nat, a .[ i + dj] = negb b .[ i + dj]
    end.
Proof.
intros a b i odi.
split; intros H.
 apply fst_same_iff; symmetry; assumption.

 symmetry; apply fst_same_iff; assumption.
Qed.

Theorem forall_and_distr : ∀ α (P Q : α → Prop),
  (∀ a, P a ∧ Q a) → (∀ a, P a) ∧ (∀ a, Q a).
Proof. intros; split; intros a; apply H. Qed.

Theorem forall_compat : ∀ α (P Q : α → Prop),
  (∀ x, P x → Q x)
  → (∀ x, P x)
  → id (∀ x, Q x).
Proof.
intros α P Q HPQ HP x.
apply HPQ, HP.
Qed.

Theorem forall_add_succ_r : ∀ α i f (a : α),
  (∀ j, f (i + S j) = a)
  → id (∀ j, f (S i + j) = a).
Proof.
intros α i f a; unfold id; intros H j.
rewrite Nat.add_succ_l, <- Nat.add_succ_r; apply H.
Qed.

Theorem forall_add_succ_l : ∀ α i f (a : α),
  (∀ j : nat, f (S (i + j)) = a)
  → id (∀ j : nat, f (S i + j) = a).
Proof.
intros α i f a; unfold id; intros H j.
apply H.
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

Theorem fst_same_comm : ∀ a b i, fst_same a b i = fst_same b a i.
Proof.
intros a b i.
apply fst_same_iff.
remember (fst_same b a i) as sba eqn:Hsba .
symmetry in Hsba.
apply fst_same_iff in Hsba.
destruct sba as [di| ]; [ idtac | intros dj; apply negb_sym, Hsba ].
destruct Hsba as (Hns, Hs).
split; auto.
intros dj Hdjn; apply negb_sym, Hns; assumption.
Qed.

Theorem carry_comm : ∀ a b i, carry a b i = carry b a i.
Proof.
intros a b i.
unfold carry; simpl.
rewrite fst_same_comm.
remember (fst_same b a (S i)) as s eqn:Hs .
destruct s as [di| ]; [ idtac | reflexivity ].
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct Hs; symmetry; assumption.
Qed.

Theorem rm_add_i_comm : ∀ a b i, rm_add_i a b i = rm_add_i b a i.
Proof.
intros a b i.
unfold rm_add_i, carry.
rewrite fst_same_comm.
remember (fst_same b a (S i)) as s eqn:Hs .
symmetry in Hs.
apply fst_same_iff in Hs.
destruct s as [di| ]; [ idtac | f_equal; apply xorb_comm ].
f_equal; [ apply xorb_comm | destruct Hs; auto ].
Qed.

(* TODO: carry_comm to be used *)
Theorem rm_add_comm : ∀ a b, (a + b = b + a)%rm.
Proof.
intros a b.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry; simpl.
do 2 rewrite xorb_false_r.
remember (fst_same (a + b) 0 (S i)) as sab eqn:Hsab .
remember (fst_same (b + a) 0 (S i)) as sba eqn:Hsba .
symmetry in Hsab, Hsba.
apply fst_same_iff in Hsab.
apply fst_same_iff in Hsba.
simpl in Hsab, Hsba.
destruct sab as [diab| ].
 destruct Hsab as (Hnab, Hsab).
 destruct sba as [diba| ].
  destruct Hsba as (Hnba, Hsba).
  rewrite Hsab, Hsba.
  rewrite rm_add_i_comm; reflexivity.

  rewrite xorb_comm, rm_add_i_comm, Hsba.
  rewrite xorb_comm, rm_add_i_comm; reflexivity.

 destruct sba as [diba| ]; [ idtac | rewrite rm_add_i_comm; reflexivity ].
 destruct Hsba as (Hnba, Hsba).
 symmetry; rewrite xorb_comm.
 rewrite rm_add_i_comm, Hsab.
 rewrite rm_add_i_comm, rm_add_i_comm; reflexivity.
Qed.

Theorem rm_add_0_inf_1 : ∀ a i,
  (∀ dj, rm_add_i a 0 (i + dj) = true)
  → id (∀ dk, a .[i + dk] = true).
Proof.
intros a i Hs dk.
revert i Hs.
induction dk; intros.
 rewrite Nat.add_0_r.
 pose proof (Hs 0) as H; simpl in H.
 rewrite Nat.add_0_r in H.
 unfold rm_add_i, carry in H; simpl in H.
 rewrite xorb_false_r in H.
 remember (fst_same a 0 (S i)) as s2 eqn:Hs2 .
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
  remember (fst_same a 0 (S (i + 1))) as s3 eqn:Hs3 .
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

Theorem not_rm_add_0_inf_1 : ∀ a i, ¬ (∀ dj, rm_add_i a 0 (i + dj) = true).
Proof.
intros a i Hs.
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
remember (fst_same a 0 si) as s2 eqn:Hs2 .
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

Theorem not_rm_add_0_inf_1_succ : ∀ a i,
  ¬ (∀ dj, rm_add_i a 0 (i + S dj) = true).
Proof.
intros a i H.
eapply not_rm_add_0_inf_1 with (i := S i); intros dj.
rewrite Nat.add_succ_l, <- Nat.add_succ_r.
apply H.
Qed.

Theorem rm_add_i_0_r : ∀ a i, rm_add_i (a + 0%rm) 0 i = rm_add_i a 0 i.
Proof.
intros a i.
unfold rm_add_i, carry at 1.
remember (S i) as si; simpl.
rewrite xorb_false_r.
remember (fst_same (a + 0%rm) 0 si) as s1 eqn:Hs1 .
symmetry in Hs1.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hs1, xorb_false_r; reflexivity.

 exfalso; eapply not_rm_add_0_inf_1; eauto .
Qed.

Theorem rm_add_0_r : ∀ a, (a + 0 = a)%rm.
Proof.
intros a.
unfold rm_eq.
apply rm_add_i_0_r.
Qed.

Theorem carry_compat_r : ∀ a b c j,
  (∀ i, a .[ i] = b .[ i])
  → carry b c j = carry a c j.
Proof.
intros a b c j Hab.
unfold carry; intros.
remember (fst_same b c (S j)) as s1 eqn:Hs1 .
remember (fst_same a c (S j)) as s2 eqn:Hs2 .
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
   rewrite Hab, Hs1 in H.
   destruct c .[ S (j + di1)]; discriminate H.

   apply Nat.nlt_ge in H1.
   destruct (lt_dec di2 di1) as [H2| H2].
    remember H2 as H; clear HeqH.
    apply Hn1 in H.
    rewrite <- Hab, Hs2 in H.
    destruct c .[ S (j + di2)]; discriminate H.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H1; auto.

  rewrite <- Hab, Hs2 in Hs1.
  destruct c .[ S (j + di1)]; discriminate Hs1.

 destruct s2 as [di2| ]; auto.
 destruct Hs2 as (Hn2, Hs2).
 rewrite Hab, Hs1 in Hs2.
 destruct c .[ S (j + di2)]; discriminate Hs2.
Qed.

Theorem rm_add_i_compat_r : ∀ a b c j,
  (∀ i, a .[ i] = b .[ i])
  → rm_add_i b c j = rm_add_i a c j.
Proof.
intros a b c j Hab.
unfold rm_add_i.
rewrite Hab; f_equal.
apply carry_compat_r; assumption.
Qed.

Theorem rm_norm_eq_eq : ∀ a₀ b₀ a b,
  a = (a₀ + 0)%rm
  → b = (b₀ + 0)%rm
  → (a = b)%rm
  → ∀ i, a .[ i] = b .[ i].
Proof.
intros a₀ b₀ a b Ha Hb Hab i.
unfold rm_eq in Hab; simpl in Hab.
pose proof (Hab i) as Hi.
unfold rm_add_i, carry in Hi.
remember (S i) as si; simpl in Hi.
do 2 rewrite xorb_false_r in Hi.
remember (fst_same a 0 si) as s1 eqn:Hs1 .
remember (fst_same b 0 si) as s2 eqn:Hs2 .
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

Theorem carry_norm_eq_compat_r : ∀ a₀ b₀ a b c n,
  a = (a₀ + 0)%rm
  → b = (b₀ + 0)%rm
  → (a = b)%rm
  → carry (a + c) 0 n = carry (b + c) 0 n.
Proof.
intros a₀ b₀ a b c n Ha Hb Hab.
apply carry_compat_r; simpl.
intros; apply rm_add_i_compat_r.
eapply rm_norm_eq_eq; eassumption.
Qed.

Theorem rm_norm_eq_compat_r : ∀ a₀ b₀ a b c,
  a = (a₀ + 0)%rm
  → b = (b₀ + 0)%rm
  → (a = b)%rm
  → (a + c = b + c)%rm.
Proof.
intros a₀ b₀ a b c Ha Hb Hab.
unfold rm_eq; simpl; intros i.
unfold rm_add_i; simpl.
do 2 rewrite xorb_false_r; f_equal.
 apply rm_add_i_compat_r.
 intros j; symmetry.
 eapply rm_norm_eq_eq; eassumption.

 eapply carry_norm_eq_compat_r; eassumption.
Qed.

Fixpoint first_false_before a i :=
  match i with
  | 0 => None
  | S j => if a.[j] then first_false_before a j else Some j
  end.

Theorem first_false_before_none_iff : ∀ a i,
  first_false_before a i = None
  ↔ (∀ k, k < i → a.[k] = true).
Proof.
intros a i.
split.
 intros Hi k Hki.
 revert k Hki.
 induction i; intros.
  exfalso; revert Hki; apply Nat.nlt_0_r.

  simpl in Hi.
  remember a .[ i] as ai eqn:Hai .
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
 remember a .[ i] as ai eqn:Hai .
 symmetry in Hai.
 destruct ai.
  apply IHi; intros k Hk.
  apply Hki.
  apply Nat.lt_lt_succ_r; assumption.

  apply not_true_iff_false in Hai.
  exfalso; apply Hai, Hki.
  apply Nat.lt_succ_r; reflexivity.
Qed.

Theorem first_false_before_some_iff : ∀ a i j,
  first_false_before a i = Some j
  ↔ j < i ∧
    a.[j] = false ∧
    (∀ k, j < k → k < i → a.[k] = true).
Proof.
intros a i j.
split.
 intros Hij.
 revert j Hij.
 induction i; intros; [ discriminate Hij | idtac ].
 simpl in Hij.
 remember a .[ i] as ai eqn:Hai .
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
 remember a .[ i] as ai eqn:Hai .
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

Theorem no_room_for_infinite_carry : ∀ a b i di1 di2 di3,
  (∀ dj : nat, dj < di2 → rm_add_i a 0 (S i + dj) = negb b .[ S i + dj])
  → (∀ dj : nat, a .[ S (S i) + di2 + dj] = true)
  → (∀ dj : nat, dj < di3 → a .[ S i + dj] = negb b .[ S i + dj])
  → a .[ S i + di2] = true
  → a .[ S i + di1] = false
  → di1 < di2
  → di2 < di3
  → False.
Proof.
intros a b i di1 di2 di3 Hn1 Hs4 Hn2 Hs1 Hs3 H4 H3.
remember (S i) as si.
remember (S si) as ssi.
remember (first_false_before a (si + di2)) as j eqn:Hj .
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
   remember (fst_same a 0 sj) as s7 eqn:Hs7 .
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

Theorem rm_add_inf_true_eq_if : ∀ a b i,
  (∀ di, rm_add_i a b (i + di) = true)
  → a.[i] = b.[i]
  → (∀ di, a.[i + S di] = true) ∧
    (∀ di, b.[i + S di] = true).
Proof.
intros a b i Hdi Hab.
apply forall_and_distr; intros di.
induction di.
 rewrite Nat.add_1_r.
 pose proof (Hdi 0) as H.
 unfold rm_add_i, carry in H.
 rewrite Nat.add_0_r in H.
 remember (S i) as si.
 remember (fst_same a b si) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Hs1).
  rewrite Hab in H.
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
   remember (fst_same a b ssi) as s2 eqn:Hs2 .
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
  remember (fst_same a b ssi) as s2 eqn:Hs2 .
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
 remember (fst_same a b (ssi + di)) as s1 eqn:Hs1 .
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
   remember (fst_same a b (sssi + di)) as s2 eqn:Hs2 .
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
  remember (fst_same a b (sssi + di)) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2.
  destruct s2 as [di2| ]; [ idtac | discriminate H ].
  destruct Hs2 as (Hn2, Hb2).
  rewrite Heqsssi, Nat.add_succ_l in Hb2.
  rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hb2.
  rewrite Hs1 in Hb2.
  destruct b .[ ssi + di + S di2]; discriminate Hb2.
Qed.

Theorem rm_add_inf_true_neq_if : ∀ a b i,
  (∀ di, rm_add_i a b (i + di) = true)
  → a.[i] = negb b.[i]
  → ∃ j,
    i < j ∧
    (∀ di, i + di < j → a.[i + di] = negb b.[i + di]) ∧
    a.[j] = false ∧ b.[j] = false ∧
    (∀ di, a.[j + S di] = true) ∧
    (∀ di, b.[j + S di] = true).
Proof.
intros a b i Hdi Hab.
pose proof (Hdi 0) as H.
rewrite Nat.add_0_r in H.
unfold rm_add_i, carry in H.
remember (S i) as si.
remember (fst_same a b si) as s1 eqn:Hs1 .
symmetry in Hs1.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hab in H.
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
   remember (fst_same a b (ssi + di1)) as s2 eqn:Hs2 .
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
      remember (fst_same a b (sssi + di1 + di)) as s3 eqn:Hs3 .
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
        rename H into Hab3.
        pose proof (Hdi (S (S (S (di1 + di + di3))))) as H.
        do 3 rewrite Nat.add_succ_r in H.
        do 3 rewrite <- Nat.add_succ_l in H.
        rewrite <- Heqsi, <- Heqssi, <- Heqsssi in H.
        do 2 rewrite Nat.add_assoc in H.
        unfold rm_add_i, carry in H.
        rewrite Hab3, negb_xorb_diag_l, xorb_true_l in H.
        do 3 rewrite <- Nat.add_succ_l in H.
        remember (S sssi) as ssssi.
        remember (fst_same a b (ssssi + di1 + di + di3)) as s4 eqn:Hs4 .
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
       remember (fst_same a b (ssssi + di1 + di)) as s4 eqn:Hs4 .
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
        destruct b .[ ssssi + di1 + di + di4]; discriminate H.

        rewrite xorb_true_r in H.
        apply negb_true_iff in H.
        apply xorb_eq in H.
        rename H into Hab1.
        pose proof (Hs3 0) as H.
        rewrite Nat.add_0_r in H.
        rewrite Hab1 in H.
        destruct b .[ sssi + di1 + di]; discriminate H.

     rename H into Ha2.
     rewrite Ha2 in Hs2; symmetry in Hs2.
     pose proof (Hn2 0 (Nat.lt_0_succ di2)) as H.
     rewrite Nat.add_0_r in H.
     rename H into Hab1.
     pose proof (Hdi (S (S di1))) as H.
     do 2 rewrite Nat.add_succ_r in H.
     do 2 rewrite <- Nat.add_succ_l in H.
     rewrite <- Heqsi, <- Heqssi in H.
     unfold rm_add_i, carry in H.
     rewrite Hab1, negb_xorb_diag_l, xorb_true_l in H.
     apply negb_true_iff in H.
     rewrite <- Nat.add_succ_l in H; remember (S ssi) as sssi.
     remember (fst_same a b (sssi + di1)) as s3 eqn:Hs3 .
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
    remember (fst_same a b (sssi + di1)) as s3 eqn:Hs3 .
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

 rewrite Hab, negb_xorb_diag_l in H; discriminate H.
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

Theorem rm_add_inf_true_if : ∀ a b i,
  (∀ di, rm_add_i a b (i + di) = true)
  → ∃ j,
    (∀ dj, a.[i+j+dj] = true) ∧
    (∀ dj, b.[i+j+dj] = true) ∧
    (0 < j → a.[i+pred j] = false) ∧
    (0 < j → b.[i+pred j] = false) ∧
    (fst_same a b i = Some (pred j)).
Proof.
intros a b i Hdi.
destruct (bool_dec a .[ i] b .[ i]) as [H1| H1].
 remember Hdi as H; clear HeqH.
 apply rm_add_inf_true_eq_if in H; auto.
 destruct H as (Ha, Hb).
 remember a .[ i] as x eqn:H2 .
 symmetry in H1, H2.
 destruct x.
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

Theorem rm_add_add_0_l_when_lhs_has_relay : ∀ a b i di1,
  fst_same (a + 0%rm) b (S i) = Some di1
  → rm_add_i (a + 0%rm) b i = rm_add_i a b i.
Proof.
intros a b i di1 Hs1.
unfold rm_add_i, carry at 1; remember (S i) as si; simpl.
rewrite Hs1.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Hs1).
rewrite Hs1.
unfold rm_add_i, carry; rewrite <- Heqsi; simpl.
rewrite xorb_false_r.
remember (fst_same a b si) as s2 eqn:Hs2 .
symmetry in Hs2.
apply fst_same_iff in Hs2; simpl in Hs2.
remember (fst_same a 0 si) as s3 eqn:Hs3 .
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
  remember (fst_same a 0 (ssi + di1)) as s4 eqn:Hs4 .
  symmetry in Hs4.
  apply fst_same_iff in Hs4; simpl in Hs4.
  destruct s4 as [di4| ].
   destruct Hs4 as (Hn4, Hs4).
   rewrite Hs4, xorb_false_r in Hs1.
   destruct (lt_dec di1 di2) as [H1| H1].
    remember H1 as H; clear HeqH.
    apply Hn2 in H.
    rewrite Hs1 in H.
    destruct b .[ si + di1]; discriminate H.

    apply Nat.nlt_ge in H1.
    destruct (lt_dec di2 di1) as [H2| H2].
     remember H2 as H; clear HeqH.
     apply Hn1 in H.
     unfold rm_add_i, carry in H.
     rewrite <- Nat.add_succ_l, <- Heqssi in H.
     simpl in H.
     remember (fst_same a 0 (ssi + di2)) as s5 eqn:Hs5 .
     symmetry in Hs5.
     apply fst_same_iff in Hs5; simpl in Hs5.
     destruct s5 as [di5| ].
      destruct Hs5 as (Hn5, Hs5).
      rewrite xorb_false_r, Hs2, Hs5, xorb_false_r in H.
      destruct b .[ si + di2]; discriminate H.

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
    remember (fst_same a 0 (ssi + di2)) as s5 eqn:Hs5 .
    symmetry in Hs5.
    apply fst_same_iff in Hs5; simpl in Hs5.
    destruct s5 as [di5| ].
     destruct Hs5 as (Hn5, Hs5).
     rewrite xorb_false_r, Hs2, Hs5, xorb_false_r in H.
     destruct b .[ si + di2]; discriminate H.

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
      destruct (bool_dec a .[ si + di2] false) as [H4| H4].
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
        remember (fst_same a 0 (ssi + di3)) as s6 eqn:Hs6 .
        symmetry in Hs6.
        apply fst_same_iff in Hs6; simpl in Hs6.
        destruct s6 as [di6| ]; [ idtac | discriminate H ].
        destruct Hs6 as (Hn6, Hs6).
        clear H.
        remember (first_false_before a (si + di2)) as j eqn:Hj .
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
           remember (fst_same a 0 sj) as s7 eqn:Hs7 .
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
     remember b .[ si + di1] as bi eqn:Hbi .
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
  remember (fst_same a 0 (ssi + di1)) as s4 eqn:Hs4 .
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
  remember (fst_same a 0 (ssi + di1)) as s4 eqn:Hs4 .
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
     remember (fst_same a 0 (ssi + di1)) as s5 eqn:Hs5 .
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
     remember (fst_same a 0 (ssi + di1)) as s5 eqn:Hs5 .
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
   remember (fst_same a 0 (ssi + di1)) as s5 eqn:Hs5 .
   symmetry in Hs5.
   apply fst_same_iff in Hs5; simpl in Hs5.
   destruct s5 as [di5| ].
    destruct Hs5 as (Hn5, Hs5); rewrite Hs5 in Hs1.
    rewrite xorb_false_r in Hs1.
    destruct b .[ si + di1]; discriminate Hs1.

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
      remember (fst_same a 0 (ssi + di3)) as s5 eqn:Hs5 .
      symmetry in Hs5.
      apply fst_same_iff in Hs5; simpl in Hs5.
      destruct s5 as [di5| ].
       destruct Hs5 as (Hn5, Hs5); rewrite Hs5 in H.
       rewrite xorb_false_r in H.
       apply not_true_iff_false; intros Ha.
       subst si ssi.
       eapply no_room_for_infinite_carry in Hs3; eauto .

       rewrite xorb_true_r, <- Hs2 in H.
       destruct a .[ si + di3]; discriminate H.

      apply Nat.nlt_ge in H2.
      apply Nat.le_antisymm in H2; auto.
      subst di3; assumption.

  rewrite xorb_true_r, <- Hs2.
  apply Hs3.
Qed.

Theorem rm_add_add_0_l_when_lhs_has_no_relay : ∀ a b i dj2 dj5,
  fst_same ((a + 0)%rm + b) 0 (S i) = Some dj2
  → fst_same (a + b) 0 (S i) = Some dj5
  → fst_same (a + 0%rm) b (S i) = None
  → rm_add_i (a + 0%rm) b i = rm_add_i a b i.
Proof.
intros a b i dj2 dj5 Ps2 Ps5 Hs1.
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
remember (fst_same a b si) as s2 eqn:Hs2 .
symmetry in Hs2.
apply fst_same_iff in Hs2; simpl in Hs2.
remember (fst_same a 0 si) as s3 eqn:Hs3 .
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
   remember (fst_same a 0 (ssi + di2)) as s4 eqn:Hs4 .
   symmetry in Hs4.
   apply fst_same_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4); rewrite Hs4, xorb_false_r in H.
    rewrite Hs2 in H.
    destruct b .[ si + di2]; discriminate H.

    clear H.
    apply not_false_iff_true.
    intros Ha.
    destruct dj5.
     rewrite Nat.add_0_r in Ps5.
     unfold rm_add_i, carry in Ps5.
     rewrite <- Heqssi in Ps5.
     remember (fst_same a b ssi) as s6 eqn:Ps6 .
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
        destruct b .[ ssi + dj6]; discriminate H2.

        apply Nat.nlt_ge in H2.
        destruct (lt_dec di2 (S dj6)) as [H3| H3].
         destruct di2.
          rewrite Nat.add_0_r in Hs4.
          rewrite Nat.add_0_r in Hs2.
          rewrite <- Hs2, Hs4 in Ps5.
          rewrite xorb_true_r in Ps5.
          apply negb_false_iff in Ps5.
          destruct a .[ si]; discriminate Ps5.

          apply Nat.succ_lt_mono in H3.
          apply Pn6 in H3.
          rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs2.
          rewrite <- Heqssi, H3 in Hs2.
          destruct b .[ ssi + di2]; discriminate Hs2.

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
       destruct b .[ si]; discriminate Ps5.

      destruct di2.
       rewrite Nat.add_0_r in Hs2.
       rewrite <- Hs2 in Ps5.
       destruct a .[ si]; discriminate Ps5.

       rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs2.
       rewrite <- Heqssi in Hs2.
       rewrite Ps6 in Hs2.
       destruct b .[ ssi + di2]; discriminate Hs2.

     assert (S dj5 = di2) as H.
      destruct (lt_dec (S dj5) di2) as [H2| H2].
       unfold rm_add_i, carry in Ps5.
       rewrite <- Nat.add_succ_l, <- Heqssi in Ps5.
       remember (fst_same a b (ssi + S dj5)) as s6 eqn:Ps6 .
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
          destruct b .[ ssi + S dj5 + di6]; discriminate H3.

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
           destruct b .[ si + di2]; discriminate H.

           apply Nat.nlt_ge in H4.
           apply Nat.le_antisymm; auto.

         rewrite <- H in Ha.
         rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in Ha.
         rewrite Nat.add_assoc in Ha.
         rewrite Ha, xorb_false_r in Ps5.
         apply Hn2 in H2.
         rewrite H2 in Ps5.
         destruct b .[ si + S dj5]; discriminate Ps5.

        pose proof (Ps6 (di2 - S (S dj5))) as H.
        rewrite Nat.add_sub_assoc in H; auto.
        rewrite Heqssi in H.
        rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
        rewrite Nat.add_shuffle0, Nat.add_sub in H.
        rewrite Hs2 in H.
        destruct b .[ si + di2]; discriminate H.

       apply Nat.nlt_ge in H2.
       destruct (lt_dec di2 (S dj5)) as [H3| H3].
        unfold rm_add_i, carry in Ps5.
        rewrite <- Nat.add_succ_l, <- Heqssi in Ps5.
        remember (fst_same a b (ssi + S dj5)) as s6 eqn:Ps6 .
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
         remember (fst_same a 0 (ssi + S dj5 + dj6)) as s7 eqn:Ps7 .
         symmetry in Ps7.
         apply fst_same_iff in Ps7; simpl in Ps7.
         destruct s7 as [dj7| ].
          destruct Ps7 as (Pn7, Ps7); rewrite Ps7, xorb_false_r in H.
          rename H into Hab.
          pose proof (Hs1 (S (S dj5 + dj6))) as H.
          rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H.
          rewrite Nat.add_assoc in H.
          unfold rm_add_i, carry in H.
          do 2 rewrite <- Nat.add_succ_l in H.
          remember (S ssi) as sssi; simpl in H.
          rewrite xorb_false_r in H.
          remember (fst_same a 0 (sssi + S dj5 + dj6)) as s8 eqn:Ps8 .
          symmetry in Ps8.
          apply fst_same_iff in Ps8; simpl in Ps8.
          destruct s8 as [dj8| ].
           destruct Ps8 as (Pn8, Ps8); rewrite Ps8, xorb_false_r in H.
           rewrite Ps6 in H.
           destruct b .[ ssi + S dj5 + dj6]; discriminate H.

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
           destruct a .[ si + S dj5]; discriminate Ps5.

           rename H into Hba.
           pose proof (Pn6 dj6 (Nat.lt_succ_diag_r dj6)) as H.
           rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hba.
           rewrite <- Nat.add_succ_l in Hba.
           rewrite <- Heqssi in Hba.
           rewrite Hba in H.
           destruct a .[ ssi + S dj5 + dj6]; discriminate H.

         pose proof (Hs1 (S dj5)) as H.
         unfold rm_add_i, carry in H.
         rewrite <- Nat.add_succ_l, <- Heqssi in H; simpl in H.
         rewrite xorb_false_r in H.
         remember (fst_same a 0 (ssi + S dj5)) as s7 eqn:Ps7 .
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
          destruct a .[ si + S dj5]; discriminate Ps5.

        apply Nat.nlt_ge in H3.
        apply Nat.le_antisymm; auto.

      rewrite H in Ps5.
      unfold rm_add_i, carry in Ps5.
      rewrite <- Nat.add_succ_l, <- Heqssi in Ps5.
      remember (fst_same a b (ssi + di2)) as s6 eqn:Ps6 .
      symmetry in Ps6.
      apply fst_same_iff in Ps6; simpl in Ps6.
      destruct s6 as [dj6| ].
       rewrite Hs4, Hs2, xorb_true_r in Ps5.
       destruct b .[ si + di2]; discriminate Ps5.

       rewrite Hs2, xorb_true_r in Ps5.
       destruct b .[ si + di2]; discriminate Ps5.

  symmetry; simpl.
  assert (∀ dj, b .[ si + dj] = true) as Hb.
   intros dj.
   apply negb_false_iff.
   rewrite <- Hs1.
   unfold rm_add_i, carry.
   rewrite <- Nat.add_succ_l; remember (S si) as ssi; simpl.
   rewrite xorb_false_r.
   remember (fst_same a 0 (ssi + dj)) as s4 eqn:Hs4 .
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
    remember (fst_same a b (ssi + dj5)) as s6 eqn:Ps6 .
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
  remember (fst_same a 0 ssi) as s4 eqn:Hs4 .
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
   destruct a .[ si]; discriminate H1.
Qed.

Theorem rm_add_add_0_l_when_both_hs_has_relay : ∀ a b i dj2 dj5,
  fst_same ((a + 0)%rm + b) 0 (S i) = Some dj2
  → fst_same (a + b) 0 (S i) = Some dj5
  → rm_add_i ((a + 0)%rm + b) 0 i = rm_add_i (a + b) 0 i.
Proof.
intros a b i dj2 dj5 Ps2 Ps5.
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
remember (fst_same (a + 0%rm) b (S i)) as s1 eqn:Hs1 .
symmetry in Hs1.
subst si.
destruct s1 as [di1| ].
 eapply rm_add_add_0_l_when_lhs_has_relay; eauto .

 eapply rm_add_add_0_l_when_lhs_has_no_relay; eauto .
Qed.

Theorem rm_add_add_0_l_when_relay : ∀ a b i di1,
  fst_same (a + 0%rm) b (S i) = Some di1
  → fst_same (a + b) 0 (S i) ≠ None.
Proof.
intros a b i di1 Hs1 Hs5.
apply rm_add_add_0_l_when_lhs_has_relay in Hs1.
remember (S i) as si.
unfold rm_add_i, carry in Hs1.
rewrite <- Heqsi in Hs1; simpl in Hs1.
unfold rm_add_i in Hs1 at 1.
unfold carry in Hs1.
rewrite <- Heqsi in Hs1; simpl in Hs1.
rewrite xorb_false_r in Hs1.
apply fst_same_iff in Hs5; simpl in Hs5.
remember (fst_same a b si) as s8 eqn:Hs8 .
apply fst_same_sym_iff in Hs8.
destruct s8 as [di8| ].
 destruct Hs8 as (Hn8, Hs8).
 destruct di8.
  clear Hn8; rewrite Nat.add_0_r in Hs8, Hs1.
  apply rm_add_inf_true_eq_if in Hs5; auto.
  destruct Hs5 as (Has, Hbs).
  remember (fst_same a 0 si) as s3 eqn:Hs3 .
  apply fst_same_sym_iff in Hs3; simpl in Hs3.
  destruct s3 as [di3| ].
   destruct Hs3 as (Hn3, Hs3).
   rewrite Hs3, xorb_false_r in Hs1.
   remember (fst_same (a + 0%rm) b si) as s4 eqn:Hs4 .
   apply fst_same_sym_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4).
    unfold rm_add_i, carry in Hs1.
    rewrite <- Nat.add_succ_l in Hs1.
    remember (S si) as ssi; simpl in Hs1.
    rewrite xorb_false_r in Hs1.
    remember (fst_same a 0 (ssi + di4)) as s5 eqn:Hs5 .
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
     remember (fst_same a 0 (ssi + di4)) as s6 eqn:Hs6 .
     destruct s6 as [di6| ].
      rewrite Hs5, xorb_true_r in Hs4.
      destruct di4.
       rewrite Nat.add_0_r in Hs1.
       rewrite <- negb_xorb_r in Hs1.
       destruct (a .[ i] ⊕ b .[ i] ⊕ a .[ si]); discriminate Hs1.

       rewrite Has, Hbs in Hs4; discriminate Hs4.

      rewrite xorb_true_r in Hs4.
      destruct di4.
       rewrite Nat.add_0_r in Hs1.
       rewrite <- negb_xorb_r in Hs1.
       destruct (a .[ i] ⊕ b .[ i] ⊕ a .[ si]); discriminate Hs1.

       rewrite Has, Hbs in Hs4; discriminate Hs4.

    destruct di3.
     rewrite Nat.add_0_r in Hs3.
     rewrite Hs3 in Hs1.
     destruct (a .[ i] ⊕ b .[ i]); discriminate Hs1.

     rewrite Has in Hs3; discriminate Hs3.

   remember (fst_same (a + 0%rm) b si) as s4 eqn:Hs4 .
   apply fst_same_sym_iff in Hs4; simpl in Hs4.
   destruct s4 as [di4| ].
    destruct Hs4 as (Hn4, Hs4); rewrite Hs4 in Hs1.
    unfold rm_add_i, carry in Hs4.
    rewrite <- Nat.add_succ_l in Hs4.
    remember (S si) as ssi; simpl in Hs4.
    rewrite xorb_false_r in Hs4.
    remember (fst_same a 0 (ssi + di4)) as s5 eqn:Hs5 .
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
    destruct a .[ i], b .[ i]; discriminate Hs1.

  pose proof (Hn8 0 (Nat.lt_0_succ di8)) as H.
  rewrite Nat.add_0_r in H.
  apply rm_add_inf_true_neq_if in Hs5; auto.
  destruct Hs5 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
  rename H into Hab.
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
    destruct b .[ si + S di8]; discriminate H.

    apply Nat.nlt_ge in H2.
    apply Nat.le_antisymm in H1; auto; clear H2.
    rewrite <- H1, Ha, xorb_false_r in Hs1.
    remember (fst_same a 0 si) as s3 eqn:Hs3 .
    apply fst_same_sym_iff in Hs3; simpl in Hs3.
    destruct s3 as [di3| ].
     destruct Hs3 as (Hn3, Hs3); rewrite Hs3, xorb_false_r in Hs1.
     remember (fst_same (a + 0%rm) b si) as s4 eqn:Hs4 .
     apply fst_same_sym_iff in Hs4; simpl in Hs4.
     destruct s4 as [di4| ].
      destruct Hs4 as (Hn4, Hs4); rewrite Hs4 in Hs1.
      unfold rm_add_i, carry in Hs4.
      rewrite <- Nat.add_succ_l in Hs4.
      remember (S si) as ssi; simpl in Hs4.
      rewrite xorb_false_r in Hs4.
      remember (fst_same a 0 (ssi + di4)) as s5 eqn:Hs5 .
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
         destruct b .[ si + di4]; discriminate H.

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

      destruct (xorb a .[ i] b .[ i]); discriminate Hs1.

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

Theorem rm_add_add_0_l_when_no_relay : ∀ a b i,
  fst_same (a + 0%rm) b (S i) = None
  → fst_same (a + b) 0 (S i) = None
  → rm_add_i (a + 0%rm) b i = negb (rm_add_i a b i).
Proof.
intros a b i Hs1 Hs5.
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
remember (fst_same a 0 si) as s3 eqn:Hs3 .
apply fst_same_sym_iff in Hs3; simpl in Hs3.
destruct s3 as [di3| ].
 destruct Hs3 as (Hn3, Hs3); rewrite Hs3.
 remember (fst_same a b si) as s4 eqn:Hs4 .
 apply fst_same_sym_iff in Hs4; simpl in Hs4.
 destruct s4 as [di4| ].
  destruct Hs4 as (Hn4, Hs4).
  symmetry.
  pose proof (Hs1 0) as H; rewrite Nat.add_0_r in H.
  unfold rm_add_i, carry in H.
  remember (S si) as ssi; simpl in H.
  rewrite xorb_false_r in H.
  remember (fst_same a 0 ssi) as s6 eqn:Hs6 .
  apply fst_same_sym_iff in Hs6; simpl in Hs6.
  destruct s6 as [di6| ].
   destruct Hs6 as (Hn6, Hs6); rewrite Hs6, xorb_false_r in H.
   apply rm_add_inf_true_neq_if in Hs5; auto.
   destruct Hs5 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   rename H into Hab.
   destruct (lt_dec (si + di4) j) as [H1| H1].
    remember H1 as H; clear HeqH.
    apply Hni in H.
    rewrite Hs4 in H.
    destruct b .[ si + di4]; discriminate H.

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

    rename H into Hab.
    pose proof (Hn4 0 (Nat.lt_0_succ di4)) as H.
    rewrite Nat.add_0_r, Hab in H.
    destruct b .[ si]; discriminate H.

  pose proof (Hs5 0) as H.
  rewrite Nat.add_0_r in H.
  unfold rm_add_i, carry in H.
  remember (S si) as ssi; simpl in H.
  remember (fst_same a b ssi) as s6 eqn:Hs6 .
  apply fst_same_sym_iff in Hs6; simpl in Hs6.
  destruct s6 as [di6| ].
   destruct Hs6 as (Hn6, Hs6).
   rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Hs6.
   rewrite Hs4 in Hs6.
   destruct b .[ si + S di6]; discriminate Hs6.

   pose proof (Hs4 0) as H1.
   rewrite Nat.add_0_r in H1.
   rewrite H1 in H.
   rewrite negb_xorb_diag_l in H.
   discriminate H.

 destruct (fst_same a b si) as [di| ]; [ idtac | reflexivity ].
 rewrite Hs3; reflexivity.
Qed.

Theorem rm_add_add_0_l_when_rhs_has_no_relay : ∀ a b i di2,
  fst_same ((a + 0)%rm + b) 0 (S i) = Some di2
  → fst_same (a + b) 0 (S i) = None
  → rm_add_i ((a + 0)%rm + b) 0 i = rm_add_i (a + b) 0 i.
Proof.
intros a b i di2 Hs2 Hs5.
unfold rm_add_i, carry.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
rewrite Hs2, Hs5.
remember Hs2 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, H); rewrite H; clear H.
rewrite xorb_false_r, xorb_true_r.
remember (fst_same (a + 0%rm) b (S i)) as s1 eqn:Hs1 .
symmetry in Hs1; subst si.
destruct s1 as [di1| ].
 exfalso.
 eapply rm_add_add_0_l_when_relay; eauto .

 eapply rm_add_add_0_l_when_no_relay; eauto .
Qed.

Theorem rm_add_add_0_r_not_without_relay : ∀ a b i,
  fst_same ((a + 0)%rm + b) 0 (S i) ≠ None.
Proof.
intros a b i Hs2.
remember (S i) as si.
apply fst_same_iff in Hs2; simpl in Hs2.
destruct (bool_dec ((a + 0)%rm) .[ si] b .[ si]) as [H1| H1].
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
Theorem rm_add_add_0_r : ∀ a b, (a + 0 + b = a + b)%rm.
Proof.
intros a b.
unfold rm_eq; intros i; simpl.
remember (fst_same ((a + 0)%rm + b) 0 (S i)) as s2 eqn:Hs2 .
remember (fst_same (a + b) 0 (S i)) as s5 eqn:Hs5 .
symmetry in Hs2, Hs5.
destruct s2 as [di2| ].
 destruct s5 as [di5| ].
  eapply rm_add_add_0_l_when_both_hs_has_relay; eauto .

  eapply rm_add_add_0_l_when_rhs_has_no_relay; eauto .

 exfalso; revert Hs2.
 eapply rm_add_add_0_r_not_without_relay; eauto .
Qed.

Theorem rm_add_compat_r : ∀ a b c, (a = b)%rm → (a + c = b + c)%rm.
Proof.
intros a b c Hab.
remember (a + 0)%rm as a1.
remember (b + 0)%rm as b1.
remember Heqa1 as H; clear HeqH.
eapply rm_norm_eq_compat_r with (b₀ := b) (c := c) in H; eauto .
 subst a1 b1.
 do 2 rewrite rm_add_add_0_r in H; assumption.

 subst a1 b1.
 do 2 rewrite rm_add_0_r; assumption.
Qed.

Theorem rm_add_compat : ∀ a b c d,
  (a = b)%rm
  → (c = d)%rm
  → (a + c = b + d)%rm.
Proof.
intros a b c d Hab Hcd.
transitivity (a + d)%rm; [ idtac | apply rm_add_compat_r; assumption ].
rewrite rm_add_comm; symmetry.
rewrite rm_add_comm; symmetry.
apply rm_add_compat_r; assumption.
Qed.

Add Parametric Morphism : rm_add
  with signature rm_eq ==> rm_eq ==> rm_eq
  as rm_add_morph.
Proof.
intros a b Hab c d Hcd.
apply rm_add_compat; assumption.
Qed.

Theorem rm_add_opp_r : ∀ a, (a - a = 0)%rm.
Proof.
intros a.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry.
remember (S i) as si; simpl.
rewrite xorb_false_r.
remember (fst_same 0 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ]; [ clear di1 Hs1 | discriminate Hs1; auto ].
remember (fst_same (a - a) 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); rewrite Hs1, xorb_false_r.
 unfold rm_add_i, carry.
 rewrite <- Heqsi; simpl.
 remember (fst_same a (- a) si) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 rewrite <- negb_xorb_r, negb_xorb_l, negb_xorb_diag_l.
 destruct s2 as [di2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Hs2).
 destruct a .[ si + di2]; discriminate Hs2.

 destruct (bool_dec a .[ si] (negb a .[ si])) as [H1| H1].
  destruct a .[ si]; discriminate H1.

  apply neq_negb in H1.
  apply rm_add_inf_true_neq_if in Hs1; auto.
  simpl in Hs1.
  destruct Hs1 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
  rewrite Ha in Hb; discriminate Hb.
Qed.

Theorem rm_zerop : ∀ a, {(a = 0)%rm} + {(a ≠ 0)%rm}.
Proof.
intros a.
remember (fst_same (a + 0%rm) rm_zero' 0) as s eqn:Hs .
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

Theorem fst_same_diag : ∀ a i, fst_same a a i = Some 0.
Proof.
intros a i.
apply fst_same_iff; simpl.
split; [ idtac | reflexivity ].
intros dj Hdj; exfalso.
revert Hdj; apply Nat.nlt_0_r.
Qed.

Theorem carry_diag : ∀ a i, carry a a i = a.[S i].
Proof.
intros a i.
unfold carry; simpl.
rewrite fst_same_diag, Nat.add_0_r; reflexivity.
Qed.

(* requires associativity
Axiom rm_add_assoc : ∀ a b c, (a+(b+c) = (a+b)+c)%rm.
Theorem rm_dec : ∀ a b, {(a = b)%rm} + {(a ≠ b)%rm}.
Proof.
intros a b.
destruct (rm_zerop (a - b)%rm) as [Hab| Hab].
 left.
 rewrite rm_add_comm in Hab.
 eapply rm_add_compat with (a := b) in Hab; [ idtac | reflexivity ].
 rewrite rm_add_assoc in Hab.
 rewrite rm_add_opp_r in Hab.
 rewrite rm_add_comm in Hab.
 do 2 rewrite rm_add_0_r in Hab.
 assumption.

 right.
 intros H; apply Hab; rewrite H.
 apply rm_add_opp_r.
Qed.

Theorem rm_decidable : ∀ a b, Decidable.decidable (a = b)%rm.
Proof.
intros a b.
destruct (rm_dec a b); [ left | right ]; assumption.
*)

(* associativity *)

Theorem fold_rm_add_i : ∀ a b i, rm_add_i a b i = ((a+b)%rm).[i].
Proof. reflexivity. Qed.

Theorem nat_compare_add_succ : ∀ i j, nat_compare i (i + S j) = Lt.
Proof.
intros i j.
apply nat_compare_lt.
apply Nat.lt_sub_lt_add_l.
rewrite Nat.sub_diag.
apply Nat.lt_0_succ.
Qed.

Theorem same_fst_same : ∀ a b i di dj,
  fst_same a b i = Some (di + dj)
  → fst_same a b (i + di) = Some dj.
Proof.
intros a b i di dj Hs.
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

Lemma lt_add_r : ∀ a b,
  0 < b
  → a < a + b.
Proof.
intros a b Hb.
apply Nat.lt_sub_lt_add_l.
rewrite Nat.sub_diag.
assumption.
Qed.

Theorem fst_same_before : ∀ a b i dk dl di4,
  fst_same a b (S i) = Some dk
  → dl < dk
  → fst_same a b (S (S (i + dl))) = Some di4
  → di4 = dk - S dl.
Proof.
intros a b i dk dl di4 Hsk Hdl Hs4.
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
 destruct b .[ S (S (i + dl + di4))]; discriminate H2.

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
  destruct b .[ S i + dk]; discriminate H3.

  apply Nat.nlt_ge in H3.
  apply Nat.le_antisymm; assumption.
Qed.

Theorem fst_same_inf_after : ∀ a b i di,
  fst_same a b i = None
  → fst_same a b (i + di) = None.
Proof.
intros a b i di Hs.
apply fst_same_iff in Hs.
apply fst_same_iff; intros dj.
rewrite <- Nat.add_assoc.
apply Hs.
Qed.

Theorem not_add_norm_inf_1 : ∀ a b i,
  ¬ (∀ dj : nat, rm_add_i (a + 0%rm) (b + 0%rm) (i + dj) = true).
Proof.
intros a b i Hab.
destruct (bool_dec ((a + 0)%rm) .[ i] ((b + 0)%rm) .[ i]) as [H1| H1].
 apply rm_add_inf_true_eq_if in Hab; auto.
 destruct Hab as (H, _); simpl in H.
 apply not_rm_add_0_inf_1_succ in H; auto.

 apply neq_negb in H1.
 apply rm_add_inf_true_neq_if in Hab; auto.
 simpl in Hab.
 destruct Hab as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 apply not_rm_add_0_inf_1_succ in Hat; auto.
Qed.

Theorem rm_add_i_norm_norm : ∀ a b i,
  rm_add_i ((a + 0)%rm + (b + 0)%rm) 0 i = rm_add_i (a + 0%rm) (b + 0%rm) i.
Proof.
intros a b i.
unfold rm_add_i, carry at 1.
remember (S i) as si; simpl.
rewrite xorb_false_r.
remember (fst_same ((a + 0)%rm + (b + 0)%rm) 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); rewrite Hs1, xorb_false_r; reflexivity.

 apply not_add_norm_inf_1 in Hs1; contradiction.
Qed.

(* still proved as rm_add_inf_true_if!! *)
Theorem rm_add_inf_if : ∀ a b i,
  (∀ dj, rm_add_i a b (i + dj) = true)
  → ∃ j,
    i < j ∧
    (∀ di, a.[j + S di] = true) ∧
    (∀ di, b.[j + S di] = true).
Proof.
intros a b i Hj.
destruct (bool_dec a .[ i] b .[ i]) as [H1| H1].
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

Theorem carry_0_r_true_if : ∀ a i,
  carry a 0 i = true
  → id (∀ dj, a.[i + S dj] = true).
Proof.
intros a i H j.
unfold carry in H; simpl in H.
remember (fst_same a 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 rewrite Hs1 in H; discriminate H.

 rewrite Nat.add_succ_r; apply Hs1.
Qed.

(* trying to make a lemma for something used many times, but it does
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

Theorem fst_same_in_range : ∀ a b i j di s,
  fst_same a b i = Some di
  → fst_same a b j = s
  → i ≤ j ≤ i + di
  → s = Some (i + di - j).
Proof.
intros a b i j di s Hi Hj (Hij, Hji).
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

Theorem fst_same_in_range2 : ∀ a b i di dj s,
  fst_same a b i = Some dj
  → fst_same a b (i + di) = s
  → di ≤ dj
  → s = Some (dj - di).
Proof.
intros a b i di dj s Hdj Hdi Hdij.
eapply fst_same_in_range in Hdi; try eassumption.
 rewrite <- minus_plus_simpl_l_reverse in Hdi.
 assumption.

 split; [ apply Nat.le_add_r | idtac ].
 apply Nat.add_le_mono_l; assumption.
Qed.

Theorem carry_before_relay : ∀ a b i di,
  fst_same a b i = Some di
  → ∀ dj, dj < di → carry a b (i + dj) = a.[i + di].
Proof.
intros a b i di Hs dj Hdj.
remember a.[i+di] as x eqn:Ha; symmetry in Ha.
unfold carry; simpl.
remember (fst_same a b (S (i + dj))) as s2 eqn:Hs2 .
symmetry in Hs2.
assert (S (i + dj) ≤ i + di) as H by (apply Nat.add_lt_mono_l; auto).
eapply fst_same_in_range in Hs2; try eassumption; [ idtac | split; auto ].
 subst s2.
 rewrite <- Nat.add_succ_l, Nat.add_sub_assoc; auto.
 rewrite Nat.add_comm, Nat.add_sub; assumption.

 rewrite <- Nat.add_succ_r.
 apply Nat.le_add_r.
Qed.

Theorem carry_before_inf_relay : ∀ a b i,
  fst_same a b i = None
  → ∀ dj, carry a b (i + dj) = true.
Proof.
intros a b i Hs dj.
unfold carry; simpl.
remember (fst_same a b (S (i + dj))) as s2 eqn:Hs2 .
symmetry in Hs2.
apply fst_same_iff in Hs2; simpl in Hs2.
destruct s2 as [di2| ]; [ idtac | reflexivity ].
apply fst_same_iff in Hs; simpl in Hs.
destruct Hs2 as (_, Hs2).
rewrite <- Nat.add_assoc, <- Nat.add_succ_r in Hs2.
rewrite Hs in Hs2.
exfalso; revert Hs2; apply no_fixpoint_negb.
Qed.

Theorem sum_before_relay : ∀ a b i di x,
  fst_same a b i = Some di
  → a .[i + di] = x
  → ∀ dj, dj < di → rm_add_i a b (i + dj) = negb x.
Proof.
intros a b i di x Hs Ha dj Hdj.
unfold rm_add_i.
remember Hs as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hs1, Hn1).
remember Hdj as H; clear HeqH.
apply Hs1 in H.
rewrite H, negb_xorb_diag_l, xorb_true_l.
f_equal; erewrite carry_before_relay; try eassumption; reflexivity.
Qed.

Theorem carry_when_inf_1 : ∀ a b i j,
  (∀ di, a.[S (i + di)] = true)
  → i ≤ j
  → carry a b j = true.
Proof.
intros a b i j Hdi Hij.
unfold carry; simpl.
remember (fst_same a b (S j)) as s1 eqn:Hs1 .
destruct s1 as [di1| ]; [ idtac | reflexivity ].
apply Nat.sub_add in Hij.
rewrite Nat.add_comm in Hij.
rewrite <- Hij, <- Nat.add_assoc.
apply Hdi.
Qed.

Theorem carry_comm_l : ∀ a b c i,
  carry (a + b) c i = carry (b + a) c i.
Proof.
intros a b c i.
rewrite carry_compat_r with (a := (b + a)%rm); [ reflexivity | idtac ].
apply rm_add_i_comm.
Qed.

Theorem carry_assoc_l : ∀ a b c d i,
  carry ((a + b) + c)%rm d i = carry (c + (b + a))%rm d i.
Proof.
intros a b c d i.
apply carry_compat_r.
intros j; simpl.
rewrite rm_add_i_comm.
apply rm_add_i_compat_r, rm_add_i_comm.
Qed.

Theorem rm_add_assoc_norm : ∀ a b c,
  ((a + 0) + ((b + 0) + (c + 0)) = ((a + 0) + (b + 0)) + (c + 0))%rm
  → (a + (b + c) = (a + b) + c)%rm.
Proof.
intros a b c H.
do 3 rewrite rm_add_0_r in H; assumption.
Qed.

Theorem carry_sum_norm : ∀ a₀ b₀ a b i,
  a = (a₀ + 0)%rm
  → b = (b₀ + 0)%rm
  → carry (a + b)%rm 0 i = false.
Proof.
intros a₀ b₀ a b i Ha₀ Hb₀.
unfold carry; simpl.
remember (fst_same (a + b) 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); assumption.

 apply forall_add_succ_l in Hs1.
 apply rm_add_inf_if in Hs1.
 destruct Hs1 as (j, (Hij, (Haj, Hbj))).
 rewrite Ha₀ in Haj; simpl in Haj.
 apply forall_add_succ_r in Haj.
 apply rm_add_inf_if in Haj.
 destruct Haj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem carry_sum_3_norm_assoc_l : ∀ c₀ a b c i,
  c = (c₀ + 0)%rm
  → carry ((a + b) + c)%rm 0 i = false.
Proof.
intros c₀ a b c i Hc₀.
unfold carry; simpl.
remember (fst_same ((a + b) + c)%rm 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); assumption.

 apply forall_add_succ_l in Hs1.
 apply rm_add_inf_if in Hs1.
 destruct Hs1 as (j, (Hij, (Haj, Hbj))).
 rewrite Hc₀ in Hbj; simpl in Hbj.
 apply forall_add_succ_r in Hbj.
 apply rm_add_inf_if in Hbj.
 destruct Hbj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem carry_sum_3_norm_assoc_r : ∀ a₀ a b c i,
  a = (a₀ + 0)%rm
  → carry (a + (b + c))%rm 0 i = false.
Proof.
intros a₀ a b c i Ha₀.
unfold carry; simpl.
remember (fst_same (a + (b + c)%rm) 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); assumption.

 apply forall_add_succ_l in Hs1.
 apply rm_add_inf_if in Hs1.
 destruct Hs1 as (j, (Hij, (Haj, Hbj))).
 rewrite Ha₀ in Haj; simpl in Haj.
 apply forall_add_succ_r in Haj.
 apply rm_add_inf_if in Haj.
 destruct Haj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem sum_x1_x_sum_0_0 : ∀ a b i,
  b.[i] = true
  → rm_add_i a b i = a.[i]
  → a.[S i] = false
  → rm_add_i a b (S i) = false.
Proof.
intros b c i Ht5 Hbd Ht6.
remember b.[i] as y eqn:Hb5; symmetry in Hb5.
apply not_true_iff_false; intros H.
unfold rm_add_i in H; simpl in H.
rewrite Ht6, xorb_false_l in H.
rename H into Hcc.
remember Hbd as H; clear HeqH.
unfold rm_add_i in H; simpl in H.
rewrite Hb5, Ht5, xorb_true_r in H.
apply xorb_move_l_r_1 in H.
rewrite negb_xorb_diag_l in H.
rename H into Hbc.
remember (S i) as x.
replace x with (x + 0) in Hcc by apply Nat.add_0_r.
unfold carry in Hbc.
rewrite <- Heqx in Hbc.
remember (fst_same b c x) as s1 eqn:Hs1 .
destruct s1 as [di1| ].
 symmetry in Hs1.
 destruct di1.
  rewrite Nat.add_0_r, Ht6 in Hbc; discriminate Hbc.

  assert (0 < S di1) as H by apply Nat.lt_0_succ.
  erewrite carry_before_relay in Hcc; try eassumption.
  rewrite Nat.add_0_r, Hbc, xorb_true_r in Hcc.
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

Theorem carry_succ_negb : ∀ a b i x,
  carry a b i = x
  → carry a b (S i) = negb x
  → a.[S i] = x ∧ b.[S i] = x.
Proof.
intros a b i x Hc1 Hc2.
unfold carry in Hc1; simpl in Hc1.
remember (fst_same a b (S i)) as s1 eqn:Hs1 .
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

 subst x; simpl in Hc2.
 rewrite Nat.add_0_r in Hc2.
 unfold carry in Hc2.
 apply fst_same_inf_after with (di := 1) in Hs1.
 rewrite <- Nat.add_1_r, Hs1 in Hc2.
 discriminate Hc2.
Qed.

Theorem sum_11_1_sum_x1 : ∀ a b i di,
  a .[ i] = true
  → b .[ i] = true
  → (∀ dj, dj ≤ di → rm_add_i a b (i + dj) = a.[i + dj])
  → b.[i + di] = true.
Proof.
intros a b i di Ha Hb Hab.
revert i Ha Hb Hab.
induction di; intros; [ rewrite Nat.add_0_r; assumption | idtac ].
pose proof (Hab (S di) (Nat.le_refl (S di))) as H.
unfold rm_add_i in H; simpl in H.
rewrite xorb_assoc in H.
apply xorb_move_l_r_1 in H.
rewrite xorb_nilpotent in H.
remember b .[ i + S di] as y eqn:Hy .
destruct y; [ reflexivity | symmetry in Hy ].
rewrite xorb_false_l in H.
rename H into Hd.
pose proof (Hab di (Nat.le_succ_diag_r di)) as H.
unfold rm_add_i in H; simpl in H.
rewrite xorb_assoc in H.
apply xorb_move_l_r_1 in H.
rewrite xorb_nilpotent in H.
rewrite IHdi in H; try assumption.
 rewrite xorb_true_l in H.
 apply negb_false_iff in H.
 rewrite Nat.add_succ_r in Hd.
 apply carry_succ_negb in H; [ idtac | assumption ].
 rewrite <- Nat.add_succ_r, Hy in H.
 destruct H as (_, H); discriminate H.

 intros dj Hdj.
 apply Hab, Nat.le_le_succ_r; assumption.
Qed.

Theorem case_1 : ∀ a b c i,
  carry a (b + c) i = true
  → carry b c i = true
  → carry a b i = false
  → False.
Proof.
intros a b c i Hc3 Hc5 Hc6.
remember Hc6 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same a b (S i)) as s6 eqn:Hs6 .
destruct s6 as [di6| ]; [ idtac | discriminate H ].
remember Hs6 as HH; clear HeqHH.
apply fst_same_sym_iff in HH; simpl in HH.
destruct HH as (Hn6, Ht6).
rewrite H in Ht6; symmetry in Ht6.
rename H into Ha6.
remember Hc5 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same b c (S i)) as s5 eqn:Hs5 .
remember Hs5 as HH; clear HeqHH.
apply fst_same_sym_iff in HH; simpl in HH.
destruct s5 as [di5| ]; [ idtac | clear H ].
 destruct HH as (Hn5, Ht5); rewrite H in Ht5.
 symmetry in Ht5; rename H into Hb5.
 destruct (lt_eq_lt_dec di5 di6) as [[H1| H1]| H1].
  remember Hc3 as H; clear HeqH.
  unfold carry in H; simpl in H.
  remember (fst_same a (b + c) (S i)) as s3 eqn:Hs3 .
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
     rename H into Hbc1.
     erewrite sum_x1_x_sum_0_0 in Ht3; try eassumption.
      discriminate Ht3.

      rewrite Nat.add_assoc, Nat.add_shuffle0.
      rewrite <- Nat.add_succ_l.
      apply sum_11_1_sum_x1 with (a := b); try assumption.
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
      apply sum_11_1_sum_x1 with (a := b); try assumption.
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
    apply sum_11_1_sum_x1 with (a := b); try assumption.
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
  remember (fst_same a (b + c) (S i)) as s3 eqn:Hs3 .
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
 remember (fst_same a (b + c) (S i)) as s3 eqn:Hs3 .
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

Theorem carry_x_before_xx : ∀ a b i x,
  a.[S i] = x
  → b.[S i] = x
  → carry a b i = x.
Proof.
intros a b i x Ha Hb; unfold carry.
remember (fst_same a b (S i)) as s eqn:Hs .
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

Theorem carry_eq_l_add_eq_r : ∀ a b i,
  carry a b i = a.[i] ↔ rm_add_i a b i = b.[i].
Proof.
intros a b i.
split; intros H.
 unfold rm_add_i; rewrite xorb_shuffle0.
 rewrite H, xorb_nilpotent, xorb_false_l; reflexivity.

 unfold rm_add_i in H; rewrite xorb_shuffle0, xorb_comm in H.
 apply xorb_move_l_r_1 in H.
 rewrite xorb_nilpotent in H.
 apply xorb_eq.
 rewrite xorb_comm; assumption.
Qed.

Theorem sum_0x_x_not_sum_y1_0 : ∀ a b c i di1 di2 di4 y t,
  (∀ dj, dj < di1 → rm_add_i a b (S (i + dj)) = negb c .[ S (i + dj)])
  → (∀ dj, dj < di4 → b .[ S (i + di2 + dj)] = negb c .[ S (i + di2 + dj)])
  → carry a b (i + di2) = false
  → di2 + di4 < di1
  → a .[ S (i + di2)] = false
  → b .[ S (i + di2)] = y
  → rm_add_i a b (S (i + di2)) = y
  → carry a b (S (i + di2)) = false
  → a .[ S (i + di2 + di4)] = negb t
  → b .[ S (i + di2 + di4)] = true
  → rm_add_i a b (S (i + di2 + di4)) = false
  → carry a b (S (i + di2 + di4)) = t
  → False.
Proof.
intros a b c i di1 di2 di4 y t.
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
   apply carry_x_before_xx with (b := b) in Ha4; try eassumption.
   rewrite Hf6 in Ha4; discriminate Ha4.

  rewrite Nat.add_succ_r in H2, Ha4, Hb4, He4, Hf4.
  clear He5 y Ha6 Hb6 He6.
  remember a .[ S (S (i + di2))] as x eqn:Ha6 .
  symmetry in Ha6.
  remember b .[ S (S (i + di2))] as y eqn:Hb6 .
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

Theorem sum_x1_0_carry_not_x : ∀ a b c i di1 di2 di4 t,
  (∀ dj, dj < di1 → rm_add_i a b (S (i + dj)) = negb c .[ S (i + dj)])
  → (∀ dj, dj < S di4 →
     b .[ S (S (i + di2 + dj))] = negb c .[ S (S (i + di2 + dj))])
  → carry a b (S (i + di2)) = false
  → S (S (di2 + di4)) < di1
  → a .[ S (S (S (i + di2 + di4)))] = negb t
  → b .[ S (S (S (i + di2 + di4)))] = true
  → rm_add_i a b (S (S (S (i + di2 + di4)))) = false
  → carry a b (S (S (S (i + di2 + di4)))) = t
  → False.
Proof.
intros a b c i di1 di2 di4 t Hn1 Hn4 He5 H2 Ha4 Hb4 He4 Hf4.
simpl in Hn4, He5, H2, Ha4, Hb4, He4, Hf4.
remember a .[ S (S (i + di2))] as x eqn:Ha6 .
symmetry in Ha6.
remember b .[ S (S (i + di2))] as y eqn:Hb6 .
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

(* TODO: compare with sum_x1_0_carry_not_x *)
Theorem sum_x1_carry_not_x2 : ∀ a b c i di2 di4 di x,
  (∀ dj,  dj < di2 + di
   → rm_add_i a b (S (i + dj)) = negb c .[ S (i + dj)])
  → (∀ dj, S dj < di4 →
     b .[ S (i + di2 + dj)] = negb c .[ S (i + di2 + dj)])
  → di < di4
  → a .[ S (i + di2 + di)] = x
  → b .[ S (i + di2 + di)] = true
  → c .[ S (i + di2 + di)] = false
  → carry a b (i + di2) = false
  → carry a b (S (i + di2 + di)) = negb x
  → False.
Proof.
intros a b c i di2 di4 di x Hn1 Hn4 H2 Ha2 Hb3 Hd1 Hf1 H.
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
  remember a .[ S (i + di2)] as y eqn:Ha5 .
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

(*
Theorem old_subcase_2a : ∀ a b c i di3 di2 u,
  fst_same a (b + c) (S i) = Some di3
  → fst_same b c (S i) = Some di2
  → a .[ S (i + di3)] = u
  → b .[ S (i + di2)] = u
  → di3 < di2
  → False.
Proof.
intros a b c i di3 di2 u.
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
*)

Theorem subcase_2a : ∀ a b c i di1 di3 di2,
  fst_same (a + b) c (S i) = Some di1
  → fst_same a (b + c) (S i) = Some di3
  → fst_same b c (S i) = Some di2
  → a .[ S (i + di3)] = true
  → di2 < di1
  → di3 < di2
  → False.
Proof.
intros a b c i di1 di3 di2.
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
 remember a .[ S (S (i + di3))] as x eqn:Ha2 .
 symmetry in Ha2.
 destruct x.
  apply carry_succ_negb in He2; [ idtac | assumption ].
  rewrite Hb2 in He2.
  destruct He2 as (_, H); discriminate H.

  eapply carry_x_before_xx in Hb2; [ idtac | eassumption ].
  rewrite Hf3 in Hb2; discriminate Hb2.

 remember (carry a b (S (S (i + di3)))) as x eqn:Hx .
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

(*
     i  i+1  -   i2  -   i1
  b  .   .   .   .   .   .
                  +t
  a  .   .   .   1   .   .
         ≠   ≠
b+c  .   .   .   .   .   .

a+b  .   .   .   .   .   .
         ≠   ≠   ≠   ≠
  c  .   .   .   .   .   0
         ≠   ≠    +t
  b  .   .   .   1   .   .

 *)
Theorem subcase_2b : ∀ a b c i di1 di2,
  fst_same (a + b) c (S i) = Some di1
  → fst_same b c (S i) = Some di2
  → fst_same a (b + c) (S i) = Some di2
  → rm_add_i a b (S (i + di1)) = false
  → a .[ S (i + di2)] = true
  → di2 < di1
  → False.
Proof.
intros a b c i di1 di2.
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
remember (fst_same b c (S (S (i + di2)))) as s4 eqn:Hs4 .
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
   remember a .[ S (S (i + di2))] as x eqn:Ha4 .
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
    remember (fst_same a b (S (S (i + di2)))) as s5 eqn:Hs5 .
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
   remember (carry a b (S (S (S (i + di2 + di4))))) as t eqn:Hf4 .
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
  remember a .[ S (S (i + di2 + di))] as t eqn:Ha6 .
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
 remember a .[ S (S (i + di2 + di))] as t eqn:Ha6 .
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

Theorem after_carry_negb : ∀ a b i u,
  carry a b i = u
  → a .[ S i] = negb u
  → b .[ S i] = u.
Proof.
intros a b i u Hc Ha.
unfold carry in Hc; simpl in Hc.
remember (fst_same a b (S i)) as s eqn:Hs .
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

Theorem carry_succ_diff : ∀ a b i t u,
  carry a b i = t
  → a .[ S i] = u
  → b .[ S i] = negb u
  → carry a b (S i) = t.
Proof.
intros a b i t u Hc Ha Hb.
rewrite <- negb_involutive.
apply neq_negb.
intros H.
apply carry_succ_negb in H; [ idtac | assumption ].
rewrite Ha, Hb in H.
destruct H as (Hu, H); rewrite Hu in H.
revert H; apply no_fixpoint_negb.
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

(*
Theorem zzz :
  Rabn : carry a b (S (i + m)) = false
  Rab_cn : carry (a + b) c (S (i + m)) = false
  Rbcn : carry b c (S (i + m)) = true
  →
  Rabp : carry a b (S (S (i + m + p))) = false
  Rab_cp : carry (a + b) c (S (S (i + m + p))) = false
  Rbcp : carry b c (S (S (i + m + p))) = true
*)

Theorem zzz : ∀ a b c i,
  carry a b i = false
  → carry (a + b) c i = false
  → carry b c i = true
  → ∃ m,
    carry a b (S (i + m)) = false ∧
    carry (a + b) c (S (i + m)) = false ∧
    carry b c (S (i + m)) = true.
Proof.
intros a b c i Rab Rabc Rbc.
rename Rab into Rabn.
rename Rabc into Rab_cn.
rename Rbc into Rbcn.
remember Rabn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same a b (S i)) as sabn eqn:Hsabn .
destruct sabn as [dabn| ]; [ idtac | discriminate H ].
rename H into A_p.
symmetry in Hsabn.
remember Rab_cn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (a + b) c (S i)) as sab_cn.
rename Heqsab_cn into Hsab_cn.
destruct sab_cn as [dab_cn| ]; [ idtac | discriminate H ].
rename H into AB_p; symmetry in Hsab_cn.
remember Rbcn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same b c (S i)) as sbcn eqn:Hsbcn .
symmetry in Hsbcn.
destruct sbcn as [dbcn| ]; [ idtac | clear H ].
 rename H into B_p.
 remember (List.fold_right min dbcn [dabn; dab_cn … []]) as p.
 rename Heqp into Hp.
 destruct (eq_nat_dec dabn p) as [H| H].
  move H at top; subst dabn; rename A_p into Ap.
  remember Hsabn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnabn, Bp).
  rewrite Ap in Bp; symmetry in Bp.
  remember Hsbcn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnbcn, Htbcn).
  destruct (eq_nat_dec dbcn p) as [H| H].
   move H at top; subst dbcn.
   rewrite B_p in Bp; discriminate Bp.

   eapply min_neq_lt in H; eauto ; try (left; auto).
   rename H into Hpdbcn.
   remember Bp as Cp; clear HeqCp.
   rewrite Hnbcn in Cp; [ idtac | assumption ].
   apply negb_false_iff in Cp.
   remember Hsab_cn as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hnab_cn, Htab_cn).
   destruct (eq_nat_dec dab_cn p) as [H| H].
    move H at top; subst dab_cn.
    rewrite Cp in Htab_cn.
    rewrite AB_p in Htab_cn; discriminate Htab_cn.

    eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
    rename H into Hpdab_cn.
    pose proof (Hnab_cn p Hpdab_cn) as H.
    rewrite Cp in H; simpl in H; rename H into ABp.
    remember ABp as H; clear HeqH.
    unfold rm_add_i in H.
    rewrite Ap, Bp, xorb_false_l in H.
    rename H into Rabp.
    remember Hsab_cn as H; clear HeqH.
    eapply carry_before_relay in H; [ idtac | eassumption ].
    simpl in H.
    rewrite AB_p in H.
    rename H into Rab_cp.
    remember Hsbcn as H; clear HeqH.
    eapply carry_before_relay in H; [ idtac | eassumption ].
    simpl in H.
    rewrite B_p in H.
    rename H into Rbcp.
    exists p.
    split; [ assumption | split; assumption ].

  exfalso.
  eapply min_neq_lt in H; eauto ; try (right; left; auto).
  rename H into Hpdan.
  remember Hsabn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnabn, Htabn).
  remember Hsab_cn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnab_cn, Htab_cn).
  remember Hsbcn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnbcn, Htbcn).
  rename Htbcn into C_p; rewrite B_p in C_p; symmetry in C_p.
  rename Htab_cn into C_q; rewrite AB_p in C_q; symmetry in C_q.
  destruct (eq_nat_dec dbcn p) as [H| H].
   move H at top; subst dbcn.
   rename B_p into Bp; rename C_p into Cp.
   destruct (eq_nat_dec dab_cn p) as [H| H].
    move H at top; subst dab_cn.
    rewrite Cp in C_q; discriminate C_q.

    eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
    rename H into Hpdab_cn.
    pose proof (Hnab_cn p Hpdab_cn) as H.
    rewrite Cp in H; rename H into ABp; simpl in ABp.
    remember ABp as H; clear HeqH.
    unfold rm_add_i in H.
    rewrite Hnabn in H; [ idtac | assumption ].
    rewrite negb_xorb_diag_l, xorb_true_l in H.
    rewrite <- Nat.add_succ_l in H.
    erewrite carry_before_relay in H; try eassumption.
    simpl in H; rewrite A_p in H; discriminate H.

   eapply min_neq_lt in H; eauto ; try (left; auto).
   rename H into Hpdbcn.
   destruct (eq_nat_dec dab_cn p) as [H| H].
    move H at top; subst dab_cn.
    remember AB_p as H; clear HeqH.
    unfold rm_add_i in H; simpl in H.
    rewrite Hnabn in H; [ idtac | assumption ].
    rewrite negb_xorb_diag_l, xorb_true_l in H.
    apply negb_false_iff in H.
    rewrite <- Nat.add_succ_l in H.
    erewrite carry_before_relay in H; try eassumption.
    simpl in H; rewrite A_p in H; discriminate H.

    eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
    rename H into Hpdab_cn; simpl in Hp.
    revert Hp Hpdan Hpdbcn Hpdab_cn; clear; intros Hp H1 H2 H3.
    destruct (Nat.min_dec dab_cn dbcn) as [L1| L1].
     rewrite L1 in Hp.
     destruct (Nat.min_dec dabn dab_cn) as [L2| L2].
      rewrite L2 in Hp; subst p.
      revert H1; apply Nat.lt_irrefl.

      rewrite L2 in Hp; subst p.
      revert H3; apply Nat.lt_irrefl.

     rewrite L1 in Hp.
     destruct (Nat.min_dec dabn dbcn) as [L2| L2].
      rewrite L2 in Hp; subst p.
      revert H1; apply Nat.lt_irrefl.

      rewrite L2 in Hp; subst p.
      revert H2; apply Nat.lt_irrefl.

 remember (min dabn dab_cn) as p eqn:Hp .
 destruct (eq_nat_dec dabn p) as [H| H].
  move H at top; subst dabn; rename A_p into Ap.
  remember Hsabn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnabn, Bp).
  rewrite Ap in Bp; symmetry in Bp.
  remember Hsbcn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  rename H into Hnbcn.
  remember Bp as Cp; clear HeqCp.
  rewrite Hnbcn in Cp.
  apply negb_false_iff in Cp.
  remember Hsab_cn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnab_cn, Htab_cn).
  destruct (eq_nat_dec dab_cn p) as [H| H].
   move H at top; subst dab_cn.
   rewrite Cp in Htab_cn.
   rewrite AB_p in Htab_cn; discriminate Htab_cn.
bbb.

       i   -   n
  b    .   .   .
0
  a    .   .   .

 b+c   .   .   .

 a+b   .   .   .
0
  c    .   .   .
1
  b    .   .   .


Theorem case_2 : ∀ a₀ b₀ c₀ a b c i u,
  a = (a₀ + 0)%rm
  → b = (b₀ + 0)%rm
  → c = (c₀ + 0)%rm
  → carry (a + (b + c)%rm) 0 i = false
  → carry ((a + b)%rm + c) 0 i = false
  → carry a (b + c) i = true
  → carry (a + b) c i = false
  → carry b c i = u
  → carry a b i = u
  → False.
Proof.
intros a₀ b₀ c₀ a b c i u Ha₀ Hb₀ Hc₀ Hc1 Hc2 Hc3 Hc4 Hc5 Hc6.
remember Hc3 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same a (b + c) (S i)) as s3 eqn:Hs3 .
symmetry in Hs3; rename H into H3.
remember Hc4 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (a + b) c (S i)) as s4 eqn:Hs4 .
symmetry in Hs4; rename H into H4.
remember Hc5 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same b c (S i)) as s5 eqn:Hs5 .
symmetry in Hs5; rename H into H5.
remember Hc6 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same a b (S i)) as s6 eqn:Hs6 .
symmetry in Hs6; rename H into H6.
destruct s4 as [di4| ]; [ idtac | discriminate H4 ].
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
       symmetry in H; rename H into Habm.
       remember Habm as H; clear HeqH.
       unfold rm_add_i in H; simpl in H.
       rewrite H3, H5, xorb_nilpotent, xorb_false_l in H.
       rename H into Hcabm.
       remember Ht3 as H; clear HeqH.
       unfold rm_add_i in H.
       rewrite H5, Ht5, xorb_nilpotent, xorb_false_l in H.
       rename H into Hcbcm.
       remember Hcabm as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same a b (S (S (i + m)))) as sabm eqn:Hsabm .
       destruct sabm as [djabm| ]; [ idtac | discriminate H ].
       symmetry in Hsabm.
       rename H into Haabm.
       remember Hs4 as H; clear HeqH.
       eapply carry_before_relay in H; [ idtac | eassumption ].
       simpl in H; rewrite H4 in H.
       rename H into Habcm.
       revert Hcabm Habcm Hcbcm; clear; intros.
       rename Hcabm into Rabn.
       rename Habcm into Rab_cn.
       rename Hcbcm into Rbcn.
(**)
Focus 1.
bbb.
       remember Rabn as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same a b (S (S (i + m)))) as sabn eqn:Hsabn .
       destruct sabn as [dabn| ]; [ idtac | discriminate H ].
       rename H into A_p.
       symmetry in Hsabn.
       remember Rab_cn as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same (a + b) c (S (S (i + m)))) as sab_cn.
       rename Heqsab_cn into Hsab_cn.
       destruct sab_cn as [dab_cn| ]; [ idtac | discriminate H ].
       rename H into AB_p; symmetry in Hsab_cn.
       remember Rbcn as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same b c (S (S (i + m)))) as sbcn eqn:Hsbcn .
       symmetry in Hsbcn.
       destruct sbcn as [dbcn| ]; [ idtac | clear H ].
        rename H into B_p.
        remember (List.fold_right min dbcn [dabn; dab_cn … []]) as p.
        rename Heqp into Hp.
        destruct (eq_nat_dec dabn p) as [H| H].
         move H at top; subst dabn; rename A_p into Ap.
         remember Hsabn as H; clear HeqH.
         apply fst_same_iff in H; simpl in H.
         destruct H as (Hnabn, Bp).
         rewrite Ap in Bp; symmetry in Bp.
         remember Hsbcn as H; clear HeqH.
         apply fst_same_iff in H; simpl in H.
         destruct H as (Hnbcn, Htbcn).
         destruct (eq_nat_dec dbcn p) as [H| H].
          move H at top; subst dbcn.
          rewrite B_p in Bp; discriminate Bp.

          eapply min_neq_lt in H; eauto ; try (left; auto).
          rename H into Hpdbcn.
          remember Bp as Cp; clear HeqCp.
          rewrite Hnbcn in Cp; [ idtac | assumption ].
          apply negb_false_iff in Cp.
          remember Hsab_cn as H; clear HeqH.
          apply fst_same_iff in H; simpl in H.
          destruct H as (Hnab_cn, Htab_cn).
          destruct (eq_nat_dec dab_cn p) as [H| H].
           move H at top; subst dab_cn.
           rewrite Cp in Htab_cn.
           rewrite AB_p in Htab_cn; discriminate Htab_cn.

           eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
           rename H into Hpdab_cn.
           pose proof (Hnab_cn p Hpdab_cn) as H.
           rewrite Cp in H; simpl in H; rename H into ABp.
           remember ABp as H; clear HeqH.
           unfold rm_add_i in H.
           rewrite Ap, Bp, xorb_false_l in H.
           rename H into Rabp.
           remember Hsab_cn as H; clear HeqH.
           eapply carry_before_relay in H; [ idtac | eassumption ].
           simpl in H.
           rewrite AB_p in H.
           rename H into Rab_cp.
           remember Hsbcn as H; clear HeqH.
           eapply carry_before_relay in H; [ idtac | eassumption ].
           simpl in H.
           rewrite B_p in H.
           rename H into Rbcp.

bbb.
           Focus 2.
           eapply min_neq_lt in H; eauto ; try (right; left; auto).
           rename H into Hpdan.
           remember Hsabn as H; clear HeqH.
           apply fst_same_iff in H; simpl in H.
           destruct H as (Hnabn, Htabn).
           remember Hsab_cn as H; clear HeqH.
           apply fst_same_iff in H; simpl in H.
           destruct H as (Hnab_cn, Htab_cn).
           remember Hsbcn as H; clear HeqH.
           apply fst_same_iff in H; simpl in H.
           destruct H as (Hnbcn, Htbcn).
           rename Htbcn into C_p; rewrite B_p in C_p; symmetry in C_p.
           rename Htab_cn into C_q; rewrite AB_p in C_q; symmetry in C_q.
           destruct (eq_nat_dec dbcn p) as [H| H].
            move H at top; subst dbcn.
            rename B_p into Bp; rename C_p into Cp.
            destruct (eq_nat_dec dab_cn p) as [H| H].
             move H at top; subst dab_cn.
             rewrite Cp in C_q; discriminate C_q.

             eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
             rename H into Hpdab_cn.
             pose proof (Hnab_cn p Hpdab_cn) as H.
             rewrite Cp in H; rename H into ABp; simpl in ABp.
             remember ABp as H; clear HeqH.
             unfold rm_add_i in H.
             rewrite Hnabn in H; [ idtac | assumption ].
             rewrite negb_xorb_diag_l, xorb_true_l in H.
             do 2 rewrite <- Nat.add_succ_l in H.
             erewrite carry_before_relay in H; try eassumption.
             simpl in H; rewrite A_p in H; discriminate H.

            eapply min_neq_lt in H; eauto ; try (left; auto).
            rename H into Hpdbcn.
            destruct (eq_nat_dec dab_cn p) as [H| H].
             move H at top; subst dab_cn.
             remember AB_p as H; clear HeqH.
             unfold rm_add_i in H; simpl in H.
             rewrite Hnabn in H; [ idtac | assumption ].
             rewrite negb_xorb_diag_l, xorb_true_l in H.
             apply negb_false_iff in H.
             do 2 rewrite <- Nat.add_succ_l in H.
             erewrite carry_before_relay in H; try eassumption.
             simpl in H; rewrite A_p in H; discriminate H.

             eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
             rename H into Hpdab_cn; simpl in Hp.
             revert Hp Hpdan Hpdbcn Hpdab_cn; clear; intros Hp H1 H2 H3.
             destruct (Nat.min_dec dab_cn dbcn) as [L1| L1].
              rewrite L1 in Hp.
              destruct (Nat.min_dec dabn dab_cn) as [L2| L2].
               rewrite L2 in Hp; subst p.
               revert H1; apply Nat.lt_irrefl.

               rewrite L2 in Hp; subst p.
               revert H3; apply Nat.lt_irrefl.

              rewrite L1 in Hp.
              destruct (Nat.min_dec dabn dbcn) as [L2| L2].
               rewrite L2 in Hp; subst p.
               revert H1; apply Nat.lt_irrefl.

               rewrite L2 in Hp; subst p.
               revert H2; apply Nat.lt_irrefl.
bbb.

       i  i+1  -   m   -   p
  b    .   .   .   .   .   1
1                   +0 ≠   ≠+0
  a    .   .   .   .   .   0
1
 b+c   .   .   .   .   .   .

 a+b   .   .   .   .   .   0
0                   +0 ≠
  c    .   .   .   .   .   0
1                   +1 ≠   ≠
  b    .   .   .   .   .   1


p like n

       i  i+1  -   m   -   n   -   p
  b    .   0   .   1   1   0   .   0
1          ≠   ≠    +0 ≠    +0 ≠    +0
  a    .   1   .   1   0   0   .   0
1          ≠   ≠
 b+c   .   0   .   1   0   0   .   0

 a+b   .   0   .   0   1   0   .   0
0          ≠   ≠   ≠+0 ≠   ≠+0 ≠    +0
  c    .   1   .   1   0   1   .   1
1          ≠+1 ≠    +1 ≠   ≠+1 ≠    +1
  b    .   0   .   1   1   0   .   0

       i  i+1  -   m
  b    .   .   .   1
1          ≠   ≠    +0
  a    .   .   .   1
1          ≠   ≠
 b+c   .   .   .   1

 a+b   .   .   .   0
0          ≠   ≠   ≠+0 ... m4
  c    .   .   .   1
1          ≠   ≠    +1
  b    .   .   .   1

       remember Ht5 as H; clear HeqH.
       apply negb_false_iff in H.
       rewrite <- Hn4 in H; [ idtac | omega ].
       unfold rm_add_i in H; simpl in H.
       rewrite H3, H5, xorb_nilpotent, xorb_false_l in H.
       rename H into Hd6.
       remember Ht3 as H; clear HeqH.
       unfold rm_add_i in H.
       rewrite H5, Ht5, xorb_nilpotent, xorb_false_l in H.
       rename H into Hd5.
       remember Hs4 as H; clear HeqH.
       apply carry_before_relay with (dj := m) in H; [ idtac | omega ].
       simpl in H; rewrite Nat.add_succ_r, Nat.add_assoc in H.
       rewrite H4 in H; rename H into Hd4.
       remember b .[ S (S (i + m))] as x eqn:Hb6 .
       symmetry in Hb6.
       destruct (bool_dec x false) as [H1| H1].
        move H1 at top; subst x.
        remember Hd5 as H; clear HeqH.
        apply after_carry_negb in H; [ idtac | assumption ].
        rename H into He6.
        destruct m4.
         rewrite Nat.add_0_r, He6 in Ht4.
         discriminate Ht4.

         remember He6 as H; clear HeqH.
         apply negb_false_iff in H.
         rewrite <- Nat.add_succ_r in H.
         rewrite <- Hn4 in H; [ idtac | omega ].
         rewrite Nat.add_succ_r in H.
         unfold rm_add_i in H.
         rewrite Hb6, xorb_false_r in H.
         apply xorb_eq in H.
         remember a .[ S (S (i + m))] as x eqn:Hx .
         symmetry in Hx, H.
         destruct x.
          apply carry_succ_negb in Hd6; try assumption.
          rewrite Hx in Hd6.
          destruct Hd6 as (Hd6, _); discriminate Hd6.

          rename Hx into Ha6; rename H into Hf6.
bbb.

Ah oui mais non, il faut voir qui est le plus petit entre m4 et
le relais en b c après m, et le relais en a b après m.

D'un autre côté, il faut bien limiter un peu m4, il va tout de même
pas partir à l'infini !

Hyp b.[m+1]=0
       i  i+1  -   m   -   m4
  b    .   .   .   1   ₀   1
1          ≠   ≠    +0  +₀  +₀ <-- contrad
  a    .   .   .   1   ₀   ₀
1          ≠   ≠
 b+c   .   .   .   1   ₀   ₀

 a+b   .   .   .   0   ₀   0
0          ≠   ≠   ≠+0 ≠
  c    .   .   .   1   1   0
1          ≠   ≠    +1      +1
  b    .   .   .   1   ₀   1

(* end test 1 *)
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       remember Ht5 as H; clear HeqH.
       apply negb_false_iff in H.
       rewrite <- Hn4 in H; [ idtac | assumption ].
       unfold rm_add_i in H; simpl in H.
       rewrite H6, Ht6, xorb_nilpotent, xorb_false_l in H.
       rename H into Hd6.
       remember Ht3 as H; clear HeqH.
       unfold rm_add_i in H.
       rewrite Ht6, Ht5, xorb_nilpotent, xorb_false_l in H.
       rename H into Hd5.
       remember Hs4 as H; clear HeqH.
       apply carry_before_relay with (dj := m) in H; [ idtac | assumption ].
       simpl in H; rewrite H4 in H; rename H into Hd4.
       remember (S (i + m)) as j eqn:Hj .
       remember Hd4 as H; clear HeqH.
       unfold carry in H; simpl in H.
bbb.
       remember (fst_same (a + b) c (S j)) as u4 eqn:Hu4 .
       symmetry in Hu4; rename H into I4.
       remember Hd5 as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same b c (S j)) as u5 eqn:Hu5 .
       symmetry in Hu5; rename H into I5.
       remember Hd6 as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same a b (S j)) as u6 eqn:Hu6 .
       symmetry in Hu6; rename H into I6.
       destruct u4 as [dj4| ]; [ idtac | discriminate I4 ].
       destruct u6 as [dj6| ]; [ idtac | discriminate I6 ].
       destruct u5 as [dj5| ].
        remember (List.fold_right min dj6 [dj4; dj5 … []]) as n eqn:Hn .
bbb.

       i  i+1  -   m
  b    .   .   .   1
1          ≠   ≠    +0
  a    .   .   .   1
1          ≠   ≠
 b+c   .   .   .   1

 a+b   .   .   .   0
0          ≠   ≠   ≠+0    ... di4
  c    .   .   .   1
1          ≠   ≠    +1
  b    .   .   .   1

        remember Hu4 as H; clear HeqH.
        apply fst_same_iff in H; simpl in H.
        destruct H as (In4, It4).
        rewrite I4 in It4; symmetry in It4.
        remember Hu5 as H; clear HeqH.
        apply fst_same_iff in H; simpl in H.
        destruct H as (In5, It5).
        rewrite I5 in It5; symmetry in It5.
        remember Hu6 as H; clear HeqH.
        apply fst_same_iff in H; simpl in H.
        destruct H as (In6, It6).
        rewrite I6 in It6; symmetry in It6.
        destruct (eq_nat_dec dj4 n) as [N4| N4].
         move N4 at top; subst dj4.
         destruct (eq_nat_dec dj5 n) as [N5| N5].
          move N5 at top; subst dj5.
          rewrite It4 in It5; discriminate It5.

          eapply min_neq_lt in N5; eauto ; try (do 2 right; left; auto).
          destruct (eq_nat_dec dj6 n) as [N6| N6].
           move N6 at top; subst dj6.
           remember N5 as H; clear HeqH.
           apply In5 in H.
           rewrite It6, It4 in H.
           discriminate H.

           eapply min_neq_lt in N6; eauto ; try (left; auto).
           remember I4 as H; clear HeqH.
           unfold rm_add_i in H.
           rewrite In6 in H; [ idtac | assumption ].
           rewrite negb_xorb_diag_l, xorb_true_l in H.
           apply negb_false_iff in H.
           apply carry_before_relay with (dj := n) in Hu6; auto.
           simpl in Hu6; rewrite H, I6 in Hu6.
           discriminate Hu6.

         eapply min_neq_lt in N4; eauto ; try (right; left; auto).
         destruct (eq_nat_dec dj5 n) as [N5| N5].
          move N5 at top; subst dj5.
          destruct (eq_nat_dec dj6 n) as [N6| N6].
           move N6 at top; subst dj6.
           rewrite It6 in I5; discriminate I5.

           eapply min_neq_lt in N6; eauto ; try (left; auto).
           pose proof (In4 n N4) as H.
           rewrite It5 in H; simpl in H.
           unfold rm_add_i in H.
           rewrite In6 in H; [ idtac | assumption ].
           rewrite negb_xorb_diag_l, xorb_true_l in H.
           apply negb_false_iff in H.
           apply carry_before_relay with (dj := n) in Hu6; auto.
           simpl in Hu6; rewrite H, I6 in Hu6.
           discriminate Hu6.

          eapply min_neq_lt in N5; eauto ; try (do 2 right; left; auto).
          destruct (eq_nat_dec dj6 n) as [N6| N6].
           move N6 at top; subst dj6.
           remember It6 as H; clear HeqH.
           rewrite In5 in H; [ idtac | assumption ].
           apply negb_false_iff in H.
           rename H into Hcn.
           pose proof (In4 n N4) as H.
           rewrite Hcn in H; simpl in H.
           unfold rm_add_i in H.
           rewrite I6, It6, xorb_false_l in H.
           rename H into He6.
           remember Hu4 as H; clear HeqH.
           eapply carry_before_relay in H; [ idtac | eassumption ].
           simpl in H; rewrite I4 in H; rename H into He4.
           remember Hu5 as H; clear HeqH.
           eapply carry_before_relay in H; [ idtac | eassumption ].
           simpl in H; rewrite I5 in H; rename H into He5.
           remember (S (j + n)) as k eqn:Hk .
           remember He4 as H; clear HeqH.
           unfold carry in H; simpl in H.
           remember (fst_same (a + b) c (S k)) as v4 eqn:Hv4 .
           symmetry in Hv4; rename H into J4.
           remember He5 as H; clear HeqH.
           unfold carry in H; simpl in H.
           remember (fst_same b c (S k)) as v5 eqn:Hv5 .
           symmetry in Hv5; rename H into J5.
           remember He6 as H; clear HeqH.
           unfold carry in H; simpl in H.
           remember (fst_same a b (S k)) as v6 eqn:Hv6 .
           symmetry in Hv6; rename H into J6.
           destruct v4 as [dk4| ]; [ idtac | discriminate J4 ].
           destruct v6 as [dk6| ]; [ idtac | discriminate J6 ].
           destruct v5 as [dk5| ].
            remember (List.fold_right min dk6 [dk4; dk5 … []]) as p eqn:Hp .
            remember Hv4 as H; clear HeqH.
            apply fst_same_iff in H; simpl in H.
            destruct H as (Jn4, Jt4).
            rewrite J4 in Jt4; symmetry in Jt4.
            remember Hv5 as H; clear HeqH.
            apply fst_same_iff in H; simpl in H.
            destruct H as (Jn5, Jt5).
            rewrite J5 in Jt5; symmetry in Jt5.
            remember Hv6 as H; clear HeqH.
            apply fst_same_iff in H; simpl in H.
            destruct H as (Jn6, Jt6).
            rewrite J6 in Jt6; symmetry in Jt6.
            destruct (eq_nat_dec dk4 p) as [P4| P4].
             move P4 at top; subst dk4.
             destruct (eq_nat_dec dk5 p) as [P5| P5].
              move P5 at top; subst dk5.
              rewrite Jt4 in Jt5; discriminate Jt5.

              eapply min_neq_lt in P5; eauto ; try (do 2 right; left; auto).
              destruct (eq_nat_dec dk6 p) as [P6| P6].
               move P6 at top; subst dk6.
               remember P5 as H; clear HeqH.
               apply Jn5 in H.
               rewrite Jt6, Jt4 in H.
               discriminate H.

               eapply min_neq_lt in P6; eauto ; try (left; auto).
               remember J4 as H; clear HeqH.
               unfold rm_add_i in H.
               rewrite Jn6 in H; [ idtac | assumption ].
               rewrite negb_xorb_diag_l, xorb_true_l in H.
               apply negb_false_iff in H.
               apply carry_before_relay with (dj := p) in Hv6; auto.
               simpl in Hv6; rewrite H, J6 in Hv6.
               discriminate Hv6.

             eapply min_neq_lt in P4; eauto ; try (right; left; auto).
             destruct (eq_nat_dec dk5 p) as [P5| P5].
              move P5 at top; subst dk5.
              destruct (eq_nat_dec dk6 p) as [P6| P6].
               move P6 at top; subst dk6.
               rewrite Jt6 in J5; discriminate J5.

               eapply min_neq_lt in P6; eauto ; try (left; auto).
               pose proof (Jn4 p P4) as H.
               rewrite Jt5 in H; simpl in H.
               unfold rm_add_i in H.
               rewrite Jn6 in H; [ idtac | assumption ].
               rewrite negb_xorb_diag_l, xorb_true_l in H.
               apply negb_false_iff in H.
               apply carry_before_relay with (dj := p) in Hv6; auto.
               simpl in Hv6; rewrite H, J6 in Hv6.
               discriminate Hv6.

              eapply min_neq_lt in P5; eauto ; try (do 2 right; left; auto).
              destruct (eq_nat_dec dk6 p) as [P6| P6].
               move P6 at top; subst dk6.
               remember Jt6 as H; clear HeqH.
               rewrite Jn5 in H; [ idtac | assumption ].
               apply negb_false_iff in H.
               rename H into Hf6.
               pose proof (Jn4 p P4) as H.
               rewrite Hf6 in H; simpl in H.
               unfold rm_add_i in H.
               rewrite J6, Jt6, xorb_false_l in H.
               rename H into Je6.
               remember Hv4 as H; clear HeqH.
               eapply carry_before_relay in H; [ idtac | eassumption ].
               simpl in H; rewrite J4 in H; rename H into Je4.
               remember Hv5 as H; clear HeqH.
               eapply carry_before_relay in H; [ idtac | eassumption ].
               simpl in H; rewrite J5 in H; rename H into Je5.
bbb.
répétition du motif co-inductif !
oui, mais il faut bien que le 1 1 arrive un jour pour b c
qui briserait peut-être la boucle infernale.
et pis aussi le 0 0 pour a+b c

Faut voir aussi ceci :
  Hs5 : fst_same b c (S i) = Some m
  Hu5 : fst_same b c (S j) = Some dj5
  Hv5 : fst_same b c (S k) = Some dk5
  Hj : j = S (i + m)
  Hk : k = S (j + n)
  N5 : n < dj5
En fait, dj5 et dk5 sont liés à m, etc.

m=j
n=k
       i  i+1  -   m   -   n   -   p
  b    .   .   .   1   .   0   .   0
1          ≠   ≠    +0 ≠    +0 ≠    +0
  a    .   .   .   1   .   0   .   0
1          ≠   ≠
 b+c   .   .   .   1   .   0   .   0

 a+b   .   .   .   0   .   0   .   0
0          ≠   ≠   ≠+0 ≠   ≠+0      +0
  c    .   .   .   1   .   1   .   1
1          ≠   ≠    +1 ≠   ≠+1 ≠   ≠+1
  b    .   .   .   1   .   0   .   0


       i  i+1  -   m
  b    .   .   .   1
1          ≠   ≠    +0
  a    .   .   .   1
1          ≠   ≠
 b+c   .   .   .   1

 a+b   .   .   .   0
0          ≠   ≠   ≠+0
  c    .   .   .   1
1          ≠   ≠    +1
  b    .   .   .   1

        remember (di4 - S m) as di.
        apply nat_sub_add_r in Heqdi; [ idtac | assumption ].
        subst di4; clear M4 Hm.
        rewrite Nat.add_assoc in H4, Ht4.
        rewrite Nat.add_succ_r in Hs4, H4, Hn4, Ht4.
        induction di.
         rewrite Nat.add_0_r in Hs4, H4, Hn4, Ht4.
         remember Ht3 as H; clear HeqH.
         unfold rm_add_i in H; simpl in H.
         rewrite Ht6, Ht5, xorb_nilpotent, xorb_false_l in H.
         rewrite carry_comm in H.
         apply after_carry_negb in H; [ idtac | assumption ].
         rename H into Hbm.
         pose proof (Hn4 m (Nat.lt_succ_diag_r m)) as H.
         rewrite Ht5 in H; simpl in H.
         unfold rm_add_i in H.
         rewrite H3, H5, xorb_nilpotent, xorb_false_l in H.
         rename H into Hem.
         remember Hem as H; clear HeqH.
         rewrite carry_comm in H.
         apply after_carry_negb in H; [ idtac | assumption ].
         rename H into Ham.
         remember H4 as H; clear HeqH.
         unfold rm_add_i in H.
         rewrite Ham, Hbm, xorb_true_l in H.
         apply negb_false_iff in H.
         erewrite carry_succ_diff in H; try eassumption.
         discriminate H.
bbb.

Hyp b.[m+1]=1
       i  i+1  -   m   -   -   i4
  b    .   .   .   1   1   .   .
1          ≠   ≠    +0  +₀
  a    .   .   .   1   ₀   .   .
1          ≠   ≠
 b+c   .   .   .   1   .   .   .

 a+b   .   .   .   0   1   .   0
0          ≠   ≠   ≠+0 ≠   ≠
  c    .   .   .   1   ₀   .   0
1          ≠   ≠    +1  +1
  b    .   .   .   1   1   .   .


       i  i+1  -   m
  b    .   0   0   1
1          ≠   ≠    +0
  a    .   1   1   1
1          ≠   ≠
 b+c   .   0   0   1

 a+b   .   0   0   0
0          ≠   ≠
  c    .   1   1   1
1          ≠+1 ≠+1  +1
  b    .   0   0   1

      remember H3 as H; clear HeqH.
      rewrite H6 in H.
      move H at top; subst u.
bbb.

    destruct (eq_nat_dec di3 m) as [M3| M3].
     move M3 at top; subst di3.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       remember H3 as H; clear HeqH.
       rewrite H6 in H; move H at top; subst u.
       rewrite Hs4 in Hs5; discriminate Hs5.
       destruct (eq_nat_dec di6 m) as [M6| M6].
        move M6 at top; subst di6.
        move M6 at top; subst di6; rewrite H6 in Hs6; symmetry in Hs6.
bbb.
       i  i+1  -   m
  b    .   .   .   1
u          ≠   ≠
  a    .   .   .   1
1          ≠   ≠
 b+c   .   .   .   1

 a+b   .   .   .   .
0          ≠   ≠
  c    .   .   .   .
u          ≠   ≠
  b    .   .   .   .

    assert (0 < di3 ∧ 0 < di4 ∧ 0 < di5 ∧ 0 < di6) as H.
     apply Nat.lt_lt_0 in H1.
     rewrite Hm in H1; simpl in H1.
     apply Nat.min_glb_lt_iff in H1.
     rewrite and_comm, and_assoc.
     split; [ destruct H1; assumption | idtac ].
     destruct H1 as (_, H1).
     apply Nat.min_glb_lt_iff in H1.
     rewrite and_assoc.
     split; [ destruct H1; assumption | idtac ].
     destruct H1 as (_, H1).
     apply Nat.min_glb_lt_iff in H1.
     assumption.

     destruct H as (M3, (M4, (M5, M6))).
     apply Hn3 in M3; apply Hn4 in M4.
     apply Hn5 in M5; apply Hn6 in M6.
     rewrite Nat.add_0_r in M3, M4, M5, M6.
     remember Hc3 as H; clear HeqH.
     rewrite carry_comm in H.
     eapply carry_succ_diff in H; [ idtac | reflexivity | assumption ].
     rewrite carry_comm in H; rename H into Hg3.
     remember Hc4 as H; clear HeqH; rewrite carry_comm in H.
     eapply carry_succ_diff in H; [ idtac | reflexivity | assumption ].
     rewrite carry_comm in H; rename H into Hg4.
     remember Hc5 as H; clear HeqH; rewrite carry_comm in H.
     eapply carry_succ_diff in H; [ idtac | reflexivity | assumption ].
     rewrite carry_comm in H; rename H into Hg5.
     remember Hc6 as H; clear HeqH; rewrite carry_comm in H.
     eapply carry_succ_diff in H; [ idtac | reflexivity | assumption ].
     rewrite carry_comm in H; rename H into Hg6.
     eapply IHi.
bbb.
merde, c'est de la co-induction, pas de l'induction
bordel à queue

bon, il faut en fait faire l'induction plus tard, sur (m-S (S i)), un
truc comme ça.

il faut se ramener à un problème où m = min

i+1<min → co-induct
       i  i+1
  b    .  ¬u
u          ≠+u
  a    .   u
1          ≠+1
 b+c   .  ¬u

 a+b   .  ¬u
0          ≠+0
  c    .   u
u          ≠+u
  b    .  ¬u

bbb.
intros a₀ b₀ c₀ a b c i u Ha₀ Hb₀ Hc₀ Hc1 Hc2 Hc3 Hc4 Hc5 Hc6.
remember Hc4 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (a + b) c (S i)) as s1 eqn:Hs1 .
destruct s1 as [di1| ]; [ idtac | discriminate H ].
rename H into He1.
remember Hc5 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same b c (S i)) as s2 eqn:Hs2 .
destruct s2 as [di2| ]; [ idtac | clear H ].
 rename H into Hb2.
 destruct (lt_eq_lt_dec di2 di1) as [[H1| H1]| H1].
  remember Hc3 as H; clear HeqH.
  unfold carry in H; simpl in H.
  remember (fst_same a (b + c) (S i)) as s3 eqn:Hs3 .
  destruct s3 as [di3| ]; [ idtac | clear H ].
   rename H into Ha3.
   symmetry in Hs1, Hs2, Hs3.
   destruct (lt_eq_lt_dec di3 di2) as [[H2| H2]| H2].
    eapply subcase_2a; eassumption.

    subst di3.
    eapply subcase_2b; eassumption.

    remember Hs3 as H; clear HeqH.
    eapply carry_before_relay in H; [ idtac | eassumption ].
    simpl in H; rewrite Ha3 in H.
    rename H into Hg3.
    remember Hs1 as H; clear HeqH.
    eapply carry_before_relay in H; [ idtac | eassumption ].
    simpl in H; rewrite He1 in H.
    rename H into Hg4.
    remember (carry b c (S (i + di2))) as t eqn:Hg5 .
    symmetry in Hg5.
    move t before u.
    remember Hs3 as H; clear HeqH.
    apply fst_same_iff in H; simpl in H.
    destruct H as (Hn3, Ht3).
    pose proof (Hn3 di2 H2) as H.
    unfold rm_add_i in H.
    remember Hs2 as HH; clear HeqHH.
    apply fst_same_iff in HH; simpl in HH.
    destruct HH as (Hn2, Ht2).
    rewrite Ht2, Hg5, xorb_nilpotent, xorb_false_l in H.
    remember Hs1 as HH; clear HeqHH.
    apply fst_same_iff in HH; simpl in HH.
    destruct HH as (Hn1, Ht1).
    pose proof (Hn1 di2 H1) as HH.
    unfold rm_add_i in HH.
    rewrite <- Ht2, H, Hb2, xorb_shuffle0, xorb_comm in HH.
    apply xorb_move_l_r_1 in HH.
    rewrite negb_xorb_diag_r in HH.
    rewrite <- negb_xorb_l in HH.
    apply negb_true_iff in HH.
    apply xorb_eq in HH; symmetry in HH.
    rename HH into Hg6; move Hg6 before Hg5.
    clear Hn3 Ht3 H Hn2 Ht2 Hn1 Ht1.
bbb.
x≠t et i+1<min → contrad
       i  i+1
  b    .  ¬t
x
  a    .   t
y
 b+c   .  ¬t

 a+b   .  ¬x
z
  c    .   x
t
  b    .  ¬x


i+1=min=(a,b+c)<oth → contrad
       i  i+1
  b    .   0
u          ≠
  a    .   1
1
 b+c   .   1=¬u  \
                   contrad
 a+b   .   0=¬u  /
0          ≠
  c    .   1
u          ≠
  b    .   0

i+1=min=(a,b)<oth → induc
       i  i+1
  b    .   u
u           +u
  a    .   u
1          ≠+1
 b+c   .  ¬u

 a+b   .   u
0          ≠+0
  c    .  ¬u
u          ≠+u
  b    .   u


       i  i+1
  b    .   .
u          ≠
  a    .   .
1          ≠
 b+c   .   .

 a+b   .   .
0          ≠
  c    .   .
u          ≠
  b    .   .



       i  i+1  -   i2  -   i1
  b    .   .   .   u   .   .
u           +u  +u  +t
  a    .   u   u  ¬t   .   .
1          ≠   ≠   ≠+1
 b+c   .   .   .   t   .   .

 a+b   .   .   .   .   .   0
0          ≠   ≠   ≠+0 ≠
  c    .   .   .   u   .   0
u          ≠   ≠    +t
  b    .   .   .   u   .   .


       i  i+1  -   i2  -   i1
  b    .   .   .   .   .   .
u
  a    .   .   .   .   .   .
1          ≠   ≠   ≠
 b+c   .   .   .   .   .   .

 a+b   .   .   .   .   .   0
0          ≠   ≠   ≠   ≠
  c    .   .   .   u   .   0
u          ≠   ≠
  b    .   .   .   u   .   .

    remember (di3 - S di2) as di.
    apply nat_sub_add_r in Heqdi; [ idtac | assumption ].
    subst di3; clear H2.
(*
    revert Hc6 Hs1 Hs2 Hs3 He1 Hb2 Ha3 H1; clear; intros.
    revert i di1 di2 Hc6 Hs1 Hs2 Hs3 He1 Hb2 Ha3 H1.
    induction di; intros.
*)
    destruct di.
(**)
     remember (carry b c (S (i + di2))) as t eqn:Hg5 .
     symmetry in Hg5.
     destruct t.
      assert (carry a b (S (i + di2)) = true) as Hg6.
       remember Hs1 as H; clear HeqH.
       apply fst_same_iff in H; simpl in H.
       destruct H as (Hn1, Hd1); rewrite He1 in Hd1; symmetry in Hd1.
       remember Hs2 as H; clear HeqH.
       apply fst_same_iff in H; simpl in H.
       destruct H as (Hn2, Hd2); rewrite Hb2 in Hd2; symmetry in Hd2.
       remember Hs3 as H; clear HeqH.
       apply fst_same_iff in H; simpl in H.
       destruct H as (Hn3, He3); rewrite Ha3 in He3; symmetry in He3.
       rewrite Nat.add_1_r in Hn3.
       pose proof (Hn3 di2 (Nat.lt_succ_diag_r di2)) as H.
       unfold rm_add_i in H.
       rewrite Hb2, Hd2, xorb_nilpotent, xorb_false_l in H.
       rewrite Hg5 in H; simpl in H.
       pose proof (Hn1 di2 H1) as HH.
       rewrite Hd2 in HH; simpl in HH.
       unfold rm_add_i in HH.
       rewrite H, Hb2, xorb_false_l in HH.
       apply xorb_move_l_r_1 in HH.
       rewrite negb_xorb_diag_r in HH.
       assumption.

       rewrite Nat.add_assoc, <- Nat.add_succ_l in Ha3.
       rename i into i₀.
       remember (S (i₀ + di2)) as i eqn:Hi .
       rename Hc3 into Hc3₀; rename Hc4 into Hc4₀.
       rename Hc5 into Hc5₀; rename Hc6 into Hc6₀.
       rename Hg3 into Hc3; rename Hg4 into Hc4.
       rename Hg5 into Hc5; rename Hg6 into Hc6.
       rename Hs1 into Hs1₀; rename Hs2 into Hs2₀.
       rename Hs3 into Hs3₀; rename He1 into He1₀.
       rename Hb2 into Hb2₀; rename Ha3 into Ha3₀.
       rename di1 into di1₀; rename di2 into di2₀.
       rename H1 into H1₀.
       remember Hc4 as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same (a + b) c (S i)) as s1 eqn:Hs1 .
       destruct s1 as [di1| ]; [ idtac | discriminate H ].
       rename H into He1.
       remember Hc5 as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same b c (S i)) as s2 eqn:Hs2 .
       destruct s2 as [di2| ]; [ idtac | clear H ].
        rename H into Hb2.
        destruct (lt_eq_lt_dec di2 di1) as [[H1| H1]| H1].
         remember Hc3 as H; clear HeqH.
         unfold carry in H; simpl in H.
         remember (fst_same a (b + c) (S i)) as s3 eqn:Hs3 .
         destruct s3 as [di3| ]; [ idtac | clear H ].
          rename H into Ha3.
          symmetry in Hs1, Hs2, Hs3.
          destruct (lt_eq_lt_dec di3 di2) as [[H2| H2]| H2].
           eapply subcase_2a; eassumption.

           subst di3.
           eapply subcase_2b; eassumption.

           rewrite Hi in Hs3.
           rewrite Nat.add_1_r in Hs3₀.
           apply fst_same_iff in Hs3₀; simpl in Hs3₀.
           apply fst_same_iff in Hs3; simpl in Hs3.
           destruct Hs3₀ as (Hn3₀, Hs3₀).
           destruct Hs3 as (Hn3, Hs3).
           destruct di3; [ revert H2; apply Nat.nlt_0_r | idtac ].
           pose proof (Hn3 0 (Nat.lt_0_succ di3)) as H.
           rewrite Nat.add_0_r in H.
           rewrite Nat.add_succ_r in Hs3₀.
           rewrite <- Hs3₀ in H.
           symmetry in H; revert H; apply no_fixpoint_negb.

          apply fst_same_iff in Hs3₀; simpl in Hs3₀.
          apply fst_same_sym_iff in Hs3; simpl in Hs3.
          destruct Hs3₀ as (Hn3₀, Hs3₀).
          rewrite Hi in Hs3.
          pose proof (Hs3 0) as H.
          rewrite <- Nat.add_succ_r in H.
          rewrite Nat.add_succ_l in H.
          rewrite <- Nat.add_assoc in H.
          rewrite <- Hs3₀ in H.
          symmetry in H; revert H; apply no_fixpoint_negb.

         subst di2.
         apply fst_same_sym_iff in Hs1; simpl in Hs1.
         apply fst_same_sym_iff in Hs2; simpl in Hs2.
         destruct Hs1 as (Hn1, Hs1).
         destruct Hs2 as (Hn2, Hs2).
         rewrite Hb2 in Hs2; symmetry in Hs2.
         rewrite Hs2 in Hs1.
         rewrite Hs1 in He1; discriminate He1.

         apply fst_same_iff in Hs3₀; simpl in Hs3₀.
         destruct Hs3₀ as (Hn3₀, Hs3₀).
         rewrite Nat.add_assoc, <- Nat.add_succ_l, <- Hi in Hs3₀.
         rewrite Ha3₀ in Hs3₀; symmetry in Hs3₀.
         unfold rm_add_i in Hs3₀.
         apply fst_same_sym_iff in Hs2; simpl in Hs2.
         destruct Hs2 as (Hn2, Hs2).
         assert (0 < di2) as H by (eapply Nat.lt_lt_0; eauto ).
         apply Hn2 in H.
         rewrite Nat.add_0_r in H.
         rewrite Nat.add_1_r, H in Hs3₀.
         rewrite negb_xorb_diag_l, xorb_true_l in Hs3₀.
         symmetry in Hs3₀; apply negb_sym in Hs3₀.
         apply carry_succ_negb in Hs3₀; [ idtac | assumption ].
         destruct Hs3₀ as (H2, H3).
         rewrite H2, H3 in H.
         discriminate H.

        apply fst_same_iff in Hs3₀; simpl in Hs3₀.
        destruct Hs3₀ as (Hn3₀, Hs3₀).
        rewrite Nat.add_assoc, <- Nat.add_succ_l, <- Hi in Hs3₀.
        rewrite Ha3₀ in Hs3₀; symmetry in Hs3₀.
        unfold rm_add_i in Hs3₀.
        apply fst_same_sym_iff in Hs2; simpl in Hs2.
        pose proof (Hs2 0) as H.
        rewrite Nat.add_0_r in H.
        rewrite Nat.add_1_r, H in Hs3₀.
        rewrite negb_xorb_diag_l, xorb_true_l in Hs3₀.
        symmetry in Hs3₀; apply negb_sym in Hs3₀.
        apply carry_succ_negb in Hs3₀; [ idtac | assumption ].
        destruct Hs3₀ as (H2, H3).
        rewrite H2, H3 in H.
        discriminate H.

bbb.
      remember (di1 - S di2) as di.
      apply nat_sub_add_r in Heqdi; [ idtac | assumption ].
      subst di1; clear H1.
      rewrite Nat.add_1_r in Hs3, Ha3.
      rewrite Nat.add_succ_r in Ha3, Hs1, He1, He1.
      rewrite Nat.add_assoc, <- Nat.add_succ_l in He1.
      clear Ha3.
(*
      revert i u di2 Hs1 Hs2 Hs3 Hb2 Hc6 He1 Hg3 Hg4 Hg5.
      induction di; intros.
*)
      destruct di.
(**)
        assert (a .[ S (S (i + di2))] = true) as Ha3.
         remember Hg3 as H; clear HeqH.
         unfold carry in H.
         replace (S di2) with (S di2 + 0) in Hs3 by apply Nat.add_0_r.
         apply same_fst_same in Hs3.
         rewrite Nat.add_succ_r in Hs3; simpl in Hs3.
         rewrite Hs3, Nat.add_0_r in H; assumption.

        rewrite Nat.add_0_r in Hs1, He1.
        remember Hs1 as H; clear HeqH.
        apply fst_same_iff in H; simpl in H.
        destruct H as (Hn1, Ht1).
        rewrite Nat.add_succ_r, He1 in Ht1.
        symmetry in Ht1.
        remember Hs2 as H; clear HeqH.
        apply fst_same_iff in H; simpl in H.
        destruct H as (Hn2, Ht2).
        rewrite Hb2 in Ht2; symmetry in Ht2.
        pose proof (Hn1 di2 (Nat.lt_succ_diag_r di2)) as H.
        rewrite Ht2 in H; simpl in H.
        rename H into He2.
        remember Hs3 as H; clear HeqH.
        apply fst_same_iff in H; simpl in H.
        destruct H as (Hn3, Ht3).
        rewrite Nat.add_succ_r in Ht3.
        pose proof (Hn3 di2 (Nat.lt_succ_diag_r di2)) as H.
        unfold rm_add_i in H.
        rewrite Hb2, Ht2, Hg5 in H; simpl in H.
        rewrite xorb_nilpotent in H; simpl in H.
        rename H into Ha2.
        remember He2 as H; clear HeqH.
        unfold rm_add_i in H.
        rewrite Ha2, Hb2, xorb_true_l in H.
        apply xorb_move_l_r_1 in H.
        rewrite xorb_nilpotent in H.
        rename H into Hf2.
        remember He1 as H; clear HeqH.
        unfold rm_add_i in H.
        rewrite Ha3, xorb_true_l in H.
        apply xorb_eq in H.
        remember b .[ S (S (i + di2))] as x eqn:Hb3 .
        symmetry in Hb3, H.
        destruct x.
         apply carry_x_before_xx with (a := a) in Hb3; try assumption.
         rewrite Hf2 in Hb3; discriminate Hb3.

         apply carry_succ_negb in H; [ idtac | assumption ].
         rewrite Ha3 in H.
         destruct H as (H, _); discriminate H.

        rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs1.
        remember He1 as H; clear HeqH.
        unfold rm_add_i in H.
        rename H into He2.
        remember Hs2 as H; clear HeqH.
        apply fst_same_iff in H; simpl in H.
        destruct H as (Hn2, Ht2).
        rewrite Hb2 in Ht2; symmetry in Ht2; move Ht2 before Hb2.
        remember Hs3 as H; clear HeqH.
        apply fst_same_iff in H; simpl in H.
        destruct H as (Hn3, Ht3).
        pose proof (Hn3 di2 (Nat.lt_succ_diag_r di2)) as H.
        unfold rm_add_i in H; simpl in H.
        rewrite Hb2, Ht2, Hg5, xorb_nilpotent in H; simpl in H.
        rename H into Ha2; move Ha2 after Hb2.
        remember Hs1 as H; clear HeqH.
        apply fst_same_iff in H; simpl in H.
        destruct H as (Hn1, Ht1).
        remember Hg3 as H; clear HeqH.
        unfold carry in H; simpl in H.
        rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H.
        replace (S di2) with (S di2 + 0) in Hs3 by apply Nat.add_0_r.
        erewrite same_fst_same in H; [ idtac | eassumption ].
        rewrite Nat.add_0_r in H.
        rename H into Ha3.
        rewrite Nat.add_succ_r in Ht3.
        rewrite Ha3 in Ht3; symmetry in Ht3.
        do 2 rewrite Nat.add_succ_r in Ht1.
        rewrite Nat.add_assoc in Ht1.
        destruct di.
         rewrite Nat.add_0_r in Hs1, Hn1, Ht1.
         rewrite Nat.add_1_r in He1, He2.
         pose proof (Nat.lt_succ_diag_r di2) as H.
         apply Nat.lt_lt_succ_r in H.
         apply Hn1 in H.
         rewrite Ht2 in H.
         unfold rm_add_i in H; simpl in H.
         rewrite Ha2, Hb2, xorb_true_l in H.
         apply xorb_move_l_r_1 in H.
         rewrite xorb_nilpotent in H.
         rename H into Hf2; move Hf2 before Ht2.
         move Ha3 before Hf2.
         remember Hf2 as H; clear HeqH.
         apply after_carry_negb in H; [ idtac | assumption ].
         rename H into Hb3; move Hb3 before Ha3.
         remember Hf2 as H; clear HeqH.
         eapply carry_succ_diff in H; try eassumption.
         rename H into Hf3; move Hf3 before Hb3.
         pose proof (Hn1 (S di2) (Nat.lt_succ_diag_r (S di2))) as H.
         rewrite Nat.add_succ_r in H.
         unfold rm_add_i in H.
         rewrite Ha3, Hb3, Hf3, xorb_true_l in H.
         apply negb_sym in H; simpl in H.
         rename H into Hd3; move Hd3 before Hb3.
         move Ht3 before Hd3.
         remember Ht3 as H; clear HeqH.
         unfold rm_add_i in H.
         rewrite Hb3, Hd3, xorb_false_l in H.
         rename H into Hh3; move Hh3 before Hf3.
         rewrite He1 in Ht1; symmetry in Ht1.
         move Ht1 before Hh3; move He1 before Ht1.
         remember Hh3 as H; clear HeqH.
         rewrite carry_comm in H.
         apply after_carry_negb in H; [ idtac | assumption ].
         rename H into Hb4; move Hb4 after Ht1.
         remember Hf3 as H; clear HeqH.
         rewrite carry_comm in H.
         apply after_carry_negb in H; [ idtac | assumption ].
         rename H into Ha4; move Ha4 after Hb4.
         rewrite Ha4, Hb4, xorb_true_r, xorb_true_l in He2.
         apply negb_false_iff in He2.
         erewrite carry_succ_diff in He2; try eassumption.
         discriminate He2.

         move Ha3 before Ht2; move Ht3 before Ha3.
         rewrite Nat.add_succ_r in He1, He2, Ht1.
         rewrite Nat.add_succ_r in He1, He2.
         simpl in He1, He2, Ht1.
         rewrite Nat.add_succ_r in Hn1.
         assert (di2 < S (S (S (di2 + di)))) as H by omega.
         apply Hn1 in H.
         rewrite Ht2 in H; simpl in H.
         rename H into Hf2; move Hf2 before Ht2.
         remember Hf2 as H; clear HeqH.
         unfold rm_add_i in H.
         rewrite Ha2, Hb2, xorb_true_l in H.
         apply xorb_move_l_r_1 in H.
         rewrite xorb_nilpotent in H.
         rename H into Hh2; move Hh2 before Hf2.
         remember Ha2 as H; clear HeqH.
         rewrite Hn3 in H; [ idtac | apply Nat.lt_succ_diag_r ].
         apply negb_true_iff in H.
         rename H into Hi2; move Hi2 before Hf2.
         remember Hh2 as H; clear HeqH.
         apply after_carry_negb in H; [ idtac | assumption ].
         rename H into Hb3; move Hb3 before Ha3.
         remember Hh2 as H; clear HeqH.
         eapply carry_succ_diff in H; try eassumption.
         rename H into Hf3; move Hf3 before Ht3.
         remember (rm_add_i a b (S (S (i + di2)))) as x eqn:H .
         symmetry in H.
         remember H as He3; clear HeqHe3.
         move He3 after Ht3.
         unfold rm_add_i in H; simpl in H.
         rewrite Ha3, Hb3, Hf3 in H; simpl in H.
         rewrite <- H in He3; clear x H.
         assert (S di2 < S (S (S (di2 + di)))) as H by omega.
         apply Hn1 in H.
         rewrite Nat.add_succ_r, He3 in H; symmetry in H.
         apply negb_true_iff in H.
         rename H into Hd3; move Hd3 before Hb3.
         remember Ht3 as H; clear HeqH.
         unfold rm_add_i in H.
         rewrite Hb3, Hd3, xorb_false_l in H.
         rename H into Hh3; move Hh3 before Hf3.
         remember b .[ S (S (S (i + di2)))] as x eqn:Hx .
         symmetry in Hx.
         destruct (bool_dec x false) as [H1| H1].
          move H1 at top; subst x.
          rename Hx into Hb4; move Hb4 before Hh3.
          remember Hh3 as H; clear HeqH.
          apply after_carry_negb in H; [ idtac | assumption ].
          rename H into Hd4; move Hd4 before Hb4.
          assert (S (S di2) < S (S (S (di2 + di)))) as H by omega.
          apply Hn1 in H.
          do 2 rewrite Nat.add_succ_r in H.
          rewrite Hd4 in H; simpl in H.
          rename H into He4; move He4 before Hd4.
          remember He4 as H; clear HeqH.
          unfold rm_add_i in H; simpl in H.
          rewrite Hb4, xorb_false_r in H.
          apply xorb_eq in H.
          remember a .[ S (S (S (i + di2)))] as x eqn:Hx .
          symmetry in Hx, H.
          destruct x.
           eapply carry_succ_diff in Hx; try eassumption.
           rewrite Hx in H; discriminate H.

           rename Hx into Ha4; move Ha4 after Hb4.
           rename H into Hf4; move Hf4 before He4.
           remember Hh3 as H; clear HeqH.
           eapply carry_succ_diff in H; try eassumption.
           rename H into Hh4; move Hh4 before Hf4.
bbb.
do an induction on (di - S di2)?

Hyp: b.[i2+2]=0

       i  i+1  -   i2  +1  -   di
  b    .   .   .   u   0   ₀   1
u                   +0  +0  +₀  +1  <-- contrad
  a    .   .   .   1   1   ₀   ₀
1          ≠   ≠   ≠+1
 b+c   .   .   .   0   1   ₀   1

 a+b   .   .   .   .   1   ₀   0
0          ≠   ≠   ≠+0 ≠   ≠
  c    .   .   .   u   0   1   0
u          ≠   ≠    +0  +1  +1  +1
  b    .   .   .   u   0   ₀   1


       i  i+1  -   i2  +1  -   di
  b    .   .   .   u   .   .   .
u
  a    .   .   .   .   .   .   .
1          ≠   ≠   ≠+1
 b+c   .   .   .   .   .   .   .

 a+b   .   .   .   .   .   .   0
0          ≠   ≠   ≠+0 ≠   ≠
  c    .   .   .   .   .   .   .
u          ≠   ≠    +0
  b    .   .   .   u   .   .   .

         remember (S (i + di2)) as j eqn:Hj .
         replace j with (j + 0) in Hg3, Hg4, Hg5 by apply Nat.add_0_r.
         replace j with (j + 0) in Hb2, Ha3 by apply Nat.add_0_r.
         subst j.
         simpl in Hg3, Hg4, Hg5, Ha3, Hb2.
bbb.
         eapply IHdi with (i := i + di2); try eassumption; simpl.
          rewrite Nat.add_0_r in Hb2, Ha3, Hg3, Hg4, Hg5.
          apply carry_x_before_xx; [ idtac | assumption ].
          remember Hs3 as H; clear HeqH.
          apply fst_same_iff in H; simpl in H.
          destruct H as (Hn3, Ht3).
          rewrite Hn3; [ idtac | apply Nat.lt_succ_diag_r ].
          apply negb_true_iff.
          unfold rm_add_i.
          rewrite Hb2, Hg5, xorb_true_l, xorb_false_r.
          apply negb_false_iff.
          remember Hs2 as H; clear HeqH.
          apply fst_same_iff in H; simpl in H.
          destruct H as (Hn2, Ht2).
          rewrite <- Ht2, Hb2; reflexivity.
bbb.
       i  i+1  -   i2  +1  -
  b    .   .   .   1   .   .
1       +1
  a    .   1   1   1   1   .
1          ≠   ≠   ≠+1
 b+c   .   0   0   0   1   .

 a+b   .   .   .   .   .   .   .   .   0
0                   +0
  c    .   .   .   1   .   .
1          ≠   ≠    +0
  b    .   .   .   1   .   .


          remember Hc6 as H; clear HeqH.
          unfold carry in H; simpl in H.
          remember (fst_same a b (S i)) as s6 eqn:Hs6 .
          apply fst_same_sym_iff in Hs6; simpl in Hs6.
          destruct s6 as [di6| ]; [ idtac | clear H ].
           destruct Hs6 as (Hn6, Ht6).
           rewrite H in Ht6; symmetry in Ht6.
           rename H into Ha6.
           destruct (lt_eq_lt_dec di2 di6) as [[H1| H1]| H1].
            remember H1 as H; clear HeqH.
            apply Hn6 in H.
            rewrite Hb2 in H; simpl in H.

bbb.

       i  i+1  -   i2  +1  -
  b    .   .   x   1   0   .
1           +1  +1  +0  +0
  a    .   1   1   1   1   .
1          ≠   ≠   ≠
 b+c   .   0   0   0   1   .

 a+b   .   .   x   0   1   .
0          ≠   ≠   ≠+0  +0
  c    .   .   .   1   0   .
1          ≠   ≠    +0  +1
  b    .   .   x   1   0   .


       i  i+1  -   i2  -   i3
  b    .   .   x   1   .   .
1           +1  +1  +t
  a    .   1   1  ¬t   .   1
1          ≠   ≠   ≠   ≠
 b+c   .   0   0   t   .   1

 a+b   .   .   x   0   .   .
0          ≠   ≠   ≠+0
  c    .   .   .   1   .   .
1          ≠   ≠    +t
  b    .   .   x   1   .   .

Theorem rm_add_assoc : ∀ a b c, (a + (b + c) = (a + b) + c)%rm.
Proof.
intros a b c.
apply rm_add_assoc_norm.
rename a into a₀; rename b into b₀; rename c into c₀.
remember (a₀ + 0)%rm as a.
remember (b₀ + 0)%rm as b.
remember (c₀ + 0)%rm as c.
unfold rm_eq; intros i; simpl.
unfold rm_add_i; simpl.
do 2 rewrite xorb_false_r.
remember (carry (a + (b + c))%rm 0%rm i) as c1 eqn:Hc1 .
remember (carry (a + b + c)%rm 0%rm i) as c2 eqn:Hc2 .
unfold rm_add_i; simpl.
remember (carry a (b + c)%rm i) as c3 eqn:Hc3 .
remember (carry (a + b)%rm c i) as c4 eqn:Hc4 .
unfold rm_add_i; simpl.
remember (carry b c i) as c5 eqn:Hc5 .
remember (carry a b i) as c6 eqn:Hc6 .
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

 apply case_1 with (a := c) (b := b) (c := a) (i := i).
  rewrite carry_comm.
  rewrite carry_compat_r with (a := (a + b)%rm); [ assumption | idtac ].
  apply rm_add_i_comm.

  rewrite carry_comm; assumption.

  rewrite carry_comm; assumption.

 eapply case_2 with (a := a) (b := b); eassumption.

bbb.
 apply case_1 with (c := a) (b := b) (a := c) (i := i).
  rewrite carry_compat_r with (a := (a + b + c)%rm); [ assumption | idtac ].
  intros j; simpl; symmetry.
  rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_compat_r with (a := (a + (b + c))%rm); [ assumption | idtac ].
  intros j; simpl; rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_comm.
  rewrite carry_compat_r with (a := (a + b)%rm); [ assumption | idtac ].
  apply rm_add_i_comm.

  rewrite carry_comm; assumption.

  rewrite carry_comm; assumption.

 eapply case_2; eassumption.

 eapply case_3; eassumption.

 apply case_2 with (c := a) (b := b) (a := c) (i := i).
  rewrite carry_compat_r with (a := (a + b + c)%rm); [ assumption | idtac ].
  intros j; simpl; symmetry.
  rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_compat_r with (a := (a + (b + c))%rm); [ assumption | idtac ].
  intros j; simpl; rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_comm.
  rewrite carry_compat_r with (a := (a + b)%rm); [ assumption | idtac ].
  apply rm_add_i_comm.

  rewrite carry_compat_r with (a := (b + c)%rm).
   rewrite carry_comm; assumption.

   apply rm_add_i_comm.

  rewrite carry_comm; assumption.

  rewrite carry_comm; assumption.

 apply case_3 with (c := a) (b := b) (a := c) (i := i).
  rewrite carry_compat_r with (a := (a + b + c)%rm); [ assumption | idtac ].
  intros j; simpl; symmetry.
  rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_compat_r with (a := (a + (b + c))%rm); [ assumption | idtac ].
  intros j; simpl; rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_comm.
  rewrite carry_compat_r with (a := (a + b)%rm); [ assumption | idtac ].
  apply rm_add_i_comm.

  rewrite carry_compat_r with (a := (b + c)%rm).
   rewrite carry_comm; assumption.

   apply rm_add_i_comm.

  rewrite carry_comm; assumption.

  rewrite carry_comm; assumption.

 eapply case_4; eassumption.

 apply case_4 with (c := a) (b := b) (a := c) (i := i).
  rewrite carry_compat_r with (a := (a + b + c)%rm); [ assumption | idtac ].
  intros j; simpl; symmetry.
  rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_compat_r with (a := (a + (b + c))%rm); [ assumption | idtac ].
  intros j; simpl; rewrite rm_add_i_comm.
  apply rm_add_i_compat_r, rm_add_i_comm.

  rewrite carry_comm.
  rewrite carry_compat_r with (a := (a + b)%rm); [ assumption | idtac ].
  apply rm_add_i_comm.

  rewrite carry_compat_r with (a := (b + c)%rm).
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

Theorem rm_add_assoc_hop : ∀ a b c, (a + (b + c) = (a + b) + c)%rm.
Proof.
intros a b c.
assert (∀ x, (x = x + 0)%rm) as Hx by (symmetry; apply rm_add_0_r).
setoid_replace (b + c)%rm with (b + c + 0)%rm by apply Hx.
setoid_replace (a + b)%rm with (a + b + 0)%rm by apply Hx.
setoid_replace a with (a + 0)%rm by apply Hx.
setoid_replace b with (b + 0)%rm by apply Hx.
setoid_replace c with (c + 0)%rm by apply Hx.
set (a1 := (a + 0)%rm).
set (b1 := (b + 0)%rm).
set (c1 := (c + 0)%rm).
rename a into a₀; rename b into b₀; rename c into c₀.
rename a1 into a; rename b1 into b; rename c1 into c.
unfold rm_eq; intros i; simpl.
rewrite rm_add_add2_i; symmetry.
rewrite rm_add_add2_i; symmetry.
unfold rm_add2_i; simpl.
do 2 rewrite xorb_false_r.
remember (carry (a + (b + c + 0))%rm 0%rm i) as c1 eqn:Hc1 .
remember (carry (a + b + 0 + c)%rm 0%rm i) as c2 eqn:Hc2 .
rewrite rm_add_add2_i; symmetry.
rewrite rm_add_add2_i; symmetry.
unfold rm_add2_i; simpl.
remember (carry a (b + c + 0)%rm i) as c3 eqn:Hc3 .
remember (carry (a + b + 0)%rm c i) as c4 eqn:Hc4 .
rewrite rm_add_add2_i; symmetry.
rewrite rm_add_add2_i; symmetry.
unfold rm_add2_i; simpl.
do 2 rewrite xorb_false_r.
remember (carry a₀ 0%rm i) as c5 eqn:Hc5 .
bbb.

Theorem rm_add_assoc_ini : ∀ a b c, (a + (b + c) = (a + b) + c)%rm.
Proof.
intros a b c.
assert (∀ x, (x = x + 0)%rm) as Hx by (symmetry; apply rm_add_0_r).
setoid_replace (b + c)%rm with (b + c + 0)%rm by apply Hx.
setoid_replace (a + b)%rm with (a + b + 0)%rm by apply Hx.
setoid_replace a with (a + 0)%rm by apply Hx.
setoid_replace b with (b + 0)%rm by apply Hx.
setoid_replace c with (c + 0)%rm by apply Hx.
set (a1 := (a + 0)%rm).
set (b1 := (b + 0)%rm).
set (c1 := (c + 0)%rm).
rename a into a₀; rename b into b₀; rename c into c₀.
rename a1 into a; rename b1 into b; rename c1 into c.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
remember (fst_same (a + (b + c + 0)%rm) 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 remember (fst_same ((a + b + 0)%rm + c) 0 si) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [di2| ].
  Focus 2.
  destruct (bool_dec ((a + b + 0)%rm) .[ si] c .[ si]) as [H1| H1].
   apply rm_add_inf_true_eq_if in Hs2; auto; simpl in Hs2.
   destruct Hs2 as (Hab, Hc).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

   apply neq_negb in H1.
   apply rm_add_inf_true_neq_if in Hs2; auto; simpl in Hs2.
   destruct Hs2 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

  Focus 2.
  destruct (bool_dec a .[ si] ((b + c + 0)%rm) .[ si]) as [H1| H1].
   apply rm_add_inf_true_eq_if in Hs1; auto; simpl in Hs1.
   destruct Hs1 as (Ha, Hbc).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

   apply neq_negb in H1.
   apply rm_add_inf_true_neq_if in Hs1; auto; simpl in Hs1.
   destruct Hs1 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

 destruct Hs1 as (Hn1, Hs1); rewrite Hs1, xorb_false_r.
 destruct Hs2 as (Hn2, Hs2); rewrite Hs2, xorb_false_r.
 clear di1 Hn1 Hs1 di2 Hn2 Hs2.
 unfold rm_add_i, carry; rewrite <- Heqsi; simpl.
 remember (rm_add_i a₀ 0 i) as xai eqn:Hxai .
 remember (rm_add_i (b + c) 0 i) as xbci eqn:Hxbci .
 remember (rm_add_i (a + b) 0 i) as xabi eqn:Hxabi .
 remember (rm_add_i c₀ 0 i) as xci eqn:Hxci .
 remember b .[ i] as xbi eqn:Hxbi ; simpl in Hxbi.
 symmetry in Hxai, Hxbci, Hxabi, Hxci, Hxbi.
 remember (fst_same a (b + c + 0)%rm si) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Hxbcs).
  remember (rm_add_i a₀ 0 (si + di1)) as xas eqn:Hxas .
  symmetry in Hxas, Hxbcs.
  remember (fst_same (a + b + 0)%rm c si) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s2 as [di2| ].
   destruct Hs2 as (Hn2, Hxabs); rewrite Hxabs.
   remember (rm_add_i c₀ 0 (si + di2)) as xcs eqn:Hxcs .
   symmetry in Hxcs.
   move Hxai at bottom; move Hxas at bottom.
   move Hxci at bottom; move Hxcs at bottom.
   move Hxabi at bottom; move Hxabs at bottom.
   move Hxbci at bottom; move Hxbcs at bottom.
   move Hxbi at bottom.
(*1-*)
   remember Hxabi as H; clear HeqH.
   subst a b.
   rewrite rm_add_i_norm_norm in H.
   set (a := (a₀ + 0)%rm) in *.
   set (b := (b₀ + 0)%rm) in *.
   move b before Hx; move a before Hx.
   rename H into Habi.
   remember Habi as H; clear HeqH.
   unfold rm_add_i, carry in H.
   rewrite <- Heqsi in H; simpl in H.
   rewrite Hxai, Hxbi in H.
   remember (fst_same a b si) as s3 eqn:Hs3 .
   apply fst_same_sym_iff in Hs3; simpl in Hs3.
   destruct s3 as [di3| ].
    destruct Hs3 as (Hn3, Hb3).
    symmetry in Hb3.
    apply xorb_move_l_r_1 in H.
    rewrite H in Hb3; rename H into Ha3.
    move Ha3 after Hb3; move Hn3 after Hxai.
    remember Hxbci as H; clear HeqH.
    subst b c.
    rewrite rm_add_i_norm_norm in H.
    set (b := (b₀ + 0)%rm) in *.
    set (c := (c₀ + 0)%rm) in *.
    move c before Hx; move b before Hx.
    remember H as Hbci; clear HeqHbci.
    unfold rm_add_i, carry in H.
    rewrite <- Heqsi in H; simpl in H.
    rewrite Hxbi, Hxci in H.
    remember (fst_same b c si) as s4 eqn:Hs4 .
    apply fst_same_sym_iff in Hs4; simpl in Hs4.
    destruct s4 as [di4| ].
     destruct Hs4 as (Hn4, Hc4).
     symmetry in Hc4.
     apply xorb_move_l_r_1 in H.
     rewrite H in Hc4; rename H into Hb4.
     move Hb4 after Hc4; move Hn4 after Hxai.
     move Hbci before Habi.
(*1-*)
     destruct (lt_dec di1 di3) as [H1| H1].
      remember H1 as H; clear HeqH.
      apply Hn3 in H.
      rewrite Hxas in H.
      apply negb_sym in H.
      destruct (lt_dec di3 di4) as [H4| H4].
       remember H4 as H4₀; clear HeqH4₀.
       apply Hn4 in H4₀.
       rewrite Hb3 in H4₀.
       apply negb_sym in H4₀.
       assert (di1 < di4) as H2 by omega.
       remember H2 as H2₀; clear HeqH2₀.
       apply Hn4 in H2₀.
       destruct (lt_dec di4 di2) as [H3| H3].
        remember H3 as H3₀; clear HeqH3₀.
        apply Hn2 in H3₀.
        rewrite Hc4 in H3₀.
        assert (di1 < di2) as H5 by omega.
        remember H5 as H5₀; clear HeqH5₀.
        apply Hn2 in H5₀.
        assert (di3 < di2) as H6 by omega.
        remember H6 as H6₀; clear HeqH6₀.
        apply Hn2 in H6₀.
        rewrite <- H2₀ in H5₀.
        rewrite H4₀ in H6₀.
        rewrite negb_involutive in H6₀.
(*
     assert (xas ⊕ xcs = xai ⊕ xabi ⊕ xci ⊕ xbci) as Hr.
*)
bbb.

     destruct xai, xas, xci, xcs, xabi, xbci; try reflexivity;
      try discriminate Hr.

bbb.
(*1-*)
     destruct xai, xas, xci, xcs, xabi, xbci; try reflexivity; exfalso;
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
          unfold rm_add_i, carry in Hxabs.
          rewrite <- Nat.add_succ_l in Hxabs.
          remember (S si) as ssi; simpl in Hxabs.
          rewrite xorb_false_r in Hxabs.
bbb.

(*-1*)
   destruct xai, xas, xci, xcs, xabi, xbci; try reflexivity; exfalso;
    destruct xbi, xbs.
    Focus 1.
bbb.
    destruct di2.
     rewrite Nat.add_0_r in Hxcs.
     apply not_true_iff_false in Hxbci.
     eapply Hxbci, case_1; eassumption.

     (* cf theorem case_1 *)
bbb.
     apply not_true_iff_false in Hxbci.
     apply Hxbci; clear Hxbci.
     apply eq_true_negb_classical; intros Hxbci.
     apply negb_true_iff in Hxbci.
     unfold rm_add_i, carry in Hxbci.
     rewrite <- Heqsi in Hxbci; simpl in Hxbci.
     rewrite xorb_false_r in Hxbci.
     unfold rm_add_i, carry in Hxbci at 1.
     rewrite <- Heqsi in Hxbci; simpl in Hxbci.
     rewrite Hxbi, Hxci, xorb_true_r in Hxbci.
     rewrite xorb_false_l in Hxbci.
     remember (fst_same b c si) as s1 eqn:Hs1 .
     apply fst_same_sym_iff in Hs1; simpl in Hs1.
     destruct s1 as [di3| ].
      destruct Hs1 as (Hn3, Hs3).
      destruct di3.
       rewrite Nat.add_0_r, Hxbs, xorb_true_l in Hxbci.
       apply negb_false_iff in Hxbci.
       remember (fst_same (b + c) 0 si) as s2 eqn:Hs2 .
       apply fst_same_sym_iff in Hs2; simpl in Hs2.
       destruct s2 as [di4| ].
        destruct Hs2 as (Hn4, Hs4); rewrite Hs4 in Hxbci.
        discriminate Hxbci.

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
       remember (fst_same (b + c) 0 si) as s4 eqn:Hs4 .
       apply fst_same_sym_iff in Hs4; simpl in Hs4.
       destruct s4 as [di4| ].
        destruct Hs4 as (Hn4, Hs4); rewrite Hs4, xorb_false_r in Hxbci.
        rewrite Hxbci in Hs3; symmetry in Hs3.

bbb.
   destruct di1.
    clear Hn1.
    rewrite Nat.add_0_r in Hxas, Hxbcs.
    destruct di2.
     clear Hn2.
     rewrite Nat.add_0_r in Hxcs, Hxabs.
     destruct xai, xas, xci, xcs, xabi, xbci; try reflexivity; exfalso;
      destruct bi, bs.
      apply not_true_iff_false in Hxbci.
      eapply Hxbci, case_1; eassumption.

      Focus 4.
      apply not_true_iff_false in Hxabi.
      eapply Hxabi, case_1; eassumption.
bbb.

Theorem rm_add_assoc : ∀ a b c, (a + (b + c) = (a + b) + c)%rm.
Proof.
intros a b c.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
remember (fst_same (a + (b + c)%rm) 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); rewrite Hs1, xorb_false_r.
 remember (fst_same ((a + b)%rm + c) 0 si) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [di2| ].
  destruct Hs2 as (Hn2, Hs2); rewrite Hs2, xorb_false_r.
bbb.
  unfold rm_add_i, carry.
  rewrite <- Heqsi; simpl.
  remember (fst_same a (b + c) si) as s3 eqn:Hs3 .
  apply fst_same_sym_iff in Hs3; simpl in Hs3.
  destruct s3 as [di3| ].
   destruct Hs3 as (Hn3, Hs3).
   remember (fst_same (a + b) c si) as s4 eqn:Hs4 .
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
    remember (fst_same b c si) as s5 eqn:Hs5 .
    apply fst_same_sym_iff in Hs5; simpl in Hs5.
    destruct s5 as [di5| ].
     destruct Hs5 as (Hn5, Hs5).
     remember (fst_same a b si) as s6 eqn:Hs6 .
     apply fst_same_sym_iff in Hs6; simpl in Hs6.
     destruct s6 as [di6| ].
      destruct Hs6 as (Hn6, Hs6).
bbb.

intros a b c.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry.
remember (fst_same a (b + c) (S i)) as s1 eqn:Hs1 .
symmetry in Hs1.
remember (fst_same (a + b) c (S i)) as s2 eqn:Hs2 .
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
  remember (fst_same a b (S i)) as s3 eqn:Hs3 .
  remember (fst_same b c (S i)) as s4 eqn:Hs4 .
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
    remember (fst_same a b (S (si + di2)))) as s5 eqn:Hs5 .
    remember (fst_same b c (S (si + di1)))) as s6 eqn:Hs6 .
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
       remember (fst_same a b (S (si + di1)))) as s7 eqn:Hs7 .
       symmetry in Hs7.
       apply fst_same_iff in Hs7.
       destruct s7 as [di7| ].
        simpl in Hs7.
        destruct Hs7 as (Hs7n, Hs7).
bbb.
*)

Theorem neq_xorb : ∀ b b', b ≠ b' → b ⊕ b' = true.
Proof.
intros b b' H.
apply not_false_iff_true.
intros H1; apply H.
apply xorb_eq; assumption.
Qed.

Close Scope nat_scope.
