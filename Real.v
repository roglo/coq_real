Require Import Utf8 QArith NPeano.

Set Implicit Arguments.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

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

Definition carry_i a b i :=
  match fst_same a b (S i) with
  | Some dj => a.[S i + dj]
  | None => true
  end.

Definition rm_add_i a b i := a.[i] ⊕ b.[i] ⊕ carry_i a b i.
Definition rm_add a b := {| rm := rm_add_i a b |}.
Definition rm_eq a b := ∀ i,
  rm (rm_add a rm_zero) i = rm (rm_add b rm_zero) i.

Delimit Scope rm_scope with rm.
Notation "a + b" := (rm_add a b) (at level 50, left associativity) : rm_scope.
Notation "a = b" := (rm_eq a b) : rm_scope.
Notation "a ≠ b" := (¬ rm_eq a b) : rm_scope.
Notation "0" := rm_zero : rm_scope.

Arguments rm r%rm i%nat.
Arguments carry_i a%rm b%rm i%nat.
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

Theorem negb_xorb_diag : ∀ a, negb a ⊕ a = true.
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

Theorem carry_comm : ∀ a b i, carry_i a b i = carry_i b a i.
Proof.
intros a b i.
unfold carry_i; simpl.
rewrite fst_same_comm.
remember (fst_same b a (S i)) as s eqn:Hs .
destruct s as [di| ]; [ idtac | reflexivity ].
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct Hs; symmetry; assumption.
Qed.

Theorem rm_add_i_comm : ∀ a b i, rm_add_i a b i = rm_add_i b a i.
Proof.
intros a b i.
unfold rm_add_i, carry_i.
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
unfold rm_add_i, carry_i; simpl.
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
 unfold rm_add_i, carry_i in H; simpl in H.
 rewrite xorb_false_r in H.
 remember (fst_same a 0 (S i)) as s₂ eqn:Hs₂ .
 symmetry in Hs₂.
 apply fst_same_iff in Hs₂; simpl in Hs₂.
 destruct s₂ as [di₂| ].
  destruct Hs₂ as (Hn₂, Hs₂).
  rewrite Hs₂, xorb_false_r in H.
  assumption.

  rewrite xorb_true_r in H.
  apply negb_true_iff in H.
  pose proof (Hs 1) as H₁; simpl in H₁.
  unfold rm_add_i, carry_i in H₁; simpl in H₁.
  rewrite xorb_false_r in H₁.
  remember (fst_same a 0 (S (i + 1))) as s₃ eqn:Hs₃ .
  symmetry in Hs₃.
  apply fst_same_iff in Hs₃; simpl in Hs₃.
  destruct s₃ as [di₃| ].
   destruct Hs₃ as (Hn₃, Hs₃).
   rewrite Hs₃ in H₁.
   rewrite xorb_false_r in H₁.
   pose proof (Hs₂ (S di₃)) as H₂.
   rewrite <- Nat.add_assoc in Hs₃.
   simpl in Hs₃.
   rewrite Hs₃ in H₂; discriminate H₂.

   rewrite xorb_true_r in H₁.
   apply negb_true_iff in H₁.
   pose proof (Hs₂ 0) as H₂.
   rewrite Nat.add_0_r in H₂.
   rewrite Nat.add_1_r in H₁.
   rewrite H₁ in H₂; discriminate H₂.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 apply IHdk; intros dj.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hs.
Qed.

Theorem not_rm_add_0_inf_1 : ∀ a i, ¬ (∀ dj, rm_add_i a 0 (i + dj) = true).
Proof.
intros a i Hs.
rename Hs into Hs₁.
remember Hs₁ as H; clear HeqH.
apply rm_add_0_inf_1 in H; unfold id in H.
rename H into Hk.
pose proof (Hs₁ 0) as H; simpl in H.
rewrite Nat.add_0_r in H.
unfold rm_add_i, carry_i in H.
remember (S i) as si.
simpl in H.
rewrite xorb_false_r in H.
remember (fst_same a 0 si) as s₂ eqn:Hs₂ .
symmetry in Hs₂.
apply fst_same_iff in Hs₂; simpl in Hs₂.
destruct s₂ as [di₂| ].
 destruct Hs₂ as (Hn₂, Hs₂).
 subst si.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hs₂.
 rewrite Hk in Hs₂; discriminate Hs₂.

 rewrite xorb_true_r in H.
 apply negb_true_iff in H.
 rename H into H₁.
 pose proof (Hk 0) as H; simpl in H.
 rewrite Nat.add_0_r in H.
 rewrite H₁ in H; discriminate H.
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
unfold rm_add_i, carry_i at 1.
remember (S i) as si; simpl.
rewrite xorb_false_r.
remember (fst_same (a + 0%rm) 0 si) as s₁ eqn:Hs₁ .
symmetry in Hs₁.
apply fst_same_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁).
 rewrite Hs₁, xorb_false_r; reflexivity.

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
  → carry_i b c j = carry_i a c j.
Proof.
intros a b c j Hab.
unfold carry_i; intros.
remember (fst_same b c (S j)) as s₁ eqn:Hs₁ .
remember (fst_same a c (S j)) as s₂ eqn:Hs₂ .
symmetry in Hs₁, Hs₂.
apply fst_same_iff in Hs₁.
apply fst_same_iff in Hs₂.
simpl in Hs₁, Hs₂; simpl.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁).
 rewrite Hs₁.
 destruct s₂ as [di₂| ].
  destruct Hs₂ as (Hn₂, Hs₂).
  rewrite Hs₂.
  destruct (lt_dec di₁ di₂) as [H₁| H₁].
   remember H₁ as H; clear HeqH.
   apply Hn₂ in H.
   rewrite Hab, Hs₁ in H.
   destruct c .[ S (j + di₁)]; discriminate H.

   apply Nat.nlt_ge in H₁.
   destruct (lt_dec di₂ di₁) as [H₂| H₂].
    remember H₂ as H; clear HeqH.
    apply Hn₁ in H.
    rewrite <- Hab, Hs₂ in H.
    destruct c .[ S (j + di₂)]; discriminate H.

    apply Nat.nlt_ge in H₂.
    apply Nat.le_antisymm in H₁; auto.

  rewrite <- Hab, Hs₂ in Hs₁.
  destruct c .[ S (j + di₁)]; discriminate Hs₁.

 destruct s₂ as [di₂| ]; auto.
 destruct Hs₂ as (Hn₂, Hs₂).
 rewrite Hab, Hs₁ in Hs₂.
 destruct c .[ S (j + di₂)]; discriminate Hs₂.
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
unfold rm_add_i, carry_i in Hi.
remember (S i) as si; simpl in Hi.
do 2 rewrite xorb_false_r in Hi.
remember (fst_same a 0 si) as s₁ eqn:Hs₁ .
remember (fst_same b 0 si) as s₂ eqn:Hs₂ .
symmetry in Hs₁, Hs₂.
apply fst_same_iff in Hs₁.
apply fst_same_iff in Hs₂.
simpl in Hs₁, Hs₂.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁).
 rewrite Hs₁, xorb_false_r in Hi.
 destruct s₂ as [di₂| ].
  destruct Hs₂ as (Hn₂, Hs₂).
  rewrite Hs₂, xorb_false_r in Hi; assumption.

  exfalso; revert Hs₂; rewrite Hb; apply not_rm_add_0_inf_1.

 exfalso; revert Hs₁; rewrite Ha; apply not_rm_add_0_inf_1.
Qed.

Theorem carry_norm_eq_compat_r : ∀ a₀ b₀ a b c n,
  a = (a₀ + 0)%rm
  → b = (b₀ + 0)%rm
  → (a = b)%rm
  → carry_i (a + c) 0 n = carry_i (b + c) 0 n.
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
  destruct (eq_nat_dec k i) as [H₁| H₁].
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
  destruct (eq_nat_dec k i) as [H₁| H₁].
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
  destruct (eq_nat_dec i j) as [H₁| H₁].
   subst j; rewrite Haj in Hai; discriminate Hai.

   apply Nat.succ_le_mono in Hji.
   apply Nat.nle_gt; intros H.
   apply Nat.le_antisymm in H; auto.

  apply Nat.succ_le_mono in Hji.
  destruct (le_dec i j) as [H₁| H₁].
   apply Nat.le_antisymm in H₁; auto.

   apply Nat.nle_gt in H₁.
   apply Hjk in H₁; [ idtac | apply Nat.lt_succ_r; auto ].
   rewrite Hai in H₁.
   discriminate H₁.
Qed.

Theorem no_room_for_infinite_carry : ∀ a b i di₁ di₂ di₃,
  (∀ dj : nat, dj < di₂ → rm_add_i a 0 (S i + dj) = negb b .[ S i + dj])
  → (∀ dj : nat, a .[ S (S i) + di₂ + dj] = true)
  → (∀ dj : nat, dj < di₃ → a .[ S i + dj] = negb b .[ S i + dj])
  → a .[ S i + di₂] = true
  → a .[ S i + di₁] = false
  → di₁ < di₂
  → di₂ < di₃
  → False.
Proof.
intros a b i di₁ di₂ di₃ Hn₁ Hs₄ Hn₂ Hs₁ Hs₃ H₄ H₃.
remember (S i) as si.
remember (S si) as ssi.
remember (first_false_before a (si + di₂)) as j eqn:Hj .
symmetry in Hj.
destruct j as [j| ].
 apply first_false_before_some_iff in Hj.
 destruct Hj as (Hji, (Hjf, Hk)).
 assert (i < j) as Hij.
  apply Nat.nle_gt; intros H.
  rewrite Hk in Hs₃; [ discriminate Hs₃ | idtac | idtac ].
   eapply Nat.le_lt_trans; eauto .
   rewrite Heqsi, Nat.add_succ_l, <- Nat.add_succ_r.
   apply Nat.lt_sub_lt_add_l.
   rewrite Nat.sub_diag.
   apply Nat.lt_0_succ.

   apply Nat.add_lt_mono_l; assumption.

  assert (j - si < di₂) as H.
   apply Nat.add_lt_mono_r with (p := si).
   unfold lt in Hij; rewrite <- Heqsi in Hij.
   rewrite <- Nat.add_sub_swap; auto.
   rewrite Nat.add_sub, Nat.add_comm; assumption.

   apply Hn₁ in H.
   unfold lt in Hij; rewrite <- Heqsi in Hij.
   rewrite Nat.add_sub_assoc in H; auto.
   rewrite Nat.add_comm, Nat.add_sub in H.
   unfold rm_add_i, carry_i in H.
   remember (S j) as sj; simpl in H.
   rewrite Hjf, xorb_false_r, xorb_false_l in H.
   remember (fst_same a 0 sj) as s₇ eqn:Hs₇ .
   symmetry in Hs₇.
   apply fst_same_iff in Hs₇; simpl in Hs₇.
   destruct s₇ as [di₇| ].
    destruct Hs₇ as (Hn₇, Hs₇).
    rewrite Hs₇ in H.
    symmetry in H.
    apply negb_false_iff in H.
    rewrite Hk in Hs₇; [ discriminate Hs₇ | idtac | idtac ].
     rewrite Heqsj, Nat.add_succ_l, <- Nat.add_succ_r.
     apply Nat.lt_sub_lt_add_l.
     rewrite Nat.sub_diag.
     apply Nat.lt_0_succ.

     apply Nat.nle_gt; intros Hcont.
     rename H into Hbt.
     destruct (lt_dec (si + di₂) (sj + di₇)) as [H₅| H₅].
      pose proof (Hs₄ (sj + di₇ - (ssi + di₂))) as H.
      unfold lt in H₅; rewrite <- Nat.add_succ_l, <- Heqssi in H₅.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Nat.add_comm, Nat.add_sub in H.
      rewrite Hs₇ in H; discriminate H.

      apply Nat.nlt_ge in H₅.
      apply Nat.le_antisymm in H₅; auto.
      rewrite <- H₅, Hs₁ in Hs₇; discriminate Hs₇.

    symmetry in H.
    apply negb_true_iff in H.
    rename H into Hbt.
    assert (j - si < di₃) as H.
     apply Nat.add_lt_mono_r with (p := si).
     rewrite <- Nat.add_sub_swap; auto.
     rewrite Nat.add_sub.
     rewrite Nat.add_comm.
     eapply Nat.lt_trans; [ eauto  | idtac ].
     apply Nat.add_lt_mono_l; assumption.

     apply Hn₂ in H.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_comm, Nat.add_sub in H.
     rewrite Hjf, Hbt in H; discriminate H.

 rewrite first_false_before_none_iff in Hj.
 rewrite Hj in Hs₃; [ discriminate Hs₃ | idtac ].
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
 unfold rm_add_i, carry_i in H.
 rewrite Nat.add_0_r in H.
 remember (S i) as si.
 remember (fst_same a b si) as s₁ eqn:Hs₁ .
 apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
 destruct s₁ as [di₁| ].
  destruct Hs₁ as (Hn₁, Hs₁).
  rewrite Hab in H.
  rewrite xorb_nilpotent, xorb_false_l in H.
  rewrite H in Hs₁; symmetry in Hs₁.
  rename H into Ha₁.
  rename Hs₁ into Hb₁.
  destruct di₁.
   rewrite Nat.add_0_r in Ha₁, Hb₁.
   split; assumption.

   rewrite Nat.add_succ_r, <- Nat.add_succ_l in Ha₁.
   rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hb₁.
   pose proof (Hdi 1) as H.
   rewrite Nat.add_1_r, <- Heqsi in H.
   unfold rm_add_i, carry_i in H.
   pose proof (Hn₁ 0 (Nat.lt_0_succ di₁)) as H₁.
   rewrite Nat.add_0_r in H₁.
   rewrite H₁, negb_xorb_diag, xorb_true_l in H.
   apply negb_true_iff in H.
   remember (S si) as ssi.
   remember (fst_same a b ssi) as s₂ eqn:Hs₂ .
   apply fst_same_sym_iff in Hs₂.
   destruct s₂ as [di₂| ]; [ idtac | discriminate H ].
   destruct Hs₂ as (Hn₂, Hb₂).
   rewrite H in Hb₂.
   rename H into Ha₂; symmetry in Hb₂.
   destruct (lt_dec di₁ di₂) as [H₂| H₂].
    apply Hn₂ in H₂.
    rewrite Ha₁, Hb₁ in H₂; discriminate H₂.

    apply Nat.nlt_ge in H₂.
    destruct (lt_dec di₂ di₁) as [H₃| H₃].
     apply Nat.succ_lt_mono in H₃.
     apply Hn₁ in H₃.
     rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H₃.
     rewrite Ha₂, Hb₂ in H₃; discriminate H₃.

     apply Nat.nlt_ge in H₃.
     apply Nat.le_antisymm in H₂; auto.
     subst di₂; clear H₃.
     rewrite Ha₁ in Ha₂; discriminate Ha₂.

  clear H.
  pose proof (Hdi 1) as H.
  rewrite Nat.add_1_r, <- Heqsi in H.
  unfold rm_add_i, carry_i in H.
  pose proof (Hs₁ 0) as H₁.
  rewrite Nat.add_0_r in H₁.
  rewrite H₁, negb_xorb_diag, xorb_true_l in H.
  apply negb_true_iff in H.
  remember (S si) as ssi.
  remember (fst_same a b ssi) as s₂ eqn:Hs₂ .
  apply fst_same_sym_iff in Hs₂.
  destruct s₂ as [di₂| ]; [ idtac | discriminate H ].
  destruct Hs₂ as (Hn₂, Hb₂).
  rewrite H in Hb₂.
  rename H into Ha₂; symmetry in Hb₂.
  pose proof (Hs₁ (S di₂)) as H.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H.
  rewrite Ha₂, Hb₂ in H; discriminate H.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l in IHdi.
 do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 remember (S i) as si.
 remember (S si) as ssi.
 pose proof (Hdi (S di)) as H.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqsi in H.
 unfold rm_add_i, carry_i in H.
 destruct IHdi as (Ha, Hb).
 rewrite Ha, Hb in H.
 rewrite xorb_true_l, xorb_false_l in H.
 rewrite <- Nat.add_succ_l, <- Heqssi in H.
 remember (fst_same a b (ssi + di)) as s₁ eqn:Hs₁ .
 apply fst_same_sym_iff in Hs₁.
 destruct s₁ as [di₁| ].
  destruct Hs₁ as (Hn₁, Hb₁).
  rewrite H in Hb₁.
  rename H into Ha₁; symmetry in Hb₁.
  destruct di₁.
   rewrite Nat.add_0_r in Ha₁, Hb₁.
   split; assumption.

   rewrite Nat.add_succ_r, <- Nat.add_succ_l in Ha₁.
   rewrite <- Nat.add_succ_l in Ha₁.
   rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hb₁.
   rewrite <- Nat.add_succ_l in Hb₁.
   pose proof (Hdi (S (S di))) as H.
   do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
   rewrite <- Heqsi, <- Heqssi in H.
   unfold rm_add_i, carry_i in H.
   pose proof (Hn₁ 0 (Nat.lt_0_succ di₁)) as H₁.
   rewrite Nat.add_0_r in H₁.
   rewrite H₁, negb_xorb_diag, xorb_true_l in H.
   apply negb_true_iff in H.
   rewrite <- Nat.add_succ_l in H.
   remember (S ssi) as sssi.
   remember (fst_same a b (sssi + di)) as s₂ eqn:Hs₂ .
   apply fst_same_sym_iff in Hs₂.
   destruct s₂ as [di₂| ]; [ idtac | discriminate H ].
   destruct Hs₂ as (Hn₂, Hb₂).
   rewrite H in Hb₂.
   rename H into Ha₂; symmetry in Hb₂.
   destruct (lt_dec di₁ di₂) as [H₂| H₂].
    apply Hn₂ in H₂.
    rewrite Ha₁, Hb₁ in H₂; discriminate H₂.

    apply Nat.nlt_ge in H₂.
    destruct (lt_dec di₂ di₁) as [H₃| H₃].
     apply Nat.succ_lt_mono in H₃.
     apply Hn₁ in H₃.
     rewrite Nat.add_succ_r, <- Nat.add_succ_l in H₃.
     rewrite <- Nat.add_succ_l, <- Heqsssi in H₃.
     rewrite Ha₂, Hb₂ in H₃; discriminate H₃.

     apply Nat.nlt_ge in H₃.
     apply Nat.le_antisymm in H₂; auto.
     subst di₂; clear H₃.
     rewrite Ha₁ in Ha₂; discriminate Ha₂.

  clear H.
  pose proof (Hdi (S (S di))) as H.
  do 2 rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
  rewrite <- Heqsi, <- Heqssi in H.
  unfold rm_add_i, carry_i in H.
  pose proof (Hs₁ 0) as H₁.
  rewrite Nat.add_0_r in H₁.
  rewrite H₁, negb_xorb_diag, xorb_true_l in H.
  apply negb_true_iff in H.
  rewrite <- Nat.add_succ_l in H.
  remember (S ssi) as sssi.
  remember (fst_same a b (sssi + di)) as s₂ eqn:Hs₂ .
  apply fst_same_sym_iff in Hs₂.
  destruct s₂ as [di₂| ]; [ idtac | discriminate H ].
  destruct Hs₂ as (Hn₂, Hb₂).
  rewrite Heqsssi, Nat.add_succ_l in Hb₂.
  rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hb₂.
  rewrite Hs₁ in Hb₂.
  destruct b .[ ssi + di + S di₂]; discriminate Hb₂.
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
unfold rm_add_i, carry_i in H.
remember (S i) as si.
remember (fst_same a b si) as s₁ eqn:Hs₁ .
symmetry in Hs₁.
apply fst_same_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁).
 rewrite Hab in H.
 exists (si + di₁).
 split.
  rewrite Heqsi; apply Nat.le_sub_le_add_l.
  rewrite Nat.sub_diag; apply Nat.le_0_l.

  rewrite negb_xorb_diag, xorb_true_l in H.
  apply negb_true_iff in H.
  rewrite H in Hs₁; symmetry in Hs₁.
  split.
   intros di Hidi.
   rewrite Heqsi in Hidi; simpl in Hidi.
   rewrite <- Nat.add_succ_r in Hidi.
   apply Nat.add_lt_mono_l in Hidi.
   destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
   apply Nat.succ_lt_mono in Hidi.
   rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqsi.
   apply Hn₁; assumption.

   split; auto.
   split; auto.
   apply forall_and_distr; intros di.
   rename H into Ha.
   pose proof (Hdi (S di₁)) as H.
   unfold rm_add_i, carry_i in H.
   rewrite Nat.add_succ_r in H.
   rewrite <- Nat.add_succ_l, <- Heqsi in H.
   rewrite <- Nat.add_succ_l in H; remember (S si) as ssi.
   rewrite Hs₁, Ha, xorb_false_r, xorb_false_l in H.
   remember (fst_same a b (ssi + di₁)) as s₂ eqn:Hs₂ .
   symmetry in Hs₂.
   apply fst_same_iff in Hs₂; simpl in Hs₂.
   destruct s₂ as [di₂| ].
    destruct Hs₂ as (Hn₂, Hs₂).
    destruct di₂.
     rewrite Nat.add_0_r in Hs₂, H.
     induction di.
      rewrite Nat.add_1_r, <- Nat.add_succ_l.
      rewrite <- Heqssi, <- Hs₂.
      split; assumption.

      rename H into Hat.
      pose proof (Hdi (S (S (di₁ + di)))) as H.
      do 2 rewrite Nat.add_succ_r in H.
      rewrite <- Nat.add_succ_l, <- Heqsi in H.
      rewrite <- Nat.add_succ_l, <- Heqssi in H.
      rewrite Nat.add_assoc in H.
      unfold rm_add_i, carry_i in H.
      do 2 rewrite <- Nat.add_succ_l in H; remember (S ssi) as sssi.
      rewrite Nat.add_succ_r in IHdi.
      do 2 rewrite <- Nat.add_succ_l in IHdi.
      rewrite <- Heqssi in IHdi.
      destruct IHdi as (H₁, H₂).
      rewrite H₁, H₂, xorb_true_r, xorb_false_l in H.
      remember (fst_same a b (sssi + di₁ + di)) as s₃ eqn:Hs₃ .
      symmetry in Hs₃.
      apply fst_same_iff in Hs₃; simpl in Hs₃.
      destruct s₃ as [di₃| ].
       do 2 rewrite Nat.add_succ_r.
       do 4 rewrite <- Nat.add_succ_l.
       rewrite <- Heqssi, <- Heqsssi.
       destruct Hs₃ as (Hn₃, Hs₃).
       rewrite H in Hs₃; symmetry in Hs₃.
       destruct di₃.
        rewrite Nat.add_0_r in Hs₃, H.
        split; assumption.

        rename H into Ha₃.
        pose proof (Hn₃ di₃ (Nat.lt_succ_diag_r di₃)) as H.
        rename H into Hab₃.
        pose proof (Hdi (S (S (S (di₁ + di + di₃))))) as H.
        do 3 rewrite Nat.add_succ_r in H.
        do 3 rewrite <- Nat.add_succ_l in H.
        rewrite <- Heqsi, <- Heqssi, <- Heqsssi in H.
        do 2 rewrite Nat.add_assoc in H.
        unfold rm_add_i, carry_i in H.
        rewrite Hab₃, negb_xorb_diag, xorb_true_l in H.
        do 3 rewrite <- Nat.add_succ_l in H.
        remember (S sssi) as ssssi.
        remember (fst_same a b (ssssi + di₁ + di + di₃)) as s₄ eqn:Hs₄ .
        symmetry in Hs₄.
        apply fst_same_iff in Hs₄; simpl in Hs₄.
        destruct s₄ as [di₄| ]; [ idtac | discriminate H ].
        destruct Hs₄ as (Hn₄, Hs₄).
        destruct di₄.
         rewrite Nat.add_0_r in H.
         apply negb_true_iff in H.
         rewrite Nat.add_succ_r in Ha₃.
         do 3 rewrite <- Nat.add_succ_l in Ha₃.
         rewrite <- Heqssssi, H in Ha₃.
         discriminate Ha₃.

         rename H into Ha₄.
         pose proof (Hn₄ 0 (Nat.lt_0_succ di₄)) as H.
         rewrite Nat.add_0_r in H.
         rewrite Nat.add_succ_r in Hs₃, Ha₃.
         do 3 rewrite <- Nat.add_succ_l in Hs₃, Ha₃.
         rewrite <- Heqssssi in Hs₃, Ha₃.
         rewrite Hs₃, Ha₃ in H.
         discriminate H.

       clear H.
       pose proof (Hdi (S (S (S (di₁ + di))))) as H.
       do 3 rewrite Nat.add_succ_r in H.
       do 3 rewrite <- Nat.add_succ_l in H.
       rewrite <- Heqsi, <- Heqssi, <- Heqsssi in H.
       rewrite Nat.add_assoc in H.
       do 2 rewrite Nat.add_succ_r.
       do 4 rewrite <- Nat.add_succ_l.
       rewrite <- Heqssi, <- Heqsssi.
       unfold rm_add_i, carry_i in H.
       do 2 rewrite <- Nat.add_succ_l in H.
       remember (S sssi) as ssssi.
       remember (fst_same a b (ssssi + di₁ + di)) as s₄ eqn:Hs₄ .
       symmetry in Hs₄.
       apply fst_same_iff in Hs₄; simpl in Hs₄.
       destruct s₄ as [di₄| ].
        destruct Hs₄ as (Hn₄, Hs₄).
        clear H.
        pose proof (Hs₃ (S di₄)) as H.
        rewrite Nat.add_succ_r in H.
        do 3 rewrite <- Nat.add_succ_l in H.
        rewrite <- Heqssssi in H.
        rewrite Hs₄ in H.
        destruct b .[ ssssi + di₁ + di + di₄]; discriminate H.

        rewrite xorb_true_r in H.
        apply negb_true_iff in H.
        apply xorb_eq in H.
        rename H into Hab₁.
        pose proof (Hs₃ 0) as H.
        rewrite Nat.add_0_r in H.
        rewrite Hab₁ in H.
        destruct b .[ sssi + di₁ + di]; discriminate H.

     rename H into Ha₂.
     rewrite Ha₂ in Hs₂; symmetry in Hs₂.
     pose proof (Hn₂ 0 (Nat.lt_0_succ di₂)) as H.
     rewrite Nat.add_0_r in H.
     rename H into Hab₁.
     pose proof (Hdi (S (S di₁))) as H.
     do 2 rewrite Nat.add_succ_r in H.
     do 2 rewrite <- Nat.add_succ_l in H.
     rewrite <- Heqsi, <- Heqssi in H.
     unfold rm_add_i, carry_i in H.
     rewrite Hab₁, negb_xorb_diag, xorb_true_l in H.
     apply negb_true_iff in H.
     rewrite <- Nat.add_succ_l in H; remember (S ssi) as sssi.
     remember (fst_same a b (sssi + di₁)) as s₃ eqn:Hs₃ .
     symmetry in Hs₃.
     apply fst_same_iff in Hs₃; simpl in Hs₃.
     destruct s₃ as [di₃| ]; [ idtac | discriminate H ].
     destruct Hs₃ as (Hn₃, Hb₃).
     rename H into Ha₃.
     rewrite Ha₃ in Hb₃; symmetry in Hb₃.
     rewrite Nat.add_succ_r in Hs₂, Ha₂.
     do 2 rewrite <- Nat.add_succ_l in Hs₂, Ha₂.
     rewrite <- Heqsssi in Hs₂, Ha₂.
     destruct (lt_dec di₂ di₃) as [H₁| H₁].
      apply Hn₃ in H₁.
      rewrite Hs₂, Ha₂ in H₁; discriminate H₁.

      apply Nat.nlt_ge in H₁.
      destruct (lt_dec di₃ di₂) as [H₂| H₂].
       apply Nat.succ_lt_mono in H₂.
       apply Hn₂ in H₂.
       rewrite Nat.add_succ_r in H₂.
       do 2 rewrite <- Nat.add_succ_l in H₂.
       rewrite <- Heqsssi in H₂.
       rewrite Ha₃, Hb₃ in H₂; discriminate H₂.

       apply Nat.nlt_ge in H₂.
       apply Nat.le_antisymm in H₁; auto.
       subst di₃; clear H₂.
       rewrite Ha₂ in Ha₃; discriminate Ha₃.

    clear H.
    pose proof (Hs₂ 0) as H.
    rewrite Nat.add_0_r in H.
    rename H into Ha₁.
    pose proof (Hdi (S (S di₁))) as H.
    do 2 rewrite Nat.add_succ_r in H.
    rewrite <- Nat.add_succ_l, <- Heqsi in H.
    rewrite <- Nat.add_succ_l, <- Heqssi in H.
    unfold rm_add_i, carry_i in H.
    rewrite Ha₁, negb_xorb_diag, xorb_true_l in H.
    apply negb_true_iff in H.
    rewrite <- Nat.add_succ_l in H.
    remember (S ssi) as sssi.
    remember (fst_same a b (sssi + di₁)) as s₃ eqn:Hs₃ .
    symmetry in Hs₃.
    apply fst_same_iff in Hs₃; simpl in Hs₃.
    destruct s₃ as [di₃| ]; [ idtac | discriminate H ].
    destruct Hs₃ as (Hn₃, Hs₃).
    rename H into Ha₃; rename Hs₃ into Hb₃.
    rewrite Ha₃ in Hb₃; symmetry in Hb₃.
    pose proof (Hs₂ (S di₃)) as H.
    rewrite Nat.add_succ_r in H.
    do 2 rewrite <- Nat.add_succ_l in H.
    rewrite <- Heqsssi in H.
    rewrite Ha₃, Hb₃ in H; discriminate H.

 rewrite Hab, negb_xorb_diag in H; discriminate H.
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
destruct (bool_dec a .[ i] b .[ i]) as [H₁| H₁].
 remember Hdi as H; clear HeqH.
 apply rm_add_inf_true_eq_if in H; auto.
 destruct H as (Ha, Hb).
 remember a .[ i] as x eqn:H₂ .
 symmetry in H₁, H₂.
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
    split; [ idtac | rewrite H₁, H₂; reflexivity ].
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
  split; [ idtac | rewrite H₁, H₂; reflexivity ].
  intros dj H; exfalso; revert H; apply Nat.nlt_0_r.

 apply neq_negb in H₁.
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

Theorem rm_add_add_0_l_when_lhs_has_relay : ∀ a b i di₁,
  fst_same (a + 0%rm) b (S i) = Some di₁
  → rm_add_i (a + 0%rm) b i = rm_add_i a b i.
Proof.
intros a b i di₁ Hs₁.
unfold rm_add_i, carry_i at 1; remember (S i) as si; simpl.
rewrite Hs₁.
apply fst_same_iff in Hs₁; simpl in Hs₁.
destruct Hs₁ as (Hn₁, Hs₁).
rewrite Hs₁.
unfold rm_add_i, carry_i; rewrite <- Heqsi; simpl.
rewrite xorb_false_r.
remember (fst_same a b si) as s₂ eqn:Hs₂ .
symmetry in Hs₂.
apply fst_same_iff in Hs₂; simpl in Hs₂.
remember (fst_same a 0 si) as s₃ eqn:Hs₃ .
symmetry in Hs₃.
apply fst_same_iff in Hs₃; simpl in Hs₃.
destruct s₂ as [di₂| ].
 destruct Hs₂ as (Hn₂, Hs₂).
 rewrite Hs₂.
 destruct s₃ as [di₃| ].
  destruct Hs₃ as (Hn₃, Hs₃).
  rewrite Hs₃, xorb_false_r; f_equal.
  unfold rm_add_i, carry_i in Hs₁.
  rewrite <- Nat.add_succ_l in Hs₁.
  remember (S si) as ssi.
  move Heqssi before Heqsi.
  simpl in Hs₁; rewrite xorb_false_r in Hs₁.
  remember (fst_same a 0 (ssi + di₁)) as s₄ eqn:Hs₄ .
  symmetry in Hs₄.
  apply fst_same_iff in Hs₄; simpl in Hs₄.
  destruct s₄ as [di₄| ].
   destruct Hs₄ as (Hn₄, Hs₄).
   rewrite Hs₄, xorb_false_r in Hs₁.
   destruct (lt_dec di₁ di₂) as [H₁| H₁].
    remember H₁ as H; clear HeqH.
    apply Hn₂ in H.
    rewrite Hs₁ in H.
    destruct b .[ si + di₁]; discriminate H.

    apply Nat.nlt_ge in H₁.
    destruct (lt_dec di₂ di₁) as [H₂| H₂].
     remember H₂ as H; clear HeqH.
     apply Hn₁ in H.
     unfold rm_add_i, carry_i in H.
     rewrite <- Nat.add_succ_l, <- Heqssi in H.
     simpl in H.
     remember (fst_same a 0 (ssi + di₂)) as s₅ eqn:Hs₅ .
     symmetry in Hs₅.
     apply fst_same_iff in Hs₅; simpl in Hs₅.
     destruct s₅ as [di₅| ].
      destruct Hs₅ as (Hn₅, Hs₅).
      rewrite xorb_false_r, Hs₂, Hs₅, xorb_false_r in H.
      destruct b .[ si + di₂]; discriminate H.

      clear H.
      pose proof (Hs₅ (di₁ - di₂ + di₄)) as H.
      do 2 rewrite Nat.add_comm, Nat.add_assoc in H.
      rewrite Nat.add_assoc in H.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Nat.add_sub_swap in H; auto.
      rewrite Nat.sub_diag, Nat.add_0_l in H.
      rewrite Nat.add_comm, Nat.add_assoc in H.
      rewrite Hs₄ in H; discriminate H.

     apply Nat.nlt_ge in H₂.
     apply Nat.le_antisymm in H₁; auto.

   rewrite xorb_true_r in Hs₁.
   destruct (lt_dec di₂ di₁) as [H₂| H₂].
    remember H₂ as H; clear HeqH.
    apply Hn₁ in H.
    unfold rm_add_i, carry_i in H.
    rewrite <- Nat.add_succ_l, <- Heqssi in H.
    simpl in H.
    remember (fst_same a 0 (ssi + di₂)) as s₅ eqn:Hs₅ .
    symmetry in Hs₅.
    apply fst_same_iff in Hs₅; simpl in Hs₅.
    destruct s₅ as [di₅| ].
     destruct Hs₅ as (Hn₅, Hs₅).
     rewrite xorb_false_r, Hs₂, Hs₅, xorb_false_r in H.
     destruct b .[ si + di₂]; discriminate H.

     clear H.
     rewrite <- Hs₁, <- Hs₂.
     destruct (lt_dec di₂ di₃) as [H₃| H₃].
      pose proof (Hs₅ (di₃ - S di₂)) as H.
      rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in H.
      do 2 rewrite Nat.add_comm, Nat.add_assoc in H.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Nat.add_sub_swap in H; auto.
      rewrite Nat.sub_diag, Nat.add_0_l in H; simpl in H.
      rewrite Nat.add_comm, Hs₃ in H.
      discriminate H.

      apply Nat.nlt_ge in H₃.
      destruct (bool_dec a .[ si + di₂] false) as [H₄| H₄].
       rewrite H₄.
       apply negb_false_iff.
       pose proof (Hs₅ (di₁ - S di₂)) as H.
       rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in H.
       do 2 rewrite Nat.add_comm, Nat.add_assoc in H.
       rewrite Nat.add_sub_assoc in H; auto.
       rewrite Nat.add_sub_swap in H; auto.
       rewrite Nat.sub_diag, Nat.add_0_l in H; simpl in H.
       rewrite Nat.add_comm.
       assumption.

       apply not_false_iff_true in H₄.
       rewrite H₄ in Hs₂.
       symmetry in Hs₂.
       exfalso.
       destruct (lt_dec di₃ di₂) as [H₅| H₅].
        remember H₅ as H; clear HeqH.
        apply Hn₂ in H.
        rewrite Hs₃ in H; symmetry in H.
        apply negb_false_iff in H.
        rename H into Hb.
        remember H₂ as H; clear HeqH.
        eapply Nat.lt_trans in H; [ idtac | eauto  ].
        apply Hn₁ in H.
        rewrite Hb in H; simpl in H.
        unfold rm_add_i, carry_i in H.
        rewrite <- Nat.add_succ_l, <- Heqssi in H.
        simpl in H.
        rewrite Hs₃, xorb_false_r, xorb_false_l in H.
        remember (fst_same a 0 (ssi + di₃)) as s₆ eqn:Hs₆ .
        symmetry in Hs₆.
        apply fst_same_iff in Hs₆; simpl in Hs₆.
        destruct s₆ as [di₆| ]; [ idtac | discriminate H ].
        destruct Hs₆ as (Hn₆, Hs₆).
        clear H.
        remember (first_false_before a (si + di₂)) as j eqn:Hj .
        symmetry in Hj.
        destruct j as [j| ].
         apply first_false_before_some_iff in Hj.
         destruct Hj as (Hji, (Hjf, Hk)).
         assert (j - si < di₁) as H.
          eapply Nat.le_lt_trans; [ idtac | eauto  ].
          rewrite Heqsi in Hji; simpl in Hji.
          apply Nat.succ_le_mono in Hji.
          apply Nat.le_sub_le_add_l.
          rewrite Heqsi.
          apply Nat.le_le_succ_r; assumption.

          apply Hn₁ in H.
          rewrite Nat.add_sub_assoc in H.
           rewrite Nat.add_comm, Nat.add_sub in H.
           unfold rm_add_i, carry_i in H.
           remember (S j) as sj; simpl in H.
           rewrite Hjf, xorb_false_r, xorb_false_l in H.
           remember (fst_same a 0 sj) as s₇ eqn:Hs₇ .
           symmetry in Hs₇.
           apply fst_same_iff in Hs₇; simpl in Hs₇.
           destruct s₇ as [di₇| ].
            destruct Hs₇ as (Hn₇, Hs₇).
            rewrite Hs₇ in H.
            symmetry in H.
            apply negb_false_iff in H.
            destruct (lt_dec (sj + di₇) (si + di₂)) as [H₁| H₁].
             rewrite Hk in Hs₇; auto; [ discriminate Hs₇ | idtac ].
             rewrite Heqsj, Nat.add_succ_l, <- Nat.add_succ_r.
             apply Nat.lt_sub_lt_add_l.
             rewrite Nat.sub_diag.
             apply Nat.lt_0_succ.

             apply Nat.nlt_ge in H₁.
             rename H into Hbt.
             destruct (lt_dec (si + di₂) (sj + di₇)) as [H₆| H₆].
              pose proof (Hs₅ (j + di₇ - (si + di₂))) as H.
              rewrite Heqsj in H₆.
              simpl in H₆.
              apply Nat.succ_le_mono in H₆.
              rewrite Nat.add_sub_assoc in H; auto.
              rewrite Heqssi in H.
              do 2 rewrite Nat.add_succ_l in H.
              rewrite <- Nat.add_succ_r in H.
              rewrite Nat.add_comm, Nat.add_sub in H.
              rewrite <- Nat.add_succ_l, <- Heqsj in H.
              rewrite Hs₇ in H; discriminate H.

              apply Nat.nlt_ge in H₆.
              apply Nat.le_antisymm in H₁; auto.
              rewrite H₁, H₄ in Hs₇; discriminate Hs₇.

            symmetry in H.
            apply negb_true_iff in H.
            rename H into H₆.
            assert (j - si < di₂) as H by (eapply lt_add_sub_lt_r; eauto ).
            apply Hn₂ in H.
            rewrite Nat.add_sub_assoc in H.
             rewrite Nat.add_comm, Nat.add_sub in H.
             rewrite Hjf, H₆ in H; discriminate H.

             clear H.
             apply Nat.nlt_ge; intros Hcont.
             assert (j < si + di₃) as H.
              rewrite Heqsi in Hcont.
              apply Nat.succ_le_mono in Hcont.
              eapply Nat.le_lt_trans; eauto .
              rewrite Heqsi; simpl.
              rewrite <- Nat.add_succ_r.
              apply Nat.lt_sub_lt_add_l.
              rewrite Nat.sub_diag; apply Nat.lt_0_succ.

              apply Hk in H; [ rewrite Hs₃ in H; discriminate H | idtac ].
              apply Nat.add_lt_mono_l; assumption.

           apply Nat.nlt_ge; intros Hcont.
           rewrite Heqsi in Hcont.
           apply Nat.succ_le_mono in Hcont.
           rewrite Hk in Hs₃; [ discriminate Hs₃ | idtac | idtac ].
            rewrite Heqsi.
            eapply Nat.le_lt_trans; [ eauto  | idtac ].
            rewrite Nat.add_succ_l, <- Nat.add_succ_r.
            apply Nat.lt_sub_lt_add_l.
            rewrite Nat.sub_diag.
            apply Nat.lt_0_succ.

            apply Nat.add_lt_mono_l; assumption.

         rewrite first_false_before_none_iff in Hj.
         rewrite Hj in Hs₃; [ discriminate Hs₃ | idtac ].
         apply Nat.add_lt_mono_l; assumption.

        apply Nat.nlt_ge in H₅.
        apply Nat.le_antisymm in H₅; [ subst di₃ | auto ].
        rewrite H₄ in Hs₃; discriminate Hs₃.

    apply Nat.nlt_ge in H₂.
    destruct (lt_dec di₁ di₂) as [H₃| H₃].
     pose proof (Hs₄ (di₂ - S di₁)) as H.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Heqssi in H; simpl in H.
     rewrite Nat.add_shuffle0, Nat.add_sub in H.
     rewrite H in Hs₂; symmetry in Hs₂.
     rename H into Ha; move Ha after Hs₂; rewrite Hs₂.
     symmetry in Hs₁; apply negb_sym in Hs₁.
     remember b .[ si + di₁] as bi eqn:Hbi .
     destruct bi; [ reflexivity | idtac ].
     symmetry in Hbi; simpl in Hs₁.
     exfalso.
     destruct (lt_dec di₁ di₃) as [H₁| H₁].
      pose proof (Hs₄ (di₃ - S di₁)) as H.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Heqssi in H; simpl in H.
      rewrite Nat.add_shuffle0, Nat.add_sub in H.
      rewrite Hs₃ in H; discriminate H.

      apply Nat.nlt_ge in H₁.
      destruct (eq_nat_dec di₁ di₃) as [H₄| H₄].
       subst di₃.
       rewrite Hs₁ in Hs₃; discriminate Hs₃.

       assert (di₃ < di₁) as H.
        apply Nat.nle_gt; intros H.
        apply Nat.le_antisymm in H; auto; contradiction.

        subst si ssi.
        eapply no_room_for_infinite_carry in Hs₃; eauto .

     apply Nat.nlt_ge in H₃.
     apply Nat.le_antisymm in H₃; auto.

  do 3 rewrite xorb_assoc; f_equal.
  rewrite xorb_comm, xorb_assoc; f_equal.
  rewrite xorb_true_r.
  rewrite <- Hs₂, Hs₃, <- Hs₁.
  apply negb_true_iff.
  unfold rm_add_i, carry_i; rewrite <- Nat.add_succ_l.
  remember (S si) as ssi; simpl.
  rewrite Hs₃, xorb_false_r, xorb_true_l.
  apply negb_false_iff.
  remember (fst_same a 0 (ssi + di₁)) as s₄ eqn:Hs₄ .
  symmetry in Hs₄.
  destruct s₄ as [s₄| ]; [ idtac | reflexivity ].
  rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r.
  rewrite <- Nat.add_assoc, Hs₃; reflexivity.

 do 3 rewrite xorb_assoc; f_equal.
 rewrite xorb_comm, xorb_assoc; f_equal.
 destruct s₃ as [di₃| ].
  destruct Hs₃ as (Hn₃, Hs₃).
  rewrite Hs₃, xorb_false_r.
  rewrite <- Hs₁.
  unfold rm_add_i, carry_i.
  rewrite <- Nat.add_succ_l.
  remember (S si) as ssi; simpl.
  rewrite xorb_false_r.
  remember (fst_same a 0 (ssi + di₁)) as s₄ eqn:Hs₄ .
  symmetry in Hs₄.
  apply fst_same_iff in Hs₄; simpl in Hs₄.
  destruct s₄ as [di₄| ].
   destruct Hs₄ as (Hn₄, Hs₄); rewrite Hs₄.
   rewrite xorb_false_r.
   destruct (lt_dec di₁ di₃) as [H₁| H₁].
    remember H₁ as H; clear HeqH.
    apply Hn₃; assumption.

    apply Nat.nlt_ge in H₁.
    destruct (lt_dec di₃ di₁) as [H₂| H₂].
     apply not_false_iff_true.
     intros Ha.
     remember Ha as Hb; clear HeqHb.
     rewrite Hs₂ in Hb.
     apply negb_false_iff in Hb.
     rewrite <- Hs₁ in Hb.
     unfold rm_add_i, carry_i in Hb.
     rewrite <- Nat.add_succ_l in Hb.
     rewrite <- Heqssi in Hb; simpl in Hb.
     rewrite Ha, xorb_false_r, xorb_false_l in Hb.
     remember (fst_same a 0 (ssi + di₁)) as s₅ eqn:Hs₅ .
     symmetry in Hs₅.
     apply fst_same_iff in Hs₅; simpl in Hs₅.
     destruct s₅ as [di₅| ].
      destruct Hs₅ as (Hn₅, Hs₅); rewrite Hs₅ in Hb; discriminate Hb.

      rewrite Hs₅ in Hs₄; discriminate Hs₄.

     apply Nat.nlt_ge, Nat.le_antisymm in H₂; auto.
     subst di₃; clear H₁.
     rewrite Hs₂ in Hs₃.
     apply negb_false_iff in Hs₃.
     rewrite <- Hs₁ in Hs₃.
     unfold rm_add_i, carry_i in Hs₃.
     rewrite <- Nat.add_succ_l in Hs₃.
     rewrite <- Heqssi in Hs₃; simpl in Hs₃.
     rewrite xorb_false_r in Hs₃.
     remember (fst_same a 0 (ssi + di₁)) as s₅ eqn:Hs₅ .
     symmetry in Hs₅.
     apply fst_same_iff in Hs₅; simpl in Hs₅.
     destruct s₅ as [di₅| ].
      destruct Hs₅ as (Hn₅, Hs₅); rewrite Hs₅ in Hs₃.
      rewrite xorb_false_r in Hs₃; assumption.

      rewrite Hs₅ in Hs₄; discriminate Hs₄.

   rewrite xorb_true_r.
   apply negb_true_iff.
   unfold rm_add_i, carry_i in Hs₁.
   rewrite <- Nat.add_succ_l, <- Heqssi in Hs₁.
   simpl in Hs₁.
   rewrite xorb_false_r in Hs₁.
   rewrite Hs₂ in Hs₁.
   remember (fst_same a 0 (ssi + di₁)) as s₅ eqn:Hs₅ .
   symmetry in Hs₅.
   apply fst_same_iff in Hs₅; simpl in Hs₅.
   destruct s₅ as [di₅| ].
    destruct Hs₅ as (Hn₅, Hs₅); rewrite Hs₅ in Hs₁.
    rewrite xorb_false_r in Hs₁.
    destruct b .[ si + di₁]; discriminate Hs₁.

    clear Hs₁ Hs₅.
    destruct (lt_dec di₁ di₃) as [H₁| H₁].
     pose proof (Hs₄ (di₃ - S di₁)) as H.
     rewrite Heqssi in H.
     rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_shuffle0, Nat.add_sub in H.
     rewrite Hs₃ in H; discriminate H.

     apply Nat.nlt_ge in H₁.
     destruct (lt_dec di₃ di₁) as [H₂| H₂].
      remember H₂ as H; clear HeqH.
      apply Hn₁ in H.
      unfold rm_add_i, carry_i in H.
      rewrite <- Nat.add_succ_l, <- Heqssi in H; simpl in H.
      rewrite xorb_false_r in H.
      remember (fst_same a 0 (ssi + di₃)) as s₅ eqn:Hs₅ .
      symmetry in Hs₅.
      apply fst_same_iff in Hs₅; simpl in Hs₅.
      destruct s₅ as [di₅| ].
       destruct Hs₅ as (Hn₅, Hs₅); rewrite Hs₅ in H.
       rewrite xorb_false_r in H.
       apply not_true_iff_false; intros Ha.
       subst si ssi.
       eapply no_room_for_infinite_carry in Hs₃; eauto .

       rewrite xorb_true_r, <- Hs₂ in H.
       destruct a .[ si + di₃]; discriminate H.

      apply Nat.nlt_ge in H₂.
      apply Nat.le_antisymm in H₂; auto.
      subst di₃; assumption.

  rewrite xorb_true_r, <- Hs₂.
  apply Hs₃.
Qed.

Theorem rm_add_add_0_l_when_lhs_has_no_relay : ∀ a b i dj₂ dj₅,
  fst_same ((a + 0)%rm + b) 0 (S i) = Some dj₂
  → fst_same (a + b) 0 (S i) = Some dj₅
  → fst_same (a + 0%rm) b (S i) = None
  → rm_add_i (a + 0%rm) b i = rm_add_i a b i.
Proof.
intros a b i dj₂ dj₅ Ps₂ Ps₅ Hs₁.
remember (S i) as si.
unfold rm_add_i, carry_i.
rewrite <- Heqsi; simpl.
rewrite Hs₁.
unfold rm_add_i, carry_i at 1; rewrite <- Heqsi; simpl.
apply fst_same_iff in Hs₁; simpl in Hs₁.
apply fst_same_iff in Ps₂; simpl in Ps₂.
destruct Ps₂ as (Pn₂, _).
apply fst_same_iff in Ps₅; simpl in Ps₅.
destruct Ps₅ as (Pn₅, Ps₅).
rewrite xorb_false_r.
do 3 rewrite xorb_assoc; f_equal.
rewrite xorb_comm, xorb_assoc; f_equal.
rewrite xorb_true_l.
remember (fst_same a b si) as s₂ eqn:Hs₂ .
symmetry in Hs₂.
apply fst_same_iff in Hs₂; simpl in Hs₂.
remember (fst_same a 0 si) as s₃ eqn:Hs₃ .
symmetry in Hs₃.
apply fst_same_iff in Hs₃; simpl in Hs₃.
destruct s₂ as [di₂| ].
 destruct Hs₂ as (Hn₂, Hs₂).
 destruct s₃ as [di₃| ].
  destruct Hs₃ as (Hn₃, Hs₃).
  rewrite Hs₃; simpl; symmetry.
  destruct (lt_dec di₂ di₃) as [H₁| H₁].
   apply Hn₃; assumption.

   apply Nat.nlt_ge in H₁.
   pose proof (Hs₁ di₂) as H.
   unfold rm_add_i, carry_i in H.
   rewrite <- Nat.add_succ_l in H.
   remember (S si) as ssi; simpl in H.
   rewrite xorb_false_r in H.
   remember (fst_same a 0 (ssi + di₂)) as s₄ eqn:Hs₄ .
   symmetry in Hs₄.
   apply fst_same_iff in Hs₄; simpl in Hs₄.
   destruct s₄ as [di₄| ].
    destruct Hs₄ as (Hn₄, Hs₄); rewrite Hs₄, xorb_false_r in H.
    rewrite Hs₂ in H.
    destruct b .[ si + di₂]; discriminate H.

    clear H.
    apply not_false_iff_true.
    intros Ha.
    destruct dj₅.
     rewrite Nat.add_0_r in Ps₅.
     unfold rm_add_i, carry_i in Ps₅.
     rewrite <- Heqssi in Ps₅.
     remember (fst_same a b ssi) as s₆ eqn:Ps₆ .
     symmetry in Ps₆.
     apply fst_same_iff in Ps₆; simpl in Ps₆.
     destruct s₆ as [dj₆| ].
      destruct Ps₆ as (Pn₆, Ps₆).
      assert (S dj₆ = di₂) as H.
       destruct (lt_dec (S dj₆) di₂) as [H₂| H₂].
        apply Hn₂ in H₂.
        rewrite Nat.add_succ_r, <- Nat.add_succ_l in H₂.
        rewrite <- Heqssi in H₂.
        rewrite Ps₆ in H₂.
        destruct b .[ ssi + dj₆]; discriminate H₂.

        apply Nat.nlt_ge in H₂.
        destruct (lt_dec di₂ (S dj₆)) as [H₃| H₃].
         destruct di₂.
          rewrite Nat.add_0_r in Hs₄.
          rewrite Nat.add_0_r in Hs₂.
          rewrite <- Hs₂, Hs₄ in Ps₅.
          rewrite xorb_true_r in Ps₅.
          apply negb_false_iff in Ps₅.
          destruct a .[ si]; discriminate Ps₅.

          apply Nat.succ_lt_mono in H₃.
          apply Pn₆ in H₃.
          rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs₂.
          rewrite <- Heqssi, H₃ in Hs₂.
          destruct b .[ ssi + di₂]; discriminate Hs₂.

         apply Nat.nlt_ge in H₃.
         apply Nat.le_antisymm; auto.

       rewrite <- H, Nat.add_succ_r, <- Nat.add_succ_l in Ha.
       rewrite <- Heqssi in Ha.
       rewrite Ha, xorb_false_r in Ps₅.
       rewrite <- H in Hn₂; clear H.
       assert (0 < S dj₆) as H by apply Nat.lt_0_succ.
       apply Hn₂ in H.
       rewrite Nat.add_0_r in H.
       rewrite H in Ps₅.
       destruct b .[ si]; discriminate Ps₅.

      destruct di₂.
       rewrite Nat.add_0_r in Hs₂.
       rewrite <- Hs₂ in Ps₅.
       destruct a .[ si]; discriminate Ps₅.

       rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hs₂.
       rewrite <- Heqssi in Hs₂.
       rewrite Ps₆ in Hs₂.
       destruct b .[ ssi + di₂]; discriminate Hs₂.

     assert (S dj₅ = di₂) as H.
      destruct (lt_dec (S dj₅) di₂) as [H₂| H₂].
       unfold rm_add_i, carry_i in Ps₅.
       rewrite <- Nat.add_succ_l, <- Heqssi in Ps₅.
       remember (fst_same a b (ssi + S dj₅)) as s₆ eqn:Ps₆ .
       symmetry in Ps₆.
       apply fst_same_iff in Ps₆; simpl in Ps₆.
       destruct s₆ as [di₆| ].
        destruct Ps₆ as (Pn₆, Ps₆).
        assert (S (S dj₅ + di₆) = di₂) as H.
         destruct (lt_dec (S (S dj₅ + di₆)) di₂) as [H₃| H₃].
          apply Hn₂ in H₃.
          rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H₃.
          rewrite Nat.add_assoc in H₃.
          rewrite Ps₆ in H₃.
          destruct b .[ ssi + S dj₅ + di₆]; discriminate H₃.

          apply Nat.nlt_ge in H₃.
          destruct (lt_dec di₂ (S (S dj₅ + di₆))) as [H₄| H₄].
           remember H₄ as H; clear HeqH.
           rewrite <- Nat.add_succ_l in H.
           apply Nat.succ_lt_mono in H₂.
           apply lt_add_sub_lt_l with (a := di₂) in H; auto.
           apply Nat.succ_lt_mono in H₂.
           apply Pn₆ in H.
           rewrite Heqssi in H.
           rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
           rewrite Nat.add_sub_assoc in H; auto.
           rewrite Nat.add_shuffle0, Nat.add_sub in H.
           rewrite Hs₂ in H.
           destruct b .[ si + di₂]; discriminate H.

           apply Nat.nlt_ge in H₄.
           apply Nat.le_antisymm; auto.

         rewrite <- H in Ha.
         rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in Ha.
         rewrite Nat.add_assoc in Ha.
         rewrite Ha, xorb_false_r in Ps₅.
         apply Hn₂ in H₂.
         rewrite H₂ in Ps₅.
         destruct b .[ si + S dj₅]; discriminate Ps₅.

        pose proof (Ps₆ (di₂ - S (S dj₅))) as H.
        rewrite Nat.add_sub_assoc in H; auto.
        rewrite Heqssi in H.
        rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
        rewrite Nat.add_shuffle0, Nat.add_sub in H.
        rewrite Hs₂ in H.
        destruct b .[ si + di₂]; discriminate H.

       apply Nat.nlt_ge in H₂.
       destruct (lt_dec di₂ (S dj₅)) as [H₃| H₃].
        unfold rm_add_i, carry_i in Ps₅.
        rewrite <- Nat.add_succ_l, <- Heqssi in Ps₅.
        remember (fst_same a b (ssi + S dj₅)) as s₆ eqn:Ps₆ .
        symmetry in Ps₆.
        apply fst_same_iff in Ps₆; simpl in Ps₆.
        destruct s₆ as [dj₆| ].
         destruct Ps₆ as (Pn₆, Ps₆).
         pose proof (Hs₁ (S dj₅ + dj₆)) as H.
         rewrite Nat.add_assoc in H.
         unfold rm_add_i, carry_i in H.
         rewrite <- Nat.add_succ_l in H.
         rewrite <- Nat.add_succ_l in H.
         rewrite <- Heqssi in H; simpl in H.
         rewrite xorb_false_r in H.
         remember (fst_same a 0 (ssi + S dj₅ + dj₆)) as s₇ eqn:Ps₇ .
         symmetry in Ps₇.
         apply fst_same_iff in Ps₇; simpl in Ps₇.
         destruct s₇ as [dj₇| ].
          destruct Ps₇ as (Pn₇, Ps₇); rewrite Ps₇, xorb_false_r in H.
          rename H into Hab.
          pose proof (Hs₁ (S (S dj₅ + dj₆))) as H.
          rewrite Nat.add_succ_r, <- Nat.add_succ_l, <- Heqssi in H.
          rewrite Nat.add_assoc in H.
          unfold rm_add_i, carry_i in H.
          do 2 rewrite <- Nat.add_succ_l in H.
          remember (S ssi) as sssi; simpl in H.
          rewrite xorb_false_r in H.
          remember (fst_same a 0 (sssi + S dj₅ + dj₆)) as s₈ eqn:Ps₈ .
          symmetry in Ps₈.
          apply fst_same_iff in Ps₈; simpl in Ps₈.
          destruct s₈ as [dj₈| ].
           destruct Ps₈ as (Pn₈, Ps₈); rewrite Ps₈, xorb_false_r in H.
           rewrite Ps₆ in H.
           destruct b .[ ssi + S dj₅ + dj₆]; discriminate H.

           clear H.
           pose proof (Hs₄ (S dj₅ + dj₆ + dj₇ - di₂)) as H.
           rewrite Nat.add_sub_assoc in H.
            rewrite Nat.add_shuffle0, Nat.add_sub in H.
            do 2 rewrite Nat.add_assoc in H.
            rewrite Ps₇ in H; discriminate H.

            eapply Nat.le_trans; eauto .
            rewrite <- Nat.add_assoc.
            apply Nat.le_sub_le_add_l.
            rewrite Nat.sub_diag.
            apply Nat.le_0_l.

          rewrite xorb_true_r in H.
          apply negb_sym in H.
          rewrite negb_involutive in H.
          destruct dj₆.
           rewrite Nat.add_0_r in H.
           rewrite H in Ps₅.
           rewrite Nat.add_0_r in Ps₇.
           rewrite Ps₇ in Ps₅.
           rewrite xorb_true_r in Ps₅.
           destruct a .[ si + S dj₅]; discriminate Ps₅.

           rename H into Hba.
           pose proof (Pn₆ dj₆ (Nat.lt_succ_diag_r dj₆)) as H.
           rewrite Nat.add_succ_r, <- Nat.add_succ_l in Hba.
           rewrite <- Nat.add_succ_l in Hba.
           rewrite <- Heqssi in Hba.
           rewrite Hba in H.
           destruct a .[ ssi + S dj₅ + dj₆]; discriminate H.

         pose proof (Hs₁ (S dj₅)) as H.
         unfold rm_add_i, carry_i in H.
         rewrite <- Nat.add_succ_l, <- Heqssi in H; simpl in H.
         rewrite xorb_false_r in H.
         remember (fst_same a 0 (ssi + S dj₅)) as s₇ eqn:Ps₇ .
         symmetry in Ps₇.
         apply fst_same_iff in Ps₇; simpl in Ps₇.
         destruct s₇ as [dj₇| ].
          destruct Ps₇ as (Pn₇, Ps₇); rewrite Ps₇, xorb_false_r in H.
          clear H.
          pose proof (Hs₄ (S dj₅ + dj₇ - di₂)) as H.
          rewrite Nat.add_sub_swap in H; auto.
          rewrite Nat.add_assoc in H.
          rewrite Nat.add_sub_assoc in H; auto.
          rewrite Nat.add_shuffle0, Nat.add_sub in H.
          rewrite Ps₇ in H; discriminate H.

          rewrite xorb_true_r in H.
          apply negb_sym in H.
          rewrite negb_involutive in H.
          rewrite H in Ps₅.
          destruct a .[ si + S dj₅]; discriminate Ps₅.

        apply Nat.nlt_ge in H₃.
        apply Nat.le_antisymm; auto.

      rewrite H in Ps₅.
      unfold rm_add_i, carry_i in Ps₅.
      rewrite <- Nat.add_succ_l, <- Heqssi in Ps₅.
      remember (fst_same a b (ssi + di₂)) as s₆ eqn:Ps₆ .
      symmetry in Ps₆.
      apply fst_same_iff in Ps₆; simpl in Ps₆.
      destruct s₆ as [dj₆| ].
       rewrite Hs₄, Hs₂, xorb_true_r in Ps₅.
       destruct b .[ si + di₂]; discriminate Ps₅.

       rewrite Hs₂, xorb_true_r in Ps₅.
       destruct b .[ si + di₂]; discriminate Ps₅.

  symmetry; simpl.
  assert (∀ dj, b .[ si + dj] = true) as Hb.
   intros dj.
   apply negb_false_iff.
   rewrite <- Hs₁.
   unfold rm_add_i, carry_i.
   rewrite <- Nat.add_succ_l; remember (S si) as ssi; simpl.
   rewrite xorb_false_r.
   remember (fst_same a 0 (ssi + dj)) as s₄ eqn:Hs₄ .
   symmetry in Hs₄.
   apply fst_same_iff in Hs₄; simpl in Hs₄.
   destruct s₄ as [di₄| ]; [ idtac | rewrite Hs₃; reflexivity ].
   destruct Hs₄ as (Hn₄, Hs₄).
   rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Hs₄.
   rewrite <- Nat.add_assoc, Hs₃ in Hs₄; discriminate Hs₄.

   destruct di₂.
    rewrite Nat.add_0_r in Hs₂; rewrite Nat.add_0_r.
    clear Hn₂.
    unfold rm_add_i, carry_i in Ps₅.
    rewrite <- Nat.add_succ_l in Ps₅; remember (S si) as ssi; simpl in Ps₅.
    rewrite Hs₃, Hb, xorb_true_r in Ps₅.
    rewrite xorb_false_l in Ps₅.
    remember (fst_same a b (ssi + dj₅)) as s₆ eqn:Ps₆ .
    symmetry in Ps₆.
    apply fst_same_iff in Ps₆; simpl in Ps₆.
    destruct s₆ as [dj₆| ]; [ idtac | discriminate Ps₅ ].
    rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Ps₅.
    rewrite <- Nat.add_assoc, Hs₃ in Ps₅; discriminate Ps₅.

    pose proof (Hn₂ 0 (Nat.lt_0_succ di₂)) as H.
    rewrite Hs₃, Hb in H; discriminate H.

 destruct s₃ as [di₃| ].
  destruct Hs₃ as (Hn₃, Hs₃); rewrite Hs₃; reflexivity.

  pose proof (Hs₁ 0) as H.
  rewrite Nat.add_0_r in H.
  unfold rm_add_i, carry_i in H.
  remember (S si) as ssi; simpl in H.
  rewrite xorb_false_r in H.
  remember (fst_same a 0 ssi) as s₄ eqn:Hs₄ .
  symmetry in Hs₄.
  apply fst_same_iff in Hs₄; simpl in Hs₄.
  destruct s₄ as [di₄| ].
   destruct Hs₄ as (Hn₄, Hs₄).
   rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Hs₄.
   rewrite Hs₃ in Hs₄; discriminate Hs₄.

   rewrite xorb_true_r in H.
   apply negb_sym in H.
   rewrite negb_involutive in H.
   pose proof (Hs₂ 0) as H₁.
   rewrite Nat.add_0_r, H in H₁.
   destruct a .[ si]; discriminate H₁.
Qed.

Theorem rm_add_add_0_l_when_both_hs_has_relay : ∀ a b i dj₂ dj₅,
  fst_same ((a + 0)%rm + b) 0 (S i) = Some dj₂
  → fst_same (a + b) 0 (S i) = Some dj₅
  → rm_add_i ((a + 0)%rm + b) 0 i = rm_add_i (a + b) 0 i.
Proof.
intros a b i dj₂ dj₅ Ps₂ Ps₅.
unfold rm_add_i, carry_i.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
rewrite Ps₂, Ps₅.
remember Ps₂ as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, H); rewrite H; clear H.
remember Ps₅ as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, H); rewrite H; clear H.
do 2 rewrite xorb_false_r.
remember (fst_same (a + 0%rm) b (S i)) as s₁ eqn:Hs₁ .
symmetry in Hs₁.
subst si.
destruct s₁ as [di₁| ].
 eapply rm_add_add_0_l_when_lhs_has_relay; eauto .

 eapply rm_add_add_0_l_when_lhs_has_no_relay; eauto .
Qed.

Theorem rm_add_add_0_l_when_relay : ∀ a b i di₁,
  fst_same (a + 0%rm) b (S i) = Some di₁
  → fst_same (a + b) 0 (S i) ≠ None.
Proof.
intros a b i di₁ Hs₁ Hs₅.
apply rm_add_add_0_l_when_lhs_has_relay in Hs₁.
remember (S i) as si.
unfold rm_add_i, carry_i in Hs₁.
rewrite <- Heqsi in Hs₁; simpl in Hs₁.
unfold rm_add_i in Hs₁ at 1.
unfold carry_i in Hs₁.
rewrite <- Heqsi in Hs₁; simpl in Hs₁.
rewrite xorb_false_r in Hs₁.
apply fst_same_iff in Hs₅; simpl in Hs₅.
remember (fst_same a b si) as s₈ eqn:Hs₈ .
apply fst_same_sym_iff in Hs₈.
destruct s₈ as [di₈| ].
 destruct Hs₈ as (Hn₈, Hs₈).
 destruct di₈.
  clear Hn₈; rewrite Nat.add_0_r in Hs₈, Hs₁.
  apply rm_add_inf_true_eq_if in Hs₅; auto.
  destruct Hs₅ as (Has, Hbs).
  remember (fst_same a 0 si) as s₃ eqn:Hs₃ .
  apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
  destruct s₃ as [di₃| ].
   destruct Hs₃ as (Hn₃, Hs₃).
   rewrite Hs₃, xorb_false_r in Hs₁.
   remember (fst_same (a + 0%rm) b si) as s₄ eqn:Hs₄ .
   apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
   destruct s₄ as [di₄| ].
    destruct Hs₄ as (Hn₄, Hs₄).
    unfold rm_add_i, carry_i in Hs₁.
    rewrite <- Nat.add_succ_l in Hs₁.
    remember (S si) as ssi; simpl in Hs₁.
    rewrite xorb_false_r in Hs₁.
    remember (fst_same a 0 (ssi + di₄)) as s₅ eqn:Hs₅ .
    apply fst_same_sym_iff in Hs₅; simpl in Hs₅.
    destruct s₅ as [di₅| ].
     destruct Hs₅ as (Hn₅, Hs₅); rewrite Hs₅, xorb_false_r in Hs₁.
     rewrite Heqssi, Nat.add_succ_l in Hs₅.
     rewrite <- Nat.add_succ_r, <- Nat.add_assoc in Hs₅.
     simpl in Hs₅.
     rewrite Has in Hs₅; discriminate Hs₅.

     rewrite xorb_true_r in Hs₁.
     unfold rm_add_i, carry_i in Hs₄.
     rewrite <- Nat.add_succ_l in Hs₄.
     rewrite <- Heqssi in Hs₄; simpl in Hs₄.
     rewrite xorb_false_r in Hs₄.
     remember (fst_same a 0 (ssi + di₄)) as s₆ eqn:Hs₆ .
     destruct s₆ as [di₆| ].
      rewrite Hs₅, xorb_true_r in Hs₄.
      destruct di₄.
       rewrite Nat.add_0_r in Hs₁.
       rewrite <- negb_xorb_r in Hs₁.
       destruct (a .[ i] ⊕ b .[ i] ⊕ a .[ si]); discriminate Hs₁.

       rewrite Has, Hbs in Hs₄; discriminate Hs₄.

      rewrite xorb_true_r in Hs₄.
      destruct di₄.
       rewrite Nat.add_0_r in Hs₁.
       rewrite <- negb_xorb_r in Hs₁.
       destruct (a .[ i] ⊕ b .[ i] ⊕ a .[ si]); discriminate Hs₁.

       rewrite Has, Hbs in Hs₄; discriminate Hs₄.

    destruct di₃.
     rewrite Nat.add_0_r in Hs₃.
     rewrite Hs₃ in Hs₁.
     destruct (a .[ i] ⊕ b .[ i]); discriminate Hs₁.

     rewrite Has in Hs₃; discriminate Hs₃.

   remember (fst_same (a + 0%rm) b si) as s₄ eqn:Hs₄ .
   apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
   destruct s₄ as [di₄| ].
    destruct Hs₄ as (Hn₄, Hs₄); rewrite Hs₄ in Hs₁.
    unfold rm_add_i, carry_i in Hs₄.
    rewrite <- Nat.add_succ_l in Hs₄.
    remember (S si) as ssi; simpl in Hs₄.
    rewrite xorb_false_r in Hs₄.
    remember (fst_same a 0 (ssi + di₄)) as s₅ eqn:Hs₅ .
    apply fst_same_sym_iff in Hs₅; simpl in Hs₅.
    destruct s₅ as [di₅| ].
     destruct Hs₅ as (Hn₅, Hs₅).
     rewrite Heqssi, Nat.add_succ_l in Hs₅.
     rewrite <- Nat.add_succ_r, <- Nat.add_assoc in Hs₅.
     simpl in Hs₅.
     rewrite Has in Hs₅; discriminate Hs₅.

     clear Hs₁.
     rewrite Hs₃, xorb_true_r in Hs₄.
     symmetry in Hs₄; simpl in Hs₄.
     destruct di₄.
      rewrite Nat.add_0_r in Hs₄; clear Hs₅.
      clear Hn₄.
      pose proof (Hs₃ 0) as H; rewrite Nat.add_0_r in H.
      rewrite H, Hs₄ in Hs₈; discriminate Hs₈.

      rewrite Hbs in Hs₄; discriminate Hs₄.

    pose proof (Hs₃ 0) as H; rewrite Nat.add_0_r in H.
    rewrite H in Hs₁.
    destruct a .[ i], b .[ i]; discriminate Hs₁.

  pose proof (Hn₈ 0 (Nat.lt_0_succ di₈)) as H.
  rewrite Nat.add_0_r in H.
  apply rm_add_inf_true_neq_if in Hs₅; auto.
  destruct Hs₅ as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
  rename H into Hab.
  destruct (lt_dec j (si + S di₈)) as [H₁| H₁].
   remember H₁ as H; clear HeqH.
   apply Nat.le_sub_le_add_l in H.
   rewrite Nat.sub_succ_l in H; [ idtac | apply Nat.lt_le_incl; auto ].
   apply Hn₈ in H.
   rewrite Nat.add_sub_assoc in H; [ idtac | apply Nat.lt_le_incl; auto ].
   rewrite Nat.add_comm, Nat.add_sub in H.
   rewrite Ha, Hb in H; discriminate H.

   apply Nat.nlt_ge in H₁.
   destruct (lt_dec (si + S di₈) j) as [H₂| H₂].
    remember H₂ as H; clear HeqH.
    apply Hni in H.
    rewrite Hs₈ in H.
    destruct b .[ si + S di₈]; discriminate H.

    apply Nat.nlt_ge in H₂.
    apply Nat.le_antisymm in H₁; auto; clear H₂.
    rewrite <- H₁, Ha, xorb_false_r in Hs₁.
    remember (fst_same a 0 si) as s₃ eqn:Hs₃ .
    apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
    destruct s₃ as [di₃| ].
     destruct Hs₃ as (Hn₃, Hs₃); rewrite Hs₃, xorb_false_r in Hs₁.
     remember (fst_same (a + 0%rm) b si) as s₄ eqn:Hs₄ .
     apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
     destruct s₄ as [di₄| ].
      destruct Hs₄ as (Hn₄, Hs₄); rewrite Hs₄ in Hs₁.
      unfold rm_add_i, carry_i in Hs₄.
      rewrite <- Nat.add_succ_l in Hs₄.
      remember (S si) as ssi; simpl in Hs₄.
      rewrite xorb_false_r in Hs₄.
      remember (fst_same a 0 (ssi + di₄)) as s₅ eqn:Hs₅ .
      apply fst_same_sym_iff in Hs₅; simpl in Hs₅.
      destruct s₅ as [di₅| ].
       destruct Hs₅ as (Hn₅, Hs₅); rewrite Hs₅, xorb_false_r in Hs₄.
       destruct (lt_dec j (si + di₄)) as [H₂| H₂].
        pose proof (Hat (si + di₄ + di₅ - j)) as H₃.
        rewrite <- Nat.sub_succ_l in H₃.
         rewrite Nat.add_sub_assoc in H₃.
          rewrite Nat.add_comm, Nat.add_sub in H₃.
          do 2 rewrite <- Nat.add_succ_l in H₃.
          rewrite <- Heqssi, Hs₅ in H₃; discriminate H₃.

          apply Nat.lt_le_incl.
          eapply Nat.lt_le_trans; [ eauto  | idtac ].
          rewrite <- Nat.add_succ_r.
          apply Nat.le_sub_le_add_l.
          rewrite Nat.sub_diag; apply Nat.le_0_l.

         apply Nat.lt_le_incl.
         eapply Nat.lt_le_trans; eauto .
         apply Nat.le_sub_le_add_l.
         rewrite Nat.sub_diag; apply Nat.le_0_l.

        apply Nat.nlt_ge in H₂.
        destruct (lt_dec (si + di₄) j) as [H₃| H₃].
         remember H₃ as H; clear HeqH.
         apply Hni in H.
         rewrite Hs₄ in H.
         destruct b .[ si + di₄]; discriminate H.

         apply Nat.nlt_ge in H₃.
         apply Nat.le_antisymm in H₂; auto.
         pose proof (Hat di₅) as H.
         rewrite H₂, Nat.add_succ_r in H.
         do 2 rewrite <- Nat.add_succ_l in H.
         rewrite <- Heqssi, Hs₅ in H.
         discriminate H.

       rewrite xorb_true_r in Hs₄.
       symmetry in Hs₄.
       apply negb_sym in Hs₄.
       destruct (lt_dec (si + di₄) j) as [H₂| H₂].
        pose proof (Hs₅ (j - S (si + di₄))) as H.
        rewrite Nat.add_sub_assoc in H; auto.
        rewrite <- Nat.add_succ_l, <- Heqssi in H.
        rewrite Nat.add_comm, Nat.add_sub in H.
        rewrite Ha in H; discriminate H.

        apply Nat.nlt_ge in H₂.
        destruct (lt_dec j (si + di₄)) as [H₃| H₃].
         pose proof (Hat (si + di₄ - S j)) as H₄.
         pose proof (Hbt (si + di₄ - S j)) as H₅.
         rewrite <- Nat.sub_succ_l in H₄; auto.
         rewrite <- Nat.sub_succ_l in H₅; auto.
         simpl in H₄, H₅.
         rewrite Nat.add_sub_assoc in H₄; auto.
         rewrite Nat.add_sub_assoc in H₅; auto.
         rewrite Nat.add_comm, Nat.add_sub in H₄.
         rewrite Nat.add_comm, Nat.add_sub in H₅.
         rewrite H₄, H₅ in Hs₄; discriminate Hs₄.

         apply Nat.nlt_ge in H₃.
         apply Nat.le_antisymm in H₃; auto.
         rewrite <- H₃, Ha, Hb in Hs₄; discriminate Hs₄.

      destruct (xorb a .[ i] b .[ i]); discriminate Hs₁.

     pose proof (Hs₃ (j - si)) as H.
     apply Nat.lt_le_incl in Hij.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_comm, Nat.add_sub in H.
     rewrite Ha in H; discriminate H.

 pose proof (Hs₈ 0) as H; rewrite Nat.add_0_r in H.
 apply rm_add_inf_true_neq_if in Hs₅; auto; clear H.
 destruct Hs₅ as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 pose proof (Hs₈ (j - si)) as H.
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
intros a b i Hs₁ Hs₅.
unfold rm_add_i, carry_i.
remember (S i) as si; simpl.
rewrite Hs₁.
rewrite negb_xorb_l, negb_xorb_r.
rewrite xorb_true_r, negb_xorb_r.
unfold rm_add_i, carry_i.
rewrite <- Heqsi; simpl.
rewrite xorb_false_r.
do 2 rewrite xorb_assoc; f_equal.
rewrite xorb_comm; f_equal.
apply fst_same_iff in Hs₁.
apply fst_same_iff in Hs₅.
simpl in Hs₁, Hs₅.
remember (fst_same a 0 si) as s₃ eqn:Hs₃ .
apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
destruct s₃ as [di₃| ].
 destruct Hs₃ as (Hn₃, Hs₃); rewrite Hs₃.
 remember (fst_same a b si) as s₄ eqn:Hs₄ .
 apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
 destruct s₄ as [di₄| ].
  destruct Hs₄ as (Hn₄, Hs₄).
  symmetry.
  pose proof (Hs₁ 0) as H; rewrite Nat.add_0_r in H.
  unfold rm_add_i, carry_i in H.
  remember (S si) as ssi; simpl in H.
  rewrite xorb_false_r in H.
  remember (fst_same a 0 ssi) as s₆ eqn:Hs₆ .
  apply fst_same_sym_iff in Hs₆; simpl in Hs₆.
  destruct s₆ as [di₆| ].
   destruct Hs₆ as (Hn₆, Hs₆); rewrite Hs₆, xorb_false_r in H.
   apply rm_add_inf_true_neq_if in Hs₅; auto.
   destruct Hs₅ as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   rename H into Hab.
   destruct (lt_dec (si + di₄) j) as [H₁| H₁].
    remember H₁ as H; clear HeqH.
    apply Hni in H.
    rewrite Hs₄ in H.
    destruct b .[ si + di₄]; discriminate H.

    apply Nat.nlt_ge in H₁.
    destruct (lt_dec j (si + di₄)) as [H₂| H₂].
     assert (si < S j) as H by (eapply lt_le_trans; eauto ).
     apply lt_add_sub_lt_l in H₂; auto; clear H.
     rename H₂ into H.
     apply Hn₄ in H.
     apply Nat.lt_le_incl in Hij.
     rewrite Nat.add_sub_assoc in H; auto.
     rewrite Nat.add_comm, Nat.add_sub in H.
     rewrite Ha, Hb in H; discriminate H.

     apply Nat.nlt_ge in H₂.
     apply Nat.le_antisymm in H₂; auto.
     rewrite <- H₂, Hb in Hs₄.
     rewrite <- H₂; assumption.

   rewrite xorb_true_r in H.
   apply negb_sym in H.
   rewrite negb_involutive in H.
   symmetry in H.
   apply rm_add_inf_true_eq_if in Hs₅; auto.
   destruct Hs₅ as (Hat, Hbt).
   destruct di₄.
    destruct di₃; [ assumption | idtac ].
    rewrite Hat in Hs₃; discriminate Hs₃.

    rename H into Hab.
    pose proof (Hn₄ 0 (Nat.lt_0_succ di₄)) as H.
    rewrite Nat.add_0_r, Hab in H.
    destruct b .[ si]; discriminate H.

  pose proof (Hs₅ 0) as H.
  rewrite Nat.add_0_r in H.
  unfold rm_add_i, carry_i in H.
  remember (S si) as ssi; simpl in H.
  remember (fst_same a b ssi) as s₆ eqn:Hs₆ .
  apply fst_same_sym_iff in Hs₆; simpl in Hs₆.
  destruct s₆ as [di₆| ].
   destruct Hs₆ as (Hn₆, Hs₆).
   rewrite Heqssi, Nat.add_succ_l, <- Nat.add_succ_r in Hs₆.
   rewrite Hs₄ in Hs₆.
   destruct b .[ si + S di₆]; discriminate Hs₆.

   pose proof (Hs₄ 0) as H₁.
   rewrite Nat.add_0_r in H₁.
   rewrite H₁ in H.
   rewrite negb_xorb_diag in H.
   discriminate H.

 destruct (fst_same a b si) as [di| ]; [ idtac | reflexivity ].
 rewrite Hs₃; reflexivity.
Qed.

Theorem rm_add_add_0_l_when_rhs_has_no_relay : ∀ a b i di₂,
  fst_same ((a + 0)%rm + b) 0 (S i) = Some di₂
  → fst_same (a + b) 0 (S i) = None
  → rm_add_i ((a + 0)%rm + b) 0 i = rm_add_i (a + b) 0 i.
Proof.
intros a b i di₂ Hs₂ Hs₅.
unfold rm_add_i, carry_i.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
rewrite Hs₂, Hs₅.
remember Hs₂ as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, H); rewrite H; clear H.
rewrite xorb_false_r, xorb_true_r.
remember (fst_same (a + 0%rm) b (S i)) as s₁ eqn:Hs₁ .
symmetry in Hs₁; subst si.
destruct s₁ as [di₁| ].
 exfalso.
 eapply rm_add_add_0_l_when_relay; eauto .

 eapply rm_add_add_0_l_when_no_relay; eauto .
Qed.

Theorem rm_add_add_0_r_not_without_relay : ∀ a b i,
  fst_same ((a + 0)%rm + b) 0 (S i) ≠ None.
Proof.
intros a b i Hs₂.
remember (S i) as si.
apply fst_same_iff in Hs₂; simpl in Hs₂.
destruct (bool_dec ((a + 0)%rm) .[ si] b .[ si]) as [H₁| H₁].
 apply rm_add_inf_true_eq_if in Hs₂; auto.
 simpl in Hs₂, H₁.
 destruct Hs₂ as (Hn₂, Hs₂).
 eapply not_rm_add_0_inf_1_succ; eauto .

 apply neq_negb in H₁.
 apply rm_add_inf_true_neq_if in Hs₂; auto.
 simpl in Hs₂.
 destruct Hs₂ as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 eapply not_rm_add_0_inf_1_succ; eauto .
Qed.

(* perhaps could be proved if associativity proved before;
   in that case, that would be very simple instead of these
   big lemmas before *)
Theorem rm_add_add_0_r : ∀ a b, (a + 0 + b = a + b)%rm.
Proof.
intros a b.
unfold rm_eq; intros i; simpl.
remember (fst_same ((a + 0)%rm + b) 0 (S i)) as s₂ eqn:Hs₂ .
remember (fst_same (a + b) 0 (S i)) as s₅ eqn:Hs₅ .
symmetry in Hs₂, Hs₅.
destruct s₂ as [di₂| ].
 destruct s₅ as [di₅| ].
  eapply rm_add_add_0_l_when_both_hs_has_relay; eauto .

  eapply rm_add_add_0_l_when_rhs_has_no_relay; eauto .

 exfalso; revert Hs₂.
 eapply rm_add_add_0_r_not_without_relay; eauto .
Qed.

Theorem rm_add_compat_r : ∀ a b c, (a = b)%rm → (a + c = b + c)%rm.
Proof.
intros a b c Hab.
remember (a + 0)%rm as a₁.
remember (b + 0)%rm as b₁.
remember Heqa₁ as H; clear HeqH.
eapply rm_norm_eq_compat_r with (b₀ := b) (c := c) in H; eauto .
 subst a₁ b₁.
 do 2 rewrite rm_add_add_0_r in H; assumption.

 subst a₁ b₁.
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
unfold rm_add_i, carry_i.
remember (S i) as si; simpl.
rewrite xorb_false_r.
remember (fst_same 0 0 si) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ]; [ clear di₁ Hs₁ | discriminate Hs₁; auto ].
remember (fst_same (a - a) 0 si) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁); rewrite Hs₁, xorb_false_r.
 unfold rm_add_i, carry_i.
 rewrite <- Heqsi; simpl.
 remember (fst_same a (- a) si) as s₂ eqn:Hs₂ .
 apply fst_same_sym_iff in Hs₂; simpl in Hs₂.
 rewrite <- negb_xorb_r, negb_xorb_l, negb_xorb_diag.
 destruct s₂ as [di₂| ]; [ idtac | reflexivity ].
 destruct Hs₂ as (Hn₂, Hs₂).
 destruct a .[ si + di₂]; discriminate Hs₂.

 destruct (bool_dec a .[ si] (negb a .[ si])) as [H₁| H₁].
  destruct a .[ si]; discriminate H₁.

  apply neq_negb in H₁.
  apply rm_add_inf_true_neq_if in Hs₁; auto.
  simpl in Hs₁.
  destruct Hs₁ as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
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
 unfold carry_i in HH; simpl in HH.
 remember (fst_same 0%rm 0%rm (S di)) as s₁ eqn:Hs₁ .
 apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
 destruct s₁ as [di₁| ]; [ idtac | discriminate Hs₁; assumption ].
 discriminate HH.

 left.
 unfold rm_eq; intros i; simpl.
 rewrite Hs.
 unfold rm_add_i; simpl.
 unfold carry_i; simpl.
 remember (fst_same 0 0 (S i)) as s₁ eqn:Hs₁ .
 destruct s₁; [ reflexivity | idtac ].
 apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
 discriminate Hs₁; assumption.
Qed.

Theorem fst_same_diag : ∀ a i, fst_same a a i = Some 0.
Proof.
intros a i.
apply fst_same_iff; simpl.
split; [ idtac | reflexivity ].
intros dj Hdj; exfalso.
revert Hdj; apply Nat.nlt_0_r.
Qed.

Theorem carry_diag : ∀ a i, carry_i a a i = a.[S i].
Proof.
intros a i.
unfold carry_i; simpl.
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

Theorem fst_same_before : ∀ a b i dk dl di₄,
  fst_same a b (S i) = Some dk
  → dl < dk
  → fst_same a b (S (S (i + dl))) = Some di₄
  → di₄ = dk - S dl.
Proof.
intros a b i dk dl di₄ Hsk Hdl Hs₄.
destruct (lt_dec di₄ (dk - S dl)) as [H₂| H₂].
 apply Nat.lt_add_lt_sub_r in H₂.
 apply fst_same_iff in Hsk; simpl in Hsk.
 destruct Hsk as (Hnk, Hsk).
 apply Hnk in H₂.
 apply fst_same_iff in Hs₄; simpl in Hs₄.
 destruct Hs₄ as (Hn₄, Hs₄).
 rewrite Nat.add_assoc, Nat.add_shuffle0 in H₂.
 rewrite Nat.add_succ_r in H₂; simpl in H₂.
 rewrite Hs₄ in H₂.
 destruct b .[ S (S (i + dl + di₄))]; discriminate H₂.

 apply Nat.nlt_ge in H₂.
 destruct (lt_dec (dk - S dl) di₄) as [H₃| H₃].
  apply fst_same_iff in Hs₄.
  destruct Hs₄ as (Hn₄, Hs₄).
  apply Hn₄ in H₃.
  apply fst_same_iff in Hsk.
  destruct Hsk as (Hnk, Hsk).
  rewrite Nat.add_sub_assoc in H₃; auto.
  rewrite <- Nat.add_succ_r in H₃.
  rewrite <- Nat.add_succ_l in H₃.
  rewrite Nat.add_shuffle0, Nat.add_sub in H₃.
  rewrite Hsk in H₃.
  destruct b .[ S i + dk]; discriminate H₃.

  apply Nat.nlt_ge in H₃.
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
destruct (bool_dec ((a + 0)%rm) .[ i] ((b + 0)%rm) .[ i]) as [H₁| H₁].
 apply rm_add_inf_true_eq_if in Hab; auto.
 destruct Hab as (H, _); simpl in H.
 apply not_rm_add_0_inf_1_succ in H; auto.

 apply neq_negb in H₁.
 apply rm_add_inf_true_neq_if in Hab; auto.
 simpl in Hab.
 destruct Hab as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 apply not_rm_add_0_inf_1_succ in Hat; auto.
Qed.

Theorem rm_add_i_norm_norm : ∀ a b i,
  rm_add_i ((a + 0)%rm + (b + 0)%rm) 0 i = rm_add_i (a + 0%rm) (b + 0%rm) i.
Proof.
intros a b i.
unfold rm_add_i, carry_i at 1.
remember (S i) as si; simpl.
rewrite xorb_false_r.
remember (fst_same ((a + 0)%rm + (b + 0)%rm) 0 si) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁); rewrite Hs₁, xorb_false_r; reflexivity.

 apply not_add_norm_inf_1 in Hs₁; contradiction.
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
destruct (bool_dec a .[ i] b .[ i]) as [H₁| H₁].
 apply rm_add_inf_true_eq_if in Hj; auto.
 destruct Hj as (Ha, Hb).
 exists (S i).
 split; [ apply Nat.lt_succ_diag_r | idtac ].
 split; intros di; rewrite Nat.add_succ_l, <- Nat.add_succ_r.
   apply Ha.

   apply Hb.

 apply neq_negb in H₁.
 apply rm_add_inf_true_neq_if in Hj; auto.
 destruct Hj as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 exists j.
 split; [ assumption | split; assumption ].
Qed.

Theorem carry_0_r_true_if : ∀ a i,
  carry_i a 0 i = true
  → id (∀ dj, a.[i + S dj] = true).
Proof.
intros a i H j.
unfold carry_i in H; simpl in H.
remember (fst_same a 0 (S i)) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁).
 rewrite Hs₁ in H; discriminate H.

 rewrite Nat.add_succ_r; apply Hs₁.
Qed.

(* trying to make a lemma for something used many times, but it does
   not seem to work properly *)
Theorem same_relays : ∀ di₁ di₂ f g,
  (∀ dj, dj < di₁ → f dj = negb (g dj))
  → (∀ dj, dj < di₂ → f dj = negb (g dj))
  → f di₁ = g di₁
  → f di₂ = g di₂
  → di₁ = di₂.
Proof.
intros di₁ di₂ f g Hdi₁ Hdi₂ Hf₁ Hf₂.
destruct (lt_dec di₁ di₂) as [H₁| H₁].
 apply Hdi₂ in H₁.
 rewrite Hf₁ in H₁.
 destruct (g di₁); discriminate H₁.

 apply Nat.nlt_ge in H₁.
 destruct (lt_dec di₂ di₁) as [H₂| H₂].
  apply Hdi₁ in H₂.
  rewrite Hf₂ in H₂.
  destruct (g di₂); discriminate H₂.

  apply Nat.nlt_ge in H₂.
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
 destruct (lt_eq_lt_dec dj (i + di - j)) as [[H₁| H₁]| H₁].
  apply Nat.lt_add_lt_sub_l in H₁; rename H₁ into H.
  apply lt_add_sub_lt_l in H.
   apply Hni in H; simpl in H.
   rewrite Nat.add_sub_assoc in H.
    rewrite Nat.add_comm, Nat.add_sub in H.
    rewrite Hsj in H.
    exfalso; apply neq_negb in H; apply H; reflexivity.

    eapply le_trans; eauto; apply Nat.le_add_r.

   apply le_n_S.
   eapply le_trans; eauto; apply Nat.le_add_r.

  rewrite H₁; reflexivity.

  apply Hnj in H₁.
  rewrite Nat.add_sub_assoc in H₁; [ idtac | assumption ].
  rewrite Nat.add_comm, Nat.add_sub in H₁.
  rewrite Hsi in H₁.
  exfalso; apply neq_negb in H₁; apply H₁; reflexivity.

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

Theorem carry_before_relay : ∀ a b i di x,
  fst_same a b i = Some di
  → a .[i + di] = x
  → ∀ dj, dj < di → carry_i a b (i + dj) = x.
Proof.
intros a b i di x Hs Ha dj Hdj.
unfold carry_i; simpl.
remember (fst_same a b (S (i + dj))) as s₂ eqn:Hs₂ .
symmetry in Hs₂.
assert (S (i + dj) ≤ i + di) as H by (apply Nat.add_lt_mono_l; auto).
eapply fst_same_in_range in Hs₂; try eassumption; [ idtac | split; auto ].
 subst s₂.
 rewrite <- Nat.add_succ_l, Nat.add_sub_assoc; auto.
 rewrite Nat.add_comm, Nat.add_sub; assumption.

 rewrite <- Nat.add_succ_r.
 apply Nat.le_add_r.
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
destruct H as (Hs₁, Hn₁).
remember Hdj as H; clear HeqH.
apply Hs₁ in H.
rewrite H, negb_xorb_diag, xorb_true_l.
f_equal; erewrite carry_before_relay; try eassumption; reflexivity.
Qed.

Theorem carry_when_inf_1 : ∀ a b i j,
  (∀ di, a.[S (i + di)] = true)
  → i ≤ j
  → carry_i a b j = true.
Proof.
intros a b i j Hdi Hij.
unfold carry_i; simpl.
remember (fst_same a b (S j)) as s₁ eqn:Hs₁ .
destruct s₁ as [di₁| ]; [ idtac | reflexivity ].
apply Nat.sub_add in Hij.
rewrite Nat.add_comm in Hij.
rewrite <- Hij, <- Nat.add_assoc.
apply Hdi.
Qed.

(*
Theorem case_1 : ∀ a b c i,
  carry_i (a + (b + c)%rm) 0 i = true
  → carry_i ((a + b)%rm + c) 0 i = true
  → carry_i a (b + c) i = true
  → carry_i b c i = true
  → carry_i a b i = false
  → False.
Proof.
intros a b c i Hc₁ Hc₂ Hc₃ Hc₅ Hc₆.
apply carry_0_r_true_if in Hc₁.
apply carry_0_r_true_if in Hc₂.
unfold id in Hc₁, Hc₂.
simpl in Hc₁, Hc₂.
unfold carry_i in Hc₆; simpl in Hc₆.
remember (fst_same a b (S i)) as s₆ eqn:Hs₆ .
remember Hs₆ as Hss₆; clear HeqHss₆.
apply fst_same_sym_iff in Hs₆; simpl in Hs₆.
destruct s₆ as [di₆| ]; [ idtac | discriminate Hc₆ ].
destruct Hs₆ as (Hn₆, Hs₆).
rewrite Hc₆ in Hs₆.
rename Hc₆ into Ha₆; rename Hs₆ into Hb₆.
move Ha₆ after Hb₆; symmetry in Hb₆.
pose proof (Hc₁ di₆) as H; simpl in H.
rewrite Nat.add_succ_r in H; simpl in H.
unfold rm_add_i in H; simpl in H.
rewrite Ha₆, xorb_false_l in H.
rename H into Hca; move Hca before Hb₆.
unfold carry_i in Hc₃; simpl in Hc₃.
remember (fst_same a (b + c) (S i)) as s₃ eqn:Hs₃ .
remember Hs₃ as Hss₃; clear HeqHss₃.
apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
destruct s₃ as [di₃| ].
 destruct Hs₃ as (Hn₃, Hs₃).
 destruct (lt_eq_lt_dec di₃ di₆) as [[H₁| H₁] | H₁].
  remember H₁ as H; clear HeqH.
  apply Hn₆ in H.
  rewrite Hc₃ in H.
  symmetry in H.
  apply negb_true_iff in H.
  rename H into Hb₃.
  move Hb₃ before Hc₃.
  rename Hc₃ into Ha₃.
  move Hs₃ after Hb₃.
  rewrite Ha₃ in Hs₃; symmetry in Hs₃.
  unfold rm_add_i in Hs₃; simpl in Hs₃.
  rewrite Hb₃, xorb_false_l in Hs₃.
  unfold carry_i in Hc₅; simpl in Hc₅.
  remember (fst_same b c (S i)) as s₅ eqn:Hs₅ .
  remember Hs₅ as Hss₅; clear HeqHss₅.
  destruct s₅ as [di₅| ].
   apply fst_same_sym_iff in Hs₅; simpl in Hs₅.
   destruct Hs₅ as (Hn₅, Hs₅).
   rewrite Hc₅ in Hs₅.
   rename Hc₅ into Hb₅; rename Hs₅ into Hc₅.
   symmetry in Hc₅; move Hb₅ after Hc₅.
   destruct (lt_eq_lt_dec di₅ di₃) as [[H₂|H₂]|H₂].
    remember H₂ as H; clear HeqH.
    apply Hn₃ in H.
    apply negb_sym in H.
    rename H into Hs₅.
    move Hs₅ before Hc₅.
    assert (di₅ < di₆) as H₅₆ by (eapply lt_trans; eauto ).
    apply Hn₆ in H₅₆.
    rewrite Hb₅ in H₅₆; simpl in H₅₆.
    move H₅₆ after Hb₅.
    rewrite H₅₆ in Hs₅; simpl in Hs₅.
    destruct di₅.
     clear Hn₅; rewrite Nat.add_0_r in H₅₆, Hb₅, Hc₅, Hs₅.
     pose proof (Hc₁ 0) as H.
     rewrite Nat.add_1_r in H.
     unfold rm_add_i in H; simpl in H.
     rewrite H₅₆, xorb_false_l in H.
     unfold rm_add_i in H; simpl in H.
     rewrite Hb₅, Hc₅, xorb_nilpotent, xorb_false_l in H.
     unfold rm_add_i in Hs₅.
     rewrite Hb₅, Hc₅, xorb_nilpotent, xorb_false_l in Hs₅.
     rewrite Hs₅, xorb_true_l in H.
     apply negb_true_iff in H.
     unfold carry_i in H; simpl in H.
     remember (fst_same a (b + c) (S (S i))) as s₁ eqn:Hs₁ .
     symmetry in Hss₃, Hs₁.
     assert (S i ≤ i + di₃) as HH by (apply lt_add_r; auto).
     eapply fst_same_in_range in Hs₁; try eassumption.
      subst s₁; simpl in H.
      rewrite <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Nat.add_comm, Nat.add_sub in H.
      rewrite Ha₃ in H; discriminate H.

      split; [ apply Nat.le_succ_diag_r | idtac ].
      apply le_n_S; assumption.

     remember Hss₅ as H; clear HeqH; symmetry in H.
     assert (di₅ < S di₅) as HH by apply Nat.lt_succ_diag_r.
     eapply sum_before_relay in H; try eassumption; clear HH.
     simpl in H; rewrite fold_rm_add_i in H; rename H into Hx.
     assert (di₅ < di₃) as H.
      eapply le_lt_trans; [ apply Nat.le_succ_diag_r | eauto  ].

      apply Hn₃ in H.
      rewrite fold_rm_add_i in H.
      rewrite Hx in H; simpl in H.
      rename H into Ha₅; rename Hx into Hbc.
      remember Hss₆ as H; clear HeqH; symmetry in H.
      apply Nat.lt_le_incl in H₂.
      assert (di₅ < di₆) as HH by (eapply lt_trans; eauto ).
      eapply sum_before_relay in H; try eassumption; clear HH.
      simpl in H; rewrite fold_rm_add_i in H; rename H into Hx.
      pose proof (Hc₁ di₅) as H.
      rewrite Nat.add_succ_r in H.
      unfold rm_add_i in H; simpl in H.
      rewrite fold_rm_add_i in H.
      rewrite Ha₅, Hbc in H.
      rewrite xorb_true_l in H.
      apply negb_true_iff in H.
      rewrite <- Nat.add_succ_l in H.
      erewrite carry_before_relay in H; eauto; discriminate H.

    subst di₅.
    rewrite Hb₃ in Hb₅; discriminate Hb₅.

    remember Hss₅ as H; clear HeqH; symmetry in H.
    eapply sum_before_relay in H; try eassumption; simpl in H.
    rename H into Hx; rewrite <- Nat.add_succ_r in Hx.
    remember H₂ as H; clear HeqH.
    apply Hn₅ in H.
    rewrite Hb₃ in H.
    symmetry in H.
    apply negb_false_iff in H.
    rewrite H in Hs₃.
    rewrite xorb_true_l in Hs₃.
    apply negb_true_iff in Hs₃.
    rewrite <- Nat.add_succ_l in Hs₃.
    erewrite carry_before_relay in Hs₃; eauto; discriminate Hs₃.

   apply fst_same_sym_iff in Hs₅.
   simpl in Hs₅.
   rewrite Hs₅ in Hb₃.
   apply negb_false_iff in Hb₃.
   rewrite Hb₃, xorb_true_l in Hs₃.
   apply negb_true_iff in Hs₃.
   unfold carry_i in Hs₃.
   remember (fst_same b c (S (S (i + di₃)))) as s₁ eqn:Hs₁ .
   destruct s₁ as [di₁| ]; [ idtac | discriminate Hs₃ ].
   apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
   destruct Hs₁ as (Hn₁, Hs₁).
   rewrite <- Nat.add_succ_r, <- Nat.add_assoc in Hs₁.
   rewrite Hs₅ in Hs₁.
   destruct c .[ S (i + (di₃ + S di₁))]; discriminate Hs₁.

  subst di₆.
  rewrite Hc₃ in Ha₆; discriminate Ha₆.

  remember H₁ as H; clear HeqH.
  apply Hn₃ in H.
  rewrite Ha₆ in H; symmetry in H.
  apply negb_false_iff in H.
  rename H into Hbc; move Hbc before Hb₆.
  rewrite Hbc, xorb_true_l in Hca.
  apply negb_true_iff in Hca.
  remember Hbc as H; clear HeqH.
  unfold rm_add_i in H; simpl in H.
  rewrite Hb₆, xorb_false_l in H.
  rename H into Hcc; move Hcc before Hb₆.
  remember Hca as H; clear HeqH.
  rewrite <- Nat.add_succ_l in H.
  erewrite carry_before_relay in H; eauto ; discriminate H.

 clear Hc₃.
 pose proof (Hs₃ di₆) as H.
 rewrite Ha₆ in H; symmetry in H.
 apply negb_false_iff in H.
 rename H into Hbc; move Hbc before Hb₆.
 rewrite Hbc, xorb_true_l in Hca.
 apply negb_true_iff in Hca.
 remember Hbc as H; clear HeqH.
 unfold rm_add_i in H; simpl in H.
 rewrite Hb₆, xorb_false_l in H.
 rename H into Hcc; move Hcc before Hb₆.
 remember Hca as H; clear HeqH.
 unfold carry_i in H; simpl in H.
 remember (fst_same a (b + c) (S (S (i + di₆)))) as s₁ eqn:Hs₁ .
 destruct s₁ as [di₁| ]; [ idtac | discriminate H ].
 apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
 destruct Hs₁ as (Hn₁, Hs₁).
 rewrite H in Hs₁.
 symmetry in Hs₁.
 rename H into Ha₁; move Ha₁ after Hs₁.
 pose proof (Hs₃ (S (di₆ + di₁))) as H.
 rewrite Nat.add_succ_r in H.
 rewrite Nat.add_assoc in H.
 rewrite Ha₁, Hs₁ in H.
 discriminate H.
Qed.
*)

(*
Theorem case_2 : ∀ a b c i,
  carry_i (a + (b + c)%rm) 0 i = true
  → carry_i ((a + b)%rm + c) 0 i = true
  → carry_i a (b + c) i = true
  → carry_i (a + b) c i = false
  → carry_i b c i = true
  → carry_i a b i = true
  → False.
Proof.
(* à revoir, refaire à partir de (*1*); voir à partir de (*2*) *)
intros a b c i Hc₁ Hc₂ Hc₃ Hc₄ Hc₅ Hc₆.
remember Hc₁ as H; clear HeqH.
apply carry_0_r_true_if in H; unfold id in H; simpl in H.
rename H into Hj₁; move Hj₁ before Hc₁.
remember Hc₂ as H; clear HeqH.
apply carry_0_r_true_if in H; unfold id in H; simpl in H.
rename H into Hj₂; move Hj₂ before Hc₂.
remember Hj₁ as H; clear HeqH; move H before Hj₁.
apply forall_add_succ_r in H; unfold id in H.
apply rm_add_inf_true_if in H; simpl in H.
destruct H as (dj₁, (Hta₁, (Htb₁, (Hfa₁, (Hfb₁, Hsj₁))))).
remember Hj₂ as H; clear HeqH; move H before Hj₂.
apply forall_add_succ_r in H; unfold id in H.
apply rm_add_inf_true_if in H; simpl in H.
destruct H as (dj₂, (Hta₂, (Htb₂, (Hfa₂, (Hfb₂, Hsj₂))))).
rewrite <- Nat.add_succ_r in Hfa₁.
rewrite <- Nat.add_succ_r in Hfb₁.
rewrite <- Nat.add_succ_r in Hfa₂.
rewrite <- Nat.add_succ_r in Hfb₂.
remember Htb₁ as H; clear HeqH.
apply forall_add_succ_l in H.
unfold id in H.
apply rm_add_inf_true_if in H.
move H before Hsj₁.
destruct H as (dk₁, (Hbl₁, (Hcl₁, (Hbk₁, (Hck₁, Hss₁))))).
remember Hta₂ as H; clear HeqH.
apply forall_add_succ_l in H; unfold id in H.
apply rm_add_inf_true_if in H.
move H before Hsj₂.
destruct H as (dk₂, (Hbl₂, (Hcl₂, (Hbk₂, (Hck₂, Hss₂))))).
(*1*)
remember Hc₄ as H; clear HeqH.
unfold carry_i in H; simpl in H.
remember (fst_same (a + b) c (S i)) as s₄ eqn:Hs₄ .
remember Hs₄ as Hss₄; clear HeqHss₄.
apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
destruct s₄ as [di₄| ]; [ idtac | discriminate H ].
destruct Hs₄ as (Hn₄, Hs₄).
rewrite H in Hs₄; symmetry in Hs₄.
move Hn₄ before Hc₄; move Hs₄ before Hn₄.
rename H into Hi₄; move Hi₄ before Hs₄.
remember Hc₅ as H; clear HeqH.
unfold carry_i in H; simpl in H.
remember (fst_same b c (S i)) as s₅ eqn:Hs₅ .
rename H into Hj₅.
move Hs₅ before Hc₅; move Hj₅ before Hs₅.
destruct s₅ as [di₅| ].
 remember Hs₅ as H; clear HeqH.
 apply fst_same_sym_iff in H; simpl in H.
 destruct H as (Hn₅, Ht₅).
 rewrite Hj₅ in Ht₅; symmetry in Ht₅.
 move Hn₅ after Hs₅; move Ht₅ before Hj₅.
 destruct (lt_eq_lt_dec di₄ di₅) as [[H₄| H₄]| H₄].
  remember H₄ as H; clear HeqH.
  apply Hn₅ in H.
  rewrite Hs₄ in H; simpl in H.
  rename H into Hb₄; move Hb₄ after Hs₄.
  remember Hi₄ as H; clear HeqH.
  unfold rm_add_i in H; simpl in H.
  rewrite Hb₄, xorb_true_r in H.
  rewrite <- negb_xorb_l in H.
  apply negb_false_iff in H.
  rename H into Ha₄; move Ha₄ after Hb₄.
  remember Hc₆ as H; clear HeqH.
  unfold carry_i in H; simpl in H.
  rename H into Hk₁.
  remember (fst_same a b (S i)) as s₁ eqn:Hs₁ .
  destruct s₁ as [di₁| ].
   remember Hs₁ as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn₁, Ht₁).
   rewrite Hk₁ in Ht₁; symmetry in Ht₁.
   move Hn₁ after Hs₁.
   destruct (lt_eq_lt_dec di₁ di₄) as [[H₂| H₂]| H₂].
    remember H₂ as H; clear HeqH.
    apply Hn₄ in H.
    rename H into Hab₁.
    move Hab₁ before Ht₁.
    assert (di₁ < di₅) as H by (eapply lt_trans; eauto ).
    apply Hn₅ in H.
    rewrite Ht₁ in H; apply negb_sym in H; simpl in H.
    rewrite H in Hab₁; simpl in Hab₁.
    rename H into Hd₁; move Hd₁ before Ht₁.
    destruct di₁.
     clear Hn₁; rewrite Nat.add_0_r in Hk₁, Ht₁, Hd₁, Hab₁.
     pose proof (Hj₁ 0) as H; simpl in H.
     rewrite Nat.add_1_r in H.
     unfold rm_add_i in H; simpl in H.
     unfold rm_add_i in H.
     rewrite Hk₁, Ht₁, Hd₁ in H.
     rewrite xorb_true_l, xorb_false_r in H.
     rewrite negb_xorb_l, xorb_false_l in H.
     symmetry in Hs₅.
     assert (0 < di₅) as HH by (eapply lt_trans; eauto ).
     replace (S i) with (S i + 0) in H by apply Nat.add_0_r.
     erewrite carry_before_relay in H; try eassumption.
     rewrite Nat.add_0_r in H.
     rename H into Hk₂.
     rewrite xorb_true_l in Hk₂.
     apply negb_true_iff in Hk₂.
     remember Hc₃ as H₁; clear HeqH₁.
     remember Hk₂ as H₃; clear HeqH₃.
     unfold carry_i in H₁; simpl in H₁.
     remember (fst_same a (b + c) (S i)) as s₆ eqn:Hs₆ .
     destruct s₆ as [di₆| ].
      symmetry in Hs₆.
      destruct di₆.
       apply fst_same_iff in Hs₆; simpl in Hs₆.
       destruct Hs₆ as (_, Hs₆).
       rewrite Nat.add_0_r in Hs₆, H₁.
       rewrite H₁ in Hs₆; symmetry in Hs₆.
       unfold rm_add_i in Hs₆; simpl in Hs₆.
       rewrite Ht₁, Hd₁ in Hs₆.
       rewrite xorb_true_l in Hs₆.
       apply negb_true_iff in Hs₆.
       replace (S i) with (S i + 0) in Hs₆ by apply Nat.add_0_r.
       erewrite carry_before_relay in Hs₆; try eassumption.
       discriminate Hs₆.

       replace (S i) with (S i + 0) in H₃ by apply Nat.add_0_r.
       pose proof (Nat.lt_0_succ di₆) as H.
       erewrite carry_before_relay in H₃; try eassumption.
       discriminate H₃.

      apply fst_same_sym_iff in Hs₆; simpl in Hs₆.
      unfold carry_i in H₃; simpl in H₃.
      remember (fst_same a (b + c) (S (S i))) as s₇ eqn:Hs₇ .
      destruct s₇ as [di₇| ]; [ idtac | discriminate H₃ ].
      apply fst_same_sym_iff in Hs₇; simpl in Hs₇.
      destruct Hs₇ as (Hn₇, Hs₇).
      rewrite <- Nat.add_succ_r in Hs₇.
      rewrite Hs₆ in Hs₇; symmetry in Hs₇.
      apply neq_negb in Hs₇; apply Hs₇; reflexivity.

     pose proof (Hn₁ 0 (Nat.lt_0_succ di₁)) as H.
     rewrite Nat.add_0_r in H.
     rename H into Hab.
     assert (0 < di₅) as H by (eapply Nat.lt_lt_0; eauto ).
     apply Hn₅ in H; simpl in H.
     rewrite Nat.add_0_r in H.
     rename H into Hbc.
     pose proof (Hj₁ 0) as H; simpl in H.
     rewrite Nat.add_1_r in H.
     unfold rm_add_i in H; simpl in H.
     unfold rm_add_i in H.
     do 2 rewrite <- xorb_assoc in H.
     rewrite Hab, negb_xorb_diag in H.
     rewrite xorb_true_l in H.
     replace (S i) with (S i + 0) in H by apply Nat.add_0_r.
     symmetry in Hs₅.
     assert (0 < di₅) as HH by (eapply Nat.lt_lt_0; eauto ).
     erewrite carry_before_relay in H; try eassumption.
     rewrite xorb_true_r, negb_involutive in H.
     rewrite Nat.add_0_r in H; rename H into Hk₂.
     remember Hs₅ as H; clear HeqH.
     eapply sum_before_relay in H; try eassumption; clear HH.
     rewrite Nat.add_0_r in H; simpl in H.
     rename H into Hx.
     remember Hs₁ as H; clear HeqH; symmetry in H.
     assert (0 < S di₁) as HH by apply Nat.lt_0_succ.
     eapply sum_before_relay in H; try eassumption; clear HH.
     rewrite Nat.add_0_r in H; simpl in H.
     rename H into Hy.
     pose proof (Hj₂ 0) as H.
     rewrite Nat.add_1_r in H.
     unfold rm_add_i in H; simpl in H.
     rewrite Hy, xorb_false_l in H.
     rename H into Hk₃.
     assert (0 < di₄) as H by (eapply Nat.lt_lt_0; eauto ).
     apply Hn₄ in H; simpl in H.
     rewrite Nat.add_0_r in H.
     rewrite Hy in H.
     apply negb_sym in H; simpl in H.
     rewrite H in Hbc, Hk₂, Hk₃.
     rewrite xorb_true_l in Hk₂, Hk₃; simpl in Hbc.
     rewrite Hbc in Hab; simpl in Hab.
     apply negb_true_iff in Hk₂.
     apply negb_true_iff in Hk₃.
     rename H into Hcc.
     move Hcc before Hbc.
     remember Hx as H; clear HeqH.
     unfold rm_add_i in H; simpl in H.
     rewrite Hbc, Hcc, xorb_true_l in H.
     apply negb_false_iff in H.
     rename H into Hca.
     remember Hc₃ as H₁; clear HeqH₁.
     unfold carry_i in H₁; simpl in H₁.
     remember (fst_same a (b + c) (S i)) as s₆ eqn:Hs₆ .
     destruct s₆ as [di₆| ].
      symmetry in Hs₆.
      destruct di₆.
       apply fst_same_iff in Hs₆; simpl in Hs₆.
       destruct Hs₆ as (_, Hs₆).
       rewrite Nat.add_0_r in Hs₆, H₁.
       rewrite H₁ in Hs₆; symmetry in Hs₆.
       unfold rm_add_i in Hs₆; simpl in Hs₆.
       rewrite Hbc, Hcc in Hs₆.
       rewrite xorb_true_l in Hs₆.
       apply negb_true_iff in Hs₆.
       rewrite Hca in Hs₆; discriminate Hs₆.

       remember Hk₂ as H₃; clear HeqH₃.
       replace (S i) with (S i + 0) in H₃ by apply Nat.add_0_r.
       assert (0 < S di₆) as H by apply Nat.lt_0_succ.
       erewrite carry_before_relay in H₃; try eassumption.
       discriminate H₃.

      apply fst_same_sym_iff in Hs₆; simpl in Hs₆.
      remember Hk₂ as H₃; clear HeqH₃.
      unfold carry_i in H₃; simpl in H₃.
      remember (fst_same a (b + c) (S (S i))) as s₇ eqn:Hs₇ .
      destruct s₇ as [di₇| ]; [ idtac | discriminate H₃ ].
      apply fst_same_sym_iff in Hs₇; simpl in Hs₇.
      destruct Hs₇ as (Hn₇, Hs₇).
      rewrite <- Nat.add_succ_r in Hs₇.
      rewrite Hs₆ in Hs₇.
      destruct (rm_add_i b c (S (i + S di₇))); discriminate Hs₇.

    subst di₄.
    rewrite Hk₁, xorb_true_l in Ha₄.
    apply negb_true_iff in Ha₄.
    destruct di₁.
     clear Hn₁ Hn₄ Hb₄; rewrite Nat.add_0_r in Hk₁, Ht₁, Ha₄, Hs₄, Hi₄.
     destruct dj₁.
      clear Hfa₁ Hfb₁; rewrite Nat.add_0_r in Hta₁, Htb₁.
      pose proof (Htb₁ 0) as H.
      rewrite Nat.add_0_r in H.
      unfold rm_add_i in H; simpl in H.
      rewrite Ht₁, Hs₄ in H.
      rewrite xorb_true_l in H.
      apply negb_true_iff in H.
      replace (S i) with (S i + 0) in H by apply Nat.add_0_r.
      symmetry in Hs₅.
      erewrite carry_before_relay in H; try eassumption.
      discriminate H.

      simpl in Hsj₁, Hfa₁.
      remember Hc₃ as H; clear HeqH.
      unfold carry_i in H.
      rewrite Hsj₁ in H; simpl in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hfa₁ in H; [ discriminate H | apply Nat.lt_0_succ ].

     injection Hsj₂; clear Hsj₂; intros Hsj₂.
     destruct dj₂; [ discriminate Hsj₂ | simpl in Hsj₂; subst dj₂ ].
     clear Hfa₂ Hfb₂; simpl in Hta₂, Htb₂.
     pose proof (Hta₂ (di₅ - S (S di₁))) as H.
     rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
     rewrite Nat.add_shuffle0, Nat.add_sub in H.
     rename H into Hab.
     pose proof (Hn₁ 0 (Nat.lt_0_succ di₁)) as H₁.
     pose proof (Hn₄ 0 (Nat.lt_0_succ di₁)) as H₂.
     rewrite Nat.add_0_r in H₁, H₂.
     unfold rm_add_i in H₂; simpl in H₂.
     rewrite H₁, negb_xorb_diag, xorb_true_l in H₂.
     apply negb_sym in H₂.
     rewrite negb_involutive in H₂.
     replace (S i) with (S i + 0) in H₂ by apply Nat.add_0_r.
     symmetry in Hs₁.
     assert (0 < S di₁) as H by apply Nat.lt_0_succ.
     erewrite carry_before_relay in H₂; try eassumption; clear H.
     rewrite Nat.add_0_r in H₂.
     assert (0 < di₅) as H by (eapply Nat.lt_lt_0; eauto ).
     apply Hn₅ in H; rewrite Nat.add_0_r in H.
     rewrite H₂ in H.
     rewrite H in H₁; simpl in H₁, H.
     rename H into H₃.
     destruct dj₁.
      pose proof (Htb₁ 0) as HH.
      rewrite Nat.add_0_r in HH.
      rewrite Nat.add_0_r in HH.
      unfold rm_add_i in HH.
      rewrite H₃, H₂, xorb_false_l, xorb_true_l in HH.
      apply negb_true_iff in HH.
      symmetry in Hs₅.
      replace (S i) with (S i + 0) in HH by apply Nat.add_0_r.
      assert (0 < di₅) as H by (eapply Nat.lt_lt_0; eauto ).
      erewrite carry_before_relay in HH; try eassumption.
      discriminate HH.

      simpl in Hsj₁.
      pose proof (Hj₁ 0) as H; rewrite Nat.add_1_r in H.
      unfold rm_add_i in H; simpl in H.
      unfold rm_add_i in H.
      rewrite H₁, H₃, H₂ in H.
      rewrite xorb_true_l, xorb_false_l in H.
      rewrite negb_xorb_l, xorb_false_l in H.
      symmetry in Hs₅.
      replace (S i) with (S i + 0) in H by apply Nat.add_0_r.
      assert (0 < di₅) as HH by (eapply Nat.lt_lt_0; eauto ).
      erewrite carry_before_relay in H; try eassumption.
      rewrite xorb_true_l in H.
      apply negb_true_iff in H.
      destruct dj₁.
       simpl in Hfa₁; rewrite Nat.add_1_r in Hfa₁.
       rewrite Hfa₁ in H₁; [ discriminate H₁ | apply Nat.lt_0_1 ].

       rename H into Hca.
       remember Hc₃ as H; clear HeqH.
       unfold carry_i in H; simpl in H.
       rewrite Hsj₁ in H; simpl in H.
       assert (0 < S dj₁) as H₅ by apply Nat.lt_0_succ.
       erewrite carry_before_relay in Hca; try eassumption.
       discriminate Hca.

    injection Hsj₂; clear Hsj₂; intros Hsj₂; move Hsj₂ before Hfb₂.
    remember H₂ as H; clear HeqH.
    apply Hn₁ in H.
    rewrite Hb₄ in H; simpl in H.
    rewrite H, xorb_false_l in Ha₄.
    rename Ha₄ into Hab₄; move Hab₄ after Hs₄.
    rename H into Ha₄; move Ha₄ after Hb₄.
    remember Hc₃ as H; clear HeqH.
    unfold carry_i in H; simpl in H.
    rewrite Hsj₁ in H.
    remember (pred dj₁) as di₃ eqn:Hdi₃ .
    rename H into Ha₃; move Ha₃ before Hc₃.
    move Hc₄ after Ha₄.
    destruct dj₁.
     simpl in Hdi₃; subst di₃; clear Hfa₁ Hfb₁.
     remember Hsj₁ as H; clear HeqH.
     apply fst_same_iff in H; simpl in H.
     destruct H as (_, Hbc₃).
     rewrite Ha₃ in Hbc₃; symmetry in Hbc₃.
     rewrite Nat.add_0_r in Ha₃, Hbc₃.
     remember Hbc₃ as H; clear HeqH.
     unfold rm_add_i in H; simpl in H.
     assert (0 < di₁) as HH by (eapply Nat.lt_lt_0; eauto ).
     apply Hn₁ in HH; rewrite Nat.add_0_r in HH.
     rewrite Ha₃ in HH; apply negb_sym in HH; simpl in HH.
     rename HH into Hb₃.
     assert (0 < di₅) as HH by (eapply Nat.lt_lt_0; eauto ).
     apply Hn₅ in HH; rewrite Nat.add_0_r in HH.
     rewrite Hb₃ in HH; apply negb_sym in HH; simpl in HH.
     rename HH into Hd₃.
     rewrite Hb₃, Hd₃, xorb_true_l in H.
     apply negb_true_iff in H.
     replace (S i) with (S i + 0) in H by apply Nat.add_0_r.
     symmetry in Hs₅.
     assert (0 < di₅) as HH by (eapply Nat.lt_lt_0; eauto ).
     erewrite carry_before_relay in H; try eassumption.
     discriminate H.

     simpl in Hdi₃.
     subst dj₁.
     rewrite Nat.add_succ_r in Hfa₁.
     rewrite Hfa₁ in Ha₃; [ discriminate Ha₃ | idtac ].
     apply Nat.lt_0_succ.

   clear Hk₁.
   apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
   rename Ha₄ into Hd₄.
   pose proof (Hs₁ di₄) as Ha₄; move Ha₄ after Hb₄.
   rewrite Hb₄ in Ha₄; simpl in Ha₄.
   rewrite Ha₄, xorb_false_l in Hd₄; simpl in Hd₄.
   move Hd₄ after Hs₄.
   remember Hc₃ as H; clear HeqH.
   unfold carry_i in H; simpl in H.
   rewrite Hsj₁ in H.
   destruct dj₁.
    rewrite Nat.add_0_r in H.
    rename H into Has.
    pose proof (Hs₁ 0) as Hbs; rewrite Nat.add_0_r, Has in Hbs.
    apply negb_sym in Hbs; simpl in Hbs.
    assert (0 < di₅) as Hcs by (eapply Nat.lt_lt_0; eauto ).
    apply Hn₅ in Hcs; rewrite Nat.add_0_r in Hcs.
    rewrite Hbs in Hcs; apply negb_sym in Hcs; simpl in Hcs.
    remember Hsj₁ as H; clear HeqH; simpl in H.
    apply fst_same_iff in H; simpl in H.
    destruct H as (_, H).
    rewrite Nat.add_0_r, Has in H; symmetry in H.
    unfold rm_add_i in H; simpl in H.
    rewrite Hbs, Hcs, xorb_true_l in H.
    apply negb_true_iff in H.
    replace (S i) with (S i + 0) in H by apply Nat.add_0_r.
    symmetry in Hs₅.
    assert (0 < di₅) as HH by (eapply Nat.lt_lt_0; eauto ).
    erewrite carry_before_relay in H; try eassumption.
    discriminate H.

    simpl in H.
    rewrite Nat.add_succ_r in Hfa₁; simpl in Hfa₁.
    rewrite Hfa₁ in H; [ discriminate H | idtac ].
    apply Nat.lt_0_succ.

  subst di₅.
  rewrite Hs₄ in Ht₅; discriminate Ht₅.

(*2*)
(* technique : couper-coller les hypothèses dans un fichier toto et faire :
      LC_ALL=C sort -t: -k 2 toto | less
   pour essayer de comprendre où se trouve les trucs *)
  destruct dj₁.
   simpl in Hbk₁; rewrite Nat.add_0_r in Hbk₁.
   rewrite Nat.add_0_r in Hss₁; simpl in Hss₁.
   rewrite <- Hs₅ in Hss₁.
   injection Hss₁; intros; subst di₅.
   destruct dk₂.
    destruct dk₁.
     do 2 rewrite Nat.add_0_r in Hcl₁.
     simpl in Hs₄, Hcl₁.
     rewrite Hcl₁ in Hs₄; discriminate Hs₄.

     rewrite Hbk₁ in Hj₅; [ idtac | apply Nat.lt_0_succ ].
     discriminate Hj₅.

    destruct dk₁.
     do 2 rewrite Nat.add_0_r in Hcl₁; simpl in Hs₄, Hcl₁.
     rewrite Hcl₁ in Hs₄; discriminate Hs₄.

     rewrite Nat.add_0_r in Hck₁; simpl in Hck₁, Ht₅.
     rewrite Hck₁ in Ht₅; [ idtac | apply Nat.lt_0_succ ].
     discriminate Ht₅.

   remember Hc₃ as H; clear HeqH.
   unfold carry_i in H; simpl in H.
   rewrite Hsj₁ in H.
   rename H into Ha₃; move Ha₃ before Hc₃.
   rewrite <- Nat.add_succ_r in Ha₃.
   rewrite Hfa₁ in Ha₃; [ idtac | apply Nat.lt_0_succ ].
   discriminate Ha₃.

 injection Hsj₂; clear Hsj₂; intros; subst di₄; clear Hj₅.
 apply fst_same_sym_iff in Hs₅; simpl in Hs₅.
 destruct dj₁, dk₁.
  pose proof (Hs₅ 0) as H.
  do 2 rewrite Nat.add_0_r in Hbl₁, Hcl₁; simpl in Hbl₁, Hcl₁.
  rewrite Hbl₁, Hcl₁ in H; discriminate H.

  pose proof (Hs₅ (S dk₁ + 0)) as H.
  rewrite Nat.add_assoc in H.
  rewrite Nat.add_0_r in Hbl₁, Hcl₁; simpl in Hbl₁, Hcl₁.
  rewrite Hbl₁, Hcl₁ in H; discriminate H.

  pose proof (Hs₅ (S dj₁ + 0)) as H.
  rewrite Nat.add_assoc in H.
  rewrite Nat.add_0_r in Hbl₁, Hcl₁; simpl in Hbl₁, Hcl₁.
  rewrite Hbl₁, Hcl₁ in H; discriminate H.

  pose proof (Hs₅ (S dj₁ + S dk₁ + 0)) as H.
  do 2 rewrite Nat.add_assoc in H.
  simpl in Hbl₁, Hcl₁.
  rewrite Hbl₁, Hcl₁ in H; discriminate H.
Qed.
*)

(*
Theorem case_3 : ∀ a b c i,
  carry_i (a + (b + c)%rm) 0 i = true
  → carry_i ((a + b)%rm + c) 0 i = true
  → carry_i a (b + c) i = true
  → carry_i (a + b) c i = false
  → carry_i b c i = false
  → carry_i a b i = false
  → False.
Proof.
intros a b c i Hc₁ Hc₂ Hc₃ Hc₄ Hc₅ Hc₆.
remember Hc₁ as H; clear HeqH.
apply carry_0_r_true_if in H; unfold id in H; simpl in H.
rename H into Hj₁; move Hj₁ before Hc₁.
remember Hc₂ as H; clear HeqH.
apply carry_0_r_true_if in H; unfold id in H; simpl in H.
rename H into Hj₂; move Hj₂ before Hc₂.
remember Hj₁ as H; clear HeqH; move H before Hj₁.
apply forall_add_succ_r in H; unfold id in H.
apply rm_add_inf_true_if in H; simpl in H.
destruct H as (dj₁, (Hta₁, (Htb₁, (Hfa₁, (Hfb₁, Hsj₁))))).
remember Hj₂ as H; clear HeqH; move H before Hj₂.
apply forall_add_succ_r in H; unfold id in H.
apply rm_add_inf_true_if in H; simpl in H.
destruct H as (dj₂, (Hta₂, (Htb₂, (Hfa₂, (Hfb₂, Hsj₂))))).
rewrite <- Nat.add_succ_r in Hfa₁.
rewrite <- Nat.add_succ_r in Hfb₁.
rewrite <- Nat.add_succ_r in Hfa₂.
rewrite <- Nat.add_succ_r in Hfb₂.
remember Htb₁ as H; clear HeqH.
apply forall_add_succ_l in H.
unfold id in H.
apply rm_add_inf_true_if in H.
move H before Hsj₁.
destruct H as (dk₁, (Hbl₁, (Hcl₁, (Hbk₁, (Hck₁, Hss₁))))).
remember Hta₂ as H; clear HeqH.
apply forall_add_succ_l in H; unfold id in H.
apply rm_add_inf_true_if in H.
move H before Hsj₂.
destruct H as (dk₂, (Hbl₂, (Hcl₂, (Hbk₂, (Hck₂, Hss₂))))).
unfold carry_i in Hc₄; simpl in Hc₄.
remember (fst_same (a + b) c (S i)) as s₄ eqn:Hs₄ .
destruct s₄ as [di₄| ]; [ idtac | discriminate Hc₄ ].
injection Hsj₂; clear Hsj₂; intros; subst di₄.
unfold carry_i in Hc₅; simpl in Hc₅.
remember (fst_same b c (S i)) as s₅ eqn:Hs₅ .
destruct s₅ as [di₅| ]; [ idtac | discriminate Hc₅ ].
apply fst_same_sym_iff in Hs₅; simpl in Hs₅.
destruct Hs₅ as (Hn₅, Hs₅); rewrite Hc₅ in Hs₅; symmetry in Hs₅.
unfold carry_i in Hc₆; simpl in Hc₆.
remember (fst_same a b (S i)) as s₆ eqn:Hs₆ .
destruct s₆ as [di₆| ]; [ idtac | discriminate Hc₆ ].
apply fst_same_sym_iff in Hs₆; simpl in Hs₆.
destruct Hs₆ as (Hn₆, Hs₆); rewrite Hc₆ in Hs₆; symmetry in Hs₆.
destruct dj₁.
 rewrite Nat.add_0_r in Hta₁.
 rewrite Hta₁ in Hc₆; discriminate Hc₆.

 destruct dj₂.
  rewrite Nat.add_0_r in Htb₂.
  rewrite Htb₂ in Hs₅; discriminate Hs₅.

  remember Hc₃ as H; clear HeqH.
  unfold carry_i in H; simpl in H.
  rewrite Hsj₁ in H.
  rewrite <- Nat.add_succ_r in H.
  rewrite Hfa₁ in H; [ idtac | apply Nat.lt_0_succ ].
  discriminate H.
Qed.
*)

(*
Theorem case_4 : ∀ a b c i,
  carry_i (a + (b + c)%rm) 0 i = true
  → carry_i ((a + b)%rm + c) 0 i = true
  → carry_i a (b + c) i = false
  → carry_i (a + b) c i = false
  → carry_i b c i = true
  → carry_i a b i = false
  → False.
Proof.
intros a b c i Hc₁ Hc₂ Hc₃ Hc₄ Hc₅ Hc₆.
remember Hc₁ as H; clear HeqH.
apply carry_0_r_true_if in H; unfold id in H; simpl in H.
rename H into Hj₁; move Hj₁ before Hc₁.
remember Hc₂ as H; clear HeqH.
apply carry_0_r_true_if in H; unfold id in H; simpl in H.
rename H into Hj₂; move Hj₂ before Hc₂.
remember Hj₁ as H; clear HeqH; move H before Hj₁.
apply forall_add_succ_r in H; unfold id in H.
apply rm_add_inf_true_if in H; simpl in H.
destruct H as (dj₁, (Hta₁, (Htb₁, (Hfa₁, (Hfb₁, Hsj₁))))).
remember Hj₂ as H; clear HeqH; move H before Hj₂.
apply forall_add_succ_r in H; unfold id in H.
apply rm_add_inf_true_if in H; simpl in H.
destruct H as (dj₂, (Hta₂, (Htb₂, (Hfa₂, (Hfb₂, Hsj₂))))).
rewrite <- Nat.add_succ_r in Hfa₁.
rewrite <- Nat.add_succ_r in Hfb₁.
rewrite <- Nat.add_succ_r in Hfa₂.
rewrite <- Nat.add_succ_r in Hfb₂.
remember Htb₁ as H; clear HeqH.
apply forall_add_succ_l in H; unfold id in H.
apply rm_add_inf_true_if in H.
move H before Hsj₁.
destruct H as (dk₁, (Hbl₁, (Hcl₁, (Hbk₁, (Hck₁, Hss₁))))).
remember Hta₂ as H; clear HeqH.
apply forall_add_succ_l in H; unfold id in H.
apply rm_add_inf_true_if in H.
move H before Hsj₂.
destruct H as (dk₂, (Hbl₂, (Hcl₂, (Hbk₂, (Hck₂, Hss₂))))).
unfold carry_i in Hc₄; simpl in Hc₄.
remember (fst_same (a + b) c (S i)) as s₄ eqn:Hs₄ .
destruct s₄ as [di₄| ]; [ idtac | discriminate Hc₄ ].
injection Hsj₂; clear Hsj₂; intros; subst di₄.
apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
destruct Hs₄ as (Hn₄, Hs₄); rewrite Hc₄ in Hs₄; symmetry in Hs₄.
unfold carry_i in Hc₃; simpl in Hc₃.
rewrite Hsj₁ in Hc₃; simpl in Hc₃.
unfold carry_i in Hc₆; simpl in Hc₆.
remember (fst_same a b (S i)) as s₆ eqn:Hs₆ .
destruct s₆ as [di₆| ]; [ idtac | discriminate Hc₆ ].
symmetry in Hs₆; rename Hs₆ into Hss₆.
remember Hss₆ as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hn₆, Ht₆); rewrite Hc₆ in Ht₆; symmetry in Ht₆.
destruct dj₁.
 rewrite Nat.add_0_r in Hta₁.
 rewrite Hta₁ in Hc₆; discriminate Hc₆.

 destruct dj₂.
  replace (S i) with (S i + 0) in Hs₄ by apply Nat.add_0_r; simpl in Hs₄.
  rewrite Nat.add_0_r in Htb₂.
  rewrite Htb₂ in Hs₄; discriminate Hs₄.

  simpl in *.
  unfold carry_i in Hc₅; simpl in Hc₅.
  remember (fst_same b c (S i)) as s₅ eqn:Hs₅ .
  destruct s₅ as [di₅| ]; [ idtac | clear Hc₅ ].
   symmetry in Hs₅.
   remember Hs₅ as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn₅, Ht₅).
   rewrite Hc₅ in Ht₅; symmetry in Ht₅.
   destruct (lt_eq_lt_dec di₅ di₆) as [[H₁| H₁]| H₁].
    remember H₁ as H; clear HeqH.
    apply Hn₆ in H; simpl in H.
    rewrite Hc₅ in H; simpl in H.
    rename H into Ha₅.
    destruct (lt_eq_lt_dec dj₂ di₅) as [[H₂| H₂]| H₂].
     assert (dj₂ < di₆) as H by (eapply lt_trans; eauto ).
     apply Hn₆ in H; simpl in H.
     rename H into Ha₂.
     remember Hc₄ as H; clear HeqH.
     unfold rm_add_i in H; simpl in H.
     rewrite Ha₂, negb_xorb_diag, xorb_true_l in H.
     apply negb_false_iff in H.
     rewrite <- Nat.add_succ_l in H.
     assert (dj₂ < di₆) as HH by (eapply lt_trans; eauto ).
     erewrite carry_before_relay in H; try eassumption.
     discriminate H.

     subst dj₂.
     rewrite Hs₄ in Ht₅; discriminate Ht₅.

     remember H₂ as H; clear HeqH.
     apply Hn₄ in H; simpl in H.
     unfold rm_add_i in H; simpl in H.
     rewrite Ha₅, Hc₅, Ht₅ in H.
     rewrite xorb_true_l in H.
     apply negb_false_iff in H.
     rewrite <- Nat.add_succ_l in H.
     erewrite carry_before_relay in H; try eassumption.
     discriminate H.

    subst di₆.
    rewrite Ht₆ in Hc₅; discriminate Hc₅.

    pose proof (Hfb₁ (Nat.lt_0_succ dj₁)) as Hd₄.
    rewrite Nat.add_succ_r in Hd₄; simpl in Hd₄.
    clear Hfb₂ Hfa₂ Hfa₁ Hfb₁.
    destruct (lt_eq_lt_dec dj₂ di₆) as [[H₂| H₂]| H₂].
     remember H₂ as H; clear HeqH.
     apply Hn₆ in H; simpl in H.
     rename H into Hab.
     remember Hc₄ as H; clear HeqH.
     unfold rm_add_i in H; simpl in H.
     rewrite Hab, negb_xorb_diag in H.
     apply negb_false_iff in H.
     rewrite <- Nat.add_succ_l in H.
     erewrite carry_before_relay in H; try eassumption.
     discriminate H.

     subst di₆.
     remember H₁ as H; clear HeqH.
     apply Hn₅ in H; rewrite Ht₆, Hs₄ in H; discriminate H.

     destruct (lt_eq_lt_dec dj₁ di₆) as [[H₃| H₃]| H₃].
      pose proof (Hta₁ (di₆ - S dj₁)) as H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_shuffle0, Nat.add_sub in H.
      rewrite Hc₆ in H; discriminate H.

      subst dj₁.
      destruct (lt_eq_lt_dec (S di₆) di₅) as [[H₃| H₃]| H₃].
       pose proof (Htb₁ 0) as H; rewrite Nat.add_0_r in H.
       unfold rm_add_i in H; simpl in H.
       rewrite Hn₅ in H; [ idtac | assumption ].
       rewrite negb_xorb_diag, xorb_true_l in H.
       apply negb_true_iff in H.
       rewrite <- Nat.add_succ_l in H.
       erewrite carry_before_relay in H; try eassumption.
       discriminate H.

       subst di₅; clear H₁.
       pose proof (Hn₅ di₆ (Nat.lt_succ_diag_r di₆)) as H.
       rewrite Ht₆ in H; apply negb_sym in H; simpl in H.
       rename H into Hd₆.
       pose proof (Hn₄ di₆ H₂) as H; rewrite Hd₆ in H; simpl in H.
       unfold rm_add_i in H; simpl in H.
       rewrite Hc₃, Ht₆, xorb_false_l in H.
       unfold carry_i in H; simpl in H.
       remember (fst_same a b (S (S (i + di₆)))) as s₆ eqn:Hs₆ .
       destruct s₆ as [di₇| ]; [ idtac | discriminate H ].
       rewrite <- Nat.add_assoc, <- Nat.add_succ_r in H.
       do 2 rewrite <- Nat.add_succ_l in H.
       rewrite Nat.add_succ_l in H.
       rewrite Nat.add_assoc in H.
       rewrite Hta₁ in H; discriminate H.

       apply Nat.succ_le_mono in H₃.
       apply Nat.nlt_ge in H₃.
       contradiction.

      remember Hsj₁ as H; clear HeqH.
      apply fst_same_iff in H; simpl in H.
      destruct H as (Hn₁, Hs₁).
      pose proof (Hn₁ di₆ H₃) as H.
      rewrite Hc₆ in H; apply negb_sym in H; simpl in H.
      unfold rm_add_i in H; simpl in H.
      rewrite Hn₅ in H; [ idtac | assumption ].
      rewrite negb_xorb_diag, xorb_true_l in H.
      apply negb_true_iff in H.
      rewrite <- Nat.add_succ_l in H.
      erewrite carry_before_relay in H; try eassumption.
      discriminate H.

   apply fst_same_sym_iff in Hs₅.
   pose proof (Htb₁ 0) as H; rewrite Nat.add_0_r in H.
   unfold rm_add_i in H; simpl in H.
   simpl in Hs₅.
   rewrite Hs₅, negb_xorb_diag, xorb_true_l in H.
   apply negb_true_iff in H.
   unfold carry_i in H; simpl in H.
   remember (fst_same b c (S (S (i + S dj₁)))) as s₁ eqn:Hs₁ .
   destruct s₁ as [di₁| ]; [ idtac | discriminate H ].
   apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
   destruct Hs₁ as (Hn₁, Hs₁).
   rewrite <- Nat.add_succ_r in Hs₁.
   rewrite <- Nat.add_assoc in Hs₁.
   rewrite Hs₅ in Hs₁.
   apply neq_negb in Hs₁; [ contradiction | reflexivity ].
Qed.
*)

(*
Theorem carry_non_assoc_if : ∀ a b c i,
  carry_i (a + (b + c)%rm) 0 i = true
  → carry_i ((a + b)%rm + c) 0 i = false
  → ∃ j,
    0 < j ∧
    (∀ dj, a .[ S (i + j + dj)] = true) ∧
    (∀ dj, rm_add_i b c (S (i + j + dj)) = true) ∧
    (a .[ S (i + pred j)] = false) ∧
    (rm_add_i b c (S (i + pred j)) = false) ∧
    fst_same a (b + c) (S i) = Some (pred j).
Proof.
intros a b c i Hc₁ Hc₂.
remember Hc₁ as H; clear HeqH.
apply carry_0_r_true_if in H; unfold id in H; simpl in H.
rename H into Hj₁; move Hj₁ before Hc₁.
remember Hj₁ as H; clear HeqH; move H before Hj₁.
apply forall_add_succ_r in H; unfold id in H.
apply rm_add_inf_true_if in H; simpl in H.
destruct H as (dj₁, (Hta₁, (Htb₁, (Hfa₁, (Hfb₁, Hsj₁))))).
remember Htb₁ as H; clear HeqH.
apply forall_add_succ_l in H; unfold id in H.
apply rm_add_inf_true_if in H.
move H before Hsj₁.
destruct H as (dk₁, (Hbl₁, (Hcl₁, (Hbk₁, (Hck₁, Hss₁))))).
remember Hc₂ as H; clear HeqH.
unfold carry_i in H; simpl in H.
remember (fst_same ((a + b)%rm + c) 0 (S i)) as s₂ eqn:Hs₂ .
destruct s₂ as [di₂| ]; [ idtac | discriminate H ].
symmetry in Hs₂.
apply fst_same_iff in Hs₂; simpl in Hs₂.
destruct Hs₂ as (Hn₂, Ht₂); clear H.
destruct dj₁.
 exfalso.
 rewrite <- Nat.add_succ_r in Hfa₁.
 rewrite <- Nat.add_succ_r in Hfb₁.
 remember Hsj₁ as H; clear HeqH.
 apply fst_same_iff in H; simpl in H.
 destruct H as (_, Ha₁).
 rewrite Nat.add_0_r in Hta₁.
 rewrite Hta₁, Nat.add_0_r in Ha₁.
 symmetry in Ha₁.
 destruct dk₁.
  remember Ht₂ as H; clear HeqH.
  unfold rm_add_i in H; simpl in H.
  unfold rm_add_i in H; simpl in H.
  rewrite Nat.add_0_r in Hbl₁, Hcl₁.
  rewrite Nat.add_0_r in Hbl₁, Hcl₁.
  simpl in Hbl₁, Hcl₁.
  rewrite Hta₁, Hbl₁, Hcl₁ in H.
  rewrite xorb_true_l, xorb_true_r, xorb_false_l in H.
  rewrite <- negb_xorb_l in H.
  apply negb_false_iff in H.
  unfold carry_i in H; simpl in H.
  remember (fst_same a b (S (S (i + di₂)))) as s₁ eqn:Hs₁ .
  remember (fst_same (a + b) c (S (S (i + di₂)))) as s₃ eqn:Hs₃ .
  destruct s₁ as [di₁| ].
   apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
   destruct Hs₁ as (Hn₁, _).
   rewrite <- Nat.add_assoc, <- Nat.add_succ_r, Hta₁, xorb_true_l in H.
   destruct s₃ as [di₃| ]; [ idtac | discriminate H ].
   apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
   destruct Hs₃ as (Hn₃, Hs₃).
   apply negb_true_iff in H.
   rewrite Hs₃ in H.
   rewrite <- Nat.add_assoc, <- Nat.add_succ_r in H.
   rewrite Hcl₁ in H; discriminate H.

   destruct s₃ as [di₃| ]; [ idtac | discriminate H ].
   apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
   destruct Hs₃ as (Hn₃, Hs₃); rewrite Hs₃ in H.
   rewrite <- Nat.add_assoc, <- Nat.add_succ_r in H.
   rewrite Hcl₁ in H; discriminate H.

  destruct dk₁.
   try rewrite Nat.add_0_r in *; try rewrite Nat.add_1_r in *; simpl in *.
   try rewrite Nat.add_0_r in *; try rewrite Nat.add_1_r in *; simpl in *.
   remember Hc₂ as H; clear HeqH.
   unfold carry_i in H; simpl in H.
   remember (fst_same ((a + b)%rm + c) 0 (S i)) as s₃ eqn:Hs₃ .
   destruct s₃ as [di₃| ]; [ idtac | discriminate H ].
   unfold rm_add_i in H; simpl in H.
   destruct di₃.
    rewrite Nat.add_0_r in H; simpl in H.
    unfold rm_add_i in H; simpl in H.
    pose proof (Hta₁ 0) as Ha₂; rewrite Nat.add_0_r in Ha₂.
    rewrite Ha₂, Hbk₁ in H; [ idtac | apply Nat.lt_0_1 ].
    rewrite Hck₁ in H; [ idtac | apply Nat.lt_0_1 ].
    rewrite xorb_true_l, xorb_false_r in H.
    rewrite <- negb_xorb_l in H.
    apply negb_false_iff in H.
    unfold carry_i in H; simpl in H.
    remember (fst_same a b (S (S i))) as s₄ eqn:Hs₄ .
    remember (fst_same (a + b) c (S (S i))) as s₈ eqn:Hs₈ .
    destruct s₄ as [di₄| ].
     rewrite <- Nat.add_succ_r in H.
     rewrite Hta₁, xorb_true_l in H.
     destruct s₈ as [di₈| ]; [ idtac | discriminate H ].
     apply negb_true_iff in H.
     unfold rm_add_i in H; simpl in H.
     unfold carry_i in H; simpl in H.
     remember (fst_same a b (S (S (S (i + di₈))))) as s₉ eqn:Hs₉ .
     destruct s₉ as [di₉| ].
      rewrite Hbl₁ in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hta₁ in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Nat.add_assoc in H.
      rewrite Hta₁ in H.
      discriminate H.

      rewrite Hbl₁ in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hta₁ in H; discriminate H.

     destruct s₈ as [di₈| ]; [ idtac | discriminate H ].
     rewrite xorb_true_l in H.
     apply negb_true_iff in H.
     unfold rm_add_i in H; simpl in H.
     rewrite Hbl₁ in H.
     unfold carry_i in H; simpl in H.
     remember (fst_same a b (S (S (S (i + di₈))))) as s₉ eqn:Hs₉ .
     destruct s₉ as [di₉| ].
      rewrite <- Nat.add_succ_r in H.
      rewrite Hta₁ in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Nat.add_assoc in H.
      rewrite Hta₁ in H.
      discriminate H.

      rewrite <- Nat.add_succ_r in H.
      rewrite Hta₁ in H.
      discriminate H.

    unfold rm_add_i in H; simpl in H.
    rewrite Nat.add_succ_r in H.
    rewrite Hcl₁, xorb_true_r in H.
    rewrite <- negb_xorb_l in H.
    apply negb_false_iff in H.
    unfold carry_i in H; simpl in H.
    rewrite Hbl₁, xorb_true_r in H.
    rewrite <- Nat.add_succ_r in H at 1.
    rewrite Hta₁, xorb_false_l in H.
    remember (fst_same a b (S (S (S (i + di₃))))) as s₄ eqn:Hs₄ .
    remember (fst_same (a + b) c (S (S (S (i + di₃))))) as s₈ eqn:Hs₈ .
    destruct s₄ as [di₄| ].
     rewrite <- Nat.add_succ_r in H.
     rewrite <- Nat.add_succ_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite Hta₁, xorb_true_l in H.
     destruct s₈ as [di₈| ]; [ idtac | discriminate H ].
     apply negb_true_iff in H.
     unfold rm_add_i in H; simpl in H.
     unfold carry_i in H; simpl in H.
     remember (fst_same a b (S (S (S (S (i + di₃ + di₈)))))) as s₉ eqn:Hs₉ .
     rewrite <- Nat.add_succ_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite Hbl₁ in H.
     rewrite <- Nat.add_succ_r in H.
     rewrite Hta₁ in H.
     rewrite xorb_nilpotent, xorb_false_l in H.
     destruct s₉ as [di₉| ]; [ idtac | discriminate H ].
     do 2 rewrite <- Nat.add_assoc in H.
     do 3 rewrite <- Nat.add_succ_r in H.
     rewrite Hta₁ in H; discriminate H.

     rewrite xorb_true_l in H.
     apply negb_true_iff in H.
     destruct s₈ as [di₈| ]; [ idtac | discriminate H ].
     unfold rm_add_i in H; simpl in H.
     rewrite <- Nat.add_assoc in H.
     rewrite <- Nat.add_succ_r in H.
     rewrite Hbl₁ in H.
     rewrite <- Nat.add_succ_r in H.
     rewrite Hta₁ in H.
     rewrite xorb_nilpotent, xorb_false_l in H.
     unfold carry_i in H; simpl in H.
     remember (fst_same a b (S (S (i + S (S (di₃ + di₈)))))) as s₉ eqn:Hs₉ .
     destruct s₉ as [di₉| ]; [ idtac | discriminate H ].
     rewrite <- Nat.add_succ_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite Hta₁ in H; discriminate H.

   simpl in *; try rewrite Nat.add_0_r in *.
   clear Hfa₁ Hfb₁.
   pose proof (Hbk₁ (Nat.lt_0_succ (S dk₁))) as Hb₁; clear Hbk₁.
   pose proof (Hck₁ (Nat.lt_0_succ (S dk₁))) as Hd₁; clear Hck₁.
   rename Htb₁ into Ht₁.
   remember Hss₁ as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hnk, Hsk).
   destruct (lt_eq_lt_dec di₂ (S dk₁)) as [[H₁| H₁]| H₁].
    remember Ht₂ as H; clear HeqH.
    unfold rm_add_i in H; simpl in H.
    unfold rm_add_i in H; simpl in H.
    rewrite Hta₁, xorb_true_l in H.
    do 3 rewrite <- negb_xorb_l in H.
    apply negb_false_iff in H.
    rewrite xorb_shuffle0, xorb_comm in H.
    do 2 rewrite <- xorb_assoc in H.
    rewrite Hnk in H; [ idtac | assumption ].
    rewrite <- negb_xorb_r, xorb_nilpotent, xorb_true_l in H.
    rewrite <- negb_xorb_l in H.
    apply negb_true_iff in H.
    unfold carry_i in H.
    remember (fst_same a b (S (S (i + di₂)))) as s₃ eqn:Hs₃ .
    remember (fst_same (a + b) c (S (S (i + di₂)))) as s₄ eqn:Hs₄ .
    simpl in H.
    destruct s₃ as [di₃| ].
     rewrite <- Nat.add_succ_r, <- Nat.add_assoc in H.
     rewrite Hta₁, xorb_true_l in H.
     apply negb_false_iff in H.
     destruct s₄ as [di₄| ].
      apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
      destruct Hs₄ as (Hn₄, Hs₄).
      rewrite Hs₄ in H.
      rename H into Hd₄.
      rewrite Hd₄ in Hs₄.
      destruct (lt_eq_lt_dec (di₂ + di₄) dk₁) as [[H₂| H₂]| H₂].
       remember H₂ as H; clear HeqH.
       apply Nat.succ_lt_mono in H.
       apply Hnk in H.
       rewrite Nat.add_succ_r, Nat.add_assoc in H.
       rewrite Hd₄ in H; simpl in H.
       rename H into Hb₄.
       remember Hs₄ as H; clear HeqH.
       unfold rm_add_i in H; simpl in H.
       rewrite Hb₄, <- Nat.add_assoc, <- Nat.add_succ_r in H.
       rewrite Hta₁ in H.
       rewrite xorb_true_l in H.
       apply negb_true_iff in H.
       rewrite Nat.add_succ_r, Nat.add_assoc in H.
       unfold carry_i in H; simpl in H.
       remember (fst_same a b (S (S (S (i + di₂ + di₄))))) as s₅ eqn:Hs₅ .
       destruct s₅ as [di₅| ]; [ idtac | discriminate H ].
       do 2 rewrite <- Nat.add_assoc in H.
       do 2 rewrite <- Nat.add_succ_r in H.
       rewrite Hta₁ in H; discriminate H.

       rewrite <- Nat.add_assoc, <- Nat.add_succ_r, H₂ in Hd₄.
       rewrite Hd₁ in Hd₄; discriminate Hd₄.

       remember H₂ as H; clear HeqH.
       apply lt_add_sub_lt_l in H; [ idtac | assumption ].
       apply Hn₄ in H; simpl in H.
       apply Nat.succ_le_mono in H₁.
       rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
       rewrite Nat.add_shuffle0, Nat.add_sub in H.
       rewrite <- Nat.add_succ_r, Hd₁ in H; simpl in H.
       unfold rm_add_i in H; simpl in H.
       rewrite Hta₁, Hb₁, xorb_true_l in H.
       apply negb_true_iff in H.
       unfold carry_i in H; simpl in H.
       remember (fst_same a b (S (S (i + S dk₁)))) as s₅ eqn:Hs₅ .
       destruct s₅ as [di₅| ]; [ idtac | discriminate H ].
       rewrite <- Nat.add_assoc, <- Nat.add_succ_r in H.
       rewrite Hta₁ in H; discriminate H.

      clear H.
      apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
      pose proof (Hs₄ (dk₁ - di₂)) as H.
      apply Nat.succ_le_mono in H₁.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_shuffle0, Nat.add_sub in H.
      rewrite <- Nat.add_succ_r, Hd₁ in H; simpl in H.
      unfold rm_add_i in H; simpl in H.
      rewrite Hta₁, Hb₁, xorb_true_l in H.
      apply negb_true_iff in H.
      unfold carry_i in H; simpl in H.
      remember (fst_same a b (S (S (i + S dk₁)))) as s₅ eqn:Hs₅ .
      destruct s₅ as [di₅| ]; [ idtac | discriminate H ].
      rewrite <- Nat.add_assoc, <- Nat.add_succ_r in H.
      rewrite Hta₁ in H; discriminate H.

     clear H.
     apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
     pose proof (Hs₃ (S dk₁ - di₂)) as H.
     apply Nat.lt_le_incl in H₁.
     rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
     rewrite Nat.add_shuffle0, Nat.add_sub in H.
     rewrite <- Nat.add_succ_r, Hta₁ in H; simpl in H.
     pose proof (Hbl₁ 0) as HH; simpl in HH.
     rewrite Nat.add_0_r in HH; rewrite HH in H.
     discriminate H.

    remember Ht₂ as H; clear HeqH.
    unfold rm_add_i in H; simpl in H.
    unfold rm_add_i in H; simpl in H.
    rewrite <- H₁ in Hb₁, Hd₁.
    rewrite Hta₁, Hb₁, Hd₁ in H.
    rewrite xorb_true_l, xorb_false_r in H.
    rewrite <- negb_xorb_l in H.
    apply negb_false_iff in H.
    unfold carry_i in H.
    remember (fst_same a b (S (S (i + di₂)))) as s₃ eqn:Hs₃ .
    remember (fst_same (a + b) c (S (S (i + di₂)))) as s₄ eqn:Hs₄ .
    simpl in H.
    destruct s₃ as [di₃| ].
     rewrite <- Nat.add_succ_r, <- Nat.add_assoc in H.
     rewrite Hta₁, xorb_true_l in H.
     apply negb_true_iff in H.
     destruct s₄ as [di₄| ]; [ idtac | discriminate H ].
     unfold rm_add_i in H; simpl in H.
     rewrite <- Nat.add_assoc, <- Nat.add_succ_r in H.
     rewrite Hta₁ in H.
     rewrite <- H₁ in Hbl₁, Hcl₁.
     do 2 rewrite <- Nat.add_succ_l in H.
     rewrite Nat.add_succ_l, Nat.add_assoc in H.
     rewrite Hbl₁ in H.
     rewrite xorb_nilpotent, xorb_false_l in H.
     unfold carry_i in H; simpl in H.
     remember (fst_same a b (S (S (i + S di₂ + di₄)))) as s₅ eqn:Hs₅ .
     destruct s₅ as [di₅| ]; [ idtac | discriminate H ].
     do 2 rewrite <- Nat.add_assoc in H.
     rewrite <- Nat.add_succ_r, Hta₁ in H.
     discriminate H.

     apply fst_same_sym_iff in Hs₃; simpl in Hs₃; clear H.
     pose proof (Hs₃ 0) as H; rewrite Nat.add_0_r in H.
     rewrite <- Nat.add_succ_r, Hta₁ in H.
     pose proof (Hbl₁ 0) as HH; rewrite Nat.add_0_r in HH.
     rewrite H₁, HH in H.
     discriminate H.

    remember Ht₂ as H; clear HeqH.
    unfold rm_add_i in H; simpl in H.
    unfold rm_add_i in H; simpl in H.
    rewrite Hta₁, xorb_true_l in H.
    pose proof (Hbl₁ (di₂ - S (S dk₁))) as HH.
    rewrite Nat.add_sub_assoc in HH; [ idtac | assumption ].
    rewrite Nat.add_shuffle0, Nat.add_sub in HH.
    rename HH into Hb₂.
    rewrite Hb₂, xorb_false_l in H.
    pose proof (Hcl₁ (di₂ - S (S dk₁))) as HH.
    rewrite Nat.add_sub_assoc in HH; [ idtac | assumption ].
    rewrite Nat.add_shuffle0, Nat.add_sub in HH.
    rename HH into Hd₂.
    rewrite Hd₂, xorb_true_r in H.
    rewrite <- negb_xorb_l in H.
    apply negb_false_iff in H.
    unfold carry_i in H; simpl in H.
    remember (fst_same a b (S (S (i + di₂)))) as s₃ eqn:Hs₃ .
    remember (fst_same (a + b) c (S (S (i + di₂)))) as s₄ eqn:Hs₄ .
    destruct s₃ as [di₃| ].
     rewrite <- Nat.add_succ_r, <- Nat.add_assoc in H.
     rewrite Hta₁, xorb_true_l in H.
     apply negb_true_iff in H.
     destruct s₄ as [di₄| ]; [ idtac | discriminate H ].
     unfold rm_add_i in H; simpl in H.
     rewrite <- Nat.add_assoc, <- Nat.add_succ_r in H.
     rewrite Hta₁ in H.
     assert (S dk₁ < di₂ + di₄) as HHH.
      eapply lt_le_trans; eauto .
      apply Nat.le_sub_le_add_l.
      rewrite Nat.sub_diag.
      apply Nat.le_0_l.

      pose proof (Hbl₁ (di₂ + di₄ - S dk₁)) as HH.
      apply Nat.lt_le_incl in HHH.
      rewrite Nat.add_succ_r in HH.
      rewrite Nat.add_sub_assoc in HH; [ idtac | assumption ].
      rewrite <- Nat.add_succ_l in HH.
      rewrite Nat.add_shuffle0, Nat.add_sub in HH.
      rewrite <- Nat.add_succ_r in HH.
      simpl in HH.
      rewrite HH in H.
      rewrite xorb_true_l, xorb_false_l in H.
      rename HH into Hb₃.
      unfold carry_i in H; simpl in H.
      remember (fst_same a b (S (S (i + S (di₂ + di₄))))) as s₅ eqn:Hs₅ .
      destruct s₅ as [di₅| ]; [ idtac | discriminate H ].
      rewrite <- Nat.add_assoc, <- Nat.add_succ_r in H.
      rewrite Hta₁ in H; discriminate H.

     apply fst_same_sym_iff in Hs₃; simpl in Hs₃; clear H.
     pose proof (Hs₃ 0) as H; rewrite Nat.add_0_r in H.
     rewrite <- Nat.add_succ_r, Hta₁ in H.
     apply negb_sym in H; simpl in H.
     pose proof (Hbl₁ (di₂ - S dk₁)) as HH.
     apply Nat.lt_le_incl in H₁.
     rewrite Nat.add_succ_r in HH.
     rewrite Nat.add_sub_assoc in HH; [ idtac | assumption ].
     rewrite <- Nat.add_succ_l in HH.
     rewrite Nat.add_shuffle0, Nat.add_sub in HH.
     rewrite <- Nat.add_succ_r in HH.
     simpl in HH.
     rewrite HH in H; discriminate H.
 exists (S dj₁).
 split; auto; [ apply Nat.lt_0_succ | idtac ].
 split; auto.
 split; auto.
 split; auto; [ apply Hfa₁, Nat.lt_0_succ | split; auto ].
 apply Hfb₁, Nat.lt_0_succ.
Qed.
*)

(*
Theorem case_5 : ∀ a b c i,
  carry_i (a + (b + c)%rm) 0 i = true
  → carry_i ((a + b)%rm + c) 0 i = false
  → carry_i a (b + c) i = true
  → False.
Proof.
intros a b c i Hc₁ Hc₂ Hc₃.
remember Hc₁ as H; clear HeqH.
apply carry_non_assoc_if in H; [ idtac | assumption ].
destruct H as (dj₁, (Hdj₁, (Hta₁, (Htb₁, (Hfa₁, (Hfb₁, Hsj₁)))))).
destruct dj₁; [ revert Hdj₁; apply Nat.nlt_0_r | clear Hdj₁ ].
simpl in Hfa₁, Hfb₁, Hsj₁.
remember Hc₃ as H; clear HeqH.
unfold carry_i in H; simpl in H.
rewrite Hsj₁ in H; simpl in H.
rewrite Hfa₁ in H; discriminate H.
Qed.
*)

(*
Theorem case_6 : ∀ a b c i,
  carry_i (a + (b + c)%rm) 0 i = false
  → carry_i ((a + b)%rm + c) 0 i = true
  → carry_i (a + b) c i = true
  → False.
Proof.
intros a b c i Hc₁ Hc₂ Hc₄.
apply case_5 with (c := a) (b := b) (a := c) (i := i).
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
Qed.
*)

(*
Theorem case_7 : ∀ a b c i,
  carry_i (a + (b + c)%rm) 0 i = true
  → carry_i ((a + b)%rm + c) 0 i = false
  → carry_i a (b + c) i = false
  → carry_i (a + b) c i = true
  → carry_i b c i = true
  → carry_i a b i = false
  → False.
Proof.
intros a b c i Hc₁ Hc₂ Hc₃ Hc₄ Hc₅ Hc₆.
Abort.
remember Hc₁ as H; clear HeqH.
apply carry_non_assoc_if in H; [ idtac | assumption ].
destruct H as (dj₁, (Hdj₁, (Hta₁, (Htb₁, (Hfa₁, (Hfb₁, Hsj₁)))))).
destruct dj₁; [ revert Hdj₁; apply Nat.nlt_0_r | clear Hdj₁ ].
simpl in Hfa₁, Hfb₁, Hsj₁.
remember Hc₆ as H; clear HeqH.
unfold carry_i in H; simpl in H.
remember (fst_same a b (S i)) as s₁ eqn:Hs₁ .
destruct s₁ as [di₁| ]; [ idtac | discriminate H ].
rename H into Ha₁.
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct Hs₁ as (Hn₁, Hs₁); rewrite Ha₁ in Hs₁; symmetry in Hs₁.
destruct di₁.
 clear Hn₁; rewrite Nat.add_0_r in Hs₁, Ha₁.
 remember Hc₅ as H; clear HeqH.
 unfold carry_i in H; simpl in H.
 remember (fst_same b c (S i)) as s₂ eqn:Hs₂ .
 apply fst_same_sym_iff in Hs₂; simpl in Hs₂.
 destruct s₂ as [di₂| ].
  destruct Hs₂ as (Hn₂, Hs₂).
  rewrite H in Hs₂; symmetry in Hs₂.
  rename H into Hb₂.
  destruct di₂.
   rewrite Nat.add_0_r, Hs₁ in Hb₂; discriminate Hb₂.

   pose proof (Hn₂ 0 (Nat.lt_0_succ di₂)) as H.
   rewrite Nat.add_0_r, Hs₁ in H.
   apply negb_sym in H; simpl in H.
   rename H into Hd₁.
   destruct dj₁.
    clear Hfa₁.
    rewrite Nat.add_0_r in Hfb₁.
    destruct di₂.
     rewrite Nat.add_1_r in Hs₂, Hb₂; simpl in Hs₂, Hb₂.
     clear Hn₂.
     remember Hc₂ as H; clear HeqH.
     unfold carry_i in H; simpl in H.
     remember (fst_same ((a + b)%rm + c) 0 (S i)) as s₃ eqn:Hs₃ .
     destruct s₃ as [di₃| ]; [ idtac | discriminate H ].
     apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
     destruct Hs₃ as (Hn₃, Hs₃).
     destruct di₃.
      clear Hn₃; rewrite Nat.add_0_r in Hs₃, H.
      unfold rm_add_i in H; simpl in H.
      rewrite Hd₁, xorb_true_r in H.
      rewrite <- negb_xorb_l in H.
      apply negb_false_iff in H.
      unfold rm_add_i in H; simpl in H.
      rewrite Ha₁, Hs₁, xorb_false_l in H.
      unfold carry_i in H; simpl in H.
      remember (fst_same a b (S (S i))) as s₄ eqn:Hs₄ .
      remember (fst_same (a + b) c (S (S i))) as s₅ eqn:Hs₅ .
      rewrite Nat.add_1_r in Hta₁, Htb₁; simpl in Hta₁, Htb₁.
      destruct s₄ as [di₄| ].
       rewrite Hta₁ in H.
       destruct s₅ as [di₅| ]; [ idtac | discriminate H ].
       rewrite xorb_true_l in H.
       apply negb_true_iff in H.
       unfold rm_add_i in H; simpl in H.
       rewrite Hta₁, xorb_true_l in H.
       rewrite <- negb_xorb_l in H.
       apply negb_false_iff in H.
       rewrite carry_when_inf_1 with (i := S i) in H.
        rewrite xorb_true_r in H.
        apply negb_true_iff in H.
        rename H into Hb₅.
        remember Hs₄ as H; clear HeqH.
        apply fst_same_sym_iff in H; simpl in H.
        destruct H as (Hnn, Hsn).
        rewrite Hta₁ in Hsn; symmetry in Hsn.
        destruct (lt_eq_lt_dec di₄ di₅) as [[H₁| H₁]| H₁].
         remember Hs₅ as H; clear HeqH.
         apply fst_same_sym_iff in H; simpl in H.
         destruct H as (Hn₅, Ht₅).
         pose proof (Hn₅ di₄ H₁) as H.
         rename H into Hab.
         assert (0 < di₅) as H by (eapply Nat.lt_lt_0; eauto ).
         apply Hn₅ in H.
         rewrite Nat.add_0_r in H.
         rewrite Hs₂ in H; simpl in H.
         unfold rm_add_i in H; simpl in H.
         pose proof (Hta₁ 0) as HH; rewrite Nat.add_0_r in HH.
         rewrite HH, Hb₂ in H.
         rewrite xorb_nilpotent, xorb_false_l in H.
         rewrite carry_when_inf_1 with (i := S i) in H.
          discriminate H.

          intros di; rewrite Nat.add_succ_l; apply Hta₁.

          apply Nat.le_succ_diag_r.

         subst di₄.
         rewrite Hb₅ in Hsn; discriminate Hsn.

         remember H₁ as H; clear HeqH.
         apply Hnn in H.
         rename H into Hab.
         assert (0 < di₄) as H by (eapply Nat.lt_lt_0; eauto ).
         apply Hnn in H; simpl in H.
         rewrite Nat.add_0_r in H.
         rewrite Hb₂ in H; simpl in H.
         pose proof (Hta₁ 0) as HH; rewrite Nat.add_0_r in HH.
         rewrite HH in H; discriminate H.

        intros di; rewrite Nat.add_succ_l; apply Hta₁.

        rewrite <- Nat.add_succ_r, <- Nat.add_succ_l.
        apply Nat.le_sub_le_add_l.
        rewrite Nat.sub_diag.
        apply Nat.le_0_l.

       apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
       clear H; pose proof (Hs₄ 0) as H.
       rewrite Hta₁, Nat.add_0_r, Hb₂ in H.
       discriminate H.

      clear H.
bbb.

            i  i+1  -   i₃
        b   .   0   .   .
0
        a   .   0   1   1   1   1   1 ...
0
       b+c  .   0   1   1   1   1   1 ...

       a+b  .   1   .   .
1
        c   .   1   .   .
1                +1
        b   .   0   .   .

      pose proof (Hn₃ 0 (Nat.lt_0_succ di₃)) as H.
      rewrite Nat.add_0_r in H.
      unfold rm_add_i in H; simpl in H.
      rewrite Hd₁, xorb_true_r in H.
      rewrite <- negb_xorb_l in H.
      apply negb_true_iff in H.
      unfold rm_add_i in H; simpl in H.
      rewrite Ha₁, Hs₁, xorb_false_l in H.
      rewrite Nat.add_1_r in Hta₁.
      rewrite carry_when_inf_1 with (i := S i) in H; auto.
      rewrite xorb_true_l in H.
      apply negb_false_iff in H.
      rewrite Nat.add_1_r in Htb₁.
      unfold carry_i in H; simpl in H.
      remember (fst_same (a + b) c (S (S i))) as s₄ eqn:Hs₄ .
      apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
      destruct s₄ as [di₄| ].
       destruct Hs₄ as (Hn₄, Hs₄); rewrite H in Hs₄; symmetry in Hs₄.
       unfold rm_add_i in H; simpl in H.
       rewrite <- Nat.add_succ_l, Hta₁, xorb_true_l in H.
       rewrite <- negb_xorb_l in H.
       apply negb_true_iff in H.
       erewrite carry_when_inf_1 in H; try eassumption.
        rewrite xorb_true_r in H.
        apply negb_false_iff in H.
        rename H into Hb₄; simpl in Hb₄.
bbb.

            i  i+1  -   i₃
        b   .   0   1   .
0
        a   .   0   1   1   1   1   1 ...
0
       b+c  .   0   1   1   1   1   1 ...

       a+b  .   1   .   .
1
        c   .   1   1   .
1                +1
        b   .   0   1   .



            i  i+1  -   j₁   -
        b   .   0   .   .   .
             -0
        a   .   0   .   0   1   1   1 ...
0            -0 ≠   ≠
       b+c  .   1   .   0   1   1   1 ...

       a+b  .   .   .   .   .
             -1
        c   .   1   .   .   .
             -1  -1
        b   .   0   .   .   .



            i  i+1  -   j₁   -
        b   .   .   .   .   .
             -0
        a   .   .   .   0   1   1   1 ...
0            -0 ≠   ≠
       b+c  .   .   .   0   1   1   1 ...

       a+b  .   .   .   .   .
             -1
        c   .   .   .   .   .
             -1
        b   .   .   .   .   .
*)

Theorem carry_comm_l : ∀ a b c i,
  carry_i (a + b) c i = carry_i (b + a) c i.
Proof.
intros a b c i.
rewrite carry_compat_r with (a := (b + a)%rm); [ reflexivity | idtac ].
apply rm_add_i_comm.
Qed.

Theorem carry_assoc_l : ∀ a b c d i,
  carry_i ((a + b) + c)%rm d i = carry_i (c + (b + a))%rm d i.
Proof.
intros a b c d i.
apply carry_compat_r.
intros j; simpl.
rewrite rm_add_i_comm.
apply rm_add_i_compat_r, rm_add_i_comm.
Qed.

(*
Theorem case_8 : ∀ a b c i,
  carry_i (a + (b + c)%rm) 0 i = false
  → carry_i ((a + b)%rm + c) 0 i = true
  → carry_i a (b + c) i = true
  → carry_i (a + b) c i = false
  → carry_i b c i = true
  → carry_i a b i = false
  → False.
Proof.
intros a b c i Hc₁ Hc₂ Hc₃ Hc₄ Hc₅ Hc₆.
rewrite <- carry_assoc_l in Hc₁.
rewrite carry_assoc_l in Hc₂.
remember Hc₂ as H; clear HeqH.
apply carry_non_assoc_if in H; [ idtac | assumption ].
destruct H as (dj₁, (Hdj₁, (Hta₁, (Htb₁, (Hfa₁, (Hfb₁, Hsj₁)))))).
destruct dj₁; [ revert Hdj₁; apply Nat.nlt_0_r | clear Hdj₁ ].
simpl in Hfa₁, Hfb₁, Hsj₁.
remember Hc₄ as H; clear HeqH.
unfold carry_i in H; simpl in H.
rewrite fst_same_comm in Hsj₁.
remember (fst_same (a + b) c (S i)) as s₁ eqn:Hs₁ .
destruct s₁ as [di₁| ]; [ idtac | discriminate H ].
rewrite rm_add_i_comm in Hfb₁.
Abort.
bbb.
*)

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
  → carry_i (a + b)%rm 0 i = false.
Proof.
intros a₀ b₀ a b i Ha₀ Hb₀.
unfold carry_i; simpl.
remember (fst_same (a + b) 0 (S i)) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁); assumption.

 apply forall_add_succ_l in Hs₁.
 apply rm_add_inf_if in Hs₁.
 destruct Hs₁ as (j, (Hij, (Haj, Hbj))).
 rewrite Ha₀ in Haj; simpl in Haj.
 apply forall_add_succ_r in Haj.
 apply rm_add_inf_if in Haj.
 destruct Haj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem carry_sum_3_norm_assoc_l : ∀ c₀ a b c i,
  c = (c₀ + 0)%rm
  → carry_i ((a + b) + c)%rm 0 i = false.
Proof.
intros c₀ a b c i Hc₀.
unfold carry_i; simpl.
remember (fst_same ((a + b) + c)%rm 0 (S i)) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁); assumption.

 apply forall_add_succ_l in Hs₁.
 apply rm_add_inf_if in Hs₁.
 destruct Hs₁ as (j, (Hij, (Haj, Hbj))).
 rewrite Hc₀ in Hbj; simpl in Hbj.
 apply forall_add_succ_r in Hbj.
 apply rm_add_inf_if in Hbj.
 destruct Hbj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem carry_sum_3_norm_assoc_r : ∀ a₀ a b c i,
  a = (a₀ + 0)%rm
  → carry_i (a + (b + c))%rm 0 i = false.
Proof.
intros a₀ a b c i Ha₀.
unfold carry_i; simpl.
remember (fst_same (a + (b + c)%rm) 0 (S i)) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁); assumption.

 apply forall_add_succ_l in Hs₁.
 apply rm_add_inf_if in Hs₁.
 destruct Hs₁ as (j, (Hij, (Haj, Hbj))).
 rewrite Ha₀ in Haj; simpl in Haj.
 apply forall_add_succ_r in Haj.
 apply rm_add_inf_if in Haj.
 destruct Haj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem sum_11_1_sum_0_0 : ∀ a b i,
  a.[i] = true
  → b.[i] = true
  → rm_add_i a b i = true
  → a.[S i] = false
  → rm_add_i a b (S i) = false.
Proof.
intros b c i Hb₅ Ht₅ Hbd Ht₆.
apply not_true_iff_false; intros H.
unfold rm_add_i in H; simpl in H.
rewrite Ht₆, xorb_false_l in H.
rename H into Hcc.
remember Hbd as H; clear HeqH.
unfold rm_add_i in H; simpl in H.
rewrite Hb₅, Ht₅, xorb_true_l, xorb_false_l in H.
rename H into Hbc.
remember (S i) as x.
replace x with (x + 0) in Hcc by apply Nat.add_0_r.
unfold carry_i in Hbc.
rewrite <- Heqx in Hbc.
remember (fst_same b c x) as s₁ eqn:Hs₁ .
destruct s₁ as [di₁| ].
 symmetry in Hs₁.
 destruct di₁.
  rewrite Nat.add_0_r, Ht₆ in Hbc; discriminate Hbc.

  assert (0 < S di₁) as H by apply Nat.lt_0_succ.
  erewrite carry_before_relay in Hcc; try eassumption.
  rewrite Nat.add_0_r, xorb_true_r in Hcc.
  apply negb_true_iff in Hcc.
  apply fst_same_iff in Hs₁; simpl in Hs₁.
  destruct Hs₁ as (Hn₁, _).
  apply Hn₁ in H; rewrite Nat.add_0_r in H.
  rewrite Ht₆, Hcc in H; discriminate H.

 symmetry in Hs₁.
 remember Hs₁ as H; clear HeqH.
 apply fst_same_inf_after with (di := 1) in H.
 rewrite Nat.add_1_r in H.
 rename H into Hs₂.
 apply fst_same_iff in Hs₁.
 pose proof (Hs₁ 0) as H; apply negb_sym in H.
 rewrite H, Nat.add_0_r, Ht₆, xorb_true_l in Hcc.
 apply negb_true_iff in Hcc.
 unfold carry_i in Hcc.
 rewrite Hs₂ in Hcc; discriminate Hcc.
Qed.

Theorem case_1 : ∀ a₀ b₀ c₀ a b c i,
  a = (a₀ + 0)%rm
  → b = (b₀ + 0)%rm
  → c = (c₀ + 0)%rm
  → carry_i (a + (b + c)%rm) 0 i = false
  → carry_i ((a + b)%rm + c) 0 i = false
  → carry_i a (b + c) i = true
  → carry_i (a + b) c i = true
  → carry_i b c i = true
  → carry_i a b i = false
  → False.
Proof.
intros a₀ b₀ c₀ a b c i Ha₀ Hb₀ Hc₀ Hc₁ Hc₂ Hc₃ Hc₄ Hc₅ Hc₆.
(*
clear Hb₀ Hc₀ Hc₁ Hc₂ Hc₄.
*)
remember Hc₆ as H; clear HeqH.
unfold carry_i in H; simpl in H.
remember (fst_same a b (S i)) as s₆ eqn:Hs₆ .
destruct s₆ as [di₆| ]; [ idtac | discriminate H ].
remember Hs₆ as HH; clear HeqHH.
apply fst_same_sym_iff in HH; simpl in HH.
destruct HH as (Hn₆, Ht₆).
rewrite H in Ht₆; symmetry in Ht₆.
rename H into Ha₆.
remember Hc₅ as H; clear HeqH.
unfold carry_i in H; simpl in H.
remember (fst_same b c (S i)) as s₅ eqn:Hs₅ .
remember Hs₅ as HH; clear HeqHH.
apply fst_same_sym_iff in HH; simpl in HH.
destruct s₅ as [di₅| ]; [ idtac | clear H ].
 destruct HH as (Hn₅, Ht₅); rewrite H in Ht₅.
 symmetry in Ht₅; rename H into Hb₅.
 destruct (lt_eq_lt_dec di₅ di₆) as [[H₁| H₁]| H₁].
  remember (di₆ - S di₅) as n eqn:Hn .
  apply nat_sub_add_r in Hn; [ idtac | assumption ].
  rewrite Nat.add_comm in Hn; simpl in Hn.
  subst di₆; clear H₁.
(**)
  revert di₅ Hs₅ Hb₅ Hn₅ Ht₅ Hs₆ Ha₆ Hn₆ Ht₆.
(*
  clear Hs₆.
  revert di₅ Hs₅ Hb₅ Hn₅ Ht₅ Ha₆ Hn₆ Ht₆.
*)
  induction n; intros.
   simpl in *.
   remember Hc₃ as H; clear HeqH.
   unfold carry_i in H; simpl in H.
   remember (fst_same a (b + c) (S i)) as s₃ eqn:Hs₃ .
   apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
   destruct s₃ as [di₃| ]; [ idtac | clear H ].
    destruct Hs₃ as (Hn₃, Ht₃).
    rewrite H in Ht₃; symmetry in Ht₃.
    rename H into Ha₃.
    destruct (lt_eq_lt_dec di₃ di₅) as [[H₂| H₂]| H₂].
     remember Ht₃ as H; clear HeqH.
     unfold rm_add_i in H; simpl in H.
     rewrite <- Nat.add_succ_l in H.
     symmetry in Hs₅.
     erewrite carry_before_relay in H; try eassumption; simpl in H.
     apply Hn₅ in H₂.
     rewrite H₂, negb_xorb_diag in H.
     discriminate H.

     subst di₃.
     pose proof (Hn₆ di₅ (Nat.lt_succ_diag_r di₅)) as H.
     rewrite Ha₃, Hb₅ in H.
     discriminate H.

     remember H₂ as H; clear HeqH.
     apply Hn₃ in H.
     rewrite Hn₆ in H; [ idtac | apply Nat.lt_succ_diag_r ].
     rewrite Hb₅ in H.
     apply negb_sym in H; simpl in H.
     rename H into Hbd.
     destruct (lt_eq_lt_dec di₃ (S di₅)) as [[H₃| H₃]| H₃].
      apply Nat.nle_gt in H₃; contradiction.

      subst di₃; clear H₂.
      rewrite Nat.add_succ_r in Ht₃, Ht₆.
      rewrite sum_11_1_sum_0_0 in Ht₃; try assumption.
      discriminate Ht₃.

      remember H₃ as H; clear HeqH.
      apply Hn₃ in H; simpl in H.
      rewrite Ha₆ in H.
      apply negb_sym in H; simpl in H.
      rewrite Nat.add_succ_r in H, Ht₆.
      rewrite sum_11_1_sum_0_0 in H; try assumption.
      discriminate H.

    pose proof (Hn₆ di₅ (Nat.lt_succ_diag_r di₅)) as Ha₅.
    rewrite Hb₅ in Ha₅; simpl in Ha₅.
    pose proof (Hs₃ di₅) as H.
    rewrite Ha₅ in H.
    apply negb_sym in H; simpl in H.
    rename H into Hbd.
    pose proof (Hs₃ (S di₅)) as H.
    rewrite Ha₆ in H.
    apply negb_sym in H; simpl in H.
    rewrite Nat.add_succ_r in H, Ht₆.
    rewrite sum_11_1_sum_0_0 in H; try assumption.
    discriminate H.
bbb.

            i  i+1  -   i₅  -
        b   .   0   0   1   .
0               ≠+0 ≠+0 ≠+0
        a   .   1   1   0   0
1               ≠   ≠   ≠   ≠   ≠   ≠ ...
       b+c  .   0   0   1   1

       a+b  .   1   1   1   .
1
        c   .   1   1   1   .
1               ≠   ≠    +1
        b   .   0   0   1   .

            i  i+1  -   i₅  .   i₃  -   i₆
        b   .   0   0   1   .   0   .   0
0            +0 ≠+0 ≠+0 ≠+0 ≠+0 ≠+0 ≠+0
        a   .   1   1   0   .   1   .   0
1            +1 ≠+1 ≠+1 ≠+1 ≠+1
       b+c  .   0   0   1   .   1   .   .

       a+b  .   1   1   1   1   1   1   .
1            +1
        c   .   1   1   1   .   .   .   .
1            +1 ≠+1 ≠+1  +1 <--------------- c'est ça qui se propage
        b   .   0   0   1   .   0   .   0

            i  i+1  -   i₅  .   i₁  -   i₃  -   i₆
        b   .   0   0   1   1   1   .   0   .   0
0            +0 ≠+0 ≠+0 ≠+0 ≠+0 ≠+0 ≠+0 ≠+0 ≠+0
        a   .   1   1   0   0   0   .   1   .   0
1            +1 ≠+1 ≠+1 ≠+1 ≠+1 ≠+1 ≠+1
       b+c  .   0   0   1   0   1   .   1   .   .

       a+b  .   1   1   1   1   1   1   1   1   .
1            +1
        c   .   1   1   1   0   1   .   .   .   .
1            +1 ≠+1 ≠+1  +1 ≠+1  +1
        b   .   0   0   1   1   1   .   0   .   0


            i  i+1  -   i₅  .   i₃  -   i₆
        b   .   0   0   1   .   0   .   0
0            +0 ≠+0 ≠+0 ≠+0 ≠+0 ≠+0 ≠+0
        a   .   1   1   0   .   1   .   0
1            +1 ≠+1 ≠+1 ≠+1 ≠+1
       b+c  .   0   0   1   .   1   .   .

       a+b  .   1   1   1   1   1   1   .
1            +1
        c   .   1   1   1   .   .   .   .
1            +1 ≠+1 ≠+1  +1
        b   .   0   0   1   .   0   .   0


            i  i+1  -   i₅  -   i₆
        b   .   .   x   1   .   0
0               ≠+0 ≠+0 ≠+0 ≠+0
        a   .   .  ¬x   0   .   0
1            +1
       b+c  .   0   0   .   .   .

       a+b  .   1   1   1   1   .
1            +1
        c   .   .  ¬x   1   .   .
1            +1 ≠+1 ≠+1
        b   .   .   x   1   .   0

bbb.
*)

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
remember (carry_i (a + (b + c))%rm 0%rm i) as c₁ eqn:Hc₁ .
remember (carry_i (a + b + c)%rm 0%rm i) as c₂ eqn:Hc₂ .
unfold rm_add_i; simpl.
remember (carry_i a (b + c)%rm i) as c₃ eqn:Hc₃ .
remember (carry_i (a + b)%rm c i) as c₄ eqn:Hc₄ .
unfold rm_add_i; simpl.
remember (carry_i b c i) as c₅ eqn:Hc₅ .
remember (carry_i a b i) as c₆ eqn:Hc₆ .
do 8 rewrite xorb_assoc; f_equal; f_equal; symmetry.
rewrite xorb_comm, xorb_assoc; f_equal; symmetry.
rewrite <- xorb_assoc.
symmetry in Hc₁, Hc₂, Hc₃, Hc₄, Hc₅, Hc₆.
move c₂ before c₁; move c₃ before c₂.
move c₄ before c₃; move c₅ before c₄.
move c₆ before c₅.
remember Hc₁ as H; clear HeqH.
erewrite carry_sum_3_norm_assoc_r in H; try eassumption.
move H at top; subst c₁.
remember Hc₂ as H; clear HeqH.
erewrite carry_sum_3_norm_assoc_l in H; try eassumption.
move H at top; subst c₂.
do 2 rewrite xorb_false_r.
destruct c₃, c₄, c₅, c₆; try reflexivity; exfalso.
 eapply case_1; eassumption.

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
set (a₁ := (a + 0)%rm).
set (b₁ := (b + 0)%rm).
set (c₁ := (c + 0)%rm).
rename a into a₀; rename b into b₀; rename c into c₀.
rename a₁ into a; rename b₁ into b; rename c₁ into c.
unfold rm_eq; intros i; simpl.
rewrite rm_add_add2_i; symmetry.
rewrite rm_add_add2_i; symmetry.
unfold rm_add2_i; simpl.
do 2 rewrite xorb_false_r.
remember (carry_i (a + (b + c + 0))%rm 0%rm i) as c₁ eqn:Hc₁ .
remember (carry_i (a + b + 0 + c)%rm 0%rm i) as c₂ eqn:Hc₂ .
rewrite rm_add_add2_i; symmetry.
rewrite rm_add_add2_i; symmetry.
unfold rm_add2_i; simpl.
remember (carry_i a (b + c + 0)%rm i) as c₃ eqn:Hc₃ .
remember (carry_i (a + b + 0)%rm c i) as c₄ eqn:Hc₄ .
rewrite rm_add_add2_i; symmetry.
rewrite rm_add_add2_i; symmetry.
unfold rm_add2_i; simpl.
do 2 rewrite xorb_false_r.
remember (carry_i a₀ 0%rm i) as c₅ eqn:Hc₅ .
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
set (a₁ := (a + 0)%rm).
set (b₁ := (b + 0)%rm).
set (c₁ := (c + 0)%rm).
rename a into a₀; rename b into b₀; rename c into c₀.
rename a₁ into a; rename b₁ into b; rename c₁ into c.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry_i.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
remember (fst_same (a + (b + c + 0)%rm) 0 si) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 remember (fst_same ((a + b + 0)%rm + c) 0 si) as s₂ eqn:Hs₂ .
 apply fst_same_sym_iff in Hs₂; simpl in Hs₂.
 destruct s₂ as [di₂| ].
  Focus 2.
  destruct (bool_dec ((a + b + 0)%rm) .[ si] c .[ si]) as [H₁| H₁].
   apply rm_add_inf_true_eq_if in Hs₂; auto; simpl in Hs₂.
   destruct Hs₂ as (Hab, Hc).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

   apply neq_negb in H₁.
   apply rm_add_inf_true_neq_if in Hs₂; auto; simpl in Hs₂.
   destruct Hs₂ as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

  Focus 2.
  destruct (bool_dec a .[ si] ((b + c + 0)%rm) .[ si]) as [H₁| H₁].
   apply rm_add_inf_true_eq_if in Hs₁; auto; simpl in Hs₁.
   destruct Hs₁ as (Ha, Hbc).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

   apply neq_negb in H₁.
   apply rm_add_inf_true_neq_if in Hs₁; auto; simpl in Hs₁.
   destruct Hs₁ as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

 destruct Hs₁ as (Hn₁, Hs₁); rewrite Hs₁, xorb_false_r.
 destruct Hs₂ as (Hn₂, Hs₂); rewrite Hs₂, xorb_false_r.
 clear di₁ Hn₁ Hs₁ di₂ Hn₂ Hs₂.
 unfold rm_add_i, carry_i; rewrite <- Heqsi; simpl.
 remember (rm_add_i a₀ 0 i) as xai eqn:Hxai .
 remember (rm_add_i (b + c) 0 i) as xbci eqn:Hxbci .
 remember (rm_add_i (a + b) 0 i) as xabi eqn:Hxabi .
 remember (rm_add_i c₀ 0 i) as xci eqn:Hxci .
 remember b .[ i] as xbi eqn:Hxbi ; simpl in Hxbi.
 symmetry in Hxai, Hxbci, Hxabi, Hxci, Hxbi.
 remember (fst_same a (b + c + 0)%rm si) as s₁ eqn:Hs₁ .
 apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
 destruct s₁ as [di₁| ].
  destruct Hs₁ as (Hn₁, Hxbcs).
  remember (rm_add_i a₀ 0 (si + di₁)) as xas eqn:Hxas .
  symmetry in Hxas, Hxbcs.
  remember (fst_same (a + b + 0)%rm c si) as s₂ eqn:Hs₂ .
  apply fst_same_sym_iff in Hs₂; simpl in Hs₂.
  destruct s₂ as [di₂| ].
   destruct Hs₂ as (Hn₂, Hxabs); rewrite Hxabs.
   remember (rm_add_i c₀ 0 (si + di₂)) as xcs eqn:Hxcs .
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
   unfold rm_add_i, carry_i in H.
   rewrite <- Heqsi in H; simpl in H.
   rewrite Hxai, Hxbi in H.
   remember (fst_same a b si) as s₃ eqn:Hs₃ .
   apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
   destruct s₃ as [di₃| ].
    destruct Hs₃ as (Hn₃, Hb₃).
    symmetry in Hb₃.
    apply xorb_move_l_r_1 in H.
    rewrite H in Hb₃; rename H into Ha₃.
    move Ha₃ after Hb₃; move Hn₃ after Hxai.
    remember Hxbci as H; clear HeqH.
    subst b c.
    rewrite rm_add_i_norm_norm in H.
    set (b := (b₀ + 0)%rm) in *.
    set (c := (c₀ + 0)%rm) in *.
    move c before Hx; move b before Hx.
    remember H as Hbci; clear HeqHbci.
    unfold rm_add_i, carry_i in H.
    rewrite <- Heqsi in H; simpl in H.
    rewrite Hxbi, Hxci in H.
    remember (fst_same b c si) as s₄ eqn:Hs₄ .
    apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
    destruct s₄ as [di₄| ].
     destruct Hs₄ as (Hn₄, Hc₄).
     symmetry in Hc₄.
     apply xorb_move_l_r_1 in H.
     rewrite H in Hc₄; rename H into Hb₄.
     move Hb₄ after Hc₄; move Hn₄ after Hxai.
     move Hbci before Habi.
(*1-*)
     destruct (lt_dec di₁ di₃) as [H₁| H₁].
      remember H₁ as H; clear HeqH.
      apply Hn₃ in H.
      rewrite Hxas in H.
      apply negb_sym in H.
      destruct (lt_dec di₃ di₄) as [H₄| H₄].
       remember H₄ as H₄₀; clear HeqH₄₀.
       apply Hn₄ in H₄₀.
       rewrite Hb₃ in H₄₀.
       apply negb_sym in H₄₀.
       assert (di₁ < di₄) as H₂ by omega.
       remember H₂ as H₂₀; clear HeqH₂₀.
       apply Hn₄ in H₂₀.
       destruct (lt_dec di₄ di₂) as [H₃| H₃].
        remember H₃ as H₃₀; clear HeqH₃₀.
        apply Hn₂ in H₃₀.
        rewrite Hc₄ in H₃₀.
        assert (di₁ < di₂) as H₅ by omega.
        remember H₅ as H₅₀; clear HeqH₅₀.
        apply Hn₂ in H₅₀.
        assert (di₃ < di₂) as H₆ by omega.
        remember H₆ as H₆₀; clear HeqH₆₀.
        apply Hn₂ in H₆₀.
        rewrite <- H₂₀ in H₅₀.
        rewrite H₄₀ in H₆₀.
        rewrite negb_involutive in H₆₀.
(*
     assert (xas ⊕ xcs = xai ⊕ xabi ⊕ xci ⊕ xbci) as Hr.
*)
bbb.

     destruct xai, xas, xci, xcs, xabi, xbci; try reflexivity;
      try discriminate Hr.

bbb.
(*1-*)
     destruct xai, xas, xci, xcs, xabi, xbci; try reflexivity; exfalso;
      destruct xbi; simpl in Ha₃, Hb₃, Hb₄, Hc₄.
      destruct di₄.
       clear Hn₄.
       rewrite Nat.add_0_r in Hb₄, Hc₄.
       destruct di₃.
        rewrite Nat.add_0_r, Hb₄ in Hb₃; discriminate Hb₃.

        destruct di₂.
         rewrite Nat.add_0_r, Hc₄ in Hxcs; discriminate Hxcs.

         destruct (lt_dec di₂ di₃) as [H₁| H₁].
          remember H₁ as H; clear HeqH.
          apply Nat.succ_lt_mono, Hn₃ in H.
          unfold rm_add_i, carry_i in Hxabs.
          rewrite <- Nat.add_succ_l in Hxabs.
          remember (S si) as ssi; simpl in Hxabs.
          rewrite xorb_false_r in Hxabs.
bbb.

(*-1*)
   destruct xai, xas, xci, xcs, xabi, xbci; try reflexivity; exfalso;
    destruct xbi, xbs.
    Focus 1.
bbb.
    destruct di₂.
     rewrite Nat.add_0_r in Hxcs.
     apply not_true_iff_false in Hxbci.
     eapply Hxbci, case_1; eassumption.

     (* cf theorem case_1 *)
bbb.
     apply not_true_iff_false in Hxbci.
     apply Hxbci; clear Hxbci.
     apply eq_true_negb_classical; intros Hxbci.
     apply negb_true_iff in Hxbci.
     unfold rm_add_i, carry_i in Hxbci.
     rewrite <- Heqsi in Hxbci; simpl in Hxbci.
     rewrite xorb_false_r in Hxbci.
     unfold rm_add_i, carry_i in Hxbci at 1.
     rewrite <- Heqsi in Hxbci; simpl in Hxbci.
     rewrite Hxbi, Hxci, xorb_true_r in Hxbci.
     rewrite xorb_false_l in Hxbci.
     remember (fst_same b c si) as s₁ eqn:Hs₁ .
     apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
     destruct s₁ as [di₃| ].
      destruct Hs₁ as (Hn₃, Hs₃).
      destruct di₃.
       rewrite Nat.add_0_r, Hxbs, xorb_true_l in Hxbci.
       apply negb_false_iff in Hxbci.
       remember (fst_same (b + c) 0 si) as s₂ eqn:Hs₂ .
       apply fst_same_sym_iff in Hs₂; simpl in Hs₂.
       destruct s₂ as [di₄| ].
        destruct Hs₂ as (Hn₄, Hs₄); rewrite Hs₄ in Hxbci.
        discriminate Hxbci.

        apply rm_add_inf_true_eq_if in Hs₂.
         destruct Hs₂ as (Hs₂, Hs₄); simpl in Hs₂, Hs₄.
         exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

         rewrite Nat.add_0_r in Hs₃; assumption.

       pose proof (Hn₃ 0 (Nat.lt_0_succ di₃)) as H.
       rewrite Nat.add_0_r, Hxbs in H.
       symmetry in H; apply negb_true_iff in H.
       pose proof (Hn₂ 0 (Nat.lt_0_succ di₂)) as H₁.
       rewrite Nat.add_0_r, H in H₁; simpl in H₁.
bbb.
       remember (fst_same (b + c) 0 si) as s₄ eqn:Hs₄ .
       apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
       destruct s₄ as [di₄| ].
        destruct Hs₄ as (Hn₄, Hs₄); rewrite Hs₄, xorb_false_r in Hxbci.
        rewrite Hxbci in Hs₃; symmetry in Hs₃.

bbb.
   destruct di₁.
    clear Hn₁.
    rewrite Nat.add_0_r in Hxas, Hxbcs.
    destruct di₂.
     clear Hn₂.
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
unfold rm_add_i, carry_i.
remember (S i) as si; simpl.
do 2 rewrite xorb_false_r.
remember (fst_same (a + (b + c)%rm) 0 si) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁); rewrite Hs₁, xorb_false_r.
 remember (fst_same ((a + b)%rm + c) 0 si) as s₂ eqn:Hs₂ .
 apply fst_same_sym_iff in Hs₂; simpl in Hs₂.
 destruct s₂ as [di₂| ].
  destruct Hs₂ as (Hn₂, Hs₂); rewrite Hs₂, xorb_false_r.
bbb.
  unfold rm_add_i, carry_i.
  rewrite <- Heqsi; simpl.
  remember (fst_same a (b + c) si) as s₃ eqn:Hs₃ .
  apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
  destruct s₃ as [di₃| ].
   destruct Hs₃ as (Hn₃, Hs₃).
   remember (fst_same (a + b) c si) as s₄ eqn:Hs₄ .
   apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
   destruct s₄ as [di₄| ].
    destruct Hs₄ as (Hn₄, Hs₄); rewrite Hs₄.
    unfold rm_add_i, carry_i; rewrite <- Heqsi.
    do 6 rewrite xorb_assoc; f_equal; f_equal.
    symmetry; rewrite xorb_comm.
    rewrite xorb_assoc; f_equal; symmetry.
(*
bbb.
    destruct (lt_dec di₃ di₄) as [H₁| H₁].
     remember H₁ as H; clear HeqH.
     apply Hn₄ in H.
     unfold rm_add_i, carry_i in Hs₃.
     rewrite <- Nat.add_succ_l in Hs₃.
     remember (S si) as ssi; simpl in Hs₃.
     unfold rm_add_i, carry_i in H.
     rewrite <- Nat.add_succ_l in H.
     rewrite <- Heqssi in H; simpl in H.
     apply xorb_move_l_r_2 in H.
     rewrite <- negb_xorb_l in H.
     rewrite negb_xorb_r in H.
     apply xorb_move_r_l_1 in H.
     rewrite xorb_comm in H.
     apply xorb_move_r_l_1 in Hs₃.
     rewrite xorb_comm in Hs₃.
     rewrite <- xorb_assoc in Hs₃.
     rewrite Hs₃ in H.
bbb.
*)
    remember (fst_same b c si) as s₅ eqn:Hs₅ .
    apply fst_same_sym_iff in Hs₅; simpl in Hs₅.
    destruct s₅ as [di₅| ].
     destruct Hs₅ as (Hn₅, Hs₅).
     remember (fst_same a b si) as s₆ eqn:Hs₆ .
     apply fst_same_sym_iff in Hs₆; simpl in Hs₆.
     destruct s₆ as [di₆| ].
      destruct Hs₆ as (Hn₆, Hs₆).
bbb.

intros a b c.
unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry_i.
remember (fst_same a (b + c) (S i)) as s₁ eqn:Hs₁ .
symmetry in Hs₁.
remember (fst_same (a + b) c (S i)) as s₂ eqn:Hs₂ .
symmetry in Hs₂.
apply fst_same_iff in Hs₁.
apply fst_same_iff in Hs₂.
simpl in Hs₁, Hs₂; simpl.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hs₁n, Hs₁).
 destruct s₂ as [di₂| ].
  destruct Hs₂ as (Hs₂n, Hs₂).
  rewrite Hs₂.
  unfold rm_add, rm_add_i; simpl.
  remember (fst_same a b (S i)) as s₃ eqn:Hs₃ .
  remember (fst_same b c (S i)) as s₄ eqn:Hs₄ .
  symmetry in Hs₃, Hs₄.
  apply fst_same_iff in Hs₃.
  apply fst_same_iff in Hs₄.
  simpl in Hs₃, Hs₄.
  destruct s₃ as [di₃| ].
   destruct Hs₃ as (Hs₃n, Hs₃).
   destruct s₄ as [di₄| ].
    destruct Hs₄ as (Hs₄n, Hs₄).
    do 6 rewrite xorb_assoc.
    do 2 f_equal; symmetry.
    rewrite xorb_comm, xorb_assoc; f_equal.
    symmetry in Hs₂, Hs₄.
    unfold rm_add_i, carry_i in Hs₁, Hs₂; simpl in Hs₁, Hs₂.
    remember (fst_same a b (S (si + di₂)))) as s₅ eqn:Hs₅ .
    remember (fst_same b c (S (si + di₁)))) as s₆ eqn:Hs₆ .
    symmetry in Hs₅, Hs₆.
    apply fst_same_iff in Hs₅.
    apply fst_same_iff in Hs₆.
    simpl in Hs₅, Hs₆.
    destruct s₅ as [di₅| ].
     destruct s₆ as [di₆| ].
      destruct Hs₅ as (Hs₅n, Hs₅).
      destruct Hs₆ as (Hs₆n, Hs₆).
      symmetry in Hs₆.
      move Hs₁ at bottom; move Hs₂ at bottom; move Hs₃ at bottom.
      move Hs₄ at bottom; move Hs₅ at bottom; move Hs₆ at bottom.
      move di₆ before di₁; move di₅ before di₁.
      move di₄ before di₁; move di₃ before di₁.
      move di₂ before di₁.
      move Hs₂n after Hs₆n; move Hs₃n after Hs₆n.
      move Hs₄n after Hs₆n; move Hs₅n after Hs₆n.
      rewrite xorb_comm.
bbb.
      destruct (lt_dec di₃ di₄) as [H₁| H₁].
       remember H₁ as H; clear HeqH.
       apply Hs₄n in H.
       rewrite <- Hs₃ in H.
       Focus 1.
      rewrite Hs₁, Hs₂.
      rewrite <- Hs₄, <- Hs₆.
      rewrite Hs₃, Hs₅.
bbb.
      destruct (lt_dec di₁ di₂) as [H₁| H₁].
       remember H₁ as H; clear HeqH.
       apply Hs₂n in H.
       unfold rm_add_i, carry_i in H; simpl in H.
       remember (fst_same a b (S (si + di₁)))) as s₇ eqn:Hs₇ .
       symmetry in Hs₇.
       apply fst_same_iff in Hs₇.
       destruct s₇ as [di₇| ].
        simpl in Hs₇.
        destruct Hs₇ as (Hs₇n, Hs₇).
bbb.
*)

Theorem neq_xorb : ∀ b b', b ≠ b' → b ⊕ b' = true.
Proof.
intros b b' H.
apply not_false_iff_true.
intros H₁; apply H.
apply xorb_eq; assumption.
Qed.

Close Scope nat_scope.
