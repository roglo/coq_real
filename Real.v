Require Import Utf8 QArith NPeano.

Set Implicit Arguments.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).

Open Scope nat_scope.

(* reals modulo 1 *)
Record real_mod_1 := { rm : nat → bool }.

Definition rm_zero := {| rm i := false |}.

Notation "s .[ i ]" := (rm s i) (at level 1).

Axiom fst_same : real_mod_1 → real_mod_1 → nat → option nat.

Axiom fst_same_iff : ∀ a b i odi,
  fst_same a b i = odi ↔
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
Arguments rm r%rm i%nat.
Arguments carry_i a%rm b%rm i%nat.
Arguments rm_add_i a%rm b%rm i%nat.
Arguments fst_same a%rm b%rm i%nat.
Notation "a + b" := (rm_add a b) : rm_scope.
Notation "a = b" := (rm_eq a b) : rm_scope.
Notation "a ≠ b" := (¬ rm_eq a b) : rm_scope.
Notation "0" := rm_zero : rm_scope.

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

Theorem negb_xorb_diag : ∀ a, negb a ⊕ a = true.
Proof. intros a; destruct a; reflexivity. Qed.

Theorem xorb_shuffle0 : ∀ a b c, a ⊕ b ⊕ c = a ⊕ c ⊕ b.
Proof.
intros a b c.
do 2 rewrite xorb_assoc; f_equal.
apply xorb_comm.
Qed.

Theorem neq_negb : ∀ b b', b ≠ b' → b = negb b'.
Proof.
intros b b' H.
destruct b'; simpl.
 apply not_true_iff_false; auto.

 apply not_false_iff_true; auto.
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

Theorem rm_add_i_compat_r : ∀ a b c j,
  (∀ i, a .[ i] = b .[ i])
  → rm_add_i b c j = rm_add_i a c j.
Proof.
intros a b c j Hab.
unfold rm_add_i, carry_i; simpl.
rewrite Hab; f_equal.
remember (fst_same b c (S j)) as s₁ eqn:Hs₁ .
remember (fst_same a c (S j)) as s₂ eqn:Hs₂ .
symmetry in Hs₁, Hs₂.
apply fst_same_iff in Hs₁.
apply fst_same_iff in Hs₂.
simpl in Hs₁, Hs₂.
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

Theorem rm_norm_eq_compat_r : ∀ a₀ b₀ a b c,
  a = (a₀ + 0)%rm
  → b = (b₀ + 0)%rm
  → (a = b)%rm
  → (a + c = b + c)%rm.
Proof.
intros a₀ b₀ a b c Ha Hb Hab.
assert (∀ i, a .[ i] = b .[ i]) as H.
 intros i.
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

 clear Hab; rename H into Hab.
 unfold rm_eq; simpl.
 intros i; unfold rm_add_i, carry_i.
 remember (S i) as si; simpl.
 do 2 rewrite xorb_false_r.
 symmetry; erewrite rm_add_i_compat_r; [ symmetry | eauto  ].
 f_equal.
 remember (fst_same (a + c) 0 si) as s₁ eqn:Hs₁ .
 remember (fst_same (b + c) 0 si) as s₂ eqn:Hs₂ .
 symmetry in Hs₁, Hs₂.
 apply fst_same_iff in Hs₁.
 apply fst_same_iff in Hs₂.
 simpl in Hs₁, Hs₂.
 destruct s₁ as [di₁| ].
  destruct Hs₁ as (Hn₁, Hs₁).
  destruct s₂ as [di₂| ].
   destruct Hs₂ as (Hn₂, Hs₂).
   rewrite Hs₁, Hs₂; reflexivity.

   pose proof (Hs₂ di₁) as H.
   apply not_false_iff_true in H.
   rewrite <- Hs₁ in H.
   exfalso; apply H.
   apply rm_add_i_compat_r; auto.

  destruct s₂ as [di₂| ]; auto.
  rewrite <- Hs₁ with (dj := di₂).
  apply rm_add_i_compat_r; auto.
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
            assert (j - si < di₂) as H.
             revert Hji H₅; clear; intros.
             omega.

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
           assert (di₂ - S (S dj₅) < di₆) as H by omega.
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
     assert (j - si < di₄) as H by omega.
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

(* associativity; Ambroise Lafont's pen and paper proof *)

Definition opt2nat x :=
  match x with
  | Some y => S y
  | None => 0
  end.

Definition second n a i :=
  {| rm j :=
       match nat_compare j (i + S n) with
       | Eq => true
       | Lt => a.[j]
       | Gt => false
       end |}.
Arguments second n%nat a%rm i%nat.

Theorem fst_same_fin_eq_second : ∀ a b i di,
  fst_same a b (S i) = Some di
  → ∀ n₀ n, n = S di + n₀ →
    fst_same (second n a i) (second n b i) (S i) = Some di.
Proof.
intros a b i di Hdi n₀ n Hn.
apply fst_same_iff.
apply fst_same_iff in Hdi; simpl in Hdi.
destruct Hdi as (Hn₁, Hs₁).
split.
 intros dj Hdj; simpl.
 rewrite Nat.add_succ_r; simpl.
 remember (nat_compare (i + dj) (i + n)) as cmp eqn:Hcmp .
 symmetry in Hcmp.
 subst n.
 destruct cmp.
  apply nat_compare_eq in Hcmp.
  apply Nat.add_cancel_l in Hcmp; subst dj.
  rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hdj.
  apply Nat.lt_add_lt_sub_l in Hdj.
  rewrite Nat.sub_diag in Hdj.
  exfalso; revert Hdj; apply Nat.nlt_0_r.

  apply Hn₁ in Hdj; assumption.

  apply nat_compare_gt in Hcmp.
  apply Nat.add_lt_mono_l in Hcmp.
  eapply Nat.lt_trans in Hdj; [ idtac | eauto  ].
  rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hdj.
  apply Nat.lt_add_lt_sub_l in Hdj.
  rewrite Nat.sub_diag in Hdj.
  exfalso; revert Hdj; apply Nat.nlt_0_r.

 simpl.
 rewrite Nat.add_succ_r; simpl.
 simpl in Hs₁; rewrite Hs₁; reflexivity.
Qed.

Theorem fst_same_inf_second : ∀ a b i,
  fst_same a b (S i) = None
  → ∀ n, fst_same (second n a i) (second n b i) (S i) = Some n.
Proof.
intros a b i Hs n.
apply fst_same_iff in Hs; simpl in Hs.
apply fst_same_iff; simpl.
rewrite Nat.add_succ_r.
split.
 intros dj Hdj.
 apply Nat.add_lt_mono_l with (p := i) in Hdj.
 apply nat_compare_lt in Hdj; rewrite Hdj.
 apply Hs.

 assert (i + n = i + n) as H by reflexivity.
 apply nat_compare_eq_iff in H; rewrite H.
 reflexivity.
Qed.

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

(* [ a'' + b'']_i = [a+b]_i *)
Theorem tr_add_i_eq_rm_add_i : ∀ a b i n,
  (second n (a + b) i).[i] = (a + b)%rm.[i].
Proof.
intros a b i n; simpl.
rewrite nat_compare_add_succ; reflexivity.
Qed.

(* [(a+b)'']_i = [a'' + b'']_i *)
Theorem tr_add_rm_add_distr : ∀ a b i di,
  di = opt2nat (fst_same a b (S i))
  → ∀ n₀ n, n = S di + n₀ →
     (second n (a + b) i).[i] = (second n a i + second n b i)%rm.[i].
Proof.
intros a b i di Hdi n₀ n Hn; simpl.
rewrite nat_compare_add_succ.
unfold rm_add_i, carry_i; simpl.
rewrite nat_compare_add_succ; f_equal.
remember (fst_same a b (S i)) as s eqn:Hs .
symmetry in Hs.
destruct s as [di₁| ].
 subst di; simpl in Hn.
 rewrite <- Nat.add_succ_r in Hn.
 erewrite fst_same_fin_eq_second; try eassumption.
 rewrite Nat.add_succ_r.
 remember (nat_compare (i + di₁) (i + n)) as cmp₁ eqn:Hcmp₁ .
 symmetry in Hcmp₁.
 destruct cmp₁; auto.
  apply nat_compare_eq in Hcmp₁.
  apply Nat.add_cancel_l in Hcmp₁.
  subst di₁.
  rewrite <- Nat.add_succ_r in Hn.
  symmetry in Hn.
  apply Nat.add_sub_eq_l in Hn.
  rewrite Nat.sub_diag in Hn; discriminate Hn.

  apply nat_compare_gt in Hcmp₁.
  apply Nat.add_lt_mono_l in Hcmp₁.
  subst n.
  rewrite <- Nat.add_succ_r in Hcmp₁.
  apply Nat.lt_add_lt_sub_l in Hcmp₁.
  rewrite Nat.sub_diag in Hcmp₁.
  exfalso; revert Hcmp₁; apply Nat.nlt_0_r.

 remember (fst_same (second n a i) (second n b i) (S i)) as s₂ eqn:Hs₂ .
 apply fst_same_sym_iff in Hs₂.
 destruct s₂ as [di₁| ]; [ idtac | reflexivity ].
 rewrite Nat.add_succ_r; simpl.
 simpl in Hdi.
 subst n di; simpl.
 apply fst_same_iff in Hs; simpl in Hs.
 destruct Hs₂ as (Hn₂, Hs₂).
 simpl in Hs₂.
 rewrite Nat.add_succ_r in Hs₂.
 remember (nat_compare (i + di₁) (i + S n₀)) as cmp₁ eqn:Hcmp₁ .
 symmetry in Hcmp₁.
 destruct cmp₁; auto.
  rewrite Hs in Hs₂.
  destruct b .[ S (i + di₁)]; discriminate Hs₂.

  apply nat_compare_gt in Hcmp₁.
  apply Nat.add_lt_mono_l in Hcmp₁.
  apply Hn₂ in Hcmp₁.
  simpl in Hcmp₁.
  rewrite Nat.add_succ_r in Hcmp₁.
  remember (nat_compare (i + S n₀) (i + S n₀)) as cmp eqn:Hcmp .
  symmetry in Hcmp.
  destruct cmp; auto.
  apply nat_compare_lt in Hcmp.
  exfalso; revert Hcmp; apply Nat.lt_irrefl.
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

Theorem fst_same_inf_second2 : ∀ a b i di,
  fst_same a b (S i) = None
  → ∀ n₀ n, n = di + n₀ →
    fst_same (second n a i) (second n b i) (S i + di) = Some n₀.
Proof.
intros a b i di Hs n₀ n Hn.
apply fst_same_iff in Hs; simpl in Hs.
apply fst_same_iff; simpl.
split.
 intros dj Hdj.
 rewrite Nat.add_succ_r.
 assert (i + di + dj < i + n) as H by omega.
 apply nat_compare_lt in H; rewrite H.
 rewrite <- Nat.add_assoc.
 apply Hs.

 rewrite Nat.add_succ_r.
 assert (i + di + n₀ = i + n) as H by omega.
 apply nat_compare_eq_iff in H.
 rewrite H; reflexivity.
Qed.

Theorem fst_same_second : ∀ a b i j di dj dk,
  fst_same a b (S i) = Some dk
  → j = i + di
  → dk = di + dj
  → ∀ n₀ n, n = S dk + n₀ →
    fst_same (second n a i) (second n b i) (S j) = Some dj.
Proof.
intros a b i j di dj dk Hs Hj Hk n₀ n Hn.
apply fst_same_iff; simpl.
rewrite Nat.add_succ_r.
split.
 intros dl Hdl.
 remember (nat_compare (j + dl) (i + n)) as cmp eqn:Hcmp .
 symmetry in Hcmp.
 destruct cmp.
  apply nat_compare_eq in Hcmp.
  exfalso; omega.

  apply nat_compare_lt in Hcmp.
  apply fst_same_iff in Hs; simpl in Hs.
  destruct Hs as (Hnn, Hs).
  assert (di + dl < dk) as H by omega.
  apply Hnn in H.
  rewrite Nat.add_assoc, <- Hj in H.
  assumption.

  apply nat_compare_gt in Hcmp.
  exfalso; omega.

 remember (nat_compare (j + dj) (i + n)) as cmp eqn:Hcmp .
 symmetry in Hcmp.
 destruct cmp; try reflexivity.
 apply fst_same_iff in Hs; simpl in Hs.
 destruct Hs as (Hnn, Hs).
 rewrite Hk, Nat.add_assoc, <- Hj in Hs.
 assumption.
Qed.

Theorem fst_same_add_second : ∀ a b i di dj dk j,
  fst_same a b (S i) = Some dk
  → j = i + di
  → dk = di + dj
  → ∀ n₀ n, n = S dk + n₀ →
    ((a + b)%rm).[j] = ((second n a i + second n b i)%rm).[ j].
Proof.
intros a b i di dj dk j Hs Hj Hk n₀ n Hn; simpl.
unfold rm_add_i, carry_i; simpl.
remember Hs as H; clear HeqH.
rewrite Hk in H.
apply same_fst_same in H; simpl in H.
rewrite <- Hj in H.
rewrite H.
rename H into Hsj.
remember (nat_compare j (i + S n)) as cmp eqn:Hcmp .
symmetry in Hcmp.
destruct cmp.
 apply nat_compare_eq in Hcmp.
 exfalso; omega.

 f_equal.
 rewrite Nat.add_succ_r; simpl.
 apply nat_compare_lt in Hcmp.
 clear Hcmp.
 erewrite fst_same_second; try eassumption.
 remember (nat_compare (j + dj) (i + n)) as cmp eqn:Hcmp .
 symmetry in Hcmp.
 destruct cmp; [ idtac | reflexivity | idtac ].
  apply nat_compare_eq in Hcmp.
  exfalso; omega.

  apply nat_compare_gt in Hcmp.
  exfalso; omega.

 apply nat_compare_gt in Hcmp.
 exfalso; omega.
Qed.

Theorem fst_same_second_add : ∀ a b i j di n,
  fst_same (second (n + di) a i) b j = fst_same (second n a (i + di)) b j.
Proof.
intros a b i j di n.
apply fst_same_iff; simpl.
remember (fst_same (second n a (i + di)) b j) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 split.
  intros dj Hdj.
  apply Hs₁ in Hdj.
  rewrite <- Nat.add_succ_l, Nat.add_assoc, Nat.add_shuffle0.
  assumption.

  rewrite <- Nat.add_succ_l, Nat.add_assoc, Nat.add_shuffle0.
  destruct Hs₁; assumption.

 intros dj.
 rewrite <- Nat.add_succ_l, Nat.add_assoc, Nat.add_shuffle0.
 apply Hs₁.
Qed.

Theorem second_add_add : ∀ a n i di,
  (second (n + di) a i = second n a (i + di))%rm.
Proof.
intros a n i di.
unfold rm_eq; intros j; simpl.
unfold rm_add_i, carry_i; simpl.
rewrite <- Nat.add_succ_l, Nat.add_assoc, Nat.add_shuffle0.
rewrite fst_same_second_add.
reflexivity.
Qed.

Theorem fst_same_before : ∀ a b i dk dl di₄,
  fst_same a b (S i) = Some dk
  → dl < dk
  → fst_same a b (S (S (i + dl))) = Some di₄
  → di₄ = dk - S dl.
Proof.
intros a b i dk dl di₄ Hsk Hdl Hs₄.
destruct (lt_dec di₄ (dk - S dl)) as [H₂| H₂].
 assert (di₄ + S dl < dk) as H by omega.
 apply fst_same_iff in Hsk; simpl in Hsk.
 destruct Hsk as (Hnk, Hsk).
 apply Hnk in H.
 apply fst_same_iff in Hs₄; simpl in Hs₄.
 destruct Hs₄ as (Hn₄, Hs₄).
 rewrite Nat.add_assoc, Nat.add_shuffle0 in H.
 rewrite Nat.add_succ_r in H.
 simpl in H.
 rewrite Hs₄ in H.
 destruct b .[ S (S (i + dl + di₄))]; discriminate H.

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

Theorem same_fst_same_add_second : ∀ a b c i di dj dk,
  fst_same (a + b) c (S i) = Some di
  → opt2nat (fst_same a b (S i + S di)) = dj
  → fst_same a b (S i) = Some dk
  → dk ≤ di + dj
  → ∀ n₀ n, n = S (S (S di + dj)) + n₀ →
    fst_same (second n a i + second n b i) (second n c i) (S i) = Some di.
Proof.
intros a b c i di dj dk Hsi Hsj Hsk Hdk n₀ n Hns.
apply fst_same_iff; simpl.
rewrite Nat.add_succ_r.
apply fst_same_iff in Hsi; simpl in Hsi.
destruct Hsi as (Hni, Hsi).
split.
 intros dl Hdl.
 remember Hdl as H; clear HeqH.
 apply Hni in H; simpl in H.
 unfold rm_add_i, carry_i in H; simpl in H.
 unfold rm_add_i, carry_i; simpl.
 rewrite Nat.add_succ_r.
 assert (i + dl < i + n) as Hcmp by omega.
 apply nat_compare_lt in Hcmp; rewrite Hcmp; clear Hcmp.
 remember (fst_same a b (S (S (i + dl)))) as s₄ eqn:Hs₄ .
 symmetry in Hs₄.
 destruct s₄ as [di₄| ].
  rewrite <- H; clear H; f_equal.
  destruct (lt_dec dl dk) as [H₁| H₁].
   erewrite fst_same_second with (dj := dk - S dl) (n₀ := n - S dk).
    remember (i + n) as ipn eqn:Hin .
    symmetry in Hin.
    destruct ipn; [ exfalso; omega | idtac ].
    remember Hs₄ as H; clear HeqH.
    apply fst_same_before with (dk := dk) in H; auto.
    rewrite <- H.
    assert (i + dl + di₄ < ipn) as Hcmp by omega.
    apply nat_compare_lt in Hcmp.
    rewrite Hcmp; reflexivity.

    eassumption.

    rewrite <- Nat.add_succ_r; reflexivity.

    omega.

    omega.

   clear H₁.
   destruct (le_dec (S dl + S di₄) n) as [H₂| H₂].
    replace n with (n - S dl + S dl) at 1 by omega.
    rewrite fst_same_second_add.
    replace n with (n - S dl + S dl) at 2 by omega.
    rewrite fst_same_comm, fst_same_second_add, fst_same_comm.
    rewrite Nat.add_succ_r.
    remember (n - (S dl + S di₄)) as n₁.
    rewrite fst_same_fin_eq_second with (n₀ := n₁) (di := di₄).
     remember (i + n) as ipn eqn:Hin .
     symmetry in Hin.
     destruct ipn; [ exfalso; omega | idtac ].
     assert (i + dl + di₄ < ipn) as Hcmp by omega.
     apply nat_compare_lt in Hcmp; rewrite Hcmp; reflexivity.

     assumption.

     subst n₁; rewrite Nat.add_sub_assoc; omega.

    apply Nat.nle_gt in H₂.
    apply fst_same_iff in Hs₄; simpl in Hs₄.
    destruct Hs₄ as (Hn₄, Hs₄).
    rename Hsj into Hoj.
    rename dj into oj.
    remember (fst_same a b (S i + S di)) as dj eqn:Hsj .
    symmetry in Hsj.
    destruct dj as [dj| ]; simpl in Hoj; subst oj.
     assert (di + dj - dl < di₄) as H by omega.
     apply Hn₄ in H.
     rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
     rewrite Nat.add_shuffle0, Nat.add_sub in H.
     rewrite Nat.add_assoc in H.
     apply fst_same_iff in Hsj; simpl in Hsj.
     destruct Hsj as (Hnj, Hsj).
     rewrite Nat.add_succ_r in Hsj; simpl in Hsj.
     rewrite Hsj in H.
     destruct b .[ S (S (i + di + dj))]; discriminate H.

     rewrite Nat.add_succ_r in Hsj; simpl in Hsj.
     apply fst_same_iff in Hsj; simpl in Hsj.
     pose proof (Hsj (dl + di₄ - di)) as H.
     rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
     rewrite Nat.add_shuffle0, Nat.add_sub, Nat.add_assoc in H.
     rewrite Hs₄ in H.
     destruct b .[ S (S (i + dl + di₄))]; discriminate H.

  rename H into Hab.
  apply fst_same_iff in Hs₄; simpl in Hs₄.
  rename Hsj into Hoj.
  rename dj into oj.
  remember (fst_same a b (S i + S di)) as dj eqn:Hsj .
  symmetry in Hsj.
  destruct dj as [dj| ]; simpl in Hoj; subst oj.
   pose proof (Hs₄ (di + dj - dl)) as H.
   rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
   rewrite Nat.add_shuffle0, Nat.add_sub in H.
   rewrite Nat.add_assoc in H.
   apply fst_same_iff in Hsj; simpl in Hsj.
   destruct Hsj as (Hnj, Hsj).
   rewrite Nat.add_succ_r in Hsj; simpl in Hsj.
   rewrite Hsj in H.
   destruct b .[ S (S (i + di + dj))]; discriminate H.

   rewrite Nat.add_0_r in Hdk.
   remember (fst_same (second n a i) (second n b i) (S (S (i + dl)))) as s₁.
   rename Heqs₁ into Hs₁.
   apply fst_same_sym_iff in Hs₁.
   destruct s₁ as [di₁| ]; [ idtac | assumption ].
   destruct Hs₁ as (Hn₁, Hs₁); simpl in Hs₁.
   rewrite Nat.add_succ_r in Hs₁.
   remember (i + n) as ipn eqn:Hin .
   symmetry in Hin.
   destruct ipn; [ exfalso; omega | idtac ].
   remember (nat_compare (i + dl + di₁) ipn) as cmp eqn:Hcmp .
   symmetry in Hcmp.
   destruct cmp; [ assumption | idtac | idtac ].
    pose proof (Hs₄ di₁) as H₁.
    rewrite Hs₁ in H₁.
    destruct b .[ S (S (i + dl + di₁))]; discriminate H₁.

    apply nat_compare_gt in Hcmp.
    assert (n - S dl < di₁) as H by omega.
    apply Hn₁ in H.
    simpl in H.
    rewrite Nat.add_succ_r, Hin in H.
    rewrite Nat.add_0_r in Hns.
    rewrite Hns in H.
    rewrite Nat.add_succ_l in H.
    rewrite Nat.sub_succ in H.
    rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
    rewrite Nat.add_shuffle0, Nat.add_sub in H.
    assert (i + (S (S di) + n₀) = ipn) as H₁ by omega.
    apply nat_compare_eq_iff in H₁.
    rewrite H₁ in H; discriminate H.

 rename di into dl.
 remember Hsi as H; clear HeqH.
 unfold rm_add_i, carry_i in H; simpl in H.
 unfold rm_add_i, carry_i; simpl.
 rewrite Nat.add_succ_r.
 assert (i + dl < i + n) as Hcmp by omega.
 apply nat_compare_lt in Hcmp; rewrite Hcmp; clear Hcmp.
 remember (fst_same a b (S (S (i + dl)))) as s₄ eqn:Hs₄ .
 symmetry in Hs₄.
 destruct s₄ as [di₄| ].
  rewrite <- H; clear H; f_equal.
  destruct (lt_dec dl dk) as [H₁| H₁].
   erewrite fst_same_second with (dj := dk - S dl) (n₀ := n - S dk).
    remember (i + n) as ipn eqn:Hin .
    symmetry in Hin.
    destruct ipn; [ exfalso; omega | idtac ].
    remember Hs₄ as H; clear HeqH.
    apply fst_same_before with (dk := dk) in H; auto.
    rewrite <- H.
    assert (i + dl + di₄ < ipn) as Hcmp by omega.
    apply nat_compare_lt in Hcmp.
    rewrite Hcmp; reflexivity.

    eassumption.

    rewrite <- Nat.add_succ_r; reflexivity.

    omega.

    omega.

   clear H₁.
   destruct (le_dec (S dl + S di₄) n) as [H₂| H₂].
    replace n with (n - S dl + S dl) at 1 by omega.
    rewrite fst_same_second_add.
    replace n with (n - S dl + S dl) at 2 by omega.
    rewrite fst_same_comm, fst_same_second_add, fst_same_comm.
    rewrite Nat.add_succ_r.
    remember (n - (S dl + S di₄)) as n₁.
    rewrite fst_same_fin_eq_second with (n₀ := n₁) (di := di₄).
     remember (i + n) as ipn eqn:Hin .
     symmetry in Hin.
     destruct ipn; [ exfalso; omega | idtac ].
     assert (i + dl + di₄ < ipn) as Hcmp by omega.
     apply nat_compare_lt in Hcmp; rewrite Hcmp; reflexivity.

     assumption.

     subst n₁; rewrite Nat.add_sub_assoc; omega.

    apply Nat.nle_gt in H₂.
    apply fst_same_iff in Hs₄; simpl in Hs₄.
    destruct Hs₄ as (Hn₄, Hs₄).
    rename Hsj into Hoj.
    rename dj into oj.
    remember (fst_same a b (S i + S dl)) as dj eqn:Hsj .
    symmetry in Hsj.
    destruct dj as [dj| ]; simpl in Hoj; subst oj.
     assert (dl + dj - dl < di₄) as H by omega.
     apply Hn₄ in H.
     rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
     rewrite Nat.add_shuffle0, Nat.add_sub in H.
     rewrite Nat.add_assoc in H.
     rewrite Nat.add_succ_r in Hsj; simpl in Hsj.
     apply fst_same_iff in Hsj; simpl in Hsj.
     destruct Hsj as (Hnj, Hsj).
     rewrite Hsj in H.
     destruct b .[ S (S (i + dl + dj))]; discriminate H.

     rewrite Nat.add_succ_r in Hsj; simpl in Hsj.
     apply fst_same_iff in Hsj; simpl in Hsj.
     pose proof (Hsj di₄) as H.
     rewrite Hs₄ in H.
     destruct b .[ S (S (i + dl + di₄))]; discriminate H.

  rename H into Hab.
  apply fst_same_iff in Hs₄; simpl in Hs₄.
  rename Hsj into Hoj.
  rename dj into oj.
  remember (fst_same a b (S i + S dl)) as dj eqn:Hsj .
  symmetry in Hsj.
  destruct dj as [dj| ]; simpl in Hoj; subst oj.
   pose proof (Hs₄ dj) as H.
   apply fst_same_iff in Hsj; simpl in Hsj.
   destruct Hsj as (Hnj, Hsj).
   rewrite Nat.add_succ_r in Hsj; simpl in Hsj.
   rewrite Hsj in H.
   destruct b .[ S (S (i + dl + dj))]; discriminate H.

   rewrite Nat.add_0_r in Hdk.
   remember (fst_same (second n a i) (second n b i) (S (S (i + dl)))) as s₁.
   rename Heqs₁ into Hs₁.
   apply fst_same_sym_iff in Hs₁.
   destruct s₁ as [di₁| ]; [ idtac | assumption ].
   destruct Hs₁ as (Hn₁, Hs₁); simpl in Hs₁.
   rewrite Nat.add_succ_r in Hs₁.
   remember (i + n) as ipn eqn:Hin .
   symmetry in Hin.
   destruct ipn; [ exfalso; omega | idtac ].
   remember (nat_compare (i + dl + di₁) ipn) as cmp eqn:Hcmp .
   symmetry in Hcmp.
   destruct cmp; [ assumption | idtac | idtac ].
    pose proof (Hs₄ di₁) as H₁.
    rewrite Hs₁ in H₁.
    destruct b .[ S (S (i + dl + di₁))]; discriminate H₁.

    apply nat_compare_gt in Hcmp.
    assert (n - S dl < di₁) as H by omega.
    apply Hn₁ in H.
    simpl in H.
    rewrite Nat.add_succ_r, Hin in H.
    rewrite Nat.add_0_r in Hns.
    rewrite Hns in H.
    rewrite Nat.add_succ_l in H.
    rewrite Nat.sub_succ in H.
    rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
    rewrite Nat.add_shuffle0, Nat.add_sub in H.
    assert (i + (S (S dl) + n₀) = ipn) as H₁ by omega.
    apply nat_compare_eq_iff in H₁.
    rewrite H₁ in H; discriminate H.
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

Definition rm_add'_i a b i :=
  a.[i] ⊕ b.[i] ⊕
  match fst_same a b (S i) with
  | Some dj => a.[S i + dj]
  | None => false
  end.

Definition rm_add' a b := {| rm := rm_add'_i a b |}.

Notation "a +' b" := (rm_add' a b) (left associativity, at level 50) : rm_scope.

Definition rnot a := {| rm i := negb a.[i] |}.

Theorem add_and_add'_are_twins : ∀ a b i,
  (a +' b)%rm.[i] = (rnot (rnot a + rnot b))%rm.[i].
Proof.
intros a b i; simpl.
unfold rm_add'_i.
unfold rm_add_i, carry_i; simpl.
remember (fst_same a b (S i)) as s₁ eqn:Hs₁ .
remember (fst_same (rnot a) (rnot b) (S i)) as s₂ eqn:Hs₂ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
apply fst_same_sym_iff in Hs₂; simpl in Hs₂.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁).
 destruct s₂ as [di₂| ].
  destruct Hs₂ as (Hn₂, Hs₂).
  do 2 rewrite negb_xorb_l.
  rewrite negb_involutive.
  do 2 rewrite xorb_assoc; f_equal.
  rewrite <- negb_xorb_l.
  rewrite <- negb_xorb_r.
  rewrite negb_involutive; f_equal.
  destruct (lt_dec di₁ di₂) as [H₁| H₁].
   apply Hn₂ in H₁.
   rewrite negb_involutive in H₁.
   rewrite Hs₁ in H₁.
   destruct b .[ S (i + di₁)]; discriminate H₁.

   apply Nat.nlt_ge in H₁.
   destruct (lt_dec di₂ di₁) as [H₂| H₂].
    apply Hn₁ in H₂.
    rewrite H₂ in Hs₂.
    destruct b .[ S (i + di₂)]; discriminate Hs₂.

    apply Nat.nlt_ge in H₂.
    apply Nat.le_antisymm in H₂; auto.

  pose proof (Hs₂ di₁) as H.
  rewrite Hs₁ in H.
  destruct b .[ S (i + di₁)]; discriminate H.

 destruct s₂ as [di₂| ].
  destruct Hs₂ as (Hn₂, Hs₂).
  pose proof (Hs₁ di₂) as H.
  rewrite <- Hs₂ in H.
  destruct a .[ S (i + di₂)]; discriminate H.

  destruct a .[ i], b .[ i]; reflexivity.
Qed.

(* I don't think the method with +' works...
Theorem www : ∀ a b, (a + b = a +' b)%rm.
Proof.
intros a b.
bbb.

unfold rm_eq; intros i; simpl.
unfold rm_add_i, carry_i; simpl.
do 2 rewrite xorb_false_r.
unfold rm_add_i, carry_i at 1.
unfold rm_add'_i at 1.
remember (fst_same a b (S i)) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁).
 f_equal.
 remember (fst_same (a + b) 0 (S i)) as s₂ eqn:Hs₂ .
 remember (fst_same (a +' b) 0 (S i)) as s₃ eqn:Hs₃ .
 apply fst_same_sym_iff in Hs₂; simpl in Hs₂.
 destruct s₂ as [di₂| ].
  destruct Hs₂ as (Hn₂, Hs₂); rewrite Hs₂.
  destruct s₃ as [di₃| ].
   apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
   destruct Hs₃ as (Hn₃, Hs₃); rewrite Hs₃.
   reflexivity.

   apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
   pose proof (Hs₃ di₂) as H.
   unfold rm_add_i, carry_i in Hs₂.
   unfold rm_add'_i in H.
   remember (fst_same a b (S (S (i + di₂)))) as s₄ eqn:Hs₄ .
   destruct s₄ as [di₄| ].
    rewrite Hs₂ in H; discriminate H.

    apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
    rewrite xorb_false_r in H.
    clear Hs₂; rename H into Hs₂.
    move Hs₂ before Hn₂.
    Focus 1.
    pose proof (Hs₃ di₁) as H.
    unfold rm_add'_i in H; simpl in H.
    simpl in Hs₁.
    rewrite Hs₁, xorb_nilpotent, xorb_false_l in H.
    remember (fst_same a b (S (S (i + di₁)))) as s₅ eqn:Hs₅ .
    apply fst_same_sym_iff in Hs₅; simpl in Hs₅.
    destruct s₅ as [di₅| ]; [ idtac | discriminate H ].
    destruct Hs₅ as (Hn₅, Hs₅).
bbb.
*)

(* (a+b)''+c'' = (a''+b'')+c'' *)
(* seems that it is false with this example :
   a = 0,00001011101110111011101110111... (repetition pattern 0111)
   b = 0,01101110111011101110111011101... (repetition pattern 1101)
   c = 0,00000101010101010101010101010... (repetition pattern 10)
 a'' = 0,00001011000...
 b'' = 0,01101111000...
 c'' = 0,00000101000...
 *)
Theorem yyy : ∀ a b c i d₁ d₂ di,
  d₁ = opt2nat (fst_same (a + b) c (S i))
  → d₂ = opt2nat (fst_same a b (S i + d₁))
  → di = S (d₁ + d₂)
  → ∀ n₀ n, n = S di + n₀ →
     (second n (a + b) i + second n c i)%rm.[i] =
     ((second n a i + second n b i) + second n c i)%rm.[i].
Proof.
intros a b c i d₁ d₂ di Hd₁ Hd₂ Hdi n₀ n Hn; simpl.
Abort. (*
bbb.
unfold rm_add_i, carry_i; simpl.
rewrite nat_compare_add_succ, Nat.add_succ_r.
remember (fst_same (a + b) c (S i)) as s₁ eqn:Hs₁ .
symmetry in Hs₁.
destruct s₁ as [di₁| ]; simpl in Hd₁.
 remember Hs₁ as H; clear HeqH.
 eapply fst_same_fin_eq_second with (n := n) (n₀ := S n₀ + di - d₁) in H.
  Focus 2.
  rewrite Hd₁.
  rewrite Nat.add_sub_assoc.
   rewrite Nat.add_comm, Nat.add_sub.
   simpl; rewrite Nat.add_comm; assumption.

   rewrite Nat.add_comm, Hdi, Hd₁.
   rewrite <- Nat.add_succ_r.
   rewrite <- Nat.add_assoc.
   apply Nat.le_sub_le_add_l.
   rewrite Nat.sub_diag.
   apply Nat.le_0_l.

  rewrite H.
  unfold rm_add_i, carry_i at 1.
  unfold rm_add_i, carry_i at 2; simpl.
  rewrite nat_compare_add_succ, Nat.add_succ_r.
  clear H.
  remember (fst_same a b (S i)) as s₂ eqn:Hs₂ .
  symmetry in Hs₂.
  destruct s₂ as [di₂| ].
   erewrite fst_same_fin_eq_second with (n₀ := n - S di₂); try eassumption.
    Focus 2.
    rewrite Nat.add_sub_assoc.
     rewrite Nat.add_comm, Nat.add_sub; reflexivity.

     destruct (lt_dec di₂ (S di₁)) as [H₁| H₁].
      eapply Nat.lt_le_trans; [ eassumption | idtac ].
      rewrite Hn, Hdi; simpl.
      do 2 rewrite <- Nat.add_succ_r.
      rewrite Hd₁.
      rewrite <- Nat.add_assoc.
      apply Nat.le_sub_le_add_l.
      rewrite Nat.sub_diag.
      apply Nat.le_0_l.

      apply Nat.nlt_ge in H₁.
      remember (fst_same a b (S i + d₁)) as s₃ eqn:Hs₃ .
      symmetry in Hs₃.
      destruct s₃ as [di₃| ]; simpl in Hd₂.
       subst d₁ d₂.
       destruct (lt_dec (S di₁ + di₃) di₂) as [H₂| H₂].
        apply fst_same_iff in Hs₂; simpl in Hs₂.
        destruct Hs₂ as (Hn₂, Hs₂).
        remember H₂ as H; clear HeqH.
        apply Hn₂ in H.
        apply fst_same_iff in Hs₃; simpl in Hs₃.
        destruct Hs₃ as (Hn₃, Hs₃).
        rewrite Nat.add_succ_r in Hs₃; simpl in Hs₃.
        rewrite Nat.add_succ_l, Nat.add_succ_r in H.
        rewrite Nat.add_assoc, Hs₃ in H.
        destruct b .[ S (S (i + di₁ + di₃))]; discriminate H.

        apply Nat.nlt_ge in H₂.
        apply Nat.succ_le_mono in H₂.
        rewrite <- Nat.add_succ_r in H₂.
        eapply le_trans; eauto .
        rewrite Hn, Hdi.
        remember (S di₁ + S di₃) as x; simpl.
        do 2 rewrite <- Nat.add_succ_r.
        apply Nat.le_sub_le_add_l.
        rewrite Nat.sub_diag.
        apply Nat.le_0_l.

       rewrite Hn, Hdi.
       subst d₂.
       rewrite Nat.add_0_r in Hdi |- *.
       rewrite Hd₁; simpl.
       apply fst_same_iff in Hs₃; simpl in Hs₃.
       apply fst_same_iff in Hs₂; simpl in Hs₂.
       destruct Hs₂ as (Hn₂, Hs₂).
       subst d₁.
       pose proof (Hs₃ (di₂ - S di₁)) as H.
       rewrite Nat.add_sub_assoc in H; auto.
       rewrite Nat.add_shuffle0, Nat.add_sub in H.
       rewrite Hs₂ in H.
       destruct b .[ S (i + di₂)]; discriminate H.

    remember (nat_compare (i + di₁) (i + n)) as cmp eqn:Hcmp .
    symmetry in Hcmp.
    destruct cmp.
     apply nat_compare_eq in Hcmp.
     exfalso; omega.

     apply nat_compare_lt in Hcmp.
     clear Hcmp.
     assert (di₂ < n) as H.
      rewrite Hn.
      apply fst_same_iff in Hs₂; simpl in Hs₂.
      destruct Hs₂ as (Hn₂, Hs₂).
      remember (fst_same a b (S i + d₁)) as s₃ eqn:Hs₃ .
      symmetry in Hs₃.
      destruct s₃ as [di₃| ]; simpl in Hd₂.
       apply fst_same_iff in Hs₃; simpl in Hs₃.
       destruct Hs₃ as (Hn₃, Hs₃).
       apply Nat.nle_gt.
       intros H₁.
       simpl in H₁.
       assert (d₁ + di₃ < di₂) as H by omega.
       apply Hn₂ in H.
       rewrite Nat.add_assoc in H.
       rewrite Hs₃ in H.
       destruct b .[ S (i + d₁ + di₃)]; discriminate H.

       subst d₂.
       rewrite Nat.add_0_r in Hdi.
       apply fst_same_iff in Hs₃; simpl in Hs₃.
       apply Nat.nle_gt.
       intros H₁.
       pose proof (Hs₃ (di₂ - d₁)) as H.
       rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
       rewrite Nat.add_shuffle0, Nat.add_sub in H.
       rewrite Hs₂ in H.
       destruct b .[ S (i + di₂)]; discriminate H.

      remember (nat_compare (i + di₂) (i + n)) as cmp eqn:Hcmp .
      symmetry in Hcmp.
      destruct cmp.
       apply nat_compare_eq in Hcmp.
       apply Nat.add_cancel_l in Hcmp.
       rewrite Hcmp in H.
       exfalso; revert H; apply Nat.lt_irrefl.

       clear Hcmp; f_equal.
       remember Hd₂ as Hd₂v; clear HeqHd₂v; symmetry in Hd₂v.
       remember (fst_same a b (S i + d₁)) as s₃ eqn:Hs₃ in Hd₂.
       symmetry in Hs₃.
       destruct s₃ as [di₃| ]; simpl in Hd₂.
        destruct (lt_dec (S di₁ + di₃) di₂) as [H₂| H₂].
         apply fst_same_iff in Hs₂; simpl in Hs₂.
         destruct Hs₂ as (Hn₂, Hs₂).
         rename H into H₁.
         remember H₂ as H; clear HeqH.
         apply Hn₂ in H.
         apply fst_same_iff in Hs₃; simpl in Hs₃.
         destruct Hs₃ as (Hn₃, Hs₃).
         rewrite Hd₁, Nat.add_succ_r in Hs₃; simpl in Hs₃.
         rewrite Nat.add_succ_l, Nat.add_succ_r in H.
         rewrite Nat.add_assoc, Hs₃ in H.
         destruct b .[ S (S (i + di₁ + di₃))]; discriminate H.

         apply Nat.nlt_ge in H₂.
         subst d₁ d₂ di.
         rewrite Nat.add_succ_l, <- Nat.add_succ_r in H₂.
         erewrite same_fst_same_add_second; try eassumption.
         destruct (eq_nat_dec di₂ (S di₁ + di₃)) as [H₃| H₃].
          rewrite Nat.add_succ_r in Hs₃; simpl in Hs₃.
          unfold rm_add_i, carry_i.
          rewrite Hs₃.
          erewrite fst_same_second with (dj := di₃).
           2: eassumption.

           2: rewrite <- Nat.add_succ_r; reflexivity.

           2: assumption.

           2: rewrite Hn.
           2: rewrite Nat.add_succ_r, <- H₃.
           2: simpl.
           2: rewrite <- Nat.add_succ_r.
           2: rewrite <- Nat.add_succ_r.
           2: reflexivity.

           simpl.
           rewrite Nat.add_succ_r.
           assert (di₁ < n) as Hdn by omega.
           remember (nat_compare (i + di₁) (i + n)) as cmp eqn:Hcmp .
           symmetry in Hcmp.
           destruct cmp.
            apply nat_compare_eq in Hcmp.
            exfalso; omega.

            clear Hcmp.
            f_equal.
            remember (i + n) as ipn eqn:Hin .
            symmetry in Hin.
            destruct ipn.
             exfalso; omega.

             remember (nat_compare (i + di₁ + di₃) ipn) as cmp eqn:Hcmp .
             symmetry in Hcmp.
             destruct cmp.
              apply nat_compare_eq in Hcmp.
              exfalso; omega.

              reflexivity.

              apply nat_compare_gt in Hcmp.
              exfalso; omega.

            apply nat_compare_gt in Hcmp.
            exfalso; omega.

          rename H into Hdn.
          assert (di₂ < S di₁ + di₃) as H by omega.
          clear H₂ H₃.
          rename H into H₁.
          destruct (lt_dec di₁ di₂) as [H₂| H₂].
           apply fst_same_iff in Hs₂; simpl in Hs₂.
           destruct Hs₂ as (Hn₂, Hs₂).
           apply fst_same_iff in Hs₃; simpl in Hs₃.
           destruct Hs₃ as (Hn₃, Hs₃).
           assert (di₂ - S di₁ < di₃) as H by omega.
           apply Hn₃ in H.
           rewrite Nat.add_sub_assoc in H; auto.
           rewrite Nat.add_shuffle0, Nat.add_sub in H.
           rewrite Hs₂ in H.
           destruct b .[ S (i + di₂)]; discriminate H.

           apply Nat.nlt_ge in H₂.
           destruct (lt_dec di₂ di₁) as [H₃| H₃].
            unfold rm_add_i, carry_i.
            rewrite <- Nat.add_succ_r, <- Nat.add_succ_l, Hs₃.
            rewrite Nat.add_succ_l.
            replace n with (n - S di₁ + S di₁) at 3 by omega.
            rewrite fst_same_second_add.
            rewrite fst_same_comm.
            replace n with (n - S di₁ + S di₁) at 3 by omega.
            rewrite fst_same_second_add.
            rewrite fst_same_comm.
            erewrite fst_same_fin_eq_second with (n₀ := n - S (di₁ + S di₃)).
             2: eassumption.

             2: rewrite <- Nat.add_succ_l.
             2: rewrite Nat.sub_add_distr.
             2: rewrite Nat.add_sub_assoc; [ idtac | omega ].
             2: rewrite Nat.add_comm, Nat.add_sub.
             2: reflexivity.

             simpl.
             rewrite Nat.add_succ_r.
             rewrite Nat.add_succ_r.
             assert (di₁ < n) as H by omega.
             remember (nat_compare (S (i + di₁)) (S (i + n))) as cmp eqn:Hcmp .
             symmetry in Hcmp.
             destruct cmp.
              apply nat_compare_eq in Hcmp.
              exfalso; omega.

              clear Hcmp.
              f_equal.
              remember (nat_compare (S (i + di₁) + di₃) (i + n)) as cmp.
              rename Heqcmp into Hcmp.
              symmetry in Hcmp.
              destruct cmp.
               apply nat_compare_eq in Hcmp.
               exfalso; omega.

               reflexivity.

               apply nat_compare_gt in Hcmp.
               exfalso; omega.

              apply nat_compare_gt in Hcmp.
              exfalso; omega.

            apply Nat.nlt_ge in H₃.
            apply Nat.le_antisymm in H₃; auto.
            subst di₂.
            clear H₁ H₂.
            unfold rm_add_i, carry_i.
            rewrite <- Nat.add_succ_r, <- Nat.add_succ_l, Hs₃.
            rewrite Nat.add_succ_l.
            replace n with (n - S di₁ + S di₁) at 3 by omega.
            rewrite fst_same_second_add.
            rewrite fst_same_comm.
            replace n with (n - S di₁ + S di₁) at 3 by omega.
            rewrite fst_same_second_add.
            rewrite fst_same_comm.
            erewrite fst_same_fin_eq_second with (n₀ := n - S (di₁ + S di₃)).
             2: eassumption.

             2: rewrite <- Nat.add_succ_l.
             2: rewrite Nat.sub_add_distr.
             2: rewrite Nat.add_sub_assoc; [ idtac | omega ].
             2: rewrite Nat.add_comm, Nat.add_sub.
             2: reflexivity.

             simpl.
             rewrite Nat.add_succ_r.
             rewrite Nat.add_succ_r.
             remember (nat_compare (S (i + di₁)) (S (i + n))) as cmp eqn:Hcmp .
             symmetry in Hcmp.
             destruct cmp.
              apply nat_compare_eq in Hcmp.
              exfalso; omega.

              clear Hcmp.
              f_equal.
              remember (nat_compare (S (i + di₁) + di₃) (i + n)) as cmp.
              rename Heqcmp into Hcmp.
              symmetry in Hcmp.
              destruct cmp.
               apply nat_compare_eq in Hcmp.
               exfalso; omega.

               reflexivity.

               apply nat_compare_gt in Hcmp.
               exfalso; omega.

              apply nat_compare_gt in Hcmp.
              exfalso; omega.

        subst d₁ d₂.
        unfold rm_add_i, carry_i at 1; simpl.
        rewrite Nat.add_succ_r in Hs₃; simpl in Hs₃; rewrite Hs₃.
        rewrite Nat.add_0_r in Hdi.
        destruct (lt_dec di₁ di₂) as [H₁| H₁].
         apply fst_same_iff in Hs₂; simpl in Hs₂.
         destruct Hs₂ as (Hn₂, Hs₂).
         apply fst_same_iff in Hs₃; simpl in Hs₃.
         clear H.
         pose proof (Hs₃ (di₂ - S di₁)) as H.
         rewrite Nat.add_shuffle0, Nat.add_comm in H.
         rewrite <- Nat.add_succ_l, Nat.add_assoc in H.
         rewrite Nat.add_sub_assoc in H; auto.
         rewrite <- Nat.add_assoc, Nat.add_comm, Nat.add_sub in H.
         rewrite Hs₂ in H.
         destruct b .[ S (i + di₂)]; discriminate H.

         apply Nat.nlt_ge in H₁.
         rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in Hs₃.
         subst di.
         rewrite <- Nat.add_0_r in H₁.
         replace (S di₁) with (S di₁ + 0) in Hn by apply Nat.add_0_r.
         erewrite same_fst_same_add_second; try eassumption.
         rewrite Nat.add_0_r in H₁, Hn.
         unfold rm_add_i, carry_i; simpl.
         rewrite Nat.add_succ_r.
         assert (i + di₁ < i + n) as Hcmp by omega.
         apply nat_compare_lt in Hcmp.
         rewrite Hcmp; clear Hcmp; f_equal.
         remember (i + n) as ipn eqn:Hin .
         symmetry in Hin.
         destruct ipn; [ exfalso; omega | idtac ].
         remember (S (S (i + di₁))) as x.
         remember (fst_same (second n a i) (second n b i) x) as s₄ eqn:Hs₄ .
         subst x.
         symmetry in Hs₄.
         destruct s₄ as [di₄| ]; [ idtac | reflexivity ].
         apply fst_same_iff in Hs₄.
         destruct Hs₄ as (Hn₄, Hs₄); simpl in Hs₄.
         rewrite Nat.add_succ_r, Hin in Hs₄.
         remember (nat_compare (i + di₁ + di₄) ipn) as cmp eqn:Hcmp .
         symmetry in Hcmp.
         destruct cmp; [ reflexivity | idtac | idtac ].
          apply fst_same_iff in Hs₃; simpl in Hs₃.
          rename H into Hdi₂.
          pose proof (Hs₃ di₄) as H.
          rewrite Nat.add_succ_r in H; simpl in H.
          rewrite Hs₄ in H.
          destruct b .[ S (S (i + di₁ + di₄))]; discriminate H.

          simpl in Hn₄.
          rewrite Nat.add_succ_r, Hin in Hn₄.
          apply nat_compare_gt in Hcmp.
          rename H into Hdi₂.
          assert (ipn - (i + di₁) < di₄) as H by omega.
          apply Hn₄ in H.
          rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
          rewrite Nat.add_comm, Nat.add_sub in H.
          pose proof (eq_refl ipn) as H₂.
          apply nat_compare_eq_iff in H₂.
          rewrite H₂ in H; discriminate H.

       apply nat_compare_gt in Hcmp.
       exfalso; omega.

     apply nat_compare_gt in Hcmp.
     exfalso; omega.

   rewrite fst_same_inf_after in Hd₂; [ simpl in Hd₂ | assumption ].
   subst d₂; rewrite Nat.add_0_r in Hdi.
   subst d₁ di.
   assert (i + di₁ < i + n) as H by omega.
   apply nat_compare_lt in H; rewrite H; clear H.
   remember (fst_same (second n a i) (second n b i) (S i)) as s₃ eqn:Hs₃ .
   symmetry in Hs₃.
   destruct s₃ as [di₃| ].
    apply fst_same_iff in Hs₃.
    destruct Hs₃ as (Hn₃, Hs₃); simpl in Hs₃.
    rewrite Nat.add_succ_r in Hs₃.
    remember (nat_compare (i + di₃) (i + n)) as cmp eqn:Hcmp .
    symmetry in Hcmp.
    destruct cmp.
     f_equal.
     unfold rm_add_i, carry_i at 1.
     rewrite <- Nat.add_succ_l, <- Nat.add_succ_r.
     rewrite fst_same_inf_after; [ idtac | assumption ].
     remember (second n a i + second n b i)%rm as x.
     remember (fst_same x (second n c i) (S i)) as s₄ eqn:Hs₄ ; subst x.
     symmetry in Hs₄.
     destruct s₄ as [di₄| ].
      apply fst_same_iff in Hs₄.
      destruct Hs₄ as (Hn₄, Hs₄); simpl in Hs₄.
      rewrite Nat.add_succ_r in Hs₄.
      rewrite Hs₄.
      apply nat_compare_eq in Hcmp.
      rename Hcmp into Hdi₃.
      remember (nat_compare (i + di₄) (i + n)) as cmp eqn:Hcmp .
      symmetry in Hcmp.
      destruct cmp.
       apply nat_compare_eq in Hcmp.
       apply Nat.add_cancel_l in Hcmp; subst di₄.
       unfold rm_add_i, carry_i in Hs₄; simpl in Hs₄.
       rewrite Nat.add_succ_r in Hs₄.
       assert (i + n = i + n) as H by reflexivity.
       apply nat_compare_eq_iff in H.
       rewrite H in Hs₄; clear H.
       rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in Hs₄.
       remember (fst_same (second n a i) (second n b i) (S i + S n)) as s₅.
       rename Heqs₅ into Hs₅.
       symmetry in Hs₅.
       destruct s₅ as [di₅| ].
        remember (i + n) as ipn eqn:Hin .
        symmetry in Hin.
        destruct ipn; [ exfalso; omega | idtac ].
        assert (S ipn + di₅ > ipn) as H by omega.
        apply nat_compare_gt in H.
        rewrite H in Hs₄; discriminate Hs₄.

        apply fst_same_iff in Hs₅; simpl in Hs₅.
        rewrite Nat.add_succ_r in Hs₅.
        pose proof (Hs₅ 0) as H.
        assert (S (i + n) + 0 > i + n) as H₁ by omega.
        apply nat_compare_gt in H₁.
        rewrite H₁ in H; discriminate H.

       unfold rm_add_i, carry_i in Hs₄; simpl in Hs₄.
       rewrite Nat.add_succ_r, Hcmp in Hs₄.
       remember (S (S (i + di₄))) as x.
       remember (fst_same (second n a i) (second n b i) x) as s₅ eqn:Hs₅ .
       subst x.
       symmetry in Hs₅.
       destruct s₅ as [di₅| ].
        remember (i + n) as ipn eqn:Hin .
        symmetry in Hin.
        destruct ipn; [ exfalso; omega | idtac ].
        apply nat_compare_lt in Hcmp.
        apply fst_same_iff in Hs₅.
        destruct Hs₅ as (Hn₅, Hs₅).
        simpl in Hs₅.
        rewrite Nat.add_succ_r, Hin in Hs₅.
        rename Hcmp into Hdi₄.
        remember (nat_compare (i + di₄ + di₅) ipn) as cmp eqn:Hcmp .
        symmetry in Hcmp.
        destruct cmp.
         apply fst_same_iff in Hs₂; simpl in Hs₂.
         rewrite <- Hs₄; simpl.
         do 2 rewrite Hs₂.
         do 2 rewrite negb_xorb_diag; reflexivity.

         apply fst_same_iff in Hs₂.
         rewrite <- Nat.add_succ_r, <- Nat.add_succ_l in Hs₅.
         rewrite <- Nat.add_succ_l, <- Nat.add_assoc in Hs₅.
         rewrite Hs₂ in Hs₅.
         destruct b .[ S i + (di₄ + S di₅)]; discriminate Hs₅.

         apply nat_compare_gt in Hcmp.
         assert (n - S di₄ < di₅) as H by omega.
         apply Hn₅ in H.
         rewrite <- Nat.add_succ_r in H.
         rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
         rewrite Nat.add_succ_l, Nat.add_shuffle0 in H.
         rewrite <- Nat.add_succ_l in H.
         rewrite Nat.add_sub in H; simpl in H.
         rewrite Nat.add_succ_r, Hin in H.
         assert (S ipn = S ipn) as H₁ by reflexivity.
         apply nat_compare_eq_iff in H₁.
         rewrite H₁ in H; discriminate H.

        apply fst_same_iff in Hs₂; simpl in Hs₂.
        rewrite <- Hs₄; simpl.
        do 2 rewrite Hs₂.
        do 2 rewrite negb_xorb_diag; reflexivity.

       apply fst_same_iff in Hs₂.
       rewrite Hs₂.
       rewrite negb_xorb_diag; reflexivity.

      apply fst_same_iff in Hs₄; simpl in Hs₄.
      rewrite Nat.add_succ_r in Hs₄.
      pose proof (Hs₄ di₁) as H.
      assert (i + di₁ < i + n) as H₁ by omega.
      apply nat_compare_lt in H₁.
      rewrite H₁ in H; clear H₁.
      unfold rm_add_i, carry_i in H.
      rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H.
      rewrite fst_same_inf_second2 with (n₀ := S (S n₀)) in H; auto;
       try omega.
      simpl in H.
      rewrite Nat.add_succ_r in H.
      assert (i + di₁ < i + n) as H₁ by omega.
      apply nat_compare_lt in H₁; rewrite H₁ in H; clear H₁.
      assert (i + S di₁ + S (S n₀) = i + n) as H₁ by omega.
      apply nat_compare_eq_iff in H₁.
      rewrite H₁ in H; clear H₁.
      apply fst_same_iff in Hs₁; simpl in Hs₁.
      destruct Hs₁ as (Hn₁, Hs₁).
      unfold rm_add_i, carry_i in Hs₁; simpl in Hs₁.
      rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in Hs₁.
      rewrite fst_same_inf_after in Hs₁; auto.
      simpl in Hs₁.
      rewrite Hs₁ in H.
      destruct c .[ S (i + di₁)]; discriminate H.

     apply fst_same_iff in Hs₂; simpl in Hs₂.
     rewrite Hs₂ in Hs₃.
     destruct b .[ S (i + di₃)]; discriminate Hs₃.

     apply nat_compare_gt in Hcmp.
     apply Nat.add_lt_mono_l in Hcmp.
     apply Hn₃ in Hcmp; simpl in Hcmp.
     rewrite Nat.add_succ_r in Hcmp.
     assert (i + n = i + n) as H by reflexivity.
     apply nat_compare_eq_iff in H.
     rewrite H in Hcmp; discriminate Hcmp.

    replace (S i) with (S i + 0) in Hs₃ by apply Nat.add_0_r.
    erewrite fst_same_inf_second2 in Hs₃; try reflexivity; auto.
    discriminate Hs₃.

 subst d₁ di.
 rewrite Nat.add_0_r in Hd₂; simpl in Hn.
(* pourrait servir, on sait jamais...
   assert (∀ di, rm_add_i (a + b) c (S i + di) = false) as Hdi.
    intros di.
    unfold rm_add_i, carry_i.
    rewrite <- Nat.add_succ_r.
    rewrite fst_same_inf_after; [ idtac | assumption ].
    apply fst_same_iff in Hs₁; rewrite Hs₁.
    destruct c .[ S i + di]; reflexivity.
*)
 unfold rm_add_i, carry_i at 1.
 unfold rm_add_i, carry_i at 2; simpl.
 rewrite Nat.add_succ_r.
 rewrite <- Nat.add_succ_r, nat_compare_add_succ.
 rewrite fst_same_inf_second; auto.
 assert (i + n = i + n) as H by reflexivity.
 apply nat_compare_eq_iff in H; rewrite H; clear H.
 do 6 rewrite xorb_assoc; f_equal; f_equal.
 rewrite xorb_comm; symmetry.
 rewrite xorb_comm; symmetry.
 do 2 rewrite xorb_assoc; f_equal.
 remember (fst_same a b (S i)) as s₂ eqn:Hs₂ .
 symmetry in Hs₂.
 destruct s₂ as [di₂| ]; simpl in Hd₂; subst d₂.
  erewrite fst_same_second with (n₀ := S (S n₀)); try eassumption.
   2: rewrite Nat.add_0_r; reflexivity.

   2: reflexivity.

   2: omega.

   assert (i + di₂ < i + n) as H by omega.
   apply nat_compare_lt in H; rewrite H; clear H.
   f_equal.
bbb.

   remember
    (fst_same (second n a i + second n b i) (second n c i) (S i)) as s₃
    eqn:Hs₃ .
   symmetry in Hs₃.
   destruct s₃ as [di₃| ]; [ idtac | reflexivity ].
   apply fst_same_iff in Hs₃.
   destruct Hs₃ as (Hn₃, Hs₃); simpl in Hs₃.
   rewrite Nat.add_succ_r in Hs₃.
   rewrite Hs₃.
   remember (nat_compare (i + di₃) (i + n)) as cmp eqn:Hcmp .
   symmetry in Hcmp.
   destruct cmp; [ reflexivity | idtac | idtac ].
    unfold rm_add_i, carry_i in Hs₃; simpl in Hs₃.
    rewrite Nat.add_succ_r, Hcmp in Hs₃.
    destruct (lt_dec di₃ di₂) as [H₁| H₁].
     erewrite fst_same_second with (dj := di₂ - S di₃) (n₀ := S (S n₀))
      in Hs₃.
      2: eassumption.

      2: rewrite Nat.add_succ_r; reflexivity.

      2: omega.

      2: omega.

      remember (i + n) as ipn eqn:Hin .
      symmetry in Hin.
      destruct ipn; [ exfalso; omega | idtac ].
      apply nat_compare_lt in Hcmp.
      rename Hcmp into Hdi₃.
      assert (i + di₃ + (di₂ - S di₃) < ipn) as Hcmp by omega.
      apply nat_compare_lt in Hcmp.
      rewrite Hcmp in Hs₃; clear Hcmp.
      rewrite Nat.add_sub_assoc in Hs₃; [ idtac | omega ].
      rewrite Nat.add_shuffle0 in Hs₃.
      rewrite <- Nat.sub_succ_l in Hs₃; [ idtac | omega ].
      rewrite <- Nat.add_succ_r in Hs₃.
      rewrite <- Nat.add_succ_r in Hs₃.
      rewrite Nat.add_sub in Hs₃.
      apply fst_same_iff in Hs₂; simpl in Hs₂.
      destruct Hs₂ as (Hn₂, Hs₂).
      assert (di₃ < di₂) as H by omega.
      apply Hn₂ in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite H, negb_xorb_diag in Hs₃.
      apply fst_same_iff in Hs₁; simpl in Hs₁.
      rename H into Hab.
      pose proof (Hs₁ di₃) as H.
      unfold rm_add_i, carry_i in H; simpl in H.
      remember (fst_same a b (S (S (i + di₃)))) as s₄ eqn:Hs₄ .
      destruct s₄ as [di₄| ].
       apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
       destruct Hs₄ as (Hn₄, Hs₄).
       assert (di₂ = S (di₃ + di₄)) as HH.
        destruct (lt_dec di₂ (S (di₃ + di₄))) as [H₂| H₂].
         assert (di₂ - S di₃ < di₄) as HH by omega.
         apply Hn₄ in HH.
         rewrite <- Nat.add_succ_l in HH.
         rewrite <- Nat.add_succ_l in HH.
         rewrite <- Nat.add_succ_r in HH.
         rewrite <- Nat.add_succ_l in HH.
         rewrite Nat.add_sub_assoc in HH; [ idtac | omega ].
         rewrite Nat.add_shuffle0, Nat.add_sub in HH.
         simpl in HH.
         rewrite Hs₂ in HH.
         destruct b .[ S (i + di₂)]; discriminate HH.

         apply Nat.nlt_ge in H₂.
         destruct (lt_dec (S (di₃ + di₄)) di₂) as [H₃| H₃].
          apply Hn₂ in H₃.
          rewrite Nat.add_succ_r in H₃; simpl in H₃.
          rewrite Nat.add_assoc in H₃.
          rewrite Hs₄ in H₃.
          destruct b .[ S (S (i + di₃ + di₄))]; discriminate H₃.

          apply Nat.nlt_ge in H₃.
          apply Nat.le_antisymm; assumption.

        rewrite HH in Hs₃.
        rewrite Nat.add_succ_r in Hs₃.
        rewrite Nat.add_assoc in Hs₃.
        rewrite Nat.add_succ_r in Hab.
        rewrite Hab in H.
        rewrite negb_xorb_diag in H.
        rewrite Hs₃ in H.
        rewrite Nat.add_succ_r in H.
        destruct c .[ S (i + di₃)]; discriminate H.

       apply fst_same_sym_iff in Hs₄.
       pose proof (Hs₄ (di₂ - S di₃)) as HH.
       rewrite Nat.add_sub_assoc in HH; [ idtac | omega ].
       rewrite <- Nat.add_succ_l in HH.
       rewrite <- Nat.add_succ_r in HH.
       rewrite Nat.add_shuffle0, Nat.add_sub in HH.
       simpl in HH.
       rewrite Hs₂ in HH.
       destruct b .[ S (i + di₂)]; discriminate HH.

     apply Nat.nlt_ge in H₁.
     destruct (lt_dec di₂ di₃) as [H₂| H₂].
      remember H₂ as H; clear HeqH.
      apply Hn₃ in H.
      simpl in H.
      rewrite Nat.add_succ_r in H.
      assert (i + di₂ < i + n) as HH by omega.
      apply nat_compare_lt in HH.
      rewrite HH in H; clear HH.
      unfold rm_add_i, carry_i in H.
      simpl in H.
      rewrite Nat.add_succ_r in H.
      assert (i + di₂ < i + n) as HH by omega.
      apply nat_compare_lt in HH.
      rewrite HH in H; clear HH.
      remember (i + n) as ipn eqn:Hin .
      symmetry in Hin.
      destruct ipn; [ exfalso; omega | idtac ].
bbb.
      remember (S (S (i + di₃))) as x.
      remember (fst_same (second n a i) (second n b i) x) as s₄ eqn:Hs₄ .
      subst x.
      apply fst_same_sym_iff in Hs₄.
      destruct s₄ as [di₄| ].
       apply nat_compare_lt in Hcmp.
       destruct (lt_dec (S (di₃ + di₄)) n) as [H₃| H₃].
        rename H into Hab.
        assert (i + di₃ + di₄ < ipn) as H by omega.
        apply nat_compare_lt in H.
        rewrite H in Hs₃; clear H.
bbb.
*)

(* actually false because we should add 0 to both sides but just to see *)
Theorem zzz : ∀ a b c i, rm_add_i a (b + c) i = rm_add_i (a + b) c i.
Proof.
intros a b c i.
remember (opt2nat (fst_same a (b + c) (S i))) as d₂ eqn:Hd₂ .
remember (opt2nat (fst_same b c (S i))) as d₃ eqn:Hd₃ .
remember (opt2nat (fst_same (a + b) c (S i))) as d₅ eqn:Hd₅ .
remember (opt2nat (fst_same a b (S i))) as d₆ eqn:Hd₆ .
remember [d₂; d₃; d₅; d₆ … []] as dl eqn:Hdl .
remember (S (List.fold_right max 0 dl)) as di eqn:Hdi .
assert (List.In d₂ dl) as Hi₂ by (subst dl; left; reflexivity).
assert (List.In d₃ dl) as Hi₃ by (subst dl; right; left; reflexivity).
assert (List.In d₅ dl) as Hi₅ by (subst dl; do 2 right; left; reflexivity).
assert (List.In d₆ dl) as Hi₆ by (subst dl; do 3 right; left; reflexivity).
do 2 rewrite fold_rm_add_i.
symmetry.
erewrite <- tr_add_i_eq_rm_add_i.
erewrite tr_add_rm_add_distr; [ idtac | eauto  | reflexivity ].
Abort. (*
erewrite yyy; [ idtac | eauto  | reflexivity ].
bbb.

erewrite rm_add_i_eq_tr_add with (n := di - d₂); try reflexivity.
rewrite <- Hd₂.
erewrite add_succ_sub_max; [ idtac | eauto  | auto ].
bbb.
erewrite rm_add_i_eq_tr_add with (n := di - d₅); try reflexivity.
rewrite <- Hd₅.
erewrite add_succ_sub_max; [ idtac | eauto  | auto ].
1-
unfold tr_add_i.
remember Hd₂ as H; clear HeqH.
apply yyy with (n := di - d₂) in H.
rewrite Nat.add_sub_assoc in H.
 rewrite Nat.add_succ_l, <- Nat.add_succ_r in H.
 rewrite Nat.add_comm, Nat.add_sub in H.
 rewrite H.
 clear H.
bbb.
-1
unfold tr_add_i.
rewrite last_tr_add_with_carry.
 erewrite last_carry_on_max; try eassumption.
 rewrite last_tr_add_with_carry.
  erewrite last_carry_on_max; try eassumption.
  do 4 rewrite last_trunc_from; simpl.
  remember (a .[ i + d₂] || Nat.eqb d₂ 0) as c₃.
  remember (rm_add_i a b (i + d₅) || Nat.eqb d₅ 0) as c₄.
  erewrite rm_add_i_eq_tr_add with (n := di - d₃); try reflexivity.
  rewrite <- Hd₃.
  erewrite add_succ_sub_max; [ idtac | eauto  | auto ].
  erewrite rm_add_i_eq_tr_add with (n := di - d₆); try reflexivity.
  rewrite <- Hd₆.
  erewrite add_succ_sub_max; [ idtac | eauto  | auto ].
  unfold tr_add_i.
  rewrite last_tr_add_with_carry.
   erewrite last_carry_on_max; try eassumption.
   rewrite last_tr_add_with_carry.
    erewrite last_carry_on_max; try eassumption.
    do 3 rewrite last_trunc_from; simpl.
    remember (b .[ i + d₃] || Nat.eqb d₃ 0) as c₅.
    remember (a .[ i + d₆] || Nat.eqb d₆ 0) as c₆.
    do 6 rewrite xorb_assoc; f_equal; f_equal; symmetry.
    rewrite xorb_comm, xorb_assoc; f_equal.
    remember Hd₅ as H; clear HeqH.
    apply same_on_relay in H; simpl in H.
    rewrite H in Heqc₄; clear H.
bbb.
  Heqc₃ : c₃ = a .[ i + d₂] || Nat.eqb d₂ 0
  Heqc₄ : c₄ = c .[ i + d₅] || Nat.eqb d₅ 0
  Heqc₅ : c₅ = b .[ i + d₃] || Nat.eqb d₃ 0
  Heqc₆ : c₆ = a .[ i + d₆] || Nat.eqb d₆ 0
  ============================
   c₄ ⊕ c₆ = c₅ ⊕ c₃
*)

Theorem rm_add_assoc : ∀ a b c, (a + (b + c) = (a + b) + c)%rm.
Proof.
intros a b c.
unfold rm_eq; intros i.
remember (opt2nat (fst_same (a + (b + c)%rm) 0 (S i))) as d₁ eqn:Hd₁ .
remember (opt2nat (fst_same a (b + c) (S i))) as d₂ eqn:Hd₂ .
remember (opt2nat (fst_same b c (S i))) as d₃ eqn:Hd₃ .
remember (opt2nat (fst_same ((a + b)%rm + c) 0 (S i))) as d₄ eqn:Hd₄ .
remember (opt2nat (fst_same (a + b) c (S i))) as d₅ eqn:Hd₅ .
remember (opt2nat (fst_same a b (S i))) as d₆ eqn:Hd₆ .
remember [d₁; d₂; d₃; d₄; d₅; d₆ … []] as dl eqn:Hdl .
remember (S (List.fold_right max 0 dl)) as di eqn:Hdi .
assert (List.In d₁ dl) as Hi₁ by (subst dl; left; reflexivity).
assert (List.In d₂ dl) as Hi₂ by (subst dl; right; left; reflexivity).
assert (List.In d₃ dl) as Hi₃ by (subst dl; do 2 right; left; reflexivity).
assert (List.In d₄ dl) as Hi₄ by (subst dl; do 3 right; left; reflexivity).
assert (List.In d₅ dl) as Hi₅ by (subst dl; do 4 right; left; reflexivity).
assert (List.In d₆ dl) as Hi₆ by (subst dl; do 5 right; left; reflexivity).
Abort. (*
erewrite <- xxx; [ idtac | eassumption | reflexivity ].
bbb.

intros a b c.
unfold rm_eq; intros i; simpl.
remember (opt2nat (fst_same (a + (b + c)%rm) 0 (S i))) as d₁ eqn:Hd₁ .
remember (opt2nat (fst_same a (b + c) (S i))) as d₂ eqn:Hd₂ .
remember (opt2nat (fst_same b c (S i))) as d₃ eqn:Hd₃ .
remember (opt2nat (fst_same ((a + b)%rm + c) 0 (S i))) as d₄ eqn:Hd₄ .
remember (opt2nat (fst_same (a + b) c (S i))) as d₅ eqn:Hd₅ .
remember (opt2nat (fst_same a b (S i))) as d₆ eqn:Hd₆ .
remember [d₁; d₂; d₃; d₄; d₅; d₆ … []] as dl eqn:Hdl .
remember (S (List.fold_right max 0 dl)) as di eqn:Hdi .
assert (List.In d₁ dl) as Hi₁ by (subst dl; left; reflexivity).
assert (List.In d₂ dl) as Hi₂ by (subst dl; right; left; reflexivity).
assert (List.In d₃ dl) as Hi₃ by (subst dl; do 2 right; left; reflexivity).
assert (List.In d₄ dl) as Hi₄ by (subst dl; do 3 right; left; reflexivity).
assert (List.In d₅ dl) as Hi₅ by (subst dl; do 4 right; left; reflexivity).
assert (List.In d₆ dl) as Hi₆ by (subst dl; do 5 right; left; reflexivity).
erewrite rm_add_i_eq_tr_add with (n := di - d₁); try reflexivity.
rewrite <- Hd₁.
erewrite add_succ_sub_max; [ idtac | eauto  | auto ].
erewrite rm_add_i_eq_tr_add with (n := di - d₄); try reflexivity.
rewrite <- Hd₄.
erewrite add_succ_sub_max; [ idtac | eauto  | auto ].
(*
bbb.
  ============================
   tr_add_i (S di) (a + (b + c))%rm 0%rm i =
   tr_add_i (S di) (a + b + c)%rm 0%rm i
*)
unfold tr_add_i.
rewrite last_tr_add_with_carry.
 erewrite last_carry_on_max; try eassumption.
 rewrite last_tr_add_with_carry.
  erewrite last_carry_on_max; try eassumption.
  do 3 rewrite last_trunc_from; simpl.
  do 2 rewrite xorb_false_r.
(*
bbb.
  ============================
   rm_add_i a (b + c) i ⊕ (rm_add_i a (b + c) (i + d₁) || Nat.eqb d₁ 0) =
   rm_add_i (a + b) c i ⊕ (rm_add_i (a + b) c (i + d₄) || Nat.eqb d₄ 0)
*)
  remember (rm_add_i a (b + c) (i + d₁) || Nat.eqb d₁ 0) as c₁.
  remember (rm_add_i (a + b) c (i + d₄) || Nat.eqb d₄ 0) as c₂.
  erewrite rm_add_i_eq_tr_add with (n := di - d₂); try reflexivity.
  rewrite <- Hd₂.
  erewrite add_succ_sub_max; [ idtac | eauto  | auto ].
  erewrite rm_add_i_eq_tr_add with (n := di - d₅); try reflexivity.
  rewrite <- Hd₅.
  erewrite add_succ_sub_max; [ idtac | eauto  | auto ].
  unfold tr_add_i.
  rewrite last_tr_add_with_carry.
   erewrite last_carry_on_max; try eassumption.
   rewrite last_tr_add_with_carry.
    erewrite last_carry_on_max; try eassumption.
    do 4 rewrite last_trunc_from; simpl.
    remember (a .[ i + d₂] || Nat.eqb d₂ 0) as c₃.
    remember (rm_add_i a b (i + d₅) || Nat.eqb d₅ 0) as c₄.
    erewrite rm_add_i_eq_tr_add with (n := di - d₃); try reflexivity.
    rewrite <- Hd₃.
    erewrite add_succ_sub_max; [ idtac | eauto  | auto ].
    erewrite rm_add_i_eq_tr_add with (n := di - d₆); try reflexivity.
    rewrite <- Hd₆.
    erewrite add_succ_sub_max; [ idtac | eauto  | auto ].
    unfold tr_add_i.
    rewrite last_tr_add_with_carry.
     erewrite last_carry_on_max; try eassumption.
     rewrite last_tr_add_with_carry.
      erewrite last_carry_on_max; try eassumption.
      do 3 rewrite last_trunc_from; simpl.
      remember (b .[ i + d₃] || Nat.eqb d₃ 0) as c₅.
      remember (a .[ i + d₆] || Nat.eqb d₆ 0) as c₆.
      do 8 rewrite xorb_assoc; f_equal; f_equal.
      symmetry.
      rewrite xorb_comm, xorb_assoc; f_equal.
      symmetry; rewrite <- xorb_assoc.
bbb.
  Heqc₁ : c₁ = rm_add_i a (b + c) (i + d₁) || Nat.eqb d₁ 0
  Heqc₂ : c₂ = rm_add_i (a + b) c (i + d₄) || Nat.eqb d₄ 0
  Heqc₃ : c₃ = a .[ i + d₂] || Nat.eqb d₂ 0
  Heqc₄ : c₄ = rm_add_i a b (i + d₅) || Nat.eqb d₅ 0
  Heqc₅ : c₅ = b .[ i + d₃] || Nat.eqb d₃ 0
  Heqc₆ : c₆ = a .[ i + d₆] || Nat.eqb d₆ 0
  ============================
   c₅ ⊕ c₃ ⊕ c₁ = c₄ ⊕ c₂ ⊕ c₆

bbb.
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
bbb.
*)

(* old method; but need 4800 goals to resolve *)

Theorem case_1 : ∀ b₀ c₀ i si,
  let b := (b₀ + 0)%rm in
  let c := (c₀ + 0)%rm in
  si = S i
  → rm_add_i c₀ 0 i = true
  → rm_add_i c₀ 0 si = true
  → rm_add_i b₀ 0 i = true
  → rm_add_i b₀ 0 si = true
  → rm_add_i (b + c) 0 i = true.
Proof.
intros b₀ c₀ i si b c Heqsi Hxci Hxcs Hxbi Hxbs.
apply eq_true_negb_classical; intros Hxbci.
apply negb_true_iff in Hxbci.
unfold rm_add_i, carry_i in Hxbci.
rewrite <- Heqsi in Hxbci; simpl in Hxbci.
rewrite xorb_false_r in Hxbci.
unfold rm_add_i in Hxbci at 1.
unfold carry_i in Hxbci.
rewrite <- Heqsi in Hxbci; simpl in Hxbci.
rewrite Hxbi, Hxci, xorb_true_r in Hxbci.
rewrite xorb_false_l in Hxbci.
remember (fst_same b c si) as s₁ eqn:Hs₁ .
apply fst_same_sym_iff in Hs₁; simpl in Hs₁.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁).
 destruct di₁.
  rewrite Nat.add_0_r, Hxbs, xorb_true_l in Hxbci.
  apply negb_false_iff in Hxbci.
  remember (fst_same (b + c) 0 si) as s₂ eqn:Hs₂ .
  apply fst_same_sym_iff in Hs₂; simpl in Hs₂.
  destruct s₂ as [di₂| ].
   destruct Hs₂ as (Hn₂, Hs₂); rewrite Hs₂ in Hxbci.
   discriminate Hxbci.

   apply rm_add_inf_true_eq_if in Hs₂.
    destruct Hs₂ as (Hs₂, Hs₃); simpl in Hs₂, Hs₃.
    exfalso; eapply not_rm_add_0_inf_1_succ; eauto .

    simpl; rewrite Hxcs; assumption.

  pose proof (Hn₁ 0 (Nat.lt_0_succ di₁)) as H.
  rewrite Nat.add_0_r, Hxbs, Hxcs in H.
  discriminate H.

 pose proof (Hs₁ 0) as H.
 rewrite Nat.add_0_r, Hxbs, Hxcs in H.
 discriminate H.
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
  → id (∀ j, a.[i + S j] = true).
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

Theorem rm_add_assoc : ∀ a b c, (a + (b + c) = (a + b) + c)%rm.
Proof.
intros a b c.
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
destruct c₁, c₂, c₃, c₄, c₅, c₆; try reflexivity; simpl.
 apply carry_0_r_true_if in Hc₁.
 apply carry_0_r_true_if in Hc₂.
 unfold id in Hc₁, Hc₂.
 simpl in Hc₁, Hc₂.
bbb.

 unfold carry_i in Hc₆; simpl in Hc₆.
 remember (fst_same a b (S i)) as s₆ eqn:Hs₆ .
 apply fst_same_sym_iff in Hs₆; simpl in Hs₆.
 destruct s₆ as [di₆| ]; [ idtac | discriminate Hc₆ ].
 destruct Hs₆ as (Hn₆, Hs₆).
 rewrite Hc₆ in Hs₆.
 rename Hc₆ into Ha₆; rename Hs₆ into Hb₆.
 move Ha₆ after Hb₆; symmetry in Hb₆.
 unfold carry_i in Hc₃; simpl in Hc₃.
 remember (fst_same a (b + c) (S i)) as s₃ eqn:Hs₃ .
 destruct s₃ as [di₃| ].
  apply fst_same_sym_iff in Hs₃; simpl in Hs₃.
  destruct Hs₃ as (Hn₃, Hs₃).
  destruct (lt_dec di₃ di₆) as [H₃₆| H₃₆].
   remember H₃₆ as H; clear HeqH.
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
   destruct s₅ as [di₅| ].
    apply fst_same_sym_iff in Hs₅; simpl in Hs₅.
    destruct Hs₅ as (Hn₅, Hs₅).
    rewrite Hc₅ in Hs₅.
    rename Hc₅ into Hb₅; rename Hs₅ into Hc₅.
    symmetry in Hc₅; move Hb₅ after Hc₅.
    destruct (lt_dec di₅ di₃) as [H₅₃| H₃₅].
     remember H₅₃ as H; clear HeqH.
     apply Hn₃ in H.
     apply negb_sym in H.
     rename H into Hs₅.
     move Hs₅ before Hc₅.
     assert (di₅ < di₆) as H₅₆ by omega.
     apply Hn₆ in H₅₆.
     rewrite Hb₅ in H₅₆; simpl in H₅₆.
     move H₅₆ after Hb₅.
     rewrite H₅₆ in Hs₅; simpl in Hs₅.
     destruct di₅.
      clear Hn₅; rewrite Nat.add_0_r in H₅₆, Hb₅, Hc₅, Hs₅.
bbb.
      unfold carry_i in Hc₄; simpl in Hc₄.
      remember (fst_same (a + b) c (S i)) as s₄ eqn:Hs₄ .
      destruct s₄ as [di₄| ].
       apply fst_same_sym_iff in Hs₄; simpl in Hs₄.
       destruct Hs₄ as (Hn₄, Hs₄); rewrite Hc₄ in Hs₄.
       symmetry in Hs₄.
       unfold rm_add_i in Hc₄; simpl in Hc₄.
       unfold rm_add_i in Hs₅; simpl in Hs₅.
       rewrite Hb₅, Hc₅ in Hs₅.
       rewrite xorb_nilpotent, xorb_false_l in Hs₅.
       destruct di₄.
        clear Hn₄; rewrite Nat.add_0_r in Hs₄, Hc₄.
        rewrite H₅₆, Hb₅ in Hc₄.
        rewrite xorb_false_l, xorb_true_l in Hc₄.
        apply negb_true_iff in Hc₄.
        unfold carry_i in Hc₂; simpl in Hc₂.
        clear Hs₄.
        unfold carry_i in Hc₁; simpl in Hc₁.
        remember (fst_same (a + (b + c)%rm) 0 (S i)) as s₇ eqn:Hs₇ .
        destruct s₇ as [di₇| ].
         apply fst_same_sym_iff in Hs₇; simpl in Hs₇.
         destruct Hs₇ as (Hn₇, Hs₇).
         rewrite Hc₁ in Hs₇; discriminate Hs₇.

         apply fst_same_sym_iff in Hs₇; simpl in Hs₇.
         pose proof (Hs₇ 0) as H; simpl in H.
         rewrite Nat.add_0_r in H.
         unfold rm_add_i in H; simpl in H.
         rewrite H₅₆, xorb_false_l in H.
         unfold carry_i in H; simpl in H.
         unfold rm_add_i in H; simpl in H.
         rewrite Hb₅, Hc₅, Hs₅ in H.
         rewrite xorb_nilpotent, xorb_false_l, xorb_true_l in H.
         apply negb_true_iff in H.
         unfold carry_i in Hc₄; simpl in Hc₄.
bbb.

destruct c₁.
 unfold carry_i in Hc₁.
 remember (fst_same (a + (b + c)%rm) 0 (S i)) as s₁ eqn:Hs₁ .
 apply fst_same_sym_iff in Hs₁.
 destruct s₁ as [di₁| ].
  rewrite Hc₁ in Hs₁.
  destruct Hs₁ as (_, Hs₁); discriminate Hs₁.

  clear Hc₁.
  remember (S i) as si; simpl in Hs₁; subst si.
  remember Hs₁ as H; clear HeqH.
  apply rm_add_inf_if in H.
  destruct H as (j, (Hj, (Ha, Hb))).
  simpl in Hb.
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
