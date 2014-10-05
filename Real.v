Require Import Utf8 QArith NPeano.

Set Implicit Arguments.

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

Definition rm_add_i a b i :=
  a.[i] ⊕ b.[i] ⊕
  match fst_same a b (S i) with
  | Some dj => a.[S i + dj]
  | None => true
  end.

Definition rm_add a b := {| rm := rm_add_i a b |}.
Definition rm_eq a b := ∀ i,
  rm (rm_add a rm_zero) i = rm (rm_add b rm_zero) i.

Delimit Scope rm_scope with rm.
Arguments rm r%rm i%nat.
Arguments rm_add_i a%rm b%rm i%nat.
Arguments fst_same a%rm b%rm i%nat.
Notation "a + b" := (rm_add a b) : rm_scope.
Notation "a = b" := (rm_eq a b) : rm_scope.
Notation "a ≠ b" := (¬ rm_eq a b) : rm_scope.
Notation "0" := rm_zero : rm_scope.

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
unfold rm_add_i.
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
unfold rm_add_i; simpl.
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
 unfold rm_add_i in H; simpl in H.
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
  unfold rm_add_i in H₁; simpl in H₁.
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
unfold rm_add_i in H.
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

Theorem rm_add_i_0_r : ∀ a i, rm_add_i (a + 0%rm) 0 i = rm_add_i a 0 i.
Proof.
intros a i.
unfold rm_add_i at 1.
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

Theorem rm_add_eq_compat_r : ∀ a b c j,
  (∀ i, a .[ i] = b .[ i])
  → rm_add_i b c j = rm_add_i a c j.
Proof.
intros a b c j Hab.
unfold rm_add_i; simpl.
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
 unfold rm_add_i in Hi.
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

   rewrite xorb_true_r in Hi.
   exfalso; revert Hs₂; rewrite Hb; apply not_rm_add_0_inf_1.

  exfalso; revert Hs₁; rewrite Ha; apply not_rm_add_0_inf_1.

 clear Hab; rename H into Hab.
 unfold rm_eq; simpl.
 intros i; unfold rm_add_i.
 remember (S i) as si; simpl.
 do 2 rewrite xorb_false_r.
 symmetry; erewrite rm_add_eq_compat_r; [ symmetry | eauto  ].
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
   apply rm_add_eq_compat_r; auto.

  destruct s₂ as [di₂| ]; auto.
  rewrite <- Hs₁ with (dj := di₂).
  apply rm_add_eq_compat_r; auto.
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

Theorem xxx : ∀ a b i, rm_add_i (a + 0%rm) b i = rm_add_i a b i.
Proof.
intros a b i.
unfold rm_add_i; simpl.
remember (fst_same (a + 0%rm) b (S i)) as s₁ eqn:Hs₁ .
remember (fst_same a b (S i)) as s₂ eqn:Hs₂ .
symmetry in Hs₁, Hs₂.
apply fst_same_iff in Hs₁.
apply fst_same_iff in Hs₂.
simpl in Hs₁, Hs₂.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁).
 rewrite <- Nat.add_succ_r in Hs₁.
 rewrite <- Nat.add_succ_r.
 rewrite Hs₁.
 unfold rm_add_i; simpl.
 rewrite xorb_false_r.
 remember (fst_same a 0 (S i)) as s₃ eqn:Hs₃ .
 symmetry in Hs₃.
 apply fst_same_iff in Hs₃; simpl in Hs₃.
 destruct s₂ as [di₂| ].
  rewrite <- Nat.add_succ_r in Hs₂.
  rewrite <- Nat.add_succ_r.
  destruct Hs₂ as (Hn₂, Hs₂).
  rewrite Hs₂.
  destruct s₃ as [di₃| ].
   rewrite <- Nat.add_succ_r in Hs₃.
   rewrite <- Nat.add_succ_r.
   destruct Hs₃ as (Hn₃, Hs₃).
   rewrite Hs₃, xorb_false_r; f_equal.
   unfold rm_add_i in Hs₁; simpl in Hs₁.
   rewrite xorb_false_r in Hs₁.
   remember (fst_same a 0 (S (i + S di₁))) as s₄ eqn:Hs₄ .
   symmetry in Hs₄.
   apply fst_same_iff in Hs₄; simpl in Hs₄.
   destruct s₄ as [di₄| ].
    rewrite <- Nat.add_succ_r in Hs₄, Hs₁.
    destruct Hs₄ as (Hn₄, Hs₄).
    rewrite Hs₄, xorb_false_r in Hs₁.
    destruct (lt_dec di₁ di₂) as [H₁| H₁].
     remember H₁ as H; clear HeqH.
     apply Hn₂ in H.
     rewrite <- Nat.add_succ_r in H.
     rewrite Hs₁ in H.
     destruct b .[ i + S di₁]; discriminate H.

     apply Nat.nlt_ge in H₁.
     destruct (lt_dec di₂ di₁) as [H₂| H₂].
      remember H₂ as H; clear HeqH.
      apply Hn₁ in H.
      rewrite <- Nat.add_succ_r in H.
      unfold rm_add_i in H; simpl in H.
      remember (fst_same a 0 (S (i + S di₂))) as s₅ eqn:Hs₅ .
      symmetry in Hs₅.
      apply fst_same_iff in Hs₅; simpl in Hs₅.
      destruct s₅ as [di₅| ].
       rewrite <- Nat.add_succ_r in Hs₅, H.
       destruct Hs₅ as (Hn₅, Hs₅).
       rewrite xorb_false_r, Hs₂, Hs₅, xorb_false_r in H.
       destruct b .[ i + S di₂]; discriminate H.

       clear H.
       pose proof (Hs₅ (di₁ - di₂ + di₄)) as H.
       rewrite Nat.add_succ_r in H.
       do 3 rewrite <- Nat.add_succ_l in H.
       remember (S (S i)) as ssi.
       do 2 rewrite Nat.add_comm, Nat.add_assoc in H.
       rewrite Nat.add_assoc in H.
       rewrite Nat.add_sub_assoc in H; auto.
       rewrite Nat.add_sub_swap in H; auto.
       rewrite Nat.sub_diag, Nat.add_0_l in H.
       rewrite Nat.add_comm, Nat.add_assoc in H.
       subst ssi; simpl in H.
       rewrite <- Nat.add_succ_r in H.
       rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H.
       rewrite Hs₄ in H; discriminate H.

      apply Nat.nlt_ge in H₂.
      apply Nat.le_antisymm in H₁; auto.

    rewrite xorb_true_r in Hs₁.
    destruct (lt_dec di₂ di₁) as [H₂| H₂].
     remember H₂ as H; clear HeqH.
     apply Hn₁ in H.
     rewrite <- Nat.add_succ_r in H.
     unfold rm_add_i in H; simpl in H.
     remember (fst_same a 0 (S (i + S di₂))) as s₅ eqn:Hs₅ .
     symmetry in Hs₅.
     apply fst_same_iff in Hs₅; simpl in Hs₅.
     destruct s₅ as [di₅| ].
      rewrite <- Nat.add_succ_r in Hs₅, H.
      destruct Hs₅ as (Hn₅, Hs₅).
      rewrite xorb_false_r, Hs₂, Hs₅, xorb_false_r in H.
      destruct b .[ i + S di₂]; discriminate H.

      clear H.
      rewrite <- Hs₁, <- Hs₂.
      destruct (lt_dec di₂ di₃) as [H₃| H₃].
       pose proof (Hs₅ (di₃ - S di₂)) as H.
       do 2 rewrite Nat.add_comm, Nat.add_assoc in H.
       rewrite <- Nat.add_succ_l in H.
       rewrite Nat.add_sub_assoc in H; auto.
       rewrite Nat.add_sub_swap in H; auto.
       rewrite Nat.sub_diag, Nat.add_0_l in H; simpl in H.
       rewrite Nat.add_comm, <- Nat.add_succ_r, Hs₃ in H.
       discriminate H.

       apply Nat.nlt_ge in H₃.
       destruct (bool_dec a .[ i + S di₂] false) as [H₄| H₄].
        rewrite H₄.
        apply negb_false_iff.
        pose proof (Hs₅ (di₁ - S di₂)) as H.
        do 2 rewrite Nat.add_comm, Nat.add_assoc in H.
        rewrite Nat.add_sub_assoc in H; auto.
        rewrite Nat.add_sub_swap in H; auto.
        rewrite Nat.sub_diag, Nat.add_0_l in H; simpl in H.
        rewrite Nat.add_comm, <- Nat.add_succ_r in H.
        assumption.

        apply not_false_iff_true in H₄.
        rewrite H₄ in Hs₂.
        symmetry in Hs₂.
        exfalso.
        destruct (lt_dec di₃ di₂) as [H₅| H₅].
         remember H₅ as H; clear HeqH.
         apply Hn₂ in H.
         rewrite <- Nat.add_succ_r in H.
         rewrite Hs₃ in H; symmetry in H.
         apply negb_false_iff in H.
         rename H into Hb.
         remember H₂ as H; clear HeqH.
         eapply Nat.lt_trans in H; [ idtac | eauto  ].
         apply Hn₁ in H.
         rewrite <- Nat.add_succ_r in H.
         rewrite Hb in H; simpl in H.
         unfold rm_add_i in H; simpl in H.
         rewrite Hs₃, xorb_false_r, xorb_false_l in H.
         remember (fst_same a 0 (S (i + S di₃))) as s₆ eqn:Hs₆ .
         symmetry in Hs₆.
         apply fst_same_iff in Hs₆; simpl in Hs₆.
         destruct s₆ as [di₆| ]; [ idtac | discriminate H ].
         rewrite <- Nat.add_succ_r in Hs₆, H.
         destruct Hs₆ as (Hn₆, Hs₆).
         clear H.
         remember (first_false_before a (i + S di₂)) as j eqn:Hj .
         symmetry in Hj.
         destruct j as [j| ].
          apply first_false_before_some_iff in Hj.
          destruct Hj as (Hji, (Hjf, Hk)).
          assert (j - S i < di₁) as H.
           eapply Nat.le_lt_trans; [ idtac | eauto  ].
           rewrite Nat.add_succ_r in Hji.
           apply Nat.succ_le_mono in Hji.
           apply Nat.le_sub_le_add_l.
           apply Nat.le_le_succ_r; assumption.

           apply Hn₁ in H.
           rewrite Nat.add_sub_assoc in H.
            Focus 2.
            apply Nat.nlt_ge; intros Hcont.
            apply Nat.succ_le_mono in Hcont.
            rewrite Hk in Hs₃; [ discriminate Hs₃ | idtac | idtac ].
             eapply Nat.le_lt_trans; [ eauto  | idtac ].
             apply Nat.lt_sub_lt_add_l.
             rewrite Nat.sub_diag.
             apply Nat.lt_0_succ.

             apply Nat.add_lt_mono_l.
             apply Nat.succ_lt_mono in H₅; assumption.

            rewrite <- Nat.sub_succ_l in H.
             rewrite <- Nat.add_succ_l, Nat.add_comm, Nat.add_sub in H.
             unfold rm_add_i in H; simpl in H.
             rewrite Hjf, xorb_false_r, xorb_false_l in H.
             remember (fst_same a 0 (S j)) as s₇ eqn:Hs₇ .
             symmetry in Hs₇.
             apply fst_same_iff in Hs₇; simpl in Hs₇.
             destruct s₇ as [di₇| ].
              destruct Hs₇ as (Hn₇, Hs₇).
              rewrite Hs₇ in H.
              symmetry in H.
              apply negb_false_iff in H.
              rewrite <- Nat.add_succ_r in Hs₇.
              destruct (lt_dec (j + S di₇) (i + S di₂)) as [H₁| H₁].
               rewrite Hk in Hs₇; auto; [ discriminate Hs₇ | idtac ].
               apply Nat.lt_sub_lt_add_l.
               rewrite Nat.sub_diag.
               apply Nat.lt_0_succ.

               apply Nat.nlt_ge in H₁.
               rename H into Hbt.
               destruct (lt_dec (i + S di₂) (j + S di₇)) as [H₆| H₆].
                pose proof (Hs₅ (j + di₇ - (i + S di₂))) as H.
                rewrite Nat.add_succ_r in H₆.
                rewrite Nat.add_succ_r in H₆.
                apply Nat.succ_le_mono in H₆.
                rewrite <- Nat.add_succ_r in H₆.
                rewrite Nat.add_sub_assoc in H; auto.
                rewrite Nat.add_comm, Nat.add_sub in H.
                rewrite <- Nat.add_succ_r, Hs₇ in H; discriminate H.

                apply Nat.nlt_ge in H₆.
                apply Nat.le_antisymm in H₁; auto.
                rewrite H₁, H₄ in Hs₇; discriminate Hs₇.

              symmetry in H.
              apply negb_true_iff in H.
              rename H into H₆.
              assert (j - S i < di₂) as H.
               revert Hji H₅; clear; intros; omega.

               apply Hn₂ in H.
               rewrite <- Nat.add_succ_l in H.
               rewrite Nat.add_sub_assoc in H.
                rewrite Nat.add_comm, Nat.add_sub in H.
                rewrite Hjf, H₆ in H; discriminate H.

                clear H.
                apply Nat.nlt_ge; intros Hcont.
                assert (j < i + S di₃) as H.
                 apply Nat.succ_le_mono in Hcont.
                 eapply Nat.le_lt_trans; eauto .
                 apply Nat.lt_sub_lt_add_l.
                 rewrite Nat.sub_diag; apply Nat.lt_0_succ.

                 apply Hk in H; [ rewrite Hs₃ in H; discriminate H | idtac ].
                 apply Nat.add_lt_mono_l.
                 apply Nat.succ_lt_mono in H₅; auto.

             destruct j.
              rewrite Hk in Hs₃; [ discriminate Hs₃ | idtac | idtac ].
               rewrite Nat.add_succ_r.
               apply Nat.lt_0_succ.

               apply Nat.add_lt_mono_l.
               apply Nat.succ_lt_mono in H₅; auto.

              rewrite Nat.add_succ_r, <- Nat.add_succ_l.
              apply Nat.le_sub_le_add_l.
              rewrite Nat.sub_diag.
              apply Nat.le_0_l.

          rewrite first_false_before_none_iff in Hj.
          rewrite Hj in Hs₃; [ discriminate Hs₃ | idtac ].
          apply Nat.add_lt_mono_l.
          apply Nat.succ_lt_mono in H₅; assumption.

         apply Nat.nlt_ge in H₅.
         apply Nat.le_antisymm in H₅; [ idtac | auto ].
         subst di₃.
         rewrite H₄ in Hs₃; discriminate Hs₃.

     apply Nat.nlt_ge in H₂.
     destruct (lt_dec di₁ di₂) as [H₃| H₃].
      pose proof (Hs₄ (di₂ - S di₁)) as H.
      rewrite Nat.add_sub_assoc in H; auto.
      rewrite Nat.add_shuffle0, Nat.add_sub in H.
      rewrite <- Nat.add_succ_r in H.
      rewrite H in Hs₂; symmetry in Hs₂.
      rename H into Ha; move Ha after Hs₂; rewrite Hs₂.
      symmetry in Hs₁; apply negb_sym in Hs₁.
      remember b .[ i + S di₁] as bi eqn:Hbi .
      destruct bi; [ reflexivity | idtac ].
      symmetry in Hbi; simpl in Hs₁.
      exfalso.
      destruct (lt_dec di₁ di₃) as [H₁| H₁].
       pose proof (Hs₄ (di₃ - S di₁)) as H.
       rewrite Nat.add_sub_assoc in H; auto.
       rewrite Nat.add_shuffle0, Nat.add_sub in H.
       rewrite <- Nat.add_succ_r, Hs₃ in H; discriminate H.

       apply Nat.nlt_ge in H₁.
       destruct (eq_nat_dec di₁ di₃) as [H₄| H₄].
        subst di₃.
        rewrite Hs₁ in Hs₃; discriminate Hs₃.

        assert (di₃ < di₁) as H.
         apply Nat.nle_gt; intros H.
         apply Nat.le_antisymm in H; auto; contradiction.

         clear H₄; rename H into H₄.
         remember (first_false_before a (i + S di₁)) as j eqn:Hj .
         symmetry in Hj.
         destruct j as [j| ].
          apply first_false_before_some_iff in Hj.
          destruct Hj as (Hji, (Hjf, Hk)).
          assert (i < j) as Hij.
           apply Nat.nle_gt; intros H.
           rewrite Hk in Hs₃; [ discriminate Hs₃ | idtac | idtac ].
            eapply Nat.le_lt_trans; eauto .
            apply Nat.lt_sub_lt_add_l.
            rewrite Nat.sub_diag.
            apply Nat.lt_0_succ.

            apply Nat.add_lt_mono_l.
            apply Nat.succ_lt_mono in H₄; assumption.

           assert (j - S i < di₁) as H.
            apply Nat.add_lt_mono_r with (p := S i).
            rewrite <- Nat.add_sub_swap; auto.
            rewrite Nat.add_succ_r, <- Nat.add_succ_l, Nat.add_comm in Hji.
            rewrite Nat.add_sub; assumption.

            apply Hn₁ in H.
            rewrite <- Nat.add_succ_l in H.
            rewrite Nat.add_sub_assoc in H; auto.
            rewrite Nat.add_comm, Nat.add_sub in H.
            unfold rm_add_i in H; simpl in H.
            rewrite Hjf, xorb_false_r, xorb_false_l in H.
            remember (fst_same a 0 (S j)) as s₇ eqn:Hs₇ .
            symmetry in Hs₇.
            apply fst_same_iff in Hs₇; simpl in Hs₇.
            destruct s₇ as [di₇| ].
             destruct Hs₇ as (Hn₇, Hs₇).
             rewrite Hs₇ in H.
             symmetry in H.
             apply negb_false_iff in H.
             rewrite <- Nat.add_succ_r in Hs₇.
             rewrite Hk in Hs₇; [ discriminate Hs₇ | idtac | idtac ].
              apply Nat.lt_sub_lt_add_l.
              rewrite Nat.sub_diag.
              apply Nat.lt_0_succ.

              apply Nat.nle_gt; intros Hcont.
              rename H into Hbt.
              destruct (lt_dec (i + S di₁) (j + S di₇)) as [H₅| H₅].
               pose proof (Hs₄ (j + S di₇ - S (i + S di₁))) as H.
               rewrite <- Nat.add_succ_l in H.
               rewrite Nat.add_sub_assoc in H; auto.
               rewrite Nat.add_comm, Nat.add_sub in H.
               rewrite Hs₇ in H; discriminate H.

               apply Nat.nlt_ge in H₅.
               apply Nat.le_antisymm in H₅; auto.
               rewrite <- H₅, Hs₁ in Hs₇; discriminate Hs₇.

             symmetry in H.
             apply negb_true_iff in H.
bbb.
*)

Theorem yyy : ∀ a b, (a + 0 + b = a + b)%rm.
Proof.
intros a b.
unfold rm_eq; intros i; simpl.
unfold rm_add_i; simpl.
do 2 rewrite xorb_false_r.
bbb.
remember (fst_same (a + b) 0 (S i)) as s₁ eqn:Hs₁ .
remember (fst_same (a + 0 + b)%rm 0 (S i)) as s₂ eqn:Hs₂ .
symmetry in Hs₁, Hs₂.
apply fst_same_iff in Hs₁.
apply fst_same_iff in Hs₂.
simpl in Hs₁, Hs₂.
bbb.
destruct s₁ as [di₁| ].
 destruct Hs₁ as (Hn₁, Hs₁).
 rewrite Hs₁, xorb_false_r.
 destruct s₂ as [di₂| ].
  destruct Hs₂ as (Hn₂, Hs₂).
  rewrite Hs₂, xorb_false_r.
bbb.
*)

Theorem rm_add_compat_r : ∀ a b c, (a = b)%rm → (a + c = b + c)%rm.
Proof.
intros a b c Hab.
remember (a + 0)%rm as a₁.
remember (b + 0)%rm as b₁.
remember Heqa₁ as H; clear HeqH.
eapply rm_norm_eq_compat_r with (b₀ := b) (c := c) in H; eauto .
 Focus 2.
 subst a₁ b₁.
 do 2 rewrite rm_add_0_r.
 assumption.

 subst a₁ b₁.
bbb.
 rewrite <- yyy in H.
 rewrite rm_add_0_r in H.
 rewrite <- yyy in H.
 symmetry in H.
 rewrite rm_add_0_r in H.
 rewrite rm_add_comm, <- yyy, rm_add_0_r in H.
 symmetry in H.
 rewrite rm_add_comm, <- yyy, rm_add_0_r in H.
 rewrite rm_add_comm; symmetry.
 rewrite rm_add_comm; symmetry.
 assumption.
bbb.

intros a b c Hab.
remember (a + 0)%rm as a₁.
remember (b + 0)%rm as b₁.
remember (c + 0)%rm as c₁.
remember Heqa₁ as H; clear HeqH.
eapply zzz with (b₀ := b) (c₀ := c) in H; eauto .
 subst a₁ b₁ c₁.
 Focus 2.
 subst a₁ b₁.
 rewrite rm_add_0_r.
 rewrite rm_add_0_r.
 assumption.

bbb.
 etransitivity.

intros a b c Hab.
unfold rm_eq; simpl; intros i.
unfold rm_add_i; simpl.
do 2 rewrite xorb_false_r.
remember (fst_same (a + c) 0 (S i)) as sac eqn:Hsac .
remember (fst_same (b + c) 0 (S i)) as sbc eqn:Hsbc .
symmetry in Hsac, Hsbc.
apply fst_same_iff in Hsac.
apply fst_same_iff in Hsbc.
simpl in Hsac, Hsbc.
destruct sac as [diac| ].
 destruct Hsac as (Hnac, Hsac).
 destruct sbc as [dibc| ].
  destruct Hsbc as (Hnbc, Hsbc).
  rewrite Hsac, Hsbc.
  do 2 rewrite xorb_false_r.
bbb.
  unfold rm_add_i; simpl.
  remember (fst_same a c (S i)) as sac₁ eqn:Hsac₁ .
  remember (fst_same b c (S i)) as sbc₁ eqn:Hsbc₁ .
  symmetry in Hsac₁, Hsbc₁.
  apply fst_same_iff in Hsac₁.
  apply fst_same_iff in Hsbc₁.
  simpl in Hsac₁, Hsbc₁.
  destruct sac₁ as [diac₁| ].
   destruct Hsac₁ as (Hnac₁, Hsac₁).
   destruct sbc₁ as [dibc₁| ].
    destruct Hsbc₁ as (Hnbc₁, Hsbc₁).
bbb.
    unfold rm_eq in Hab; simpl in Hab.
    unfold rm_add_i in Hab; simpl in Hab.
bbb.

unfold rm_eq in Hab; simpl in Hab.
unfold rm_eq; simpl.
intros i.
unfold rm_add_i; simpl.
rewrite <- Hab.
remember (fst_same a c (S i)) as sac eqn:Hsac .
remember (fst_same b c (S i)) as sbc eqn:Hsbc .
symmetry in Hsac, Hsbc.
apply fst_same_iff in Hsac.
apply fst_same_iff in Hsbc.
destruct sac as [dja| ].
 destruct Hsac as (Hnac, Hsac).
 destruct sbc as [djc| ].
  rewrite <- Hab.
  destruct Hsbc as (Hnbc, Hsbc).
  destruct (lt_dec dja djc) as [H₁| H₁].
   apply Hnbc in H₁.
   rewrite <- Hab in H₁; contradiction.

   apply Nat.nlt_ge in H₁.
   destruct (lt_dec djc dja) as [H₂| H₂].
    apply Hnac in H₂.
    rewrite <- Hab in Hsbc.
    contradiction.

    apply Nat.nlt_ge in H₂.
    apply Nat.le_antisymm in H₁; auto.
    subst djc.
    reflexivity.

  pose proof (Hsbc dja) as H.
  rewrite <- Hab in H.
  contradiction.

 destruct sbc as [djc| ]; [ idtac | reflexivity ].
 destruct Hsbc as (Hnbc, Hsbc).
 pose proof (Hsac djc) as H.
 rewrite <- Hab in Hsbc.
 contradiction.
Qed.

Theorem rm_add_0_r : ∀ a, (a + 0 = a)%rm.
Proof.
intros a.
unfold rm_eq, rm_add_i; intros i; simpl.
unfold rm_eq; simpl.
unfold rm_add_i; simpl.
rewrite xorb_false_r.
remember (fst_same a 0 (S i)) as s eqn:Hs .
symmetry in Hs.
apply fst_same_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hsn, Hs).
 rewrite Hs.
 rewrite xorb_false_r; reflexivity.

 rewrite xorb_true_r.
bbb.

Theorem rm_add_assoc : ∀ a b c, (a + (b + c) = (a + b) + c)%rm.
Proof.
intros a b c.
unfold rm_eq; intros i; simpl.
unfold rm_add_i.
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
    unfold rm_add_i in Hs₁, Hs₂; simpl in Hs₁, Hs₂.
    remember (fst_same a b (S (S (i + di₂)))) as s₅ eqn:Hs₅ .
    remember (fst_same b c (S (S (i + di₁)))) as s₆ eqn:Hs₆ .
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
       unfold rm_add_i in H; simpl in H.
       remember (fst_same a b (S (S (i + di₁)))) as s₇ eqn:Hs₇ .
       symmetry in Hs₇.
       apply fst_same_iff in Hs₇.
       destruct s₇ as [di₇| ].
        simpl in Hs₇.
        destruct Hs₇ as (Hs₇n, Hs₇).
bbb.

Close Scope nat_scope.
