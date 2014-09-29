Require Import Utf8 QArith NPeano.

Set Implicit Arguments.

Open Scope nat_scope.

(* reals modulo 1 *)
Record real_mod_1 := { rm : nat → bool }.

Delimit Scope rm_scope with rm.
Arguments rm r%rm i%nat.
Notation "s .[ i ]" := (rm s i) (at level 1).

Axiom fst_same : real_mod_1 → real_mod_1 → nat → option nat.

Axiom fst_same_iff : ∀ a b i odi,
  fst_same a b i = odi ↔
  match odi with
  | Some di =>
      (∀ dj, dj < di → a.[i + dj] ≠ b.[i + dj])
      ∧ a.[i + di] = b.[i + di]
  | None =>
      ∀ dj, a.[i + dj] ≠ b.[i + dj]
  end.

Arguments fst_same a%rm b%rm i%nat.

Definition rm_eq a b := ∀ i, rm a i = rm b i.

Notation "a = b" := (rm_eq a b) : rm_scope.
Notation "a ≠ b" := (¬ rm_eq a b) : rm_scope.

Definition rm_add_i a b i :=
  xorb (xorb a.[i] b.[i])
  match fst_same a b (S i) with
  | Some dj => a.[S i + dj]
  | None => true
  end.

Arguments rm_add_i a%rm b%rm i%nat.

Definition rm_add a b := {| rm := rm_add_i a b |}.

Notation "a + b" := (rm_add a b) : rm_scope.

Theorem fst_same_comm : ∀ a b i, fst_same a b i = fst_same b a i.
Proof.
intros a b i.
apply fst_same_iff.
remember (fst_same b a i) as sba eqn:Hsba .
symmetry in Hsba.
apply fst_same_iff in Hsba.
destruct sba as [di| ].
 destruct Hsba as (Hns, Hs).
 split; [ idtac | symmetry; assumption ].
 intros dj Hdjn.
 intros H; symmetry in H; revert H.
 apply Hns; assumption.

 intros dj H.
 symmetry in H; revert H.
 apply Hsba.
Qed.

Theorem rm_add_comm : ∀ a b, (a + b = b + a)%rm.
Proof.
intros a b.
unfold rm_eq; intros i; simpl.
unfold rm_add_i.
rewrite fst_same_comm.
remember (fst_same b a (S i)) as sba eqn:Hsba .
symmetry in Hsba.
apply fst_same_iff in Hsba.
destruct sba as [di| ]; [ idtac | f_equal; apply xorb_comm ].
destruct Hsba; f_equal; auto; apply xorb_comm.
Qed.

Theorem eq_fst_same : ∀ a b i,
  a .[ i] = b .[ i] → fst_same a b i = Some 0.
Proof.
intros a b i Hab.
apply fst_same_iff; simpl.
rewrite Nat.add_0_r; split; auto.
intros dj Hdj.
exfalso; revert Hdj; apply Nat.nlt_0_r.
Qed.

Theorem rm_add_compat_r : ∀ a b c, (a = b)%rm → (a + c = b + c)%rm.
Proof.
intros a b c Hab.
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

Theorem rm_add_assoc : ∀ a b c, (a + (b + c) = (a + b) + c)%rm.
Proof.
intros a b c.
unfold rm_eq; intros i; simpl.
unfold rm_add_i.
remember (fst_same a (b + c) (S i)) as sa eqn:Hsa .
symmetry in Hsa.
remember (fst_same (a + b) c (S i)) as sc eqn:Hsc .
symmetry in Hsc.
apply fst_same_iff in Hsa.
apply fst_same_iff in Hsc.
destruct sa as [di_ab_c| ].
 destruct Hsa as (Hsan, Hsa).
 destruct sc as [di_a_bc| ].
  destruct Hsc as (Hscn, Hsc).
  rewrite Hsc.
  unfold rm_add, rm_add_i; simpl.
  remember (fst_same a b (S i)) as sab eqn:Hsab .
  remember (fst_same b c (S i)) as sbc eqn:Hsbc .
  symmetry in Hsab, Hsbc.
  apply fst_same_iff in Hsab.
  apply fst_same_iff in Hsbc.
  destruct sab as [di_ab| ].
   destruct Hsab as (Hsabn, Hsab).
   destruct sbc as [di_bc| ].
    destruct Hsbc as (Hsbcn, Hsbc).
    do 6 rewrite xorb_assoc.
    do 2 f_equal; symmetry.
    rewrite xorb_comm, xorb_assoc; f_equal.
    simpl in Hsbc; rewrite Hsbc.
    simpl in Hsa, Hsc.
    unfold rm_add_i in Hsa, Hsc; simpl in Hsa, Hsc.
    remember (fst_same b c (S (S (i + di_ab_c)))) as sbc₂ eqn:Hsbc₂ .
    remember (fst_same a b (S (S (i + di_a_bc)))) as sab₂ eqn:Hsab₂ .
    symmetry in Hsab₂, Hsbc₂.
    apply fst_same_iff in Hsab₂.
    apply fst_same_iff in Hsbc₂.
    destruct sab₂ as [di_ab₂| ].
     destruct sbc₂ as [di_bc₂| ].
      destruct Hsab₂ as (Hnab₂, Hsab₂).
      destruct Hsbc₂ as (Hnbc₂, Hsbc₂).
      simpl in Hsab₂, Hsbc₂.
bbb.

Close Scope nat_scope.
