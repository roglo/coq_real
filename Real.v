Require Import Utf8 QArith NPeano.

Open Scope nat_scope.

(* reals modulo 1 *)
Record real_mod_1 := { rm : nat → bool }.

Axiom fst_same : real_mod_1 → real_mod_1 → nat → option nat.

Axiom fst_same_iff : ∀ x y i odi,
  fst_same x y i = odi ↔
  match odi with
  | Some di =>
      (∀ dj, dj < di → rm x (i + dj) ≠ rm y (i + dj))
      ∧ rm x (i + di) = rm y (i + di)
  | None =>
      ∀ dj, rm x (i + dj) ≠ rm y (i + dj)
  end.

Delimit Scope rm_scope with rm.

Definition rm_eq x y := ∀ i, rm x i = rm y i.

Notation "x = y" := (rm_eq x y) : rm_scope.
Notation "x ≠ y" := (¬ rm_eq x y) : rm_scope.

Definition rm_add_i x y i :=
  match fst_same x y i with
  | Some di =>
      (* x[i+di]=y[i+di] *)
      if zerop di then
        (* x[i]=y[i] *)
        match fst_same x y (S i) with
        | Some dj =>
            (* x[i+dj]=y[i+dj] *)
            xorb (rm x i) (rm x (S i + dj))
        | None =>
            false
        end
      else negb (rm x (i + di))
  | None =>
      true
  end.

Definition rm_add x y := {| rm := rm_add_i x y |}.

Notation "x + y" := (rm_add x y) : rm_scope.

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
 intros H; symmetry in H; revert H.
 apply Hns; assumption.

 intros dj H.
 symmetry in H; revert H.
 apply Hsyx.
Qed.

Theorem rm_add_comm : ∀ x y, (x + y = y + x)%rm.
Proof.
intros x y.
unfold rm_eq; intros i; simpl.
unfold rm_add_i.
rewrite fst_same_comm.
remember (fst_same y x i) as syx eqn:Hsyx .
symmetry in Hsyx.
apply fst_same_iff in Hsyx.
destruct syx as [di| ]; auto.
destruct Hsyx as (Hns, Hs).
destruct (zerop di) as [H₁| H₁]; [ idtac | rewrite Hs; reflexivity ].
rewrite fst_same_comm.
remember (fst_same y x (S i)) as syxs eqn:Hsyxs .
symmetry in Hsyxs.
apply fst_same_iff in Hsyxs.
destruct syxs as [dis| ]; auto.
destruct Hsyxs as (Hnss, Hss).
subst di; rewrite Nat.add_0_r in Hs.
rewrite Hs; f_equal; symmetry; assumption.
Qed.

Theorem fst_same_assoc : ∀ x y z i,
  fst_same x (y + z)%rm i = fst_same (x + y)%rm z i.
Proof.
intros x y z i.
apply fst_same_iff.
remember (fst_same (x + y)%rm z i) as sxy eqn:Hsxy .
symmetry in Hsxy.
apply fst_same_iff in Hsxy.
destruct sxy as [di| ].
 destruct Hsxy as (Hne, Heq).
 split.
  intros dj Hdji.
  remember Hdji as H; clear HeqH.
  apply Hne in H.
  intros H₁; apply H; clear H; rename H₁ into H.
  rewrite rm_add_comm in H.
  unfold rm_add, rm_add_i in H; simpl in H.
  unfold rm_add, rm_add_i; simpl.
  remember (fst_same z y (i + dj)) as syz eqn:Hsyz .
  symmetry in Hsyz.
  apply fst_same_iff in Hsyz.
  destruct syz as [diy| ].
   Focus 1.
   destruct (zerop diy) as [H₁| H₁].
    Focus 1.
    subst diy.
    destruct Hsyz as (Hyne, Hyeq).
    remember (fst_same z y (S (i + dj))) as syij eqn:Hsyij .
    symmetry in Hsyij.
    apply fst_same_iff in Hsyij.
    destruct syij as [dj₁| ].
     Focus 1.
     destruct Hsyij as (Hyine, Hyieq).
     rewrite Nat.add_0_r in Hyeq.
     clear Hyne.
     simpl in Hyieq.
     rewrite Hyieq, Hyeq in H.
     remember (fst_same x y (i + dj)) as sxy eqn:Hsxy .
     symmetry in Hsxy.
     apply fst_same_iff in Hsxy.
     destruct sxy as [dix| ].
      destruct (zerop dix) as [H₁| H₁].
       subst dix.
       rewrite Nat.add_0_r in Hsxy.
       destruct Hsxy as (Hxne, Hxeq).
       remember (fst_same x y (S (i + dj))) as sxij eqn:Hsxij .
       symmetry in Hsxij.
       apply fst_same_iff in Hsxij.
       destruct sxij as [dix| ].
        destruct Hsxij as (Hxine, Hxieq).
        simpl in Hxieq.
        rewrite Hxieq.
        symmetry.
        rewrite Hyeq, <- Hxeq.
bbb.

Theorem rm_add_assoc : ∀ x y z, (x + (y + z) = (x + y) + z)%rm.
Proof.
intros x y z.
unfold rm_eq; intros i; simpl.
unfold rm_add_i.
bbb.

Close Scope nat_scope.
