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
  match fst_same a b (S i) with
  | Some dj =>
      (* a[S i+di]=b[S i+di] *)
      if xorb a.[i] b.[i] then
        (* a[i]≠b[i] *)
        negb a.[S i + dj]
      else
        (* a[i]=b[i] *)
        xorb a.[i] a.[S i + dj]
  | None =>
      xorb a.[i] b.[i]
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
destruct sba as [di| ]; [ idtac | apply xorb_comm ].
rewrite xorb_comm.
remember (xorb b .[ i] a .[ i]) as xab eqn:Hxab .
symmetry in Hxab.
destruct Hsba as (_, Hsba); rewrite Hsba.
destruct xab; [ reflexivity | idtac ].
apply xorb_eq in Hxab.
rewrite Hxab; reflexivity.
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
destruct sa as [dia| ].
 destruct Hsa as (Hsan, Hsa).
 destruct sc as [dic| ].
  destruct Hsc as (Hscn, Hsc).
  remember (xorb a .[ i] (b + c) .[ i]) as xa eqn:Hxa .
  remember (xorb (a + b) .[ i] c .[ i]) as xc eqn:Hxc .
  symmetry in Hxa, Hxc.
  destruct xa.
   destruct xc.
    f_equal.
    rewrite Hsc.
bbb.

Close Scope nat_scope.
