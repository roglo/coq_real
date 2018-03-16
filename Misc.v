Require Import Utf8 Arith.
Require List.
Import List.ListNotations.
Open Scope list_scope.

Notation "x < y <= z" := (x < y ∧ y <= z) (at level 70, y at next level).
Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y < z" := (x <= y ∧ y < z)%nat (at level 70, y at next level).

Theorem Nat_le_neq_lt : ∀ a b, a ≤ b → a ≠ b → a < b.
Proof.
intros a b Hab Hnab.
apply le_lt_eq_dec in Hab.
destruct Hab as [Hle| Heq]; [ assumption | idtac ].
exfalso; apply Hnab; assumption.
Qed.

Theorem list_Forall_inv : ∀ A (P : A → Prop) a l,
  List.Forall P (a :: l) → P a ∧ List.Forall P l.
Proof.
intros A P a l H.
inversion H; split; assumption.
Qed.

Theorem last_cons_id : ∀ A (a : A) al,
  List.last al a ≠ a
  → List.last (a :: al) a ≠ a.
Proof.
intros * Hal.
now destruct al.
Qed.

Theorem last_cons_cons : ∀ A (a b : A) al d,
  List.last (a :: b :: al) d = List.last (b :: al) d.
Proof. easy. Qed.

Theorem last_cons_ne : ∀ A (a d : A) al,
  a ≠ d
  → List.last al d ≠ d
  → List.last (a :: al) d ≠ d.
Proof.
intros * Had Hal.
revert a Had.
induction al as [| a1]; intros; [ easy | ].
rewrite last_cons_cons.
simpl in Hal.
destruct al as [| a2]; [ easy | ].
now rewrite last_cons_cons.
Qed.

Theorem List_cons_comm_app : ∀ A (x : A) l l', l ++ x :: l' = l ++ [x] ++ l'.
Proof. easy. Qed.

Theorem Nat_mod_same_l : ∀ a b, a ≠ 0 → (a + b) mod a = b mod a.
Proof.
intros * Ha.
rewrite <- Nat.add_mod_idemp_l; [ | easy ].
now rewrite Nat.mod_same.
Qed.

Theorem Nat_sqr_sub_1 : ∀ a, a ^ 2 - 1 = (a + 1) * (a - 1).
Proof.
intros; simpl.
rewrite Nat.mul_sub_distr_l.
do 2 rewrite Nat.mul_1_r.
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_1_l.
rewrite Nat.sub_add_distr.
now rewrite Nat.add_sub.
Qed.

Theorem Nat_sqr_sub_1_mod : ∀ a, (a ^ 2 - 1) mod a = a - 1.
Proof.
intros.
destruct (zerop a) as [Ha| Ha]; [ now subst a | ].
assert (Haz : a ≠ 0) by (now intros H; subst a).
rewrite Nat_sqr_sub_1.
rewrite <- Nat.mul_mod_idemp_l; [ | easy ].
replace (a + 1) with (1 + 1 * a) by now rewrite Nat.mul_1_l, Nat.add_comm.
rewrite Nat.mod_add; [ | easy ].
destruct a; [ easy | ].
rewrite Nat.sub_succ, Nat.sub_0_r.
destruct a; [ easy | ].
rewrite Nat.mod_1_l.
-rewrite Nat.mul_1_l.
 rewrite Nat.mod_small; [ easy | apply Nat.lt_succ_diag_r ].
-apply -> Nat.succ_lt_mono.
 apply Nat.lt_0_succ.
Qed.

Theorem Nat_sqr_sub_1_div : ∀ a, (a ^ 2 - 1) / a = a - 1.
Proof.
intros.
destruct (zerop a) as [Ha| Ha]; [ now subst a | ].
assert (Haz : a ≠ 0) by (now intros H; subst a).
specialize (Nat.div_mod (a ^ 2 - 1) a Haz) as H.
apply Nat.mul_cancel_r with (p := a); [ easy | ].
apply Nat.add_cancel_r with (p := (a ^ 2 - 1) mod a).
rewrite Nat.mul_comm in H.
rewrite <- H; simpl; rewrite Nat.mul_1_r.
rewrite <- Nat.pow_2_r.
rewrite Nat_sqr_sub_1_mod; simpl.
rewrite Nat.mul_1_r.
rewrite <- Nat.pow_2_r.
rewrite Nat_sqr_sub_1.
now rewrite Nat.mul_comm, Nat.mul_add_distr_l, Nat.mul_1_r.
Qed.

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

Theorem Nat_sub_sub_assoc : ∀ a b c,
  c ≤ b ≤ a + c
  → a - (b - c) = a + c - b.
Proof.
intros * (Hcb, Hba).
revert a c Hcb Hba.
induction b; intros.
-apply Nat.le_0_r in Hcb; subst c.
 now rewrite Nat.add_0_r.
-destruct c; [ now rewrite Nat.add_0_r | ].
 apply Nat.succ_le_mono in Hcb.
 rewrite Nat.add_succ_r in Hba.
 apply Nat.succ_le_mono in Hba.
 specialize (IHb a c Hcb Hba) as H1.
 rewrite Nat.sub_succ, H1.
 rewrite Nat.add_succ_r.
 now rewrite Nat.sub_succ.
Qed.

(*
Theorem Nat_sub_sub_assoc : ∀ a b c,
  c ≤ b ≤ a
  → a - (b - c) = a - b + c.
Proof.
intros * (Hcb, Hba).
revert a c Hcb Hba.
induction b; intros.
-now apply Nat.le_0_r in Hcb; subst c.
-destruct c; [ easy | ].
 destruct a; [ easy | ].
 apply Nat.succ_le_mono in Hcb.
 apply Nat.succ_le_mono in Hba.
 do 2 rewrite Nat.sub_succ.
 specialize (IHb a c Hcb Hba) as H.
 rewrite Nat.add_succ_r, <- H.
 rewrite <- Nat.sub_succ_l; [ easy | ].
 apply le_trans with (m := b); [ | easy ].
 apply Nat.le_sub_l.
Qed.
*)
