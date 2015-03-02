(* I is complete *)

Require Import Utf8 QArith NPeano Misc.
Require Import Real01 Real01Cmp Real01Add.
Require Import Digit Real RealAdd RealAddGrp.

Open Scope nat_scope.

Definition I_abs_sub x y := if I_lt_dec x y then (y - x)%I else (x - y)%I.

Definition I_cauchy_sequence u :=
  ∀ ε, (ε ≠ 0)%I → ∃ N, ∀ p q, p > N → q > N → (I_abs_sub (u p) (u q) < ε)%I.

Definition I_converges_to u r :=
  ∀ ε, (ε ≠ 0)%I → ∃ N, ∀ n, n > N → (I_abs_sub r (u n) < ε)%I.

Definition R_cauchy_sequence u :=
  ∀ ε, (ε > 0)%R → ∃ N, ∀ p q, p > N → q > N → (R_abs (u p - u q) < ε)%R.

Axiom functional_choice :
  ∀ A B (P : A → B → Prop),
  (∀ x, ∃ y, P x y)
  → ∃ f, ∀ x, P x (f x).

Theorem R_lt_0_1 : (0 < 1)%R.
Proof.
unfold R_lt, R_compare; simpl.
rewrite carry_diag; simpl.
rewrite b2z_0; reflexivity.
Qed.

Definition R_max x y := if R_lt_dec x y then y else x.
Arguments R_max x%R y%R.

Fixpoint R_max_abs_seq_upto u n :=
  match n with
  | 0 => 0%R
  | S n1 => R_max (R_abs (u n)) (R_max_abs_seq_upto u n1)
  end.

Theorem R_lt_le_incl : ∀ x y, (x < y)%R → (x ≤ y)%R.
Proof.
intros x y Hxy.
unfold R_lt in Hxy; unfold R_le.
rewrite Hxy; intros H; discriminate H.
Qed.

Theorem R_le_max_l : ∀ x y, (x ≤ R_max x y)%R.
Proof.
intros x y.
unfold R_max.
destruct (R_lt_dec x y) as [H1| H1]; [ idtac | apply R_le_refl ].
apply R_lt_le_incl; assumption.
Qed.

Theorem R_lt_nle : ∀ x y, (x < y)%R ↔ ¬(y ≤ x)%R.
Proof.
intros x y.
split; intros Hxy.
 intros H.
 apply R_ge_le_iff in H.
 unfold R_lt in Hxy; unfold R_ge in H.
 rewrite Hxy in H; apply H; reflexivity.

 apply R_gt_lt_iff.
 unfold R_le in Hxy; unfold R_gt.
 remember (y ?= x)%R as c eqn:Hc.
 symmetry in Hc.
 destruct c; [ exfalso | exfalso | reflexivity ].
  apply Hxy; intros H; discriminate H.

  apply Hxy; intros H; discriminate H.
Qed.

Theorem R_lt_trans : ∀ x y z, (x < y)%R → (y < z)%R → (x < z)%R.
Proof.
intros x y z Hxy Hyz.
destruct (R_dec x y) as [H1| H1].
 rewrite H1 in Hxy; exfalso; revert Hxy; apply R_lt_irrefl.

 destruct (R_dec y z) as [H2| H2].
  rewrite H2 in Hyz; exfalso; revert Hyz; apply R_lt_irrefl.

  remember Hxy as Hxye; clear HeqHxye.
  remember Hyz as Hyze; clear HeqHyze.
  apply R_lt_le_incl in Hxye.
  apply R_lt_le_incl in Hyze.
  pose proof (R_le_trans x y z Hxye Hyze) as H.
  destruct (R_dec x z) as [H3| H3].
   rewrite <- H3 in Hyze.
   apply R_lt_nle in Hxy; contradiction.

   unfold R_le in H; unfold R_lt.
   remember (x ?= z)%R as c eqn:Hc.
   symmetry in Hc.
   destruct c; [ idtac | reflexivity | exfalso; apply H; reflexivity ].
   apply R_compare_eq in Hc; contradiction.
Qed.

Theorem R_lt_le_trans : ∀ x y z, (x < y)%R → (y ≤ z)%R → (x < z)%R.
Proof.
intros x y z Hxy Hyz.
destruct (R_dec y z) as [H1| H1]; [ rewrite <- H1; assumption | idtac ].
assert (y < z)%R as H.
 unfold R_le in Hyz; unfold R_lt.
 remember (y ?= z)%R as c eqn:Hc.
 symmetry in Hc.
 destruct c; [ idtac | reflexivity | exfalso; apply Hyz; reflexivity ].
 apply R_compare_eq in Hc.
 contradiction.

 eapply R_lt_trans.
bbb.

eapply R_le_trans in Hyz.

unfold R_lt in Hxy.
unfold R_le in Hyz.
unfold R_lt.
Check R_le_trans.
bbb.

Theorem R_le_pos_lt_compat : ∀ x y z, (x ≤ y)%R → (z > 0)%R → (x < y + z)%R.
Proof.
intros x y z Hxy Hz.
apply R_lt_le_trans.

unfold R_le in Hxy.
unfold R_gt in Hz.
unfold R_lt.

Theorem R_cauchy_sequence_bounded : ∀ u,
  R_cauchy_sequence u → ∃ m, ∀ n, (R_abs (u n) < m)%R.
Proof.
intros u Hc.
pose proof R_lt_0_1 as H.
apply R_gt_lt_iff in H.
apply Hc in H.
destruct H as (N, HN).
exists (R_max (R_max_abs_seq_upto u N) (R_abs (u (S N))) + 1)%R.
intros n.
destruct (le_dec n N) as [H1 | H1].
bbb.

(* to be completed *)
Theorem zzz : ∀ u, cauchy_sequence u → ∃ r, converges_to u r.
Proof.
intros u Hc.
unfold cauchy_sequence in Hc.
unfold converges_to.
(*
bbb.
*)

(*
apply functional_choice in Hc.
destruct Hc as (f, Hf).
bbb.
*)
