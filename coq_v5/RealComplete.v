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

Theorem R_le_max_l : ∀ x y, (x ≤ R_max x y)%R.
Proof.
intros x y.
unfold R_max.
destruct (R_lt_dec x y) as [H1| H1]; [ idtac | apply R_le_refl ].
apply R_lt_le_incl; assumption.
Qed.

Theorem R_lt_sub_lt_add_l : ∀ x y z, (x - y < z)%R ↔ (x < y + z)%R.
Proof.
intros x y z.
split; intros Hxyz.
bbb.

Theorem R_le_pos_lt_compat : ∀ x y z, (x ≤ y)%R → (z > 0)%R → (x < y + z)%R.
Proof.
intros x y z Hxy Hz.
eapply R_le_lt_trans; [ eassumption | idtac ].
SearchAbout (_ < _ + _)%Z.
bbb.

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
