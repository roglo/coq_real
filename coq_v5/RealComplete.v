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

Theorem R_compare_add_compat : ∀ x y z, (x ?= y)%R = (x + z ?= y + z)%R.
Proof.
intros x y z.
unfold R_compare.
remember (R_norm x) as nx eqn:Hnx.
remember (R_norm y) as ny eqn:Hny.
remember (R_norm z) as nz eqn:Hnz.
remember (R_norm (x + z)) as nxz eqn:Hnxz.
remember (R_norm (y + z)) as nyz eqn:Hnyz.
remember (R_int nx ?= R_int ny)%Z as c1 eqn:Hc1.
remember (R_int nxz ?= R_int nyz)%Z as c2 eqn:Hc2.
symmetry in Hc1, Hc2.
remember (fst_same (R_frac nx) (- R_frac ny) 0) as s1 eqn:Hs1.
remember (fst_same (R_frac nxz) (- R_frac nyz) 0) as s2 eqn:Hs2.
destruct c1, c2; try reflexivity.
 apply Z.compare_eq in Hc1.
 apply Z.compare_eq in Hc2.
 destruct s1 as [j1| ].
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, Ht1).
  destruct s2 as [j2| ].
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   destruct (Digit.dec (R_frac nx .[ j1])) as [H1| H1].
    destruct (Digit.dec (R_frac nxz .[ j2])) as [H2| H2]; auto; exfalso.
    subst; simpl in *.
    rewrite H2 in Ht2.
    apply Digit.opp_sym in Ht2; rewrite Digit.opp_0 in Ht2.
    rewrite H1 in Ht1.
    apply Digit.opp_sym in Ht1; rewrite Digit.opp_1 in Ht1.
    unfold I_add_i in H1; simpl in H1.
    unfold I_add_i in H2; simpl in H2.
    unfold I_add_i in Ht1; simpl in Ht1.
    unfold I_add_i in Ht2; simpl in Ht2.
    rewrite Digit.add_0_r in H1, H2, Ht1, Ht2.
    unfold I_add_i in H2; simpl in H2.
    unfold I_add_i in Ht2; simpl in Ht2.
    remember (R_frac x) as xf eqn:Hxf.
    remember (R_frac y) as yf eqn:Hyf.
    remember (R_frac z) as zf eqn:Hzf.
    remember (R_int x) as xi eqn:Hxi.
    remember (R_int y) as yi eqn:Hyi.
    remember (R_int z) as zi eqn:Hzi.
    move Hyf before Hxf; move yf before xf; move zf before yf.
    move xi before zf; move yi before xi; move zi before yi.
    move Hxi before Hzf; move Hyi before Hxi; move Hzi before Hyi.
    move H1 after H2; move Hc1 after Hc2.
    do 4 rewrite <- Z.add_assoc in Hc2.
    rewrite Z.add_comm in Hc2; symmetry in Hc2.
    rewrite Z.add_comm in Hc2; symmetry in Hc2.
    do 4 rewrite <- Z.add_assoc in Hc2.
    apply Z.add_reg_l in Hc2.
    rewrite Z.add_comm in Hc2; symmetry in Hc2.
    rewrite Z.add_comm in Hc2; symmetry in Hc2.
    move Ht1 before H1; move Ht2 before H2.
bbb.
*)

SearchAbout R_compare.

Theorem R_lt_sub_lt_add_l : ∀ x y z, (x - y < z)%R ↔ (x < y + z)%R.
Proof.
intros x y z.
split; intros Hxyz.
SearchAbout I_le.
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
