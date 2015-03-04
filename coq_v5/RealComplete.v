(* I is complete *)

Require Import Utf8 QArith NPeano Misc.
Require Import Real01 Real01Cmp Real01AddMono Real01Add.
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

Theorem carry_0_0_r : ∀ x, (x ≠ 1)%I → (carry x 0 0 = 0)%D.
Proof.
intros x Hx.
unfold carry; simpl.
remember (fst_same x 0 0) as s1 eqn:Hs1.
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1|]; [ idtac | exfalso ].
destruct Hs1 as (Hn1, Ht1); assumption.
apply Hx; unfold I_eq; simpl.
unfold I_eq_ext; simpl; intros i.
unfold I_add_i; simpl.
rewrite Hs1; apply Digit.add_compat; [ reflexivity | idtac ].
unfold carry; simpl.
remember (fst_same x 0 (S i)) as s2 eqn:Hs2.
remember (fst_same 1 0 (S i)) as s3 eqn:Hs3.
destruct s2 as [dj2| ]; [ idtac | destruct s3; reflexivity ].
rewrite Hs1; destruct s3; reflexivity.
Qed.

Theorem R_lt_add_compat_r : ∀ x y z, (x < y)%R → (x + z < y + z)%R.
Proof.
intros x y z Hxy.
unfold R_lt in Hxy; unfold R_lt.
unfold R_compare in Hxy; unfold R_compare.
remember (R_norm x) as nx eqn:Hnx.
remember (R_norm y) as ny eqn:Hny.
remember (R_norm (x + z)) as nxz eqn:Hnxz.
remember (R_norm (y + z)) as nyz eqn:Hnyz.
remember (R_int nx ?= R_int ny)%Z as cmp1 eqn:Hcmp1.
remember (R_int nxz ?= R_int nyz)%Z as cmp2 eqn:Hcmp2.
symmetry in Hcmp1, Hcmp2.
remember (fst_same (R_frac nx) (- R_frac ny) 0) as s1 eqn:Hs1.
remember (fst_same (R_frac nxz) (- R_frac nyz) 0) as s2 eqn:Hs2.
destruct cmp1; [ idtac | clear Hxy | discriminate Hxy ].
 apply Z.compare_eq in Hcmp1.
 destruct s1 as [j1| ]; [| discriminate Hxy ].
 destruct (Digit.dec (R_frac nx .[ j1])) as [H1| H1].
  discriminate Hxy.

  clear Hxy.
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, Ht1).
  rewrite H1 in Ht1; rename H1 into Hnx1; rename Ht1 into Hny1.
  apply Digit.opp_sym in Hny1; rewrite Digit.opp_0 in Hny1.
  destruct cmp2; [ idtac | reflexivity | exfalso ].
   apply Z.compare_eq in Hcmp2.
   destruct s2 as [j2| ]; [ idtac | exfalso ].
    destruct (Digit.dec (R_frac nxz .[ j2])) as [H2| H2].
     2: reflexivity.
     exfalso.
     apply fst_same_sym_iff in Hs2; simpl in Hs2.
     destruct Hs2 as (Hn2, Ht2).
     rewrite H2 in Ht2; rename H2 into Hnxz2; rename Ht2 into Hnyz2.
     apply Digit.opp_sym in Hnyz2; rewrite Digit.opp_1 in Hnyz2.
     subst; simpl in *.
     remember (R_frac x) as xf eqn:Hxf.
     remember (R_frac y) as yf eqn:Hyf.
     remember (R_frac z) as zf eqn:Hzf.
     remember (R_int x) as xi eqn:Hxi.
     remember (R_int y) as yi eqn:Hyi.
     remember (R_int z) as zi eqn:Hzi.
     move xf after zf; move yf after zf.
     move xi before zf; move yi before xi; move zi before yi.
     move Hxf after Hyf; move Hxi before Hzf; move Hyi before Hxi.
     move Hzi before Hyi; move Hcmp1 after Hcmp2; move Hnxz2 after Hnyz2.
     move Hnx1 after Hnxz2; move Hny1 after Hnxz2.
     unfold I_add_i in Hnxz2; simpl in Hnxz2.
     unfold I_add_i in Hnxz2; simpl in Hnxz2.
     rewrite Digit.add_0_r in Hnxz2.
     unfold I_add_i in Hnyz2; simpl in Hnyz2.
     unfold I_add_i in Hnyz2; simpl in Hnyz2.
     rewrite Digit.add_0_r in Hnyz2.
     unfold I_add_i in Hnx1; simpl in Hnx1.
     rewrite Digit.add_0_r in Hnx1.
     unfold I_add_i in Hny1; simpl in Hny1.
     rewrite Digit.add_0_r in Hny1.
     rewrite <- Z.add_assoc, Z.add_comm, Z.add_assoc in Hcmp2.
     symmetry in Hcmp2.
     rewrite <- Z.add_assoc, Z.add_comm, Z.add_assoc in Hcmp2.
     symmetry in Hcmp2.
     apply Z.add_cancel_r in Hcmp2.
     destruct (I_eq_dec xf 1) as [H1| H1].
bbb.
unfold carry in *; simpl in *.
     remember (carry xf 0 0) as c1 eqn:Hc1.
     remember (carry yf 0 0) as c2 eqn:Hc2.
     remember (carry xf zf 0) as c3 eqn:Hc3.
     remember (carry yf zf 0) as c4 eqn:Hc4.
bbb.
     destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
      remember H1 as H; clear HeqH.
      apply Hn2 in H; rewrite Digit.opp_involutive in H.
      unfold I_add_i in H; simpl in H.
      rewrite Digit.add_0_r in H.
      unfold I_add_i in H; simpl in H.
bbb.

   Focus 2.
   apply Z.compare_gt_iff in Hc2.
   rewrite Hnyz, Hnxz in Hc2.
   unfold R_norm in Hc2; simpl in Hc2.
   rewrite Hnx, Hny in Hc1; simpl in Hc1.
   do 4 rewrite <- Z.add_assoc in Hc2.
   rewrite Z.add_comm in Hc2; apply Z.lt_gt in Hc2.
   rewrite Z.add_comm in Hc2; apply Z.gt_lt in Hc2.
   do 4 rewrite <- Z.add_assoc in Hc2.
   apply Z.add_lt_mono_l in Hc2.
   do 2 rewrite Z.add_assoc in Hc2.
   rewrite Z.add_shuffle0, <- Z.add_assoc in Hc2.


   rewrite Hc1 in Hc2.
   rewrite Hny in 

SearchAbout (_ = 1)%D.
  remember Hnx1 as H; clear HeqH.
Focus 1.
  eapply I_eq_neq_prop in H; [ idtac | idtac | eassumption ].
bbb.


destruct c1, c2; try reflexivity.
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

Theorem R_compare_add_compat_r : ∀ x y z, (x ?= y)%R = (x + z ?= y + z)%R.
Proof.
intros x y z.
remember (x ?= y)%R as c1 eqn:Hc1.
remember (x + z ?= y + z)%R as c2 eqn:Hc2.
symmetry in Hc1, Hc2.
destruct c1.
 apply R_compare_eq in Hc1.
 destruct c2; [ reflexivity | exfalso | exfalso ].
   apply R_compare_lt in Hc2.
   rewrite Hc1 in Hc2.
   revert Hc2; apply R_lt_irrefl.

   apply R_compare_gt in Hc2.
   rewrite Hc1 in Hc2.
   apply R_gt_lt_iff in Hc2.
   revert Hc2; apply R_lt_irrefl.

  apply R_compare_lt in Hc1.
  destruct c2; [ exfalso | reflexivity | exfalso ].
   apply R_compare_eq in Hc2.
   apply R_add_reg_r in Hc2.
   rewrite Hc2 in Hc1.
   revert Hc1; apply R_lt_irrefl.

   apply R_compare_gt in Hc2.
   apply R_gt_lt_iff in Hc2.
   apply R_lt_nle in Hc2.
   apply Hc2; clear Hc2.
   bbb.
apply R_lt_add_compat_r.

   Focus 2.
   apply R_compare_gt in Hc1.
   destruct c2; [ exfalso | exfalso | reflexivity ].
    apply R_compare_eq in Hc2.
    apply R_add_reg_r in Hc2.
    rewrite Hc2 in Hc1.
    apply R_gt_lt_iff in Hc1.
    revert Hc1; apply R_lt_irrefl.

    apply R_compare_lt in Hc2.


bbb.

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
