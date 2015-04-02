(** second version of adding reals in interval [0..1[ *)

Require Import Utf8 QArith NPeano.
Require Import Misc Summation.
Require Import Digit2 Real012.

Open Scope nat_scope.

(* *)

Definition S_eq (u v : nat → nat) := ∀ i, u i = v i.
Definition S_add (u v : nat → nat) i := u i + v i.
Definition S_zero (i : nat) := 0.

Delimit Scope S_scope with S.
Notation "u = v" := (S_eq u v) : S_scope.
Notation "u + v" := (S_add u v) : S_scope.
Notation "0" := S_zero : S_scope.

Theorem S_add_comm : ∀ u v, (u + v = v + u)%S.
Proof. intros u v i; apply Nat.add_comm. Qed.

Theorem S_add_0_r : ∀ u, (u + 0 = u)%S.
Proof.
intros u i; simpl.
unfold S_add; simpl.
rewrite Nat.add_0_r.
reflexivity.
Qed.

Theorem S_add_assoc_i : ∀ u v w i, (u + (v + w))%S i = ((u + v) + w)%S i.
Proof. intros u v w i; apply Nat.add_assoc. Qed.

Theorem S_add_assoc : ∀ u v w, (u + (v + w) = (u + v) + w)%S.
Proof. intros u v w i; apply Nat.add_assoc. Qed.

Theorem S_eq_refl : reflexive _ S_eq.
Proof. intros u i; reflexivity. Qed.

Theorem S_eq_sym : symmetric _ S_eq.
Proof.
intros u v Huv i.
symmetry; apply Huv.
Qed.

Theorem S_eq_trans : transitive _ S_eq.
Proof.
intros u v w Huv Hvw i.
unfold I_eqs in Huv, Hvw.
rewrite Huv, Hvw; reflexivity.
Qed.

Add Parametric Relation : _ S_eq
 reflexivity proved by S_eq_refl
 symmetry proved by S_eq_sym
 transitivity proved by S_eq_trans
 as S_eq_rel.

Add Parametric Morphism : S_add
 with signature S_eq ==> S_eq ==> S_eq
 as S_add_compat.
Proof.
intros u v Huv w t Hwt i; unfold S_add.
rewrite Huv, Hwt; reflexivity.
Qed.

Add Parametric Morphism : rm
 with signature I_eqs ==> eq ==> digit_eq
 as rm_compat.
Proof. intros x y Hxy i; apply Hxy. Qed.

(* *)

Fixpoint int_pow a b :=
  match b with
  | 0 => 1
  | S b1 => a * int_pow a b1
  end.

Definition I2S x i := d2n (x.[i]).
Definition S2I n u :=
  {| rm i :=
       n2d
         (Σ (k = 0, n),
          u (i + k) * int_pow radix (n - k) / int_pow radix n mod radix) |}.

Definition I_add_algo x y := (I2S x + I2S y)%S.
Arguments I_add_algo x%I y%I i%nat.

Definition I_add2 x y := S2I 2 (I_add_algo x y).
Arguments I_add2 x%I y%I.

Notation "x + y" := (I_add2 x y) : I_scope.

Add Parametric Morphism : S2I
 with signature eq ==> S_eq ==> I_eqs
 as S2I_compat.
Proof.
intros n u v Huv i; simpl.
unfold digit_eq; simpl; f_equal.
apply summation_compat; intros j (_, Hj).
rewrite Huv; reflexivity.
Qed.

(* commutativity *)

Theorem I_add2_comm : ∀ x y, (x + y == y + x)%I.
Proof.
intros x y.
unfold I_eqs, I_add2, I_add_algo; intros i.
rewrite S_add_comm; reflexivity.
Qed.

(* 0 neutral element *)

Theorem I_zero_S_zero : (I2S 0%I = S_zero)%S.
Proof.
intros i.
unfold I2S; simpl.
unfold d2n; simpl.
rewrite Nat.mod_0_l; [ reflexivity | apply Digit.radix_neq_0 ].
Qed.

Theorem int_pow_neq_0 : ∀ a b, a ≠ 0 → int_pow a b ≠ 0.
Proof.
intros a b Ha.
induction b; [ intros H; discriminate H | simpl ].
apply Nat.neq_mul_0; split; assumption.
Qed.

Theorem I_add2_0_r : ∀ x, (x + 0 == x)%I.
Proof.
intros x.
unfold I_eqs, I_add2, I_add_algo; intros i.
rewrite I_zero_S_zero.
rewrite S_add_0_r.
unfold digit_eq, S2I; fsimpl.
unfold summation.
remember modulo as fmod; remember div as fdiv; simpl; subst fmod fdiv.
do 2 rewrite Nat.add_0_r, Nat.mul_1_r; fsimpl.
rewrite Nat.div_mul; [ idtac | apply radix_radix_neq_0 ].
rewrite Nat.div_mul_cancel_r; try apply Digit.radix_neq_0.
rewrite Nat.div_small; [ idtac | apply d2n_lt_radix ].
rewrite Nat.mod_0_l; [ idtac | apply Digit.radix_neq_0 ].
rewrite Nat.add_0_l.
rewrite Nat.div_small.
 rewrite Nat.mod_0_l; [ idtac | apply Digit.radix_neq_0 ].
 rewrite Nat.add_0_r.
 rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
 unfold I2S, d2n.
 rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
 reflexivity.

 eapply lt_le_trans.
  apply Nat.mod_upper_bound, Digit.radix_neq_0.

  remember (radix * radix) as a.
  replace radix with (radix * 1) by apply Nat.mul_1_r; subst a.
  apply Nat.mul_le_mono_l.
  apply Digit.radix_gt_0.
Qed.

(* associativity *)

Theorem I_add_algo_upper_bound : ∀ x y i, I_add_algo x y i ≤ 2 * (radix - 1).
Proof.
intros x y i; simpl.
unfold I_add_algo; simpl.
rewrite Nat.add_0_r, Nat.sub_1_r.
apply Nat.add_le_mono; apply Nat.lt_le_pred, d2n_lt_radix.
Qed.

Theorem I_add_algo_div_sqr_radix : ∀ x y i,
  I_add_algo x y i / (radix * radix) = 0.
Proof.
intros x y i.
rewrite Nat.div_small; [ reflexivity | idtac ].
eapply le_lt_trans; [ apply I_add_algo_upper_bound | idtac ].
rewrite Nat.sub_1_r.
eapply le_lt_trans with (m := radix * pred radix).
 apply Nat.mul_le_mono; [ apply radix_ge_2 | reflexivity ].

 apply Nat.mul_lt_mono_pos_l; [ apply Digit.radix_gt_0 | idtac ].
 apply Digit.pred_radix_lt_radix.
Qed.

Theorem double_radix_le_square_radix : radix + radix ≤ radix * radix.
Proof.
pose proof radix_ge_2 rad as H.
unfold radix.
remember (radix_value rad) as radix.
apply Nat.nlt_ge in H.
destruct radix as [| n]; [ exfalso; apply H, Nat.lt_0_succ | idtac ].
destruct n; [ exfalso; apply H, Nat.lt_1_2 | simpl ].
rewrite Nat.add_comm; simpl.
rewrite Nat.mul_comm; simpl.
do 2 rewrite Nat.add_succ_r; simpl.
do 4 apply le_n_S.
rewrite Nat.add_assoc.
apply Nat.le_sub_le_add_l.
rewrite Nat.sub_diag.
apply Nat.le_0_l.
Qed.

Theorem d2n_add_lt_sqr_radix : ∀ a b, d2n a + d2n b < radix * radix.
Proof.
intros a b.
eapply lt_le_trans; [ idtac | apply double_radix_le_square_radix ].
apply Nat.add_lt_mono; apply d2n_lt_radix.
Qed.

Theorem lt_radix_div_add_sqr_radix : ∀ a b,
  a < radix
  → b < radix
  → (a + b) / (radix * radix) = 0.
Proof.
intros a b Ha Hb.
rewrite Nat.div_small; [ reflexivity | idtac ].
eapply le_trans; [ apply Nat.add_lt_mono; eassumption | idtac ].
apply double_radix_le_square_radix.
Qed.

Theorem d2n_add_div_radix : ∀ a b,
  radix ≤ d2n a + d2n b
  → (d2n a + d2n b) / radix = 1.
Proof.
intros a b Hab.
remember (d2n a + d2n b - radix) as c eqn:Hc.
apply Nat_le_sub_add_r in Hc; [ idtac | assumption ].
replace radix with (1 * radix) in Hc by apply Nat.mul_1_l.
rewrite Hc, Nat.add_comm.
rewrite Nat.div_add; [ idtac | apply Digit.radix_neq_0 ].
rewrite Nat.div_small; [ reflexivity | idtac ].
rewrite Nat.mul_1_l in Hc.
apply Nat.add_lt_mono_l with (p := radix).
rewrite <- Hc.
apply Nat.add_lt_mono; apply d2n_lt_radix.
Qed.

Theorem d2n_add_mod_radix : ∀ a b,
  radix ≤ d2n a + d2n b
  → (d2n a + d2n b) mod radix = d2n a + d2n b - radix.
Proof.
intros a b Hab.
remember (d2n a + d2n b - radix) as c eqn:Hc.
apply Nat_le_sub_add_r in Hc; [ idtac | assumption ].
replace radix with (1 * radix) in Hc by apply Nat.mul_1_l.
rewrite Hc, Nat.add_comm.
rewrite Nat.mod_add; [ idtac | apply Digit.radix_neq_0 ].
rewrite Nat.mod_small; [ reflexivity | idtac ].
rewrite Nat.mul_1_l in Hc.
apply Nat.add_lt_mono_l with (p := radix).
rewrite <- Hc.
apply Nat.add_lt_mono; apply d2n_lt_radix.
Qed.

Theorem Nat_sub_div : ∀ a b, 0 < b ≤ a → (a - b) / b = pred (a / b).
Proof.
intros a b (Hb, Hba).
apply lt_0_neq, Nat.neq_sym in Hb.
remember (a - b) as c eqn:Hc.
apply Nat_le_sub_add_r in Hc; [ subst a | assumption ].
replace (b + c) with (c + 1 * b) by (rewrite Nat.mul_1_l; apply Nat.add_comm).
rewrite Nat.div_add; [ idtac | assumption ].
rewrite Nat.add_1_r, Nat.pred_succ.
reflexivity.
Qed.

Theorem Nat_mod_succ : ∀ a b, a mod b ≠ pred b → S a mod b = S (a mod b).
Proof.
intros a b Hab.
destruct b; [ exfalso; apply Hab; reflexivity | idtac ].
remember (a mod S b) as c eqn:Hc .
symmetry in Hc.
destruct c.
 apply Nat.mod_divides in Hc; [ idtac | intros H; discriminate H ].
 destruct Hc as (c, Hc).
 subst a; rewrite <- Nat.add_1_l, Nat.mul_comm.
 rewrite Nat.mod_add.
 destruct b; [ exfalso; apply Hab; reflexivity | idtac ].
  rewrite Nat.mod_small; [ reflexivity | idtac ].
  apply lt_n_S, Nat.lt_0_succ.

  intros H; discriminate H.

 rewrite <- Nat.add_1_r.
 rewrite <- Nat.add_mod_idemp_l; [ rewrite Hc | intros H; discriminate H ].
 rewrite Nat.mod_small; [ apply Nat.add_1_r | idtac ].
 rewrite Nat.pred_succ in Hab.
 simpl; apply lt_n_S; rewrite Nat.add_1_r.
 apply Nat_le_neq_lt; [ idtac | assumption ].
 apply le_S_n; rewrite <- Hc.
 apply Nat.mod_upper_bound.
 intros H; discriminate H.
Qed.

Theorem Nat_succ_div_sub : ∀ a b, 0 < b ≤ a → S ((a - b) / b) = a / b.
Proof.
intros a b (Hb, Hba).
remember (a - b) as c eqn:Hc.
apply Nat_le_sub_add_r in Hc; [ idtac | assumption ].
replace b with (1 * b) in Hc by apply Nat.mul_1_l; subst a.
rewrite Nat.add_comm.
rewrite Nat.div_add; [ symmetry; apply Nat.add_1_r | idtac ].
intros H; subst b; revert Hb; apply Nat.nlt_0_r.
Qed.

Theorem unfold_S2I : ∀ n u i,
  S2I n u .[i] =
  n2d (Σ (k = 0, n),
       (u (i + k) * int_pow radix (n - k) / int_pow radix n) mod radix).
Proof. reflexivity. Qed.

Theorem I_add_assoc : ∀ x y z, (x + (y + z) == (x + y) + z)%I.
Proof.
intros x y z i.
unfold I_add2.
unfold I_add_algo.
do 2 rewrite unfold_S2I.
unfold digit_eq; fsimpl.
rewrite Nat.mul_1_r.
(* osons *)
f_equal.
apply summation_compat.
intros j (_, Hj).
f_equal; f_equal; f_equal.
unfold S_add; simpl.
unfold I2S, S2I; fsimpl.
do 2 rewrite d2n_n2d.
rewrite Nat.mul_1_r.
unfold summation; simpl.
remember (i + j) as k.
do 3 rewrite Nat.add_0_r.
rewrite Nat.mul_1_r.
bbb.
cf ci-dessous.

Theorem I_add_assoc : ∀ x y z, (x + (y + z) == (x + y) + z)%I.
Proof.
intros x y z.
unfold I_eqs; intros i; simpl.
unfold I_add2_i; simpl.
unfold z_of_u.
unfold summation; rewrite Nat.sub_0_r; simpl.
do 3 rewrite Nat.add_0_r.
do 2 rewrite Nat.mul_1_r.
do 2 rewrite Nat.add_assoc.
do 2 (rewrite Nat.div_mul; [ idtac | apply radix_radix_neq_0 ]).
unfold I_add_algo; simpl.
unfold I_add2_i, z_of_u.
unfold summation; rewrite Nat.sub_0_r; simpl.
do 8 rewrite Nat.mul_1_r.
do 6 rewrite I_add_algo_div_sqr_radix.
unfold I_add_algo.
do 4 rewrite Nat.add_0_r.
do 4 rewrite <- Nat.add_assoc; simpl.
do 8 rewrite Nat.add_assoc.
remember (d2n (x .[ i])) as xi eqn:Hxi .
remember (d2n (y .[ i])) as yi eqn:Hyi .
remember (d2n (z .[ i])) as zi eqn:Hzi .
remember (d2n (x .[ i + 1])) as xi1 eqn:Hxi1 .
remember (d2n (y .[ i + 1])) as yi1 eqn:Hyi1 .
remember (d2n (z .[ i + 1])) as zi1 eqn:Hzi1 .
remember (d2n (x .[ i + 2])) as xi2 eqn:Hxi2 .
remember (d2n (y .[ i + 2])) as yi2 eqn:Hyi2 .
remember (d2n (z .[ i + 2])) as zi2 eqn:Hzi2 .
do 6 (rewrite Nat.div_mul; [ idtac | apply radix_radix_neq_0 ]).
do 8 (rewrite Nat.div_mul_cancel_r; try apply Digit.radix_neq_0).
rewrite Nat.mod_0_l; [ idtac | apply Digit.radix_neq_0 ].
do 6 rewrite Nat.add_0_r.
do 6 rewrite d2n_n2d.
rewrite Nat_lt_sqr_div_mod; [ idtac | subst; apply d2n_add_lt_sqr_radix ].
rewrite Nat_lt_sqr_div_mod.
 Focus 2.
 eapply lt_le_trans; [ idtac | apply double_radix_le_square_radix ].
 apply Nat.add_lt_mono; [ subst xi1; apply d2n_lt_radix | idtac ].
 apply Nat.mod_upper_bound, Digit.radix_neq_0.

 rewrite Nat_lt_sqr_div_mod; [ idtac | subst; apply d2n_add_lt_sqr_radix ].
 rewrite Nat_lt_sqr_div_mod; [ idtac | subst; apply d2n_add_lt_sqr_radix ].
 rewrite Nat_lt_sqr_div_mod; [ idtac | subst; apply d2n_add_lt_sqr_radix ].
 rewrite Nat_lt_sqr_div_mod.
  Focus 2.
  eapply lt_le_trans; [ idtac | apply double_radix_le_square_radix ].
  apply Nat.add_lt_mono; [ idtac | subst zi1; apply d2n_lt_radix ].
  apply Nat.mod_upper_bound, Digit.radix_neq_0.

  rewrite Nat_lt_sqr_div_mod; [ idtac | subst; apply d2n_add_lt_sqr_radix ].
  rewrite Nat_lt_sqr_div_mod; [ idtac | subst; apply d2n_add_lt_sqr_radix ].
  rewrite lt_radix_div_add_sqr_radix.
   2: rewrite Hxi2; apply d2n_lt_radix.

   2: apply Nat.mod_upper_bound, Digit.radix_neq_0.

   rewrite lt_radix_div_add_sqr_radix.
    2: apply Nat.mod_upper_bound, Digit.radix_neq_0.

    2: rewrite Hzi2; apply d2n_lt_radix.

    rewrite Nat.mod_0_l; [ idtac | apply Digit.radix_neq_0 ].
    do 2 rewrite Nat.add_0_r.
    rewrite Nat.add_mod_idemp_r; [ idtac | apply Digit.radix_neq_0 ].
    rewrite Nat.add_mod_idemp_l; [ idtac | apply Digit.radix_neq_0 ].
    rewrite Nat.add_mod_idemp_l; [ idtac | apply Digit.radix_neq_0 ].
    rewrite Nat.add_mod_idemp_l; [ idtac | apply Digit.radix_neq_0 ].
    rewrite Nat.add_assoc, Nat.add_shuffle0.
    rewrite Nat.add_mod_idemp_r; [ idtac | apply Digit.radix_neq_0 ].
    rewrite Nat.add_shuffle0, Nat.add_assoc; symmetry.
    rewrite <- Nat.add_assoc.
    rewrite Nat.add_mod_idemp_l; [ idtac | apply Digit.radix_neq_0 ].
    rewrite Nat.add_assoc, Nat.add_shuffle0.
    destruct (lt_dec (yi2 + zi2) radix) as [H1| H1].
     remember ((yi2 + zi2) / radix) as a eqn:Ha .
     rewrite Nat.div_small in Ha; [ subst a | assumption ].
     rewrite Nat.add_0_r.
     destruct (lt_dec (xi2 + yi2) radix) as [H2| H2].
      remember ((xi2 + yi2) / radix) as a eqn:Ha .
      rewrite Nat.div_small in Ha; [ subst a | assumption ].
      rewrite Nat.add_0_r.
      destruct (lt_dec (yi1 + zi1) radix) as [H3| H3].
       remember ((yi1 + zi1) / radix) as a eqn:Ha .
       rewrite Nat.div_small in Ha; [ subst a | assumption ].
       rewrite Nat.add_0_r.
       remember ((yi1 + zi1) mod radix) as a eqn:Ha .
       rewrite Nat.mod_small in Ha; [ subst a | assumption ].
       rewrite Nat.add_assoc.
       destruct (lt_dec (xi1 + yi1) radix) as [H4| H4].
        remember ((xi1 + yi1) / radix) as a eqn:Ha .
        rewrite Nat.div_small in Ha; [ subst a | assumption ].
        rewrite Nat.add_0_r.
        remember ((xi1 + yi1) mod radix) as a eqn:Ha .
        rewrite Nat.mod_small in Ha; [ subst a | assumption ].
        reflexivity.

        apply Nat.nlt_ge in H4.
        remember ((xi1 + yi1) / radix) as a eqn:Ha .
        rewrite Hxi1, Hyi1 in H4, Ha.
        rewrite d2n_add_div_radix in Ha; [ idtac | assumption ].
        rewrite <- Hxi1, <- Hyi1 in H4; subst a.
        remember ((xi1 + yi1) mod radix) as a eqn:Ha .
        rewrite Hxi1, Hyi1 in H4, Ha.
        rewrite d2n_add_mod_radix in Ha; [ idtac | assumption ].
        rewrite <- Hxi1, <- Hyi1 in H4, Ha; subst a.
        destruct (eq_nat_dec ((xi + yi + zi) mod radix) (pred radix))
         as [H5| H5].
         rewrite <- Nat.add_mod_idemp_l; [ idtac | apply Digit.radix_neq_0 ].
         rewrite H5, Nat.add_1_r.
         rewrite Nat.succ_pred; [ idtac | apply Digit.radix_neq_0 ].
         rewrite Nat.mod_same; [ idtac | apply Digit.radix_neq_0 ].
         rewrite Nat.add_0_l.
         rewrite Nat.add_comm.
         rewrite Nat.add_sub_assoc; [ idtac | assumption ].
         rewrite Nat_sub_div.
          2: split;
              [ apply Digit.radix_gt_0 | revert H4; clear; intros; omega ].

          rewrite Nat.add_comm.
          rewrite Nat.add_pred_l; [ idtac | apply Digit.radix_neq_0 ].
          symmetry; rewrite Nat.add_comm.
          unfold digit_eq; simpl.
          rewrite <- Nat.add_pred_l.
           rewrite Nat.add_mod; [ idtac | apply Digit.radix_neq_0 ].
           rewrite Nat.mod_same; [ idtac | apply Digit.radix_neq_0 ].
           rewrite Nat.add_0_r.
           rewrite Nat.mod_mod; [ reflexivity | apply Digit.radix_neq_0 ].

           intros H.
           remember (xi1 + yi1 - radix) as c eqn:Hc .
           apply Nat_le_sub_add_r in Hc; [ idtac | assumption ].
           replace radix with (1 * radix) in Hc by apply Nat.mul_1_l.
           rewrite Hc, <- Nat.add_assoc, Nat.add_comm in H.
           rewrite Nat.div_add in H; [ idtac | apply Digit.radix_neq_0 ].
           rewrite Nat.add_comm in H; discriminate H.

         rewrite Nat.add_1_r.
         rewrite Nat_mod_succ; [ idtac | assumption ].
         rewrite Nat.add_succ_l, <- Nat.add_succ_r.
         rewrite <- Nat.add_sub_swap; [ idtac | assumption ].
         rewrite Nat_succ_div_sub; [ reflexivity | idtac ].
         split; [ apply Digit.radix_gt_0 | idtac ].
         eapply le_trans; [ eassumption | idtac ].
         rewrite <- Nat.le_sub_le_add_l, Nat.sub_diag.
         apply Nat.le_0_l.

       apply Nat.nlt_ge in H3.
       destruct (lt_dec (xi1 + yi1) radix) as [H4| H4].
        remember ((xi1 + yi1) / radix) as a eqn:Ha .
        rewrite Nat.div_small in Ha; [ subst a | assumption ].
        rewrite Nat.add_0_r.
        remember ((xi1 + yi1) mod radix) as a eqn:Ha .
        rewrite Nat.mod_small in Ha; [ subst a | assumption ].
bbb.
