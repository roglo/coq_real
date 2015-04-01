(** second version of adding reals in interval [0..1[ *)

Require Import Utf8 QArith NPeano.
Require Import Misc Summation.
Require Import Digit2 Real012.

Open Scope nat_scope.

Fixpoint int_pow a b :=
  match b with
  | 0 => 1
  | S b1 => a * int_pow a b1
  end.

Definition I_add_algo x y i := d2n (x.[i]) + d2n (y.[i]).
Arguments I_add_algo x%I y%I i%nat.

Definition z_of_u b n u i :=
  n2d (Σ (k = 0, n), u (i + k) * int_pow b (n - k) / int_pow b n mod b).

Definition I_add2_i x y := z_of_u radix 2 (I_add_algo x y).
Definition I_add2 x y := {| rm := I_add2_i x y |}.
Arguments I_add2_i x%I y%I i%nat.
Arguments I_add2 x%I y%I.

Notation "x + y" := (I_add2 x y) : I_scope.

(* commutativity *)

Theorem I_add_algo_comm : ∀ x y, (∀ i, I_add_algo x y i = I_add_algo y x i).
Proof.
intros x y i.
unfold I_add_algo; simpl.
apply Nat.add_comm.
Qed.

Theorem z_of_u_compat_l : ∀ b u v i n,
  (∀ j, j ≤ n → u (i + j) = v (i + j))
  → z_of_u b n u i = z_of_u b n v i.
Proof.
intros b u v i n Huv.
unfold z_of_u.
unfold z_of_u; f_equal.
apply summation_compat; intros j (_, Hj).
f_equal; f_equal; f_equal.
apply Huv; assumption.
Qed.

Theorem I_add2_i_comm : ∀ x y i, I_add2_i x y i = I_add2_i y x i.
Proof.
intros x y i.
unfold I_add2_i; simpl.
apply z_of_u_compat_l; intros j Hj.
apply I_add_algo_comm.
Qed.

Theorem I_add2_comm : ∀ x y, (x + y == y + x)%I.
Proof.
intros x y.
unfold I_eqs; intros i; simpl.
rewrite I_add2_i_comm; reflexivity.
Qed.

(* 0 neutral element *)

Theorem I_add2_i_0_r : ∀ x i, (I_add2_i x 0 i = x.[i])%D.
Proof.
intros x i.
unfold I_add2_i; simpl.
rewrite z_of_u_compat_l with (v := λ k, d2n (x .[ k])).
 Focus 2.
 intros j Hj.
 unfold I_add_algo; simpl.
 rewrite d2n_0, Nat.add_0_r.
 reflexivity.

 unfold z_of_u, summation.
 rewrite Nat.sub_0_r; simpl.
 do 2 rewrite Nat.add_0_r, Nat.mul_1_r.
 rewrite Nat.div_mul.
  2: apply Nat.neq_mul_0; split; apply Digit.radix_neq_0.

  rewrite Nat.div_mul_cancel_r; try apply Digit.radix_neq_0.
  rewrite Nat.mod_small.
   2: apply Nat.mod_upper_bound, Digit.radix_neq_0.

   rewrite Nat.mod_small.
    rewrite Nat.mod_small.
     rewrite Nat.div_small; [ idtac | apply d2n_lt_radix ].
     rewrite Nat.div_small.
      rewrite Nat.add_0_r.
      apply n2d_d2n.

      eapply lt_trans.
       apply Nat.mod_upper_bound, Digit.radix_neq_0.

       apply le_lt_trans with (m := 1 * radix).
        rewrite Nat.mul_1_l; reflexivity.

        apply Nat.mul_lt_mono_pos_r.
         apply Digit.radix_gt_0.

         apply Digit.radix_gt_1.

     apply Nat.div_lt_upper_bound.
      apply Nat.neq_mul_0; split; apply Digit.radix_neq_0.

      apply lt_trans with (m := 1 * radix).
       rewrite Nat.mul_1_l; apply d2n_lt_radix.

       apply Nat.mul_lt_mono_pos_r; [ apply Digit.radix_gt_0 | idtac ].
       replace 1 with (1 * 1) by reflexivity.
       apply Nat.mul_lt_mono; apply Digit.radix_gt_1.

    apply Nat.div_lt_upper_bound; [ apply Digit.radix_neq_0 | idtac ].
    apply lt_trans with (m := 1 * radix).
     rewrite Nat.mul_1_l; apply d2n_lt_radix.

     apply Nat.mul_lt_mono_pos_r; [ apply Digit.radix_gt_0 | idtac ].
     apply Digit.radix_gt_1.
Qed.

Theorem I_add2_0_r : ∀ x, (x + 0 == x)%I.
Proof.
intros x i; simpl.
apply I_add2_i_0_r.
Qed.

(* associativity *)

Theorem I_add_algo_upper_bound : ∀ x y i, I_add_algo x y i ≤ 2 * (radix - 1).
Proof.
intros x y i; simpl.
unfold I_add_algo; simpl.
rewrite Nat.add_0_r, Nat.sub_1_r.
apply Nat.add_le_mono; apply Nat.lt_le_pred, d2n_lt_radix.
Qed.

(*
Theorem d2n_add_iff : ∀ d e n,
  d2n d + d2n e = n
  ↔ n = 0 ∧ (d = 0)%D ∧ (e = 0)%D ∨
    n = 1 ∧ (d = 0)%D ∧ (e = 1)%D ∨
    n = 1 ∧ (d = 1)%D ∧ (e = 0)%D ∨
    n = 2 ∧ (d = 1)%D ∧ (e = 1)%D.
Proof.
intros d e n.
split; intros H.
 unfold d2n in H; simpl in H.
 destruct (Digit.dec d) as [H1| H1]; rewrite H1.
  destruct (Digit.dec e) as [H2| H2]; rewrite H2, <- H.
   right; right; right; split; [ reflexivity | split; reflexivity ].

   right; right; left; split; [ reflexivity | split; reflexivity ].

  destruct (Digit.dec e) as [H2| H2]; rewrite H2, <- H.
   right; left; split; [ reflexivity | split; reflexivity ].

   left; split; [ reflexivity | split; reflexivity ].

 destruct H as [H| [H| [H| H]]]; destruct H as (Hn, (Hd, He)); subst n.
  apply eq_d2n_0 in Hd.
  apply eq_d2n_0 in He.
  rewrite Hd, He; reflexivity.

  apply eq_d2n_0 in Hd.
  apply eq_d2n_1 in He.
  rewrite Hd, He; reflexivity.

  apply eq_d2n_1 in Hd.
  apply eq_d2n_0 in He.
  rewrite Hd, He; reflexivity.

  apply eq_d2n_1 in Hd.
  apply eq_d2n_1 in He.
  rewrite Hd, He; reflexivity.
Qed.
*)

(*
Theorem d2n_add_div_2_radix : ∀ d e, (d2n d + d2n e) / (radix + radix) = 0.
Proof.
intros d e.
rewrite Nat.div_small; [ reflexivity | idtac ].
replace 4 with (2 + 2) by reflexivity.
apply Nat.add_lt_mono; apply d2n_lt_radix.
Qed.

Theorem Nat_mul_2_div_4 : ∀ n, n * 2 / 4 = n / 2.
Proof.
intros n.
replace 4 with (2 * 2) by reflexivity.
apply Nat.div_mul_cancel_r; intros H; discriminate H.
Qed.
*)

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

Theorem I_add_algo_assoc : ∀ x y z i,
  I_add_algo x (y + z) i = I_add_algo (x + y) z i.
Proof.
intros x y z i.
unfold I_add_algo; simpl.
unfold I_add2_i; simpl.
unfold z_of_u; fsimpl.
rewrite Nat.mul_1_r.
do 2 rewrite d2n_n2d.
unfold summation; simpl.
do 3 rewrite Nat.mul_1_r.
rewrite Nat.add_0_r.
rewrite Nat.div_mul.
 rewrite Nat.div_mul.
  rewrite Nat.div_mul_cancel_r; try apply Digit.radix_neq_0.
  rewrite Nat.div_mul_cancel_r; try apply Digit.radix_neq_0.
  do 2 rewrite I_add_algo_div_sqr_radix.
  rewrite Nat.mod_0_l; [ idtac | apply Digit.radix_neq_0 ].
  do 2 rewrite Nat.add_0_r.
  unfold I_add_algo; simpl.
  remember (d2n (x .[i])) as xi eqn:Hxi.
  remember (d2n (y .[i])) as yi eqn:Hyi.
  remember (d2n (z .[i])) as zi eqn:Hzi.
  remember (d2n (x .[i+1])) as xi1 eqn:Hxi1.
  remember (d2n (y .[i+1])) as yi1 eqn:Hyi1.
  remember (d2n (z .[i+1])) as zi1 eqn:Hzi1.
  destruct (lt_dec (yi1 + zi1) radix) as [H1| H1].
   rewrite Nat.div_small; [ idtac | assumption ].
   rewrite Nat.mod_0_l; [ rewrite Nat.add_0_r | apply Digit.radix_neq_0 ].
   rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
   destruct (lt_dec (xi1 + yi1) radix) as [H2| H2].
    rewrite Nat.div_small; [ idtac | assumption ].
    rewrite Nat.mod_0_l; [ rewrite Nat.add_0_r | apply Digit.radix_neq_0 ].
    rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
    destruct (lt_dec (yi + zi) radix) as [H3| H3].
     rewrite Nat.mod_small; [ idtac | assumption ].
     destruct (lt_dec (xi + yi) radix) as [H4| H4].
      rewrite Nat.mod_small; [ idtac | assumption ].
      apply Nat.add_assoc.

      apply Nat.nlt_ge in H4.
Abort. (*
bbb.
(* mouais, bin le théorème doit être faux... *)
*)

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
(*
remember (d2n (x .[ i + 3])) as xi3 eqn:Hxi3 .
remember (d2n (y .[ i + 3])) as yi3 eqn:Hyi3 .
remember (d2n (z .[ i + 3])) as zi3 eqn:Hzi3 .
*)
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
 remember ((yi2 + zi2) / radix) as a eqn:Ha.
 rewrite Nat.div_small in Ha; [ subst a | assumption ].
 rewrite Nat.add_0_r.
 destruct (lt_dec (xi2 + yi2) radix) as [H2| H2].
  remember ((xi2 + yi2) / radix) as a eqn:Ha.
  rewrite Nat.div_small in Ha; [ subst a | assumption ].
  rewrite Nat.add_0_r.
  destruct (lt_dec (yi1 + zi1) radix) as [H3| H3].
   remember ((yi1 + zi1) / radix) as a eqn:Ha.
   rewrite Nat.div_small in Ha; [ subst a | assumption ].
   rewrite Nat.add_0_r.
   remember ((yi1 + zi1) mod radix) as a eqn:Ha.
   rewrite Nat.mod_small in Ha; [ subst a | assumption ].
   rewrite Nat.add_assoc.
   destruct (lt_dec (xi1 + yi1) radix) as [H4| H4].
    remember ((xi1 + yi1) / radix) as a eqn:Ha.
    rewrite Nat.div_small in Ha; [ subst a | assumption ].
    rewrite Nat.add_0_r.
    remember ((xi1 + yi1) mod radix) as a eqn:Ha.
    rewrite Nat.mod_small in Ha; [ subst a | assumption ].
    reflexivity.

    apply Nat.nlt_ge in H4.
bbb.

do 6 rewrite d2n_add_div_4, Nat.add_0_r.
do 6 rewrite Nat_mul_2_div_4.
remember (d2n (x .[ i])) as xi eqn:Hxi .
remember (d2n (y .[ i])) as yi eqn:Hyi .
remember (d2n (z .[ i])) as zi eqn:Hzi .
remember (d2n (x .[ i + 1])) as xi1 eqn:Hxi1 .
remember (d2n (y .[ i + 1])) as yi1 eqn:Hyi1 .
remember (d2n (z .[ i + 1])) as zi1 eqn:Hzi1 .
remember (d2n (x .[ i + 2])) as xi2 eqn:Hxi2 .
remember (d2n (y .[ i + 2])) as yi2 eqn:Hyi2 .
remember (d2n (z .[ i + 2])) as zi2 eqn:Hzi2 .
do 4 rewrite d2n_n2d.
destruct (zerop ((yi + zi) mod 2 + ((yi1 + zi1) / 2) mod 2)) as [H1| H1].
 rewrite Nat.add_0_r.
 apply Nat.eq_add_0 in H1; destruct H1 as (H11, H12).
 apply Nat_add_mod_2 in H11.
 destruct (zerop ((yi1 + zi1) mod 2 + ((yi2 + zi2) / 2) mod 2)) as [H2| H2].
  rewrite Nat.add_0_r.
  apply Nat.eq_add_0 in H2; destruct H2 as (H21, H22).
  apply Nat_add_mod_2 in H21.
  destruct (zerop ((xi + yi) mod 2 + ((xi1 + yi1) / 2) mod 2)) as [H3| H3].
   rewrite Nat.add_0_l.
   apply Nat.eq_add_0 in H3; destruct H3 as (H31, H32).
   apply Nat_add_mod_2 in H31.
   rewrite H31, H11.
   destruct (zerop ((xi1 + yi1) mod 2 + ((xi2 + yi2) / 2) mod 2)) as [H4| H4].
    apply Nat.eq_add_0 in H4; destruct H4 as (H41, H42).
    apply Nat_add_mod_2 in H41.
    rewrite Nat.add_0_l.
    subst xi1 yi1 zi1.
    apply d2n_mod_radix in H21.
    apply d2n_mod_radix in H41.
    rewrite H41, H21; reflexivity.

    rewrite Hxi1.
    rewrite Nat.div_small; [ idtac | apply d2n_lt_radix ].
    rewrite Nat.mod_0_l; [ idtac | intros H; discriminate H ].
    rewrite Hyi, Hzi in H11.
    apply d2n_mod_radix in H11.
    rewrite <- Hyi, <- Hzi in H11.
    rewrite Hyi1, Hzi1 in H21.
    apply d2n_mod_radix in H21.
    rewrite <- Hyi1, <- Hzi1 in H21.
    rewrite Hxi, Hyi in H31.
    apply d2n_mod_radix in H31.
    rewrite <- Hxi, <- Hyi in H31.
    rewrite H21, Hzi1 in H12.
    unfold d2n in H12, Hzi1.
    destruct (Digit.dec (z .[ i + 1])) as [H5| H5].
     discriminate H12.

     rewrite Hzi1; reflexivity.

   destruct (zerop ((xi1 + yi1) mod 2 + ((xi2 + yi2) / 2) mod 2)) as [H4| H4].
bbb.

    rewrite Nat.add_0_l; reflexivity.

    destruct xi1; [ reflexivity | symmetry in Hxi1 ].
    destruct xi1; [ idtac | exfalso ].
     remember modulo as fmod; simpl; subst fmod.
     rewrite Nat.mod_0_l; [ rewrite Nat.add_0_r | intros H; discriminate H ].
     rewrite Nat.mod_small; [ idtac | subst xi; apply d2n_lt_radix ].
     rewrite Nat.mod_small; [ idtac | apply Nat.lt_1_2 ].
     destruct xi; [ exfalso; symmetry in Hxi | reflexivity ].
     apply Nat.eq_add_0 in H1; destruct H1 as (H11, H12).
     apply Nat_add_mod_2 in H11.
     apply Nat.eq_add_0 in H2; destruct H2 as (H21, H22).
     apply Nat_add_mod_2 in H21.
     apply Nat.eq_add_0 in H3; destruct H3 as (H31, H32).
     apply Nat_add_mod_2 in H31; symmetry in H31.
     rewrite Nat.mod_0_l in H31; [ idtac | intros H; discriminate H ].
     rewrite H31 in H11; symmetry in H11.
     unfold d2n in Hyi1.
     destruct (Digit.dec (y .[ i + 1])) as [H5| H5]; subst yi1.
      discriminate H32.

      clear H12 H32 H4.
bbb.
         i  i+1 i+2
x        0   1   .
y        0   0   .
z        0   0   .


(*
    rewrite Nat.add_mod in H4; [ idtac | intros H; discriminate H ].
*)

(*
Theorem zzz : ∀ d e, ((d2n d + d2n e) / 2) mod 2 = 0 → d = e.
Proof.
intros d e H.
unfold d2n in H.
destruct (Digit.dec d) as [H1| H1].
 destruct (Digit.dec e) as [H2| H2]; [ discriminate H | idtac ].
*)

bbb.

unfold d2n.
destruct (Digit.dec (x.[i])) as [H1| H1].
 destruct (Digit.dec (y.[i])) as [H2| H2].
  destruct (Digit.dec (z.[i])) as [H3| H3].
   destruct (Digit.dec (y.[i+1])) as [H4| H4].
    destruct (Digit.dec (z.[i+1])) as [H5| H5].
     simpl.
     do 14 rewrite divmod_div.
     destruct (Digit.dec 1) as [H6| H6]; [ clear H6; simpl | discr_digit H6 ].
     do 14 rewrite divmod_div.
     destruct (Digit.dec (x.[i+1])) as [H6| H6]; simpl.
bbb.
*)
(* label 1 *)
erewrite z_of_u_compat_l; [ reflexivity | intros j Hj ].
Abort. (*
bbb.
(*
  Hj : j ≤ 2
  ============================
   I_add_algo x (y + z) (i + j) = I_add_algo (x + y) x (i + j)
*)
*)
