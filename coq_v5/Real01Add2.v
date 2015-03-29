(* second version of adding reals in interval [0..1[ *)

Require Import Utf8 QArith NPeano.
Require Import Misc Summation.
Require Import Digit Real01.

Open Scope nat_scope.

Fixpoint int_pow a b :=
  match b with
  | 0 => 1
  | S b1 => a * int_pow a b1
  end.

Definition I_add_algo x y i := d2n (x.[i]) + d2n (y.[i]).
Arguments I_add_algo x%I y%I i%nat.

(* repeated in Real01Mul.v; to be unified *)
Definition z_of_u b n u i :=
  n2d (Σ (k = 0, n), u (i + k) * int_pow b (n - k) / int_pow b n mod b).

Definition I_add2_i x y := z_of_u base 2 (I_add_algo x y).
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

(* repeated in Real01Mul.v; to be unified *)
Theorem z_of_u_compat_l : ∀ b u v j n,
  (∀ i, u i = v i)
  → (z_of_u b n u j = z_of_u b n v j)%D.
Proof.
intros b u v j n Huv.
unfold z_of_u; simpl.
apply eq_digit_eq; f_equal.
apply summation_compat; intros i Hi.
rewrite Huv; reflexivity.
Qed.

Theorem I_add2_i_comm : ∀ x y i, (I_add2_i x y i = I_add2_i y x i)%D.
Proof.
intros x y i.
unfold I_add2_i; simpl.
apply z_of_u_compat_l.
apply I_add_algo_comm.
Qed.

Theorem I_add2_comm : ∀ x y, (x + y == y + x)%I.
Proof.
intros x y.
unfold I_eqs; intros i; simpl.
rewrite I_add2_i_comm.
reflexivity.
Qed.

(* 0 neutral element *)

Theorem d2n_lt_base : ∀ d, d2n d < 2.
Proof.
intros d.
unfold d2n; simpl.
destruct (Digit.dec d); [ apply Nat.lt_1_2 | apply Nat.lt_0_succ ].
Qed.

Theorem n2d_d2n : ∀ d, (n2d (d2n d) = d)%D.
Proof.
intros d.
unfold n2d, d2n; simpl.
destruct (Digit.dec d) as [H1| H1]; rewrite H1; reflexivity.
Qed.

Theorem I_add2_i_0_r : ∀ x i, (I_add2_i x 0 i = x.[i])%D.
Proof.
intros x i.
unfold I_add2_i; simpl.
rewrite z_of_u_compat_l.
 Focus 2.
 clear i; intros i.
 unfold I_add_algo; simpl.
 rewrite d2n_0, Nat.add_0_r.
 reflexivity.

 unfold z_of_u.
 unfold summation.
 remember div as f; remember modulo as g; simpl; subst f g.
 do 2 rewrite Nat.add_0_r; rewrite Nat.mul_1_r.
 rewrite Nat.div_mul; [ idtac | intros H; discriminate H ].
 rewrite Nat.mod_small; [ idtac | apply d2n_lt_base ].
 rewrite Nat.mod_small.
  rewrite Nat.div_small.
   rewrite Nat.add_0_l.
   rewrite Nat.mod_small.
    rewrite Nat.div_small; [ rewrite Nat.add_0_r; apply n2d_d2n | idtac ].
    eapply Nat.lt_trans; [ apply d2n_lt_base | idtac ].
    do 2 apply lt_n_S; apply Nat.lt_0_succ.

    rewrite Nat.div_small; [ apply Nat.lt_0_succ | idtac ].
    eapply Nat.lt_trans; [ apply d2n_lt_base | idtac ].
    do 2 apply lt_n_S; apply Nat.lt_0_succ.

   replace 4 with (2 * 2) by reflexivity.
   apply Nat.mul_lt_mono_pos_r; [ apply Nat.lt_0_succ | idtac ].
   apply d2n_lt_base.

  rewrite Nat.div_small; [ apply Nat.lt_0_succ | idtac ].
  replace 4 with (2 * 2) by reflexivity.
  apply Nat.mul_lt_mono_pos_r; [ apply Nat.lt_0_succ | idtac ].
  apply d2n_lt_base.
Qed.

Theorem I_add2_0_r : ∀ x, (x + 0 == x)%I.
Proof.
intros x i; simpl.
apply I_add2_i_0_r.
Qed.

(* associativity *)

Theorem d2n_n2d : ∀ n, d2n (n2d n) = if zerop n then 0 else 1.
Proof.
intros n.
unfold d2n, n2d.
destruct n; simpl.
 destruct (Digit.dec 0) as [H1| H1]; [ discr_digit H1 | reflexivity ].

 destruct (Digit.dec 1) as [H1| H1]; [ reflexivity | discr_digit H1 ].
Qed.

Theorem I_add_algo_le : ∀ x y i, I_add_algo x y i ≤ 2 * (base - 1).
Proof.
intros x y i; simpl.
unfold I_add_algo; simpl.
unfold d2n; simpl.
destruct (Digit.dec (x .[ i])) as [H1| H1].
 destruct (Digit.dec (y .[ i])) as [H2| H2]; [ reflexivity | idtac ].
 apply Nat.le_succ_diag_r.

 destruct (Digit.dec (y .[ i])) as [H2| H2]; [ idtac | apply Nat.le_0_l ].
 apply Nat.le_succ_diag_r.
Qed.

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

Theorem I_add_algo_assoc : ∀ x y z i,
  I_add_algo x (y + z) i = I_add_algo (x + y) z i.
Proof.
intros x y z i.
unfold I_add_algo; simpl.
unfold I_add2_i; simpl.
unfold z_of_u.
remember minus as h; remember div as f; remember modulo as g.
simpl; subst f g h.
unfold summation; simpl.
do 6 rewrite fold_sub_succ_l, divmod_mod.
do 6 rewrite divmod_div.
do 2 rewrite Nat.add_0_r, Nat.mul_1_r.
rewrite Nat.add_0_r.
do 2 rewrite Nat.add_assoc.
rewrite Nat.div_mul; [ idtac | intros H; discriminate H ].
rewrite Nat.div_mul; [ idtac | intros H; discriminate H ].
unfold I_add_algo; simpl.
unfold I_add2_i; simpl.
unfold z_of_u.
remember minus as h; remember div as f; remember modulo as g.
simpl; subst f g h.
unfold summation; simpl.
do 6 rewrite fold_sub_succ_l, divmod_mod.
do 4 rewrite divmod_div.
unfold d2n.
destruct (Digit.dec (x.[i])) as [H1| H1]; simpl.
 destruct (Digit.dec (y.[i])) as [H2| H2]; simpl.
  destruct (Digit.dec (z.[i])) as [H3| H3]; simpl.
   destruct (Digit.dec (x.[i+1])) as [H4| H4]; simpl.
    destruct (Digit.dec (y.[i+1])) as [H5| H5]; simpl.
     destruct (Digit.dec (z.[i+1])) as [H6| H6]; simpl.
      destruct (Digit.dec 1); reflexivity.

      destruct (Digit.dec (y.[i+2])) as [H7| H7]; simpl.
       destruct (Digit.dec (z.[i+2])) as [H8| H8]; simpl.
        destruct (Digit.dec 0) as [H9| H9].
         destruct (Digit.dec 1) as [H10| H10]; [ reflexivity | idtac ].
         discr_digit H10.

         destruct (Digit.dec 1) as [H10| H10]; [ idtac | reflexivity ].
bbb.
   i  i+1 i+2
x  1   1   .
y  1   1   1
z  1   0   1

remember (Digit.dec (x.[i+1])) as xi1 eqn:Hxi1.
remember (Digit.dec (y.[i+1])) as yi1 eqn:Hyi1.
remember (Digit.dec (z.[i+1])) as zi1 eqn:Hzi1.
remember minus as h; remember div as f; remember modulo as g.


remember (Digit.dec (x.[i])) as xi eqn:Hxi.
remember (Digit.dec (y.[i])) as yi eqn:Hyi.
remember (Digit.dec (z.[i])) as zi eqn:Hzi.
remember (Digit.dec (x.[i+1])) as xi1 eqn:Hxi1.
remember (Digit.dec (y.[i+1])) as yi1 eqn:Hyi1.
remember (Digit.dec (z.[i+1])) as zi1 eqn:Hzi1.
remember minus as h; remember div as f; remember modulo as g.
destruct xi, yi, zi, xi1, yi1, zi1; simpl; subst f g h; simpl.
 destruct (Digit.dec 1); reflexivity.

 rewrite divmod_div.

rewrite Nat.div_mul; [ idtac | intros H; discriminate H ].
rewrite Nat.div_mul; [ idtac | intros H; discriminate H ].
unfold I_add_algo; simpl.
unfold I_add2_i; simpl.
unfold z_of_u.

apply d2n_add_iff.


do 2 rewrite d2n_n2d.
remember (I_add_algo y z) as yz eqn:Hyz.
remember (yz i mod 2) as a1 eqn:Ha1.
remember ((yz (i + 1) * 2 / 4) mod 2) as a2 eqn:Ha2.
subst yz.
bbb.

unfold I_add2_i; simpl.
unfold z_of_u.
remember minus as h; remember div as f; remember modulo as g.
simpl; subst f g h.
unfold summation; simpl.
do 6 rewrite fold_sub_succ_l, divmod_mod.
do 6 rewrite divmod_div.
do 2 rewrite Nat.add_0_r, Nat.mul_1_r.
rewrite Nat.add_0_r.
do 2 rewrite Nat.add_assoc.
rewrite Nat.div_mul; [ idtac | intros H; discriminate H ].
rewrite Nat.div_mul; [ idtac | intros H; discriminate H ].
do 2 rewrite d2n_n2d.
remember (I_add_algo y z) as yz eqn:Hyz.
remember (yz i mod 2) as a1 eqn:Ha1.
remember ((yz (i + 1) * 2 / 4) mod 2) as a2 eqn:Ha2.
subst yz.
remember (I_add_algo x y) as xy eqn:Hxy.
remember (xy i mod 2) as a3 eqn:Ha3.
remember ((xy (i + 1) * 2 / 4) mod 2) as a4 eqn:Ha4.
subst xy.
rewrite Nat.div_small.
 Focus 2.
 eapply le_lt_trans; [ apply I_add_algo_le | unfold base; simpl ].
 apply Nat.le_le_succ_r; reflexivity.

 rewrite Nat.mod_small; [ rewrite Nat.add_0_r | apply Nat.lt_0_succ ].
 rewrite Nat.div_small.
  Focus 2.
  eapply le_lt_trans; [ apply I_add_algo_le | unfold base; simpl ].
  apply Nat.le_le_succ_r; reflexivity.

  rewrite Nat.mod_small; [ rewrite Nat.add_0_r | apply Nat.lt_0_succ ].
  destruct (zerop (a1 + a2)) as [H1| H1].
   rewrite Nat.add_0_r.
   apply Nat.eq_add_0 in H1.
   destruct H1 as (H1, H2).
   subst a1 a2.
   apply Nat.mod_divides in H1; [ idtac | intros H; discriminate H ].
   destruct H1 as (c1, Hc1).
   apply Nat.mod_divides in H2; [ idtac | intros H; discriminate H ].
   destruct H2 as (c2, Hc2).
   pose proof I_add_algo_le y z (i + 1) as H; simpl in H.
   apply Nat.mul_le_mono_r with (p := 2) in H; simpl in H.
   eapply Nat.div_le_mono with (c := 4) in H.
   2: intros I; discriminate I.
   rewrite Hc2 in H; simpl in H; rewrite Nat.add_0_r in H.
   destruct c2; [ clear H | exfalso; revert H; clear; intros; omega ].
   rewrite Nat.mul_0_r in Hc2.
   unfold I_add_algo in Hc1; simpl in Hc1.
   rewrite Nat.add_0_r in Hc1.
   unfold I_add_algo in Hc2; simpl in Hc2.
   rewrite divmod_div in Hc2.
bbb.
   apply d2n_add_eq in Hc1.
   apply d2n_add_eq in Hc1.

   destruct (zerop (a3 + a4)) as [H2| H2].
    rewrite Nat.add_0_l.
    apply Nat.eq_add_0 in H2.
    destruct H2 as (H1, H2).
    subst a3 a4.
    apply Nat.mod_divides in H1; [ idtac | intros H; discriminate H ].
    destruct H1 as (c3, Hc3).
    apply Nat.mod_divides in H2; [ idtac | intros H; discriminate H ].
    destruct H2 as (c4, Hc4).
    unfold I_add_algo in Hc3; simpl in Hc3.
    rewrite Nat.add_0_r in Hc3.
    unfold I_add_algo in Hc4; simpl in Hc4.
    rewrite Nat.add_0_r, divmod_div in Hc4.
    destruct c1; simpl in Hc1.
     apply Nat.eq_add_0 in Hc1.
     destruct Hc1 as (H1, H2).
     rewrite H1, Nat.add_0_r in Hc3; rewrite H2, Hc3.
     destruct c3; [ reflexivity | exfalso; simpl in Hc3 ].
     rewrite Nat.add_succ_r in Hc3.
     pose proof d2n_lt_base (x.[i]) as H.
     rewrite Hc3 in H.
     apply Nat.nle_gt in H; apply H.
     do 2 apply le_n_S; apply Nat.le_0_l.

     rewrite Nat.add_succ_r in Hc1.
     destruct c1; simpl in Hc1.
bbb.
*)

Theorem I_add_assoc : ∀ x y z, (x + (y + z) == (x + y) + x)%I.
Proof.
intros x y z.
unfold I_eqs; intros i; simpl.
unfold I_add2_i; simpl.
apply z_of_u_compat_l; clear i.
intros i; simpl.
bbb.
