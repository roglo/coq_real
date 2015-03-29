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
   unfold I_add_algo in Hc1; simpl in Hc1.
   rewrite Nat.add_0_r in Hc1.
   unfold I_add_algo in Hc2; simpl in Hc2.
   rewrite Nat.add_0_r, divmod_div in Hc2.
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
bbb.

Theorem I_add_assoc : ∀ x y z, (x + (y + z) == (x + y) + x)%I.
Proof.
intros x y z.
unfold I_eqs; intros i; simpl.
unfold I_add2_i; simpl.
apply z_of_u_compat_l; clear i.
intros i; simpl.
bbb.
