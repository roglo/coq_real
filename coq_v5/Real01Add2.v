(** second version of adding reals in interval [0..1[ *)

Require Import Utf8 QArith NPeano.
Require Import Misc Summation.
Require Import Digit2 Real012.

Open Scope nat_scope.

(* addition numbers with numbers *)

Definition NN_eq (u v : nat → nat) := ∀ i, u i = v i.
Definition NN_add (u v : nat → nat) i := u i + v i.
Definition NN_zero (i : nat) := 0.

Delimit Scope NN_scope with NN.
Notation "u = v" := (NN_eq u v) : NN_scope.
Notation "u + v" := (NN_add u v) : NN_scope.
Notation "0" := NN_zero : NN_scope.

Theorem NN_add_comm : ∀ u v, (u + v = v + u)%NN.
Proof. intros u v i; apply Nat.add_comm. Qed.

Theorem NN_add_0_r : ∀ u, (u + 0 = u)%NN.
Proof.
intros u i; simpl.
unfold NN_add; simpl.
rewrite Nat.add_0_r.
reflexivity.
Qed.

Theorem NN_eq_refl : reflexive _ NN_eq.
Proof. intros u i; reflexivity. Qed.

Theorem NN_eq_sym : symmetric _ NN_eq.
Proof.
intros u v Huv i.
symmetry; apply Huv.
Qed.

Theorem NN_eq_trans : transitive _ NN_eq.
Proof.
intros u v w Huv Hvw i.
unfold I_eqs in Huv, Hvw.
rewrite Huv, Hvw; reflexivity.
Qed.

Add Parametric Relation : _ NN_eq
 reflexivity proved by NN_eq_refl
 symmetry proved by NN_eq_sym
 transitivity proved by NN_eq_trans
 as NN_eq_rel.

Theorem NN_add_compat : ∀ u v w x,
  (u = v)%NN
  → (w = x)%NN
  → (u + w = v + x)%NN.
Proof.
intros u v w x Huv Hwx i; unfold NN_add.
rewrite Huv, Hwx; reflexivity.
Qed.

Add Parametric Morphism : NN_add
 with signature NN_eq ==> NN_eq ==> NN_eq
 as NN_add_morph.
Proof.
intros u v Huv w t Hwt.
apply NN_add_compat; assumption.
Qed.

Theorem rm_compat : ∀ x y i, (x == y)%I → (x .[i] = y .[i])%D.
Proof. intros x y i Hxy; apply Hxy. Qed.

Add Parametric Morphism : rm
 with signature I_eqs ==> eq ==> digit_eq
 as rm_morph.
Proof. intros; apply rm_compat; assumption. Qed.

(* addition numbers with digits *)

Fixpoint int_pow a b :=
  match b with
  | 0 => 1
  | S b1 => a * int_pow a b1
  end.

Definition I2NN x i := d2n (x.[i]).
Definition NN2I n u :=
  let b := radix in
  {| rm i :=
       let s := Σ (k = 0, n), (u (i + k) * int_pow b (n - k)) in
       n2d (s / int_pow b n mod b) |}.

Definition I_add_algo x y := (I2NN x + I2NN y)%NN.
Arguments I_add_algo x%I y%I i%nat.

Definition I_add2 x y := NN2I 2 (I_add_algo x y).
Arguments I_add2 x%I y%I.

Notation "x + y" := (I_add2 x y) : I_scope.

Theorem NN2I_compat : ∀ n u v,
  (u = v)%NN
  → (NN2I n u == NN2I n v)%I.
Proof.
intros n u v Huv i; simpl.
unfold digit_eq; simpl; f_equal; f_equal; f_equal.
apply summation_compat; intros j (_, Hj).
rewrite Huv; reflexivity.
Qed.

Add Parametric Morphism : NN2I
 with signature eq ==> NN_eq ==> I_eqs
 as NN2I_morph.
Proof. intros; apply NN2I_compat; assumption. Qed.

(* commutativity *)

Theorem I_add2_comm : ∀ x y, (x + y == y + x)%I.
Proof.
intros x y.
unfold I_eqs, I_add2, I_add_algo; intros i.
rewrite NN_add_comm; reflexivity.
Qed.

(* 0 neutral element *)

Theorem I_zero_NN_zero : (I2NN 0%I = NN_zero)%NN.
Proof.
intros i.
unfold I2NN; simpl.
unfold d2n; simpl.
rewrite Nat.mod_0_l; [ reflexivity | apply Digit.radix_neq_0 ].
Qed.

Theorem radix_le_sqr_radix : radix ≤ radix * radix.
Proof.
remember (radix * radix) as a.
replace radix with (1 * radix) by apply Nat.mul_1_l; subst a.
apply Nat.mul_le_mono_r, Digit.radix_gt_0.
Qed.

Theorem I_add2_0_r : ∀ x, (x + 0 == x)%I.
Proof.
intros x.
unfold I_eqs, I_add2, I_add_algo; intros i.
rewrite I_zero_NN_zero.
rewrite NN_add_0_r.
unfold digit_eq, NN2I, I2NN; fsimpl.
unfold summation.
remember modulo as fmod; remember div as fdiv; simpl; subst fmod fdiv.
do 2 rewrite Nat.add_0_r, Nat.mul_1_r; fsimpl.
rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
rewrite Nat.div_add_l; [ idtac | apply radix_radix_neq_0 ].
rewrite Nat.div_small.
 rewrite Nat.add_0_r; unfold d2n.
 rewrite Nat.mod_mod; [ reflexivity | apply Digit.radix_neq_0 ].

 apply le_lt_trans with (m := pred radix * radix + pred radix).
  apply Nat.add_le_mono; [ idtac | apply le_d2n_1 ].
  apply Nat.mul_le_mono_r, le_d2n_1.

  rewrite <- Nat.sub_1_r.
  rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
  rewrite Nat.add_sub_assoc; [ idtac | apply Digit.radix_gt_0 ].
  rewrite Nat.sub_add; [ idtac | apply radix_le_sqr_radix ].
  rewrite Nat.sub_1_r.
  apply Nat.lt_pred_l, radix_radix_neq_0.
Qed.

(* compatibility with == *)

Theorem I_add2_compat_r : ∀ x y z, (x == y)%I → (x + z == y + z)%I.
Proof.
intros x y z Hxy i.
unfold I_add2, I_add_algo.
unfold I2NN, NN2I, NN_add; fsimpl.
rewrite Nat.mul_1_r.
unfold summation.
rewrite Nat.sub_0_r; simpl.
do 3 rewrite Nat.add_0_r.
do 3 rewrite Nat.mul_1_r.
unfold I_eqs in Hxy.
unfold d2n.
do 3 rewrite Hxy; reflexivity.
Qed.

Theorem I_add2_compat : ∀ x y z t,
  (x == y)%I
  → (z == t)%I
  → (x + z == y + t)%I.
Proof.
intros x y z t Hxy Hzt.
rewrite I_add2_compat_r; [ idtac | eassumption ].
rewrite I_add2_comm; symmetry.
rewrite I_add2_comm; symmetry.
apply I_add2_compat_r; assumption.
Qed.

Add Parametric Morphism : I_add2
 with signature I_eqs ==> I_eqs ==> I_eqs
 as I_add2_morph.
Proof. intros; apply I_add2_compat; assumption. Qed.

(* associativity *)

Theorem I_add_algo_upper_bound : ∀ x y i, I_add_algo x y i ≤ 2 * (radix - 1).
Proof.
intros x y i; simpl.
unfold I_add_algo; simpl.
rewrite Nat.add_0_r, Nat.sub_1_r.
apply Nat.add_le_mono; apply Nat.lt_le_pred, d2n_lt_radix.
Qed.

Theorem I_add_algo_div_sqr_radix : ∀ x y i,
  (d2n (x .[i]) + d2n (y .[i])) / (radix * radix) = 0.
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

Theorem summation_add_mod : ∀ b e f r,
  r ≠ 0
  → (Σ (i = b, e), (f i)) mod r =
    (Σ (i = b, e), (f i mod r)) mod r.
Proof.
intros b e f r Hr.
unfold summation.
remember (S e - b) as len.
clear e Heqlen.
revert b.
induction len; intros; [ reflexivity | simpl ].
rewrite Nat.add_mod; [ idtac | assumption ].
rewrite IHlen.
rewrite <- Nat.add_mod; [ idtac | assumption ].
rewrite Nat.add_mod_idemp_l; [ reflexivity | assumption ].
Qed.

(* is it true? *)
Theorem zzzz : ∀ x u i,
  (∀ j, u j ≤ 2 * pred radix)
  → (NN2I 2 (I2NN x + I2NN (NN2I 2 u))%NN .[ i] =
     NN2I 2 (I2NN x + u)%NN .[ i])%D.
Proof.
intros x u i Hu.
unfold NN2I, I2NN, NN_add; fsimpl.
unfold digit_eq; fsimpl.
rewrite Nat.mul_1_r.
erewrite summation_compat.
 Focus 2.
 intros j (_, Hj).
 rewrite d2n_n2d.
 unfold summation.
 rewrite Nat.sub_0_r; fsimpl.
 remember (i + j) as k.
 remember (int_pow radix (2 - j)) as a; simpl; subst a.
 do 3 rewrite Nat.add_0_r.
 do 2 rewrite Nat.mul_1_r.
 remember (plus (d2n (x .[ k]))) as a.
 rewrite Nat.add_comm; subst a.
 rewrite Nat.div_add; [ idtac | apply radix_radix_neq_0 ].
 rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
 subst k; reflexivity.

 do 2 (rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ]).
 erewrite summation_compat.
  2: intros; rewrite Nat.add_0_r; reflexivity.

  fsimpl.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite Nat.sub_0_r; fsimpl.
  rewrite Nat.mul_1_r, Nat.add_0_r.
  rewrite Nat.div_add_l; [ idtac | apply radix_radix_neq_0 ].
  symmetry.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite Nat.sub_0_r; fsimpl.
  rewrite Nat.mul_1_r, Nat.add_0_r.
  rewrite <- Nat.add_assoc; fsimpl.
  rewrite Nat.add_assoc.
  rewrite Nat.div_add_l; [ idtac | apply radix_radix_neq_0 ].
  do 2 rewrite <- Nat.add_assoc.
  rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
  rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
  f_equal; f_equal.
  symmetry.
  remember (d2n (x .[ i])) as xi eqn:Hxi .
  remember (u i) as ui eqn:Hui .
  remember (d2n (x .[ i + 1])) as xi1 eqn:Hxi1 .
  remember (u (i + 1)) as ui1 eqn:Hui1 .
  remember (d2n (x .[ i + 2])) as xi2 eqn:Hxi2 .
  remember (u (i + 2)) as ui2 eqn:Hui2 .
  remember ((ui1 * radix + ui2) / (radix * radix)) as a.
  remember ((a + ui) mod radix) as b eqn:Hb .
  rewrite Nat.add_mod in Hb; [ idtac | apply Digit.radix_neq_0 ].
  symmetry.
  rewrite Nat.add_mod; [ idtac | apply Digit.radix_neq_0 ].
  symmetry; subst b.
  rewrite Nat.add_mod_idemp_l; [ idtac | apply Digit.radix_neq_0 ].
  rewrite Nat.add_shuffle0, Nat.add_comm.
  rewrite <- Nat.add_mod_idemp_r; [ idtac | apply Digit.radix_neq_0 ].
  f_equal; f_equal; subst a.
  remember (radix * radix) as rr.
  remember (((ui1 * radix + ui2) / rr) mod radix) as a eqn:Ha .
  subst rr.
  rewrite Nat.mod_small in Ha.
  (* subgoal 2 à vérifier *)
(*
2(r-1)r+(r-1)=(r-1)(2r+1)=2r²-r-1
r³-2r²+r+1
f' = 3r²-2r+1
Δ' = 1-3 = -2
f'' = 6r-2 = 3(r-1)
donc r₃-2r²+r+1 > 0 donc en principe c'est bon
*)
subst a.
Set Printing Depth 11. Show.
remember (radix * radix) as rr.
rewrite Nat.add_comm.
unfold summation; simpl.
Set Printing Depth 16. Show.
do 2 rewrite Nat.add_assoc.
do 3 rewrite Nat.mul_1_r.
do 2 rewrite Nat.add_0_r.
rewrite <- Hxi2, <- Hui2, <- Hxi1, <- Hui1.
do 2 rewrite Nat.add_assoc.
do 2 rewrite Nat.mul_add_distr_r.
do 8 rewrite <- Nat.add_assoc; simpl.
do 4 rewrite Nat.add_assoc.
Set Printing Depth 24. Show.
rewrite <- Hui2.
remember (d2n (x .[ i + 3])) as xi3 eqn:Hxi3 .
remember (u (i + 3)) as ui3 eqn:Hui3 .
remember (d2n (x .[ i + 4])) as xi4 eqn:Hxi4 .
remember (u (i + 4)) as ui4 eqn:Hui4 .
Set Printing Depth 10. Show.
Set Printing Depth 24. Show.
remember (((ui2 * radix + ui3) / rr + ui1) mod radix) as a eqn:Ha.
remember (((ui3 * radix + ui4) / rr + ui2) mod radix) as b eqn:Hb.
rewrite Nat.add_shuffle0.
remember (xi1 * radix + a * radix + b + xi2) as c eqn:Hc.
do 2 rewrite <- Nat.add_assoc in Hc.
rewrite Nat.add_comm in Hc.
rewrite Nat.add_assoc in Hc.
subst c.
remember (a * radix + b) as c eqn:Hc.
rewrite Nat.add_shuffle0.
subst a b.
symmetry.
rewrite <- Nat.add_assoc.
rewrite Nat.add_shuffle0, Nat.add_assoc.
rewrite Nat.add_shuffle0.
symmetry.
rewrite <- Nat.add_assoc.
remember (xi1 * radix + xi2) as a eqn:Ha.
rewrite <- Nat.add_assoc.
remember (ui1 * radix + ui2) as b eqn:Hb.
Print NN2I.
Print I2NN.
Abort. (*
bbb.
          i  1  2
       x  .  1  1
       u  .  2  2
NN2I 2 u

NN2I 2 u = (ui + (2 ui1 + ui2) / 4) mod 2
I2NN (NN2I 2 u) = NN2I 2 u

(ui + 1) mod 2
ui mod 2

bordel c'est faux fait chier chais plus

 ((Σ (k = 0, 2), (u (i + k) b (2 - k))) / 4) mod 2
  (∀ j, u j ≤ 2)
  → (NN2I 2 (I2NN x + I2NN (NN2I 2 u))%NN .[ i] =
     NN2I 2 (I2NN x + u)%NN .[ i])%D.

Unset Printing Notations. Show.
Set Printing Depth 14. Show.
(*
assert (b < rr) as H.
 subst b rr.
 apply lt_trans with (m := pred radix * S radix).
 rewrite <- Nat.add_1_r, Nat.mul_add_distr_l, Nat.mul_1_r.
bbb.
u₁ ≤ 2(r-1)
u₁r ≤ 2r(r-1)
u₂ ≤ 2(r-1)
u₁r+u2 ≤ 2(r-1)²
r²-2(r-1)² = -r²+4r+2
merde, c'est négatif...
donc le assert est faux

Bon, peut-être que le théorème total est faux.
Un truc cool, ce serait de faire un contre-exemple.
bbb.

Unset Printing Notations. Show.
Set Printing Depth 14. Show.
*)
*)

Theorem zzz : ∀ x y z i,
  (NN2I 2 (I2NN x + I2NN (NN2I 2 (I2NN y + I2NN z)))%NN .[ i] =
   NN2I 2 (I2NN x + (I2NN y + I2NN z))%NN .[ i])%D.
Proof.
intros x y z i.
unfold NN2I, I2NN, NN_add; fsimpl.
unfold digit_eq; fsimpl.
rewrite Nat.mul_1_r.
erewrite summation_compat.
 Focus 2.
 intros j (_, Hj).
 rewrite d2n_n2d.
 unfold summation.
 rewrite Nat.sub_0_r; fsimpl.
 remember (i + j) as k.
 remember (int_pow radix (2 - j)) as a; simpl; subst a.
 do 3 rewrite Nat.add_0_r.
 do 2 rewrite Nat.mul_1_r.
 remember (plus (d2n (x .[ k]))) as a.
 rewrite Nat.add_comm; subst a.
 rewrite Nat.div_add; [ idtac | apply radix_radix_neq_0 ].
 rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
 do 2 rewrite Nat.add_assoc.
 subst k; reflexivity.

 do 2 (rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ]).
 erewrite summation_compat.
  2: intros; rewrite Nat.add_0_r; reflexivity.

  fsimpl.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite Nat.sub_0_r; fsimpl.
  rewrite Nat.mul_1_r, Nat.add_0_r.
  do 2 rewrite <- Nat.add_assoc; fsimpl.
  do 2 rewrite Nat.add_assoc.
  rewrite Nat.div_add_l; [ idtac | apply radix_radix_neq_0 ].
  symmetry.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite Nat.sub_0_r; fsimpl.
  rewrite Nat.mul_1_r, Nat.add_0_r.
  do 2 rewrite <- Nat.add_assoc; fsimpl.
  do 3 rewrite Nat.add_assoc.
  rewrite Nat.div_add_l; [ idtac | apply radix_radix_neq_0 ].
  do 5 rewrite <- Nat.add_assoc.
  rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
  rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
  f_equal; f_equal.
  do 3 rewrite Nat.add_assoc.
  symmetry.
  remember (d2n (x .[ i])) as xi eqn:Hxi .
  remember (d2n (y .[ i])) as yi eqn:Hyi .
  remember (d2n (z .[ i])) as zi eqn:Hzi .
  remember (d2n (x .[ i + 1])) as xi1 eqn:Hxi1 .
  remember (d2n (y .[ i + 1])) as yi1 eqn:Hyi1 .
  remember (d2n (z .[ i + 1])) as zi1 eqn:Hzi1 .
  remember (d2n (x .[ i + 2])) as xi2 eqn:Hxi2 .
  remember (d2n (y .[ i + 2])) as yi2 eqn:Hyi2 .
  remember (d2n (z .[ i + 2])) as zi2 eqn:Hzi2 .
  remember (d2n (x .[ i + 3])) as xi3 eqn:Hxi3 .
  remember (d2n (y .[ i + 3])) as yi3 eqn:Hyi3 .
  remember (d2n (z .[ i + 3])) as zi3 eqn:Hzi3 .
  remember (d2n (x .[ i + 4])) as xi4 eqn:Hxi4 .
  remember (d2n (y .[ i + 4])) as yi4 eqn:Hyi4 .
  remember (d2n (z .[ i + 4])) as zi4 eqn:Hzi4 .
  remember (((yi1 + zi1) * radix + yi2 + zi2) / (radix * radix)) as a.
  remember ((a + yi + zi) mod radix) as b eqn:Hb .
  rewrite <- Nat.add_assoc, Nat.add_comm in Hb.
  rewrite Nat.add_mod in Hb; [ idtac | apply Digit.radix_neq_0 ].
  symmetry.
  rewrite Nat.add_mod; [ idtac | apply Digit.radix_neq_0 ].
  symmetry; subst b.
  rewrite Nat.add_mod_idemp_l; [ idtac | apply Digit.radix_neq_0 ].
  rewrite <- Nat.add_assoc.
  rewrite <- Nat.add_mod_idemp_r; [ idtac | apply Digit.radix_neq_0 ].
  f_equal; f_equal; subst a.
  remember (radix * radix) as rr.
  remember ((((yi1 + zi1) * radix + yi2 + zi2) / rr) mod radix) as a eqn:Ha .
  subst rr.
  rewrite Nat.mod_small in Ha.
Abort. (*
bbb.
(* ouais, bon, qu'est-ce qu'y faut faire, main'nant ? *)

Unset Printing Notations. Show.
Set Printing Depth 14. Show.

bbb.

erewrite summation_compat.
Focus 2.
intros j (_, Hj).
destruct j.
simpl.
do 2 rewrite Nat.add_0_r.
rewrite Nat.mul_1_r.
bbb.

rewrite summation_add_mod.

rewrite summation_split_first; [ symmetry | apply Nat.le_0_l ].
rewrite summation_split_first; [ symmetry | apply Nat.le_0_l ].
rewrite Nat.add_mod.

rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].

f_equal; f_equal; f_equal.
rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].

Unset Printing Notations. Show.

rewrite summation_add_mod.

bbb.
reflexivity.

erewrite summation_compat.
Focus 2.
intros j (_, Hj).

f_equal; f_equal; f_equal.
apply summation_compat.
intros j (_, Hj).
remember (i + j) as k.
f_equal.
f_equal.
bbb.

(d2n (y .[ k + 1]) + d2n (z .[ k + 1])) * radix + d2n (y .[ k + 2]) +
      d2n (z .[ k + 2])
≤ 2(r-1)r+(r-1)+r-1
  = 2r²-2r+2r-2
  = 2r²-2
  = 2(r²-1)

rewrite Nat.add_comm.
do 2 rewrite Nat.add_assoc.
; subst a.

bbb.
subst k; reflexivity.


f_equal; f_equal; f_equal; f_equal; f_equal.
apply summation_compat; intros j (_, Hj).
f_equal; f_equal.
rewrite d2n_n2d.
unfold summation; simpl.
do 2 rewrite Nat.add_0_r.
do 2 rewrite Nat.mul_1_r.
remember (i + j) as k.
bbb.
*)

Theorem I_add2_assoc : ∀ x y z, (x + (y + z) == (x + y) + z)%I.
Proof.
intros x y z.
intros i.
unfold I_add2, I_add_algo.
unfold NN2I, I2NN, NN_add; fsimpl.
unfold summation; rewrite Nat.sub_0_r; simpl.
do 12 rewrite Nat.add_0_r.
do 9 rewrite Nat.mul_1_r.
do 6 rewrite d2n_n2d.
do 4 rewrite <- Nat.add_assoc; simpl.
do 6 (rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ]).
do 8 (rewrite Nat.div_add_l; [ idtac | apply radix_radix_neq_0 ]).
remember (d2n (x .[ i])) as xi eqn:Hxi .
remember (d2n (y .[ i])) as yi eqn:Hyi .
remember (d2n (z .[ i])) as zi eqn:Hzi .
remember (d2n (x .[ i + 1])) as xi1 eqn:Hxi1 .
remember (d2n (y .[ i + 1])) as yi1 eqn:Hyi1 .
remember (d2n (z .[ i + 1])) as zi1 eqn:Hzi1 .
remember (d2n (x .[ i + 2])) as xi2 eqn:Hxi2 .
remember (d2n (y .[ i + 2])) as yi2 eqn:Hyi2 .
remember (d2n (z .[ i + 2])) as zi2 eqn:Hzi2 .
remember (d2n (x .[ i + 3])) as xi3 eqn:Hxi3 .
remember (d2n (y .[ i + 3])) as yi3 eqn:Hyi3 .
remember (d2n (z .[ i + 3])) as zi3 eqn:Hzi3 .
remember (d2n (x .[ i + 4])) as xi4 eqn:Hxi4 .
remember (d2n (y .[ i + 4])) as yi4 eqn:Hyi4 .
remember (d2n (z .[ i + 4])) as zi4 eqn:Hzi4 .
do 8 rewrite Nat.add_assoc.
unfold digit_eq; simpl.
rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
Set Printing Depth 12. Show.
Set Printing Depth 50. Show.
symmetry.
rewrite <- Nat.add_assoc.
rewrite Nat.add_mod_idemp_l; [ idtac | apply Digit.radix_neq_0 ].
Set Printing Depth 11. Show.
do 16 rewrite <- Nat.add_assoc.
rewrite Nat.add_comm; symmetry.
rewrite Nat.add_comm; symmetry.
Set Printing Depth 13. Show.
symmetry.
bbb.

Unset Printing Notations. Show.
Set Printing Depth 11. Show.

do 2 (rewrite Nat.div_mul; [ idtac | apply radix_radix_neq_0 ]).
do 7 rewrite Nat.mul_1_r.
do 6 rewrite I_add_algo_div_sqr_radix.
do 4 rewrite Nat.add_0_r.
do 3 rewrite <- Nat.add_assoc; simpl.
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
         rewrite Nat_mod_succ_l; [ idtac | assumption ].
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
