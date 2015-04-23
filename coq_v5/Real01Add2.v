(** second version of adding reals in interval [0..1[ *)

Require Import Utf8 QArith NPeano.
Require Import Misc Summation.
Require Import Oracle Digit2 Real012.

Open Scope nat_scope.

(* addition and multiplication numbers with numbers *)

Definition NN_eq (u v : nat → nat) := ∀ i, u i = v i.
Definition NN_add (u v : nat → nat) i := u i + v i.
Definition NN_mul u v i := Σ (j = 1, i), u (j - 1) * v (i - j).
Definition NN_zero (i : nat) := 0.

Delimit Scope NN_scope with NN.
Notation "u = v" := (NN_eq u v) : NN_scope.
Notation "u + v" := (NN_add u v) : NN_scope.
Notation "u * v" := (NN_mul u v) : NN_scope.
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

Theorem NN_add_assoc : ∀ u v w, (u + (v + w) = (u + v) + w)%NN.
Proof. intros u v w i; apply Nat.add_assoc. Qed.

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

(* some extra functions *)

Fixpoint int_pow a b :=
  match b with
  | 0 => 1
  | S b1 => a * int_pow a b1
  end.

Fixpoint logn_loop m n a :=
  match m with
  | 0 => 0
  | S m1 =>
      if zerop a then 0
      else S (logn_loop m1 n (a / n))
  end.

Definition logn n a := pred (logn_loop a n a).

(* addition *)

Definition seq_pred_r (u : nat → nat) i k :=
  if eq_nat_dec (u (i + k)) (pred radix) then 0 else 1.

Definition fst_neq_pred_r u i := first_nonzero (seq_pred_r u i).
Arguments fst_neq_pred_r u%NN i%nat.

Definition carry_add u i :=
  match fst_neq_pred_r u (S i) with
  | Some n => if lt_dec (u (S (i + n))) (pred radix) then 0 else 1
  | None => 1
  end.
Arguments carry_add u%NN i%nat.

Definition I2NN x i := d2n (x.[i]).
Arguments I2NN x%I i%nat.

Definition NN2I_add u := {| rm i := n2d (u i + carry_add u i) |}.
Arguments NN2I_add u%NN.

Definition I_add2 x y := NN2I_add (I2NN x + I2NN y).
Arguments I_add2 x%I y%I.

Notation "x + y" := (I_add2 x y) : I_scope.

(* normalisation and equality *)

Definition I_norm x := (x + 0)%I.
Definition I_eq x y := (I_norm x == I_norm y)%I.

Notation "x = y" := (I_eq x y) : I_scope.

Theorem I_eq_refl : reflexive _ I_eq.
Proof. intros u i; reflexivity. Qed.

Theorem I_eq_sym : symmetric _ I_eq.
Proof.
intros u v Huv i.
symmetry; apply Huv.
Qed.

Theorem I_eq_trans : transitive _ I_eq.
Proof.
intros u v w Huv Hvw i.
unfold I_eq in Huv, Hvw.
rewrite Huv, Hvw; reflexivity.
Qed.

Add Parametric Relation : _ I_eq
 reflexivity proved by I_eq_refl
 symmetry proved by I_eq_sym
 transitivity proved by I_eq_trans
 as I_eq_rel.

Definition seq_eq x y i := if Digit.eq_dec (x.[i]) (y.[i]) then 0 else 1.

Add Parametric Morphism : I2NN
  with signature I_eqs ==> NN_eq
  as I2NN_morph.
Proof. intros x y Hxy i; apply Hxy. Qed.

Theorem I_zero_NN_zero : (I2NN 0%I = NN_zero)%NN.
Proof.
intros i.
unfold I2NN; simpl.
unfold d2n; simpl.
rewrite Nat.mod_0_l; [ reflexivity | apply Digit.radix_neq_0 ].
Qed.

Theorem NN_add_add_0_r : ∀ u, (u + I2NN 0 = u)%NN.
Proof.
intros u i.
unfold NN_eq, NN_add, I2NN; simpl.
rewrite d2n_0, Nat.add_0_r.
reflexivity.
Qed.

Theorem seq_pred_r_add_0_r : ∀ u i j,
  seq_pred_r (u + 0)%NN i j = seq_pred_r u i j.
Proof.
intros u i j.
unfold seq_pred_r; simpl.
unfold NN_add, NN_zero; simpl.
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem fst_neq_pred_r_add_0_r : ∀ u i,
  fst_neq_pred_r (u + 0%NN) i = fst_neq_pred_r u i.
Proof.
intros u i.
apply first_nonzero_iff; simpl.
remember (fst_neq_pred_r (u + 0%NN) i) as s1 eqn:Hs1.
apply first_nonzero_iff in Hs1; simpl in Hs1.
destruct s1 as [n1| ].
 destruct Hs1 as (Hn1, Ht1).
  split.
   intros j Hj.
   apply Hn1 in Hj.
   rewrite seq_pred_r_add_0_r in Hj.
   assumption.

   rewrite seq_pred_r_add_0_r in Ht1.
   assumption.

 intros j.
 rewrite <- seq_pred_r_add_0_r.
 apply Hs1.
Qed.

Theorem seq_pred_r_compat : ∀ u v i j,
  (u = v)%NN
  → seq_pred_r u i j = seq_pred_r v i j.
Proof.
intros u v i j Huv.
unfold seq_pred_r; simpl.
rewrite Huv; reflexivity.
Qed.

Theorem fst_neq_pred_r_compat : ∀ u v i,
  (u = v)%NN
  → fst_neq_pred_r u i = fst_neq_pred_r v i.
Proof.
intros u v i Huv.
unfold fst_neq_pred_r; simpl.
apply first_nonzero_iff.
remember (first_nonzero (seq_pred_r u i)) as s1 eqn:Hs1.
apply first_nonzero_iff in Hs1.
destruct s1 as [ i1 | ].
 destruct Hs1 as (Hn1, Ht1).
 split.
  intros j Hj.
  erewrite seq_pred_r_compat; [ idtac | symmetry; eassumption ].
  apply Hn1; assumption.

  erewrite seq_pred_r_compat; [ idtac | symmetry; eassumption ].
  assumption.

 intros j.
 erewrite seq_pred_r_compat; [ idtac | symmetry; eassumption ].
 apply Hs1.
Qed.

Theorem carry_add_compat : ∀ u v i,
  (u = v)%NN
  → carry_add u i = carry_add v i.
Proof.
intros u v i Huv.
unfold carry_add.
erewrite fst_neq_pred_r_compat; [ idtac | eassumption ].
remember (fst_neq_pred_r v (S i)) as s1 eqn:Hs1.
destruct s1 as [n1| ]; [ idtac | reflexivity ].
rewrite Huv; reflexivity.
Qed.

Theorem carry_add_add_0_r : ∀ u i, carry_add (u + 0%NN) i = carry_add u i.
Proof.
intros u i.
apply carry_add_compat.
apply NN_add_0_r.
Qed.

Theorem carry_add_add_0_r2 : ∀ u i, carry_add (u + I2NN 0) i = carry_add u i.
Proof.
intros u i.
apply carry_add_compat.
clear i; intros i; simpl.
unfold NN_add, I2NN, d2n; simpl.
rewrite Nat.mod_0_l; [ idtac | apply Digit.radix_neq_0 ].
apply Nat.add_0_r.
Qed.

Theorem n2d_1 : (n2d 1 = 1)%D.
Proof. reflexivity. Qed.

Theorem eq_d2n_pred_radix : ∀ d, d2n d = pred radix ↔ (d = 9)%D.
Proof.
intros d; unfold digit_eq; simpl; rewrite Nat_pred_mod.
split; intros; assumption.
Qed.

Theorem neq_d2n_pred_radix : ∀ d, d2n d ≠ pred radix ↔ (d ≠ 9)%D.
Proof.
intros d; unfold digit_eq; simpl; rewrite Nat_pred_mod.
split; intros; assumption.
Qed.

Theorem seq_eq_eq : ∀ x y i, seq_eq x y i = 0 ↔ (x.[i] = y.[i])%D.
Proof.
intros x y i; unfold seq_eq.
split; intros Hxy.
 destruct (Digit.eq_dec (x.[i]) (y.[i])) as [H1| H1]; [ assumption | idtac ].
 discriminate Hxy.

 destruct (Digit.eq_dec (x.[i]) (y.[i])) as [H1| H1]; [ reflexivity | idtac ].
 contradiction.
Qed.

Theorem seq_pred_r_neq : ∀ u i k,
  seq_pred_r u i k ≠ 0 ↔ u (i + k) ≠ pred radix.
Proof.
intros u i k; unfold seq_pred_r.
split; intros Hu.
 remember (u (i + k)) as a.
 destruct (eq_nat_dec a (pred radix)) as [H1| H1]; [ idtac | assumption ].
 exfalso; apply Hu; reflexivity.

 remember (u (i + k)) as a.
 destruct (eq_nat_dec a (pred radix)) as [H1| H1]; [ contradiction | idtac ].
 intros H; discriminate H.
Qed.

Theorem seq_pred_r_I2NN : ∀ x i di,
  seq_pred_r (I2NN x) i di = 0 ↔ d2n (x .[i + di]) = pred radix.
Proof.
intros x i di.
unfold seq_pred_r, I2NN; simpl.
remember (d2n (x .[ i + di])) as a.
split; intros H.
 destruct (eq_nat_dec a (pred radix)) as [H1| H1]; [ idtac | discriminate H ].
 assumption.

 destruct (eq_nat_dec a (pred radix)) as [H1| H1]; [ reflexivity | idtac ].
 contradiction.
Qed.

Theorem seq_pred_r_I2NN_neq : ∀ x i di,
  seq_pred_r (I2NN x) i di ≠ 0 ↔ d2n (x .[i + di]) ≠ pred radix.
Proof.
intros x i di.
split; intros HH H; apply HH; apply seq_pred_r_I2NN; assumption.
Qed.

Theorem d2n_add : ∀ a b, d2n (a + b) = (d2n a + d2n b) mod radix.
Proof.
intros a b.
unfold d2n; simpl.
rewrite Nat.add_mod; [ reflexivity | apply Digit.radix_neq_0 ].
Qed.

Theorem digit_neq_succ_digit : ∀ a, (a ≠ a + 1)%D.
Proof.
intros a H.
unfold digit_eq in H; simpl in H.
remember (dig a) as n; revert H; clear; intros.
rewrite <- Nat.add_mod_idemp_l in H; [ idtac | apply Digit.radix_neq_0 ].
destruct (eq_nat_dec (n mod radix) (pred radix)) as [H1| H1].
 rewrite H1, Nat.add_1_r in H.
 rewrite Nat.succ_pred in H; [ idtac | apply Digit.radix_neq_0 ].
 rewrite Nat.mod_same in H; [ idtac | apply Digit.radix_neq_0 ].
 remember radix as r eqn:Hr; symmetry in Hr.
 destruct r; [ revert Hr; apply Digit.radix_neq_0 | simpl in H ].
 destruct r; [ revert Hr; apply Digit.radix_neq_1 | discriminate H ].

 symmetry in H.
 rewrite Nat.mod_small in H.
  rewrite Nat.add_1_r in H.
  revert H; apply Nat.neq_succ_diag_l.

  pose proof Digit.radix_neq_0 as H2.
  apply Nat.mod_upper_bound with (a := n) in H2.
  apply Nat.lt_add_lt_sub_r; rewrite Nat.sub_1_r.
  apply Nat_le_neq_lt; [ idtac | assumption ].
  rewrite <- Nat.sub_1_r; apply Nat.le_add_le_sub_r.
  rewrite Nat.add_1_r; assumption.
Qed.

Theorem Nat_mod_add_divides : ∀ a b c, c ≠ 0 → (a + b) mod c = a → (c | b).
Proof.
intros a b c Hc Hab.
apply Nat.div_mod with (x := a + b) in Hc.
rewrite Hab, Nat.add_comm, Nat.mul_comm in Hc.
apply Nat.add_cancel_r in Hc.
exists ((b + a) / c); assumption.
Qed.

(* borrowed from Read01Add.v and adapted for this implementation *)
Theorem I_eq_neq_prop : ∀ x y i,
  (x = y)%I
  → (y.[i] = x.[i] + 1)%D
  → (∀ di, (x.[i+di] = 9)%D) ∧ (∀ di, (y.[i+di] = 0)%D) ∨
     radix = 2 ∧
     (∀ di, (x.[i+S di] = 0)%D) ∧ (∀ di, (y.[i+S di] = 1)%D).
Proof.
intros x y i Hxy Hy.
unfold I_eq, I_eqs in Hxy; simpl in Hxy.
pose proof (Hxy i) as Hn.
do 2 rewrite NN_add_add_0_r in Hn.
do 2 rewrite carry_add_add_0_r2 in Hn.
unfold digit_eq in Hn; simpl in Hn.
unfold I2NN in Hn at 1; simpl in Hn.
unfold I2NN in Hn at 2; simpl in Hn.
apply -> digit_d2n_eq_iff in Hy.
rewrite Hy in Hn; simpl in Hn.
unfold carry_add in Hn; simpl in Hn.
remember (fst_neq_pred_r (I2NN x) (S i)) as sx eqn:Hsx .
remember (fst_neq_pred_r (I2NN y) (S i)) as sy eqn:Hsy .
apply first_nonzero_iff in Hsx; simpl in Hsx.
apply first_nonzero_iff in Hsy; simpl in Hsy.
destruct sx as [dx| ].
 destruct Hsx as (Hnx, Htx).
 apply seq_pred_r_I2NN_neq in Htx; simpl in Htx.
 remember (S (i + dx)) as a.
 destruct (lt_dec (I2NN x a) (pred radix)) as [H1| H1]; subst a.
  rewrite Nat.add_0_r in Hn.
  destruct sy as [dy| ].
   destruct Hsy as (Hny, Hty).
   apply seq_pred_r_neq in Hty; simpl in Hty.
   remember (S (i + dy)) as a.
   destruct (lt_dec (I2NN y a) (pred radix)) as [H2| H2]; subst a.
    rewrite Nat.add_0_r in Hn.
    apply d2n_mod_radix in Hn.
    apply digit_d2n_eq_iff in Hn.
    exfalso; revert Hn; apply digit_neq_succ_digit.

    unfold I2NN in Hty, H2; simpl in Hty, H2.
    exfalso; apply H2; clear H2.
    pose proof (d2n_lt_radix (y .[ S (i + dy)])) as H.
    apply Nat_le_neq_lt; [ idtac | assumption ].
    apply Nat.lt_le_pred; assumption.

   rewrite d2n_add in Hn.
   pose proof Digit.radix_neq_0 as Hrnz.
   rewrite Nat.add_mod_idemp_l in Hn; [ idtac | assumption ].
   rewrite d2n_1, <- Nat.add_assoc in Hn; simpl in Hn.
   symmetry in Hn.
   rewrite <- Nat.add_mod_idemp_l in Hn; [ idtac | assumption ].
   apply Nat_mod_add_divides in Hn; [ idtac | assumption ].
   destruct Hn as (c, Hn); symmetry in Hn.
   destruct c; [ discriminate Hn | idtac ].
   pose proof Digit.radix_gt_1 as H.
   assert (0 < S c) as Hc by apply Nat.lt_0_succ.
   eapply Nat.mul_lt_mono_pos_l in H; [ idtac | eassumption ].
   rewrite Hn, Nat.mul_1_r in H.
   apply lt_S_n, Nat.lt_1_r in H; subst c.
   rewrite Nat.mul_1_l in Hn; clear Hc.
   right; split; [ assumption | idtac ].
   rename H1 into Hxlt.
   rename Hn into Hr.
   split; intros di.
    destruct (lt_eq_lt_dec di dx) as [[H1| H1]| H1].
     pose proof (Hnx di H1) as Hdi.
     destruct dx; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
     pose proof (Hxy (S (i + dx))%nat) as Hn.
     do 2 rewrite NN_add_add_0_r in Hn.
     do 2 rewrite carry_add_add_0_r2 in Hn.
     unfold digit_eq in Hn; simpl in Hn.
     unfold I2NN in Hn at 1; simpl in Hn.
     unfold I2NN in Hn at 2; simpl in Hn.
     pose proof (Hnx dx (Nat.lt_succ_diag_r dx)) as H.
     apply seq_pred_r_I2NN in H; simpl in H; rename H into H2.
     rewrite Hr in H2; simpl in H2; rewrite H2 in Hn.
     pose proof (Hsy dx) as H.
     apply seq_pred_r_I2NN in H; simpl in H; rename H into H3.
     rewrite H3 in Hn; simpl in Hn.
     unfold carry_add in Hn; simpl in Hn.
     remember (fst_neq_pred_r (I2NN x) (S (S (i + dx)))) as s2 eqn:Hs2 .
     remember (fst_neq_pred_r (I2NN y) (S (S (i + dx)))) as s3 eqn:Hs3 .
     apply first_nonzero_iff in Hs2; simpl in Hs2.
     apply first_nonzero_iff in Hs3; simpl in Hs3.
     destruct s2 as [n2| ].
      destruct Hs2 as (Hn2, Ht2).
      apply seq_pred_r_I2NN_neq in Ht2; simpl in Ht2.
      apply neq_d2n_pred_radix in Ht2.
Theorem zzz : ∀ d, radix = 2 → (d ≠ 9)%D → (d = 0)%D.
Proof.
intros d Hr Hd.
apply neq_d2n_pred_radix in Hd.
unfold digit_eq in Hd; simpl in Hd.
unfold digit_eq; simpl.
rewrite Nat.mod_0_l; [ idtac | apply Digit.radix_neq_0 ].
unfold d2n in Hd; simpl in Hd.
rewrite Hr in Hd; rewrite Hr.
remember (dig d mod 2) as n eqn:Hn.
destruct n; [ reflexivity | exfalso; apply Hd; clear Hd; simpl ].
destruct n; [ reflexivity | exfalso ].
pose proof Nat.mod_upper_bound (S (S n)) radix Digit.radix_neq_0 as H.
SearchAbout (_ mod _ < _).
bbb.

rewrite Hn, Hr in H.
rewrite Nat.mod_mod in H; [|intros HH; discriminate HH].

bbb.
      assert (x .[ S (S (i + dx + n2))] = 0)%D as H.
       pose proof d2n_lt_radix (x .[ S (S (i + dx + n2))]) as H.
       rewrite Hr in H.
       unfold d2n in Ht2.


       unfold digit_eq in Ht2; simpl in Ht2.
       unfold digit_eq; simpl.

      assert (9 = 1)%D as H by (unfold digit_rm1; rewrite Hr; reflexivity).
      rewrite H in Ht2.
bbb.
      rewrite Hr in Ht2; simpl in Ht2.
Check eq_d2n_1.
apply <- eq_d2n_1 in Ht2.

SearchAbout (d2n _ ≠ _).
unfold d2n in Ht2; simpl in Ht2.
rewrite Hr in Ht2.
SearchAbout (_ mod _ ≠ _).
bbb.
       unfold I2NN in H4, Hn.
       destruct n2; [ clear Hn2; rewrite Nat.add_0_r in H4, Hn | idtac ].
        remember (d2n (x .[ S (S (i + dx))])) as a.
        destruct (lt_dec a (pred radix)) as [H5| H5]; subst a.
         rewrite Nat.mod_small in Hn; [ idtac | apply Digit.radix_gt_1 ].
         destruct s3 as [n3| ].
          destruct Hs3 as (Hn3, Ht3).
          unfold seq_pred_r, I2NN in Ht3; simpl in Ht3.
          remember (d2n (y .[ S (S (i + dx + n3))])) as a.
          destruct (eq_nat_dec a (pred radix)) as [H6| H6].
           exfalso; apply Ht3; reflexivity.

           clear Ht3.
           destruct (lt_dec a (pred radix)) as [H7| H7]; subst a.
            destruct n3.
             rewrite Nat.add_0_r in H6.
             pose proof (Hsy (S dx)) as H.
             unfold seq_pred_r, I2NN in H; simpl in H.
             rewrite Nat.add_succ_r in H.
             remember (d2n (y .[ S (S (i + dx))])) as a.
             destruct (eq_nat_dec a (pred radix)) as [H8| H8]; subst a.
              contradiction.

              discriminate H.

             pose proof (Hsy (S (dx + S n3))) as H.
             unfold seq_pred_r, I2NN in H; simpl in H.
             rewrite Nat.add_succ_r, Nat.add_assoc in H.
             remember (d2n (y .[ S (S (i + dx + S n3))])) as a.
             destruct (eq_nat_dec a (pred radix)) as [H8| H8]; subst a.
              contradiction.

              discriminate H.

            exfalso; apply H7; clear H7.
            pose proof (d2n_lt_radix (y .[ S (S (i + dx + n3))])) as H.
            apply Nat_le_neq_lt; [ idtac | assumption ].
            apply Nat.lt_le_pred; assumption.

          rewrite Hr in Hn; discriminate Hn.

         exfalso; apply H5; clear H5.
         pose proof (d2n_lt_radix (x .[ S (S (i + dx))])) as H.
         apply Nat_le_neq_lt; [ idtac | assumption ].
         apply Nat.lt_le_pred; assumption.

        pose proof (Hn2 0 (Nat.lt_0_succ n2)) as H.
        unfold seq_pred_r, I2NN in H; simpl in H.
        rewrite Nat.add_0_r, <- Nat.add_succ_r in H.
        remember (d2n (x .[ S (i + S dx)])) as a.
        destruct (eq_nat_dec a (pred radix)) as [H5| H5]; subst a.
         contradiction.

         discriminate H.

      pose proof (Hs2 0) as H.
      unfold seq_pred_r, I2NN in H; simpl in H.
      rewrite Nat.add_0_r, <- Nat.add_succ_r in H.
      unfold I2NN in Htx; simpl in Htx.
      remember (d2n (x .[ S (i + S dx)])) as a.
      destruct (eq_nat_dec a (pred radix)) as [H5| H5]; subst a.
       contradiction.

       discriminate H.

     subst di; rewrite Nat.add_succ_r.
     unfold I2NN in Hxlt; rewrite Hr in Hxlt; simpl in Hxlt.
     apply Nat.lt_1_r, eq_d2n_0 in Hxlt; assumption.

     remember (di - S dx)%nat as n eqn:Hn .
     apply Nat_sub_add_r in Hn; [ idtac | assumption ].
     subst di; clear H1.
     rewrite Nat.add_succ_r.
     induction n as (n, IHn) using all_lt_all.
     destruct n.
      rewrite Nat.add_1_r, Nat.add_succ_r.
      pose proof (Hxy (S (i + dx))) as Hn.
      do 2 rewrite NN_add_add_0_r in Hn.
      do 2 rewrite carry_add_add_0_r2 in Hn.
      unfold digit_eq in Hn; simpl in Hn.
      unfold I2NN in Hn at 1; simpl in Hn.
      unfold I2NN in Hn at 2; simpl in Hn.
      rewrite Hr in Hxlt; simpl in Hxlt.
      apply Nat.lt_1_r in Hxlt; unfold I2NN in Hxlt.
      rewrite Hxlt, Nat.add_0_l in Hn.
      pose proof (Hsy dx) as H.
bbb.
      rewrite Htx, Hny, Digit.add_0_l in Hn.

, Digit.add_1_l in H.
      symmetry in H, Hsx, Hsy.
      rewrite <- Nat.add_succ_l in H.
      rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
      symmetry in H.
      unfold carry in H; simpl in H.
      remember (fst_same x 0 (S (S (i + dx)))) as s1 eqn:Hs1 .
      destruct s1 as [di1| ].
       rename H into Hx1.
       destruct di1.
        rewrite Nat.add_0_r in Hx1; assumption.

        generalize Hs1; intros H.
        apply fst_same_sym_iff in H; simpl in H.
        destruct H as (Hn1, _).
        pose proof (Hxy (S (S (i + dx)))) as H.
        unfold I_add_i in H; simpl in H.
        do 2 rewrite Digit.add_0_r in H.
        rewrite <- Nat.add_succ_r in H.
        rewrite Hny, Digit.add_1_l, Nat.add_succ_r in H.
        symmetry in H.
        rewrite <- Nat.add_succ_l, <- Nat.add_succ_r in H;
        rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
        symmetry in H, Hs1.
        replace dx with (dx + 0)%nat in H by apply Nat.add_0_r.
        simpl in H.
        rewrite Nat.add_succ_r, Nat.add_assoc in H.
        do 2 rewrite <- Nat.add_succ_l in H.
        assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
        erewrite carry_before_relay9 in H; try eassumption.
        simpl in H.
        rewrite Hx1, Digit.add_0_r, Nat.add_0_r in H.
        assumption.

       discr_digit H.

      rewrite Nat.add_succ_r.
      pose proof (Hxy (S (i + dx + S n))) as H.
      unfold I_add_i in H; simpl in H.
      do 2 rewrite Digit.add_0_r in H.
      rewrite <- Nat.add_assoc in H.
      rewrite IHn in H; [ idtac | apply Nat.lt_succ_diag_r ].
      rewrite Hny, Digit.add_0_l, Digit.add_1_l in H.
      symmetry in H, Hsx, Hsy.
      rewrite <- Nat.add_succ_l in H.
      rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
      symmetry in H.
      unfold carry in H; simpl in H.
      remember (fst_same x 0 (S (S (i + (dx + S n))))) as s1 eqn:Hs1 .
      destruct s1 as [di1| ].
       rename H into Hx1.
       destruct di1.
        rewrite Nat.add_0_r, <- Nat.add_succ_r in Hx1.
        assumption.

        generalize Hs1; intros H.
        apply fst_same_sym_iff in H; simpl in H.
        destruct H as (Hn1, _).
        pose proof (Hxy (S (S (i + dx + S n)))) as H.
        unfold I_add_i in H; simpl in H.
        do 2 rewrite Digit.add_0_r in H.
        rewrite <- Nat.add_succ_r in H.
        rewrite <- Nat.add_assoc in H.
        rewrite Nat.add_succ_r in H.
        rewrite Hny, Digit.add_1_l in H.
        rewrite <- Nat.add_succ_l in H.
        symmetry in H.
        rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
        symmetry in H, Hs1.
        remember (S i + S (dx + S n))%nat as z.
        replace (S z) with (S z + 0)%nat in H by apply Nat.add_0_r.
        subst z.
        rewrite Digit.add_comm in H.
        rewrite <- Nat.add_succ_l in H; simpl in H.
        rewrite <- Nat.add_succ_l in H.
        rewrite <- Nat.add_succ_r in Hs1.
        assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
        erewrite carry_before_relay9 in H; try eassumption.
        simpl in H.
        do 4 rewrite Nat.add_succ_r in H.
        do 3 rewrite Nat.add_succ_r in Hx1.
        simpl in H.
        rewrite Nat.add_assoc in Hx1.
        simpl in Hx1.
        rewrite Nat.add_assoc, Hx1, <- Digit.opp_add_l in H.
        apply Digit.opp_eq in H.
        rewrite Digit.add_1_l in H.
        apply Digit.opp_1_iff in H.
        do 3 rewrite Nat.add_succ_r.
        rewrite Nat.add_assoc; assumption.

       discr_digit H.

    rewrite Nat.add_succ_r; simpl; apply Hny.

 destruct sy as [dy| ]; [ idtac | discr_digit H ].
 symmetry in H; simpl in H.
 generalize Hsy; intros HH.
 apply fst_same_sym_iff in HH; simpl in HH.
 destruct HH as (Hny, Hty); clear H.
 left.
 generalize Hsx; intros Hnx.
 apply fst_same_sym_iff in Hnx; simpl in Hnx.
 split; intros di.
  destruct (lt_eq_lt_dec di dy) as [[H1| H1]| H1].
   pose proof (Hny di H1) as H.
   destruct dy; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
   rename H into Hdi.
   pose proof (Hxy (S (i + dy))%nat) as H.
   unfold I_add_i in H; simpl in H.
   do 2 rewrite Digit.add_0_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite Digit.add_1_l in H.
   apply Digit.opp_eq in H.
   rewrite <- Nat.add_succ_l in H.
   symmetry in Hsy, H.
   erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
   symmetry in Hsx.
   rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
   simpl in H; rewrite Hty in H.
   discr_digit H.

   subst di.
   destruct dy; [ rewrite Nat.add_0_r; assumption | idtac ].
   rewrite Nat.add_succ_r; apply Hnx.

   destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
   rewrite Nat.add_succ_r; apply Hnx.

  destruct di; [ rewrite Nat.add_0_r; assumption | idtac ].
  rewrite Nat.add_succ_r.
  destruct (lt_eq_lt_dec di dy) as [[H1| H1]| H1].
   pose proof (Hny di H1) as H.
   destruct dy; [ exfalso; revert H1; apply Nat.nlt_0_r | idtac ].
   rename H into Hdi.
   pose proof (Hxy (S (i + dy))%nat) as H.
   unfold I_add_i in H; simpl in H.
   do 2 rewrite Digit.add_0_r in H.
   rewrite Hny in H; [ idtac | apply Nat.lt_succ_diag_r ].
   rewrite Hnx in H.
   rewrite Digit.add_1_l in H.
   apply Digit.opp_eq in H.
   rewrite <- Nat.add_succ_l in H.
   symmetry in Hsy, H.
   erewrite carry_before_relay9 in H; [ idtac | eassumption | auto ].
   symmetry in Hsx.
   rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
   simpl in H; rewrite Hty in H.
   discr_digit H.

   subst di; assumption.

   remember (di - S dy)%nat as n eqn:Hn .
   apply Nat_sub_add_r in Hn; [ idtac | assumption ].
   subst di; clear H1.
   rewrite Nat.add_succ_r.
   induction n as (n, IHn) using all_lt_all.
   destruct n; [ clear IHn | idtac ].
    rewrite Nat.add_succ_r.
    pose proof (Hxy (S (i + dy))) as H.
    unfold I_add_i in H; simpl in H.
    do 2 rewrite Digit.add_0_r in H.
    rewrite Hnx, Hty, Digit.add_0_l, Digit.add_1_l in H.
    symmetry in Hsx, Hsy.
    rewrite Nat.add_0_r.
    rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
    symmetry in H.
    unfold carry in H; simpl in H.
    remember (fst_same y 0 (S (S (i + dy)))) as s1 eqn:Hs1 .
    destruct s1 as [di1| ].
     rename H into Hx1.
     destruct di1; [ rewrite Nat.add_0_r in Hx1; assumption | idtac ].
     generalize Hs1; intros H.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, _).
     pose proof (Hxy (S (S (i + dy)))) as H.
     unfold I_add_i in H; simpl in H.
     do 2 rewrite Digit.add_0_r in H.
     rewrite <- Nat.add_succ_r in H.
     pose proof (Hn1 O (Nat.lt_0_succ di1)) as HH.
     rewrite Nat.add_0_r, <- Nat.add_succ_r in HH.
     rewrite HH, Hnx, Digit.add_1_l in H.
     apply Digit.opp_eq in H.
     rewrite <- Nat.add_succ_l in H.
     rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     symmetry in H, Hs1.
     replace dy with (dy + 0)%nat in H by apply Nat.add_0_r.
     simpl in H.
     rewrite Nat.add_succ_r, Nat.add_assoc in H.
     do 2 rewrite <- Nat.add_succ_l in H.
     clear HH.
     assert (0 < S di1)%nat as HH by apply Nat.lt_0_succ.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H.
     rewrite Hx1 in H.
     discr_digit H.

    discr_digit H.

    rewrite Nat.add_succ_r.
    pose proof (Hxy (S (i + dy + S n))) as H.
    unfold I_add_i in H; simpl in H.
    do 2 rewrite Digit.add_0_r in H.
    rewrite <- Nat.add_assoc in H.
    pose proof (IHn n (Nat.lt_succ_diag_r n)) as HH.
    rewrite <- Nat.add_succ_r in HH.
    rewrite <- Nat.add_succ_r in HH.
    rewrite Nat.add_succ_r in HH.
    rewrite Hnx, HH, Digit.add_0_l, Digit.add_1_l in H.
    symmetry in Hsx, Hsy.
    rewrite <- Nat.add_succ_l in H.
    rewrite carry_before_inf_relay9 in H; [ simpl in H | assumption ].
    symmetry in H.
    unfold carry in H; simpl in H.
    remember (fst_same y 0 (S (S (i + (dy + S n))))) as s1 eqn:Hs1 .
    destruct s1 as [di1| ].
     rename H into Hx1.
     destruct di1; [ rewrite Nat.add_0_r in Hx1; assumption | idtac ].
     generalize Hs1; intros H.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, _).
     pose proof (Hxy (S (S (i + dy + S n)))) as H.
     unfold I_add_i in H; simpl in H.
     do 2 rewrite Digit.add_0_r in H.
     rewrite <- Nat.add_assoc in H.
     rewrite <- Nat.add_succ_r in H.
     rewrite Hnx, Digit.add_1_l in H.
     rewrite <- Nat.add_succ_l in H.
     erewrite carry_before_inf_relay9 in H; [ idtac | eassumption ].
     remember (S i + S (dy + S n)) as z.
     replace z with (z + 0)%nat in H by apply Nat.add_0_r.
     subst z.
     symmetry in Hs1.
     assert (0 < S di1)%nat as HHH by apply Nat.lt_0_succ.
     simpl in Hs1; rewrite <- Nat.add_succ_r in Hs1.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H; symmetry in H.
     rewrite Nat.add_succ_r in H.
     rewrite Hx1, Digit.add_0_r, Nat.add_succ_r, Nat.add_0_r in H.
     rewrite Nat.add_succ_r.
     assumption.

   discr_digit H.
Qed.

Theorem I_eq_iff_radix_2 : ∀ x y,
  radix = 2
  → (x = y)%I
    ↔ (x == y)%I ∨
      ∃ i,
      (∀ j, j < i → (x.[j] = y.[j])%D) ∧
      (x.[i] ≠ y.[i])%D ∧
      (i = 0 ∧ (∀ j, (x.[j] = x.[0])%D) ∧ (∀ j, (y.[j] = y.[0])%D) ∨
       (∀ di, (x.[i+S di] = y.[i])%D) ∧ (∀ di, (y.[i+S di] = x.[i])%D)).
Proof.
(* à nettoyer (la 2ème partie) *)
intros x y Hr.
split; intros Hxy.
 remember (first_nonzero (seq_eq x y)) as s1 eqn:Hs1 .
 apply first_nonzero_iff in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Ht1).
  right; exists di1.
  split.
   intros j Hdj.
   apply seq_eq_eq, Hn1; assumption.

   split; [ intros H; apply seq_eq_eq in H; contradiction | idtac ].
(*
    apply Digit.opp_sym in Ht1.
*)
    destruct (Digit.eq_dec (x .[ di1]) 1) as [Hx1| Hx1].
     generalize Hx1; intros Hxi1.
     eapply I_eq_neq_prop in Hxi1; try eassumption.
      destruct Hxi1 as [(Hx, Hy)| (Hx, Hy)].
       destruct di1.
        left.
        split; [ reflexivity | idtac ].
        simpl in Hx, Hy.
        split; intros j; [ do 2 rewrite Hx | do 2 rewrite Hy ]; reflexivity.

        pose proof (Hn1 di1 (Nat.lt_succ_diag_r di1)) as H.
        rewrite Digit.opp_involutive in H.
        pose proof (Hxy di1) as HH; simpl in HH.
        unfold I_add_i in HH; simpl in HH.
        do 2 rewrite Digit.add_0_r in HH.
        rewrite H in HH.
        unfold carry in HH; simpl in HH.
        remember (fst_same x 0 (S di1)) as s2 eqn:Hs2 .
        remember (fst_same y 0 (S di1)) as s3 eqn:Hs3 .
        destruct s2 as [dj2| ].
         apply fst_same_sym_iff in Hs2; simpl in Hs2.
         destruct Hs2 as (Hn2, Ht2).
         rewrite <- Nat.add_succ_l, Hx in Ht2.
         discr_digit Ht2.

         apply fst_same_sym_iff in Hs3; simpl in Hs3.
         destruct s3 as [dj3| ]; [ idtac | clear HH ].
          rewrite <- Nat.add_succ_l, Hy, Digit.add_0_r in HH.
          exfalso; revert HH; apply Digit.no_fixpoint_opp.

          pose proof (Hy 0) as HH; simpl in HH.
          rewrite Hs3 in HH.
          discr_digit HH.

       rewrite Hx1 in Ht1.
       right; split; intros di; [ rewrite Ht1; apply Hx | idtac ].
       rewrite Hx1; apply Hy.

      simpl in Ht1; simpl.
      rewrite Hx1 in Ht1.
      eapply I_eq_neq_prop in Hxi1; eassumption.

     apply Digit.not_1_iff_0 in Hx1.
     rewrite Hx1 in Ht1.
     generalize Hx1; intros Hxi1.
     symmetry in Hxy.
     eapply I_eq_neq_prop in Hxi1; try eassumption.
     destruct Hxi1 as [(Hy, Hx)| (Hy, Hx)].
      destruct di1.
       left.
       split; [ reflexivity | idtac ].
       simpl in Hx, Hy.
       split; intros j; [ do 2 rewrite Hx | do 2 rewrite Hy ]; reflexivity.

       exfalso.
       clear Ht1.
       pose proof (Hn1 di1 (Nat.lt_succ_diag_r di1)) as H.
       rewrite Digit.opp_involutive in H.
       pose proof (Hxy di1) as HH; simpl in HH.
       unfold I_add_i in HH; simpl in HH.
       do 2 rewrite Digit.add_0_r in HH.
       rewrite H in HH.
       apply Digit.add_cancel_l in HH.
       unfold carry in HH; simpl in HH.
       remember (fst_same x 0 (S di1)) as s2 eqn:Hs2 .
       remember (fst_same y 0 (S di1)) as s3 eqn:Hs3 .
       destruct s2 as [dj2| ].
        apply fst_same_sym_iff in Hs2; simpl in Hs2.
        destruct Hs2 as (Hn2, Ht2).
        rewrite Ht2 in HH.
        destruct s3 as [dj3| ]; [ idtac | revert HH; apply Digit.neq_1_0 ].
        simpl in Hy.
        rewrite Hy in HH; revert HH; apply Digit.neq_1_0.

        apply fst_same_sym_iff in Hs2; simpl in Hs2.
        clear H.
        pose proof (Hx 0) as H; simpl in H.
        rewrite Hs2 in H; revert H; apply Digit.neq_1_0.

      right; split; intros di; [ rewrite Ht1; apply Hx | idtac ].
      rewrite Hx1; apply Hy.

  left; intros i.
  rewrite Hs1, Digit.opp_involutive; reflexivity.

 destruct Hxy as [Hxy| Hxy].
  apply I_eqs_eq; assumption.

  destruct Hxy as (i, (Heq, (Hne, Hxy))).
  destruct Hxy as [(Hi, (Hx, Hy))| (Hx, Hy)].
   subst i.
   clear Heq.
   unfold I_eq; intros i; simpl.
   unfold I_add_i; simpl.
   do 2 rewrite Digit.add_0_r.
   rewrite Hx, Hy.
   unfold carry; simpl.
   remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
   remember (fst_same y 0 (S i)) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s1 as [dj1| ].
    destruct Hs1 as (Hn1, Ht1).
    rewrite Ht1, Digit.add_0_r.
    destruct s2 as [dj2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, Digit.add_0_r.
     rewrite Hx in Ht1.
     rewrite Hy in Ht2.
     rewrite <- Ht2 in Ht1; contradiction.

     rewrite Digit.add_1_r.
     apply Digit.neq_eq_opp; assumption.

    rewrite Digit.add_1_r.
    destruct s2 as [di2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, Digit.add_0_r.
     apply Digit.neq_eq_opp in Hne.
     rewrite Hne, Digit.opp_involutive; reflexivity.

     pose proof (Hs1 0) as H.
     rewrite <- Hs2 with (dj := 0) in H.
     rewrite Hx, Hy in H; contradiction.

   unfold I_eq; intros j; simpl.
   unfold I_add_i; simpl.
   do 2 rewrite Digit.add_0_r.
   unfold carry; simpl.
   remember (fst_same x 0 (S j)) as s1 eqn:Hs1 .
   remember (fst_same y 0 (S j)) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s1 as [di1| ].
    destruct Hs1 as (Hn1, Ht1).
    rewrite Ht1, Digit.add_0_r.
    destruct s2 as [di2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, Digit.add_0_r.
     rewrite <- Nat.add_succ_r in Ht1, Ht2.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      apply Heq in H1; assumption.

      subst j.
      destruct (lt_eq_lt_dec di1 di2) as [[H1| H1]| H1].
       apply Hn2 in H1.
       rewrite Hx in Ht1.
       rewrite Hy in Ht2.
       rewrite <- Ht1 in Ht2; contradiction.

       subst di2.
       rewrite <- Ht2, Hx, Hy in Ht1.
       symmetry in Ht1; contradiction.

       apply Hn1 in H1.
       rewrite Hx in Ht1.
       rewrite Hy in Ht2.
       rewrite <- Ht1 in Ht2; contradiction.

      pose proof (Hx (j - i + di1)) as H.
      rewrite Nat.add_succ_r in H.
      rewrite Nat.add_assoc in H.
      apply Nat.lt_le_incl in H1.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      remember (i + j - i) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite H in Ht1; clear H.
      pose proof (Hy (j - i + di2)) as H.
      rewrite Nat.add_succ_r in H.
      rewrite Nat.add_assoc in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      remember (i + j - i) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Ht1, H in Ht2.
      contradiction.

     rewrite Digit.add_1_r.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      pose proof (Hs2 (i - j + di1)) as H.
      rewrite Nat.add_assoc in H.
      generalize H1; intros HH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      remember (j + i - j) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hy in H.
      rewrite H in Hne; clear H.
      pose proof (Hs2 (i - S j)) as H.
      rewrite <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      symmetry in H; contradiction.

      subst j.
      apply Digit.neq_eq_opp; assumption.

      pose proof (Hx (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hxy.
      pose proof (Hy (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hyx.
      rewrite <- Hxy, <- Hyx in Hne.
      apply Digit.neq_eq_opp, Digit.neq_sym; assumption.

    rewrite Digit.add_1_r.
    destruct s2 as [di2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, Digit.add_0_r.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      pose proof (Hs1 (i - j + di2)) as H.
      rewrite Nat.add_assoc in H.
      generalize H1; intros HH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      remember (j + i - j) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hx in H.
      rewrite H in Hne; clear H.
      pose proof (Hs1 (i - S j)) as H.
      rewrite <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      contradiction.

      subst j; symmetry.
      apply Digit.neq_eq_opp, Digit.neq_sym; assumption.

      pose proof (Hy (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hxy.
      pose proof (Hx (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hyx.
      rewrite <- Hxy, <- Hyx in Hne.
      symmetry.
      apply Digit.neq_eq_opp; assumption.

     rewrite Digit.add_1_r; f_equal.
     apply Digit.opp_compat.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      apply Heq; assumption.

      subst j.
      pose proof (Hs1 0) as H.
      rewrite <- Nat.add_succ_r, Hx in H.
      rewrite H in Hne; clear H.
      pose proof (Hs2 0) as H.
      rewrite <- Nat.add_succ_r, Hy in H.
      rewrite H in Hne; clear H.
      exfalso; apply Hne; reflexivity.

      pose proof (Hx (j - i)) as H.
      rewrite Nat.add_succ_r in H.
      generalize H1; intros HH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      rewrite Nat.add_comm, Nat.add_sub in H.
      replace j with (j + 0) in H by apply Nat.add_0_r.
      rewrite Hs1 in H.
      rewrite <- H in Hne; clear H.
      pose proof (Hy (j - i)) as H.
      rewrite Nat.add_succ_r in H.
      generalize H1; intros HH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      rewrite Nat.add_comm, Nat.add_sub in H.
      replace j with (j + 0) in H by apply Nat.add_0_r.
      rewrite Hs2 in H.
      symmetry in H; contradiction.
Qed.

Theorem I_eq_iff : ∀ x y,
  (x = y)%I
  ↔ (x == y)%I ∨
    ∃ i,
    (∀ j, j < i → (x.[j] = y.[j])%D) ∧
    ((i = 0 ∧
     ((∀ j, (x.[j] = 0)%D ∧ (y.[j] = n2d (pred radix))%D) ∨
      (∀ j, (y.[j] = 0)%D ∧ (x.[j] = n2d (pred radix))%D))) ∨
     (d2n (x.[i]) = S (d2n (y.[i]))) ∧
     (∀ di, (x.[i+S di] = 0)%D ∧ (y.[i+S di] = n2d (pred radix))%D) ∨
     (d2n (y.[i]) = S (d2n (x.[i]))) ∧
     (∀ di, (y.[i+S di] = 0)%D ∧ (x.[i+S di] = n2d (pred radix))%D)).
Proof.
intros x y.
split; intros Hxy.
 remember (first_nonzero (seq_eq x y)) as s1 eqn:Hs1 .
 apply first_nonzero_iff in Hs1.
 destruct s1 as [n1| ].
  Focus 2.
  left; unfold seq_eq in Hs1; intros i.
  pose proof (Hs1 i) as H.
  destruct (Digit.eq_dec (x .[ i]) (y .[ i])); [ assumption | idtac ].
  discriminate H.

  right; destruct Hs1 as (Hn1, Ht1).
  unfold seq_eq in Hn1, Ht1.
  destruct (Digit.eq_dec (x .[ n1]) (y .[ n1])) as [H1| H1].
   exfalso; apply Ht1; reflexivity.

   exists n1; clear Ht1.
   split.
    intros i Hi; unfold seq_eq in Hn1.
    apply Hn1 in Hi.
    destruct (Digit.eq_dec (x .[ i]) (y .[ i])); [ assumption | idtac ].
    discriminate Hi.

    destruct n1.
     clear Hn1.
     destruct (Digit.eq_dec (x .[ 0]) 0) as [H2| H2]; simpl.
      apply eq_d2n_0 in H2; rewrite H2; apply eq_d2n_0 in H2.
      destruct (Digit.eq_dec (y .[ 0]) (n2d (pred radix))) as [H3| H3].
       clear H1.
       generalize H3; intros H.
       apply -> digit_d2n_eq_iff in H; rewrite d2n_n2d in H.
       rewrite Nat_pred_mod in H; rewrite H; clear H.
       destruct (eq_nat_dec radix 2) as [Hr| Hr].
        rewrite Hr in H3; simpl in H3; rewrite n2d_1 in H3.
        rewrite Hr; simpl.
bbb.
        destruct (Digit.eq_dec (x .[ 1]) 0) as [H1| H1].
         left; split; [ reflexivity | left; intros i; rewrite n2d_1 ].
         induction i; [ split; assumption | idtac ].
         destruct IHi as (Hx, Hy).
         pose proof (Hxy i) as Hn; unfold I_norm in Hn; simpl in Hn.
         do 2 rewrite NN_add_add_0_r in Hn.
         do 2 rewrite carry_add_add_0_r2 in Hn.
         unfold digit_eq in Hn; simpl in Hn.
         unfold I2NN in Hn at 1; simpl in Hn.
         unfold I2NN in Hn at 2; simpl in Hn.
         apply -> digit_d2n_eq_iff in Hx; rewrite d2n_0 in Hx.
         apply -> digit_d2n_eq_iff in Hy; rewrite d2n_1 in Hy.
         rewrite Hx, Hy, Nat.add_0_l in Hn.
         unfold carry_add in Hn; simpl in Hn.
         remember (fst_neq_pred_r (I2NN x) (S i)) as s2 eqn:Hs2 .
         remember (fst_neq_pred_r (I2NN y) (S i)) as s3 eqn:Hs3 .
         apply first_nonzero_iff in Hs2; simpl in Hs2.
         apply first_nonzero_iff in Hs3; simpl in Hs3.
         destruct s2 as [n2| ].
          destruct Hs2 as (Hn2, Ht2).
          unfold seq_pred_r in Ht2; simpl in Ht2.
          remember (I2NN x (S (i + n2))) as a.
          destruct (eq_nat_dec a (pred radix)) as [H4| H4]; subst a.
           exfalso; apply Ht2; reflexivity.

           clear Ht2.
           unfold I2NN in H4, Hn.
           destruct n2; [ clear Hn2; rewrite Nat.add_0_r in H4, Hn | idtac ].
            split.
             apply eq_d2n_0.
             pose proof (d2n_lt_radix (x .[ S i])) as H.
             rewrite Hr in H4, H; simpl in H4, H.
             remember (d2n (x .[ S i])) as a eqn:Ha .
             destruct a; [ reflexivity | exfalso; apply H4 ].
             destruct a; [ reflexivity | exfalso ].
             apply Nat.nle_gt in H; apply H; clear H.
             do 2 apply le_n_S; apply Nat.le_0_l.

             destruct (lt_dec (d2n (x .[ S i])) (pred radix)) as [H5| H5].
              rewrite Nat.mod_0_l in Hn; [ idtac | apply Digit.radix_neq_0 ].
              destruct s3 as [n3| ].
               destruct Hs3 as (Hn3, Ht3).
               unfold I2NN, seq_pred_r in Ht3; simpl in Ht3.
               remember (d2n (y .[ S (i + n3)])) as a.
               destruct (eq_nat_dec a (pred radix)) as [H6| H6]; subst a.
                exfalso; apply Ht3; reflexivity.

                clear Ht3.
                destruct n3.
                 clear Hn3; rewrite Nat.add_0_r in H6, Hn.
                 destruct (lt_dec (d2n (y .[ S i])) (pred radix)) as [H7| H7].
                  rewrite Nat.mod_1_l in Hn; [ discriminate Hn | idtac ].
                  rewrite Hr; apply Nat.lt_1_2.

                  exfalso; apply H7; clear H7.
                  pose proof (d2n_lt_radix (y .[ S i])) as H.
                  apply Nat_le_neq_lt; [ idtac | assumption ].
                  apply Nat.lt_le_pred; assumption.

                 pose proof (Hn3 0 (Nat.lt_0_succ n3)) as H.
                 unfold seq_pred_r, I2NN in H.
                 rewrite Nat.add_0_r in H.
                 remember (d2n (y .[ S i])) as a.
                 destruct (eq_nat_dec a (pred radix)) as [H7| H7]; subst a.
                  clear H.
                  rewrite Hr in H7; simpl in H7.
                  apply eq_d2n_1; assumption.

                  discriminate H.

               unfold seq_pred_r in Hs3; simpl in Hs3.
               pose proof (Hs3 0) as H.
               unfold I2NN in H; simpl in H.
               rewrite Nat.add_0_r in H.
               remember (d2n (y .[ S i])) as a.
               destruct (eq_nat_dec a (pred radix)) as [H6| H6]; subst a.
                rewrite Hr in H6; simpl in H6.
                apply eq_d2n_1; assumption.

                discriminate H.

              exfalso; apply H5; clear H5.
              pose proof (d2n_lt_radix (x .[ S i])) as H.
              apply Nat_le_neq_lt; [ idtac | assumption ].
              apply Nat.lt_le_pred; assumption.

            rewrite Nat.add_succ_r in Hn.
            remember (d2n (x .[ S (S (i + n2))])) as a.
            destruct (lt_dec a (pred radix)) as [H5| H5]; subst a.
             rewrite Nat.mod_small in Hn; [ idtac | apply Digit.radix_gt_0 ].
             unfold seq_pred_r, I2NN in Hs3; simpl in Hs3.
             destruct s3 as [n3| ].
              destruct Hs3 as (Hn3, Ht3).
              remember (d2n (y .[ S (i + n3)])) as a.
              destruct (eq_nat_dec a (pred radix)) as [H6| H6].
               exfalso; apply Ht3; reflexivity.

               clear Ht3.
               destruct (lt_dec a (pred radix)) as [H7| H7]; subst a.
                rewrite Nat.mod_small in Hn; [ discriminate Hn | idtac ].
                apply Digit.radix_gt_1.

                exfalso; apply H7; clear H7.
                pose proof (d2n_lt_radix (y .[ S (i + n3)])) as H.
                apply Nat_le_neq_lt; [ idtac | assumption ].
                apply Nat.lt_le_pred; assumption.

              clear Hn.
              pose proof (Hn2 0 (Nat.lt_0_succ n2)) as H.
              unfold seq_pred_r, I2NN in H; simpl in H.
              rewrite Nat.add_0_r in H.
              remember (d2n (x .[ S i])) as a.
              destruct (eq_nat_dec a (pred radix)) as [H6| H6]; subst a.
               2: discriminate H.

               clear H.
               pose proof (Hs3 0) as H; rewrite Nat.add_0_r in H.
               remember (d2n (y .[ S i])) as a.
               destruct (eq_nat_dec a (pred radix)) as [H7| H7]; subst a.
                2: discriminate H.

                clear H.
                pose proof (Hxy (S i)) as Hn; unfold I_norm in Hn.
                simpl in Hn.
                do 2 rewrite NN_add_add_0_r in Hn.
                do 2 rewrite carry_add_add_0_r2 in Hn.
                unfold digit_eq in Hn; simpl in Hn.
                unfold I2NN in Hn at 1; simpl in Hn.
                unfold I2NN in Hn at 2; simpl in Hn.
                rewrite H6, H7 in Hn.
                unfold carry_add in Hn; simpl in Hn.
                remember (fst_neq_pred_r (I2NN x) (S (S i))) as s4 eqn:Hs4 .
                remember (fst_neq_pred_r (I2NN y) (S (S i))) as s5 eqn:Hs5 .
                apply first_nonzero_iff in Hs4; simpl in Hs4.
                apply first_nonzero_iff in Hs5; simpl in Hs5.
                destruct s4 as [n4| ].
                 destruct Hs4 as (Hn4, Ht4).
                 unfold seq_pred_r in Ht4; simpl in Ht4.
                 remember (I2NN x (S (S (i + n4)))) as a.
                 destruct (eq_nat_dec a (pred radix)) as [H8| H8]; subst a.
                  exfalso; apply Ht4; reflexivity.

                  clear Ht4.
                  remember (I2NN x (S (S (i + n4)))) as a.
                  destruct (lt_dec a (pred radix)) as [H9| H9]; subst a.
                   rewrite Nat.add_0_r, Nat_pred_mod in Hn.
                   destruct s5 as [n5| ].
                    destruct Hs5 as (Hn5, Ht5).
                    pose proof (Hs3 (S n5)) as H.
                    rewrite Nat.add_succ_r in H.
                    unfold seq_pred_r, I2NN in Ht5; simpl in Ht5.
                    rewrite H in Ht5.
                    exfalso; apply Ht5; reflexivity.

                    rewrite Nat.add_1_r in Hn.
                    pose proof Digit.radix_neq_0 as H.
                    rewrite Nat.succ_pred in Hn; [ idtac | assumption ].
                    rewrite Nat.mod_same in Hn; [ idtac | assumption ].
                    rewrite Hr in Hn; discriminate Hn.

                   exfalso; apply H9; clear H9.
                   pose proof (d2n_lt_radix (x .[ S (S (i + n4))])) as H.
                   apply Nat_le_neq_lt; [ idtac | assumption ].
                   apply Nat.lt_le_pred; assumption.

                 pose proof (Hs4 n2) as H.
                 unfold seq_pred_r, I2NN in H; simpl in H.
                 rewrite Nat.add_succ_r in H4.
                 remember (d2n (x .[ S (S (i + n2))])) as a.
                 destruct (eq_nat_dec a (pred radix)) as [H8| H8]; subst a.
                  contradiction.

                  discriminate H.

             exfalso; apply H5; clear H5.
             pose proof (d2n_lt_radix (x .[ S (S (i + n2))])) as H.
             rewrite Nat.add_succ_r in H4.
             apply Nat_le_neq_lt; [ idtac | assumption ].
             apply Nat.lt_le_pred; assumption.

          destruct s3 as [n3| ].
           destruct Hs3 as (Hn3, Ht3).
           remember (I2NN y (S (i + n3))) as a.
           destruct (lt_dec a (pred radix)) as [H4| H4]; subst a.
            clear Hn.
            pose proof (Hs2 0) as H.
            unfold seq_pred_r in H; simpl in H.
            rewrite Nat.add_0_r in H.
            remember (I2NN x (S i)) as a.
            destruct (eq_nat_dec a (pred radix)) as [H5| H5]; subst a.
             clear H; unfold I2NN in H5.
             destruct n3.
              rewrite Nat.add_0_r in H4.
              unfold I2NN in H4.
              rewrite Hr in H4, H5; simpl in H4, H5.
              apply Nat.lt_1_r in H4.
              pose proof (Hxy (S i)) as Hn; unfold I_norm in Hn.
              simpl in Hn.
              do 2 rewrite NN_add_add_0_r in Hn.
              do 2 rewrite carry_add_add_0_r2 in Hn.
              unfold digit_eq in Hn; simpl in Hn.
              unfold I2NN in Hn at 1; simpl in Hn.
              unfold I2NN in Hn at 2; simpl in Hn.
              rewrite H4, H5 in Hn.
              unfold carry_add in Hn; simpl in Hn.
              remember (fst_neq_pred_r (I2NN x) (S (S i))) as s4 eqn:Hs4 .
              remember (fst_neq_pred_r (I2NN y) (S (S i))) as s5 eqn:Hs5 .
              apply first_nonzero_iff in Hs4; simpl in Hs4.
              apply first_nonzero_iff in Hs5; simpl in Hs5.
              destruct s4 as [n4| ].
               destruct Hs4 as (Hn4, Ht4).
               unfold seq_pred_r in Ht4; simpl in Ht4.
               remember (I2NN x (S (S (i + n4)))) as a.
               destruct (eq_nat_dec a (pred radix)) as [H8| H8]; subst a.
                exfalso; apply Ht4; reflexivity.

                clear Ht4.
                remember (I2NN x (S (S (i + n4)))) as a.
                destruct (lt_dec a (pred radix)) as [H9| H9]; subst a.
                 pose proof Digit.radix_gt_1 as H.
                 rewrite Nat.mod_small in Hn; [ clear H | assumption ].
                 destruct s5 as [n5| ].
                  destruct Hs5 as (Hn5, Ht5).
                  unfold seq_pred_r in Ht5; simpl in Ht5.
                  remember (I2NN y (S (S (i + n5)))) as a.
                  destruct (lt_dec a (pred radix)) as [H6| H6].
                   pose proof Digit.radix_neq_0 as H.
                   rewrite Nat.mod_0_l in Hn; [ clear H | assumption ].
                   discriminate Hn.

                   destruct (eq_nat_dec a (pred radix)) as [H7| H7]; subst a.
                    exfalso; apply Ht5; reflexivity.

                    exfalso; apply H6; clear H6.
                    pose proof (d2n_lt_radix (y .[ S (S (i + n5))])) as H.
                    apply Nat_le_neq_lt; [ idtac | assumption ].
                    apply Nat.lt_le_pred; assumption.

                  clear Hn Hn3.
                  pose proof (Hs5 0) as H.
                  unfold seq_pred_r, I2NN in H.
                  rewrite Nat.add_0_r in H.
                  remember (d2n (y .[ S (S i)])) as a.
                  destruct (eq_nat_dec a (pred radix)) as [H6| H6]; subst a.
                   2: discriminate H.

                   clear H.
                   assert (I2NN x (S (S (i + n4))) = 0) as H7.
                    rewrite Hr in H9; simpl in H9.
                    apply Nat.lt_1_r; assumption.

                    clear H8 H9.
                    destruct n4.
                     rewrite Nat.add_0_r in H7.
                     pose proof (Hs2 1) as H.
                     unfold seq_pred_r in H; simpl in H.
                     rewrite Nat.add_1_r in H.
                     rewrite H7 in H.
                     destruct (eq_nat_dec 0 (pred radix)) as [H9| H9].
                      rewrite Hr in H9; discriminate H9.

                      discriminate H.

                     pose proof (Hn4 0 (Nat.lt_0_succ n4)) as H.
                     unfold seq_pred_r, I2NN in H; simpl in H.
                     rewrite Nat.add_0_r in H.
                     remember (d2n (x .[ S (S i)])) as a.
                     destruct (eq_nat_dec a (pred radix)) as [H8| H8];
                      subst a.
                      2: discriminate H.

                      clear H.
                      pose proof (Hxy (S (S i))) as Hn.
                      unfold I_norm in Hn; simpl in Hn.
                      simpl in Hn.
                      do 2 rewrite NN_add_add_0_r in Hn.
                      do 2 rewrite carry_add_add_0_r2 in Hn.
                      unfold digit_eq in Hn; simpl in Hn.
                      unfold I2NN in Hn at 1; simpl in Hn.
                      unfold I2NN in Hn at 2; simpl in Hn.
                      rewrite H6, H8 in Hn.
                      unfold carry_add in Hn; simpl in Hn.
                      remember (fst_neq_pred_r (I2NN x) (S (S (S i)))) as s6
                       eqn:Hs6 .
                      remember (fst_neq_pred_r (I2NN y) (S (S (S i)))) as s7
                       eqn:Hs7 .
                      apply first_nonzero_iff in Hs6; simpl in Hs6.
                      apply first_nonzero_iff in Hs7; simpl in Hs7.
                      destruct s6 as [n6| ].
                       destruct Hs6 as (Hn6, Ht6).
                       unfold seq_pred_r in Ht6; simpl in Ht6.
                       remember (I2NN x (S (S (S (i + n6))))) as a.
                       destruct (eq_nat_dec a (pred radix)) as [H9| H9];
                        subst a.
                        exfalso; apply Ht6; reflexivity.

                        clear Ht6.
                        remember (I2NN x (S (S (S (i + n6))))) as a.
                        destruct (lt_dec a (pred radix)) as [H10| H10];
                         subst a.
                         rewrite Nat.add_0_r in Hn.
                         rewrite Nat_pred_mod in Hn.
                         destruct s7 as [n7| ].
                          destruct Hs7 as (Hn7, Ht7).
                          unfold seq_pred_r in Ht7; simpl in Ht7.
                          remember (I2NN y (S (S (S (i + n7))))) as a.
                          destruct (eq_nat_dec a (pred radix)) as [H11| H11].
                           exfalso; apply Ht7; reflexivity.

                           clear Ht7.
                           destruct (lt_dec a (pred radix)) as [H12| H12];
                            subst a.
                            pose proof (Hs5 (S n7)) as H.
                            unfold seq_pred_r in H; simpl in H.
                            rewrite Nat.add_succ_r in H.
                            remember (I2NN y (S (S (S (i + n7))))) as a.
                            destruct (eq_nat_dec a (pred radix))
                             as [H13| H13].
                             contradiction.

                             discriminate H.

                            exfalso; apply H12; clear H12.
                            pose proof
                             (d2n_lt_radix (y .[ S (S (S (i + n7)))])) 
                             as H.
                            apply Nat_le_neq_lt; [ idtac | assumption ].
                            apply Nat.lt_le_pred; assumption.

                          rewrite Nat.add_1_r, Nat.succ_pred in Hn.
                           rewrite Nat.mod_same in Hn;
                            [ idtac | apply Digit.radix_neq_0 ].
                           rewrite Hr in Hn; discriminate Hn.

                           apply Digit.radix_neq_0.

                         exfalso; apply H10; clear H10.
                         pose proof (d2n_lt_radix (x .[ S (S (S (i + n6)))]))
                          as H.
                         apply Nat_le_neq_lt; [ idtac | assumption ].
                         apply Nat.lt_le_pred; assumption.

                       destruct s7 as [n7| ].
                        destruct Hs7 as (Hn7, Ht7).
                        unfold seq_pred_r in Ht7; simpl in Ht7.
                        remember (I2NN y (S (S (S (i + n7))))) as a.
                        destruct (eq_nat_dec a (pred radix)) as [H9| H9].
                         exfalso; apply Ht7; reflexivity.

                         clear Ht7.
                         destruct (lt_dec a (pred radix)) as [H10| H10];
                          subst a.
                          rewrite Nat.add_1_r, Nat.succ_pred in Hn.
                           rewrite Nat.mod_same in Hn;
                            [ idtac | apply Digit.radix_neq_0 ].
                           rewrite Hr in Hn; discriminate Hn.

                           apply Digit.radix_neq_0.

                          exfalso; apply H10; clear H10.
                          pose proof
                           (d2n_lt_radix (y .[ S (S (S (i + n7)))])) 
                           as H.
                          apply Nat_le_neq_lt; [ idtac | assumption ].
                          apply Nat.lt_le_pred; assumption.

                        clear Hn.
                        rewrite Nat.add_succ_r in H7.
                        pose proof (Hs6 n4) as H.
                        unfold seq_pred_r in H; simpl in H.
                        rewrite H7 in H.
                        destruct (eq_nat_dec 0 (pred radix)) as [H9| H9].
                         rewrite Hr in H9; discriminate H9.

                         discriminate H.

                 exfalso; apply H9; clear H9.
                 pose proof (d2n_lt_radix (x .[ S (S (i + n4))])) as H.
                 apply Nat_le_neq_lt; [ idtac | assumption ].
                 apply Nat.lt_le_pred; assumption.

               destruct s5 as [n5| ].
                destruct Hs5 as (Hn5, Ht5).
                unfold seq_pred_r in Ht5; simpl in Ht5.
                remember (I2NN y (S (S (i + n5)))) as a.
                destruct (eq_nat_dec a (pred radix)) as [H6| H6].
                 exfalso; apply Ht5; reflexivity.

                 clear Ht5.
                 destruct (lt_dec a (pred radix)) as [H7| H7]; subst a.
vvv.

(* false if radix = 2, the right case could apply *)
       left; split; [ reflexivity | idtac ].
       left; clear H1; intros i.
       induction i; [ split; assumption | idtac ].
       pose proof (Hxy i) as Hn; unfold I_norm in Hn; simpl in Hn.
       do 2 rewrite NN_add_add_0_r in Hn.
       do 2 rewrite carry_add_add_0_r2 in Hn.
       unfold digit_eq in Hn; simpl in Hn.
       unfold I2NN in Hn at 1; simpl in Hn.
       unfold I2NN in Hn at 2; simpl in Hn.
       destruct IHi as (Hx, Hy).
       apply -> digit_d2n_eq_iff in Hx; rewrite d2n_0 in Hx.
       apply -> digit_d2n_eq_iff in Hy; rewrite d2n_n2d, Nat_pred_mod in Hy.
       rewrite Hx, Hy, Nat.add_0_l in Hn.
       unfold carry_add in Hn; simpl in Hn.
       remember (fst_neq_pred_r (I2NN x) (S i)) as s2 eqn:Hs2 .
       remember (fst_neq_pred_r (I2NN y) (S i)) as s3 eqn:Hs3 .
       apply first_nonzero_iff in Hs2; simpl in Hs2.
       apply first_nonzero_iff in Hs3; simpl in Hs3.
       destruct s2 as [n2| ].
        destruct Hs2 as (Hn2, Ht2).
        unfold seq_pred_r in Ht2; simpl in Ht2.
        destruct (eq_nat_dec (I2NN x (S (i + n2))) (pred radix)) as [H4| H4].
         exfalso; apply Ht2; reflexivity.

         clear Ht2.
         unfold I2NN in H4, Hn.
         destruct n2; [ clear Hn2; rewrite Nat.add_0_r in H4, Hn | idtac ].
          destruct (lt_dec (d2n (x .[ S i])) (pred radix)) as [H1| H1].
           rewrite Nat.mod_0_l in Hn; [ idtac | apply Digit.radix_neq_0 ].
           destruct s3 as [n3| ].
            destruct Hs3 as (Hn3, Ht3).
            unfold I2NN, seq_pred_r in Ht3; simpl in Ht3.
            remember (d2n (y .[ S (i + n3)])) as a.
            destruct (eq_nat_dec a (pred radix)) as [H5| H5]; subst a.
             exfalso; apply Ht3; reflexivity.

             clear Ht3.
             destruct n3.
              clear Hn3; rewrite Nat.add_0_r in H5, Hn.
              destruct (lt_dec (d2n (y .[ S i])) (pred radix)) as [H6| H6].
               rewrite Nat.add_0_r, Nat_pred_mod in Hn; symmetry in Hn.
               apply Nat.eq_pred_0 in Hn; exfalso.
               destruct Hn; revert H; [ apply Digit.radix_neq_0 | idtac ].
               apply Digit.radix_neq_1.

               exfalso; apply H6; clear H6.
               pose proof (d2n_lt_radix (y .[ S i])) as H.
               apply Nat_le_neq_lt; [ idtac | assumption ].
               apply Nat.lt_le_pred; assumption.

              pose proof (Hn3 0 (Nat.lt_0_succ n3)) as H.
              unfold seq_pred_r, I2NN in H.
              rewrite Nat.add_0_r in H.
              remember (d2n (y .[ S i])) as a.
              destruct (eq_nat_dec a (pred radix)) as [H6| H6]; subst a.
               clear H.
               remember (d2n (y .[ S (i + S n3)])) as a.
               destruct (lt_dec a (pred radix)) as [H7| H7]; subst a.
                rewrite Nat.add_0_r, Nat_pred_mod in Hn; symmetry in Hn.
                apply Nat.eq_pred_0 in Hn; exfalso.
                destruct Hn; revert H; [ apply Digit.radix_neq_0 | idtac ].
                apply Digit.radix_neq_1.

                exfalso; apply H7; clear H7.
                pose proof (d2n_lt_radix (y .[ S (i + S n3)])) as H.
                apply Nat_le_neq_lt; [ idtac | assumption ].
                apply Nat.lt_le_pred; assumption.

               discriminate H.

            unfold seq_pred_r in Hs3; simpl in Hs3.
            pose proof (Hs3 0) as H.
            unfold I2NN in H; simpl in H.
            rewrite Nat.add_0_r in H.
            remember (d2n (y .[ S i])) as a.
            destruct (eq_nat_dec a (pred radix)) as [H5| H5]; subst a.
             clear Hn H.
             pose proof (Hxy (S i)) as Hn; unfold I_norm in Hn; simpl in Hn.
             do 2 rewrite NN_add_add_0_r in Hn.
             do 2 rewrite carry_add_add_0_r2 in Hn.
             unfold digit_eq in Hn; simpl in Hn.
             unfold I2NN in Hn at 1; simpl in Hn.
             unfold I2NN in Hn at 2; simpl in Hn.
             rewrite H5 in Hn.
             unfold carry_add in Hn; simpl in Hn.
             remember (fst_neq_pred_r (I2NN x) (S (S i))) as s4 eqn:Hs4 .
             remember (fst_neq_pred_r (I2NN y) (S (S i))) as s5 eqn:Hs5 .
             apply first_nonzero_iff in Hs4; simpl in Hs4.
             apply first_nonzero_iff in Hs5; simpl in Hs5.
             destruct s4 as [n4| ].
              destruct Hs4 as (Hn4, Ht4).
              unfold seq_pred_r in Ht4; simpl in Ht4.
              remember (I2NN x (S (S (i + n4)))) as a.
              destruct (eq_nat_dec a (pred radix)) as [H6| H6]; subst a.
               exfalso; apply Ht4; reflexivity.

               clear Ht4.
               remember (I2NN x (S (S (i + n4)))) as a.
               destruct (lt_dec a (pred radix)) as [H7| H7]; subst a.
                rewrite Nat.add_0_r in Hn.
                destruct s5 as [n5| ].
                 destruct Hs5 as (Hn5, Ht5).
                 remember (I2NN y (S (S (i + n5)))) as a.
                 destruct (lt_dec a (pred radix)) as [H8| H8]; subst a.
                  pose proof (Hs3 (S n5)) as H.
                  rewrite Nat.add_succ_r in H.
                  remember (I2NN y (S (S (i + n5)))) as a.
                  destruct (eq_nat_dec a (pred radix)) as [H9| H9]; subst a.
                   rewrite H9 in H8.
                   exfalso; revert H8; apply Nat.lt_irrefl.

                   discriminate H.

                  rewrite Nat.add_1_r in Hn; simpl in Hn.
                  pose proof Digit.radix_neq_0 as H.
                  rewrite Nat.succ_pred in Hn; [ idtac | assumption ].
                  rewrite Nat.mod_same in Hn; [ idtac | assumption ].
                  rewrite Nat.mod_small in Hn; [ idtac | apply d2n_lt_radix ].
                  apply eq_d2n_0 in Hn.
                  split; [ assumption | idtac ].
                  apply digit_d2n_eq_iff; rewrite d2n_n2d, Nat_pred_mod.
                  assumption.

                 unfold seq_pred_r in Hs5; simpl in Hs5.
                 rewrite Nat.add_1_r in Hn; simpl in Hn.
                 pose proof Digit.radix_neq_0 as H.
                 rewrite Nat.succ_pred in Hn; [ idtac | assumption ].
                 rewrite Nat.mod_same in Hn; [ idtac | assumption ].
                 rewrite Nat.mod_small in Hn; [ idtac | apply d2n_lt_radix ].
                 apply eq_d2n_0 in Hn.
                 split; [ assumption | idtac ].
                 apply digit_d2n_eq_iff; rewrite d2n_n2d, Nat_pred_mod.
                 assumption.

                exfalso; apply H7; clear H7.
                pose proof (d2n_lt_radix (x .[ S (S (i + n4))])) as H.
                apply Nat_le_neq_lt; [ idtac | assumption ].
                apply Nat.lt_le_pred; assumption.

              unfold seq_pred_r in Hs4; simpl in Hs4.
              destruct s5 as [n5| ].
               destruct Hs5 as (Hn5, Ht5).
               remember (I2NN y (S (S (i + n5)))) as a.
               destruct (lt_dec a (pred radix)) as [H8| H8]; subst a.
                pose proof (Hs3 (S n5)) as H.
                rewrite Nat.add_succ_r in H.
                remember (I2NN y (S (S (i + n5)))) as a.
                destruct (eq_nat_dec a (pred radix)) as [H9| H9]; subst a.
                 rewrite H9 in H8.
                 exfalso; revert H8; apply Nat.lt_irrefl.

                 discriminate H.

                do 2 rewrite Nat.add_1_r in Hn; simpl in Hn.
                pose proof Digit.radix_neq_0 as H.
                rewrite Nat.succ_pred in Hn; [ idtac | assumption ].
                rewrite Nat.mod_same in Hn; [ idtac | assumption ].
                rewrite Nat.mod_small in Hn; [ discriminate Hn | idtac ].
                rewrite <- Nat.succ_pred; [ idtac | assumption ].
                apply lt_n_S; assumption.

               do 2 rewrite Nat.add_1_r in Hn; simpl in Hn.
               pose proof Digit.radix_neq_0 as H.
               rewrite Nat.succ_pred in Hn; [ idtac | assumption ].
               rewrite Nat.mod_same in Hn; [ idtac | assumption ].
               rewrite Nat.mod_small in Hn; [ discriminate Hn | idtac ].
               rewrite <- Nat.succ_pred; [ idtac | assumption ].
               apply lt_n_S; assumption.

             discriminate H.

           exfalso; apply H1; clear H1.
           pose proof (d2n_lt_radix (x .[ S i])) as H.
           apply Nat_le_neq_lt; [ idtac | assumption ].
           apply Nat.lt_le_pred; assumption.

          pose proof Hn2 0 (Nat.lt_0_succ n2) as H.
          unfold seq_pred_r in H; rewrite Nat.add_0_r in H.
          destruct s3 as [n3| ].
           destruct Hs3 as (Hn3, Ht3).
           unfold seq_pred_r in Ht3; simpl in Ht3.
           rewrite Nat.add_succ_r in Hn.
           unfold I2NN in H, Ht3; simpl in H, Ht3.
           remember (d2n (x .[ S (S (i + n2))])) as a.
           destruct (lt_dec a (pred radix)) as [H1| H1]; subst a.
            remember (d2n (y .[ S (i + n3)])) as a.
            destruct (eq_nat_dec a (pred radix)) as [H5| H5]; subst a.
             exfalso; apply Ht3; reflexivity.

             clear Ht3 H.
             remember (d2n (y .[ S (i + n3)])) as a.
             destruct (lt_dec a (pred radix)) as [H6| H6]; subst a.
              rewrite Nat.mod_0_l in Hn; [ idtac | apply Digit.radix_neq_0 ].
              rewrite Nat.add_0_r, Nat_pred_mod in Hn; symmetry in Hn.
              apply Nat.eq_pred_0 in Hn; exfalso.
              destruct Hn; revert H; [ apply Digit.radix_neq_0 | idtac ].
              apply Digit.radix_neq_1.

              exfalso; apply H6; clear H6.
              pose proof (d2n_lt_radix (y .[ S (i + n3)])) as H.
              apply Nat_le_neq_lt; [ idtac | assumption ].
              apply Nat.lt_le_pred; assumption.

            exfalso; apply H1; clear H1 H.
            rewrite Nat.add_succ_r in H4.
            pose proof (d2n_lt_radix (x .[ S (S (i + n2))])) as H.
            apply Nat_le_neq_lt; [ idtac | assumption ].
            apply Nat.lt_le_pred; assumption.

           remember (d2n (x .[ S (i + S n2)])) as a.
           destruct (lt_dec a (pred radix)) as [H1| H1]; subst a.
            rename H into Hxi.
            unfold seq_pred_r in Hs3; simpl in Hs3.
            pose proof Hs3 0 as H; rewrite Nat.add_0_r in H.
            remember (I2NN y (S i)) as a.
            destruct (eq_nat_dec a (pred radix)) as [H5| H5]; subst a.
             clear H; unfold I2NN in H5.
             remember (I2NN x (S i)) as a.
             destruct (eq_nat_dec a (pred radix)) as [H6| H6]; subst a.
              unfold I2NN in H6; clear Hn Hxi.
Set Printing Width 65. Show.
destruct radix; simpl in *. Focus 2.
destruct n; simpl in *. Focus 2.
destruct n; simpl in *.
bbb.

SearchAbout (_ → S _ < _).
apply Nat.lt_pred_lt.

rewrite Nat_mod_succ_l in Hn; [ discriminate Hn|].

                  rewrite Nat.mod_small in Hn; [ idtac | apply d2n_lt_radix ].
                  apply eq_d2n_0 in Hn.
                  split; [ assumption | idtac ].
                  apply digit_d2n_eq_iff; rewrite d2n_n2d, Nat_pred_mod.
                  assumption.

                 unfold seq_pred_r in Hs5; simpl in Hs5.
                 rewrite Nat.add_1_r in Hn; simpl in Hn.
                 pose proof Digit.radix_neq_0 as H.
                 rewrite Nat.succ_pred in Hn; [ idtac | assumption ].
                 rewrite Nat.mod_same in Hn; [ idtac | assumption ].
                 rewrite Nat.mod_small in Hn; [ idtac | apply d2n_lt_radix ].
                 apply eq_d2n_0 in Hn.
                 split; [ assumption | idtac ].
                 apply digit_d2n_eq_iff; rewrite d2n_n2d, Nat_pred_mod.
                 assumption.

                exfalso; apply H7; clear H7.
                pose proof d2n_lt_radix (x.[S (S (i + n4))]) as H.
                apply Nat_le_neq_lt; [ idtac | assumption ].
                apply Nat.lt_le_pred; assumption.
bbb.
Set Printing Width 65. Show.
             exfalso; apply Ht3; reflexivity.

             clear Ht3.
             destruct n3.
              clear Hn3; rewrite Nat.add_0_r in H5, Hn.
              destruct (lt_dec (d2n (y .[ S i])) (pred radix)) as [H6| H6].
               rewrite Nat.add_0_r, Nat_pred_mod in Hn; symmetry in Hn.
               apply Nat.eq_pred_0 in Hn; exfalso.
               destruct Hn; revert H; [ apply Digit.radix_neq_0 | idtac ].
               apply Digit.radix_neq_1.

               exfalso; apply H6; clear H6.
               pose proof d2n_lt_radix (y.[S i]) as H.
               apply Nat_le_neq_lt; [ idtac | assumption ].
               apply Nat.lt_le_pred; assumption.

              pose proof Hn3 0 (Nat.lt_0_succ n3) as H.
bbb.


           rewrite Nat.mod_0_l in Hn; [ idtac | apply Digit.radix_neq_0 ].
           destruct s3 as [n3| ].
            destruct Hs3 as (Hn3, Ht3).
            unfold seq_pred_r in Ht3; simpl in Ht3.
            destruct (eq_nat_dec (I2NN y (S (i + n3))) (pred radix)) as [H5| H5].
            exfalso; apply Ht3; reflexivity.
bbb.
   destruct n1.
    left; split; [ reflexivity | clear Hn1 ].
    destruct (Digit.eq_dec (x.[0]) 0) as [H1| H1]; [ left | right ].
     intros i.
     pose proof Hxy i as Hn.
     unfold I_norm in Hn; simpl in Hn.
     do 2 rewrite NN_add_add_0_r in Hn.
     do 2 rewrite carry_add_add_0_r2 in Hn.
     unfold digit_eq in Hn; simpl in Hn.
     unfold I2NN in Hn at 1; simpl in Hn.
     unfold I2NN in Hn at 2; simpl in Hn.
     unfold carry_add in Hn; simpl in Hn.
     remember (fst_neq_pred_r (I2NN x) (S i)) as s2 eqn:Hs2.
     remember (fst_neq_pred_r (I2NN y) (S i)) as s3 eqn:Hs3.
     apply first_nonzero_iff in Hs2; simpl in Hs2.
     apply first_nonzero_iff in Hs3; simpl in Hs3.
     destruct s2 as [n2| ].
      destruct Hs2 as (Hn2, Ht2).
      unfold seq_pred_r in Ht2; simpl in Ht2.
      destruct (eq_nat_dec (I2NN x (S (i + n2))) (pred radix)) as [H2| H2].
       exfalso; apply Ht2; reflexivity.

       clear Ht2.
       destruct s3 as [n3| ].
        destruct Hs3 as (Hn3, Ht3).
        unfold seq_pred_r in Ht3.
bbb.

    unfold seq_eq in Ht1.
    destruct (Digit.eq_dec (x .[ 0]) (y .[ 0])) as [H1| H1].
     exfalso; apply Ht1; reflexivity.

     clear Hn1 Ht1.
     pose proof Hxy 0 as Hn; simpl in Hn.
     do 2 rewrite NN_add_add_0_r in Hn.
     do 2 rewrite carry_add_add_0_r2 in Hn.
     unfold digit_eq in Hn; simpl in Hn.
     unfold I2NN in Hn at 1; simpl in Hn.
     unfold I2NN in Hn at 2; simpl in Hn.
     unfold carry_add in Hn; simpl in Hn.
     remember (fst_neq_pred_r (I2NN x) 1) as s2 eqn:Hs2.
     remember (fst_neq_pred_r (I2NN y) 1) as s3 eqn:Hs3.
     apply first_nonzero_iff in Hs2; simpl in Hs2.
     apply first_nonzero_iff in Hs3; simpl in Hs3.
     destruct s2 as [n2| ].
      destruct Hs2 as (Hn2, Ht2).
      unfold seq_pred_r in Ht2; simpl in Ht2.
      destruct (eq_nat_dec (I2NN x (S n2)) (pred radix)) as [H2| H2].
       exfalso; apply Ht2; reflexivity.

       clear Ht2.
bbb.

   unfold seq_eq in Ht1.
   destruct (lt_eq_lt_dec (d2n (x.[n1])) (d2n (y.[n1]))) as [[H1| H1]| H1].
    right; split; clear Ht1.
    unfold seq_eq in Hn1.
    pose proof Hxy n1 as Hn; simpl in Hn.
    do 2 rewrite NN_add_add_0_r in Hn.
    do 2 rewrite carry_add_add_0_r2 in Hn.
    unfold digit_eq in Hn; simpl in Hn.
    unfold I2NN in Hn at 1; simpl in Hn.
    unfold I2NN in Hn at 2; simpl in Hn.
    unfold carry_add in Hn; simpl in Hn.
    remember (fst_neq_pred_r (I2NN x) (S n1)) as s2 eqn:Hs2.
    remember (fst_neq_pred_r (I2NN y) (S n1)) as s3 eqn:Hs3.
    apply first_nonzero_iff in Hs2; simpl in Hs2.
    apply first_nonzero_iff in Hs3; simpl in Hs3.
    destruct s2 as [n2| ].
     destruct Hs2 as (Hn2, Ht2).
     unfold seq_pred_r in Ht2; simpl in Ht2.
     destruct (eq_nat_dec (I2NN x (S (n1 + n2))) (pred radix)) as [H2| H2].
      exfalso; apply Ht2; reflexivity.

      clear Ht2.
      destruct (lt_dec (I2NN x (S (n1 + n2))) (pred radix)) as [H3| H3].
       unfold I2NN in H3; simpl in H3.
       unfold seq_pred_r in Hn2; simpl in Hn2.
bbb.

      destruct s3 as [n3| ].
       destruct Hs3 as (Hn3, Ht3).
       unfold seq_pred_r in Ht3; simpl in Ht3.
       destruct ( eq_nat_dec (I2NN y (S (n1 + n3))) (pred radix)) as [H3| H3].
        exfalso; apply Ht3; reflexivity.

        clear Ht3.
Print seq_pred_r.
bbb.

    rewrite carry_add_compat with (v := I2NN y) in Hn.
     Focus 2.
     intros i; unfold I2NN; simpl.

    unfold I2NN in Hn; simpl in Hn.
    unfold carry_add in Hn.
SearchAbout d2n.

    rewrite <- Nat.add_mod_idemp_l in Hn; [ idtac | apply Digit.radix_neq_0 ].
    symmetry in Hn.
    rewrite <- Nat.add_mod_idemp_l in Hn; [ idtac | apply Digit.radix_neq_0 ].
    symmetry in Hn.
SearchAbout (_ mod _ = _ mod _).

bbb.

    rewrite carry_add_add_0_r in Hn at 1.
bbb.

    unfold digit_eq in Hn; simpl in Hn.
    rewrite I_zero_NN_zero in Hn at 1.
bbb.

 remember (fst_neq_pred_r x (- y) 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Ht1).
  right; exists di1.
  split.
   intros j Hdj.
   rewrite Hn1; [ idtac | assumption ].
   rewrite Digit.opp_involutive; reflexivity.

   split.
    intros H; rewrite Ht1 in H.
    revert H; apply Digit.no_fixpoint_opp.

    apply Digit.opp_sym in Ht1.
    destruct (Digit.eq_dec (x .[ di1]) 1) as [Hx1| Hx1].
     generalize Hx1; intros Hxi1.
     eapply I_eq_neq_prop in Hxi1; try eassumption.
      destruct Hxi1 as [(Hx, Hy)| (Hx, Hy)].
       destruct di1.
        left.
        split; [ reflexivity | idtac ].
        simpl in Hx, Hy.
        split; intros j; [ do 2 rewrite Hx | do 2 rewrite Hy ]; reflexivity.

        pose proof (Hn1 di1 (Nat.lt_succ_diag_r di1)) as H.
        rewrite Digit.opp_involutive in H.
        pose proof (Hxy di1) as HH; simpl in HH.
        unfold I_add_i in HH; simpl in HH.
        do 2 rewrite Digit.add_0_r in HH.
        rewrite H in HH.
        unfold carry in HH; simpl in HH.
        remember (fst_same x 0 (S di1)) as s2 eqn:Hs2 .
        remember (fst_same y 0 (S di1)) as s3 eqn:Hs3 .
        destruct s2 as [dj2| ].
         apply fst_same_sym_iff in Hs2; simpl in Hs2.
         destruct Hs2 as (Hn2, Ht2).
         rewrite <- Nat.add_succ_l, Hx in Ht2.
         discr_digit Ht2.

         apply fst_same_sym_iff in Hs3; simpl in Hs3.
         destruct s3 as [dj3| ]; [ idtac | clear HH ].
          rewrite <- Nat.add_succ_l, Hy, Digit.add_0_r in HH.
          exfalso; revert HH; apply Digit.no_fixpoint_opp.

          pose proof (Hy 0) as HH; simpl in HH.
          rewrite Hs3 in HH.
          discr_digit HH.

       rewrite Hx1 in Ht1.
       right; split; intros di; [ rewrite Ht1; apply Hx | idtac ].
       rewrite Hx1; apply Hy.

      simpl in Ht1; simpl.
      rewrite Hx1 in Ht1.
      eapply I_eq_neq_prop in Hxi1; eassumption.

     apply Digit.not_1_iff_0 in Hx1.
     rewrite Hx1 in Ht1.
     generalize Hx1; intros Hxi1.
     symmetry in Hxy.
     eapply I_eq_neq_prop in Hxi1; try eassumption.
     destruct Hxi1 as [(Hy, Hx)| (Hy, Hx)].
      destruct di1.
       left.
       split; [ reflexivity | idtac ].
       simpl in Hx, Hy.
       split; intros j; [ do 2 rewrite Hx | do 2 rewrite Hy ]; reflexivity.

       exfalso.
       clear Ht1.
       pose proof (Hn1 di1 (Nat.lt_succ_diag_r di1)) as H.
       rewrite Digit.opp_involutive in H.
       pose proof (Hxy di1) as HH; simpl in HH.
       unfold I_add_i in HH; simpl in HH.
       do 2 rewrite Digit.add_0_r in HH.
       rewrite H in HH.
       apply Digit.add_cancel_l in HH.
       unfold carry in HH; simpl in HH.
       remember (fst_same x 0 (S di1)) as s2 eqn:Hs2 .
       remember (fst_same y 0 (S di1)) as s3 eqn:Hs3 .
       destruct s2 as [dj2| ].
        apply fst_same_sym_iff in Hs2; simpl in Hs2.
        destruct Hs2 as (Hn2, Ht2).
        rewrite Ht2 in HH.
        destruct s3 as [dj3| ]; [ idtac | revert HH; apply Digit.neq_1_0 ].
        simpl in Hy.
        rewrite Hy in HH; revert HH; apply Digit.neq_1_0.

        apply fst_same_sym_iff in Hs2; simpl in Hs2.
        clear H.
        pose proof (Hx 0) as H; simpl in H.
        rewrite Hs2 in H; revert H; apply Digit.neq_1_0.

      right; split; intros di; [ rewrite Ht1; apply Hx | idtac ].
      rewrite Hx1; apply Hy.

  left; intros i.
  rewrite Hs1, Digit.opp_involutive; reflexivity.

 destruct Hxy as [Hxy| Hxy].
  apply I_eqs_eq; assumption.

  destruct Hxy as (i, (Heq, (Hne, Hxy))).
  destruct Hxy as [(Hi, (Hx, Hy))| (Hx, Hy)].
   subst i.
   clear Heq.
   unfold I_eq; intros i; simpl.
   unfold I_add_i; simpl.
   do 2 rewrite Digit.add_0_r.
   rewrite Hx, Hy.
   unfold carry; simpl.
   remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
   remember (fst_same y 0 (S i)) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s1 as [dj1| ].
    destruct Hs1 as (Hn1, Ht1).
    rewrite Ht1, Digit.add_0_r.
    destruct s2 as [dj2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, Digit.add_0_r.
     rewrite Hx in Ht1.
     rewrite Hy in Ht2.
     rewrite <- Ht2 in Ht1; contradiction.

     rewrite Digit.add_1_r.
     apply Digit.neq_eq_opp; assumption.

    rewrite Digit.add_1_r.
    destruct s2 as [di2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, Digit.add_0_r.
     apply Digit.neq_eq_opp in Hne.
     rewrite Hne, Digit.opp_involutive; reflexivity.

     pose proof (Hs1 0) as H.
     rewrite <- Hs2 with (dj := 0) in H.
     rewrite Hx, Hy in H; contradiction.

   unfold I_eq; intros j; simpl.
   unfold I_add_i; simpl.
   do 2 rewrite Digit.add_0_r.
   unfold carry; simpl.
   remember (fst_same x 0 (S j)) as s1 eqn:Hs1 .
   remember (fst_same y 0 (S j)) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s1 as [di1| ].
    destruct Hs1 as (Hn1, Ht1).
    rewrite Ht1, Digit.add_0_r.
    destruct s2 as [di2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, Digit.add_0_r.
     rewrite <- Nat.add_succ_r in Ht1, Ht2.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      apply Heq in H1; assumption.

      subst j.
      destruct (lt_eq_lt_dec di1 di2) as [[H1| H1]| H1].
       apply Hn2 in H1.
       rewrite Hx in Ht1.
       rewrite Hy in Ht2.
       rewrite <- Ht1 in Ht2; contradiction.

       subst di2.
       rewrite <- Ht2, Hx, Hy in Ht1.
       symmetry in Ht1; contradiction.

       apply Hn1 in H1.
       rewrite Hx in Ht1.
       rewrite Hy in Ht2.
       rewrite <- Ht1 in Ht2; contradiction.

      pose proof (Hx (j - i + di1)) as H.
      rewrite Nat.add_succ_r in H.
      rewrite Nat.add_assoc in H.
      apply Nat.lt_le_incl in H1.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      remember (i + j - i) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite H in Ht1; clear H.
      pose proof (Hy (j - i + di2)) as H.
      rewrite Nat.add_succ_r in H.
      rewrite Nat.add_assoc in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      remember (i + j - i) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite <- Ht1, H in Ht2.
      contradiction.

     rewrite Digit.add_1_r.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      pose proof (Hs2 (i - j + di1)) as H.
      rewrite Nat.add_assoc in H.
      generalize H1; intros HH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      remember (j + i - j) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hy in H.
      rewrite H in Hne; clear H.
      pose proof (Hs2 (i - S j)) as H.
      rewrite <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      symmetry in H; contradiction.

      subst j.
      apply Digit.neq_eq_opp; assumption.

      pose proof (Hx (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hxy.
      pose proof (Hy (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hyx.
      rewrite <- Hxy, <- Hyx in Hne.
      apply Digit.neq_eq_opp, Digit.neq_sym; assumption.

    rewrite Digit.add_1_r.
    destruct s2 as [di2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, Digit.add_0_r.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      pose proof (Hs1 (i - j + di2)) as H.
      rewrite Nat.add_assoc in H.
      generalize H1; intros HH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      remember (j + i - j) as k eqn:Hk .
      rewrite Nat.add_comm, Nat.add_sub in Hk; subst k.
      rewrite <- Nat.add_succ_r in H.
      rewrite Hx in H.
      rewrite H in Hne; clear H.
      pose proof (Hs1 (i - S j)) as H.
      rewrite <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      contradiction.

      subst j; symmetry.
      apply Digit.neq_eq_opp, Digit.neq_sym; assumption.

      pose proof (Hy (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hxy.
      pose proof (Hx (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rename H into Hyx.
      rewrite <- Hxy, <- Hyx in Hne.
      symmetry.
      apply Digit.neq_eq_opp; assumption.

     rewrite Digit.add_1_r; f_equal.
     apply Digit.opp_compat.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      apply Heq; assumption.

      subst j.
      pose proof (Hs1 0) as H.
      rewrite <- Nat.add_succ_r, Hx in H.
      rewrite H in Hne; clear H.
      pose proof (Hs2 0) as H.
      rewrite <- Nat.add_succ_r, Hy in H.
      rewrite H in Hne; clear H.
      exfalso; apply Hne; reflexivity.

      pose proof (Hx (j - i)) as H.
      rewrite Nat.add_succ_r in H.
      generalize H1; intros HH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      rewrite Nat.add_comm, Nat.add_sub in H.
      replace j with (j + 0) in H by apply Nat.add_0_r.
      rewrite Hs1 in H.
      rewrite <- H in Hne; clear H.
      pose proof (Hy (j - i)) as H.
      rewrite Nat.add_succ_r in H.
      generalize H1; intros HH.
      apply Nat.lt_le_incl in HH.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      clear HH.
      rewrite Nat.add_comm, Nat.add_sub in H.
      replace j with (j + 0) in H by apply Nat.add_0_r.
      rewrite Hs2 in H.
      symmetry in H; contradiction.
Qed.

(* multiplication *)

Definition seq_sum_frac_lt_1 (u : nat → nat) i n :=
  let nt := Σ (k = 1, n), u (i + k) * int_pow radix (n - k) in
  let dt := int_pow radix n in
  let ub_sum_frac :=
    let ft := nt - (nt / dt) * dt in
    ft + (i + n + 1) * (radix - 1) + 1
  in
  if lt_dec ub_sum_frac dt then 1 else 0.

Definition carry_mul u i :=
  match first_nonzero (seq_sum_frac_lt_1 u i) with
  | Some n =>
      let nt := Σ (k = 1, n), u (i + k) * int_pow radix (n - k) in
      let dt := int_pow radix n in
      nt / dt
  | None =>
      let n := logn radix (i * (radix - 1) + radix) + 2 in
      let nt := Σ (k = 1, n), u (i + k) * int_pow radix (n - k) in
      let dt := int_pow radix n in
      S (nt / dt)
  end.

Definition NN2I_mul u := {| rm i := n2d (u i + carry_mul u i) |}.
Arguments NN2I_mul u%NN.

Definition I_mul x y := NN2I_mul (NN_mul (I2NN x) (I2NN y)).
Arguments I_mul x%I y%I.

Notation "x * y" := (I_mul x y) : I_scope.

(* *)

Theorem NN2I_add_compat : ∀ u v,
  (u = v)%NN
  → (NN2I_add u == NN2I_add v)%I.
Proof.
intros u v Huv i; simpl.
unfold digit_eq; simpl; f_equal; f_equal; [ apply Huv | idtac ].
apply carry_add_compat; assumption.
Qed.

Add Parametric Morphism : NN2I_add
 with signature NN_eq ==> I_eqs
 as NN2I_add_morph.
Proof. intros; apply NN2I_add_compat; assumption. Qed.

(* commutativity *)

Theorem I_add2_comm : ∀ x y, (x + y == y + x)%I.
Proof.
intros x y.
unfold I_eqs, I_add2; intros i.
rewrite NN_add_comm; reflexivity.
Qed.

(* 0 neutral element *)

Theorem radix_le_sqr_radix : radix ≤ radix * radix.
Proof.
remember (radix * radix) as a.
replace radix with (1 * radix) by apply Nat.mul_1_l; subst a.
apply Nat.mul_le_mono_r, Digit.radix_gt_0.
Qed.

Definition add_NN_add_l u v i a := NN_add u v i + a.

Theorem fold_add_NN_add_l : ∀ u v i a,
  NN_add u v i + a = add_NN_add_l u v i a.
Proof. intros; reflexivity. Qed.

Add Parametric Morphism : add_NN_add_l
 with signature NN_eq ==> NN_eq ==> eq ==> eq ==> eq
 as add_NN_add_l_morph.
Proof.
intros u v Huv w x Hwx i a.
unfold add_NN_add_l, NN_add; simpl.
rewrite Huv, Hwx; reflexivity.
Qed.

Theorem NN2I_add_0_r : ∀ u, (NN2I_add (u + 0%NN) == NN2I_add u)%I.
Proof.
intros u i; simpl.
unfold digit_eq; simpl.
f_equal; f_equal; [ apply NN_add_0_r | idtac ].
rewrite carry_add_add_0_r.
reflexivity.
Qed.

Definition toto u v := carry_add (u + v).
Theorem fold_toto : ∀ u v, carry_add (u + v) = toto u v.
Proof. intros; reflexivity. Qed.

Theorem toto_compat : ∀ u v w x i,
  (u = v)%NN
  → (w = x)%NN
  → toto u w i = toto v x i.
Proof.
intros u v w x i Huv Hwx; unfold toto.
unfold carry_add; simpl.
erewrite fst_neq_pred_r_compat.
2: erewrite NN_add_compat; [ reflexivity | eassumption | eassumption ].
remember (fst_neq_pred_r (v + x) (S i)) as s1 eqn:Hs1.
apply first_nonzero_iff in Hs1; simpl in Hs1.
unfold seq_pred_r in Hs1; simpl in Hs1.
destruct s1 as [n1| ]; [ idtac | reflexivity ].
unfold NN_add.
rewrite Huv, Hwx; reflexivity.
Qed.

Add Parametric Morphism : toto
 with signature NN_eq ==> NN_eq ==> eq ==> eq
 as toto_morph.
Proof.
intros u v Huv w x Hwx i.
apply toto_compat; assumption.
Qed.

Theorem NN2I_add_I2NN : ∀ x, (NN2I_add (I2NN x) = x)%I.
Proof.
intros u.
bbb.

unfold I_eq, I_norm; simpl.
unfold I_add2; simpl.
rewrite I_zero_NN_zero.
do 2 rewrite NN2I_add_0_r.
intros i; simpl.
unfold digit_eq; simpl.
SearchAbout NN2I_add.
unfold I2NN; simpl.
rewrite d2n_n2d.
bbb.

SearchAbout I2NN.

unfold NN2I_add, I2NN; simpl.
bbb.

Theorem I2NN_NN2I_add : ∀ u, (NN2I_add (I2NN (NN2I_add u)) = NN2I_add u)%I.
(*
Proof. intros; apply NN2I_I2NN. Qed.
*)
Proof.
intros u i; simpl.
unfold digit_eq, n2d; simpl.
do 2 rewrite NN_add_add_0_r.
do 2 rewrite fold_toto.
rewrite I_zero_NN_zero.
unfold toto; simpl.
erewrite carry_add_compat; [ idtac | apply NN_add_0_r ].

rewrite zzz.
bbb.

unfold carry_add at 1; simpl.
remember (fst_neq_pred_r (I2NN (NN2I_add u)) (S i)) as s1 eqn:Hs1.
apply first_nonzero_iff in Hs1; simpl in Hs1.
destruct s1 as [n1| ].
 destruct (lt_dec (I2NN (NN2I_add u) (S (i + n1))) (pred radix)) as [H1| H1].
  rewrite Nat.add_0_r.
  unfold I2NN, NN2I_add; simpl.
  rewrite d2n_n2d, Nat.mod_mod; [ reflexivity | apply Digit.radix_neq_0 ].

  apply Nat.nlt_ge in H1.
  destruct Hs1 as (Hn1, Ht1).
  destruct n1.
   unfold seq_pred_r in Ht1.
   rewrite Nat.add_0_r in Ht1, H1.
   destruct (eq_nat_dec (I2NN (NN2I_add u) (S i)) (pred radix)) as [H2| H2].
    exfalso; apply Ht1; reflexivity.

    clear Ht1.
Print NN2I_add.
unfold I2NN, NN2I_add; simpl.
rewrite d2n_n2d.
bbb.

unfold I2NN, NN2I_add; simpl.
rewrite d2n_n2d.
unfold fst_neq_pred_r; simpl.
bbb.

Theorem NN2I_add_I2NN : ∀ x, (NN2I_add (I2NN x) == x)%I.
Proof.
intros x i; simpl.
unfold I2NN; simpl.
unfold digit_eq; simpl.
(*
rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
*)
rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
rewrite Nat.sub_0_r, Nat.add_0_r; fsimpl.
rewrite Nat.div_add_l; [ idtac | apply int_pow_neq_0, Digit.radix_neq_0 ].
rewrite Nat.div_small.
 rewrite Nat.add_0_r; unfold d2n.
 rewrite Nat.mod_mod; [ reflexivity | apply Digit.radix_neq_0 ].

 revert i.
 induction n; intros j; [ unfold summation; apply Nat.lt_0_1 | fsimpl ].
 rewrite summation_split_first; [ idtac | apply le_n_S, Nat.le_0_l ].
 rewrite Nat.sub_succ, Nat.sub_0_r.
 erewrite summation_shift; try (apply le_n_S, Nat.le_0_l).
 do 2 (rewrite Nat.sub_succ, Nat.sub_0_r).
 erewrite summation_compat.
  Focus 2.
  intros k (Hk, Hkn).
  rewrite Nat.add_assoc, Nat.add_shuffle0, Nat.add_1_r.
  rewrite Nat.add_1_r, Nat.sub_succ; reflexivity.

  remember (S j) as sj; simpl; subst sj.
  eapply lt_le_trans; [ apply Nat.add_lt_mono_l, IHn | idtac ].
  remember (int_pow radix n) as rn eqn:Hrn.
  remember (d2n (x .[ j + 1]) * rn) as a.
  remember (radix * rn) as b.
  replace rn with (1 * rn) by apply Nat.mul_1_l; subst a b rn.
  rewrite <- Nat.mul_add_distr_r.
  apply Nat.mul_le_mono; [ idtac | reflexivity ].
  rewrite Nat.add_comm.
  apply d2n_lt_radix.
Qed.

Theorem I_add2_0_r : ∀ x, (x + 0 = x)%I.
Proof.
intros x.
unfold I_add2; intros i; simpl.
do 2 rewrite fold_add_NN_add_l, fold_toto.
rewrite I_zero_NN_zero.
unfold add_NN_add_l, toto; simpl.
do 2 rewrite NN_add_0_r.
rewrite fold_toto.
erewrite toto_compat.
2: rewrite NN2I_add_0_r; reflexivity.
2: reflexivity.
unfold toto; simpl.
bbb.
SearchAbout NN2I_add.
  ============================
   (n2d
      (I2NN (NN2I_add (I2NN x + 0%NN)) i +
       carry_add (I2NN (NN2I_add (I2NN x + 0%NN)) + 0%NN) i) =
    n2d (I2NN x i + carry_add (I2NN x + 0%NN) i))%D
  ============================
   (n2d
      (I2NN (NN2I_add (I2NN x + 0%NN)) i +
       carry_add (I2NN (NN2I_add (I2NN x)) + 0%NN) i) =
    n2d (I2NN x i + carry_add (I2NN x + 0%NN) i))%D

bbb.

bbb.
unfold digit_eq, NN2I_add, carry_add; simpl.
remember (fst_neq_pred_r (I2NN x) (S i)) as s1 eqn:Hs1.
apply first_nonzero_iff in Hs1.
destruct s1 as [n | ].
 unfold seq_pred_r in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Ht1).
 destruct (lt_dec (I2NN x (S (i + n))) (pred radix)) as [H1| H1].
  rewrite Nat.add_0_r; unfold I2NN, d2n.
  rewrite Nat.mod_mod; [ reflexivity | apply Digit.radix_neq_0 ].

  apply Nat.nlt_ge in H1.
  destruct (eq_nat_dec (I2NN x (S (i + n))) (pred radix)) as [H2| H2].
   exfalso; apply Ht1; reflexivity.

   clear Ht1.
   unfold I2NN, d2n.
bbb.
   destruct n.
    clear Hn1.
    Focus 2.
    assert (n < S n) as H by apply Nat.lt_succ_diag_r.
    apply Hn1 in H.
    destruct (eq_nat_dec (I2NN x (S (i + n))) (pred radix)) as [H3| H3].
     unfold I2NN, d2n in H3.
bbb.

unfold summation.
remember modulo as fmod; remember div as fdiv; simpl; subst fmod fdiv.
do 2 rewrite Nat.add_0_r, Nat.mul_1_r; fsimpl.
(*
rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
*)
rewrite Nat.div_add_l; [ idtac | apply sqr_radix_neq_0 ].
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
  apply Nat.lt_pred_l, sqr_radix_neq_0.
Qed.

(* compatibility with == *)

Theorem I_add2_compat_r : ∀ x y z, (x == y)%I → (x + z == y + z)%I.
Proof.
intros x y z Hxy i.
unfold I_add2.
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

(* *)

Theorem int_pow_neq_0 : ∀ a b, a ≠ 0 → int_pow a b ≠ 0.
Proof.
intros a b Ha.
induction b; [ intros H; discriminate H | simpl ].
apply Nat.neq_mul_0; split; assumption.
Qed.

Theorem fold_I_add2 : ∀ x y, NN2I 2 (I2NN x + I2NN y) = I_add2 x y.
Proof. reflexivity. Qed.

Theorem Nat_add_shuffle3 : ∀ a b c d,
  a + b + c + d = a + c + (b + d).
Proof. intros; omega. Qed.

Theorem Nat_div_add_sqr : ∀ a b c, a < c → (a + b * c) / (c * c) = b / c.
Proof.
intros a b c Hac.
destruct c; [ exfalso; revert Hac; apply Nat.nlt_0_r | idtac ].
remember (S c) as c'.
assert (c' > 0) as Hcp by (subst c'; apply Nat.lt_0_succ).
assert (c' ≠ 0) as Hc by (subst c'; intros H; discriminate H).
clear c Heqc'; rename c' into c.
pose proof (Nat.div_mod b c Hc) as H.
rewrite Nat.add_comm in H.
remember (b * c) as d; rewrite H in Heqd; subst d.
rewrite Nat.mul_add_distr_r, Nat.mul_shuffle0.
remember (b mod c * c) as d.
rewrite Nat.add_assoc, Nat.mul_comm; subst d.
rewrite Nat.div_add.
 rewrite Nat.div_small; [ reflexivity | idtac ].
 apply Nat.le_lt_trans with (m := c - 1 + (c - 1) * c).
  apply Nat.lt_le_pred in Hac; rewrite <- Nat.sub_1_r in Hac.
  apply Nat.add_le_mono; [ assumption | idtac ].
  apply Nat.mul_le_mono_pos_r; [ assumption | idtac ].
  rewrite Nat.sub_1_r; apply Nat.lt_le_pred.
  apply Nat.mod_upper_bound; assumption.

  rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
  rewrite Nat.add_sub_assoc.
   rewrite Nat.add_comm.
   rewrite Nat.add_sub_assoc; [ idtac | assumption ].
   rewrite Nat_sub_shuffle0, Nat.add_sub.
   rewrite Nat.sub_1_r.
   apply Nat.lt_pred_l.
   apply Nat.neq_mul_0; split; assumption.

   remember (c * c) as cc.
   replace c with (1 * c) by apply Nat.mul_1_l; subst cc.
   apply Nat.mul_le_mono_pos_r; assumption.

 apply Nat.neq_mul_0; split; assumption.
Qed.

Theorem NN2I_add2_inj : ∀ u v,
  (∀ i, u i < radix ∧ v i < radix)
  → (NN2I 2 (u + v) == NN2I 2 u + NN2I 2 v)%I.
Proof.
intros u v Huv i.
bbb.
This theorem without Hu is false.
Counter-example (g=NN2I 2)
           u 0.0210
           v 0.0102
      g(u+v) 0.1000
   g(u)+g(v) 0.0000

However u+v = 0.0312 = 3/4 + 1/8 + 2/16 = 16/16 = 1, i.e. 0 in I.
Likely not enough iterations (2 in NN2I 2).

Faut-il ajouter comme conditions que u et v sont des représentations
en nombres à nombres de nombres à chiffres normaux ? c'est-à-dire
   ∀ i, u i < r et v i < r
*)
unfold I_add2, NN_add.
unfold I2NN, NN2I; fsimpl.
unfold summation; simpl.
do 6 rewrite d2n_n2d.
do 9 rewrite Nat.mul_1_r.
do 12 rewrite Nat.add_0_r.
do 4 rewrite <- Nat.add_assoc; simpl.
do 10 rewrite Nat.add_assoc.
remember (radix * radix) as rr eqn:Hrr .
remember radix as r eqn:Hr .
remember (v (i + 4)) as v4 eqn:Hv4 .
remember (v (i + 3)) as v3 eqn:Hv3 .
remember (v (i + 2)) as v2 eqn:Hv2 .
remember (v (i + 1)) as v1 eqn:Hv1 .
remember (u (i + 4)) as u4 eqn:Hu4 .
remember (u (i + 3)) as u3 eqn:Hu3 .
remember (u (i + 2)) as u2 eqn:Hu2 .
remember (u (i + 1)) as u1 eqn:Hu1 .
do 10 rewrite <- Nat.add_assoc.
do 8 (rewrite Nat.div_add_l; [ idtac | subst r rr; apply sqr_radix_neq_0 ]).
do 2 rewrite Nat.add_assoc.
unfold digit_eq, n2d; rewrite <- Hr; simpl.
pose proof Digit.radix_neq_0 as Hr0; rewrite <- Hr in Hr0.
pose proof Digit.radix_gt_0 as Hrp; rewrite <- Hr in Hrp.
assert (rr ≠ 0) as Hrr0 by (subst rr; apply Nat.neq_mul_0; split; assumption).
symmetry; rewrite <- Nat.add_assoc.
rewrite Nat.add_mod_idemp_l; [ idtac | assumption ].
do 4 rewrite <- Nat.add_assoc.
rewrite Nat.add_mod; [ symmetry | assumption ].
rewrite Nat.add_mod; [ symmetry | assumption ].
f_equal; f_equal.
rewrite Nat.add_comm.
rewrite <- Nat.add_assoc.
rewrite Nat.add_mod_idemp_l; [ idtac | assumption ].
rewrite <- Nat.add_assoc.
rewrite Nat.add_mod; [ symmetry | assumption ].
rewrite Nat.add_mod; [ symmetry | assumption ].
f_equal; f_equal.
rewrite Nat.add_comm.
do 2 rewrite Nat.add_assoc; symmetry.
destruct (lt_dec (u3 * r + u4) rr) as [H1| H1].
 remember ((u3 * r + u4) / rr) as a eqn:Ha .
 rewrite Nat.div_small in Ha; [ subst a | assumption ].
 rewrite Nat.add_0_r.
 destruct (lt_dec (v3 * r + v4) rr) as [H2| H2].
  remember ((v3 * r + v4) / rr) as a eqn:Ha .
  rewrite Nat.div_small in Ha; [ subst a | assumption ].
  rewrite Nat.add_0_r.
  destruct (lt_dec (u2 * r + u3) rr) as [H3| H3].
   generalize H3; intros H.
   rewrite Hrr in H.
   eapply lt_le_trans in H; [ idtac | apply le_n_S, Nat.le_add_r ].
   apply Nat.mul_lt_mono_pos_r in H; [ idtac | assumption ].
   rename H into Hu2r.
   remember (u2 mod r) as a eqn:Ha .
   rewrite Nat.mod_small in Ha; [ subst a | assumption ].
   remember ((u2 * r + u3) / rr) as a eqn:Ha .
   rewrite Nat.div_small in Ha; [ subst a | assumption ].
   rewrite Nat.add_0_r.
   remember (u1 * r + u2) as u12 eqn:Hu12 .
   remember (v1 * r + v2) as v12 eqn:Hv12 .
   pose proof (Nat_div_add_sqr u2 u1 r Hu2r) as Hu12rr.
   rewrite Nat.add_comm, <- Hrr, <- Hu12 in Hu12rr.
   destruct (lt_dec (v2 * r + v3) rr) as [H4| H4].
    generalize H4; intros H.
    rewrite Hrr in H.
    eapply lt_le_trans in H; [ idtac | apply le_n_S, Nat.le_add_r ].
    apply Nat.mul_lt_mono_pos_r in H; [ idtac | assumption ].
    rename H into Hv2r.
    remember (v2 mod r) as a eqn:Ha .
    rewrite Nat.mod_small in Ha; [ subst a | assumption ].
    remember ((v2 * r + v3) / rr) as a eqn:Ha .
    rewrite Nat.div_small in Ha; [ subst a | assumption ].
    rewrite Nat.add_0_r.
    do 2 rewrite Nat.mul_add_distr_r.
    do 2 rewrite Nat_add_shuffle3.
    pose proof (Nat_div_add_sqr v2 v1 r Hv2r) as Hv12rr.
    rewrite Nat.add_comm, <- Hrr, <- Hv12 in Hv12rr.
    rewrite Hv12rr, <- Hu12, <- Hv12.
    destruct (lt_dec (u12 + v12) rr) as [H5| H5].
     remember ((u12 + v12) / rr) as a eqn:Ha .
     rewrite Nat.div_small in Ha; [ subst a | assumption ].
     rewrite Nat.mod_0_l; [ idtac | assumption ].
     generalize H5; intros H.
     eapply lt_le_trans in H; [ idtac | apply le_n_S, Nat.le_add_r ].
     rename H into H6.
     remember (u12 / rr) as a eqn:Ha .
     rewrite Nat.div_small in Ha; [ subst a | assumption ].
     rewrite Nat.add_0_r.
     generalize H5; intros H; rewrite Nat.add_comm in H.
     eapply lt_le_trans in H; [ idtac | apply le_n_S, Nat.le_add_r ].
     rename H into H7.
     rewrite Nat.div_small in Hv12rr; [ rewrite <- Hv12rr | assumption ].
     rewrite Nat.add_0_r.
     rewrite Nat.div_small.
      rewrite Nat.mod_0_l; [ reflexivity | assumption ].

      rewrite <- Nat.add_assoc.
      eapply le_lt_trans.
       apply -> Nat.add_le_mono_r.
       apply Nat.mul_le_mono_r; subst r.
       apply Nat.mod_le; assumption.

       rewrite Nat.add_comm, <- Nat.add_assoc.
       rewrite Nat.add_comm.
       do 2 rewrite <- Nat.add_assoc.
       eapply le_lt_trans.
        apply -> Nat.add_le_mono_r.
        apply Nat.mul_le_mono_r; subst r.
        apply Nat.mod_le; assumption.

        rewrite Nat.add_comm, <- Nat.add_assoc.
        rewrite Nat.add_comm, <- Nat.add_assoc, <- Hu12, <- Hv12.
        assumption.

     pose proof (Nat.div_mod v1 r Hr0) as Hv1m.
     rewrite Nat.add_comm in Hv1m.
     rewrite Hv1m in Hv12.
     rewrite Hv12, <- Nat.add_assoc.
     rewrite Nat.mul_add_distr_r, Nat.add_shuffle0.
     remember (v1 mod r * r) as a.
     rewrite Nat.mul_shuffle0, Nat.mul_comm, <- Hrr; subst a.
     rewrite Nat.add_assoc, Hrr, Hr.
     rewrite Nat.div_add; [ rewrite <- Hr, <- Hrr | apply sqr_radix_neq_0 ].
     apply Nat.nlt_ge in H5.
     symmetry; rewrite Nat.add_shuffle0.
     rewrite Nat.add_shuffle0; symmetry.
     do 3 rewrite Nat.add_assoc.
     rewrite Nat.add_mod; [ symmetry | assumption ].
     rewrite Nat.add_mod; [ symmetry | assumption ].
     f_equal; f_equal.
     destruct (lt_dec u12 rr) as [H6| H6].
      remember (u12 / rr) as a eqn:Ha .
      rewrite Nat.div_small in Ha; [ subst a | assumption ].
      rewrite Nat.add_0_r.
      destruct (lt_dec v12 rr) as [H7| H7].
       generalize H6; intros H.
       rewrite Hu12, Hrr in H.
       eapply le_lt_trans in H; [ idtac | apply Nat.le_add_r ].
       apply Nat.mul_lt_mono_pos_r in H; [ idtac | assumption ].
       rename H into Hu1r.
       remember (u1 mod r) as a eqn:Ha .
       rewrite Nat.mod_small in Ha; [ subst a | assumption ].
       rewrite Hu12; reflexivity.

       apply Nat.nlt_ge in H7.
       assert (u1 < r) as Hu1r.
        apply Nat.mul_lt_mono_pos_r with (p := r); [ assumption | idtac ].
        apply Nat.add_lt_mono_r with (p := u2); rewrite <- Hu12, <- Hrr.
        eapply Nat.lt_le_trans; [ eassumption | apply Nat.le_add_r ].

        remember (u1 mod r) as a eqn:Ha .
        rewrite Nat.mod_small in Ha; [ subst a | assumption ].
        rewrite <- Hu12; reflexivity.

      rewrite Nat.nlt_ge in H6.
      destruct (lt_dec u1 r) as [H7| H7].
       exfalso.
       rewrite Hu12 in H6.
       apply Nat.nlt_ge in H6; apply H6; clear H6.
       apply Nat.le_lt_trans with (m := (r - 1) * r + (r - 1)).
        apply Nat.lt_le_pred in Hu2r; rewrite <- Nat.sub_1_r in Hu2r.
        apply Nat.add_le_mono; [ idtac | assumption ].
        apply Nat.mul_le_mono_pos_r; [ assumption | idtac ].
        rewrite Nat.sub_1_r; apply Nat.lt_le_pred; assumption.

        rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
        rewrite Nat.add_sub_assoc; [ idtac | assumption ].
        rewrite Nat.sub_1_r, Hrr, Hr.
        pose proof sqr_radix_neq_0 as H8.
        rewrite Nat.sub_add; [ apply Nat.lt_pred_l; assumption | idtac ].
        rewrite <- Hr, <- Hrr.
        replace r with (1 * r) by apply Nat.mul_1_l; rewrite Hrr.
        apply Nat.mul_le_mono_pos_r; assumption.

       apply Nat.nlt_ge in H7.
       rewrite Hu12rr, Hu12.
       pose proof (Nat.div_mod u1 r Hr0) as Hu1m.
       remember (u1 * r) as a eqn:Ha in |-*.
       rewrite Hu1m, Nat.add_comm, Nat.mul_add_distr_r in Ha.
       rewrite Nat.mul_shuffle0, <- Hrr in Ha; subst a.
       do 5 rewrite <- Nat.add_assoc; rewrite Nat.add_comm.
       do 3 rewrite <- Nat.add_assoc; rewrite Nat.add_comm.
       do 4 rewrite Nat.add_assoc; rewrite Nat.add_shuffle0, Nat.add_comm.
       do 3 rewrite Nat.add_assoc.
       remember (rr * (u1 / r)) as a eqn:Ha.
       rewrite Nat.mul_comm in Ha; subst a.
       rewrite Nat.div_add; [ reflexivity | assumption ].

    apply Nat.nlt_ge in H4.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat_add_shuffle3, <- Hu12, <- Hv12.
    destruct (lt_dec (u12 + v12) rr) as [H5| H5].
     remember ((u12 + v12) / rr) as a eqn:Ha .
     rewrite Nat.div_small in Ha; [ subst a | assumption ].
     rewrite Nat.mod_0_l; [ idtac | assumption ].
     generalize H5; intros H.
     eapply lt_le_trans in H; [ idtac | apply le_n_S, Nat.le_add_r ].
     rename H into H6.
     remember (u12 / rr) as a eqn:Ha .
     rewrite Nat.div_small in Ha; [ subst a | assumption ].
     rewrite Nat.add_0_r.
     generalize H5; intros H; rewrite Nat.add_comm in H.
     eapply lt_le_trans in H; [ idtac | apply le_n_S, Nat.le_add_r ].
     remember (v12 / rr) as a eqn:Ha.
     rewrite Nat.div_small in Ha; [ subst a | assumption ].
     rewrite Nat.add_0_r.
     rename H into H7.
     symmetry in Hu12rr.
     generalize Hu12rr; intros H.
     apply Nat.div_small_iff in H; [ idtac | assumption ].
     rename H into Hu1r.
     remember (u1 mod r) as a eqn:Ha.
     rewrite Nat.mod_small in Ha; [ subst a | assumption ].
     rewrite Nat.mul_add_distr_r, Nat_add_shuffle3, <- Hu12.
     rewrite Nat.add_assoc.
     remember (v1 + (v2 * r + v3) / rr) as a eqn:Ha.
     rewrite Nat.add_comm in Ha.
     rewrite <- Nat.div_add in Ha; [ idtac | assumption ].
     rewrite Nat.add_comm, Nat.add_assoc in Ha.
     rewrite Hrr, Nat.mul_assoc, <- Nat.mul_add_distr_r in Ha.
     rewrite <- Hv12, <- Hrr in Ha; subst a.
     assert (v3 < r) as Hv3r.
      apply Nat.mul_lt_mono_pos_r with (p := r); [ assumption | idtac ].
      rewrite <- Hrr.
      eapply Nat.le_lt_trans; [ apply Nat.le_add_r | apply H2 ].

      assert (v2 ≥ r) as Hv2r.
       apply Nat.nlt_ge; intros H.
       apply Nat.lt_le_pred in H; rewrite <- Nat.sub_1_r in H.
       apply Nat.mul_le_mono_pos_r with (p := r) in H; [ idtac | assumption ].
       apply Nat.add_le_mono_r with (p := v3) in H.
       eapply Nat.le_trans in H; [ idtac | eassumption ].
       rewrite Nat.mul_sub_distr_r, Nat.mul_1_l, <- Hrr in H.
       apply Nat.add_le_mono_l with (p := r) in H.
       rewrite Nat.add_assoc in H.
       rewrite Nat.add_sub_assoc in H.
        rewrite Nat.add_comm, Nat.add_sub in H.
        apply Nat.add_le_mono_l, Nat.nlt_ge in H; contradiction.

        replace r with (1 * r) by apply Nat.mul_1_l; rewrite Hrr.
        apply Nat.mul_le_mono_pos_r; assumption.
        assert (v1 < r) as Hv1r.
         apply Nat.mul_lt_mono_pos_r with (p := r); [ assumption | idtac ].
         rewrite Hv12 in H7; rewrite <- Hrr.
         eapply Nat.le_lt_trans; [ apply Nat.le_add_r | apply H7 ].

         subst u12 v12.
         rewrite Nat.mul_add_distr_r, <- Nat.mul_assoc, <- Hrr.
         destruct (eq_nat_dec v1 (r - 1)) as [H8| H8].
          rewrite H8, Nat.mul_sub_distr_r, Nat.mul_1_l, <- Hrr in H7.
          rewrite <- Nat.add_sub_swap in H7.
           apply Nat.lt_sub_lt_add_l in H7.
           rewrite Nat.add_comm, <- Nat.add_lt_mono_r in H7.
           apply Nat.nle_gt in H7; contradiction.

           replace r with (1 * r) by apply Nat.mul_1_l; rewrite Hrr.
           apply Nat.mul_le_mono_pos_r; assumption.
bbb.
  H5 : u12 + v12 < rr
  Hv2r : v2 ≥ r
  H4 : rr ≤ v2 * r + v3
  Hv3r : v3 < r

rr ≤ (v2 + 1) r - 1

u12 + v1 r + v2 ≤ rr - 1 ≤ (v2 + 1) r - 2

u12 + v1 r + v2 + 2 ≤ v2 r + r

(v2 + 1) (r - 1) ≥ u1 r + u2 + v1 r + 1

     remember v1 as a eqn:Ha in |-*.
     rewrite <- Nat.div_mul with (b := rr) in Ha; subst a.
bbb.
   0 = ((u12 + ((v1 + (v2 * r + v3) / rr) mod r * r + v2 mod r)) / rr) mod r

Set Printing Depth 14. Show.
Unset Printing Notations. Show.

bbb.
*)

(*
Theorem zzz : ∀ n u v, n = 2 →
  (NN2I n (u + I2NN (NN2I n v)) == NN2I n (u + v))%I.
Proof.
intros n u v Hn.
symmetry; rewrite <- I2NN_NN2I; symmetry.
subst n.
Print fold_I_add2.
Check I_add2_compat.
Unset Printing Notations. Show.
rewrite fold_I_add2.
bbb.
  ============================
   I_eqs (NN2I u (NN_add v (I2NN (NN2I u n))))
     (NN2I u (I2NN (NN2I u (NN_add v n))))
fold_I_add2 =
fun x y : I => eq_refl
     : forall x y : I,
       eq (NN2I (S (S O)) (NN_add (I2NN x) (I2NN y))) (I_add2 x y)


I2NN (NN2I 2 (u + v)) = u + v

rewrite fold_I_add2.

Check I_add2_compat.
bbb.
(*
symmetry.
apply NN2I_compat.
*)
unfold NN_eq; intros i; simpl.
NN_eq.

bbb.
  ============================
   I_eqs (NN2I n (NN_add u (I2NN (NN2I n v)))) (NN2I n (NN_add u v))

NN_add ok
NN2I ok

rewrite NN2I_compat.
apply NN_add_compat; [ reflexivity | idtac ].
SearchAbout I2NN.
(*
pose proof I2NN_NN2I v n as Hv.
Check NN2I_morph.
Check NN2I_compat.
*)
bbb.
*)

(*
Theorem NN2I_lim : ∀ u,
  (∀ j, u j ≤ 2 * pred radix)
  → ∀ n, n ≥ 2
  → (NN2I n u == NN2I 2 u)%I.
Proof.
intros u Hu n Hn i.
unfold NN2I; fsimpl.
rewrite Nat.mul_1_r.
unfold digit_eq; fsimpl.
do 2 (rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ]).
apply Nat.nlt_ge in Hn.
destruct n; [ exfalso; apply Hn, Nat.lt_0_succ | idtac ].
rewrite summation_split_last; [ symmetry | apply Nat.le_0_l ].
rewrite summation_split_last; [ symmetry | apply Nat.le_0_l ].
do 2 rewrite Nat.sub_diag; fsimpl.
do 2 rewrite Nat.mul_1_r.
Print NN2I.
bbb.

, Nat.sub_succ, Nat.sub_0_r; fsimpl.
rewrite Nat.mul_1_r.

do 2 rewrite Nat.sub_0_r; rewrite Nat.add_0_r.
SearchAbout ((_ + _)/_).
bbb.

rewrite <- Nat.add_mod_idemp_r.
Unset Printing Notations. Show.
Set Printing Depth 14. Show.
*)

(* associativity *)

(*
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

(* is it true? *)
(* no
Theorem yyy : ∀ u v,
  (∀ j, u j ≤ 2 * pred radix)
  → (∀ j, v j ≤ 2 * pred radix)
  → (NN2I 2 (u + I2NN (NN2I 2 v)) == NN2I 2 (u + v))%I.
Proof.
intros u v Hu Hv i.
unfold NN2I, I2NN, NN_add; fsimpl.
unfold digit_eq; fsimpl.
rewrite Nat.mul_1_r.
unfold summation; simpl.
do 9 rewrite Nat.add_0_r.
do 6 rewrite Nat.mul_1_r.
do 4 rewrite <- Nat.add_assoc; simpl.
do 7 rewrite Nat.add_assoc.
do 3 rewrite d2n_n2d.
do 5 (rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ]).
Set Printing Depth 13. Show.
do 7 rewrite <- Nat.add_assoc.
do 5 (rewrite Nat.div_add_l; [ idtac | apply sqr_radix_neq_0 ]).
Set Printing Depth 10. Show.
do 2 rewrite <- Nat.add_assoc.
do 2 (rewrite Nat.add_comm; symmetry).
rewrite <- Nat.add_mod_idemp_l; [ symmetry | apply Digit.radix_neq_0 ].
rewrite <- Nat.add_mod_idemp_l; [ symmetry | apply Digit.radix_neq_0 ].
f_equal; f_equal.
Set Printing Depth 12. Show.
rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
rewrite Nat.add_comm; symmetry.
rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
Set Printing Depth 18. Show.
rewrite Nat.add_mod_idemp_l; [ idtac | apply Digit.radix_neq_0 ].
rewrite <- Nat.add_assoc, Nat.add_comm; symmetry.
rewrite <- Nat.add_mod_idemp_l; [ symmetry | apply Digit.radix_neq_0 ].
rewrite <- Nat.add_mod_idemp_l; [ symmetry | apply Digit.radix_neq_0 ].
f_equal; f_equal.
Set Printing Depth 9. Show.
rewrite Nat.add_mod_idemp_r; [ idtac | apply Digit.radix_neq_0 ].
do 2 rewrite Nat.add_assoc.
Set Printing Depth 11. Show.
remember radix as r.
remember (r * r) as rr.
Set Printing Depth 14. Show.
do 2 rewrite Nat.mul_add_distr_r.
Set Printing Depth 25. Show.
remember (u (i + 1)) as u1 eqn:Hu1.
remember (u (i + 2)) as u2 eqn:Hu2.
remember (u (i + 3)) as u3 eqn:Hu3.
remember (u (i + 4)) as u4 eqn:Hu4.
remember (v (i + 1)) as v1 eqn:Hv1.
remember (v (i + 2)) as v2 eqn:Hv2.
remember (v (i + 3)) as v3 eqn:Hv3.
remember (v (i + 4)) as v4 eqn:Hv4.
bbb.

Set Printing Depth 12. Show.
Set Printing Depth 14. Show.
bbb.

bbb.

remember radix as r.
remember (r * r) as rr.
Set Printing Depth 11. Show.
do 2 (rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ]).

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
 rewrite Nat.div_add; [ idtac | apply sqr_radix_neq_0 ].
 rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
 subst k; reflexivity.

 do 2 (rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ]).
 erewrite summation_compat.
  2: intros; rewrite Nat.add_0_r; reflexivity.

  fsimpl.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite Nat.sub_0_r; fsimpl.
  rewrite Nat.mul_1_r, Nat.add_0_r.
  rewrite Nat.div_add_l; [ idtac | apply sqr_radix_neq_0 ].
  symmetry.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite Nat.sub_0_r; fsimpl.
  rewrite Nat.mul_1_r, Nat.add_0_r.
  rewrite <- Nat.add_assoc; fsimpl.
  rewrite Nat.add_assoc.
  rewrite Nat.div_add_l; [ idtac | apply sqr_radix_neq_0 ].
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
bbb.
*)

(* is it true? *)
(* no
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
 rewrite Nat.div_add; [ idtac | apply sqr_radix_neq_0 ].
 rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ].
 subst k; reflexivity.

 do 2 (rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ]).
 erewrite summation_compat.
  2: intros; rewrite Nat.add_0_r; reflexivity.

  fsimpl.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite Nat.sub_0_r; fsimpl.
  rewrite Nat.mul_1_r, Nat.add_0_r.
  rewrite Nat.div_add_l; [ idtac | apply sqr_radix_neq_0 ].
  symmetry.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite Nat.sub_0_r; fsimpl.
  rewrite Nat.mul_1_r, Nat.add_0_r.
  rewrite <- Nat.add_assoc; fsimpl.
  rewrite Nat.add_assoc.
  rewrite Nat.div_add_l; [ idtac | apply sqr_radix_neq_0 ].
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
*)

(*
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
 rewrite Nat.div_add; [ idtac | apply sqr_radix_neq_0 ].
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
  rewrite Nat.div_add_l; [ idtac | apply sqr_radix_neq_0 ].
  symmetry.
  rewrite summation_split_first; [ idtac | apply Nat.le_0_l ].
  rewrite Nat.sub_0_r; fsimpl.
  rewrite Nat.mul_1_r, Nat.add_0_r.
  do 2 rewrite <- Nat.add_assoc; fsimpl.
  do 3 rewrite Nat.add_assoc.
  rewrite Nat.div_add_l; [ idtac | apply sqr_radix_neq_0 ].
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
*)

(**** [ NN2I_add2_inj : 
∀ u v : nat → nat,
(∀ i : nat, u i < radix ∧ v i < radix)
→ (NN2I 2 (u + v) == NN2I 2 u + NN2I 2 v)%I ]
*)

Theorem I2NN_NN2I_1 : ∀ u,
  (∀ i, u i ≤ 2 * (radix - 1))
  → (I2NN (NN2I 2 u) = u)%NN.
Proof.
intros u Hu i.
Check NN2I_I2NN.
unfold NN_eq.
Abort. (*
unfold I2NN, NN2I; fsimpl.
rewrite d2n_n2d, Nat.mul_1_r.
unfold summation; rewrite Nat.sub_0_r; simpl.
do 2 rewrite Nat.add_0_r.
do 2 rewrite Nat.mul_1_r.
remember radix as r eqn:Hr.
remember (r * r) as rr eqn:Hrr.
rewrite Nat.div_add_l.
bbb.
*)

Theorem I_add2_assoc : ∀ x y z, (x + (y + z) == (x + y) + z)%I.
Proof.
intros x y z.
unfold I_add2.
Unset Printing Notations. Show.
remember 2 as n eqn:Hn.
Check I2NN_NN2I.
bbb.

rewrite NN2I_compat.
Focus 2.
rewrite NN2I_compat.
Focus 2.
SearchAbout I2NN.
rewrite I2NN_NN2I_1.
Focus 2.
intros i; simpl.
bbb.
(*
remember (I2NN x) as ux.
remember (I2NN y) as uy.
remember (I2NN z) as uz.
*)
Unset Printing Notations. Show.
Check I2NN_NN2I_1.
rewrite NN2I_compat.
Focus 2.
rewrite <- NN2I_add2_inj.
reflexivity.
Unfocus.
bbb.
I2NN (NN2I

rewrite NN2I_I2NN_1.
rewrite NN2I_I2NN.
reflexivity.
Unfocus.
unfold I_add2.
Unset Printing Notations. Show.
Check NN_add_assoc.
Check I2NN_NN2I.
rewrite I2NN_NN2I.
bbb.

NN2I 2 (I2NN (NN2I 2 (I2NN y)

NN2I
NN_add
I2NN

bbb.
   NN2I 2 (I2NN y + I2NN z) == NN2I 2 (I2NN y) + NN2I 2 (I2NN z)
  ============================
   I_eqs
     (NN2I (S (S O))
        (NN_add (I2NN x) (I2NN (NN2I (S (S O)) (NN_add (I2NN y) (I2NN z))))))
     (NN2I (S (S O))
        (NN_add (I2NN (NN2I (S (S O)) (NN_add (I2NN x) (I2NN y)))) (I2NN z)))

unfold NN2I, I2NN, NN_add; fsimpl.
unfold summation; rewrite Nat.sub_0_r; simpl.
do 12 rewrite Nat.add_0_r.
do 9 rewrite Nat.mul_1_r.
do 6 rewrite d2n_n2d.
do 4 rewrite <- Nat.add_assoc; simpl.
do 6 (rewrite Nat.mod_mod; [ idtac | apply Digit.radix_neq_0 ]).
do 8 (rewrite Nat.div_add_l; [ idtac | apply sqr_radix_neq_0 ]).
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
Set Printing Depth 12. Show.
rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
f_equal; f_equal.
Set Printing Depth 13. Show.
rewrite Nat.add_mod_idemp_l; [ idtac | apply Digit.radix_neq_0 ].
do 2 rewrite <- Nat.add_assoc.
rewrite Nat.add_comm; symmetry.
rewrite Nat.add_comm; symmetry.
rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
f_equal; f_equal.
Set Printing Depth 11. Show.
rewrite Nat.add_comm.
rewrite <- Nat.add_assoc.
rewrite Nat.add_comm; symmetry.
rewrite Nat.add_comm; symmetry.
rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
f_equal; f_equal.
clear xi yi zi Hxi Hyi Hzi.
remember (radix * radix) as rr.
Set Printing Depth 30. Show.
do 12 rewrite Nat.add_assoc.
remember radix as r.
do 8 rewrite Nat.mul_add_distr_r.
bbb.

remember (xi1+yi1) as xyi1 eqn:Hxyi1.
remember (xi2+yi2) as xyi2 eqn:Hxyi2.
remember (xi3+yi3) as xyi3 eqn:Hxyi3.
remember (xi4+yi4) as xyi4 eqn:Hxyi4.
remember (yi1+zi1) as yzi1 eqn:Hyzi1.
remember (yi2+zi2) as yzi2 eqn:Hyzi2.
remember (yi3+zi3) as yzi3 eqn:Hyzi3.
remember (yi4+zi4) as yzi4 eqn:Hyzi4.
do 6 rewrite Nat.add_assoc.
rewrite <- Hxyi1, <- Hxyi2.
do 2 rewrite Nat.mul_add_distr_r.
bbb.

rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
rewrite Nat.add_mod; [ symmetry | apply Digit.radix_neq_0 ].
Set Printing Depth 11. Show.
bbb.

do 8 rewrite Nat.mul_add_distr_r.
Unset Printing Notations. Show.
Set Printing Depth 11. Show.

do 2 (rewrite Nat.div_mul; [ idtac | apply sqr_radix_neq_0 ]).
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
do 6 (rewrite Nat.div_mul; [ idtac | apply sqr_radix_neq_0 ]).
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
