(* Multiplication/Division of a Real by a power of 2 *)

Require Import Utf8 QArith NPeano.
Require Import Digit Real01 Real01Add Real RealAdd RealAddGrp.

Definition b := 2%Z.

Definition I_mul_b_pow x n := {| rm i := x.[i+n] |}.
Arguments I_mul_b_pow x%I n%nat.

Definition I_div_b_pow_i x n i := if lt_dec i n then 0%D else x.[i-n].
Arguments I_div_b_pow_i x%I n%nat i%nat.

Definition I_div_b_pow x n := {| rm := I_div_b_pow_i x n |}.
Arguments I_div_b_pow x%I n%nat.

Fixpoint I_mul_b_pow_from xi xf n :=
  match n with
  | 0 => xi
  | S n1 => I_mul_b_pow_from (b * xi + b2z (xf.[n]))%Z xf n1
  end.

Fixpoint I_div_b_pow_from_int xi n :=
  match n with
  | 0 => if Z_zerop (xi mod 2) then 0%D else 1%D
  | S n1 => I_div_b_pow_from_int (xi / b)%Z n1
  end.

Definition I_div_b_pow_frac_i xi xf n i :=
  if lt_dec i n then I_div_b_pow_from_int xi (pred (n-i))
  else xf.[i-n].

Fixpoint I_div_b_pow_int xi n :=
  match n with
  | 0 => xi
  | S n1 => I_div_b_pow_int (xi / b)%Z n1
  end.

Definition I_div_b_pow_frac xi xf n := {| rm := I_div_b_pow_frac_i xi xf n |}.

Definition R_mul_b_pow x n :=
  {| R_int := I_mul_b_pow_from (R_int x) (R_frac x) n;
     R_frac := I_mul_b_pow (R_frac x) n |}.

Definition R_div_b_pow x n :=
  {| R_int := I_div_b_pow_int (R_int x) n;
     R_frac := I_div_b_pow_frac (R_int x) (R_frac x) n |}.

Theorem I_mul_b_pow_div : ∀ x n, (I_mul_b_pow (I_div_b_pow x n) n = x)%I.
Proof.
intros x n.
unfold I_eq; intros i; simpl.
unfold I_add_i; simpl.
do 2 rewrite Digit.add_0_r.
unfold I_div_b_pow_i; simpl.
rewrite Nat.add_sub.
destruct (lt_dec (i + n) n) as [H1| H1].
 apply Nat.lt_add_lt_sub_r in H1.
 rewrite Nat.sub_diag in H1.
 exfalso; revert H1; apply Nat.nlt_0_r.

 clear H1.
 apply Digit.add_compat; [ reflexivity | idtac ].
 unfold carry; simpl.
 remember (fst_same (I_mul_b_pow (I_div_b_pow x n) n) 0 (S i)) as s1 eqn:Hs1 .
 remember (fst_same x 0 (S i)) as s2 eqn:Hs2 .
 destruct s1 as [dj1| ].
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, Ht1); rewrite Ht1.
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s2 as [dj2| ].
   destruct Hs2 as (Hn2, Ht2); rewrite Ht2; reflexivity.

   unfold I_div_b_pow_i in Ht1; simpl in Ht1.
   destruct (lt_dec (S (i + dj1 + n)) n) as [H1| H1].
    rewrite <- Nat.add_succ_l in H1.
    apply Nat.lt_add_lt_sub_r in H1.
    rewrite Nat.sub_diag in H1.
    exfalso; revert H1; apply Nat.nlt_0_r.

    clear H1; simpl in Ht1.
    destruct n.
     rewrite Nat.add_0_r in Ht1.
     rewrite Hs2 in Ht1; discr_digit Ht1.

     rewrite Nat.add_succ_r, <- Nat.add_succ_l, Nat.add_sub in Ht1.
     rewrite Hs2 in Ht1; discr_digit Ht1.

  destruct s2 as [dj2| ]; [ idtac | reflexivity ].
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  pose proof (Hs1 dj2) as H.
  unfold I_div_b_pow_i in H; simpl in H.
  destruct (lt_dec (S (i + dj2 + n)) n) as [H1| H1].
   discr_digit H.

   clear H1; destruct n; simpl.
    rewrite Nat.add_0_r in H; rewrite H; reflexivity.

    rewrite Nat.add_succ_r, <- Nat.add_succ_l, Nat.add_sub in H.
    rewrite H; reflexivity.
Qed.

Theorem R_mul_b_pow_div : ∀ x n, (R_mul_b_pow (R_div_b_pow x n) n = x)%R.
Proof.
intros x n.
unfold R_eq; simpl; split.
 f_equal.
  Focus 2.
  unfold carry; simpl.
  remember (I_div_b_pow_frac (R_int x) (R_frac x) n) as y eqn:Hy .
  remember (fst_same (I_mul_b_pow y n) 0 0) as s1 eqn:Hs1 .
  remember (fst_same (R_frac x) 0 0) as s2 eqn:Hs2 .
  destruct s1 as [dj1| ].
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct Hs1 as (Hn1, Ht1).
   unfold I_div_b_pow_frac_i; simpl.
   rewrite Nat.add_sub.
   rewrite Hy in Ht1; simpl in Ht1.
   unfold I_div_b_pow_frac_i in Ht1; simpl in Ht1.
   destruct (lt_dec (dj1 + n) n) as [H1| H1].
    apply Nat.lt_add_lt_sub_r in H1.
    rewrite Nat.sub_diag in H1.
    exfalso; revert H1; apply Nat.nlt_0_r.

    clear H1.
    rewrite Nat.add_sub in Ht1; rewrite Ht1.
    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    destruct s2 as [dj2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2; reflexivity.

     rewrite Hs2 in Ht1; discr_digit Ht1.

   destruct s2 as [dj2| ]; [ idtac | reflexivity ].
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   rewrite Hy in Hs1; simpl in Hs1.
   unfold I_div_b_pow_frac_i in Hs1; simpl in Hs1.
   pose proof Hs1 dj2 as H; rewrite Nat.add_sub in H.
   destruct (lt_dec (dj2 + n) n) as [H1| H1].
    apply Nat.lt_add_lt_sub_r in H1.
    rewrite Nat.sub_diag in H1.
    exfalso; revert H1; apply Nat.nlt_0_r.

    rewrite H; reflexivity.

  remember (R_int x) as xi.
  remember (R_frac x) as yi.
  clear x Heqxi Heqyi.
  revert xi yi; induction n; intros; [ reflexivity | simpl ].
  unfold I_div_b_pow_frac_i.
  rewrite Nat.sub_diag.
  destruct (lt_dec (S n) (S n)) as [H1| H1].
   exfalso; revert H1; apply Nat.lt_irrefl.

   clear H1.
   remember (I_div_b_pow_int (xi / b) n) as z eqn:Hz.
   symmetry in Hz.
   destruct z as [| p| p].
    simpl.
    destruct n.
     simpl.
     destruct xi.
      simpl in Hz.
      simpl.
bbb.
