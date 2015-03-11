(* Multiplication/Division of a Real by a power of 2 *)

Require Import Utf8 QArith NPeano.
Require Import Digit Real01 Real01Add Real01AddMono.
Require Import Real RealAdd RealAddGrp.

Definition b := 2.

Definition d2n d := if Digit.dec d then 1 else 0.

Definition I_mul_b_pow x n := {| rm i := x.[i+n] |}.
Arguments I_mul_b_pow x%I n%nat.

Definition I_div_b_pow_i x n i := if lt_dec i n then 0%D else x.[i-n].
Arguments I_div_b_pow_i x%I n%nat i%nat.

Definition I_div_b_pow x n := {| rm := I_div_b_pow_i x n |}.
Arguments I_div_b_pow x%I n%nat.

Fixpoint I_mul_b_pow_from xi xf n :=
  match n with
  | 0 => xi
  | S n1 => I_mul_b_pow_from (b * xi + d2n (xf.[0])) (I_mul_b_pow xf 1) n1
  end.

Fixpoint I_div_b_pow_from_int xi n :=
  match n with
  | 0 => if zerop (xi mod 2) then 0%D else 1%D
  | S n1 => I_div_b_pow_from_int (xi / b) n1
  end.

Definition I_div_b_pow_frac_i xi xf n i :=
  if lt_dec i n then I_div_b_pow_from_int xi (pred (n-i))
  else xf.[i-n].

Fixpoint I_div_b_pow_int xi n :=
  match n with
  | 0 => xi
  | S n1 => I_div_b_pow_int (xi / b) n1
  end.

Definition I_div_b_pow_frac xi xf n := {| rm := I_div_b_pow_frac_i xi xf n |}.

Definition R_mul_b_pow x n :=
  let ax := R_abs x in
  let r :=
    let xi := R_int ax in
    let xf := R_frac ax in
    {| R_int := Z.of_nat (I_mul_b_pow_from (Z.to_nat xi) xf n);
       R_frac := I_mul_b_pow xf n |}
  in
  if R_is_neg x then R_opp r else r.

Definition R_div_b_pow x n :=
  let ax := R_abs x in
  let r :=
    let xi := R_int ax in
    let xf := R_frac ax in
    {| R_int := Z.of_nat (I_div_b_pow_int (Z.to_nat xi) n);
       R_frac := I_div_b_pow_frac (Z.to_nat xi) xf n |}
  in
  if R_is_neg x then R_opp r else r.

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
  remember (R_div_b_pow x n) as y eqn:Hy .
  remember (fst_same (R_frac (R_mul_b_pow y n)) 0 0) as s1 eqn:Hs1 .
  remember (fst_same (R_frac x) 0 0) as s2 eqn:Hs2 .
  destruct s1 as [dj1| ].
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct Hs1 as (Hn1, Ht1); rewrite Ht1.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s2 as [dj2| ].
    destruct Hs2 as (Hn2, Ht2); rewrite Ht2; reflexivity.

    unfold R_mul_b_pow in Ht1; simpl in Ht1.
    unfold R_abs in Ht1.
    remember (R_is_neg y) as yn eqn:Hyn; symmetry in Hyn.
    destruct yn; simpl in Ht1.
     rewrite Hy in Ht1.
     unfold R_div_b_pow in Ht1; simpl in Ht1.
     unfold R_abs in Ht1; simpl in Ht1.
     remember (R_is_neg x) as xn eqn:Hxn; symmetry in Hxn.
     destruct xn; simpl in Ht1.
      unfold I_div_b_pow_frac_i in Ht1; simpl in Ht1.
      destruct (lt_dec (dj1 + n) n) as [H1| H1].
       apply Nat.lt_add_lt_sub_r in H1.
       rewrite Nat.sub_diag in H1.
       exfalso; revert H1; apply Nat.nlt_0_r.

       rewrite Hs2 in Ht1; discr_digit Ht1.

      unfold I_div_b_pow_frac_i in Ht1; simpl in Ht1.
      destruct (lt_dec (dj1 + n) n) as [H1| H1].
       apply Nat.lt_add_lt_sub_r in H1.
       rewrite Nat.sub_diag in H1.
       exfalso; revert H1; apply Nat.nlt_0_r.

       rewrite Hs2 in Ht1; discr_digit Ht1.

     rewrite Hy in Ht1.
     unfold R_div_b_pow in Ht1; simpl in Ht1.
     unfold R_abs in Ht1; simpl in Ht1.
     remember (R_is_neg x) as xn eqn:Hxn; symmetry in Hxn.
     destruct xn; simpl in Ht1.
      unfold I_div_b_pow_frac_i in Ht1; simpl in Ht1.
      destruct (lt_dec (dj1 + n) n) as [H1| H1].
       apply Nat.lt_add_lt_sub_r in H1.
       rewrite Nat.sub_diag in H1.
       exfalso; revert H1; apply Nat.nlt_0_r.

       rewrite Hs2 in Ht1; discr_digit Ht1.

      unfold I_div_b_pow_frac_i in Ht1; simpl in Ht1.
      destruct (lt_dec (dj1 + n) n) as [H1| H1].
       apply Nat.lt_add_lt_sub_r in H1.
       rewrite Nat.sub_diag in H1.
       exfalso; revert H1; apply Nat.nlt_0_r.

       rewrite Hs2 in Ht1; discr_digit Ht1.

   destruct s2 as [dj2| ]; [ idtac | reflexivity ].
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   pose proof Hs1 dj2 as H.
   unfold R_mul_b_pow in H; simpl in H.
   unfold R_abs in H; simpl in H.
   remember (R_is_neg y) as yn eqn:Hyn; symmetry in Hyn.
   destruct yn; simpl in H.
    rewrite Hy in H; simpl in H.
    unfold R_div_b_pow in H; simpl in H.
    unfold R_abs in H; simpl in H.
    remember (R_is_neg x) as xn eqn:Hxn; symmetry in Hxn.
    destruct xn; simpl in H.
     unfold I_div_b_pow_frac_i in H; simpl in H.
     destruct (lt_dec (dj2 + n) n) as [H1| H1].
      apply Nat.lt_add_lt_sub_r in H1.
      rewrite Nat.sub_diag in H1.
      exfalso; revert H1; apply Nat.nlt_0_r.

      rewrite Nat.add_sub, Ht2 in H; discr_digit H.

     rewrite Hy in Hyn; simpl in Hyn.
     unfold R_div_b_pow, R_abs in Hyn; simpl in Hyn.
     rewrite Hxn in Hyn; simpl in Hyn.
     unfold R_is_neg in Hyn; simpl in Hyn.
     apply Z.ltb_lt, Z.nle_gt in Hyn.
     exfalso; apply Hyn, Nat2Z.is_nonneg.

    rewrite Hy in H; simpl in H.
    unfold R_div_b_pow, R_abs in H; simpl in H.
    remember (R_is_neg x) as xn eqn:Hxn; symmetry in Hxn.
    destruct xn; simpl in H.
     unfold I_div_b_pow_frac_i in H; simpl in H.
     destruct (lt_dec (dj2 + n) n) as [H1| H1].
      apply Nat.lt_add_lt_sub_r in H1.
      rewrite Nat.sub_diag in H1.
      exfalso; revert H1; apply Nat.nlt_0_r.

      rewrite Nat.add_sub, Ht2 in H; discr_digit H.

     unfold I_div_b_pow_frac_i in H; simpl in H.
     destruct (lt_dec (dj2 + n) n) as [H1| H1].
      apply Nat.lt_add_lt_sub_r in H1.
      rewrite Nat.sub_diag in H1.
      exfalso; revert H1; apply Nat.nlt_0_r.

      rewrite Nat.add_sub, Ht2 in H; discr_digit H.

  remember (R_div_b_pow x n) as y eqn:Hy.
  unfold R_mul_b_pow, R_abs; simpl.
  remember (R_is_neg y) as yn eqn:Hyn; symmetry in Hyn.
  destruct yn; simpl.
   rewrite Hy; simpl.
   unfold R_div_b_pow, R_abs; simpl.
   remember (R_is_neg x) as xn eqn:Hxn; symmetry in Hxn.
   destruct xn; simpl.
bbb.
