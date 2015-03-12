(* Multiplication/Division of a Real by a power of 2 *)

Require Import Utf8 QArith NPeano.
Require Import Digit Real01 Real01Add Real01AddMono.
Require Import Misc Real RealAdd RealAddGrp.

Definition base := 2.

Definition d2n d := if Digit.dec d then 1 else 0.

Definition I_mul_b_pow_frac x n := {| rm i := x.[i+n] |}.
Arguments I_mul_b_pow_frac x%I n%nat.

Definition I_div_b_pow_i x n i := if lt_dec i n then 0%D else x.[i-n].
Arguments I_div_b_pow_i x%I n%nat i%nat.

Definition I_div_b_pow x n := {| rm := I_div_b_pow_i x n |}.
Arguments I_div_b_pow x%I n%nat.

Fixpoint I_mul_b_pow_int a xf n i :=
  match n with
  | 0 => a
  | S n1 => I_mul_b_pow_int (base * a + d2n (xf.[i])) xf n1 (S i)
  end.

Fixpoint I_div_b_pow_from_int xi n :=
  match n with
  | 0 => if zerop (xi mod 2) then 0%D else 1%D
  | S n1 => I_div_b_pow_from_int (xi / base) n1
  end.

Definition I_div_b_pow_frac_i xi xf n i :=
  if lt_dec i n then I_div_b_pow_from_int xi (pred (n-i))
  else xf.[i-n].

Fixpoint I_div_b_pow_int xi n :=
  match n with
  | 0 => xi
  | S n1 => I_div_b_pow_int (xi / base) n1
  end.

Definition I_div_b_pow_frac xi xf n := {| rm := I_div_b_pow_frac_i xi xf n |}.

Definition R_abs_mul_b_pow ax n :=
  let xi := R_int ax in
  let xf := R_frac ax in
  {| R_int := Z.of_nat (I_mul_b_pow_int (Z.to_nat xi) xf n 0);
     R_frac := I_mul_b_pow_frac xf n |}.

Definition R_mul_b_pow x n :=
  let ax := R_abs x in
  let r := R_abs_mul_b_pow ax n in
  if R_is_neg x then R_opp r else r.

Definition R_abs_div_b_pow ax n :=
  let xi := R_int ax in
  let xf := R_frac ax in
  {| R_int := Z.of_nat (I_div_b_pow_int (Z.to_nat xi) n);
     R_frac := I_div_b_pow_frac (Z.to_nat xi) xf n |}.

Definition R_div_b_pow x n :=
  let ax := R_abs x in
  let r := R_abs_div_b_pow ax n in
  if R_is_neg x then R_opp r else r.

Theorem I_mul_b_pow_frac_div : ∀ x n,
  (I_mul_b_pow_frac (I_div_b_pow x n) n = x)%I.
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
 remember (fst_same (I_mul_b_pow_frac (I_div_b_pow x n) n) 0 (S i)) as s1 eqn:Hs1 .
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

Fixpoint two_power n :=
  match n with
  | O => 1
  | S n1 => 2 * two_power n1
  end.

Theorem I_mul_b_pow_int_succ : ∀ a xf n i,
  I_mul_b_pow_int (S a) xf n i = I_mul_b_pow_int a xf n i + two_power n.
Proof.
intros a xf n i.
revert a xf i.
induction n; intros; [ rewrite Nat.add_1_r; reflexivity | simpl ].
do 2 rewrite Nat.add_0_r.
rewrite Nat.add_succ_r; simpl.
do 2 rewrite IHn.
rewrite Nat.add_assoc; reflexivity.
Qed.

(* faux
Add Parametric Morphism : I_mul_b_pow_int
  with signature eq ==> I_eq ==> eq ==> eq
  as I_mul_b_prop_from_morph.
Proof.
intros accu xf yf Hxy n.
apply I_eq_prop in Hxy.
destruct Hxy as [Hxy| (i, (Hlt, (Heq, Hgt)))].
 unfold I_eq_ext in Hxy.
 revert accu xf yf Hxy.
 induction n; intros; [ reflexivity | simpl ].
 rewrite Nat.add_0_r.
 unfold d2n; simpl.
 destruct (Digit.dec (xf.[0])) as [H1| H1].
  destruct (Digit.dec (yf.[0])) as [H2| H2].
   apply IHn; intros i; apply Hxy.

   rewrite Hxy, H2 in H1; discr_digit H1.

  destruct (Digit.dec (yf.[0])) as [H2| H2].
   rewrite Hxy, H2 in H1; discr_digit H1.

   apply IHn; intros i; apply Hxy.

 destruct Hgt as [(Hi, (Hx, Hy))| (Hx, Hy)].
  subst i; clear Hlt.
  revert accu xf yf Heq Hx Hy.
  induction n; intros; [ reflexivity | simpl ].
  rewrite Nat.add_0_r.
  unfold d2n; simpl.
  destruct (Digit.dec (xf.[0])) as [H1| H1].
   destruct (Digit.dec (yf.[0])) as [H2| H2].
    apply IHn; simpl.
     rewrite Hx, Hy; assumption.

     intros j; rewrite Hx; symmetry; apply Hx.

     intros j; rewrite Hy; symmetry; apply Hy.

    rewrite Nat.add_0_r, Nat.add_1_r.
    rewrite I_mul_b_pow_int_succ.
bbb.
*)

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
    remember (R_is_neg y) as yn eqn:Hyn ; symmetry in Hyn.
    destruct yn; simpl in Ht1.
     rewrite Hy in Ht1.
     unfold R_div_b_pow in Ht1; simpl in Ht1.
     unfold R_abs in Ht1; simpl in Ht1.
     remember (R_is_neg x) as xn eqn:Hxn ; symmetry in Hxn.
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
     remember (R_is_neg x) as xn eqn:Hxn ; symmetry in Hxn.
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
   pose proof (Hs1 dj2) as H.
   unfold R_mul_b_pow in H; simpl in H.
   unfold R_abs in H; simpl in H.
   remember (R_is_neg y) as yn eqn:Hyn ; symmetry in Hyn.
   destruct yn; simpl in H.
    rewrite Hy in H; simpl in H.
    unfold R_div_b_pow in H; simpl in H.
    unfold R_abs in H; simpl in H.
    remember (R_is_neg x) as xn eqn:Hxn ; symmetry in Hxn.
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
    remember (R_is_neg x) as xn eqn:Hxn ; symmetry in Hxn.
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

(**)
  remember (R_div_b_pow x n) as y eqn:Hy .
  unfold R_div_b_pow in Hy.
  remember (R_abs x) as ax eqn:Hax .
  remember (R_int ax) as xi eqn:Hxi .
  remember (R_frac ax) as xf eqn:Hxf .
  remember (R_abs_div_b_pow ax n) as rx eqn:Hrx .
  unfold R_mul_b_pow.
  remember (R_abs y) as ay eqn:Hay .
  remember (R_int ay) as yi eqn:Hyi .
  remember (R_frac ay) as yf eqn:Hyf .
  remember (R_abs_mul_b_pow ay n) as ry eqn:Hry .
  unfold R_abs in Hax, Hay.
  remember (R_is_neg x) as nx eqn:Hnx ; symmetry in Hnx.
  remember (R_is_neg y) as ny eqn:Hny ; symmetry in Hny.
  move ay before ax; move xi before ay; move yi before xi.
  move rx before yi; move ry before rx; move xf before ry.
  move ny before nx; move yf before xf; move Hay before Hax.
  move Hrx before Hry; move Hyi before Hxi; move Hyf before Hyi.
  move Hxf after Hyf; move Hny before Hnx.
  destruct nx, ny.
   rewrite Hry; simpl.
   rewrite Hay; simpl.
   rewrite Hy; simpl.
   rewrite Z.opp_sub_distr, Z.opp_involutive, Z.add_simpl_r.
   destruct n; intros.
    rewrite Hrx; simpl.
    rewrite Nat2Z.id.
    rewrite Z2Nat.id.
     rewrite Hax; simpl.
     rewrite Z.opp_sub_distr, Z.opp_involutive, Z.add_simpl_r.
     reflexivity.

     rewrite Hax; simpl.
     unfold R_is_neg in Hnx; simpl in Hnx.
     apply Z.ltb_lt, Z.opp_lt_mono in Hnx; simpl in Hnx.
     apply Z.le_add_le_sub_r, Z.lt_pred_le; assumption.

    simpl; rewrite Nat.add_0_r.

rewrite Hrx; simpl.
rewrite divmod_div.
rewrite Nat2Z.id.
rewrite <- Hxi, <- Hxf.
unfold I_div_b_pow_frac_i; simpl.
rewrite divmod_div.
remember (I_div_b_pow_int (Z.to_nat xi / 2) n) as dxi eqn:Hdxi.
remember (I_div_b_pow_frac (Z.to_nat xi) xf (S n)) as dxf eqn:Hdxf.
remember (I_div_b_pow_from_int (Z.to_nat xi) n) as dxif eqn:Hdxif.
simpl.
bbb.

Focus 1.
remember (R_frac rx.[0]) as v eqn:H.
rewrite Hrx in H; simpl in H.
unfold I_div_b_pow_frac_i in H; simpl in H.
rewrite Hax in H; simpl in H.
bbb.
(**)

  induction n; simpl.
   remember (R_div_b_pow x 0) as y eqn:Hy .
   unfold R_mul_b_pow, R_div_b_pow, R_abs; simpl.
   remember (R_is_neg y) as ny eqn:Hny ; symmetry in Hny.
   destruct ny; simpl.
    rewrite Z2Nat.id.
     rewrite Hy; simpl.
     unfold R_div_b_pow, R_abs; simpl.
     remember (R_is_neg x) as nx eqn:Hnx ; symmetry in Hnx.
     destruct nx; simpl.
      rewrite Z2Nat.id; simpl.
       do 2 rewrite Z.opp_sub_distr, Z.opp_involutive, Z.add_simpl_r.
       reflexivity.

       unfold R_is_neg in Hnx; simpl in Hnx.
       apply Z.ltb_lt, Z.opp_lt_mono in Hnx; simpl in Hnx.
       apply Z.le_add_le_sub_r, Z.lt_pred_le; assumption.

      rewrite Z.opp_sub_distr, Z.opp_involutive, Z.add_simpl_r.
      rewrite Z2Nat.id; [ reflexivity | idtac ].
      unfold R_is_neg in Hnx; simpl in Hnx.
      apply Z.ltb_nlt, Z.nlt_ge in Hnx; simpl in Hnx.
      assumption.

     unfold R_is_neg in Hny; simpl in Hny.
     apply Z.ltb_lt, Z.opp_lt_mono in Hny; simpl in Hny.
     apply Z.le_add_le_sub_r, Z.lt_pred_le; assumption.

    rewrite Z2Nat.id.
     rewrite Hy; simpl.
     unfold R_div_b_pow, R_abs; simpl.
     remember (R_is_neg x) as nx eqn:Hnx ; symmetry in Hnx.
     destruct nx; simpl.
      rewrite Z2Nat.id.
       rewrite Z.opp_sub_distr, Z.opp_involutive, Z.add_simpl_r.
       reflexivity.

       unfold R_is_neg in Hnx; simpl in Hnx.
       apply Z.ltb_lt, Z.opp_lt_mono in Hnx; simpl in Hnx.
       apply Z.le_add_le_sub_r, Z.lt_pred_le; assumption.

      rewrite Z2Nat.id; [ reflexivity | idtac ].
      unfold R_is_neg in Hnx; simpl in Hnx.
      apply Z.ltb_nlt, Z.nlt_ge in Hnx; assumption.

     unfold R_is_neg in Hny; simpl in Hny.
     apply Z.ltb_nlt, Z.nlt_ge in Hny; assumption.

Focus 1.
unfold R_mul_b_pow, R_div_b_pow; simpl.
bbb.

      rewrite Z2Nat.id; simpl.
       reflexivity.

       unfold R_is_neg in Hnx; simpl in Hnx.
       apply Z.ltb_lt, Z.opp_lt_mono in Hnx; simpl in Hnx.
       apply Z.le_add_le_sub_r, Z.lt_pred_le; assumption.

      rewrite Z2Nat.id; simpl.
      rewrite Z.opp_sub_distr, Z.opp_involutive, Z.add_simpl_r.
      reflexivity.

      rewrite Hy in Hny; simpl in Hny.
      unfold R_div_b_pow, R_abs in Hny; simpl in Hny.
      rewrite Hnx in Hny; simpl in Hny.


      rewrite Z2Nat.id in Hny; simpl in Hny.
       unfold R_is_neg in Hnx, Hny; simpl in Hnx, Hny.
       rewrite Hnx in Hny; discriminate Hny.


       rewrite Z2Nat.id in Hny; simpl in Hny.
       unfold R_is_neg in Hnx, Hny; simpl in Hnx, Hny.
       rewrite Hnx in Hny; discriminate Hny.

      do 2 rewrite Z.opp_sub_distr, Z.opp_involutive, Z.add_simpl_r.
      reflexivity.

bbb.
  remember (R_div_b_pow x n) as y eqn:Hy.
  unfold R_mul_b_pow, R_abs; simpl.
  remember (R_is_neg y) as yn eqn:Hyn; symmetry in Hyn.
  destruct yn; simpl.
   rewrite Hy; simpl.
   unfold R_div_b_pow, R_abs; simpl.
   remember (R_is_neg x) as xn eqn:Hxn; symmetry in Hxn.
   destruct xn; simpl.
bbb.
