(* division in ℝ *)

Require Import Utf8 QArith NPeano.
Require Import Real01Add RealAdd Real01Div.

Set Implicit Arguments.

Open Scope Z_scope.

Definition R_div_2 x :=
  {| R_int := R_int x / 2;
     R_frac := I_div_2_inc (R_frac x) (Z.odd (R_int x)) |}.
Arguments R_div_2 x%R.

Fixpoint R_frac_equiv_div m x y :=
  match m with
  | O => (0%I, 0%I)
  | S m1 =>
      let x2 := R_div_2 x in
      let y2 := R_div_2 y in
      if Z.eqb (R_int x) 0 && Z.eqb (R_int y) 0 then
        (R_frac x2, R_frac y2)
      else
        R_frac_equiv_div m1 x2 y2
  end.
Arguments R_frac_equiv_div m%Z x%I y%I.

Fixpoint two_power n :=
  match n with
  | O => 1%nat
  | S n1 => (2 * two_power n1)%nat
  end.

Fixpoint R_frac_div_loop m x y :=
  match m with
  | O => (O, 0%I)
  | S m1 =>
      if I_lt_dec x y then (O, x)
      else
        let (q, r) := R_frac_div_loop m1 (I_sub x y) y in
        (S q, r)
  end.
Arguments R_frac_div_loop m%nat x%I y%I.

Definition R_frac_div x y :=
  match fst_same x I_ones 0 with
  | Some jx =>
      match fst_same y I_ones 0 with
      | Some jy =>
          if le_dec jx jy then
            let m := two_power (S (jy - jx)) in
            let (q, r) := R_frac_div_loop m x y in
            (q, I_div r y)
          else
            (O, I_div x y)
      | None => (O, y)
      end
  | None => (O, 0%I)
  end.
Arguments R_frac_div x%I y%I.

Definition R_is_neg x := Z.ltb (R_int x) 0.
Arguments R_is_neg x%R.

Definition R_abs x := if R_is_neg x then R_opp x else x.
Arguments R_abs x%R.

Definition max_iter_int_part ax ay := Z.to_nat (R_int ax + R_int ay + 1).

Definition R_div x y :=
  let ax := R_abs x in
  let ay := R_abs y in
  let m := max_iter_int_part ax ay in
  let (xm, ym) := R_frac_equiv_div m ax ay in
  let (q, rm) := R_frac_div xm ym in
  let qz := Z.of_nat q in
  {| R_int := if R_is_neg x ⊕ R_is_neg y then -qz else qz;
     R_frac := rm |}.
Arguments R_div x%R y%R.

Definition R_one := {| R_int := 1; R_frac := 0 |}.

Notation "1" := R_one : R_scope.
Notation "x / y" := (R_div x y) : R_scope.

(* *)

Definition R_frac_equiv_div_fst x y :=
  fst (R_frac_equiv_div (max_iter_int_part x y) x y).

Theorem fold_R_frac_equiv_div_fst : ∀ x y,
  fst (R_frac_equiv_div (max_iter_int_part x y) x y) = R_frac_equiv_div_fst x y.
Proof. reflexivity. Qed.

Theorem b2z_inj : ∀ b1 b2, b2z b1 = b2z b2 → b1 = b2.
Proof.
intros b1 b2 H.
destruct b1, b2; try reflexivity; discriminate H.
Qed.

Theorem two_power_neq_0 : ∀ n, two_power n ≠ O.
Proof.
intros n H.
induction n; [ discriminate H | simpl in H ].
rewrite Nat.add_0_r in H.
apply Nat.eq_add_0 in H.
destruct H as (H, _).
apply IHn; assumption.
Qed.

Theorem same_carry_fst_same_none : ∀ x y,
  carry x 0 0 = carry y 0 0
  → fst_same (I_div_2_inc y false) 0 1 = None
  → ∀ i, x.[i] = true.
Proof.
intros x y Hixy Hs2 i.
apply not_false_iff_true; intros Ht1.
remember Hs2 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
rename H into Hn2.
unfold carry in Hixy; simpl in Hixy.
remember (fst_same x 0 0) as s3 eqn:Hs3 .
remember (fst_same y 0 0) as s4 eqn:Hs4 .
destruct s3 as [dj3| ].
 remember Hs3 as H; clear HeqH.
 apply fst_same_sym_iff in H; simpl in H.
 destruct H as (Hn3, Ht3).
 rewrite Ht3 in Hixy.
 destruct s4 as [dj4| ]; [ idtac | discriminate Hixy ].
 remember Hs4 as H; clear HeqH.
 apply fst_same_sym_iff in H; simpl in H.
 destruct H as (Hn4, Ht4).
 pose proof (Hn2 dj4) as H.
 rewrite Nat.sub_0_r, Ht4 in H; discriminate H.

 remember Hs3 as H; clear HeqH.
 apply fst_same_sym_iff in H; simpl in H.
 rename H into Hn3.
 rewrite Hn3 in Ht1; discriminate Ht1.
Qed.

Theorem Z_nlt_1_0 : (1 <? 0) = false.
Proof. reflexivity. Qed.

Theorem Pos2Nat_ne_0 : ∀ a, (Pos.to_nat a ≠ 0)%nat.
Proof.
intros a H.
pose proof Pos2Nat.is_pos a as HH.
rewrite H in HH.
revert HH; apply lt_irrefl.
Qed.

Theorem R_div_2_0 : (R_div_2 0 = 0)%R.
Proof.
unfold R_eq; simpl.
split; [ idtac | apply I_div_2_0_false ].
f_equal.
rewrite carry_diag; simpl.
unfold carry; simpl.
remember (fst_same (I_div_2_inc 0 false) 0 0) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ]; [ idtac | exfalso ].
 destruct Hs1 as (Hn1, Ht1); assumption.

 pose proof (Hs1 O) as H.
 discriminate H.
Qed.

Theorem R_div_2_0_if : ∀ x, (x = 0)%R → (R_div_2 x = 0)%R.
Proof.
intros x Hx.
remember Hx as H; clear HeqH.
apply R_zero_if in H; simpl in H.
destruct H as [(Hi, Hf)| (Hi, Hf)].
 unfold R_eq; simpl.
 rewrite Hi; simpl.
 remember (I_div_2_inc (R_frac x) false) as z eqn:Hz .
 rewrite carry_diag; simpl.
 split.
  unfold carry; simpl.
  remember (fst_same z 0 0) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ]; [ idtac | exfalso ].
   destruct Hs1 as (Hn1, Ht1).
   rewrite Ht1; reflexivity.

   pose proof (Hs1 O) as H.
   rewrite Hz in H; discriminate H.

  unfold I_eq; simpl; intros i.
  unfold I_add_i; simpl.
  rewrite xorb_false_r, carry_diag; simpl.
  rewrite Hz in |- * at 1; simpl.
  unfold carry; simpl.
  remember (fst_same z 0 (S i)) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ].
   destruct Hs1 as (Hn1, Ht1); rewrite Ht1, xorb_false_r.
   destruct (zerop i); [ reflexivity | apply Hf ].

   pose proof (Hs1 O) as H.
   rewrite Hz in H; simpl in H.
   rewrite Hf in H; discriminate H.

 unfold R_eq; simpl.
 rewrite Z.add_comm.
 rewrite Hi; simpl.
 remember (I_div_2_inc (R_frac x) true) as z eqn:Hz .
 rewrite carry_diag; simpl.
 split.
  unfold carry; simpl.
  remember (fst_same z 0 0) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ]; [ idtac | reflexivity ].
  destruct Hs1 as (Hn1, Ht1).
  rewrite Hz in Ht1; simpl in Ht1.
  destruct (zerop dj1); [ discriminate Ht1 | idtac ].
  rewrite Hf in Ht1; discriminate Ht1.

  unfold I_eq; simpl; intros i.
  unfold I_add_i; simpl.
  rewrite xorb_false_r, carry_diag; simpl.
  rewrite Hz in |- * at 1; simpl.
  unfold carry; simpl.
  remember (fst_same z 0 (S i)) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ].
   destruct Hs1 as (Hn1, Ht1); rewrite Ht1, xorb_false_r.
   rewrite Hz in Ht1; simpl in Ht1.
   rewrite Hf in Ht1; discriminate Ht1.

   destruct (zerop i) as [H1| H1]; [ reflexivity | idtac ].
   rewrite Hf; reflexivity.
Qed.

Theorem R_frac_equiv_div_fst_is_0 : ∀ x y,
  (x = 0)%R
  → 0 <= R_int x
  → (R_frac_equiv_div_fst x y = 0)%I.
Proof.
intros x y Hx Hxpos.
remember Hx as H; clear HeqH.
apply R_zero_if in H; simpl in H.
destruct H as [(Hi, Hf)| (Hi, Hf)].
 unfold R_frac_equiv_div_fst; simpl.
 remember (max_iter_int_part x y) as m eqn:Hm .
 clear Hm Hxpos.
 revert x Hx Hi Hf y.
 induction m; intros; [ reflexivity | simpl ].
 rewrite Hi; simpl.
 remember (R_int y =? 0) as c eqn:Hiy .
 symmetry in Hiy.
 destruct c.
  apply Z.eqb_eq in Hiy; simpl.
  unfold I_eq; simpl; intros i.
  unfold I_add_i; simpl.
  rewrite xorb_false_r, carry_diag; simpl.
  unfold carry; simpl.
  remember (I_div_2_inc (R_frac x) false) as z eqn:Hz .
  remember (fst_same z 0 (S i)) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ].
   do 2 rewrite Hf.
   destruct (zerop i); reflexivity.

   pose proof (Hs1 O) as H; subst z; simpl in H.
   rewrite Hf in H; discriminate H.

  apply Z.eqb_neq in Hiy; simpl.
  apply IHm; simpl.
   apply R_div_2_0_if; assumption.

   rewrite Hi; reflexivity.

   intros i.
   rewrite Hi, Hf; simpl.
   destruct (zerop i); reflexivity.

 rewrite Hi in Hxpos.
 apply Z.nlt_ge in Hxpos.
 exfalso; apply Hxpos.
 apply Pos2Z.neg_is_neg.
Qed.

Theorem R_frac_equiv_div_0_l : ∀ m x y xm ym,
  (x = 0)%R
  → R_frac_equiv_div m x y = (xm, ym)
  → (∀ i, xm.[i] = false).
Proof.
intros m x y xm ym Hx HI i.
revert x y xm ym Hx HI i.
induction m; intros.
 simpl in HI.
 injection HI; clear HI; intros; subst xm; reflexivity.

 simpl in HI.
 remember ((R_int x =? 0) && (R_int y =? 0)) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  injection HI; clear HI; intros; subst xm ym; simpl.
  apply andb_true_iff in Hc.
  destruct Hc as (Hix, Hiy).
  apply Z.eqb_eq in Hix; simpl in Hix.
  rewrite Hix; simpl.
  destruct (zerop i) as [H1| H1]; [ reflexivity | idtac ].
  apply R_zero_if in Hx.
  destruct Hx as [(Hxz, Hf)| (Hxz, Hf)].
   apply Hf.

   rewrite Hxz in Hix; discriminate Hix.

  eapply IHm; [ idtac | eassumption ].
  apply R_div_2_0_if; assumption.
Qed.

Theorem R_frac_equiv_div_snd_prop : ∀ m x y xm ym,
  R_frac_equiv_div m x y = (xm, ym)
  → ym.[0] = false.
Proof.
intros m x y xm ym HI.
revert x y xm ym HI.
induction m; intros.
 simpl in HI.
 injection HI; clear HI; intros; subst xm.
 subst ym; reflexivity.

 simpl in HI.
 remember ((R_int x =? 0) && (R_int y =? 0)) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  injection HI; clear HI; intros; subst xm ym; simpl.
  apply andb_true_iff in Hc.
  destruct Hc as (Hix, Hiy).
  apply Z.eqb_eq in Hiy; simpl in Hiy.
  rewrite Hiy; reflexivity.

  apply andb_false_iff in Hc.
  eapply IHm with (x := R_div_2 x); eassumption.
Qed.

Theorem R_div_0_l : ∀ x, (0 / x = 0)%R.
Proof.
intros x.
unfold R_eq; simpl.
rewrite carry_diag; simpl.
split.
 unfold carry; simpl.
 remember (fst_same (R_frac (0 / x)) 0 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [dj1| ].
  destruct Hs1 as (Hn1, Ht1).
  rewrite Ht1; simpl.
  rewrite Z.add_0_r.
  unfold R_div; simpl.
  remember (max_iter_int_part (R_abs 0) (R_abs x)) as m eqn:Hm .
  remember (R_frac_equiv_div m (R_abs 0) (R_abs x)) as xym eqn:Hxym .
  symmetry in Hxym.
  destruct xym as (xm, ym).
  remember (R_frac_div xm ym) as qr eqn:Hqr .
  symmetry in Hqr.
  destruct qr as (q, r); simpl.
  unfold R_frac_div in Hqr.
  remember (fst_same xm I_ones 0) as s2 eqn:Hs2 .
  destruct s2 as [dj2| ].
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   remember Hxym as H; clear HeqH.
   apply R_frac_equiv_div_0_l with (i := dj2) in H; [ idtac | reflexivity ].
   rewrite Ht2 in H; discriminate H.

   injection Hqr; clear Hqr; intros; subst q r.
   destruct (R_is_neg x); reflexivity.

  unfold R_div; simpl.
  remember (max_iter_int_part (R_abs 0) (R_abs x)) as m eqn:Hm .
  remember (R_frac_equiv_div m (R_abs 0) (R_abs x)) as xym eqn:Hxym .
  symmetry in Hxym.
  destruct xym as (xm, ym).
  remember (R_frac_div xm ym) as qr eqn:Hqr .
  symmetry in Hqr.
  destruct qr as (q, r); simpl.
  unfold R_frac_div in Hqr.
  remember (fst_same xm I_ones 0) as s2 eqn:Hs2 .
  destruct s2 as [dj2| ].
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   remember Hxym as H; clear HeqH.
   apply R_frac_equiv_div_0_l with (i := dj2) in H; [ idtac | reflexivity ].
   rewrite Ht2 in H; discriminate H.

   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   injection Hqr; clear Hqr; intros; subst q r.
   exfalso.
   pose proof (Hs1 O) as H.
   unfold R_div in H; simpl in H.
   rewrite <- Hm in H.
   rewrite Hxym in H.
   remember (R_frac_div xm ym) as qr1 eqn:Hqr1 .
   symmetry in Hqr1.
   destruct qr1 as (q1, r1); simpl in H.
   rename H into Hr1.
   unfold R_frac_div in Hqr1.
   remember (fst_same xm I_ones 0) as s3 eqn:Hs3 .
   destruct s3 as [dj3| ].
    apply fst_same_sym_iff in Hs3; simpl in Hs3.
    destruct Hs3 as (Hn3, Ht3).
    rewrite Hs2 in Ht3; discriminate Ht3.

    injection Hqr1; clear Hqr1; intros; subst q1 r1.
    discriminate Hr1.

 unfold I_eq; simpl; intros i.
 unfold I_add_i; simpl.
 rewrite xorb_false_r, carry_diag; simpl.
 unfold R_div; simpl.
 remember (max_iter_int_part (R_abs 0) (R_abs x)) as m eqn:Hm .
 remember (R_frac_equiv_div m (R_abs 0) (R_abs x)) as xym eqn:Hxym .
 symmetry in Hxym.
 destruct xym as (xm, ym).
 remember (R_frac_div xm ym) as qr eqn:Hqr .
 symmetry in Hqr.
 destruct qr as (q, r); simpl.
 unfold R_frac_div in Hqr.
 remember (fst_same xm I_ones 0) as s2 eqn:Hs2 .
 destruct s2 as [dj2| ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  remember Hxym as H; clear HeqH.
  apply R_frac_equiv_div_0_l with (i := dj2) in H; [ idtac | reflexivity ].
  rewrite Ht2 in H; discriminate H.

  injection Hqr; clear Hqr; intros; subst q r.
  rewrite carry_diag; reflexivity.
Qed.

Theorem R_nneg_1 : R_is_neg 1 = false.
Proof. apply Z_nlt_1_0. Qed.

Theorem R_int_abs : ∀ x, 0 <= R_int (R_abs x).
Proof.
intros x.
unfold R_abs; simpl.
remember (R_is_neg x) as ng eqn:Hng .
symmetry in Hng.
destruct ng; simpl; [ idtac | apply Z.ltb_ge; assumption ].
apply Z.ltb_lt in Hng.
unfold Z.sub.
rewrite <- Z.opp_add_distr, <- Z.opp_0.
apply Z.opp_le_mono.
do 2 rewrite Z.opp_involutive.
apply Zlt_succ_le; simpl.
apply Z.add_lt_mono_r with (p := 1) in Hng.
assumption.
Qed.

Theorem max_iter_int_part_abs_ne_0 : ∀ x y,
  max_iter_int_part (R_abs x) (R_abs y) ≠ 0%nat.
Proof.
intros x y Hm.
unfold max_iter_int_part in Hm; simpl in Hm.
remember (R_int (R_abs x)) as iax eqn:Hiax .
symmetry in Hiax.
destruct iax as [| iax| iax].
 remember (R_int (R_abs y)) as iay eqn:Hiay .
 symmetry in Hiay.
 simpl in Hm.
 destruct iay as [| iay| iay]; try discriminate Hm.
  revert Hm; apply Pos2Nat_ne_0.

  pose proof (R_int_abs y) as H.
  rewrite Hiay in H.
  apply Z.nlt_ge in H.
  apply H, Pos2Z.neg_is_neg.

 remember (R_int (R_abs y)) as iay eqn:Hiay .
 symmetry in Hiay.
 destruct iay as [| iay| iay]; try (revert Hm; apply Pos2Nat_ne_0).
 pose proof (R_int_abs y) as H.
 rewrite Hiay in H.
 apply Z.nlt_ge in H.
 exfalso; apply H, Pos2Z.neg_is_neg.

 pose proof (R_int_abs x) as H.
 rewrite Hiax in H.
 apply Z.nlt_ge in H.
 exfalso; apply H, Pos2Z.neg_is_neg.
Qed.

Theorem zzz : ∀ x, R_int (x / 1) = R_int x.
Proof.
intros x.
unfold R_div; simpl.
remember (max_iter_int_part (R_abs x) (R_abs 1)) as m eqn:Hm .
remember (R_frac_equiv_div m (R_abs x) (R_abs 1)) as xym eqn:Hxym .
symmetry in Hxym.
destruct xym as (xm, ym).
remember (R_frac_div xm ym) as qr eqn:Hqr .
symmetry in Hqr.
destruct qr as (q, r); simpl.
rewrite R_nneg_1, xorb_false_r.
bbb.
symmetry in Hm.
destruct m.
 exfalso; revert Hm; apply max_iter_int_part_abs_ne_0.

 simpl in Hxym.
 rewrite andb_false_r in Hxym.
bbb.
*)

Theorem R_div_1_r : ∀ x, (x / 1 = x)%R.
Proof.
intros x.
unfold R_eq; simpl.
split.
 unfold R_div; simpl.
 remember (max_iter_int_part (R_abs x) (R_abs 1)) as m eqn:Hm .
 remember (R_frac_equiv_div m (R_abs x) (R_abs 1)) as xym eqn:Hxym .
 symmetry in Hxym.
 destruct xym as (xm, ym).
 remember (R_frac_div xm ym) as qr eqn:Hqr .
 symmetry in Hqr.
 destruct qr as (q, r); simpl.
 unfold carry; simpl.
 remember (fst_same r 0 0) as s1 eqn:Hs1 .
 remember (fst_same (R_frac x) 0 0) as s2 eqn:Hs2 .
 destruct s1 as [dj1| ].
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, Ht1).
  rewrite Ht1, Z.add_0_r.
  destruct s2 as [dj2| ].
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   rewrite Ht2, Z.add_0_r.
   unfold R_is_neg at 2; simpl.
   rewrite Z_nlt_1_0, xorb_false_r.
   unfold R_frac_div in Hqr; simpl in Hqr.
   remember (fst_same xm I_ones 0) as s3 eqn:Hs3 .
   remember (fst_same ym I_ones 0) as s4 eqn:Hs4 .
   destruct s3 as [dj3| ].
    apply fst_same_sym_iff in Hs3; simpl in Hs3.
    destruct Hs3 as (Hn3, Ht3).
    destruct s4 as [dj4| ].
     apply fst_same_sym_iff in Hs4; simpl in Hs4.
     destruct Hs4 as (Hn4, Ht4).
     destruct (le_dec dj3 dj4) as [H1| H1].
      rewrite Nat.add_0_r in Hqr.
      remember (two_power (dj4 - dj3)) as t eqn:Ht .
      remember (R_frac_div_loop (t + t) xm ym) as qr1 eqn:Hqr1 .
      symmetry in Hqr1.
      destruct qr1 as (q1, r1).
      injection Hqr; clear Hqr; intros; subst q1 r.
      remember (t + t)%nat as tt eqn:Htt .
      symmetry in Htt.
      destruct tt.
       symmetry in Ht.
       apply Nat.eq_add_0 in Htt.
       destruct Htt as (Htt, _); move Htt at top; subst t.
       exfalso; revert Ht; apply two_power_neq_0.

       simpl in Hqr1.
       destruct (I_lt_dec xm ym) as [H2| H2].
        injection Hqr1; clear Hqr1; intros; subst q r1.
        simpl in Hn1, Ht1.
        symmetry in Hm.
        destruct m.
         simpl in Hxym.
         unfold max_iter_int_part in Hm.
         simpl in Hm.
         injection Hxym; clear Hxym; intros; subst xm ym.
         discriminate Ht3.

         simpl in Hxym.
         rewrite andb_false_r in Hxym.

bbb.

intros x.
unfold R_div; simpl.
remember (R_abs x) as ax eqn:Hax .
unfold R_abs; simpl.
remember (R_is_neg x) as nxp eqn:Hnxp .
unfold R_is_neg; simpl.
rewrite Z_nlt_1_0, xorb_false_r.
remember (max_iter_int_part ax 1%R) as m eqn:Hm .
remember (R_frac_equiv_div m ax 1%R) as mm eqn:Hmm .
symmetry in Hmm.
destruct mm as (xm, ym).
remember (R_frac_div xm ym) as qrm eqn:Hqrm .
symmetry in Hqrm.
destruct qrm as (q, rm).
destruct m.
 unfold max_iter_int_part in Hm.
 simpl in Hm.
 subst ax.
 unfold R_abs in Hm.
 rewrite <- Hnxp in Hm.
 destruct nxp.
  simpl in Hm.
  rewrite Z.add_comm in Hm.
  simpl in Hm.
  rewrite Z.add_comm in Hm.
  simpl in Hm.
  remember (- R_int x - 1) as a.
  destruct a; [ discriminate Hm | idtac | idtac ].
   destruct p; [ discriminate Hm | idtac | discriminate Hm ].
   simpl in Hm.
   symmetry in Hm.
   exfalso; revert Hm; apply Pos2Nat_ne_0.

   remember (Z.pos_sub 1 p) as n eqn:Hn .
   symmetry in Hn.
   destruct n; [ discriminate Hm | idtac | idtac ].
    simpl in Hm.
    symmetry in Hm.
    exfalso; revert Hm; apply Pos2Nat_ne_0.
bbb.

Theorem yyy : ∀ x, (0 < x)%R → (x / x = 1)%R.
Proof.
intros x Hx.
unfold R_div; simpl.
remember (R_abs x) as ax eqn:Hax .
remember (R_is_neg x) as nxp eqn:Hnxp .
symmetry in Hnxp.
remember (max_iter_int_part ax ax) as m eqn:Hm .
remember (R_frac_equiv_div m ax ax) as mm eqn:Hmm .
symmetry in Hmm.
destruct mm as (xm, ym).
remember (R_frac_div xm ym) as qrm eqn:Hqrm .
symmetry in Hqrm.
destruct qrm as (q, rm).
unfold R_eq.
split; [ idtac | simpl ].
 unfold R_norm.
 remember Z.add as f; simpl.
bbb.

Theorem zzz : ∀ x, (0 < x)%R → (x ≤ 1)%R → (1 / x ≥ 1)%R.
Proof.
intros x Hxgt Hxle.
unfold R_div; simpl.
remember (R_abs x) as ax eqn:Hax .
unfold R_abs; simpl.
remember (R_is_neg x) as nxp eqn:Hnxp .
symmetry in Hnxp.
destruct nxp.
 unfold R_lt in Hxgt; simpl in Hxgt.
 unfold R_is_neg in Hnxp.
 unfold Z.ltb in Hnxp.
 remember (R_int x ?= 0) as xzc eqn:Hxzc .
 symmetry in Hxzc.
 destruct xzc; try discriminate Hnxp; clear Hnxp.
 Focus 2.
 remember (max_iter_int_part 1%R ax) as m eqn:Hm .
 remember (R_frac_equiv_div m 1%R ax) as mm eqn:Hmm .
 symmetry in Hmm.
 destruct mm as (xm, ym).
 remember (R_frac_div xm ym) as qrm eqn:Hqrm .
 symmetry in Hqrm.
 destruct qrm as (q, rm).
 unfold R_ge.
bbb.

Theorem R_inv_involutive : ∀ x, (R_div 1%R (R_div 1%R x) = x)%R.
Proof.
intros x.
unfold R_eq; simpl.
split.
 unfold R_div at 1.
 remember (R_abs 1) as ax eqn:Hax .
 remember (R_abs (1 / x)) as ay eqn:Hay; simpl.
 remember (Z.to_nat (R_int ax + R_int ay)) as m eqn:Hm .
 unfold R_abs in Hax, Hay.
 simpl in Hax, Hay; subst ax.
 remember (R_div_2 1) as r1 eqn:Hr1 .
 unfold R_div_2 in Hr1; simpl in Hr1.
 unfold Z.div in Hr1; simpl in Hr1.
 remember (R_div_2 (1 / x)) as r2 eqn:Hr2 .
 remember (R_frac_equiv_div m r1 r2) as mm eqn:Hmm .
 destruct mm as (xm, ym).
 remember (R_frac_div xm ym) as qr eqn:Hqr .
 destruct qr as (q, rm); simpl.
 remember (R_is_neg (1 / x)) as neg eqn:Hneg .
 symmetry in Hneg.
 destruct neg.
  unfold R_div at 1.
  unfold R_is_neg, R_abs, R_is_neg.

bbb.
 Focus 2.
 unfold R_div at 1.
 remember (R_abs 1) as ax eqn:Hax .
 remember (R_abs (1 / x)) as ay eqn:Hay .
 simpl.
 remember (Z.to_nat (R_int ax + R_int ay)) as m eqn:Hm .
 unfold R_abs in Hax, Hay.
 simpl in Hax, Hay.
 subst ax.
 remember (R_div_2 1) as r1 eqn:Hr1 .
 unfold R_div_2 in Hr1; simpl in Hr1.
 unfold Z.div in Hr1; simpl in Hr1.
 remember (R_div_2 (1 / x)) as r2 eqn:Hr2 .
 remember (R_frac_equiv_div m r1 r2) as mm eqn:Hmm .
 destruct mm as (xm, ym).
 remember (R_frac_div xm ym) as qr eqn:Hqr .
 destruct qr as (q, rm); simpl.
bbb.
