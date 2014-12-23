(* division in ℝ *)

Require Import Utf8 QArith NPeano.
Require Import Real01Add RealAdd Real01Div.

Set Implicit Arguments.

Open Scope Z_scope.

Fixpoint two_power n :=
  match n with
  | O => 1%nat
  | S n1 => (2 * two_power n1)%nat
  end.

Definition I_div_2_inc x b :=
  {| rm i := if zerop i then b else x.[i-1] |}.
Arguments I_div_2_inc x%I _.

Definition R_div_2 x :=
  {| R_int := R_int x / 2;
     R_frac := I_div_2_inc (R_frac x) (Z.odd (R_int x)) |}.
Arguments R_div_2 x%R.

Fixpoint I_equiv_div m x y :=
  match m with
  | O => (0%I, 0%I)
  | S m1 =>
      let x2 := R_div_2 x in
      let y2 := R_div_2 y in
      if Z.eqb (R_int x) 0 && Z.eqb (R_int y) 0 then
        (R_frac x2, R_frac y2)
      else
        I_equiv_div m1 x2 y2
  end.
Arguments I_equiv_div m%Z x%I y%I.

Definition R_is_neg x := Z.ltb (R_int x) 0.
Arguments R_is_neg x%R.

Definition R_abs x := if R_is_neg x then R_opp x else x.
Arguments R_abs x%R.

Fixpoint I_eucl_div_loop m x y :=
  match m with
  | O => (O, 0%I)
  | S m1 =>
      if I_lt_dec x y then (O, x)
      else
        let (q, r) := I_eucl_div_loop m1 (I_sub x y) y in
        (S q, r)
  end.
Arguments I_eucl_div_loop m%nat x%I y%I.

Definition I_eucl_div x y :=
  match fst_same x I_ones 0 with
  | Some jx =>
      match fst_same y I_ones 0 with
      | Some jy =>
          if le_dec jx jy then
            let m := two_power (S (jy - jx)) in
            let (q, r) := I_eucl_div_loop m x y in
            (q, I_div r y)
          else
            (O, I_div x y)
      | None => (O, y)
      end
  | None => (O, y)
  end.
Arguments I_eucl_div x%I y%I.

Definition max_iter_int_part ax ay := Z.to_nat (R_int ax + R_int ay + 1).

Definition R_div x y :=
  let ax := R_abs x in
  let ay := R_abs y in
  let m := max_iter_int_part ax ay in
  let (xm, ym) := I_equiv_div m ax ay in
  let (q, rm) := I_eucl_div xm ym in
  let qz := Z.of_nat q in
  {| R_int := if R_is_neg x ⊕ R_is_neg y then -qz else qz;
     R_frac := rm |}.
Arguments R_div x%R y%R.

Definition R_one := {| R_int := 1; R_frac := 0 |}.

Notation "1" := R_one : R_scope.
Notation "x / y" := (R_div x y) : R_scope.

(* *)

Theorem Z_nlt_1_0 : (1 <? 0) = false.
Proof. reflexivity. Qed.

Theorem Pos2Nat_ne_0 : ∀ a, (Pos.to_nat a ≠ 0)%nat.
Proof.
intros a H.
pose proof Pos2Nat.is_pos a as HH.
rewrite H in HH.
revert HH; apply lt_irrefl.
Qed.

Theorem I_div_2_0_false : (I_div_2_inc 0 false = 0)%I.
Proof.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
rewrite xorb_false_r, carry_diag; simpl.
remember (if zerop i then false else false) as a.
destruct a.
 destruct (zerop i); discriminate Heqa.

 rewrite xorb_false_l.
 unfold carry; simpl.
 remember (fst_same (I_div_2_inc 0 false) 0 (S i)) as s1 eqn:Hs1 .
 destruct s1; [ reflexivity | exfalso ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 pose proof (Hs1 O); discriminate H.
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

Theorem R_div_0_l : ∀ x, (0 / x = 0)%R.
Proof.
intros x.
unfold R_div; simpl.
remember (R_abs x) as ax eqn:Hax .
unfold R_abs; simpl.
remember (R_is_neg x) as nxp eqn:Hnxp .
symmetry in Hnxp.
remember (max_iter_int_part 0%R ax) as m eqn:Hm .
remember (I_equiv_div m 0%R ax) as mm eqn:Hmm .
symmetry in Hmm.
destruct mm as (xm, ym).
remember (I_eucl_div xm ym) as qrm eqn:Hqrm .
symmetry in Hqrm.
destruct qrm as (q, rm).
destruct nxp.
bbb.
 unfold max_iter_int_part in Hm; simpl in Hm.
 rewrite Z.add_comm in Hm; simpl in Hm.
 remember (R_int ax) as ai eqn:Hai .
 symmetry in Hai.
 destruct ai.
  rewrite Hax in Hai; simpl in Hai.
  unfold R_abs in Hai.
  rewrite Hnxp in Hai; simpl in Hai.
  apply Z.sub_move_0_r with (m := 1) in Hai.
  apply Z.eq_opp_l in Hai; simpl in Hai.
  simpl in Hm; subst m; simpl in Hmm.
  unfold R_abs in Hax.
  rewrite Hnxp in Hax.
  subst ax; simpl in Hmm.
  rewrite Hai in Hmm; simpl in Hmm.
  injection Hmm; clear Hmm; intros; subst xm ym.
  unfold I_eucl_div in Hqrm.
  simpl in Hqrm.
  remember (fst_same (I_div_2_inc 0 false) I_ones 0) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [j1| ].
   destruct Hs1 as (Hn1, Ht1).
   destruct j1; [ discriminate Ht1 | clear Ht1 ].
   clear Hn1.
   remember (I_div_2_inc (- R_frac x) false) as z eqn:Hz .
   remember (fst_same z I_ones 0) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s2 as [j2| ].
    destruct Hs2 as (Hn2, Ht2).
    destruct (le_dec (S j1) j2) as [H1| H1].
     remember (two_power (j2 - S j1)) as tp eqn:Htp .
     rewrite Nat.add_0_r in Hqrm.
     remember (I_div_2_inc 0 false) as t eqn:Ht .
     remember (I_eucl_div_loop (tp + tp) t z) as qr eqn:Hqr .
     symmetry in Hqr.
     destruct qr as (q1, r).
     injection Hqrm; clear Hqrm; intros; subst q1 rm.
     remember (tp + tp)%nat as m eqn:Hm .
     destruct m.
      symmetry in Hm.
      apply Nat.eq_add_0 in Hm.
      destruct Hm as (H, _).
      subst tp.
      exfalso; revert H; apply two_power_neq_0.

      simpl in Hqr.
      destruct (I_lt_dec t z) as [H2| H2].
       injection Hqr; clear Hqr; intros; subst q r; simpl.
bbb.

Theorem xxx : ∀ x, (x / 1 = x)%R.
Proof.
intros x.
unfold R_div; simpl.
remember (R_abs x) as ax eqn:Hax .
unfold R_abs; simpl.
remember (R_is_neg x) as nxp eqn:Hnxp .
unfold R_is_neg; simpl.
rewrite Z_nlt_1_0, xorb_false_r.
remember (max_iter_int_part ax 1%R) as m eqn:Hm .
remember (I_equiv_div m ax 1%R) as mm eqn:Hmm .
symmetry in Hmm.
destruct mm as (xm, ym).
remember (I_eucl_div xm ym) as qrm eqn:Hqrm .
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
remember (I_equiv_div m ax ax) as mm eqn:Hmm .
symmetry in Hmm.
destruct mm as (xm, ym).
remember (I_eucl_div xm ym) as qrm eqn:Hqrm .
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
 remember (I_equiv_div m 1%R ax) as mm eqn:Hmm .
 symmetry in Hmm.
 destruct mm as (xm, ym).
 remember (I_eucl_div xm ym) as qrm eqn:Hqrm .
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
 remember (I_equiv_div m r1 r2) as mm eqn:Hmm .
 destruct mm as (xm, ym).
 remember (I_eucl_div xm ym) as qr eqn:Hqr .
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
 remember (I_equiv_div m r1 r2) as mm eqn:Hmm .
 destruct mm as (xm, ym).
 remember (I_eucl_div xm ym) as qr eqn:Hqr .
 destruct qr as (q, rm); simpl.
bbb.
