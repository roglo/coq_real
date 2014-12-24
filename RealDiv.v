(* division in ℝ *)

Require Import Utf8 QArith NPeano.
Require Import Real01Add RealAdd Real01Div.

Set Implicit Arguments.

Open Scope Z_scope.

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

Definition I_equiv_div_fst m x y := fst (I_equiv_div m x y).

Theorem fold_I_equiv_div_fst : ∀ m x y,
  fst (I_equiv_div m x y) = I_equiv_div_fst m x y.
Proof. reflexivity. Qed.

Theorem b2z_inj : ∀ b1 b2, b2z b1 = b2z b2 → b1 = b2.
Proof.
intros b1 b2 H.
destruct b1, b2; try reflexivity; discriminate H.
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

Add Parametric Morphism : I_equiv_div_fst
  with signature eq ==> R_eq ==> R_eq ==> I_eq
  as I_equiv_div_fst_morph.
Proof.
intros m x y Hxy z t Hzt.
unfold I_equiv_div_fst.
destruct m; [ reflexivity | simpl ].
remember ((R_int x =? 0) && (R_int z =? 0)) as c1 eqn:Hc1 .
remember ((R_int y =? 0) && (R_int t =? 0)) as c2 eqn:Hc2 .
symmetry in Hc1, Hc2.
destruct c1; simpl.
 apply andb_true_iff in Hc1.
 destruct Hc1 as (Hx, Hz).
 apply Z.eqb_eq in Hx.
 apply Z.eqb_eq in Hz.
 rewrite Hx; simpl.
 destruct c2; simpl.
  apply andb_true_iff in Hc2.
  destruct Hc2 as (Hy, Ht).
  apply Z.eqb_eq in Hy.
  apply Z.eqb_eq in Ht.
  rewrite Hy; simpl.
  unfold I_eq; simpl; intros i.
  unfold I_add_i; simpl.
  do 2 rewrite xorb_false_r.
  destruct i; simpl.
   unfold R_eq in Hxy; simpl in Hxy.
   destruct Hxy as (Hixy, Hfxy).
   rewrite Hx, Hy in Hixy; simpl in Hixy.
   apply b2z_inj in Hixy.
   unfold carry; simpl.
   remember (fst_same (I_div_2_inc (R_frac x) false) 0 1) as s1 eqn:Hs1 .
   remember (fst_same (I_div_2_inc (R_frac y) false) 0 1) as s2 eqn:Hs2 .
   destruct s1 as [dj1| ]; simpl.
    remember Hs1 as H; clear HeqH.
    apply fst_same_sym_iff in H; simpl in H.
    destruct H as (Hn1, Ht1).
    rewrite Ht1; simpl.
    destruct s2 as [dj2| ]; [ idtac | exfalso ].
     remember Hs2 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn2, Ht2).
     rewrite Ht2; reflexivity.

     symmetry in Hs2.
     apply not_true_iff_false in Ht1; apply Ht1.
     eapply same_carry_fst_same_none; eassumption.

    remember Hs1 as H; clear HeqH.
    apply fst_same_sym_iff in H; simpl in H.
    rename H into Hn1.
    destruct s2 as [dj2| ]; [ idtac | reflexivity ].
    remember Hs2 as H; clear HeqH.
    apply fst_same_sym_iff in H; simpl in H.
    destruct H as (Hn2, Ht2).
    rewrite Ht2.
    exfalso.
    symmetry in Hs1, Hixy.
    apply not_true_iff_false in Ht2; apply Ht2.
    eapply same_carry_fst_same_none; eassumption.

   rewrite Nat.sub_0_r.
   unfold carry; simpl.
   remember (I_div_2_inc (R_frac x) false) as d1 eqn:Hd1 .
   remember (I_div_2_inc (R_frac y) false) as d2 eqn:Hd2 .
   remember (fst_same d1 0 (S (S i))) as s1 eqn:Hs1 .
   remember (fst_same d2 0 (S (S i))) as s2 eqn:Hs2 .
   subst d1 d2.
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s1 as [dj1| ].
    destruct Hs1 as (Hn1, Ht1).
    rewrite Ht1, xorb_false_r.
    destruct s2 as [dj2| ].
     destruct Hs2 as (Hn2, Ht2).
     rewrite Ht2, xorb_false_r.
bbb.

intros m x y Hxy z t Hzt.
unfold I_equiv_div_fst.
destruct m; [ reflexivity | simpl ].
remember ((R_int x =? 0) && (R_int z =? 0)) as c1 eqn:Hc1 .
remember ((R_int y =? 0) && (R_int t =? 0)) as c2 eqn:Hc2 .
symmetry in Hc1, Hc2.
destruct c1; simpl.
 apply andb_true_iff in Hc1.
 destruct Hc1 as (Hx, Hz).
 apply Z.eqb_eq in Hx.
 apply Z.eqb_eq in Hz.
 rewrite Hx; simpl.
 destruct c2; simpl.
  apply andb_true_iff in Hc2.
  destruct Hc2 as (Hy, Ht).
  apply Z.eqb_eq in Hy.
  apply Z.eqb_eq in Ht.
  rewrite Hy; simpl.
bbb.
  unfold R_eq in Hxy; simpl in Hxy.
  destruct Hxy as (Hixy, Hfxy).
  rewrite Hx, Hy in Hixy; simpl in Hixy.
  unfold carry in Hixy; simpl in Hixy.
  remember (fst_same (R_frac x) 0 0) as s1 eqn:Hs1 .
  remember (fst_same (R_frac y) 0 0) as s2 eqn:Hs2 .
  destruct s1 as [dj1| ]; simpl in Hixy.
   remember Hs1 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn1, Ht1).
   rewrite Ht1 in Hixy; simpl in Hixy.
   destruct s2 as [dj2| ]; [ idtac | discriminate Hixy ].
   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn2, Ht2).
   destruct (lt_eq_lt_dec dj1 dj2) as [[H1| H1]| H1].
    remember H1 as H; clear HeqH.
    apply Hn2 in H.
    rename H into Hy1.
    remember Hy1 as H; clear HeqH.
    symmetry in Hfxy.
    eapply I_eq_neq_if in H; try eassumption.
    destruct H as [(Hyi, Hxi)| (Hyi, Hxi)]; simpl in Hxi, Hyi.
     pose proof (Hyi (dj2 - dj1)%nat) as H.
     apply Nat.lt_le_incl in H1.
     rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
     rewrite Nat.add_comm, Nat.add_sub in H.
     rewrite Ht2 in H; discriminate H.

bbb.
   0   -  dj1  -  dj2
x  1   1   0   1   1   1   1 …
y  1   1   1   1   0   0   0 …

     pose proof (Hyi (dj2 - S dj1)%nat) as H.
     rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
     rewrite Nat.add_sub_assoc in H.
      rewrite Nat.add_comm, Nat.add_sub in H.
bbb.
rewrite Hfxy.

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

Theorem zzz : ∀ y m, (I_equiv_div_fst m 0%R y = 0)%I.
Proof.
intros y m.
revert y.
induction m; intros; [ reflexivity | simpl ].
unfold I_equiv_div_fst; simpl.
remember (R_int y =? 0) as c eqn:Hc .
symmetry in Hc.
destruct c; simpl; [ apply I_div_2_0_false | idtac ].
rewrite fold_I_equiv_div_fst.
bbb.
rewrite R_div_2_0.

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
