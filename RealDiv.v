Require Import Utf8 QArith NPeano.
Require Import Real01Add RealAdd.

Set Implicit Arguments.

Open Scope Z_scope.

Fixpoint two_power n :=
  match n with
  | O => 1%nat
  | S n1 => (2 * two_power n1)%nat
  end.

Definition rm_mul_2 x := {| rm i := x.[S i] |}.
Arguments rm_mul_2 x%rm.

Definition rm_div_2_inc x b :=
  {| rm i := if zerop i then b else x.[i-1] |}.
Arguments rm_div_2_inc x%rm _.

Definition re_div_2 x :=
  {| re_int := re_int x / 2;
     re_frac := rm_div_2_inc (re_frac x) (Z.odd (re_int x)) |}.
Arguments re_div_2 x%R.

Fixpoint rm_equiv_div m x y :=
  match m with
  | O => (0%rm, 0%rm)
  | S m1 =>
      let x2 := re_div_2 x in
      let y2 := re_div_2 y in
      if Z.eqb (re_int x) 0 && Z.eqb (re_int y) 0 then
        (re_frac x2, re_frac y2)
      else
        rm_equiv_div m1 x2 y2
  end.
Arguments rm_equiv_div m%Z x%rm y%rm.

Definition re_is_neg x := Z.ltb (re_int x) 0.
Arguments re_is_neg x%R.

Definition re_abs x := if re_is_neg x then re_opp x else x.
Arguments re_abs x%R.

Fixpoint rm_div_eucl_i x y i :=
  match i with
  | O => if rm_lt_dec x y then (false, x) else (true, rm_sub x y)
  | S i1 =>
      let r := snd (rm_div_eucl_i x y i1) in
      let tr := rm_mul_2 r in
      if rm_lt_dec tr y then (false, tr) else (true, rm_sub tr y)
  end.
Arguments rm_div_eucl_i x%rm y%rm i%nat.

Definition rm_div_rem_i x y i := snd (rm_div_eucl_i x y i).
Arguments rm_div_rem_i x%rm y%rm i%nat.

Definition rm_div_i x y i := fst (rm_div_eucl_i (rm_mul_2 x) y i).
Arguments rm_div_i x%rm y%rm i%nat.

Definition rm_div x y := {| rm := rm_div_i x y |}.
Arguments rm_div x%rm y%rm.

Fixpoint rm_eucl_div_loop m x y :=
  match m with
  | O => (O, 0%rm)
  | S m1 =>
      if rm_lt_dec x y then (O, x)
      else
        let (q, r) := rm_eucl_div_loop m1 (rm_sub x y) y in
        (S q, r)
  end.
Arguments rm_eucl_div_loop m%nat x%rm y%rm.

Definition rm_eucl_div x y :=
  match fst_same x rm_ones 0 with
  | Some jx =>
      match fst_same y rm_ones 0 with
      | Some jy =>
          if le_dec jx jy then
            let m := two_power (S (jy - jx)) in
            let (q, r) := rm_eucl_div_loop m x y in
            (q, rm_div r y)
          else
            (O, rm_div x y)
      | None => (O, y)
      end
  | None => (O, y)
  end.
Arguments rm_eucl_div x%rm y%rm.

Definition max_iter_int_part ax ay := Z.to_nat (re_int ax + re_int ay + 1).

Definition re_div x y :=
  let ax := re_abs x in
  let ay := re_abs y in
  let m := max_iter_int_part ax ay in
  let (xm, ym) := rm_equiv_div m ax ay in
  let (q, rm) := rm_eucl_div xm ym in
  let qz := Z.of_nat q in
  {| re_int := if re_is_neg x ⊕ re_is_neg y then -qz else qz;
     re_frac := rm |}.
Arguments re_div x%R y%R.

Definition re_one := {| re_int := 1; re_frac := 0 |}.

Notation "1" := re_one : R_scope.
Notation "x / y" := (re_div x y) : R_scope.
Notation "x / y" := (rm_div x y) : rm_scope.

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

Theorem rm_div_2_0_false : (rm_div_2_inc 0 false = 0)%rm.
Proof.
unfold rm_eq; simpl; intros i.
unfold rm_add_i; simpl.
rewrite xorb_false_r, carry_diag; simpl.
remember (if zerop i then false else false) as a.
destruct a.
 destruct (zerop i); discriminate Heqa.

 rewrite xorb_false_l.
 unfold carry; simpl.
 remember (fst_same (rm_div_2_inc 0 false) 0 (S i)) as s1 eqn:Hs1 .
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

Theorem rm_mul_2_0 : (rm_mul_2 0 = 0)%rm.
Proof.
unfold rm_eq; simpl; intros i.
unfold rm_add_i; simpl.
rewrite carry_diag; simpl.
rewrite carry_diag; simpl.
reflexivity.
Qed.

Add Parametric Morphism : rm_mul_2
  with signature rm_eq ==> rm_eq
  as rm_mul_2_morph.
Proof.
intros x y Hxy.
unfold rm_eq in Hxy; simpl in Hxy.
unfold rm_eq; simpl; intros i.
pose proof (Hxy (S i)) as H.
unfold rm_add_i in H; simpl in H.
do 2 rewrite xorb_false_r in H.
unfold carry in H; simpl in H.
remember (fst_same x 0 (S (S i))) as s3 eqn:Hs3 .
remember (fst_same y 0 (S (S i))) as s4 eqn:Hs4 .
apply fst_same_sym_iff in Hs3; simpl in Hs3.
apply fst_same_sym_iff in Hs4; simpl in Hs4.
unfold rm_add_i; simpl.
do 2 rewrite xorb_false_r.
unfold carry; simpl.
remember (fst_same (rm_mul_2 x) 0 (S i)) as s1 eqn:Hs1 .
remember (fst_same (rm_mul_2 y) 0 (S i)) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1| ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1, xorb_false_r.
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [dj2| ].
  destruct Hs2 as (Hn2, Ht2).
  rewrite Ht2, xorb_false_r.
  destruct s3 as [dj3| ].
   destruct Hs3 as (Hn3, Ht3).
   rewrite Ht3, xorb_false_r in H.
   destruct s4 as [dj4| ].
    destruct Hs4 as (Hn4, Ht4).
    rewrite Ht4, xorb_false_r in H; assumption.

    rewrite Hs4 in Ht2; discriminate Ht2.

   rewrite Hs3 in Ht1; discriminate Ht1.

  destruct s3 as [dj3| ].
   destruct Hs3 as (Hn3, Ht3).
   rewrite Ht3, xorb_false_r in H.
   destruct s4 as [dj4| ]; [ idtac | assumption ].
   destruct Hs4 as (Hn4, Ht4).
   rewrite Ht4, xorb_false_r in H.
   rewrite Hs2 in Ht4; discriminate Ht4.

   rewrite xorb_true_r in H.
   destruct s4 as [dj4| ].
    destruct Hs4 as (Hn4, Ht4).
    rewrite Ht4, xorb_false_r in H; rewrite <- H.
    rewrite xorb_true_r, negb_involutive; reflexivity.

    rewrite Hs3 in Ht1; discriminate Ht1.

 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [dj2| ].
  destruct Hs2 as (Hn2, Ht2).
  rewrite Ht2, xorb_true_r, xorb_false_r.
  destruct s3 as [dj3| ].
   destruct Hs3 as (Hn3, Ht3).
   rewrite Hs1 in Ht3; discriminate Ht3.

   destruct s4 as [dj4| ].
    destruct Hs4 as (Hn4, Ht4).
    rewrite Ht4, xorb_false_r in H; assumption.

    rewrite Hs4 in Ht2; discriminate Ht2.

  destruct s3 as [dj3| ].
   destruct Hs3 as (Hn3, Ht3).
   rewrite Hs1 in Ht3; discriminate Ht3.

   destruct s4 as [dj4| ]; [ idtac | assumption ].
   destruct Hs4 as (Hn4, Ht4).
   rewrite Hs2 in Ht4; discriminate Ht4.
Qed.

Theorem fold_rm_div_rem_i : ∀ x y i,
  snd (rm_div_eucl_i x y i) = rm_div_rem_i x y i.
Proof. reflexivity. Qed.

Add Parametric Morphism : rm_div_rem_i
  with signature rm_eq ==> rm_eq ==> eq ==> rm_eq
  as rm_div_rem_i_morph.
Proof.
intros x y Hxy z t Hzt i.
induction i.
 unfold rm_div_rem_i; simpl.
 destruct (rm_lt_dec x z) as [H1| H1].
  destruct (rm_lt_dec y t) as [H2| H2]; [ assumption | idtac ].
  rewrite Hxy, Hzt in H1.
  apply rm_lt_nge in H1.
  apply rm_ge_le_iff in H2.
  contradiction.

  rewrite Hxy, Hzt in H1.
  apply rm_ge_le_iff in H1.
  destruct (rm_lt_dec y t) as [H2| H2].
   apply rm_lt_nge in H2.
   contradiction.

   simpl.
bbb.
*)

Theorem rm_div_0_l : ∀ x, (x ≠ 0)%rm → (0 / x = 0)%rm.
Proof.
intros x Hx.
unfold rm_eq; simpl; intros i.
unfold rm_add_i; simpl.
rewrite carry_diag; simpl.
rewrite xorb_false_r.
unfold rm_div_i; simpl.
unfold carry; simpl.
remember (fst_same (0 / x) 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1| ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1, xorb_false_r.
 clear dj1 Hn1 Ht1.
 destruct i; simpl.
  destruct (rm_lt_dec (rm_mul_2 0) x) as [H1| H1]; [ reflexivity | exfalso ].
  rewrite rm_mul_2_0 in H1.
  apply rm_ge_le_iff in H1.
  apply rm_le_0_r in H1; contradiction.

  remember (rm_mul_2 0) as r1.
  remember (rm_div_eucl_i r1 x i) as r2.
  remember (rm_mul_2 (snd r2)) as r3.
  destruct (rm_lt_dec r3 x) as [H1| H1]; [ reflexivity | exfalso ].
  apply rm_ge_le_iff in H1.
  subst r3 r2 r1.
  unfold rm_le in H1.
  apply H1; clear H1.
  apply rm_gt_lt_iff.
  rewrite fold_rm_div_rem_i.
bbb.
  ============================
   (rm_mul_2 (snd (rm_div_eucl_i (rm_mul_2 0) x i)) < x)%rm

  induction i; simpl.
   destruct (rm_lt_dec (rm_mul_2 0) x) as [H2| H2]; simpl.
    rewrite rm_mul_2_0; assumption.

    rewrite rm_mul_2_0 in H2.
    apply rm_ge_le_iff in H2.
    apply rm_le_0_r in H2; contradiction.

   remember (rm_mul_2 0) as r1.
   remember (rm_div_eucl_i r1 x i) as r2.
   remember (rm_mul_2 (snd r2)) as r3.
   destruct (rm_lt_dec r3 x) as [H1| H1]; [ simpl | exfalso ].
    clear H1.
    subst r1 r2.
bbb.
    exfalso; subst r3.
    apply rm_lt_nge in IHi; apply IHi; clear IHi.
bbb.

  remember (rm_mul_2 0) as r1.
  remember (rm_div_eucl_i r1 x i) as r2.
  remember (rm_mul_2 (snd r2)) as r3.
  destruct (rm_lt_dec r3 x) as [H1| H1]; [ reflexivity | exfalso ].
  apply rm_ge_le_iff in H1.
  subst r3 r2 r1.
  destruct i.
   simpl in H1.
   destruct (rm_lt_dec (rm_mul_2 0) x) as [H2| H2]; simpl in H1.
    rewrite rm_mul_2_0 in H1.
    apply rm_gt_lt_iff in H2.
    contradiction.

    rewrite rm_mul_2_0 in H2.
    apply rm_ge_le_iff in H2.
    apply rm_le_0_r in H2.
    contradiction.

   simpl in H1.
   remember (snd (rm_div_eucl_i (rm_mul_2 0) x i)) as r eqn:Hr .
   destruct (rm_lt_dec (rm_mul_2 r) x) as [H2| H2]; simpl in H1.
    destruct i.
     simpl in Hr.
     destruct (rm_lt_dec (rm_mul_2 0) x) as [H3| H3]; simpl in Hr.
      subst r.
      rewrite rm_mul_2_0 in H1.
      rewrite rm_mul_2_0 in H1.
      rewrite rm_mul_2_0 in H1.
      apply rm_le_0_r in H1; contradiction.

      rewrite rm_mul_2_0 in H3.
      apply rm_ge_le_iff in H3.
      apply rm_le_0_r in H3; contradiction.

     simpl in Hr.
bbb.

Theorem www : ∀ x, (0 / x = 0)%R.
Proof.
intros x.
unfold re_div; simpl.
remember (re_abs x) as ax eqn:Hax .
unfold re_abs; simpl.
remember (re_is_neg x) as nxp eqn:Hnxp .
symmetry in Hnxp.
remember (max_iter_int_part 0%R ax) as m eqn:Hm .
remember (rm_equiv_div m 0%R ax) as mm eqn:Hmm .
symmetry in Hmm.
destruct mm as (xm, ym).
remember (rm_eucl_div xm ym) as qrm eqn:Hqrm .
symmetry in Hqrm.
destruct qrm as (q, rm).
destruct nxp.
 unfold max_iter_int_part in Hm; simpl in Hm.
 rewrite Z.add_comm in Hm; simpl in Hm.
 remember (re_int ax) as ai eqn:Hai .
 symmetry in Hai.
 destruct ai.
  rewrite Hax in Hai; simpl in Hai.
  unfold re_abs in Hai.
  rewrite Hnxp in Hai; simpl in Hai.
  apply Z.sub_move_0_r with (m := 1) in Hai.
  apply Z.eq_opp_l in Hai; simpl in Hai.
  simpl in Hm; subst m; simpl in Hmm.
  unfold re_abs in Hax.
  rewrite Hnxp in Hax.
  subst ax; simpl in Hmm.
  rewrite Hai in Hmm; simpl in Hmm.
  injection Hmm; clear Hmm; intros; subst xm ym.
  unfold rm_eucl_div in Hqrm.
  simpl in Hqrm.
  remember (fst_same (rm_div_2_inc 0 false) rm_ones 0) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [j1| ].
   destruct Hs1 as (Hn1, Ht1).
   destruct j1; [ discriminate Ht1 | clear Ht1 ].
   clear Hn1.
   remember (rm_div_2_inc (- re_frac x) false) as z eqn:Hz .
   remember (fst_same z rm_ones 0) as s2 eqn:Hs2 .
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct s2 as [j2| ].
    destruct Hs2 as (Hn2, Ht2).
    destruct (le_dec (S j1) j2) as [H1| H1].
     remember (two_power (j2 - S j1)) as tp eqn:Htp .
     rewrite Nat.add_0_r in Hqrm.
     remember (rm_div_2_inc 0 false) as t eqn:Ht .
     remember (rm_eucl_div_loop (tp + tp) t z) as qr eqn:Hqr .
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
      destruct (rm_lt_dec t z) as [H2| H2].
       injection Hqr; clear Hqr; intros; subst q r; simpl.
bbb.

Theorem xxx : ∀ x, (x / 1 = x)%R.
Proof.
intros x.
unfold re_div; simpl.
remember (re_abs x) as ax eqn:Hax .
unfold re_abs; simpl.
remember (re_is_neg x) as nxp eqn:Hnxp .
unfold re_is_neg; simpl.
rewrite Z_nlt_1_0, xorb_false_r.
remember (max_iter_int_part ax 1%R) as m eqn:Hm .
remember (rm_equiv_div m ax 1%R) as mm eqn:Hmm .
symmetry in Hmm.
destruct mm as (xm, ym).
remember (rm_eucl_div xm ym) as qrm eqn:Hqrm .
symmetry in Hqrm.
destruct qrm as (q, rm).
destruct m.
 unfold max_iter_int_part in Hm.
 simpl in Hm.
 subst ax.
 unfold re_abs in Hm.
 rewrite <- Hnxp in Hm.
 destruct nxp.
  simpl in Hm.
  rewrite Z.add_comm in Hm.
  simpl in Hm.
  rewrite Z.add_comm in Hm.
  simpl in Hm.
  remember (- re_int x - 1) as a.
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
unfold re_div; simpl.
remember (re_abs x) as ax eqn:Hax .
remember (re_is_neg x) as nxp eqn:Hnxp .
symmetry in Hnxp.
remember (max_iter_int_part ax ax) as m eqn:Hm .
remember (rm_equiv_div m ax ax) as mm eqn:Hmm .
symmetry in Hmm.
destruct mm as (xm, ym).
remember (rm_eucl_div xm ym) as qrm eqn:Hqrm .
symmetry in Hqrm.
destruct qrm as (q, rm).
unfold re_eq.
split; [ idtac | simpl ].
 unfold re_norm.
 remember Z.add as f; simpl.
bbb.

Theorem zzz : ∀ x, (0 < x)%R → (x ≤ 1)%R → (1 / x ≥ 1)%R.
Proof.
intros x Hxgt Hxle.
unfold re_div; simpl.
remember (re_abs x) as ax eqn:Hax .
unfold re_abs; simpl.
remember (re_is_neg x) as nxp eqn:Hnxp .
symmetry in Hnxp.
destruct nxp.
 unfold re_lt in Hxgt; simpl in Hxgt.
 unfold re_is_neg in Hnxp.
 unfold Z.ltb in Hnxp.
 remember (re_int x ?= 0) as xzc eqn:Hxzc .
 symmetry in Hxzc.
 destruct xzc; try discriminate Hnxp; clear Hnxp.
 Focus 2.
 remember (max_iter_int_part 1%R ax) as m eqn:Hm .
 remember (rm_equiv_div m 1%R ax) as mm eqn:Hmm .
 symmetry in Hmm.
 destruct mm as (xm, ym).
 remember (rm_eucl_div xm ym) as qrm eqn:Hqrm .
 symmetry in Hqrm.
 destruct qrm as (q, rm).
 unfold re_ge.
bbb.

Theorem re_inv_involutive : ∀ x, (re_div 1%R (re_div 1%R x) = x)%R.
Proof.
intros x.
unfold re_eq; simpl.
split.
 unfold re_div at 1.
 remember (re_abs 1) as ax eqn:Hax .
 remember (re_abs (1 / x)) as ay eqn:Hay; simpl.
 remember (Z.to_nat (re_int ax + re_int ay)) as m eqn:Hm .
 unfold re_abs in Hax, Hay.
 simpl in Hax, Hay; subst ax.
 remember (re_div_2 1) as r1 eqn:Hr1 .
 unfold re_div_2 in Hr1; simpl in Hr1.
 unfold Z.div in Hr1; simpl in Hr1.
 remember (re_div_2 (1 / x)) as r2 eqn:Hr2 .
 remember (rm_equiv_div m r1 r2) as mm eqn:Hmm .
 destruct mm as (xm, ym).
 remember (rm_eucl_div xm ym) as qr eqn:Hqr .
 destruct qr as (q, rm); simpl.
 remember (re_is_neg (1 / x)) as neg eqn:Hneg .
 symmetry in Hneg.
 destruct neg.
  unfold re_div at 1.
  unfold re_is_neg, re_abs, re_is_neg.

bbb.
 Focus 2.
 unfold re_div at 1.
 remember (re_abs 1) as ax eqn:Hax .
 remember (re_abs (1 / x)) as ay eqn:Hay .
 simpl.
 remember (Z.to_nat (re_int ax + re_int ay)) as m eqn:Hm .
 unfold re_abs in Hax, Hay.
 simpl in Hax, Hay.
 subst ax.
 remember (re_div_2 1) as r1 eqn:Hr1 .
 unfold re_div_2 in Hr1; simpl in Hr1.
 unfold Z.div in Hr1; simpl in Hr1.
 remember (re_div_2 (1 / x)) as r2 eqn:Hr2 .
 remember (rm_equiv_div m r1 r2) as mm eqn:Hmm .
 destruct mm as (xm, ym).
 remember (rm_eucl_div xm ym) as qr eqn:Hqr .
 destruct qr as (q, rm); simpl.
bbb.
