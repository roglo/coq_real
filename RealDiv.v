Require Import Utf8 QArith.
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
