(* division in ℝ *)

Require Import Utf8 QArith NPeano.
Require Import Real01Add RealAdd Real01Div.

Set Implicit Arguments.

Open Scope Z_scope.

Definition I_div_2_inc x b :=
  {| rm i := if zerop i then b else x.[i-1] |}.
Arguments I_div_2_inc x%I _.

Definition R_div_2 x :=
  {| R_int := R_int x / 2;
     R_frac := I_div_2_inc (R_frac x) (Z.odd (R_int x)) |}.
Arguments R_div_2 x%R.

(*
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

Fixpoint R_div_R_int_loop m ax ay :=
  match m with
  | O => O
  | S m1 =>
       if R_lt_dec ax ay then O
       else S (R_div_R_int_loop m1 (ax - ay)%R ay)
  end.
Arguments R_div_R_int_loop m%nat ax%R ay%R.

Definition R_div_R_int ax ay :=
  R_div_R_int_loop (max_iter_int_part ax ay) ax ay.
Arguments R_div_R_int ax%R ay%R.

Definition max_iter_frac_part xm ym :=
  match fst_same xm I_ones 0 with
  | Some jx =>
      match fst_same ym I_ones 0 with
      | Some jy => two_power (max 1 (jy - jx + 1))
      | None => O
      end
  | None => O
  end.
Arguments max_iter_frac_part xm%I ym%I.

Fixpoint R_div_R_frac_loop m x y :=
  match m with
  | O => 0%I
  | S m1 =>
      if I_lt_dec x y then x
      else R_div_R_frac_loop m1 (x - y)%I y
  end.
Arguments R_div_R_frac_loop m%nat x%I y%I.

Definition R_div_R_frac ax ay :=
  let ml := max_iter_int_part ax ay in
  let (xm, ym) := R_frac_equiv_div ml ax ay in
  let m2 := max_iter_frac_part xm ym in
  if eq_nat_dec m2 O then I_zero
  else
    let rm := R_div_R_frac_loop m2 xm ym in
    I_div rm ym.
Arguments R_div_R_frac ax%I ay%I.

Definition R_div x y :=
  let ax := R_abs x in
  let ay := R_abs y in
  let q := R_div_R_int ax ay in
  let r := R_div_R_frac ax ay in
  let qz := Z.of_nat q in
  {| R_int := if R_is_neg x ⊕ R_is_neg y then -qz else qz; R_frac := r |}.
Arguments R_div x%R y%R.
*)

Definition R_div_max_iter ax ay := Z.to_nat (R_int ax + R_int ay + 1).

Fixpoint R_div_equiv m x y :=
  match m with
  | O => (I_zero, I_zero)
  | S m1 =>
      if Z.eqb (R_int x) 0 && Z.eqb (R_int y) 0 then (R_frac x, R_frac y)
      else R_div_equiv m1 (R_div_2 x) (R_div_2 y)
  end.

Definition R_div x y :=
  let ax := R_abs x in
  let ay := R_abs y in
  let (mx, my) := R_div_equiv (R_div_max_iter ax ay) ax ay in
  let (ri, rf) := I_div_lim (I_div_max_iter_int my) mx my in
  {| R_int := if R_is_neg x ⊕ R_is_neg y then - Z.of_nat ri else Z.of_nat ri;
     R_frac := rf |}.
Arguments R_div x%R y%R.

Notation "x / y" := (R_div x y) : R_scope.

(* *)

(*
Definition R_frac_equiv_div_fst x y :=
  fst (R_frac_equiv_div (max_iter_int_part x y) x y).

Theorem fold_R_frac_equiv_div_fst : ∀ x y,
  fst (R_frac_equiv_div (max_iter_int_part x y) x y) = R_frac_equiv_div_fst x y.
Proof. reflexivity. Qed.
*)

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

Theorem R_div_2_0_iff : ∀ x, (x = 0)%R ↔ (R_div_2 x = 0)%R.
Proof.
intros x.
split; intros Hx.
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

 remember Hx as H; clear HeqH.
 apply R_zero_if in H; simpl in H.
 destruct H as [(Hi, Hf)| (Hi, Hf)].
  pose proof (Hf O) as H; simpl in H.
  rewrite Zodd_even_bool in H.
  apply negb_false_iff in H.
  apply Zeven_bool_iff in H.
  apply Zeven_div2 in H.
  rewrite H, Z.mul_comm in Hi.
  rewrite Z.div_mul in Hi; [ idtac | intros I; discriminate I ].
  unfold Z.div2 in Hi; simpl in Hi.
  remember (R_int x) as xi eqn:Hxi .
  symmetry in Hxi.
  destruct xi; [ idtac | idtac | discriminate Hi ].
   unfold R_eq; simpl.
   rewrite Hxi, carry_diag; simpl.
   split.
    unfold carry; simpl.
    remember (fst_same (R_frac x) 0 0) as s1 eqn:Hs1 .
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    destruct s1 as [dj1| ]; [ idtac | exfalso ].
     destruct Hs1 as (Hn1, Ht1).
     rewrite Ht1; reflexivity.

     clear H.
     pose proof (Hf 1%nat) as H; simpl in H.
     rewrite Hs1 in H; discriminate H.

    unfold I_eq; simpl; intros i.
    unfold I_add_i; simpl.
    rewrite xorb_false_r, carry_diag; simpl.
    clear H.
    pose proof (Hf (S i)) as H; simpl in H.
    rewrite Nat.sub_0_r in H; rewrite H, xorb_false_l.
    unfold carry; simpl.
    remember (fst_same (R_frac x) 0 (S i)) as s1 eqn:Hs1 .
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    destruct s1 as [dj1| ]; [ idtac | exfalso ].
     destruct Hs1 as (Hn1, Ht1); assumption.

     clear H.
     pose proof (Hf (S (S (S i)))) as H; simpl in H.
     rewrite <- Nat.add_1_r in H; simpl in H.
     rewrite Hs1 in H; discriminate H.

   destruct p; [ discriminate Hi | discriminate Hi | discriminate H ].

  unfold R_eq; simpl.
  rewrite carry_diag; simpl.
  assert (R_frac x = 0)%I as H.
   unfold I_eq; simpl; intros i.
   unfold I_add_i; simpl.
   rewrite xorb_false_r, carry_diag; simpl.
   pose proof (Hf (S i)) as H; simpl in H.
   rewrite Nat.sub_0_r in H; rewrite H, xorb_true_l.
   apply negb_false_iff.
   clear H.
   unfold carry; simpl.
   remember (fst_same (R_frac x) 0 (S i)) as s1 eqn:Hs1 .
   destruct s1 as [dj1| ]; [ idtac | reflexivity ].
   pose proof (Hf (S (S (i + dj1)))) as H; simpl in H.
   assumption.

   split; [ idtac | assumption ].
   unfold carry; simpl.
   remember (fst_same (R_frac x) 0 0) as s1 eqn:Hs1 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct s1 as [dj1| ].
    destruct Hs1 as (Hn1, Ht1).
    rename H into Hxf.
    pose proof (Hf (S dj1)) as H; simpl in H.
    rewrite Nat.sub_0_r, Ht1 in H; discriminate H.

    pose proof (Hf O) as Ho; simpl in Ho.
    apply Zodd_bool_iff in Ho.
    apply Zodd_ex_iff in Ho.
    destruct Ho as (m, Ho).
    rewrite Ho in Hi.
    rewrite Z.add_comm, Z.mul_comm in Hi.
    rewrite Z.div_add in Hi; [ idtac | intros I; discriminate I ].
    simpl in Hi.
    subst m; simpl in Ho.
    rewrite Ho; reflexivity.
Qed.

(*
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
   apply R_div_2_0_iff with (x := x); assumption.

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
  apply R_div_2_0_iff with (x := x); assumption.
Qed.
*)

(* not sure useful
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
*)

(*
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
*)

(* 0: left absorbing element *)

Theorem zzz : ∀ x,
  (x ≠ 0)%R
  → (R_frac (0 / x) = 0)%I.
Proof.
intros x Hx.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
rewrite xorb_false_r, carry_diag; simpl.
unfold carry; simpl.
remember (fst_same (R_frac (0 / x)) 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1| ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1, xorb_false_r.
 unfold R_div; simpl.
 remember (R_div_max_iter (R_abs 0) (R_abs x)) as m eqn:Hm .
 remember (R_div_equiv m (R_abs 0) (R_abs x)) as mxy eqn:Hmxy .
 symmetry in Hmxy.
 destruct mxy as (mx, my); simpl.
 remember (I_div_max_iter_int my) as m2 eqn:Hm2 .
 symmetry in Hm2.
 remember (I_div_lim m2 mx my) as rif eqn:Hrif .
 symmetry in Hrif.
 destruct rif as (ri, rf); simpl.
 destruct m2; simpl in Hrif.
  injection Hrif; intros; subst rf; reflexivity.

  destruct (I_lt_dec mx my) as [H1| H1].
   injection Hrif; clear Hrif; intros; subst ri rf; simpl.
   remember (I_div_lt_pred_i mx my i) as bxy eqn:Hbxy .
   symmetry in Hbxy.
   destruct bxy as (b, (x1, y1)); simpl.
   destruct (I_lt_dec x1 y1) as [H2| H2]; [ reflexivity | exfalso ].
   symmetry in Hm.
   destruct m.
    simpl in Hmxy.
    injection Hmxy; clear Hmxy; intros; subst mx my.
    revert H1; apply I_lt_irrefl.

    simpl in Hmxy.
    remember (R_int (R_abs x) =? 0) as c eqn:Hc .
    symmetry in Hc.
    destruct c.
     injection Hmxy; clear Hmxy; intros; subst mx my.
bbb.

intros x m z Hx Hm Hz.
symmetry in Hm.
destruct m; simpl in Hz.
 subst z; reflexivity.

 remember (R_int (R_abs x) =? 0) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  apply Z.eqb_eq in Hc.
  remember (I_div_int_frac 0 (R_frac (R_abs x))) as zif eqn:Hzif .
  symmetry in Hzif.
  destruct zif as (zi, zf).
  subst z; simpl.
  unfold I_div_int_frac in Hzif.
  remember (I_div_max_iter_int (R_frac (R_abs x))) as m2 eqn:Hm2 .
  symmetry in Hm2.
  unfold I_div_max_iter_int in Hm2; simpl in Hm2.
  remember (fst_same (R_frac (R_abs x)) I_ones 0) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ].
   destruct Hs1 as (Hn1, Ht1).
   rewrite Nat.add_0_r in Hm2.
   destruct dj1.
    simpl in Hm2.
    clear Hn1.
    subst m2.
bbb.
  destruct m2; simpl in Hzif.
   injection Hzif; intros; subst zf; reflexivity.

   destruct (I_lt_dec 0%I (R_frac (R_abs x))) as [H1| H1].
    injection Hzif; clear Hzif; intros; subst zi zf.
    unfold I_eq; simpl; intros i.
    unfold I_add_i; simpl.
    rewrite xorb_false_r, carry_diag; simpl.
    remember (I_div_lt_pred_i 0 (R_frac (R_abs x)) i) as bxy eqn:Hbxy .
    symmetry in Hbxy.
    destruct bxy as (b, (x1, y1)); simpl.
    remember Hbxy as H; clear HeqH.
    apply I_div_lt_pred_0_l in H.
    rename H into Hx1.
    destruct (I_lt_dec x1 y1) as [H2| H2]; simpl.
     rewrite Hx1 in H2.
     unfold carry; simpl.
     remember (fst_same (I_div_lt 0 (R_frac (R_abs x))) 0 (S i)) as s1
      eqn:Hs1 .
     apply fst_same_sym_iff in Hs1; simpl in Hs1.
     destruct s1 as [dj1| ].
      destruct Hs1 as (Hn1, Ht1).
      rewrite Ht1; reflexivity.

      exfalso.
      pose proof (Hs1 O) as H.
      rewrite Nat.add_0_r in H.
      rewrite Hbxy in H; simpl in H.
      destruct (I_lt_dec x1 y1) as [H3| H3]; simpl in H.
       destruct (I_lt_dec x1 (I_div_2 y1)) as [H4| H4].
        discriminate H.

        clear H.
        rewrite Hx1 in H4.
        apply I_ge_le_iff, I_le_0_r in H4.
        apply I_div_2_eq_0 in H4.
        rewrite H4 in H2.
        revert H2; apply I_lt_irrefl.

       rewrite Hx1 in H3.
       apply I_ge_le_iff, I_le_0_r in H3.
       rewrite H3 in H2.
       revert H2; apply I_lt_irrefl.

     rewrite Hx1 in H2.
     apply I_ge_le_iff, I_le_0_r in H2.
     apply I_div_lt_pred_r_eq_0 in Hbxy; [ idtac | assumption ].
     rewrite Hbxy in H1.
     exfalso; revert H1; apply I_lt_irrefl.

    apply I_ge_le_iff, I_le_0_r in H1.
    unfold I_div_max_iter_int in Hm2.
    remember (fst_same (R_frac (R_abs x)) I_ones 0) as s1 eqn:Hs1 .
    destruct s1 as [dj1| ]; [ idtac | discriminate Hm2 ].
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    destruct Hs1 as (Hn1, Ht1).
    apply I_zero_iff in H1.
    destruct H1 as [H1| H1].
     rewrite H1 in Ht1; discriminate Ht1.

     remember
      (I_div_lim m2 (0%I - R_frac (R_abs x)) (R_frac (R_abs x))) as xif
      eqn:Hxif .
     symmetry in Hxif.
     destruct xif as (xi, xf).
     injection Hzif; clear Hzif; intros; subst zi zf.
     destruct m2.
      simpl in Hxif.
      injection Hxif; intros; subst xf; reflexivity.

      simpl in Hxif.
      destruct (I_lt_dec (0 - R_frac (R_abs x))%I (R_frac (R_abs x)))
       as [H2| H2].
       injection Hxif; clear Hxif; intros; subst xi xf.
       unfold I_eq; simpl; intros i.
       unfold I_add_i; simpl.
       rewrite xorb_false_r, carry_diag; simpl.
       remember
        (I_div_lt_pred_i (0%I - R_frac (R_abs x)) (R_frac (R_abs x)) i) as bxy2
        eqn:Hbxy2 .
       symmetry in Hbxy2.
       destruct bxy2 as (b2, (x2, y2)); simpl.
       destruct (I_lt_dec x2 y2) as [H3| H3]; simpl.
        unfold carry; simpl.
bbb.
   trop la merde : revoir les définitions...
*)

Theorem R_div_0_l : ∀ x, (x ≠ 0)%R → (0 / x = 0)%R.
Proof.
intros x Hx.
unfold R_eq; simpl.
bbb.

remember (R_div_max_iter (R_abs 0) (R_abs x)) as m eqn:Hm .
remember (R_div_equiv m (R_abs 0) (R_abs x)) as z eqn:Hz .
bbb.

intros x Hx.
unfold R_eq; simpl.
rewrite carry_diag; simpl.
split.
 unfold carry; simpl.
 remember (fst_same (R_div_R_frac (R_abs 0) (R_abs x)) 0 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [dj1| ].
  destruct Hs1 as (Hn1, Ht1).
  rewrite Ht1; simpl.
  rewrite Z.add_0_r.
  unfold R_div_R_int; simpl.
  remember (max_iter_int_part (R_abs 0) (R_abs x)) as m eqn:Hm .
  destruct m; simpl.
   destruct (R_is_neg x); reflexivity.

   symmetry in Hm.
   destruct (R_lt_dec (R_abs 0) (R_abs x)) as [H1| H1].
    destruct (R_is_neg x); reflexivity.

    rewrite R_abs_0 in H1.
    apply R_ge_le_iff in H1.
    pose proof (R_abs_nonneg x) as H.
    apply R_le_antisym in H.
    apply H in H1; clear H; symmetry in H1.
    apply R_abs_0_iff with (x := x) in H1.
    contradiction.

  pose proof (Hs1 O) as H.
  unfold R_div_R_frac in H.
  remember (max_iter_int_part (R_abs 0) (R_abs x)) as m eqn:Hm .
  symmetry in Hm.
  remember (R_frac_equiv_div m (R_abs 0) (R_abs x)) as xym eqn:Hxym .
  symmetry in Hxym.
  destruct xym as (xm, ym).
  unfold max_iter_frac_part in H.
  remember (fst_same xm I_ones 0) as s2 eqn:Hs2 .
  destruct s2 as [dj2| ]; [ idtac | discriminate H ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  pose proof R_abs_0 as Ha.
  erewrite R_frac_equiv_div_0_l in Ht2; try eassumption.
  discriminate Ht2.

 unfold R_div_R_frac.
 remember (max_iter_int_part (R_abs 0) (R_abs x)) as m eqn:Hm .
 symmetry in Hm.
 remember (R_frac_equiv_div m (R_abs 0) (R_abs x)) as xym eqn:Hxym .
 symmetry in Hxym.
 destruct xym as (xm, ym).
 unfold max_iter_frac_part.
 remember (fst_same xm I_ones 0) as s2 eqn:Hs2 .
 destruct s2 as [dj2| ]; [ idtac | reflexivity ].
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct Hs2 as (Hn2, Ht2).
 pose proof R_abs_0 as Ha.
 erewrite R_frac_equiv_div_0_l in Ht2; try eassumption.
 discriminate Ht2.
Qed.
*)

(*
Theorem R_frac_equiv_div_prop : ∀ x y m i xm ym,
  (y ≠ 0)%R
  → R_frac_equiv_div m x y = (xm, ym)
  → xm.[i] = true
  → (∀ j, ym.[j] = false)
  → False.
Proof.
intros x y m i xm ym Hy Hxy Hxm Hym.
revert x y Hy Hxy.
induction m; intros; simpl in Hxy.
 injection Hxy; clear Hxy; intros; subst xm ym.
 discriminate Hxm.

 remember ((R_int x =? 0) && (R_int y =? 0)) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  injection Hxy; clear Hxy; intros; subst xm ym.
  simpl in Hxm.
  apply andb_true_iff in Hc.
  destruct Hc as (Hx, Hyy).
  apply Z.eqb_eq in Hx.
  apply Z.eqb_eq in Hyy.
  rewrite Hx in Hxm; simpl in Hxm.
  destruct i; [ discriminate Hxm | simpl in Hxm ].
  rewrite Nat.sub_0_r in Hxm.
  rewrite Hyy in Hym; simpl in Hym.
  apply Hy.
  unfold R_eq; simpl.
  rewrite carry_diag; simpl.
  rewrite Hyy; simpl.
  split.
   unfold carry; simpl.
   remember (fst_same (R_frac y) 0 0) as s1 eqn:Hs1 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct s1 as [dj1| ].
    destruct Hs1 as (Hn1, Ht1); rewrite Ht1; reflexivity.

    pose proof (Hym 1%nat) as H; simpl in H.
    rewrite Hs1 in H; discriminate H.

   unfold I_eq; simpl; intros j.
   unfold I_add_i; simpl.
   rewrite xorb_false_r, carry_diag; simpl.
   pose proof (Hym (S j)) as H; simpl in H.
   rewrite Nat.sub_0_r in H; rewrite H, xorb_false_l.
   unfold carry; simpl.
   remember (fst_same (R_frac y) 0 (S j)) as s1 eqn:Hs1 .
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct s1 as [dj1| ]; [ idtac | exfalso ].
    destruct Hs1 as (Hn1, Hs1); assumption.

    clear H.
    pose proof (Hym (S (S (S j)))) as H; simpl in H.
    rewrite <- Nat.add_1_r in H; simpl in H.
    rewrite Hs1 in H; discriminate H.

  eapply IHm; [ idtac | eassumption ].
  apply andb_false_iff in Hc.
  intros H; apply Hy; clear Hy.
  apply R_div_2_0_iff; assumption.
Qed.

Theorem R_frac_R_div_2_0 : ∀ x,
  (R_frac (R_div_2 x) = 0)%I
  → (R_frac x = 0)%I.
Proof.
intros x Hx.
unfold I_eq in Hx; simpl in Hx.
unfold I_eq; simpl; intros i.
rewrite I_add_i_diag; simpl.
unfold I_add_i; simpl.
rewrite xorb_false_r.
unfold carry; simpl.
remember (fst_same (R_frac x) 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1| ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1, xorb_false_r.
 pose proof (Hx (S i)) as H.
 rewrite I_add_i_diag in H; simpl in H.
 unfold I_add_i in H; simpl in H.
 rewrite Nat.sub_0_r, xorb_false_r in H.
 unfold carry in H; simpl in H.
 remember (I_div_2_inc (R_frac x) (Z.odd (R_int x))) as y eqn:Hy .
 remember (fst_same y 0 (S (S i))) as s2 eqn:Hs2 ; subst y.
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [dj2| ].
  destruct Hs2 as (Hn2, Ht2).
  rewrite Ht2, xorb_false_r in H; assumption.

  rewrite Hs2 in Ht1; discriminate Ht1.

 rewrite xorb_true_r; apply negb_false_iff.
 pose proof (Hx (S i)) as H.
 rewrite I_add_i_diag in H; simpl in H.
 unfold I_add_i in H; simpl in H.
 rewrite Nat.sub_0_r, xorb_false_r in H.
 unfold carry in H; simpl in H.
 remember (I_div_2_inc (R_frac x) (Z.odd (R_int x))) as y eqn:Hy .
 remember (fst_same y 0 (S (S i))) as s2 eqn:Hs2 ; subst y.
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [dj2| ].
  destruct Hs2 as (Hn2, Ht2).
  rewrite Hs1 in Ht2; discriminate Ht2.

  rewrite xorb_true_r in H; apply negb_false_iff in H; assumption.
Qed.

Theorem Zpos_ne_0 : ∀ a, Zpos a ≠ 0.
Proof. intros a H; discriminate H. Qed.

Hint Resolve Zpos_ne_0.

Fixpoint R_div_2_pow x n :=
  match n with
  | O => x
  | S n1 => R_div_2 (R_div_2_pow x n1)
  end.

Theorem R_div_2_pow_succ : ∀ x n,
  R_div_2_pow x (S n) = R_div_2 (R_div_2_pow x n).
Proof. reflexivity. Qed.

Definition Z_two_pow n := Z.of_nat (two_power n).

Theorem two_power_succ : ∀ n, two_power (S n) = (two_power n * 2)%nat.
Proof.
intros n; simpl.
rewrite Nat.mul_succ_r.
rewrite Nat.add_0_r, Nat.mul_1_r; reflexivity.
Qed.

Theorem Z_two_pow_succ : ∀ n, Z_two_pow (S n) = Z_two_pow n * 2.
Proof.
intros n; simpl.
unfold Z_two_pow.
rewrite two_power_succ, Nat2Z.inj_mul; reflexivity.
Qed.

Theorem Z_two_pow_neq_0 : ∀ n, Z_two_pow n ≠ 0.
Proof.
intros n.
unfold Z_two_pow.
rewrite <- Nat2Z.inj_0.
intros H.
apply Nat2Z.inj in H.
revert H; apply two_power_neq_0.
Qed.

Theorem div_two_pow : ∀ n, Z.of_nat n / Z_two_pow n = 0.
Proof.
intros n.
unfold Z_two_pow.
rewrite <- div_Zdiv; [ idtac | apply two_power_neq_0 ].
rewrite <- Nat2Z.inj_0.
apply Nat2Z.inj_iff, Nat.div_small.
induction n; [ apply Nat.lt_0_1 | simpl ].
rewrite Nat.add_0_r.
rewrite <- Nat.add_1_r.
apply Nat.add_lt_le_mono; [ assumption | idtac ].
remember (two_power n) as m eqn:Hm .
symmetry in Hm.
destruct m; [ exfalso; revert Hm; apply two_power_neq_0 | idtac ].
apply le_n_S, Nat.le_0_l.
Qed.

Theorem R_int_1_div_2_pow : ∀ n,
  (0 < n)%nat
  → R_int (R_div_2_pow (R_abs 1) n) = 0.
Proof.
intros n Hn.
induction n; [ exfalso; revert Hn; apply Nat.lt_irrefl | simpl ].
destruct n; [ reflexivity | idtac ].
rewrite IHn; [ reflexivity | apply Nat.lt_0_succ ].
Qed.

Theorem R_int_div_2_pow_div : ∀ x n,
  R_int (R_div_2_pow x n) = R_int x / Z_two_pow n.
Proof.
intros x n.
induction n; [ rewrite Z.div_1_r; reflexivity | simpl ].
rewrite Z_two_pow_succ.
rewrite <- Z.div_div.
 rewrite IHn; reflexivity.

 apply Z_two_pow_neq_0.

 apply Pos2Z.is_pos.
Qed.

Theorem R_div_2_pow_shift : ∀ x n i,
  (R_frac x).[i] = (R_frac (R_div_2_pow x n)).[n + i].
Proof.
intros x n i.
induction n; [ reflexivity | simpl ].
rewrite Nat.sub_0_r; assumption.
Qed.
*)

Theorem formula_1 : ∀ x x1 y1 xm ym m i di n,
  max_iter_int_part (R_abs x) (R_abs 1) = (m + S n)%nat
  → R_int (R_abs x) / Z_two_pow n ≠ 0
  → x1 = R_div_2_pow (R_abs x) (S n)
  → y1 = R_div_2_pow (R_abs 1) (S n)
  → R_frac_equiv_div m x1 y1 = (xm, ym)
  → (∀ dj, xm .[ dj] = false)
  → (R_frac x) .[ i] = (R_frac x) .[ S (i + di)].
Proof.
intros x x1 y1 xm ym m i dj2 n.
intros Hm Hc Hx1 Hy1 Hxym Hs1.
remember ((R_frac x) .[ S (i + dj2)]) as b eqn:Ht2.
symmetry in Ht2.
remember (R_int (R_abs x) / Z_two_pow n) as u eqn:Hu .
revert x x1 y1 xm ym n u i dj2 Hm Hc Hxym Hs1 Ht2 Hu Hx1 Hy1.
induction m; intros.
 simpl in Hxym.
 injection Hxym; clear Hxym; intros; subst xm ym.
 unfold max_iter_int_part in Hm; simpl in Hm.
 rewrite <- Z.add_assoc, Z.add_comm in Hm.
 rewrite Z2Nat.inj_add in Hm; [ idtac | idtac | apply R_int_abs ].
  simpl in Hm.
  destruct n; [ discriminate Hm | idtac ].
  do 2 apply eq_add_S in Hm.
  rewrite <- Nat2Z.id in Hm.
  apply Z2Nat.inj in Hm.
   exfalso; apply Hc; rewrite Hu, Hm.
   rewrite Z_two_pow_succ.
   rewrite <- Z.div_div.
    rewrite div_two_pow; reflexivity.

    apply Z_two_pow_neq_0.

    apply Pos2Z.is_pos.

   apply R_int_abs.

   apply Nat2Z.is_nonneg.

  apply Pos2Z.is_nonneg.

 rewrite Hx1, Hy1 in Hxym; simpl in Hxym.
 do 2 rewrite R_int_div_2_pow_div in Hxym.
 rewrite <- Hu in Hxym.
 clear Hc.
 remember (u / 2 =? 0) as c eqn:Hc ; symmetry in Hc.
 rewrite Z.div_small in Hxym.
  simpl in Hxym.
  rewrite andb_true_r in Hxym.
  destruct c.
   injection Hxym; clear Hxym; intros; subst xm ym.
   remember (R_is_neg x) as xn eqn:Hxn ; symmetry in Hxn.
   destruct xn.
    Focus 1.
    destruct b.
     pose proof (Hs1 (S (S (n + i)))) as H; simpl in H.
     unfold R_abs in H; rewrite Hxn in H; simpl in H.
     rewrite Nat.sub_0_r in H.
     rewrite <- R_div_2_pow_shift in H.
     simpl in H.
     apply negb_false_iff in H; assumption.

     pose proof (Hs1 (S (S (S (n + i + dj2))))) as H; simpl in H.
     rewrite <- Nat.add_assoc, <- Nat.add_succ_r in H.
     rewrite <- R_div_2_pow_shift in H.
     unfold R_abs in H; rewrite Hxn in H; simpl in H.
     rewrite Ht2 in H; discriminate H.

    destruct b.
     pose proof (Hs1 (S (S (S (n + i + dj2))))) as H; simpl in H.
     unfold R_abs in H; rewrite Hxn in H; simpl in H.
     rewrite <- Nat.add_assoc, <- Nat.add_succ_r in H.
     rewrite <- R_div_2_pow_shift in H.
     rewrite Ht2 in H; discriminate H.

     pose proof (Hs1 (S (S (n + i)))) as H; simpl in H.
     unfold R_abs in H; rewrite Hxn in H; simpl in H.
     rewrite Nat.sub_0_r in H.
     rewrite <- R_div_2_pow_shift in H; assumption.

   apply Z.eqb_neq in Hc.
   rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hm.
   do 4 rewrite <- R_div_2_pow_succ in Hxym.
   remember (R_div_2 x1) as p; subst x1.
   rename p into x1; rename Heqp into Hx1.
   remember (R_div_2 y1) as p; subst y1.
   rename p into y1; rename Heqp into Hy1.
   rewrite <- R_div_2_pow_succ in Hx1, Hy1.
   rewrite <- Hx1, <- Hy1 in Hxym.
   remember (u / 2) as p; subst u; rename p into u; rename Heqp into Hu.
   assert (0 < 2) as H1 by apply Pos2Z.is_pos.
   pose proof (Z_two_pow_neq_0 n) as H2.
   rewrite Z.div_div in Hu; try assumption; clear H1 H2.
   rewrite <- Z_two_pow_succ in Hu.
   eapply IHm; eassumption.

  destruct n; simpl.
   unfold Z_two_pow; simpl.
   rewrite Z.div_1_r.
   split; [ apply Z.le_0_1 | apply Z.lt_1_2 ].

   rewrite Z.div_small.
    split; [ reflexivity | apply Pos2Z.is_pos ].

    split; [ apply Z.le_0_1 | idtac ].
    rewrite Z_two_pow_succ.
    rewrite Z.mul_comm.
    apply Z.lt_1_mul_pos; [ apply Z.lt_1_2 | idtac ].
    clear; induction n; [ apply Z.lt_0_1 | idtac ].
    rewrite Z_two_pow_succ.
    eapply Zlt_trans; [ eassumption | idtac ].
    apply Z.lt_mul_diag_r; [ assumption | idtac ].
    apply Z.lt_1_2.
Qed.

Theorem R_div_1_r_equiv_0 : ∀ x m xm ym i di,
  max_iter_int_part (R_abs x) (R_abs 1) = m
  → R_frac_equiv_div m (R_abs x) (R_abs 1) = (xm, ym)
  → (∀ dj, xm .[ dj] = false)
  → (R_frac x) .[ i] = (R_frac x) .[ S (i + di)].
Proof.
intros x m xm ym i dj2 Hm Hxym Hs1.
destruct m.
 exfalso; revert Hm; apply max_iter_int_part_abs_ne_0.

 simpl in Hxym.
 rewrite andb_false_r in Hxym.
 destruct m.
  injection Hxym; clear Hxym; intros; subst xm ym.
  unfold max_iter_int_part in Hm; simpl in Hm.
  rewrite <- Z.add_assoc, Z.add_comm in Hm.
  rewrite Z2Nat.inj_add in Hm; [ idtac | idtac | apply R_int_abs ].
   discriminate Hm.

   apply Pos2Z.is_nonneg.

  simpl in Hxym.
  rewrite andb_true_r in Hxym.
  remember (R_int (R_abs x)) as u eqn:Hu .
  remember (u / 2 =? 0) as c eqn:Hc ; symmetry in Hc.
  destruct c.
   injection Hxym; clear Hxym; intros; subst xm ym.
   remember (R_is_neg x) as xn eqn:Hxn ; symmetry in Hxn.
   remember (R_frac x) .[ S (i + dj2)] as b eqn:Hb .
   symmetry in Hb.
   destruct xn.
    destruct b.
     pose proof (Hs1 (S (S i))) as H; simpl in H.
     unfold R_abs in H; rewrite Hxn in H; simpl in H.
     rewrite Nat.sub_0_r in H.
     apply negb_false_iff in H; assumption.

     pose proof (Hs1 (S (S (S (i + dj2))))) as H; simpl in H.
     unfold R_abs in H; rewrite Hxn in H; simpl in H.
     rewrite Hb in H; discriminate H.

    destruct b.
     pose proof (Hs1 (S (S (S (i + dj2))))) as H; simpl in H.
     unfold R_abs in H; rewrite Hxn in H; simpl in H.
     rewrite Hb in H; discriminate H.

     pose proof (Hs1 (S (S i))) as H; simpl in H.
     unfold R_abs in H; rewrite Hxn in H; simpl in H.
     rewrite Nat.sub_0_r in H; assumption.

   do 2 rewrite <- Nat.add_1_r in Hm.
   rewrite <- Nat.add_assoc in Hm.
   eapply formula_1; try eassumption.
    rewrite <- Hu; unfold Z_two_pow; simpl.
    apply Z.eqb_neq; assumption.

    symmetry; apply R_div_2_pow_succ.

    symmetry; apply R_div_2_pow_succ.
Qed.

Theorem zzz : ∀ x, (R_div_R_frac (R_abs x) (R_abs 1) = R_frac x)%I.
Proof.
intros x.
unfold R_div_R_frac; simpl.
remember (max_iter_int_part (R_abs x) (R_abs 1)) as m eqn:Hm .
symmetry in Hm.
remember (R_frac_equiv_div m (R_abs x) (R_abs 1)) as xym eqn:Hxym .
symmetry in Hxym.
destruct xym as (xm, ym).
remember (max_iter_frac_part xm ym) as m2 eqn:Hm2 .
symmetry in Hm2; symmetry.
revert m xm ym Hm Hxym Hm2.
induction m2; intros; simpl.
 unfold max_iter_frac_part in Hm2.
 remember (fst_same xm I_ones 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [dj1| ]; [ idtac | clear Hm2 ].
  destruct Hs1 as (Hn1, Ht1).
  remember (fst_same ym I_ones 0) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s2 as [dj2| ]; [ idtac | clear Hm2 ].
   destruct Hs2 as (_, Ht2).
   exfalso; revert Hm2; apply two_power_neq_0.

   exfalso; eapply R_frac_equiv_div_prop; try eassumption.
   unfold R_abs; simpl.
   intros H; unfold R_eq in H; simpl in H.
   rewrite carry_diag in H; simpl in H.
   destruct H as (H, _); discriminate H.

  unfold I_eq; simpl; intros i.
  unfold I_add_i; simpl.
  rewrite xorb_false_r, carry_diag; simpl.
  unfold carry; simpl.
  remember (fst_same (R_frac x) 0 (S i)) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s2 as [dj2| ].
   destruct Hs2 as (_, Ht2); rewrite Ht2, xorb_false_r.
   rewrite <- Ht2.
   eapply R_div_1_r_equiv_0; eassumption.

   rewrite xorb_true_r; apply negb_false_iff.
   rewrite <- Hs2 with (dj := O).
   eapply R_div_1_r_equiv_0; eassumption.

 destruct (I_lt_dec xm ym) as [H1| H1].
bbb.
  unfold I_eq; simpl; intros i.
  unfold I_add_i; simpl.
  do 2 rewrite xorb_false_r.
  unfold carry; simpl.
  remember (fst_same (R_frac x) 0 (S i)) as s1 eqn:Hs1 .
  remember (fst_same (xm / ym) 0 (S i)) as s2 eqn:Hs2 .
  destruct s1 as [dj1| ].
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct Hs1 as (Hn1, Ht1).
   rewrite Ht1, xorb_false_r.
   destruct s2 as [dj2| ].
    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    destruct Hs2 as (Hn2, Ht2).
    rewrite Ht2, xorb_false_r.
    unfold I_div_i.
    destruct i; simpl.
     destruct (I_lt_dec (I_mul_2 xm) ym) as [H2| H2]; simpl.

bbb.
 unfold max_iter_frac_part in Hm2.
 remember (fst_same xm I_ones 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [dj1| ]; [ idtac | discriminate Hm2 ].
 destruct Hs1 as (Hn1, Ht1).
 remember (fst_same ym I_ones 0) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s2 as [dj2| ]; [ idtac | discriminate Hm2 ].
 destruct Hs2 as (Hn2, Ht2).
 destruct (I_lt_dec xm ym) as [H1| H1].
  unfold I_lt, I_compare in H1; simpl in H1.
  remember (fst_same (xm + 0%I) (- (ym + 0)%I) 0) as s3 eqn:Hs3 .
  destruct s3 as [dj3| ]; [ idtac | discriminate H1 ].
  apply fst_same_sym_iff in Hs3; simpl in Hs3.
  destruct Hs3 as (Hn3, Ht3).
  remember (I_add_i xm 0 dj3) as b eqn:Hxm .
  destruct b; [ discriminate H1 | clear H1 ].
  symmetry in Hxm.
  apply negb_sym in Ht3; simpl in Ht3.
  destruct m.
   simpl in Hxym.
   injection Hxym; clear Hxym; intros; subst xm ym.
   discriminate Ht2.

   simpl in Hxym.
   rewrite andb_false_r in Hxym; simpl in Hxym.
   destruct m.
    simpl in Hxym.
    injection Hxym; clear Hxym; intros; subst xm ym.
    discriminate Ht2.

    simpl in Hxym.
    rewrite andb_true_r in Hxym.
bbb.
*)

(* 1: right neutral element *)

Theorem R_div_1_r : ∀ x, (x / 1 = x)%R.
Proof.
intros x.
unfold R_eq; simpl.
split; [ idtac | apply zzz ].
bbb.
split.
 remember (R_div_R_frac (R_abs x) (R_abs 1)) as zm eqn:Hzm .
 unfold R_div_R_frac in Hzm.
 remember (max_iter_int_part (R_abs x) (R_abs 1)) as m eqn:Hm .
 symmetry in Hm.
 remember (R_frac_equiv_div m (R_abs x) (R_abs 1)) as xym eqn:Hxym .
 symmetry in Hxym.
 destruct xym as (xm, ym).
 unfold max_iter_frac_part in Hzm.
 remember (fst_same xm I_ones 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [dj1| ].
  destruct Hs1 as (Hn1, Ht1).
  remember (fst_same ym I_ones 0) as s2 eqn:Hs2 .
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct s2 as [dj2| ].
   remember (two_power (max 1 (dj2 - dj1 + 1))) as t eqn:Ht .
   symmetry in Ht.
   destruct t.
    exfalso; revert Ht; apply two_power_neq_0.

    simpl in Hzm.
    destruct (I_lt_dec xm ym) as [H1| H1].
     unfold carry; simpl.
     remember (fst_same zm 0 0) as s3 eqn:Hs3 .
     remember (fst_same (R_frac x) 0 0) as s4 eqn:Hs4 .
     apply fst_same_sym_iff in Hs3; simpl in Hs3.
     apply fst_same_sym_iff in Hs4; simpl in Hs4.
     destruct s3 as [dj3| ].
      destruct Hs3 as (Hn3, Ht3).
      rewrite Ht3, Z.add_0_r.
      destruct s4 as [dj4| ].
       destruct Hs4 as (Hn4, Ht4).
       rewrite Ht4, Z.add_0_r.
       unfold R_div_R_int; simpl.
       rewrite Hm.
       destruct m.
        simpl.
        exfalso; revert Hm.
        apply max_iter_int_part_abs_ne_0.

        simpl.
        destruct (R_lt_dec (R_abs x) (R_abs 1)) as [H2| H2].
         simpl in Hxym.
         rewrite andb_false_r in Hxym.
         unfold R_abs at 2 in H2; simpl in H2.
         unfold R_lt, R_compare in H2.
         remember (R_int (R_norm 1)) as a; simpl in Heqa.
         rewrite carry_diag in Heqa; simpl in Heqa.
         subst a.
         remember (R_int (R_norm (R_abs x)) ?= 1) as c eqn:Hc .
         symmetry in Hc.
         destruct c; try discriminate H2.
          simpl in H2.
          remember (fst_same (R_frac (R_abs x) + 0%I) (- (0 + 0)%I) 0) as s5
           eqn:Hs5 .
          destruct s5 as [dj5| ]; [ idtac | discriminate H2 ].
          apply fst_same_sym_iff in Hs5; simpl in Hs5.
          destruct Hs5 as (Hn5, Ht5).
          rewrite Ht5 in H2.
          unfold I_add_i in H2; simpl in H2.
          rewrite carry_diag in H2; simpl in H2.
          discriminate H2.

          clear H2.
          simpl in Hc.
          remember (R_int (R_abs x)) as axi eqn:Haxi .
          symmetry in Haxi.
          apply Z.lt_add_lt_sub_r in Hc.
bbb.

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
