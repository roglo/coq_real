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

Definition max_iter_int_part ax ay := Z.to_nat (R_int ax + R_int ay + 1).

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

(* not sure useful *)
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

(* 0: left absorbing element *)

Theorem R_div_0_l : ∀ x, (x ≠ 0)%R → (0 / x = 0)%R.
Proof.
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

(* non, c'est pas ça...
Theorem yyy : ∀ x i di m n xm ym,
  max_iter_int_part (R_abs x) (R_abs 1) = S (m + n)
  → R_frac_equiv_div (S (m + n)) (R_abs x) (R_abs 1) = (xm, ym)
  → (∀ dj, xm .[ dj] = false)
  → (R_frac x) .[ S (i + di)] = false
  → (R_frac x) .[ i] = false.
Proof.
intros x i di m n xm ym Hm Hxym Hxm Hxdi.
bbb.

revert m Hm Hxym.
induction n; intros.
 simpl in Hxym.
 rewrite andb_false_r in Hxym.
 destruct m; simpl in Hxym.
  injection Hxym; clear Hxym; intros; subst xm ym.
  unfold max_iter_int_part in Hm; simpl in Hm.
  rewrite <- Z.add_assoc, Z.add_comm in Hm.
  rewrite Z2Nat.inj_add in Hm.
   discriminate Hm.

   apply Pos2Z.is_nonneg.

   apply R_int_abs.

  rewrite andb_true_r in Hxym.
  remember (R_int (R_abs x) / 2 =? 0) as c eqn:Hc .
  symmetry in Hc.
  destruct c.
   injection Hxym; clear Hxym; intros; subst xm ym.
   simpl in Hxm.
   remember (R_is_neg x) as xn eqn:Hxn .
   symmetry in Hxn.
   destruct xn.
    pose proof (Hxm (S (S (S (i + di))))) as H; simpl in H.
    unfold R_abs in H; rewrite Hxn in H; simpl in H.
    rewrite Hxdi in H; discriminate H.

    pose proof (Hxm (S (S i))) as H; simpl in H.
    unfold R_abs in H; rewrite Hxn in H; simpl in H.
    rewrite Nat.sub_0_r in H; assumption.

bbb.
*)

Theorem I_add_i_diag : ∀ x i, I_add_i x x i = x.[S i].
Proof.
intros x i.
unfold I_add_i; simpl.
rewrite xorb_nilpotent, carry_diag, xorb_false_l.
reflexivity.
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

(*
x = (-4, 0.000…)
ax = -x = (3, 0.111…)
*)

(* non, il faut que ce soit ax = R_abs x (Leibnitz)
Theorem xxx : ∀ ax x,
  (ax = R_abs x)%R
  → R_int ax = if R_is_neg x then - R_int x - 1 else R_int x.
Proof.
intros ax x Hax.
unfold R_abs in Hax.
remember (R_is_neg x) as nx eqn:Hnx .
symmetry in Hnx.
destruct nx.
 unfold R_eq in Hax; simpl in Hax.
 destruct Hax as (Hai, Haf).
 unfold carry in Hai; simpl in Hai.
 remember (fst_same (R_frac ax) 0 0) as s1 eqn:Hs1 .
 remember (fst_same (- R_frac x) 0 0) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s1 as [dj1| ].
  destruct Hs1 as (Hn1, Ht1).
  rewrite Ht1, Z.add_0_r in Hai.
  destruct s2 as [dj2| ].
   destruct Hs2 as (Hn2, Ht2).
   rewrite Ht2, Z.add_0_r in Hai; assumption.

   exfalso.
bbb.
   pose proof (Haf dj1) as H; simpl in H.
   unfold I_add_i in H; simpl in H.
   do 2 rewrite xorb_false_r in H.
   rewrite Ht1, Hs2 in H.
   rewrite xorb_false_l, xorb_true_l in H.
   unfold carry in H; simpl in H.
   remember (fst_same (R_frac ax) 0 (S dj1)) as s3 eqn:Hs3 .
   remember (fst_same (- R_frac x) 0 (S dj1)) as s4 eqn:Hs4 .
   apply fst_same_sym_iff in Hs3; simpl in Hs3.
   apply fst_same_sym_iff in Hs4; simpl in Hs4.
   destruct s3 as [dj3| ].
    destruct Hs3 as (Hn3, Ht3).
    rewrite Ht3 in H.
    destruct s4 as [dj4| ]; [ idtac | clear H ].
     destruct Hs4 as (Hn4, Ht4).
     rewrite Hs2 in Ht4; discriminate Ht4.
bbb.
*)

Theorem Zpos_ne_0 : ∀ a, Zpos a ≠ 0.
Proof. intros a H; discriminate H. Qed.

Hint Resolve Zpos_ne_0.

(*
Theorem Znneg_div_nneg : ∀ a b, 0 < b → 0 <= a / b → 0 <= a.
Proof.
intros a b Hb Hab.
apply Zlt_gt in Hb.
pose proof (Z_div_mod_eq a b Hb) as Ha.
bbb.
   remember (Z.odd a) as c eqn:Hc .
   symmetry in Hc.
   destruct c.
    apply Zodd_bool_iff in Hc.
    apply Zodd_ex_iff in Hc.
    destruct Hc as (m, Hm).
    subst a.
    rewrite Z.add_comm, Z.mul_comm in H.
    rewrite Z.div_add in H; auto.
    simpl in H.
    eapply Zle_trans; [ eassumption | idtac ].
    rewrite <- Z.add_diag.
    rewrite <- Z.add_assoc.
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    eapply Zle_trans; [ eassumption | idtac ].
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    apply Z.le_0_1.
bbb.
*)

(*
Theorem www : ∀ x, (R_div_2 (R_abs x) = R_abs (R_div_2 x))%R.
Proof.
intros x.
unfold R_eq; simpl; intros.
split.
 f_equal.
  unfold R_abs; simpl.
  remember (R_is_neg x) as nx eqn:Hnx .
  remember (R_is_neg (R_div_2 x)) as ny eqn:Hny .
  symmetry in Hnx, Hny.
  destruct nx, ny; simpl.
   remember (R_int x mod 2) as xm2 eqn:Hxm2 .
   symmetry in Hxm2.
   destruct (Z_zerop xm2) as [H1| H1].
    subst xm2.
    rewrite <- Z.div_opp_l_z; auto.
    apply Zmod_divides in H1; auto.
    destruct H1 as (c, Hc).
    rewrite Hc, Z.mul_comm, <- Z.mul_opp_l.
    rewrite Z.div_mul; auto.
    unfold Z.sub; rewrite Z.add_comm.
    rewrite Z.div_add; auto.
    rewrite Z.add_comm; reflexivity.

    subst xm2.
    rewrite <- Z.div_opp_l_nz; auto.
    remember (R_int x) as a.
    rewrite Zmod_odd in H1.
    remember (Z.odd a) as oa eqn:Hoa .
    symmetry in Hoa.
    destruct oa; [ clear H1 | exfalso; apply H1; reflexivity ].
    apply Zodd_bool_iff, Zodd_ex_iff in Hoa.
    destruct Hoa as (m, Hm).
    rewrite Hm, Z.opp_add_distr.
    unfold Z.sub.
    rewrite <- Z.add_assoc, Z.add_comm.
    rewrite <- Z.mul_opp_r, Z.mul_comm.
    rewrite Z.div_add; auto.
    rewrite Z.add_comm; simpl.
    symmetry; rewrite Z.add_comm.
    rewrite Z.div_add; auto.
    rewrite Z.add_comm; reflexivity.

   exfalso.
   unfold R_is_neg in Hnx, Hny.
   apply Z.ltb_lt in Hnx.
   apply Z.ltb_nlt in Hny.
   apply Hny; clear Hny.
   unfold R_div_2; simpl.
   apply Z.nle_gt.
   apply Z.nle_gt in Hnx.
   intros H; apply Hnx; clear Hnx.
   remember (R_int x) as a; clear x Heqa.
bbb.
   remember (Z.odd a) as c eqn:Hc .
   symmetry in Hc.
   destruct c.
    apply Zodd_bool_iff in Hc.
    apply Zodd_ex_iff in Hc.
    destruct Hc as (m, Hm).
    subst a.
    rewrite Z.add_comm, Z.mul_comm in H.
    rewrite Z.div_add in H; auto.
    simpl in H.
    eapply Zle_trans; [ eassumption | idtac ].
    rewrite <- Z.add_diag.
    rewrite <- Z.add_assoc.
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    eapply Zle_trans; [ eassumption | idtac ].
    apply Z.le_sub_le_add_l.
    rewrite Z.sub_diag.
    apply Z.le_0_1.
bbb.
*)

(*
Theorem xxx : ∀ m x y xm1 ym1 xm2 ym2,
  R_frac_equiv_div m (R_div_2 (R_abs x)) y = (xm1, ym1)
  → R_frac_equiv_div m (R_abs (R_div_2 x)) y = (xm2, ym2)
  → (xm1 = xm2)%I.
Proof.
intros m x y xm1 ym1 xm2 ym2 Hxym1 Hxym2.
destruct m.
 simpl in Hxym1, Hxym2.
 injection Hxym1; clear Hxym1; intros; subst.
 injection Hxym2; clear Hxym2; intros; subst; reflexivity.

 simpl in Hxym1, Hxym2.
 remember (R_int y =? 0) as cy eqn:Hcy .
 symmetry in Hcy.
 destruct cy.
  rewrite andb_true_r in Hxym1, Hxym2.
  remember (R_int (R_abs x) / 2 =? 0) as cx1 eqn:Hcx1 .
  remember (R_int (R_abs (R_div_2 x)) =? 0) as cx2 eqn:Hcx2 .
  symmetry in Hcx1, Hcx2.
  destruct cx1.
   injection Hxym1; clear Hxym1; intros; subst xm1 ym1.
   apply Z.eqb_eq in Hcx1; rewrite Hcx1; simpl.
   destruct cx2.
    injection Hxym2; clear Hxym2; intros; subst xm2 ym2.
    apply Z.eqb_eq in Hcx2; rewrite Hcx2; simpl.
    unfold I_eq; intros i; simpl.
    unfold I_add_i; simpl.
    destruct i; simpl.
     unfold carry; simpl.
     remember
      (fst_same
         (I_div_2_inc
            (I_div_2_inc (R_frac (R_abs x)) (Z.odd (R_int (R_abs x)))) false)
         0 1) as s1 eqn:Hs1 .
     destruct s1 as [dj1| ].
      apply fst_same_sym_iff in Hs1; simpl in Hs1.
      destruct Hs1 as (Hn1, Ht1); rewrite Ht1.
      remember
       (fst_same (I_div_2_inc (R_frac (R_abs (R_div_2 x))) false) 0 1) as s2
       eqn:Hs2 .
      destruct s2 as [dj2| ].
       apply fst_same_sym_iff in Hs2; simpl in Hs2.
       destruct Hs2 as (Hn2, Ht2).
       rewrite Ht2; reflexivity.

       exfalso.
       apply fst_same_sym_iff in Hs2; simpl in Hs2.
       rewrite Nat.sub_0_r in Ht1.
       destruct dj1; simpl in Ht1.
        clear Hn1.
bbb.
*)

(*
Theorem yyy : ∀ x y m xm ym,
  (max_iter_int_part (R_abs x) (R_abs y) = m)%nat
  → R_frac_equiv_div m (R_abs x) (R_abs y) = (xm, ym)
  → (∀ i, xm.[i] = false)
  → (R_frac x = 0)%I.
Proof.
intros x y m xm ym Hm Hxym Hxm.
unfold max_iter_int_part in Hm.
revert x y xm ym Hxm Hm Hxym.
induction m; intros.
 exfalso; revert Hm; apply max_iter_int_part_abs_ne_0.

 simpl in Hxym.
 remember ((R_int (R_abs x) =? 0) && (R_int (R_abs y) =? 0)) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  injection Hxym; clear Hxym; intros; subst xm ym.
  simpl in Hxm.
  unfold I_eq; simpl; intros i.
  rewrite I_add_i_diag; simpl.
  unfold I_add_i; simpl.
  rewrite xorb_false_r.
  apply andb_true_iff in Hc.
  destruct Hc as (Hax, Hay).
  apply Z.eqb_eq in Hax.
  apply Z.eqb_eq in Hay.
  unfold carry; simpl.
  remember (fst_same (R_frac x) 0 (S i)) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ].
   destruct Hs1 as (Hn1, Ht1).
   rewrite Ht1, xorb_false_r.
   unfold R_abs in Hax, Hxm.
   remember (R_is_neg x) as nx eqn:Hnx .
   symmetry in Hnx.
   destruct nx.
    pose proof (Hxm (S (S (i + dj1)))) as H; simpl in H.
    rewrite Ht1 in H; discriminate H.

    pose proof (Hxm (S i)) as H; simpl in H.
    rewrite Nat.sub_0_r in H; assumption.

   unfold R_abs in Hax, Hxm.
   remember (R_is_neg x) as nx eqn:Hnx .
   symmetry in Hnx.
   destruct nx.
    pose proof (Hxm (S i)) as H; simpl in H.
    rewrite Nat.sub_0_r in H; assumption.

    pose proof (Hxm (S (S i))) as H; simpl in H.
    pose proof (Hs1 O) as HH.
    rewrite Nat.add_0_r, H in HH; discriminate HH.

bbb.
  remember Hxym as H; clear HeqH.
  remember
   (R_frac_equiv_div m (R_abs (R_div_2 x)) (R_div_2 (R_abs y))) as xym
   eqn:Hxym2 .
  symmetry in Hxym2.
  destruct xym as (xm2, ym2).
  eapply xxx in H; [ idtac | eassumption ].
bbb.

revert ax ay x y Hax Hay xm ym Hxm Hm Hxym.
induction m; intros.
 subst ax ay.
 apply Nat.le_0_r in Hm.
 exfalso; revert Hm; apply max_iter_int_part_abs_ne_0.

 simpl in Hxym.
 remember ((R_int ax =? 0) && (R_int ay =? 0)) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  subst ax ay.
  injection Hxym; clear Hxym; intros; subst xm ym.
  simpl in Hxm.
  unfold I_eq; simpl; intros i.
  rewrite I_add_i_diag; simpl.
  unfold I_add_i; simpl.
  rewrite xorb_false_r.
  apply andb_true_iff in Hc.
  destruct Hc as (Hax, Hay).
  apply Z.eqb_eq in Hax.
  apply Z.eqb_eq in Hay.
  unfold carry; simpl.
  remember (fst_same (R_frac x) 0 (S i)) as s1 eqn:Hs1 .
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct s1 as [dj1| ].
   destruct Hs1 as (Hn1, Ht1).
   rewrite Ht1, xorb_false_r.
   unfold R_abs in Hax, Hxm.
   remember (R_is_neg x) as nx eqn:Hnx .
   symmetry in Hnx.
   destruct nx.
    pose proof (Hxm (S (S (i + dj1)))) as H; simpl in H.
    rewrite Ht1 in H; discriminate H.

    pose proof (Hxm (S i)) as H; simpl in H.
    rewrite Nat.sub_0_r in H; assumption.

   unfold R_abs in Hax, Hxm.
   remember (R_is_neg x) as nx eqn:Hnx .
   symmetry in Hnx.
   destruct nx.
    pose proof (Hxm (S i)) as H; simpl in H.
    rewrite Nat.sub_0_r in H; assumption.

    pose proof (Hxm (S (S i))) as H; simpl in H.
    pose proof (Hs1 O) as HH.
    rewrite Nat.add_0_r, H in HH; discriminate HH.

  remember Hxym as H; clear HeqH.
  eapply IHm with (x := R_div_2 x) in H.
   apply R_frac_R_div_2_0; assumption.
bbb.

intros x y ax ay m xm ym Hax Hay Hm Hxym Hxm.
subst ax ay.
unfold max_iter_int_part in Hm.
destruct m.
 apply Nat.le_0_r in Hm.
 exfalso; revert Hm; apply max_iter_int_part_abs_ne_0.

 simpl in Hxym.
 remember ((R_int (R_abs x) =? 0) && (R_int (R_abs y) =? 0)) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  injection Hxym; clear Hxym; intros; subst xm ym.
  simpl in Hxm.
  unfold R_eq; simpl.
  split.
   rewrite carry_diag; simpl.
   apply andb_true_iff in Hc.
   destruct Hc as (Hax, Hay).
   apply Z.eqb_eq in Hax.
   apply Z.eqb_eq in Hay.
   unfold carry; simpl.
   remember (fst_same (R_frac x) 0 0) as s1 eqn:Hs1 .
   destruct s1 as [dj1| ].
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    destruct Hs1 as (Hn1, Ht1).
    rewrite Ht1, Z.add_0_r.
    unfold R_abs in Hax.
    remember (R_is_neg x) as nx eqn:Hnx .
    symmetry in Hnx.
    destruct nx.
bbb.
*)

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
destruct m2; simpl.
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
     rewrite <- Nat.add_1_r in Hm.
     remember O as n eqn:Hn .
     remember (R_int (R_abs x)) as u eqn:Hu .
     remember (R_div_2 (R_abs x)) as x1 eqn:Hx1 .
     remember (R_div_2 (R_abs 1)) as y1 eqn:Hy1 .
     remember 7 as Hc; clear HeqHc.
     rewrite Hu in Hxym.
     rewrite Hx1, Hy1 in Hxym; simpl in Hxym.
     rewrite andb_true_r, <- Hu in Hxym; clear Hc.
     remember (u / 2 =? 0) as c eqn:Hc ; symmetry in Hc.
     destruct c.
      injection Hxym; clear Hxym; intros; subst xm ym.
      remember (R_is_neg x) as xn eqn:Hxn; symmetry in Hxn.
      destruct xn.
       pose proof (Hs1 (S (S (S (n + i + dj2))))) as H; simpl in H; subst n.
       unfold R_abs in H; rewrite Hxn in H; simpl in H.
       rewrite Ht2 in H; discriminate H.

       pose proof (Hs1 (S (S (n + i)))) as H; simpl in H; subst n.
       unfold R_abs in H; rewrite Hxn in H; simpl in H.
       rewrite Nat.sub_0_r in H; assumption.

      rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hm.
      remember (S n) as p; subst n; rename p into n; rename Heqp into Hn.
      remember (u / 2) as p; subst u; rename p into u; rename Heqp into Hu.
      remember (R_div_2 x1) as p; subst x1.
      rename p into x1; rename Heqp into Hx1.
      remember (R_div_2 y1) as p; subst y1.
      rename p into y1; rename Heqp into Hy1.
      rewrite <- Hx1, <- Hy1 in Hxym.
      assert (x1 = R_div_2_pow (R_abs x) (S n)) as H by (subst n; auto).
      clear Hx1; rename H into Hx1.
      assert (y1 = R_div_2_pow (R_abs 1) (S n)) as H by (subst n; auto).
      clear Hy1; rename H into Hy1.
(* if test then *)
      replace 2 with (Z_two_pow n) in Hu by (subst n; reflexivity).
      assert (0 < n)%nat as Hnp by (rewrite Hn; apply Nat.lt_0_1).
      clear Hn.
      destruct m; simpl in Hxym.
       injection Hxym; clear Hxym; intros; subst xm ym.
       unfold max_iter_int_part in Hm; simpl in Hm.
       apply Z.eqb_neq in Hc.
       rewrite <- Z.add_assoc, Z.add_comm in Hm.
       rewrite Z2Nat.inj_add in Hm; [ idtac | idtac | apply R_int_abs ].
        simpl in Hm.
        destruct n; [ exfalso; revert Hnp; apply Nat.lt_irrefl | idtac ].
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
bbb.

(* end test *)
(*1*)
      destruct m; simpl in Hxym.
       injection Hxym; clear Hxym; intros; subst xm ym.
       unfold max_iter_int_part in Hm; simpl in Hm.
       apply Z.eqb_neq in Hc.
       rewrite <- Z.add_assoc, Z.add_comm in Hm.
       rewrite Z2Nat.inj_add in Hm; [ idtac | idtac | apply R_int_abs ].
        simpl in Hm; move Hn at top; subst n.
        do 2 apply eq_add_S in Hm.
        rewrite <- Z2Nat.inj_0 in Hm.
        repeat (rewrite <- Z2Nat.inj_succ in Hm; [ idtac | omega ]).
        apply Z2Nat.inj in Hm; [ idtac | apply R_int_abs | omega ].
        exfalso; subst u; rewrite Hm in Hc; apply Hc; reflexivity.

        apply Pos2Z.is_nonneg.

       rewrite Hx1, Hy1, Hn in Hxym; simpl in Hxym.
       rewrite andb_true_r, <- Hu in Hxym; clear Hc.
       remember (u / 2 =? 0) as c eqn:Hc ; symmetry in Hc.
       destruct c.
        injection Hxym; clear Hxym; intros; subst xm ym.
        remember (R_is_neg x) as xn eqn:Hxn ; symmetry in Hxn.
        destruct xn.
         pose proof (Hs1 (S (S (S (n + i + dj2))))) as H; simpl in H; subst n.
         unfold R_abs in H; rewrite Hxn in H; simpl in H.
         rewrite Ht2 in H; discriminate H.

         pose proof (Hs1 (S (S (n + i)))) as H; simpl in H; subst n.
         unfold R_abs in H; rewrite Hxn in H; simpl in H.
         rewrite Nat.sub_0_r in H; assumption.

        rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hm.
        remember (S n) as p; subst n; rename p into n; rename Heqp into Hn.
        remember (u / 2) as p; subst u; rename p into u; rename Heqp into Hu.
        remember Hx1 as H; clear HeqH; rewrite Hn in H; simpl in H.
        rewrite <- H in Hxym; clear H.
        remember Hy1 as H; clear HeqH; rewrite Hn in H; simpl in H.
        rewrite <- H in Hxym; clear H.
        remember (R_div_2 x1) as p; subst x1.
        rename p into x1; rename Heqp into Hx1.
        remember (R_div_2 y1) as p; subst y1.
        rename p into y1; rename Heqp into Hy1.
        rewrite <- R_div_2_pow_succ in Hx1, Hy1.

(*2*)
      destruct m; simpl in Hxym.
       injection Hxym; clear Hxym; intros; subst xm ym.
       unfold max_iter_int_part in Hm; simpl in Hm.
       apply Z.eqb_neq in Hc.
       rewrite <- Z.add_assoc, Z.add_comm in Hm.
       rewrite Z2Nat.inj_add in Hm; [ idtac | idtac | apply R_int_abs ].
        simpl in Hm; move Hn at top; subst n.
        do 2 apply eq_add_S in Hm.
        rewrite <- Z2Nat.inj_0 in Hm.
        repeat (rewrite <- Z2Nat.inj_succ in Hm; [ idtac | omega ]).
        apply Z2Nat.inj in Hm; [ idtac | apply R_int_abs | omega ].
        exfalso; subst u; rewrite Hm in Hc; apply Hc; reflexivity.

        apply Pos2Z.is_nonneg.

       rewrite Hx1, Hy1, Hn in Hxym; simpl in Hxym.
       rewrite andb_true_r, <- Hu in Hxym; clear Hc.
       remember (u / 2 =? 0) as c eqn:Hc ; symmetry in Hc.
       destruct c.
        injection Hxym; clear Hxym; intros; subst xm ym.
        remember (R_is_neg x) as xn eqn:Hxn ; symmetry in Hxn.
        destruct xn.
         pose proof (Hs1 (S (S (S (n + i + dj2))))) as H; simpl in H; subst n.
         unfold R_abs in H; rewrite Hxn in H; simpl in H.
         rewrite Ht2 in H; discriminate H.

         pose proof (Hs1 (S (S (n + i)))) as H; simpl in H; subst n.
         unfold R_abs in H; rewrite Hxn in H; simpl in H.
         rewrite Nat.sub_0_r in H; assumption.

        rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hm.
        remember (S n) as p; subst n; rename p into n; rename Heqp into Hn.
        remember (u / 2) as p; subst u; rename p into u; rename Heqp into Hu.
        remember Hx1 as H; clear HeqH; rewrite Hn in H; simpl in H.
        rewrite <- H in Hxym; clear H.
        remember Hy1 as H; clear HeqH; rewrite Hn in H; simpl in H.
        rewrite <- H in Hxym; clear H.
        remember (R_div_2 x1) as p; subst x1.
        rename p into x1; rename Heqp into Hx1.
        remember (R_div_2 y1) as p; subst y1.
        rename p into y1; rename Heqp into Hy1.
        rewrite <- R_div_2_pow_succ in Hx1, Hy1.

(*3*)
      destruct m; simpl in Hxym.
       injection Hxym; clear Hxym; intros; subst xm ym.
       unfold max_iter_int_part in Hm; simpl in Hm.
       apply Z.eqb_neq in Hc.
       rewrite <- Z.add_assoc, Z.add_comm in Hm.
       rewrite Z2Nat.inj_add in Hm; [ idtac | idtac | apply R_int_abs ].
        simpl in Hm; move Hn at top; subst n.
        do 2 apply eq_add_S in Hm.
        rewrite <- Z2Nat.inj_0 in Hm.
        repeat (rewrite <- Z2Nat.inj_succ in Hm; [ idtac | omega ]).
        apply Z2Nat.inj in Hm; [ idtac | apply R_int_abs | omega ].
        exfalso; subst u; rewrite Hm in Hc; apply Hc; reflexivity.

        apply Pos2Z.is_nonneg.

       rewrite Hx1, Hy1, Hn in Hxym; simpl in Hxym.
       rewrite andb_true_r, <- Hu in Hxym; clear Hc.
       remember (u / 2 =? 0) as c eqn:Hc ; symmetry in Hc.
       destruct c.
        injection Hxym; clear Hxym; intros; subst xm ym.
        remember (R_is_neg x) as xn eqn:Hxn ; symmetry in Hxn.
        destruct xn.
         pose proof (Hs1 (S (S (S (n + i + dj2))))) as H; simpl in H; subst n.
         unfold R_abs in H; rewrite Hxn in H; simpl in H.
         rewrite Ht2 in H; discriminate H.

         pose proof (Hs1 (S (S (n + i)))) as H; simpl in H; subst n.
         unfold R_abs in H; rewrite Hxn in H; simpl in H.
         rewrite Nat.sub_0_r in H; assumption.

        rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hm.
        remember (S n) as p; subst n; rename p into n; rename Heqp into Hn.
        remember (u / 2) as p; subst u; rename p into u; rename Heqp into Hu.
        remember Hx1 as H; clear HeqH; rewrite Hn in H; simpl in H.
        rewrite <- H in Hxym; clear H.
        remember Hy1 as H; clear HeqH; rewrite Hn in H; simpl in H.
        rewrite <- H in Hxym; clear H.
        remember (R_div_2 x1) as p; subst x1.
        rename p into x1; rename Heqp into Hx1.
        remember (R_div_2 y1) as p; subst y1.
        rename p into y1; rename Heqp into Hy1.
        rewrite <- R_div_2_pow_succ in Hx1, Hy1.
uuu.
*)

(* 1: right neutral element *)

Theorem R_div_1_r : ∀ x, (x / 1 = x)%R.
Proof.
intros x.
unfold R_eq; simpl.
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
