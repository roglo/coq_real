(* division in ℝ *)

Require Import Utf8 QArith NPeano.
Require Import Real01Add Real01Cmp RealAdd Real01Div.

Set Implicit Arguments.

Open Scope Z_scope.

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

Definition R_div_equiv_max_iter ax ay := Z.to_nat (R_int ax + R_int ay + 1).

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
  let (mx, my) := R_div_equiv (R_div_equiv_max_iter ax ay) ax ay in
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
 apply R_zero_iff in H; simpl in H.
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
 apply R_zero_iff in H; simpl in H.
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

Theorem R_div_equiv_max_iter_abs_ne_0 : ∀ x y,
   R_div_equiv_max_iter (R_abs x) (R_abs y) ≠ 0%nat.
Proof.
intros x y Hm.
unfold R_div_equiv_max_iter in Hm; simpl in Hm.
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

Theorem R_div_equiv_0_l : ∀ x y m mx my,
  R_div_equiv m x y = (mx, my)
  → (x = 0)%R
  → (mx == 0)%I.
Proof.
intros x y m mx my Hmxy Hx.
revert x y mx my Hmxy Hx.
induction m; intros.
 simpl in Hmxy.
 injection Hmxy; intros; subst mx; reflexivity.

 simpl in Hmxy.
 remember ((R_int x =? 0) && (R_int y =? 0)) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  injection Hmxy; clear Hmxy; intros; subst mx my.
  unfold R_eq in Hx.
  simpl in Hx.
  destruct Hx as (Hi, Hf).
  apply I_zero_iff2 in Hf.
  destruct Hf as [Hf| Hf]; [ assumption | idtac ].
  rewrite carry_diag in Hi; simpl in Hi.
  apply andb_true_iff in Hc.
  destruct Hc as (Hxi, Hyi).
  apply Z.eqb_eq in Hxi.
  rewrite Hxi in Hi; simpl in Hi.
  unfold carry in Hi; simpl in Hi.
  remember (fst_same (R_frac x) 0 0) as s1 eqn:Hs1 .
  destruct s1 as [dj1| ]; [ idtac | discriminate Hi ].
  rewrite Hf in Hi; discriminate Hi.

  eapply IHm; [ eassumption | idtac ].
  apply R_div_2_0_iff in Hx; assumption.
Qed.

Theorem R_frac_div_0_l : ∀ x,
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
 remember (R_div_equiv_max_iter (R_abs 0) (R_abs x)) as m eqn:Hm .
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
     remember Hbxy as H; clear HeqH.
     apply I_div_lt_pred_0_l in H; [ simpl in H | reflexivity ].
     rename H into Hx1.
     rewrite Hx1 in H2.
     apply I_ge_le_iff, I_le_0_r_eqs_iff in H2.
     apply I_div_lt_pred_r_eqs_0 in Hbxy; [ idtac | assumption ].
     rewrite Hbxy in H1.
     revert H1; apply I_lt_irrefl.

     apply R_div_equiv_0_l in Hmxy.
      remember Hbxy as H; clear HeqH.
      apply I_div_lt_pred_0_l in H; [ idtac | assumption ].
      rename H into Hx1.
      rewrite Hx1 in H2.
      apply I_ge_le_iff, I_le_0_r_eqs_iff in H2.
      apply I_div_lt_pred_r_eqs_0 in Hbxy; [ idtac | assumption ].
      rewrite Hmxy, Hbxy in H1.
      revert H1; apply I_lt_irrefl.

      unfold R_abs; simpl.
      apply R_div_2_0.

   remember Hmxy as H; clear HeqH.
   apply R_div_equiv_0_l in H; [ idtac | apply R_abs_0 ].
   rewrite H in H1; rename H into Hmx.
   apply I_ge_le_iff, I_le_0_r_eqs_iff in H1.
   unfold I_div_max_iter_int in Hm2.
   remember (fst_same my I_ones 0) as s2 eqn:Hs2 .
   destruct s2 as [dj2| ]; [ idtac | discriminate Hm2 ].
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   rewrite I_zero_eqs_iff in H1.
   rewrite H1 in Ht2; discriminate Ht2.

 pose proof (Hs1 O) as H.
 rewrite Nat.add_0_r in H.
 unfold R_div in H; simpl in H.
 remember (R_div_equiv_max_iter (R_abs 0) (R_abs x)) as m eqn:Hm .
 remember (R_div_equiv m (R_abs 0) (R_abs x)) as mxy eqn:Hmxy .
 symmetry in Hmxy.
 destruct mxy as (mx, my); simpl.
 remember (I_div_max_iter_int my) as m2 eqn:Hm2 .
 symmetry in Hm2.
 remember (I_div_lim m2 mx my) as rif eqn:Hrif .
 symmetry in Hrif.
 destruct rif as (ri, rf); simpl in H.
 rename H into Hrf.
 remember Hmxy as H; clear HeqH.
 apply R_div_equiv_0_l in H; [ idtac | apply R_abs_0 ].
 rename H into Hmx.
 destruct m2; simpl in Hrif.
  injection Hrif; clear Hrif; intros; subst ri rf.
  discriminate Hrf.

  destruct (I_lt_dec mx my) as [H1| H1].
   injection Hrif; clear Hrif; intros; subst ri rf; simpl.
   rewrite Hmx in H1.
   unfold I_div_lt in Hrf; simpl in Hrf.
   remember (I_div_lt_pred_i mx my i) as bxy eqn:Hbxy .
   symmetry in Hbxy.
   destruct bxy as (b, (x1, y1)); simpl in Hrf.
   destruct (I_lt_dec x1 y1) as [H2| H2]; simpl in Hrf.
    remember Hbxy as H; clear HeqH.
    apply I_div_lt_pred_0_l in H; [ idtac | assumption ].
    rewrite H in H2; rename H into Hx1.
    destruct (I_lt_dec x1 (I_div_2 y1)) as [H3| H3].
     discriminate Hrf.

     rewrite Hx1 in H3.
     apply I_ge_le_iff, I_le_0_r_eqs_iff in H3.
     apply I_div_2_eqs_0 in H3.
     rewrite H3 in H2.
     exfalso; revert H2; apply I_lt_irrefl.

    destruct (I_lt_dec (x1 - y1)%I (I_div_2 y1)) as [H3| H3].
     discriminate Hrf.

     remember Hbxy as H; clear HeqH.
     apply I_div_lt_pred_0_l in H; [ idtac | assumption ].
     rewrite H in H2; rename H into Hx1.
     apply I_ge_le_iff, I_le_0_r_eqs_iff in H2.
     apply I_div_lt_pred_r_eqs_0 in Hbxy; [ idtac | assumption ].
     rewrite Hbxy in H1.
     exfalso; revert H1; apply I_lt_irrefl.

   rewrite Hmx in H1.
   apply I_ge_le_iff, I_le_0_r_eqs_iff in H1.
   unfold I_div_max_iter_int in Hm2; simpl in Hm2.
   remember (fst_same my I_ones 0) as s2 eqn:Hs2 .
   destruct s2 as [dj2| ]; [ idtac | discriminate Hm2 ].
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   rewrite I_zero_eqs_iff in H1.
   rewrite H1 in Ht2; discriminate Ht2.
Qed.

Theorem R_frac_R_abs_0 : ∀ x, (R_frac (R_abs x) == 0)%I → (R_frac x = 0)%I.
Proof.
intros x Hx.
apply I_zero_iff.
rewrite I_zero_eqs_iff in Hx.
unfold R_abs in Hx; simpl in Hx.
remember (R_is_neg x) as nx eqn:Hnx .
symmetry in Hnx.
destruct nx; simpl in Hx.
 right; intros i; apply negb_false_iff, Hx.

 left; intros i; apply Hx.
Qed.

Definition Z_two_pow n := Z.of_nat (two_power n).

Fixpoint R_div_2_pow x n :=
  match n with
  | O => x
  | S n1 => R_div_2 (R_div_2_pow x n1)
  end.

Theorem Z_div_two_pow : ∀ n, Z.of_nat n / Z_two_pow n = 0.
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

Theorem Nat_le_lt_power : ∀ a b,
  a ≤ b
  → (a < two_power b)%nat.
Proof.
intros a b Hab.
revert a Hab.
induction b; intros; simpl.
 apply Nat.le_0_r in Hab; subst a.
 apply Nat.lt_0_1.

 rewrite Nat.add_0_r.
 destruct a.
  clear.
  apply Nat.add_pos_l.
  induction b; [ apply Nat.lt_0_1 | simpl ].
  rewrite Nat.add_0_r.
  apply Nat.add_pos_l; assumption.

  apply le_S_n in Hab.
  apply IHb in Hab.
  apply lt_n_S in Hab.
  eapply Nat.lt_le_trans; [ eassumption | idtac ].
  rewrite <- Nat.add_1_r.
  apply Nat.add_le_mono_l.
  clear.
  induction b; [ apply Nat.lt_0_1 | simpl ].
  rewrite Nat.add_0_r.
  apply Nat.add_pos_l; assumption.
Qed.

(* attempt to group formula_1, _2, _3 together... *)
Theorem formula_42 : ∀ x y x1 y1 xm ym m n,
  R_div_equiv_max_iter (R_abs x) (R_abs y) = (m + S n)%nat
  → x1 = R_div_2_pow (R_abs x) (S n)
  → y1 = R_div_2_pow (R_abs y) (S n)
  → R_div_equiv m x1 y1 = (xm, ym)
  → (ym == 0)%I
  → R_int (R_abs y) / Z_two_pow n = 0.
Proof.
intros x y x1 y1 xm ym m n Hm Hx1 Hy1 Hxym Hym.
revert x y x1 y1 xm ym n Hm Hx1 Hy1 Hxym Hym.
induction m; intros; simpl in Hxym.
 injection Hxym; clear Hxym; intros; subst xm ym.
 apply Z.div_small.
 split; [ apply R_int_abs | idtac ].
 unfold R_div_equiv_max_iter in Hm; simpl in Hm.
 rewrite Z2Nat.inj_add in Hm.
  simpl in Hm.
  unfold Pos.to_nat in Hm; simpl in Hm.
  rewrite Nat.add_comm in Hm.
  simpl in Hm.
  apply eq_add_S in Hm.
  rewrite Z2Nat.inj_add in Hm; try apply R_int_abs.
  unfold Z_two_pow.
  apply Z.gt_lt.
  rewrite <- Z2Nat.id.
   apply Z.lt_gt.
   apply Nat2Z.inj_lt.
   apply Nat_le_lt_power.
   rewrite <- Hm.
   apply Nat.le_sub_le_add_r.
   rewrite Nat.sub_diag.
   apply Nat.le_0_l.

   apply R_int_abs.

  apply Z.add_nonneg_nonneg; apply R_int_abs.

  apply Z.le_0_1.

 remember ((R_int x1 =? 0) && (R_int y1 =? 0)) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  apply andb_true_iff in Hc.
  destruct Hc as (Hxi, Hyi).
  apply Z.eqb_eq in Hxi.
  apply Z.eqb_eq in Hyi.
  rewrite <- R_int_div_2_pow_div.
  rewrite Hy1 in Hyi; simpl in Hyi.
  apply Z.div_small_iff in Hyi.
   destruct Hyi as [Hyi| Hyi].
    remember (R_int (R_div_2_pow (R_abs y) n)) as yi eqn:Hy .
    symmetry in Hy.
    destruct (Z_eq_dec yi 1) as [H1| H1].
     rewrite H1 in Hy.
     injection Hxym; clear Hxym; intros; subst xm ym.
     rewrite Hy1 in Hym; simpl in Hym.
     rewrite Hy in Hym; simpl in Hym.
     rewrite I_zero_eqs_iff in Hym.
     simpl in Hym.
     pose proof (Hym O) as H; discriminate H.

     revert Hyi H1; clear; intros; omega.

    destruct Hyi as (H1, H2).
    eapply Z.lt_le_trans in H1; [ idtac | eassumption ].
    apply Z.nle_gt in H1.
    exfalso; apply H1, Z.le_0_2.

   intros H; discriminate H.

  apply andb_false_iff in Hc.
  destruct Hc as [Hc| Hc].
   apply Z.eqb_neq in Hc.
   exfalso; apply Hc; clear Hc.
   rewrite Hx1; simpl.
   rewrite R_int_div_2_pow_div; simpl.
Abort. (* failed: probably wrong hypotheses
bbb.
*)

Theorem formula_1 : ∀ y x1 y1 xm ym m n,
  R_div_equiv_max_iter (R_abs 0) (R_abs y) = (m + S n)%nat
  → x1 = R_div_2_pow (R_abs 0) (S n)
  → y1 = R_div_2_pow (R_abs y) (S n)
  → R_div_equiv m x1 y1 = (xm, ym)
  → (ym == 0)%I
  → R_int (R_abs y) / Z_two_pow n = 0.
Proof.
intros y x1 y1 xm ym m n.
intros Hm Hx1 Hy1 Hxym Hym.
revert y x1 y1 xm ym n Hm Hx1 Hy1 Hxym Hym.
induction m; intros.
 unfold R_div_equiv_max_iter in Hm.
 simpl in Hm.
 rewrite Z2Nat.inj_add in Hm.
  simpl in Hm.
  unfold Pos.to_nat in Hm; simpl in Hm.
  apply Nat.add_sub_eq_r in Hm; simpl in Hm.
  rewrite Nat.sub_0_r in Hm.
  symmetry in Hm.
  rewrite <- Nat2Z.id in Hm.
  apply Z2Nat.inj in Hm.
   rewrite Hm.
   apply Z_div_two_pow.

   apply R_int_abs.

   apply Nat2Z.is_nonneg.

  apply R_int_abs.

  apply Z.le_0_1.

 simpl in Hxym.
 remember ((R_int x1 =? 0) && (R_int y1 =? 0)) as c1 eqn:Hc1 .
 symmetry in Hc1.
 destruct c1.
  injection Hxym; clear Hxym; intros; subst xm ym.
  apply andb_true_iff in Hc1.
  destruct Hc1 as (Hxi, Hyi).
  apply Z.eqb_eq in Hxi.
  apply Z.eqb_eq in Hyi.
  rewrite <- R_int_div_2_pow_div.
  rewrite Hy1 in Hyi; simpl in Hyi.
  apply Z.div_small_iff in Hyi.
   destruct Hyi as [Hyi| Hyi].
    remember (R_int (R_div_2_pow (R_abs y) n)) as yi eqn:Hy .
    symmetry in Hy.
    destruct (Z_eq_dec yi 1) as [H1| H1].
     rewrite H1 in Hy.
     rewrite Hy1 in Hym; simpl in Hym.
     rewrite Hy in Hym; simpl in Hym.
     rewrite I_zero_eqs_iff in Hym.
     simpl in Hym.
     pose proof (Hym O) as H; discriminate H.

     revert Hyi H1; clear; intros; omega.

    destruct Hyi as (H1, H2).
    eapply Z.lt_le_trans in H1; [ idtac | eassumption ].
    apply Z.nle_gt in H1.
    exfalso; apply H1, Z.le_0_2.

   intros H; discriminate H.

  apply andb_false_iff in Hc1.
  destruct Hc1 as [Hc1| Hc1].
   apply Z.eqb_neq in Hc1.
   exfalso; apply Hc1; clear Hc1.
   rewrite Hx1; simpl.
   rewrite R_int_div_2_pow_div; simpl.
   rewrite Z.div_0_l; [ reflexivity | idtac ].
   intros H; discriminate H.

   apply Z.eqb_neq in Hc1.
   exfalso; apply Hc1; rewrite Hy1, R_int_div_2_pow_div.
   rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hm.
   eapply IHm; try eassumption.
    rewrite Hx1; reflexivity.

    rewrite Hy1; reflexivity.
Qed.

Theorem formula_2 : ∀ x x1 y1 xm ym m n,
  R_div_equiv_max_iter (R_abs x) (R_abs 1) = (m + S n)%nat
  → x1 = R_div_2_pow (R_abs x) (S n)
  → y1 = R_div_2_pow (R_abs 1) (S n)
  → R_div_equiv m x1 y1 = (xm, ym)
  → (ym == 0)%I
  → R_int (R_abs x) / Z_two_pow n = 0.
Proof.
intros x x1 y1 xm ym m n Hm Hx1 Hy1 Hxym Hym.
revert x x1 y1 xm ym n Hm Hx1 Hy1 Hxym Hym.
induction m; intros; simpl in Hxym.
 injection Hxym; clear Hxym; intros; subst xm ym.
 simpl in Hm.
 unfold R_div_equiv_max_iter in Hm; simpl in Hm.
 rewrite <- Z.add_assoc in Hm; simpl in Hm.
 rewrite Z2Nat.inj_add in Hm.
  simpl in Hm.
  unfold Pos.to_nat in Hm; simpl in Hm.
  rewrite Nat.add_comm in Hm.
  simpl in Hm.
  apply eq_add_S in Hm.
  destruct n; [ discriminate Hm | idtac ].
  rewrite Z_two_pow_succ.
  apply eq_add_S in Hm.
  rewrite <- Nat2Z.id in Hm.
  apply Z2Nat.inj in Hm.
   rewrite Hm.
   rewrite <- Z.div_div.
    rewrite Z_div_two_pow; reflexivity.

    apply Z_two_pow_neq_0.

    apply Z.lt_0_2.

   apply R_int_abs.

   apply Nat2Z.is_nonneg.

  apply R_int_abs.

  apply Z.le_0_2.

 remember ((R_int x1 =? 0) && (R_int y1 =? 0)) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  injection Hxym; clear Hxym; intros; subst xm ym.
  rewrite I_zero_eqs_iff in Hym.
  pose proof (Hym n) as H; simpl in H.
  rewrite Hy1 in H.
  exfalso; revert H; clear; intros.
  induction n; [ discriminate H | idtac ].
  remember (S n) as sn; simpl in H; subst sn.
  remember (zerop (S n)) as x; simpl in Heqx; subst x.
  rewrite Nat.sub_succ, Nat.sub_0_r in H.
  apply IHn; assumption.

  apply andb_false_iff in Hc.
  destruct Hc as [Hc| Hc].
   apply Z.eqb_neq in Hc.
   exfalso; apply Hc; rewrite Hx1, R_int_div_2_pow_div.
   rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hm.
   eapply IHm; try eassumption; try (subst x1 y1; reflexivity).

   apply Z.eqb_neq in Hc.
   exfalso; apply Hc; clear Hc.
   rewrite Hy1; simpl.
   rewrite R_int_div_2_pow_div; simpl.
   rewrite Z.div_div; [ idtac | apply Z_two_pow_neq_0 | apply Z.lt_0_2 ].
   rewrite Z.mul_comm.
   rewrite <- Z.div_div; [ reflexivity | intros H; discriminate H | idtac ].
   clear; unfold Z_two_pow.
   induction n; [ apply Z.lt_0_1 | simpl ].
   rewrite Nat.add_0_r.
   eapply Z.lt_le_trans; [ eassumption | idtac ].
   apply Nat2Z.inj_le.
   apply Nat.le_add_r.
Qed.

Theorem formula_3 : ∀ x x1 xm m n,
  R_div_equiv_max_iter (R_abs x) (R_abs x) = (m + S n)%nat
  → x1 = R_div_2_pow (R_abs x) (S n)
  → R_div_equiv m x1 x1 = (xm, xm)
  → (xm == 0)%I
  → R_int (R_abs x) / Z_two_pow n = 0.
Proof.
intros x x1 xm m n Hm Hx1 Hx1m Hxm.
revert x x1 xm n Hm Hx1 Hx1m Hxm.
induction m; intros.
 simpl in Hm.
 apply Z.div_small.
 split; [ apply R_int_abs | idtac ].
 unfold R_div_equiv_max_iter in Hm; simpl in Hm.
 rewrite Z2Nat.inj_add in Hm.
  simpl in Hm.
  unfold Pos.to_nat in Hm; simpl in Hm.
  rewrite Nat.add_comm in Hm.
  simpl in Hm.
  apply eq_add_S in Hm.
  rewrite Z2Nat.inj_add in Hm; try apply R_int_abs.
  unfold Z_two_pow.
  apply Z.gt_lt.
  rewrite <- Z2Nat.id.
   apply Z.lt_gt.
   apply Nat2Z.inj_lt.
   apply Nat_le_lt_power.
   rewrite <- Hm.
   apply Nat.le_sub_le_add_r.
   rewrite Nat.sub_diag.
   apply Nat.le_0_l.

   apply R_int_abs.

  apply Z.add_nonneg_nonneg; apply R_int_abs.

  apply Z.le_0_1.

 simpl in Hx1m.
 rewrite andb_diag in Hx1m.
 remember (R_int x1 =? 0) as c eqn:Hc .
 symmetry in Hc.
 destruct c.
  apply Z.eqb_eq in Hc.
  injection Hx1m; clear Hx1m; intros; subst xm; clear H0.
  rewrite <- R_int_div_2_pow_div.
  rewrite I_zero_eqs_iff in Hxm; simpl in Hxm.
  assert (x1 = 0)%R as H.
   apply R_zero_iff.
   left; split; assumption.

   rewrite Hx1 in H; simpl in H.
   apply R_div_2_0_iff in H.
   apply R_zero_iff in H.
   destruct H as [(H1, H2)| (H1, H2)]; [ assumption | exfalso ].
   rewrite Hx1 in Hxm; simpl in Hxm.
   pose proof (Hxm 1%nat) as H; simpl in H.
   rewrite H2 in H; discriminate H.

  apply Z.eqb_neq in Hc.
  exfalso; apply Hc; rewrite Hx1, R_int_div_2_pow_div.
  rewrite Nat.add_succ_l, <- Nat.add_succ_r in Hm.
  eapply IHm; try eassumption.
  rewrite Hx1; reflexivity.
Qed.

Theorem R_int_div_0_l : ∀ x,
  (x ≠ 0)%R
  → R_int (0 / x) = 0.
Proof.
intros x Hx.
unfold R_div; simpl.
remember (R_div_equiv_max_iter (R_abs 0) (R_abs x)) as m eqn:Hm .
remember (R_div_equiv m (R_abs 0) (R_abs x)) as mxy eqn:Hmxy .
symmetry in Hmxy.
destruct mxy as (mx, my); simpl.
remember (I_div_max_iter_int my) as m2 eqn:Hm2 .
symmetry in Hm2.
remember (I_div_lim m2 mx my) as rif eqn:Hrif .
symmetry in Hrif.
destruct rif as (ri, rf); simpl.
destruct m2; simpl in Hrif.
 injection Hrif; intros; subst ri.
 destruct (R_is_neg x); reflexivity.

 destruct (I_lt_dec mx my) as [H1| H1].
  injection Hrif; clear Hrif; intros; subst ri rf; simpl.
  destruct (R_is_neg x); reflexivity.

  remember Hmxy as H; clear HeqH.
  apply R_div_equiv_0_l in H; [ idtac | apply R_abs_0 ].
  rename H into Hmx.
  rewrite Hmx in H1.
  apply I_ge_le_iff, I_le_0_r_eqs_iff in H1.
  symmetry in Hm.
  destruct m.
   exfalso; revert Hm; apply R_div_equiv_max_iter_abs_ne_0.

   simpl in Hmxy.
   remember (R_int (R_abs x) =? 0) as c eqn:Hc .
   symmetry in Hc.
   destruct c.
    injection Hmxy; clear Hmxy; intros; subst mx my.
    clear Hmx.
    exfalso; apply Hx.
    unfold R_eq; simpl.
    apply Z.eqb_eq in Hc.
    remember H1 as H; clear HeqH.
    apply R_frac_R_abs_0 in H.
    rename H into Hfx.
    split; [ idtac | assumption ].
    rewrite carry_diag; simpl.
    unfold carry; simpl.
    remember (fst_same (R_frac x) 0 0) as s1 eqn:Hs1 .
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    destruct s1 as [dj1| ].
     destruct Hs1 as (Hn1, Ht1).
     rewrite Ht1, Z.add_0_r.
     unfold R_abs in Hc; simpl in Hc.
     remember (R_is_neg x) as nx eqn:Hnx .
     symmetry in Hnx.
     destruct nx; [ exfalso | assumption ].
     apply I_zero_iff in Hfx.
     destruct Hfx as [Hfx| Hfx].
      rewrite I_zero_eqs_iff in H1.
      unfold R_abs in H1.
      rewrite Hnx in H1; simpl in H1.
      pose proof (H1 O) as H.
      rewrite Hfx in H; discriminate H.

      rewrite Hfx in Ht1; discriminate Ht1.

     unfold R_abs in Hc; simpl in Hc.
     remember (R_is_neg x) as nx eqn:Hnx .
     symmetry in Hnx.
     destruct nx; simpl in Hc; simpl.
      apply Z.sub_move_0_l in Hc.
      rewrite Z.opp_involutive in Hc.
      rewrite <- Hc; reflexivity.

      unfold R_abs in H1.
      rewrite Hnx in H1; simpl in H1.
      rewrite I_zero_eqs_iff in H1.
      pose proof (H1 O) as H.
      rewrite Hs1 in H; discriminate H.

    apply Z.eqb_neq in Hc.
    rewrite <- Nat.add_1_r in Hm.
    eapply formula_1 in Hmxy; try eassumption; try reflexivity.
    unfold Z_two_pow in Hmxy; simpl in Hmxy.
    rewrite Z.div_1_r in Hmxy; contradiction.
Qed.

Theorem R_div_0_l : ∀ x, (x ≠ 0)%R → (0 / x = 0)%R.
Proof.
intros x Hx.
unfold R_eq; simpl.
split; [ idtac | apply R_frac_div_0_l; assumption ].
rewrite carry_diag; simpl.
unfold carry; simpl.
remember (fst_same (R_frac (0 / x)) 0 0) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1| ]; simpl.
 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1; simpl.
 rewrite Z.add_0_r.
 apply R_int_div_0_l; assumption.

 exfalso.
 pose proof (Hs1 O) as H.
 unfold R_div in H; simpl in H.
 remember (R_div_equiv_max_iter (R_abs 0) (R_abs x)) as m eqn:Hm .
 symmetry in Hm.
 remember (R_div_equiv m (R_abs 0) (R_abs x)) as xym eqn:Hxym .
 symmetry in Hxym.
 destruct xym as (xm, ym); simpl in H.
 remember Hxym as H1; clear HeqH1.
 apply R_div_equiv_0_l in H1; [ idtac | reflexivity ].
 rename H1 into Hxm.
 remember (I_div_max_iter_int ym) as m2 eqn:Hm2 .
 symmetry in Hm2.
 remember (I_div_lim m2 xm ym) as rif eqn:Hrif .
 symmetry in Hrif.
 destruct rif as (ri, rf); simpl in H; simpl.
 destruct m.
  revert Hm; apply R_div_equiv_max_iter_abs_ne_0.

  simpl in Hxym.
  remember (R_int (R_abs x) =? 0) as c eqn:Hc .
  symmetry in Hc.
  destruct c.
   apply Z.eqb_eq in Hc.
   injection Hxym; clear Hxym; intros; subst xm ym.
   clear Hxm.
   destruct m2.
    simpl in Hrif.
    injection Hrif; intros; subst rf; discriminate H.

    simpl in Hrif.
    destruct (I_lt_dec 0%I (R_frac (R_abs x))) as [H1| H1].
     injection Hrif; clear Hrif; intros; subst ri rf.
     simpl in H.
     destruct (I_lt_dec 0%I (I_div_2 (R_frac (R_abs x)))) as [H2| H2].
      discriminate H.

      clear H.
      apply I_ge_le_iff, I_le_0_r_eqs_iff in H2.
      apply I_div_2_eqs_0 in H2.
      rewrite H2 in H1.
      revert H1; apply I_lt_irrefl.

     apply I_ge_le_iff, I_le_0_r_eqs_iff in H1.
     apply Hx, R_zero_iff.
     unfold R_abs in Hc; simpl in Hc.
     remember (R_is_neg x) as nx eqn:Hnx .
     symmetry in Hnx.
     rewrite I_zero_eqs_iff in H1.
     clear H.
     destruct nx; simpl in Hc; [ right | left ].
      apply Z.sub_move_0_l in Hc.
      rewrite Z.opp_involutive in Hc.
      split; [ rewrite <- Hc; reflexivity | intros i ].
      pose proof (H1 i) as H; simpl in H.
      unfold R_abs in H; simpl in H.
      rewrite Hnx in H; simpl in H.
      apply negb_false_iff in H; assumption.

      split; [ rewrite <- Hc; reflexivity | intros i ].
      pose proof (H1 i) as H; simpl in H.
      unfold R_abs in H; simpl in H.
      rewrite Hnx in H; simpl in H; assumption.

   apply Z.eqb_neq in Hc.
   destruct m2; simpl in Hrif.
    injection Hrif; intros; subst rf; discriminate H.

    destruct (I_lt_dec xm ym) as [H1| H1].
     rewrite Hxm in H1.
     injection Hrif; clear Hrif; intros; subst ri rf.
     simpl in H.
     destruct (I_lt_dec xm (I_div_2 ym)) as [H2| H2].
      discriminate H.

      clear H.
      rewrite Hxm in H2.
      apply I_ge_le_iff, I_le_0_r_eqs_iff in H2.
      apply I_div_2_eqs_0 in H2.
      rewrite H2 in H1.
      revert H1; apply I_lt_irrefl.

     rewrite Hxm in H1.
     apply I_ge_le_iff, I_le_0_r_eqs_iff in H1.
     rename H into Hrf.
     remember Hxym as H; clear HeqH.
     rewrite <- Nat.add_1_r in Hm.
     eapply formula_1 in H; try eassumption; try reflexivity.
     apply Z.div_small_iff in H; [ idtac | apply Z_two_pow_neq_0 ].
     unfold Z_two_pow in H; simpl in H.
     destruct H as [(H2, H3)| (H2, H3)]; omega.
Qed.

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

Theorem R_div_2_pow_succ : ∀ x n,
  R_div_2_pow x (S n) = R_div_2 (R_div_2_pow x n).
Proof. reflexivity. Qed.

Theorem R_int_1_div_2_pow : ∀ n,
  (0 < n)%nat
  → R_int (R_div_2_pow (R_abs 1) n) = 0.
Proof.
intros n Hn.
induction n; [ exfalso; revert Hn; apply Nat.lt_irrefl | simpl ].
destruct n; [ reflexivity | idtac ].
rewrite IHn; [ reflexivity | apply Nat.lt_0_succ ].
Qed.

Theorem R_div_2_pow_shift : ∀ x n i,
  (R_frac x).[i] = (R_frac (R_div_2_pow x n)).[n + i].
Proof.
intros x n i.
induction n; [ reflexivity | simpl ].
rewrite Nat.sub_0_r; assumption.
Qed.
*)

(*
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
*)

(*
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

Theorem I_eql_eqs : ∀ x y, x = y → (x == y)%I.
Proof. intros; subst; reflexivity. Qed.

Theorem I_div_2_inc_0 : ∀ x y b,
  y = I_div_2_inc x b
  → y .[ 0] = b.
Proof. intros; subst; reflexivity. Qed.

Theorem I_div_2_inc_1 : ∀ x y b,
  y = I_div_2_inc x b
  → y.[1] = x.[0].
Proof. intros; subst; reflexivity. Qed.

Theorem I_div_2_inc_iff : ∀ x y b,
  (y == I_div_2_inc x b)%I
  ↔ y.[0] = b ∧ ∀ i, y.[S i] = x.[i].
Proof.
intros x y b.
split; intros Hy.
 unfold I_eqs, I_compare in Hy; simpl in Hy.
 remember (fst_same y (- I_div_2_inc x b) 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [j1| ]; [ idtac | clear Hy ].
  destruct Hs1 as (Hn1, Ht1).
  destruct (y .[ j1]); discriminate Hy.

  pose proof (Hs1 O) as H; simpl in H.
  rewrite negb_involutive in H.
  split; [ assumption | intros i ].
  pose proof (Hs1 (S i)) as Hi; simpl in Hi.
  rewrite negb_involutive, Nat.sub_0_r in Hi.
  assumption.

 destruct Hy as (Hy, Hyx).
 unfold I_eqs, I_compare; simpl.
 remember (fst_same y (- I_div_2_inc x b) 0) as s1 eqn:Hs1 .
 destruct s1 as [j1| ]; [ exfalso | reflexivity ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Ht1).
 destruct j1; simpl in Ht1.
  rewrite Ht1 in Hy.
  revert Hy; apply no_fixpoint_negb.

  rewrite Nat.sub_0_r in Ht1.
  rewrite Hyx in Ht1; symmetry in Ht1.
  revert Ht1; apply no_fixpoint_negb.
Qed.

(* proof x/x = 1 *)

Theorem R_div_equiv_diag : ∀ m x, ∃ y, R_div_equiv m x x = (y, y).
Proof.
intros m x.
revert x.
induction m; intros; simpl.
 exists 0%I; reflexivity.

 rewrite andb_diag.
 remember (R_int x =? 0) as c eqn:Hc .
 symmetry in Hc.
 destruct c; simpl; [ idtac | apply IHm ].
 exists (R_frac x); reflexivity.
Qed.

Theorem R_div_frac_diag_i  : ∀ x,
  (x ≠ 0)%R
  → ∀ i, R_frac (x / x) .[ i] = false.
Proof.
intros x Hx i.
unfold R_div; simpl.
remember (R_div_equiv_max_iter (R_abs x) (R_abs x)) as m eqn:Hm .
symmetry in Hm.
remember (R_div_equiv m (R_abs x) (R_abs x)) as xym eqn:Hxym .
pose proof (R_div_equiv_diag m (R_abs x)) as H.
destruct H as (mx, Hmx).
rewrite <- Hxym in Hmx.
move Hmx at top; subst xym.
symmetry in Hxym.
remember (I_div_max_iter_int mx) as m2 eqn:Hm2 .
symmetry in Hm2.
remember (I_div_lim m2 mx mx) as rif eqn:Hrif .
symmetry in Hrif.
destruct rif as (ri, rf); simpl.
clear Hxym.
revert ri rf mx Hm2 Hrif.
induction m2; intros; simpl in Hrif.
 injection Hrif; intros; subst rf; reflexivity.

 destruct (I_lt_dec mx mx) as [H1| H1].
  exfalso; revert H1; apply I_lt_irrefl.

  remember (I_div_lim m2 (mx - mx) mx) as rif2 eqn:Hrif2 .
  symmetry in Hrif2.
  destruct rif2 as (ri2, rf2).
  injection Hrif; clear Hrif; intros; subst ri rf.
  clear IHm2 H1.
  destruct m2; simpl in Hrif2.
   injection Hrif2; intros; subst rf2; reflexivity.

   destruct (I_lt_dec (mx - mx)%I mx) as [H1| H1].
    rewrite I_sub_diag_eqs in H1.
    injection Hrif2; clear Hrif2; intros; subst ri2 rf2; simpl.
    remember (I_div_lt_pred_i (mx - mx) mx i) as bxy eqn:Hbxy .
    symmetry in Hbxy.
    destruct bxy as (b1, (x1, y1)); simpl.
    destruct (I_lt_dec x1 y1) as [H2| H2]; [ reflexivity | exfalso ].
    remember Hbxy as H; clear HeqH.
    apply I_div_lt_pred_0_l in H.
     rewrite H in H2.
     apply I_ge_le_iff, I_le_0_r_eqs_iff in H2.
     rename H into Hx1.
     apply I_div_lt_pred_r_eqs_0 in Hbxy; [ idtac | assumption ].
     rewrite Hbxy in H1; revert H1; apply I_lt_irrefl.

     apply I_sub_diag_eqs.

    rewrite I_sub_diag_eqs in H1.
    rewrite I_ge_le_iff, I_le_0_r_eqs_iff in H1.
    unfold I_div_max_iter_int in Hm2; simpl in Hm2.
    remember (fst_same mx I_ones 0) as s2 eqn:Hs2 .
    destruct s2 as [j2| ]; [ idtac | discriminate Hm2 ].
    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    destruct Hs2 as (Hn2, Ht2).
    rewrite I_zero_eqs_iff in H1.
    rewrite H1 in Ht2; discriminate Ht2.
Qed.

Theorem R_div_frac_diag : ∀ x, (x ≠ 0)%R → (R_frac (x / x) = 0)%I.
Proof.
intros x Hx.
unfold I_eq; simpl; intros i.
rewrite I_add_i_diag; simpl.
unfold I_add_i; simpl.
rewrite xorb_false_r.
unfold carry; simpl.
remember (fst_same (R_frac (x / x)) 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1| ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1, xorb_false_r.
 apply R_div_frac_diag_i; assumption.

 pose proof (Hs1 O) as H.
 rewrite R_div_frac_diag_i in H; [ discriminate H | assumption ].
Qed.

Theorem R_div_int_diag : ∀ x,
  (x ≠ 0)%R
  → R_int (x / x) = 1.
Proof.
intros x Hx.
unfold R_div; simpl.
remember (R_div_equiv_max_iter (R_abs x) (R_abs x)) as m eqn:Hm .
symmetry in Hm.
remember (R_div_equiv m (R_abs x) (R_abs x)) as xym eqn:Hxym .
pose proof (R_div_equiv_diag m (R_abs x)) as H.
destruct H as (mx, Hmx).
rewrite <- Hxym in Hmx.
move Hmx at top; subst xym.
symmetry in Hxym.
remember (I_div_max_iter_int mx) as m2 eqn:Hm2 .
symmetry in Hm2.
remember (I_div_lim m2 mx mx) as rif eqn:Hrif .
symmetry in Hrif.
destruct rif as (ri, rf); simpl.
rewrite xorb_nilpotent.
rewrite <- Z2Nat.id; [ idtac | apply Z.le_0_1 ].
f_equal; simpl; unfold Pos.to_nat; simpl.
revert ri rf mx Hm2 Hrif Hxym.
induction m2; intros; simpl in Hrif.
 unfold I_div_max_iter_int in Hm2; simpl in Hm2.
 remember (fst_same mx I_ones 0) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct s1 as [dj1| ]; [ idtac | clear Hm2 ].
  rewrite Nat.add_0_r in Hm2.
  remember (two_power dj1) as n eqn:Hn .
  symmetry in Hn.
  destruct n; [ idtac | discriminate Hm2 ].
  exfalso; revert Hn; apply two_power_neq_0.

  apply I_zero_eqs_iff in Hs1.
  destruct m.
   exfalso; revert Hm; apply R_div_equiv_max_iter_abs_ne_0.

   simpl in Hxym.
   rewrite andb_diag in Hxym.
   remember (R_int (R_abs x) =? 0) as c eqn:Hc .
   symmetry in Hc.
   destruct c.
    injection Hxym; clear Hxym; intros.
    clear H0; subst mx.
    apply Z.eqb_eq in Hc.
    exfalso; apply Hx.
    apply R_zero_iff.
    unfold R_abs in Hc, Hs1.
    remember (R_is_neg x) as nx eqn:Hnx .
    symmetry in Hnx.
    destruct nx; simpl in Hc, Hs1.
     right.
     apply Z.sub_move_l in Hc.
     rewrite Z.opp_involutive in Hc; simpl in Hc.
     symmetry in Hc.
     split; [ assumption | intros i ].
     rewrite I_zero_eqs_iff in Hs1; simpl in Hs1.
     apply negb_false_iff, Hs1.

     left.
     split; [ assumption | intros i ].
     rewrite I_zero_eqs_iff in Hs1; simpl in Hs1.
     apply Hs1.

    apply Z.eqb_neq in Hc.
    destruct m.
     unfold R_div_equiv_max_iter in Hm.
     exfalso; apply Hc; clear Hc.
     rewrite <- Nat2Z.id in Hm.
     apply Z2Nat.inj in Hm.
      simpl in Hm.
      apply Z.add_move_r in Hm; simpl in Hm.
      rewrite Z.add_diag in Hm.
      apply Z.eq_mul_0 in Hm.
      destruct Hm as [Hm| Hm]; [ discriminate Hm | assumption ].

      apply Z.add_nonneg_nonneg; [ idtac | apply Z.le_0_1 ].
      apply Z.add_nonneg_nonneg; apply R_int_abs.

      apply Z.le_0_1.

     remember Hxym as H; clear HeqH.
     exfalso.
     rewrite <- Nat.add_1_r in Hm.
     eapply formula_3 in H; try eassumption; [ idtac | reflexivity ].
     unfold Z_two_pow in H; simpl in H.
     rewrite Z.div_1_r in H; contradiction.

 destruct (I_lt_dec mx mx) as [H1| H1].
  exfalso; revert H1; apply I_lt_irrefl.

  remember (I_div_lim m2 (mx - mx) mx) as xif eqn:Hxif .
  symmetry in Hxif.
  destruct xif as (xi, xf).
  injection Hrif; clear Hrif; intros; subst ri rf; f_equal.
  destruct m2.
   simpl in Hxif.
   injection Hxif; intros; subst xi; reflexivity.

   simpl in Hxif.
   clear H1.
   destruct (I_lt_dec (mx - mx)%I mx) as [H1| H1].
    injection Hxif; intros; subst xi; reflexivity.

    remember (I_div_lim m2 ((mx - mx)%I - mx) mx) as xif2 eqn:Hxif2 .
    symmetry in Hxif2.
    destruct xif2 as (xi2, xf2).
    injection Hxif; clear Hxif; intros; subst xi xf.
    rewrite I_sub_diag_eqs in H1.
    apply I_ge_le_iff, I_le_0_r_eqs_iff in H1.
    unfold I_div_max_iter_int in Hm2.
    remember (fst_same mx I_ones 0) as s1 eqn:Hs1 .
    destruct s1 as [dj1| ]; [ idtac | discriminate Hm2 ].
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    destruct Hs1 as (Hn1, Ht1).
    rewrite I_zero_eqs_iff in H1.
    rewrite H1 in Ht1; discriminate Ht1.
Qed.

Theorem R_div_diag : ∀ x, (x ≠ 0)%R → (x / x = 1)%R.
Proof.
intros x Hx.
unfold R_eq; simpl.
rewrite carry_diag; simpl.
split; [ idtac | apply R_div_frac_diag; assumption ].
unfold carry; simpl.
remember (fst_same (R_frac (x / x)) 0 0) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1| ].
 Focus 2.
 pose proof (Hs1 O) as H.
 rewrite R_div_frac_diag_i in H; [ discriminate H | assumption ].

 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1, Z.add_0_r.
 apply R_div_int_diag; assumption.
Qed.

(* *)

Theorem xxx : ∀ x y,
  (x < I_div_2 (x / y))%I
  → y.[0] = false.
Proof.
intros x y Hxy.
unfold I_lt, I_compare in Hxy; simpl in Hxy.
remember (fst_same x (- I_div_2 (x / y)) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate Hxy ].
remember (x .[ dj1]) as b eqn:Hxj1 .
destruct b; [ discriminate Hxy | clear Hxy ].
symmetry in Hxj1.
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
destruct dj1; simpl in Ht1.
 rewrite Ht1 in Hxj1; discriminate Hxj1.

 rewrite Nat.sub_0_r, Hxj1 in Ht1.
 apply negb_sym in Ht1; simpl in Ht1.
 unfold I_div in Ht1; simpl in Ht1.
 remember (I_div_max_iter_int y) as m eqn:Hm .
 symmetry in Hm.
 destruct m; [ discriminate Ht1 | idtac ].
 simpl in Ht1.
 destruct (I_lt_dec x y) as [H1| H1].
  simpl in Ht1.
  remember (I_div_lt_pred_i x y dj1) as bxy1 eqn:Hb1 .
  symmetry in Hb1.
  destruct bxy1 as (b1, (x1, y1)); simpl in Ht1.
  destruct (I_lt_dec x1 y1) as [H2| H2].
   discriminate Ht1.

   clear Ht1.
   destruct dj1.
    simpl in Hb1.
    injection Hb1; clear Hb1; intros; subst b1 x1 y1.
    pose proof (Hn1 O Nat.lt_0_1) as H; simpl in H.
    rename H into Hx0.
    clear Hn1.
    unfold I_ge, I_compare in H2.
    remember (fst_same x (- I_div_2 y) 0) as s2 eqn:Hs2 .
    destruct s2 as [dj2| ]; [ idtac | clear H2 ].
     remember (x .[ dj2]) as b eqn:Hxj2 .
     destruct b; [ clear H2 | exfalso; apply H2; reflexivity ].
     symmetry in Hxj2.
     apply fst_same_sym_iff in Hs2; simpl in Hs2.
     destruct Hs2 as (Hn2, Ht2).
     destruct dj2; [ rewrite Hxj2 in Hx0; discriminate Hx0 | idtac ].
     simpl in Ht2.
     rewrite Nat.sub_0_r in Ht2.
     destruct dj2.
      rewrite Hxj2 in Ht2.
      apply negb_sym in Ht2; assumption.

      assert (1 < S (S dj2))%nat as H by omega.
      apply Hn2 in H; simpl in H.
      rewrite Hxj1, negb_involutive in H.
      symmetry; assumption.

     apply fst_same_sym_iff in Hs2; simpl in Hs2.
     pose proof (Hs2 1%nat) as H; simpl in H.
     rewrite Hxj1, negb_involutive in H.
     symmetry; assumption.
bbb.

Theorem yyy : ∀ x y z,
  (x < y)%I
  → (z ≠≠ 0)%I
  → (x / y == z)%I
  → (x / z == y)%I.
Proof.
intros x y z Hxy Hz Hxyz.
remember Hxyz as Hxdyz; clear HeqHxdyz.
rewrite I_eqs_iff in Hxyz.
apply I_eqs_iff; intros i.
induction i.
 pose proof (Hxyz O) as H.
 unfold I_div in H; simpl in H.
 remember (I_div_max_iter_int y) as m eqn:Hm .
 symmetry in Hm.
 destruct m.
  unfold I_div_max_iter_int in Hm.
  remember (fst_same y I_ones 0) as s1 eqn:Hs1 .
  destruct s1 as [dj1| ]; [ idtac | clear Hm ].
   exfalso; revert Hm; apply two_power_neq_0.

   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply I_zero_eqs_iff in Hs1.
   rewrite Hs1 in Hxy.
   exfalso; revert Hxy; apply I_nlt_0_r.

  simpl in H.
  destruct (I_lt_dec x y) as [H1| H1].
   remember I_div_lt as f; simpl in H; subst f.
   unfold I_lt, I_compare in H1; simpl in H1.
   remember (fst_same x (- y) 0) as s1 eqn:Hs1 .
   destruct s1 as [dj1| ]; [ idtac | discriminate H1 ].
   remember (x .[ dj1]) as b eqn:Hxj1 .
   destruct b; [ discriminate H1 | clear H1 ].
   symmetry in Hxj1.
   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   destruct Hs1 as (Hn1, Ht1).
   rewrite Hxj1 in Ht1; apply negb_sym in Ht1; simpl in Ht1.
   rename Ht1 into Hyj1.
   symmetry in H.
   simpl in H.
   destruct (I_lt_dec x (I_div_2 y)) as [H1| H1]; simpl in H.
    unfold I_div; simpl.
    remember (I_div_max_iter_int z) as m2 eqn:Hm2 .
    symmetry in Hm2.
    destruct m2; simpl.
     symmetry.
     unfold I_div_max_iter_int in Hm2; simpl in Hm2.
     remember (fst_same z I_ones 0) as s2 eqn:Hs2 .
     destruct s2 as [dj2| ]; [ idtac | clear Hm2 ].
      rewrite Nat.add_0_r in Hm2.
      apply Nat.eq_add_0 in Hm2.
      exfalso; destruct Hm2 as (Hm2, _); revert Hm2; apply two_power_neq_0.

      apply fst_same_sym_iff in Hs2; simpl in Hs2.
      apply I_zero_eqs_iff in Hs2; contradiction.

     destruct (I_lt_dec x z) as [H2| H2].
      simpl.
      destruct (I_lt_dec x (I_div_2 z)) as [H3| H3]; simpl.
       rename H into Hz0.
       rewrite <- Hxdyz in H3.
bbb.
  H3 : (x < I_div_2 (x / y))%I
  should imply y < 1/2

       unfold I_lt, I_compare in H3; simpl in H3.
       remember (fst_same x (- I_div_2 (x / y)) 0) as s2 eqn:Hs2 .
       destruct s2 as [dj2| ]; [ idtac | discriminate H3 ].
       remember (x .[ dj2]) as b eqn:Hxj2 .
       destruct b; [ discriminate H3 | clear H3 ].
       symmetry in Hxj2.
       apply fst_same_sym_iff in Hs2; simpl in Hs2.
       destruct Hs2 as (Hn2, Ht2).
       destruct dj2; simpl in Ht2.
        rewrite Ht2 in Hxj2; discriminate Hxj2.

        rewrite Nat.sub_0_r, Hxj2 in Ht2.
        apply negb_sym in Ht2; simpl in Ht2.
        unfold I_div in Ht2; simpl in Ht2.
        rewrite Hm in Ht2; simpl in Ht2.
        destruct (I_lt_dec x y) as [H3| H3].
         clear H3.
         simpl in Ht2.
         remember (I_div_lt_pred_i x y dj2) as bxy2 eqn:Hbxy2 .
         symmetry in Hbxy2.
         destruct bxy2 as (b2, (x2, y2)); simpl in Ht2.
         destruct (I_lt_dec x2 y2) as [H3| H3]; [ idtac | clear Ht2 ].
          discriminate Ht2.

          destruct dj2.
           simpl in Hbxy2.
           injection Hbxy2; clear Hbxy2; intros; subst b2 x2 y2.
           apply I_lt_nge in H1.
           apply I_ge_le_iff in H3.
           contradiction.

           simpl in Hbxy2.
           remember (I_div_lt_pred_i x y dj2) as bxy3 eqn:Hbxy3 .
           symmetry in Hbxy3.
           destruct bxy3 as (b3, (x3, y3)); simpl in Hbxy2.
           destruct (I_lt_dec x3 y3) as [H4| H4].
            injection Hbxy2; clear Hbxy2; intros; subst b2 x2 y2.
bbb.

0 < x < y
z=x/y

x₀ x₁ x₂ …       | 0 y₀ y₁ y₂ …
                 ------------------------
                 | z₀ z₁ z₂ …

j tel que x_j=y_{j-1} et x_i≠y_{i-1} pour i < j
si x_j=1 alors x>y sinon x<y
si j=∞ alors x=y

0 u₀ u₁ … xj …       | 0 u₀ u₁ … yj₁ …
                      ------------------------
                     | z₀ z₁ z₂ …

1/ j=0

1 x₁ x₂              | 0 y₀ y₁ y₂
                      ------------------------
                     | z₀ z₁ z₂ …
Donc z₀=1

1 x₁ x₂              | 0 y₀ y₁ y₂
                      ------------------------
                     | 1 z₁ z₂ …

Mais rappelons-nous que x<y et donc comme x₀=1 alors il faut que y₀=1

1 x₁ x₂              | 0 1 y₁ y₂
                      ------------------------
                     | 1 z₁ z₂ …

Si on inverse y et z

- Mmmm... est-ce que x<z, d'abord ?
- z = x/y = x*(1/y)    1<1/y     x<x*1/y    x<z   oui


1 x₁ x₂              | 0 1 z₁ z₂ …
                      ------------------------
                     | 1 y₁ y₂ ?

ouais, ça marche, la première bimale est bien 1=y₀

2/ j>0

0 u₀ u₁ … xj …       | 0 u₀ u₁ … yj₁ …
                      ------------------------
                     | z₀ z₁ z₂ …


2a/ xj=1 et yj₁=0; alors z₀=1

0 u₀ u₁ … 1 …       | 0 u₀ u₁ … 0 …
                      ------------------------
                    | 1 z₁ z₂ …

Divisons x par z

0 u₀ u₁ … 1 …       | 0 1 z₁ z₂ …
                      ------------------------
                    | u₀ u₁ … 0 … ?

On a bien u₀ comme première bimale

Mmmm... bon. Si on arrive à prouver que la première bimale de la
division de x par z est bien y₀, comment on continue ?

y = y₀/2 + 0.0y₁y₂y₃…

x / y = x / (y₀/2 + 0.0y₁y₂y₃) = ???

Deux cas y₀=0 et y₁=1

y₀=0   x / y = x / 0.0y₁y₂y₃…
   on peut multiplier x par 2 (x₀ est forcément nul puisque x<y)
   et on est ramené à 0.x₁x₂x₃…/0.y₁y₂y₃… et ça devrait marcher
   par récurrence

y₀=1   x / y = x / 0.1y₁y₂y₃ … = z
       x / z = 0.1 …

Theorem zzz : ∀ x y z, (y ≠ 0)%R → (z ≠ 0)%R → (x / y = z)%R → (x / z = y)%R.
Proof.
intros x y z Hy Hz Hxyz.
unfold R_eq; simpl.
unfold R_eq in Hxyz; simpl in Hxyz.
destruct Hxyz as (Hixy, Hfxy).
apply I_sub_move_0_r in Hfxy.
apply I_zero_iff in Hfxy; simpl in Hfxy.
destruct Hfxy as [Hfxy| Hfxy].
 split.
  Focus 2.
  unfold I_eq; simpl; intros i.
  pose proof (Hfxy i) as H.
  unfold I_add_i in H; simpl in H.
  unfold I_add_i; simpl.
  do 2 rewrite xorb_false_r.
bbb.
  Reflexion to do, indeed, with that method of using I_sub_move_0_r
  and I_zero_iff in case of (x = y)%I in other theorems...

(* *)

Theorem R_frac_div_1_r : ∀ x, (R_frac (x / 1) = R_frac x)%I.
Proof.
intros x.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
do 2 rewrite xorb_false_r.
unfold carry; simpl.
remember (fst_same (R_frac x) 0 (S i)) as s1 eqn:Hs1 .
remember (fst_same (R_frac (x / 1)) 0 (S i)) as s2 eqn:Hs2 .
destruct s1 as [dj1| ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1, xorb_false_r.
 destruct s2 as [dj2| ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  rewrite Ht2, xorb_false_r.
  unfold R_div; simpl.
  unfold R_div in Ht2; simpl.
  remember (R_div_equiv_max_iter (R_abs x) (R_abs 1)) as m eqn:Hm .
  symmetry in Hm.
  remember (R_div_equiv m (R_abs x) (R_abs 1)) as xym eqn:Hxym .
  symmetry in Hxym.
  destruct xym as (xm, ym).
  remember (I_div_max_iter_int ym) as m2 eqn:Hm2 .
  symmetry in Hm2.
  remember (I_div_lim m2 xm ym) as rif eqn:Hrif .
  symmetry in Hrif.
  destruct rif as (ri, rf); simpl in Ht2; simpl.
  destruct m2.
   simpl in Hrif.
   injection Hrif; clear Hrif; intros; subst ri rf.
   clear Ht2; simpl.
   destruct m.
    exfalso; revert Hm; apply R_div_equiv_max_iter_abs_ne_0.

    simpl in Hxym.
    rewrite andb_false_r in Hxym.
    unfold I_div_max_iter_int in Hm2; simpl in Hm2.
    remember (fst_same ym I_ones 0) as s3 eqn:Hs3 .
    destruct s3 as [dj3| ]; [ idtac | clear Hm2 ].
     rewrite Nat.add_0_r in Hm2.
     remember (two_power dj3) as n eqn:Hn .
     symmetry in Hn.
     destruct n; [ idtac | discriminate Hm2 ].
     exfalso; revert Hn; apply two_power_neq_0.

     apply fst_same_sym_iff in Hs3; simpl in Hs3.
     apply I_zero_eqs_iff in Hs3.
     revert Hm Hxym Hs3; clear; intros.
     exfalso.
     destruct m.
      simpl in Hxym.
      injection Hxym; clear Hxym; intros; subst xm ym.
      unfold R_div_equiv_max_iter in Hm; simpl in Hm.
      rewrite <- Z.add_assoc in Hm; simpl in Hm.
      rewrite Z2Nat.inj_add in Hm.
       simpl in Hm.
       unfold Pos.to_nat in Hm; simpl in Hm.
       rewrite Nat.add_comm in Hm.
       apply Nat.add_sub_eq_r in Hm; simpl in Hm.
       destruct (Z.to_nat (R_int (R_abs x))); discriminate Hm.

       apply R_int_abs.

       apply Z.le_0_2.

      simpl in Hxym.
      rewrite andb_true_r in Hxym.
      remember (R_int (R_abs x) / 2 =? 0) as c eqn:Hc .
      symmetry in Hc.
      destruct c.
       injection Hxym; clear Hxym; intros; subst xm ym.
       rewrite I_zero_eqs_iff in Hs3.
       simpl in Hs3.
       pose proof (Hs3 O) as H; discriminate H.
       apply Z.eqb_neq in Hc.
       do 2 rewrite <- Nat.add_1_r in Hm.
       rewrite <- Nat.add_assoc in Hm; simpl in Hm.
       eapply formula_2 in Hxym; try eassumption; try reflexivity.
       contradiction.

   destruct m.
    simpl in Hxym.
    injection Hxym; clear Hxym; intros; subst xm ym.
    unfold I_div_max_iter_int in Hm2; simpl in Hm2.
    remember (fst_same 0 I_ones 0) as s3 eqn:Hs3 .
    destruct s3 as [dj3| ]; [ idtac | discriminate Hm2 ].
    apply fst_same_sym_iff in Hs3; simpl in Hs3.
    destruct Hs3 as (Hn3, Ht3).
    discriminate Ht3.

    simpl in Hxym.
    rewrite andb_false_r in Hxym.
    destruct m.
     simpl in Hxym.
     injection Hxym; clear Hxym; intros; subst xm ym.
     unfold I_div_max_iter_int in Hm2; simpl in Hm2.
     remember (fst_same 0 I_ones 0) as s3 eqn:Hs3 .
     destruct s3 as [dj3| ]; [ idtac | discriminate Hm2 ].
     apply fst_same_sym_iff in Hs3; simpl in Hs3.
     destruct Hs3 as (Hn3, Ht3).
     discriminate Ht3.

     simpl in Hxym.
     rewrite andb_true_r in Hxym.
     remember (R_int (R_abs x) / 2 =? 0) as c eqn:Hc .
     symmetry in Hc.
     destruct c.
      injection Hxym; clear Hxym; intros; subst xm ym.
      simpl in Hrif.
      apply Z.eqb_eq in Hc.
      remember (Z.odd (R_int (R_abs x))) as b.
      remember (I_div_2_inc (R_frac (R_abs x)) b) as x1 eqn:Hx1; subst b.
      remember (I_div_2_inc 0 true) as y1 eqn:Hy1 .
      remember Hx1 as H; clear HeqH.
      apply I_eql_eqs in H.
      apply I_div_2_inc_iff in H; simpl in H.
      destruct H as (Hx1_0, Hx1_S).
      remember Hy1 as H; clear HeqH.
      apply I_eql_eqs in H.
      apply I_div_2_inc_iff in H; simpl in H.
      destruct H as (Hy1_0, Hy1_S).
      rename i into j.
      symmetry.
      destruct (I_lt_dec x1 y1) as [H1| H1].
       injection Hrif; clear Hrif; intros; subst ri rf; simpl.
       remember (I_div_lt_pred_i x1 y1 j) as bxy eqn:Hbxy3 .
       symmetry in Hbxy3.
       destruct bxy as (b3, (x3, y3)); simpl.
       destruct (I_lt_dec x3 y3) as [H3| H3]; simpl.
        destruct j.
         pose proof (Hx1_S O) as H.
         unfold R_abs in H; simpl in H.
         remember (R_is_neg x) as nx eqn:Hnx .
         symmetry in Hnx.
         destruct nx; simpl in H.
          apply negb_sym in H; rewrite H.
          apply negb_false_iff.
          simpl in Hbxy3.
          injection Hbxy3; clear Hbxy3; intros; subst b3 x3 y3.
          unfold I_lt, I_compare in H3; simpl in H3.
          remember (fst_same x1 (- I_div_2 y1) 0) as s3 eqn:Hs3 .
          destruct s3 as [dj3| ]; [ idtac | discriminate H3 ].
          apply fst_same_sym_iff in Hs3; simpl in Hs3.
          destruct Hs3 as (Hn3, Ht3).
          destruct dj3; simpl in Ht3.
           rewrite Ht3 in H3; discriminate H3.

           clear H.
           destruct dj3.
            destruct (x1 .[ 1]); [ discriminate H3 | clear H3 ].
            clear Ht3.
            pose proof (Hn3 O Nat.lt_0_1) as H.
            simpl in H.
            rewrite Hx1_0 in H; simpl in H.
            rewrite H in Hx1_0.
            unfold R_abs in H.
            rewrite Hnx in H; simpl in H.
            rewrite Z.odd_sub in H; simpl in H.
            rewrite xorb_true_r in H.
            apply negb_false_iff in H.
            unfold R_abs in Hc; simpl in Hc.
            rewrite Hnx in Hc; simpl in Hc.
            apply Zodd_bool_iff in H.
            apply Zodd_ex_iff in H.
            destruct H as (i, Hi).
            rewrite Hi in Hc.
            rewrite Z.add_simpl_r in Hc.
            rewrite Z.mul_comm in Hc.
            rewrite Z.div_mul in Hc; [ idtac | intros H; discriminate H ].
            subst i; simpl in Hi.
            apply Z.eq_opp_l in Hi; simpl in Hi.
            unfold R_abs in Hx1_S.
            rewrite Hnx in Hx1_S; simpl in Hx1_S.
            clear Hn3.
            rewrite Nat.add_0_l in Ht2.
            simpl in Ht2.
            remember (I_div_lt_pred_i x1 y1 dj2) as bxy eqn:Hbxy .
            symmetry in Hbxy.
            destruct bxy as (b2, (x2, y2)); simpl in Ht2.
            destruct (I_lt_dec x2 y2) as [H2| H2]; simpl in Ht2.
             destruct (I_lt_dec x2 (I_div_2 y2)) as [H3| H3].
              2: discriminate Ht2.

              clear Ht2.
              remember (I_div_2 y2) as y3 eqn:Hy3 .
              remember Hy3 as H; clear HeqH.
              unfold I_div_2 in H.
              apply I_eql_eqs in H.
              apply I_div_2_inc_iff in H; simpl in H.
              destruct H as (Hy3_0, Hy3_S).
              unfold I_lt, I_compare in H3; simpl in H3.
              remember (fst_same x2 (- y3) 0) as s3 eqn:Hs3 .
              destruct s3 as [dj3| ]; [ idtac | discriminate H3 ].
              apply fst_same_sym_iff in Hs3; simpl in Hs3.
              destruct Hs3 as (Hn3, Ht3).
              remember (x2 .[ dj3]) as b eqn:H23 .
              destruct b; [ discriminate H3 | clear H3 ].
              symmetry in H23.
              apply negb_sym in Ht3; simpl in Ht3.
              destruct dj3.
               rewrite Hy3_0 in Ht3; discriminate Ht3.

               remember Ht3 as H; clear HeqH.
               rewrite Hy3_S in H.
               destruct dj2.
                simpl in Hbxy.
                injection Hbxy; clear Hbxy; intros; subst b2 x2 y2.
                simpl in H.
                destruct dj3; [ discriminate H | simpl in H ].
                simpl in Hy3_S.
                rewrite Nat.sub_0_r in H.
                rename H into Hy13.
                assert (1 < S (S dj3))%nat as H by omega.
                apply Hn3 in H; simpl in H.
                rewrite negb_involutive in H.
                rewrite Hy3_S in H; simpl in H.
bbb.
      destruct (I_lt_dec x1 y1) as [H1| H1].
       injection Hrif; clear Hrif; intros; subst ri rf.
       simpl.
       remember (I_div_lt_pred_i x1 y1 i) as bxy eqn:Hbxy3 .
       symmetry in Hbxy3.
       destruct bxy as (b3, (x3, y3)); simpl.
       destruct (I_lt_dec x3 y3) as [H3| H3]; simpl.
        destruct i.
         simpl in Hbxy3.
         injection Hbxy3; clear Hbxy3; intros; subst b3 x3 y3.
         remember Hx1 as H; clear HeqH.
         apply I_div_2_inc_0 in H.
         rename H into Vx1.
         remember Hy1 as H; clear HeqH.
         apply I_div_2_inc_0 in H.
         rename H into Vy1.
         remember Hx1 as H; clear HeqH.
         apply I_div_2_inc_1 in H.
         rename H into Vx2.
         remember Hy1 as H; clear HeqH.
         apply I_div_2_inc_1 in H.
         simpl in H.
         rename H into Vy2.
         unfold I_lt, I_compare in H3; simpl in H3.
         remember (fst_same x1 (- I_div_2 y1) 0) as s3 eqn:Hs3 .
         destruct s3 as [dj3| ]; [ idtac | discriminate H3 ].
         apply fst_same_sym_iff in Hs3; simpl in Hs3.
         destruct Hs3 as (Hn3, Ht3).
         destruct dj3; simpl in Ht3.
          rewrite Ht3 in H3; discriminate H3.

          rewrite Nat.sub_0_r in Ht3.
          pose proof (Hn3 O (Nat.lt_0_succ dj3)) as H; simpl in H.
          remember (x1 .[ S dj3]) as b eqn:Hx3 .
          destruct b; [ discriminate H3 | clear H3 ].
          symmetry in Hx3.
          apply negb_sym in Ht3; simpl in Ht3.
          destruct dj3.
           clear Ht3.
           rename H into Wx1.
           remember Hx3 as H; clear HeqH.
           rewrite Vx2 in H.
           unfold R_abs in H; simpl in H.
           remember (R_is_neg x) as nx eqn:Hnx .
           symmetry.
           symmetry in Hnx.
           destruct nx; [ simpl in H | assumption ].
           apply negb_false_iff in H; exfalso.
           unfold R_abs in Hc; simpl in Hc.
           rewrite Hnx in Hc; simpl in Hc.
           unfold R_abs in Vx1; simpl in Vx1.
           rewrite Hnx in Vx1; simpl in Vx1.
           unfold R_abs in Vx2; simpl in Vx2.
           rewrite Hnx in Vx2; simpl in Vx2.
           rewrite H in Vx2; simpl in Vx2.
           unfold R_abs in Hx1.
           rewrite Hnx in Hx1; simpl in Hx1.
           rename H into Hfx.
           remember Hnx as H; clear HeqH.
           unfold R_is_neg in H; simpl in H.
           apply Z.ltb_lt in H.
           rewrite <- Vx1, Wx1 in Hx1.
           unfold R_div_equiv_max_iter in Hm; simpl in Hm.
           unfold R_abs in Hm; simpl in Hm.
           rewrite Hnx in Hm; simpl in Hm.
           remember (R_int x) as xi eqn:Hxi .
           destruct (Z_eq_dec xi (- 1)) as [H2| H2].
            move H2 at top; subst xi.
            clear H.
            simpl in Vx1.
            simpl in Hc.
            clear Hc.
            simpl in Hm.
            clear m Hm.
            clear Wx1.
            clear Hn3.
            clear Hx3.
            destruct dj2.
             simpl in Ht2.
             destruct (I_lt_dec x1 (I_div_2 y1)) as [H2| H2]; simpl in Ht2.
              destruct (I_lt_dec x1 (I_div_2 (I_div_2 y1))) as [H3| H3];
               [ idtac | discriminate Ht2 ].
              clear Ht2.
              remember (x1 .[ 2]) as b eqn:Hx2 .
              symmetry in Hx2.
              remember Hx2 as H; clear HeqH.
              rewrite Hx1 in H; simpl in H.
              rewrite <- H in Hx2; clear b H.
              remember (x1 .[ S (S dj1)]) as b eqn:Hxj1 .
              symmetry in Hxj1.
              remember Hxj1 as H; clear HeqH.
              rewrite Hx1 in H; simpl in H.
              simpl in Ht1; rewrite Ht1 in H; simpl in H.
              rewrite <- H in Hxj1; clear b H.
              destruct dj1.
               rewrite Hxj1 in Hx2; apply negb_sym in Hx2; simpl in Hx2.
               unfold I_lt, I_compare in H3; simpl in H3.
               remember (fst_same x1 (- I_div_2 (I_div_2 y1)) 0) as s3
                eqn:Hs3 .
               destruct s3 as [dj3| ]; [ idtac | discriminate H3 ].
               apply fst_same_sym_iff in Hs3; simpl in Hs3.
               destruct Hs3 as (Hn3, Ht3).
               destruct dj3; simpl in Ht3.
                rewrite Ht3 in H3; discriminate H3.

                rewrite Nat.sub_0_r in Ht3.
                destruct dj3; simpl in Ht3.
                 rewrite Ht3 in H3; discriminate H3.

                 rewrite Nat.sub_0_r in Ht3.
                 remember (x1 .[ S (S dj3)]) as b eqn:Hx3 .
                 destruct b; [ discriminate H3 | clear H3 ].
                 symmetry in Hx3.
                 apply negb_sym in Ht3; simpl in Ht3.
                 destruct dj3.
                  rewrite Hx3 in Hxj1; discriminate Hxj1.

                  rewrite Hy1 in Ht3; discriminate Ht3.

               pose proof (Hn1 O (Nat.lt_0_succ dj1)) as H; simpl in H.
               rewrite H in Hx2; simpl in Hx2.
               rename H into Hx01.
               remember Hx1 as H; clear HeqH.
               apply I_eql_eqs in H.
               apply I_div_2_inc_iff in H; simpl in H.
               destruct H as (Hx1_0, Hx1_S).
bbb.

  x    0.11.
  x1   0.000.
  y1   0.10.

bbb.

     apply I_zero_eqs_iff in Hs3.
    destruct m.
     simpl in Hxym.
     injection Hxym; clear Hxym; intros; subst xm ym.
     unfold R_div_equiv_max_iter in Hm; simpl in Hm.
     rewrite <- Z.add_assoc in Hm; simpl in Hm.
     rewrite Z2Nat.inj_add in Hm.
      simpl in Hm.
      unfold Pos.to_nat in Hm; simpl in Hm.
      rewrite Nat.add_comm in Hm.
      apply Nat.add_sub_eq_r in Hm; simpl in Hm.
      destruct (Z.to_nat (R_int (R_abs x))); discriminate Hm.

      apply R_int_abs.

      apply Z.le_0_2.

     simpl in Hxym.
     rewrite andb_true_r in Hxym.
     remember (R_int (R_abs x) / 2 =? 0) as c eqn:Hc .
     symmetry in Hc.
     destruct c.
      injection Hxym; clear Hxym; intros; subst xm ym.
      unfold I_div_max_iter_int in Hm2; simpl in Hm2.
      remember (fst_same (I_div_2_inc 0 true) I_ones 0) as s3 eqn:Hs3 .
      destruct s3 as [dj3| ]; [ idtac | clear Hm2 ].
       rewrite Nat.add_0_r in Hm2.
       remember (two_power dj3) as n eqn:Hn .
       symmetry in Hn.
       destruct n.
        exfalso; revert Hn; apply two_power_neq_0.

        discriminate Hm2.

       apply fst_same_sym_iff in Hs3; simpl in Hs3.
       pose proof (Hs3 O) as H; discriminate H.

      apply Z.eqb_neq in Hc.
      unfold I_div_max_iter_int in Hm2; simpl in Hm2.
      remember (fst_same ym I_ones 0) as s3 eqn:Hs3 .
      destruct s3 as [dj3| ]; [ idtac | clear Hm2 ].
       rewrite Nat.add_0_r in Hm2.
       remember (two_power dj3) as n eqn:Hn .
       symmetry in Hn.
       destruct n.
        exfalso; revert Hn; apply two_power_neq_0.

        discriminate Hm2.

       apply fst_same_sym_iff in Hs3; simpl in Hs3.
       apply I_zero_eqs_iff in Hs3.
bbb.
       destruct m.
        simpl in Hxym.
        unfold R_div_equiv_max_iter in Hm; simpl in Hm.
        rewrite <- Z.add_assoc in Hm; simpl in Hm.
        rewrite Z2Nat.inj_add in Hm.
         simpl in Hm.
         unfold Pos.to_nat in Hm; simpl in Hm.
         rewrite Nat.add_comm in Hm.
         apply Nat.add_sub_eq_r in Hm; simpl in Hm.
         remember (Z.to_nat (R_int (R_abs x))) as xi eqn:Hxi .
         symmetry in Hxi.
         destruct xi; try discriminate Hm.
          clear Hm.
          rewrite <- Nat2Z.id in Hxi.
          apply Z2Nat.inj in Hxi.
           rewrite Hxi in Hc; simpl in Hc.
           exfalso; apply Hc; reflexivity.

           apply R_int_abs.

           reflexivity.

          destruct xi; discriminate Hm.

         apply R_int_abs.

         apply Z.le_0_2.

        simpl in Hxym.
        rewrite andb_true_r in Hxym.
        remember (R_int (R_abs x) / 2 / 2 =? 0) as c1 eqn:Hc1 .
        symmetry in Hc1.
        destruct c1.
         injection Hxym; clear Hxym; intros; subst xm ym.
         rewrite I_zero_eqs_iff in Hs3.
         simpl in Hs3.
         pose proof (Hs3 1%nat) as H; discriminate H.
bbb.

Theorem R_div_1_r : ∀ x, (x / 1 = x)%R.
Proof.
intros x.
unfold R_eq; simpl.
split; [ idtac | apply R_frac_div_1_r ].
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
