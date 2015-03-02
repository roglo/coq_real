(* Division in I = ℝ interval [0..1[ *)

Require Import Utf8 QArith NPeano.
Require Import Digit Real01 Real01Add Real01Cmp.

Set Implicit Arguments.

Open Scope Z_scope.

Fixpoint two_power n :=
  match n with
  | O => 1%nat
  | S n1 => (2 * two_power n1)%nat
  end.

Definition I_div_max_iter_int y :=
  match fst_same y I_one 0 with
  | Some j => two_power (S j)
  | None => O
  end.
Arguments I_div_max_iter_int y%I.

Definition I_div_2_inc x b :=
  {| rm i := if zerop i then b else x.[i-1] |}.
Arguments I_div_2_inc x%I b%D.

Definition I_div_2 x := I_div_2_inc x 0.
Arguments I_div_2 x%I.

Definition I_mul_2 x := {| rm i := x.[S i] |}.
Arguments I_mul_2 x%I.

Notation "½ x" := (I_div_2 x) (at level 40) : I_scope.

(*
  Remainder of division x/y (x<y) before evaluating i-th bimal (0th=1st
  after dot)
         | x               if i = 0
   R_i = | 2 * R_i-1       if 2 * R_i-1 < y
         | 2 * R_i-1 - y   if 2 * R_i-1 ≥ y
  In base B would be
       R_0 = x
     R_i+1 = B * R_i mod y
 *)
Fixpoint I_div_rem_i x y i :=
  match i with
  | O => x
  | S i1 =>
      let x1 := I_mul_2 (I_div_rem_i x y i1) in
      if I_lt_dec x1 y then x1 else (x1 - y)%I
  end.
Arguments I_div_rem_i x%I y%I i%nat.

(* i-th bimal (0th=1st after dot) of division x/y (x<y) *)
Definition I_div_lt_i x y i :=
  if I_lt_dec (I_mul_2 (I_div_rem_i x y i)) y then 0%D else 1%D.
Arguments I_div_lt_i x%I y%I i%nat.

(* division x/y when x<y *)
Definition I_div_lt x y := {| rm := I_div_lt_i (I_div_2 x) (I_div_2 y) |}.
Arguments I_div_lt x%I y%I.

(* integer part of division x/y *)
Fixpoint I_div_int m x y :=
  match m with
  | O => O
  | S m1 =>
      if I_lt_dec x y then O
      else S (I_div_int m1 (x - y)%I y)
  end.
Arguments I_div_int m%nat x%I y%I.

(* fractionnal part of division x/y with limited iterations *)
Fixpoint I_div_frac m x y :=
  match m with
  | O => 0%I
  | S m1 =>
      if I_lt_dec x y then I_div_lt x y
      else I_div_frac m1 (x - y)%I y
  end.
Arguments I_div_frac m%nat x%I y%I.

(* fractional part of division x/y *)
Definition I_div x y := I_div_frac (I_div_max_iter_int y) x y.
Arguments I_div x%I y%I.

Notation "x / y" := (I_div x y) : I_scope.

(* experimentation *)

Definition I_div_2_pow x i :=
  {| rm j := if lt_dec j i then 0%D else x.[j-i] |}.

Fixpoint I_div_by_sub m x y :=
  match m with
  | O => 0%D
  | S m1 =>
      if I_lt_dec x y then 0%D
      else oppd (I_div_by_sub m1 (I_sub x y) y)
  end.

Definition I_div3_lt_i x y i :=
  I_div_by_sub (two_power (S i)) x (I_div_2_pow y (S i)).

Definition I_div3_lt x y := {| rm := I_div3_lt_i x y |}.

Fixpoint I_div3_frac m x y :=
  match m with
  | O => I_zero
  | S m1 =>
      if I_lt_dec x y then I_div3_lt x y
      else I_div3_frac m1 (I_sub x y) y
  end.

Definition I_div3 x y := I_div3_frac (I_div_max_iter_int y) x y.

(* *)

Theorem zzz : ∀ x y, (I_div3 x y == x / y)%I.
Proof.
intros x y.
apply I_eqs_iff; simpl; intros i.
unfold I_div3, I_div; simpl.
remember (I_div_max_iter_int y) as m eqn:Hm .
symmetry in Hm.
destruct m; [ reflexivity | simpl ].
destruct (I_lt_dec x y) as [H1| H1].
 unfold I_div3_lt, I_div_lt; simpl.
 unfold I_div3_lt_i, I_div_lt_i.
 remember (two_power (S i)) as m2 eqn:Hm2 .
 symmetry in Hm2; simpl.
 destruct (I_lt_dec (I_mul_2 (I_div_rem_i (½x) (½y) i)) (½y)%I) as [H2| H2].
  destruct m2; [ reflexivity | simpl ].
  destruct (I_lt_dec x (I_div_2_pow y (S i))) as [H3| H3].
   reflexivity.

   apply oppd_0_iff.
   destruct m2.
    simpl.
    simpl in Hm2.
    revert Hm2; clear; intros.
    Focus 2.
    simpl.
    destruct (I_lt_dec (x - I_div_2_pow y (S i))%I (I_div_2_pow y (S i)))
     as [H4| H4].
     remember (I_div_2_pow y (S i)) as y1 eqn:Hy1 .
Abort. (* faut réfléchir...
bbb.
*)

(* *)

Theorem I_add_i_diag : ∀ x i, (I_add_i x x i = x.[S i])%D.
Proof.
intros x i.
unfold I_add_i; simpl.
rewrite digit_add_nilpotent, carry_diag, digit_add_0_l.
reflexivity.
Qed.

Theorem I_zero_iff2 : ∀ x, (x = 0)%I ↔ (x == 0)%I ∨ (∀ j, (x.[j] = 1)%D).
Proof.
intros x.
split; intros Hx.
 apply I_zero_iff in Hx.
 destruct Hx as [Hx| Hx].
  left.
  unfold I_eqs, I_compare.
  remember (fst_same x (- 0%I) 0) as s1 eqn:Hs1 .
  destruct s1 as [j1| ]; [ exfalso | reflexivity ].
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, Ht1).
  rewrite Hx in Ht1; discr_digit Ht1.

  right; assumption.

 apply I_zero_iff.
 destruct Hx as [Hx| Hx].
  left; intros i.
  unfold I_eqs, I_compare in Hx; simpl in Hx.
  remember (fst_same x (- 0%I) 0) as s1 eqn:Hs1 .
  destruct s1 as [dj1| ]; [ idtac | clear Hx ].
   destruct (digit_eq_dec (x .[ dj1]) 1); discriminate Hx.

   apply fst_same_sym_iff in Hs1; simpl in Hs1.
   apply Hs1.

  right; assumption.
Qed.

Theorem I_div_2_eqs_0 : ∀ x, (I_div_2 x == 0)%I → (x == 0)%I.
Proof.
intros x Hx.
apply I_zero_eqs_iff.
intros i.
rewrite I_zero_eqs_iff in Hx.
pose proof (Hx (S i)) as H; simpl in H.
rewrite Nat.sub_0_r in H; assumption.
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

Add Parametric Morphism : I_mul_2
  with signature I_eqs ==> I_eqs
  as I_mul_2_morph.
Proof.
intros x y Hxy.
rewrite I_eqs_iff in Hxy.
apply I_eqs_iff.
intros i; apply Hxy.
Qed.

Add Parametric Morphism : I_div_2
  with signature I_eqs ==> I_eqs
  as I_div_2_morph.
Proof.
intros x y Hxy.
rewrite I_eqs_iff in Hxy.
apply I_eqs_iff.
intros i; destruct i; [ reflexivity | simpl ].
apply Hxy.
Qed.

Theorem I_mul_2_0 : ∀ x, (x == 0)%I → (I_mul_2 x == 0)%I.
Proof.
intros x Hx; rewrite Hx.
apply I_zero_eqs_iff; intros j; reflexivity.
Qed.

Theorem I_div_2_0 : ∀ x, (x == 0)%I → (I_div_2 x == 0)%I.
Proof.
intros x Hx; rewrite Hx.
apply I_zero_eqs_iff; intros j; destruct j; reflexivity.
Qed.

Theorem I_div_rem_i_0_l : ∀ y i, (I_div_rem_i 0 y i == 0)%I.
Proof.
intros y i.
revert y.
induction i; intros; [ reflexivity | simpl ].
remember (I_mul_2 (I_div_rem_i 0 y i)) as x1 eqn:Hx1 .
destruct (I_lt_dec x1 y) as [H1| H1].
 rewrite Hx1, IHi.
 apply I_mul_2_0; reflexivity.

 subst x1.
 rewrite IHi, I_mul_2_0 in H1; [ idtac | reflexivity ].
 rewrite IHi, I_mul_2_0; [ idtac | reflexivity ].
 apply I_ge_0_l_eqs_iff in H1.
 rewrite H1; apply I_sub_diag_eqs.
Qed.

(* division by 0 is 0 in this implementation *)
Theorem I_div_0_r : ∀ x y, (y == 0)%I → (x / y == 0)%I.
Proof.
intros x y Hy.
rewrite I_eqs_iff in Hy; simpl in Hy.
apply I_eqs_iff; simpl; intros i.
unfold I_div; simpl.
remember (I_div_max_iter_int y) as m eqn:Hm .
symmetry in Hm.
unfold I_div_max_iter_int in Hm.
remember (fst_same y I_one 0) as s2 eqn:Hs2 .
destruct s2 as [dj2| ].
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct Hs2 as (Hn2, Ht2).
 rewrite Hy in Ht2; discr_digit Ht2.

 subst m; reflexivity.
Qed.

Theorem I_div_0_l : ∀ x, (0 / x == 0)%I.
Proof.
intros x.
destruct (I_eqs_dec x 0%I) as [Hx| Hx].
 apply I_div_0_r; assumption.

 apply I_zero_eqs_iff; simpl; intros i.
 unfold I_div; simpl.
 remember (I_div_max_iter_int x) as m eqn:Hm .
 symmetry in Hm.
 destruct m; [ reflexivity | simpl ].
 destruct (I_lt_dec 0%I x) as [H1| H1]; simpl.
  unfold I_div_lt_i; simpl.
  remember (I_div_2 x) as y1 eqn:Hy1 .
  remember (I_mul_2 (I_div_rem_i (I_div_2 0) y1 i)) as x1 eqn:Hx1 .
  destruct (I_lt_dec x1 y1) as [H2| H2]; [ reflexivity | exfalso ].
  subst x1.
  rewrite I_mul_2_0 in H2.
   apply I_ge_0_l_eqs_iff in H2.
   subst y1.
   apply I_div_2_eqs_0 in H2; contradiction.

   clear.
   induction i; [ apply I_div_2_0; reflexivity | idtac ].
   simpl.
   remember (I_mul_2 (I_div_rem_i (I_div_2 0) y1 i)) as x1 eqn:Hx1 .
   destruct (I_lt_dec x1 y1) as [H3| H3].
    subst x1.
    apply I_mul_2_0, IHi.

    subst x1.
    rewrite IHi.
    rewrite I_mul_2_0; [ idtac | reflexivity ].
    rewrite I_mul_2_0 in H3.
     apply I_ge_0_l_eqs_iff in H3.
     rewrite H3.
     apply I_sub_diag_eqs.

     apply IHi.

  apply I_ge_0_l_eqs_iff in H1; contradiction.
Qed.

Theorem I_mul_2_div_2 : ∀ x, (I_mul_2 (I_div_2 x) == x)%I.
Proof.
intros x.
apply I_eqs_iff; intros i.
destruct i; reflexivity.
Qed.

Theorem I_div_eqs_compat_l : ∀ x y z, (x == y)%I → (x / z == y / z)%I.
Proof.
intros x y z Hxy.
rewrite I_eqs_iff in Hxy.
rewrite I_eqs_iff; intros i.
unfold I_div; simpl.
remember (I_div_max_iter_int z) as m eqn:Hm .
symmetry in Hm.
destruct m; [ reflexivity | simpl ].
unfold I_div_max_iter_int in Hm.
remember (fst_same z I_one 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate Hm ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
destruct (I_lt_dec x z) as [H1| H1].
 destruct (I_lt_dec y z) as [H2| H2].
  unfold I_div_lt; simpl.
  unfold I_div_lt_i.
  remember (I_mul_2 (I_div_rem_i (½x) (½z) i)) as x1 eqn:Hx1 .
  remember (I_mul_2 (I_div_rem_i (½y) (½z) i)) as y1 eqn:Hy1 .
  destruct (I_lt_dec x1 (½z)%I) as [H3| H3].
   destruct (I_lt_dec y1 (½z)%I) as [H4| H4]; [ reflexivity | exfalso ].
   unfold I_lt, I_compare in H3; simpl in H3.
   unfold I_ge, I_compare in H4; simpl in H4.
   remember (fst_same x1 (- (½z)%I) 0) as s3 eqn:Hs3 .
   remember (fst_same y1 (- (½z)%I) 0) as s4 eqn:Hs4 .
   destruct s3 as [dj3| ]; [ idtac | discriminate H3 ].
   remember (x1 .[ dj3]) as b eqn:Hxj3 .
Abort. (*
   oui bon, c'est merdique ; peut-être faisable avec beaucoup
   de patience

   destruct b; [ discriminate H3 | clear H3 ].
   symmetry in Hxj3.
   apply fst_same_sym_iff in Hs3; simpl in Hs3.
   destruct Hs3 as (Hn3, Ht3).
   rewrite Hxj3 in Ht3; apply negb_sym in Ht3; simpl in Ht3.
   destruct dj3; [ discriminate Ht3 | simpl in Ht3 ].
   rewrite Nat.sub_0_r in Ht3.
   pose proof (Hn3 O (Nat.lt_0_succ dj3)) as H; simpl in H.
   rename H into Hx10.
   destruct s4 as [dj4| ].
    remember (y1 .[ dj4]) as b eqn:Hyj4 .
    destruct b; [ clear H4 | exfalso; apply H4; reflexivity ].
    symmetry in Hyj4.
    apply fst_same_sym_iff in Hs4; simpl in Hs4.
    destruct Hs4 as (Hn4, Ht4).
    rewrite Hyj4 in Ht4; apply negb_sym in Ht4; simpl in Ht4.
*)

Theorem I_div_eqs_compat_r : ∀ x y z, (x == y)%I → (z / x == z / y)%I.
Proof.
intros x y z Hxy.
rewrite I_eqs_iff in Hxy.
rewrite I_eqs_iff; intros i.
unfold I_div; simpl.
remember (I_div_max_iter_int x) as mx eqn:Hmx .
remember (I_div_max_iter_int y) as my eqn:Hmy .
symmetry in Hmx, Hmy.
destruct mx; simpl.
 unfold I_div_max_iter_int in Hmx.
 remember (fst_same x I_one 0) as s1 eqn:Hs1 .
 destruct s1 as [dj1| ]; [ idtac | clear Hmx ].
  exfalso; revert Hmx; apply two_power_neq_0.

  apply fst_same_sym_iff in Hs1; simpl in Hs1.
Abort.
(* faut voir...

 destruct my; [ reflexivity | simpl ].
 destruct (I_lt_dec z y) as [H1| H1].
  unfold I_div_lt; simpl.
  symmetry.
  destruct i; simpl.
   unfold I_div_lt_i; simpl.
   destruct (I_lt_dec (I_mul_2 (½z)) (½y)%I) as [H2| H2].
    reflexivity.

    exfalso.
    unfold I_div_max_iter_int in Hmx.
bbb.
*)

Theorem xxx : ∀ x y,
  (x < I_div_2 (x / y))%I
  → (y.[0] = 0)%D.
Proof.
intros x y Hxy.
unfold I_lt, I_compare in Hxy; simpl in Hxy.
remember (fst_same x (- I_div_2 (x / y)) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ idtac | discriminate Hxy ].
bbb.
remember (x .[ dj1]) as b eqn:Hxj1 .
destruct b; [ discriminate Hxy | clear Hxy ].
symmetry in Hxj1.
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
destruct dj1; simpl in Ht1.
 rewrite Ht1 in Hxj1; discriminate Hxj1.

 pose proof (Hn1 O (Nat.lt_0_succ dj1)) as H; simpl in H.
 rename H into Hx0.
 rewrite Nat.sub_0_r, Hxj1 in Ht1.
 apply negb_sym in Ht1; simpl in Ht1.
 unfold I_div in Ht1; simpl in Ht1.
 remember (I_div_max_iter_int y) as m eqn:Hm .
 symmetry in Hm.
 destruct m; [ discriminate Ht1 | idtac ].
 simpl in Ht1.
 destruct (I_lt_dec x y) as [H1| H1].
  Focus 2.
  unfold I_ge, I_compare in H1; simpl in H1.
  remember (fst_same x (- y) 0) as s2 eqn:Hs2 .
  destruct s2 as [dj2| ]; [ idtac | clear H1 ].
   remember (x .[ dj2]) as b eqn:Hxj2 .
   destruct b; [ clear H1 | exfalso; apply H1; reflexivity ].
   symmetry in Hxj2.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   rewrite Hxj2 in Ht2.
   apply negb_sym in Ht2; simpl in Ht2.
   rename Ht2 into Hyj2.
   destruct dj2; [ assumption | idtac ].
   rewrite Hn2 in Hx0; [ idtac | apply Nat.lt_0_succ ].
   rewrite negb_involutive in Hx0; assumption.

   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   rewrite Hs2, negb_involutive in Hx0; assumption.

  simpl in Ht1.
  unfold I_div_lt_i in Ht1.
  remember (I_div_2 x) as x1 eqn:Hx1 .
  remember (I_div_2 y) as y1 eqn:Hy1 .
  remember (I_mul_2 (I_div_rem_i x1 y1 dj1)) as x2 eqn:Hx2 .
  destruct (I_lt_dec x2 y1) as [H2| H2]; [ discriminate Ht1 | clear Ht1 ].
  destruct dj1; simpl in Hx2.
   subst x1 x2 y1.
   rewrite I_mul_2_div_2 in H2.
   unfold I_ge, I_compare in H2; simpl in H2.
   remember (fst_same x (- I_div_2 y) 0) as s2 eqn:Hs2 .
   destruct s2 as [dj2| ]; [ idtac | clear H2 ].
    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    destruct Hs2 as (Hn2, Ht2).
    remember (x .[ dj2]) as b eqn:Hxj2 .
    destruct b; [ clear H2 | exfalso; apply H2; reflexivity ].
    symmetry in Hxj2.
    apply negb_sym in Ht2; simpl in Ht2.
    destruct dj2; [ rewrite Hxj2 in Hx0; discriminate Hx0 | idtac ].
    simpl in Ht2.
    rewrite Nat.sub_0_r in Ht2.
    destruct dj2; [ assumption | idtac ].
    assert (1 < S (S dj2))%nat as H by omega.
    apply Hn2 in H; simpl in H.
    rewrite Hxj1, negb_involutive in H.
    symmetry; assumption.

    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    pose proof (Hs2 1%nat) as H; simpl in H.
    rewrite Hxj1, negb_involutive in H.
    symmetry; assumption.

   assert (1 < S (S dj1))%nat as H by omega.
   apply Hn1 in H; simpl in H.
   rewrite negb_involutive in H.
   unfold I_div in H; simpl in H.
   rewrite Hm in H; simpl in H.
   apply I_lt_nge in H1.
   destruct (I_lt_dec x y) as [H3| H3]; [ idtac | contradiction ].
   apply I_lt_nge in H1.
   clear H3; rename H into Hx_1.
   subst x1 x2.
   remember (I_mul_2 (I_div_rem_i (I_div_2 x) y1 dj1)) as x1 eqn:Hx1 .
   destruct (I_lt_dec x1 y1) as [H3| H3].
    unfold I_lt, I_compare in H3.
    unfold I_ge, I_compare in H2.
    remember (fst_same (I_mul_2 x1) (- y1) 0) as s2 eqn:Hs2 .
    remember (fst_same x1 (- y1) 0) as s3 eqn:Hs3 .
    destruct s3 as [dj3| ]; [ idtac | discriminate H3 ].
    remember (x1 .[ dj3]) as b eqn:Hxj3 .
    symmetry in Hxj3.
    destruct b; [ discriminate H3 | clear H3 ].
    apply fst_same_sym_iff in Hs3; simpl in Hs3.
    destruct Hs3 as (Hn3, Ht3).
    rewrite Hxj3 in Ht3; apply negb_sym in Ht3; simpl in Ht3.
    destruct s2 as [dj2| ]; [ idtac | clear H2 ].
     remember (I_mul_2 x1 .[ dj2]) as b eqn:Hxj2 .
     symmetry in Hxj2.
     destruct b; [ clear H2 | exfalso; apply H2; reflexivity ].
     apply fst_same_sym_iff in Hs2; simpl in Hs2.
     destruct Hs2 as (Hn2, Ht2).
     simpl in Hxj2.
     rewrite Hxj2 in Ht2; apply negb_sym in Ht2; simpl in Ht2.
     rewrite Hy1 in Ht3; simpl in Ht3.
     rewrite Hy1 in Ht2; simpl in Ht2.
     destruct dj2; [ clear Ht2 | idtac ].
      rewrite Hx1 in Hxj2; simpl in Hxj2.
      unfold I_div_lt in Hx_1.
      simpl in Hx_1.
      unfold I_div_lt_i in Hx_1.
      simpl in Hx_1.
      destruct dj3; [ discriminate Ht3 | simpl in Ht3 ].
      rewrite Nat.sub_0_r in Ht3.
      pose proof (Hn3 O (Nat.lt_0_succ dj3)) as H.
      rewrite negb_involutive in H.
      rewrite Hx1, Hy1 in H; simpl in H.
      rewrite <- Hy1 in H.
      rename H into Hxj4.
      clear Hn2.
      rewrite Hx1 in Hxj3; simpl in Hxj3.
      destruct dj3; [ rewrite Hxj2 in Hxj3; discriminate Hxj3 | idtac ].
      assert (1 < S (S dj3))%nat as H by omega.
      apply Hn3 in H; simpl in H.
      rewrite negb_involutive in H.
      rewrite Hx1, Hy1 in H; simpl in H.
      rewrite <- Hy1, Hxj2 in H.
      clear H.
      assert (1 < S (S dj3))%nat as H by omega.
      apply Hn3 in H; simpl in H.
      rewrite Hx1, Hy1 in H; simpl in H.
      rewrite negb_involutive in H.
      rewrite <- Hy1, Hxj2 in H.
      symmetry in H.
      rename H into Hy0.
      exfalso.
      subst y1.
(* if test then *)
      destruct (I_lt_dec (I_mul_2 (½x)) (½y)%I) as [H2| H2].
       rewrite I_mul_2_div_2 in H2.
       destruct dj1.
        simpl in Hxj2.
        rewrite Hx_1 in Hxj2; discriminate Hxj2.

        simpl in Hx1, Hxj4, Hxj2, Hxj3.
        remember (I_mul_2 (I_div_rem_i (½x) (½y) dj1)) as x2 eqn:Hx2 .
        assert (2 < S (S (S dj1)))%nat as H by omega.
        apply Hn1 in H; simpl in H.
        rewrite negb_involutive in H.
        unfold I_div in H; simpl in H.
        rewrite Hm in H; simpl in H.
        apply I_lt_nge in H1.
        destruct (I_lt_dec x y) as [H3| H3]; [ idtac | contradiction ].
        apply I_lt_nge in H1.
        clear H3; rename H into Hx_2.
        simpl in Hx_2.
        unfold I_div_lt_i in Hx_2; simpl in Hx_2.
        destruct (I_lt_dec x2 (½y)%I) as [H3| H3].
         subst x2.
         simpl in Hx1, Hxj4, Hxj2, Hxj3.
         destruct (I_lt_dec (I_mul_2 (½x)) (½y)%I) as [H4| H4].
          2: rewrite I_mul_2_div_2 in H4.
          clear H4.
          destruct (I_lt_dec (I_mul_2 (I_mul_2 (½x))) (½y)%I) as [H4| H4].
           destruct dj1.
            simpl in Hxj2.
            rewrite Hxj2 in Hx_2; discriminate Hx_2.

            simpl in Hx1, Hxj4, Hxj2, Hxj3, H3.
            remember (I_mul_2 (I_div_rem_i (½x) (½y) dj1)) as x2 eqn:Hx2 .
            assert (3 < S (S (S (S dj1))))%nat as H by omega.
            apply Hn1 in H; simpl in H.
            rewrite negb_involutive in H.
            unfold I_div in H; simpl in H.
            rewrite Hm in H; simpl in H.
            apply I_lt_nge in H1.
            destruct (I_lt_dec x y) as [H5| H5]; [ idtac | contradiction ].
            apply I_lt_nge in H1.
            rewrite I_mul_2_div_2 in H4.
            clear H5; rename H into Hx_3.
            simpl in Hx_3.
            unfold I_div_lt_i in Hx_3; simpl in Hx_3.
            destruct (I_lt_dec x2 (½y)%I) as [H5| H5].
             destruct (I_lt_dec (I_mul_2 (½x)) (½y)%I) as [H6| H6].
              2: rewrite I_mul_2_div_2 in H6.
              clear H6.
              destruct (I_lt_dec (I_mul_2 (I_mul_2 (½x))) (½y)%I) as [H6| H6].
               2: rewrite I_mul_2_div_2 in H6.
               clear H6.
               destruct (I_lt_dec (I_mul_2 (I_mul_2 (I_mul_2 (½x)))) (½y)%I)
                as [H6| H6].
                2: rewrite I_mul_2_div_2 in H6.
                rewrite I_mul_2_div_2 in H6.
                subst x2.
                simpl in Hx1, Hxj4, Hxj2, Hxj3, H3.
                destruct dj1.
                 simpl in Hx1, Hxj4, Hxj2, Hxj3, H3.
                 rewrite Hxj2 in Hx_3; discriminate Hx_3.

                 simpl in Hx1, Hxj4, Hxj2, Hxj3, H3.
                 assert (4 < S (S (S (S (S dj1)))))%nat as H by omega.
                 apply Hn1 in H; simpl in H.
                 rewrite negb_involutive in H.
                 unfold I_div in H; simpl in H.
                 rewrite Hm in H; simpl in H.
                 apply I_lt_nge in H1.
                 destruct (I_lt_dec x y) as [H7| H7];
                  [ idtac | contradiction ].
                 apply I_lt_nge in H1.
                 clear H7; rename H into Hx_4.
                 simpl in Hx_4.
                 unfold I_div_lt_i in Hx_4; simpl in Hx_4.
                 destruct (I_lt_dec (I_mul_2 (½x)) (½y)%I) as [H7| H7].
                  rewrite I_mul_2_div_2 in H7.
                  clear H7.
                  destruct (I_lt_dec (I_mul_2 (I_mul_2 (½x))) (½y)%I)
                   as [H7| H7].
                   rewrite I_mul_2_div_2 in H7.
                   clear H7.
                   destruct
                    (I_lt_dec (I_mul_2 (I_mul_2 (I_mul_2 (½x)))) (½y)%I)
                    as [H7| H7].
                    rewrite I_mul_2_div_2 in H7.
                    clear H7.
                    destruct
                     (I_lt_dec (I_mul_2 (I_mul_2 (I_mul_2 (I_mul_2 (½x)))))
                        (½y)%I) as [H7| H7].
                     rewrite I_mul_2_div_2 in H7.
                     destruct
                      (I_lt_dec (I_mul_2 (I_div_rem_i (½x) (½y) dj1)) (½y)%I)
                      as [H8| H8].
                      simpl in H8.
                      remember (I_div_rem_i (½x) (½y) dj1) as x2 eqn:Hx2 .
Abort. (* complicated... perhaps could be continued one day...
bbb.

(* end test *)
      destruct dj3.
       destruct dj1.
        simpl in Hxj4, Hxj2, Hxj3.
        destruct (I_lt_dec (I_mul_2 (½x)) (½y)%I) as [H2| H2].
         rewrite Hx_1 in Hxj2; discriminate Hxj2.

         unfold I_ge, I_compare in H2.
         remember (fst_same (I_mul_2 (½x)) (- (½y)%I) 0) as s4 eqn:Hs4 .
         destruct s4 as [dj4| ]; [ idtac | clear H2 ].
          simpl in H2.
          rewrite Nat.sub_0_r in H2.
          remember (x .[ dj4]) as b eqn:Hxj5 .
          symmetry in Hxj5.
          destruct b; [ clear H2 | exfalso; apply H2; reflexivity ].
          apply fst_same_sym_iff in Hs4; simpl in Hs4.
          rewrite Nat.sub_0_r in Hs4.
          destruct Hs4 as (Hn4, Ht4).
          destruct dj4; [ rewrite Hx0 in Hxj5; discriminate Hxj5 | idtac ].
          simpl in Ht4.
          rewrite Nat.sub_0_r in Ht4.
          rewrite Hxj5 in Ht4.
          apply negb_sym in Ht4; simpl in Ht4.
          destruct dj4; [ rewrite Hy0 in Ht4; discriminate Ht4 | idtac ].
          destruct dj4; [ rewrite Ht3 in Ht4; discriminate Ht4 | idtac ].
          assert (2 < S (S (S dj4)))%nat as H by omega.
          apply Hn4 in H; simpl in H.
          rewrite Hxj3, Ht3 in H; simpl in H.
          discriminate H.

          apply fst_same_sym_iff in Hs4; simpl in Hs4.
          pose proof (Hs4 2%nat) as H; simpl in H.
          rewrite Hxj3, Ht3 in H; discriminate H.

        assert (2 < S (S (S dj1)))%nat as H by omega.
        apply Hn1 in H; simpl in H.
        rewrite negb_involutive in H.
        unfold I_div in H; simpl in H.
        rewrite Hm in H; simpl in H.
        apply I_lt_nge in H1.
        destruct (I_lt_dec x y) as [H3| H3]; [ idtac | contradiction ].
        apply I_lt_nge in H1.
        clear H3; rename H into Hx_2.
        simpl in Hx_2.
        unfold I_div_lt_i in Hx_2; simpl in Hx_2.
        simpl in Hx1, Hxj4, Hxj2, Hxj3.
        remember (I_mul_2 (I_div_rem_i (½x) (½y) dj1)) as x2 eqn:Hx2 .
        destruct (I_lt_dec x2 (½y)%I) as [H2| H2].
         subst x2; simpl in Hx1, Hxj4, Hxj2, Hxj3.
         remember (I_div_rem_i (½x) (½y) dj1) as x2 eqn:Hx2 .
         move Hx1 after Hn3.
         destruct (I_lt_dec (I_mul_2 (½x)) (½y)%I) as [H3| H3].
          rewrite I_mul_2_div_2 in H3.
          destruct (I_lt_dec (I_mul_2 (I_mul_2 (½x))) (½y)%I) as [H4| H4].
           rewrite I_mul_2_div_2 in H4.
           destruct dj1.
            simpl in Hx2; subst x2; simpl in Hxj2.
            rewrite Hx_2 in Hxj2; discriminate Hxj2.

            assert (3 < S (S (S (S dj1))))%nat as H by omega.
            apply Hn1 in H; simpl in H.
            rewrite negb_involutive in H.
            unfold I_div in H; simpl in H.
            rewrite Hm in H; simpl in H.
            apply I_lt_nge in H1.
            destruct (I_lt_dec x y) as [H5| H5]; [ idtac | contradiction ].
            apply I_lt_nge in H1.
            clear H5; rename H into Hx_3.
            simpl in Hx_3.
            unfold I_div_lt_i in Hx_3; simpl in Hx_3.
            simpl in Hx2.
            remember (I_mul_2 (I_div_rem_i (½x) (½y) dj1)) as x3 eqn:Hx3 .
            destruct (I_lt_dec x3 (½y)%I) as [H5| H5].
             move Hx2 at top; subst x3.
             subst x2.
             simpl in Hxj4, Hxj2, Hxj3.
             remember (I_div_rem_i (½x) (½y) dj1) as x2 eqn:Hx2 .
bbb.

(*1*)
subst y1.
clear Ht2.
revert dj2 Hn1 Hn2 Hm Hb1 Hx0 Hxj1 Hxj2; clear; intros.
(*
    Focus 1.
    remember (I_div_2 (I_div_2_pow y (S dj1))) as y1 eqn:Hy1 .
    eapply www with (n := O); try eassumption.
     simpl; intros dj Hdj.
     rewrite Hn1; [ idtac | assumption ].
     rewrite negb_involutive; reflexivity.

     intros i Hi.
     destruct i; [ assumption | exfalso; omega ].

     intros dj Hdj.
     rewrite Hn2; [ idtac | assumption ].
     rewrite negb_involutive; reflexivity.
*)
    assert (1 < S (S dj1))%nat as H by omega.
    apply Hn1 in H; simpl in H.
    rewrite negb_involutive in H.
    unfold I_div in H; simpl in H.
    rewrite Hm in H; simpl in H.
    destruct (I_lt_dec x y) as [H3| H3].
     clear H3; simpl in H.
     destruct (I_lt_dec x (I_div_2 y)) as [H3| H3]; simpl in H.
      rename H into Hx1.
      simpl in Hb1.
      remember (I_div_lt_pred_i x y dj1) as b eqn:Hb2 .
      symmetry in Hb2.
      destruct b as (b2, x2); simpl in Hb1.
      remember (I_div_2 (I_div_2_pow y dj1)) as y2 eqn:Hy2.
      destruct (I_lt_dec x2 y2) as [H4| H4].
       injection Hb1; clear Hb1; intros; subst b1 x1.
       destruct dj1.
        simpl in Hb2.
        rename Hxj1 into Hx2.
        injection Hb2; clear Hb2; intros; subst b2 x2 y2.
        clear H4.
        destruct dj2; [ rewrite Hxj2 in Hx0; discriminate Hx0 | idtac ].
        destruct dj2; [ rewrite Hxj2 in Hx1; discriminate Hx1 | idtac ].
        destruct dj2; [ rewrite Hxj2 in Hx2; discriminate Hx2 | idtac ].
        assert (2 < S (S (S dj2)))%nat as H by omega.
        apply Hn2 in H; simpl in H.
        rewrite Hx2, negb_involutive in H.
        symmetry; assumption.

(*2*)
revert Hn1 Hm Hx0 Hx1 Hxj1 Hb2 Hy2 Hn2 Hxj2; clear; intros.
(*
        Focus 1.
        remember (I_div_2 (I_div_2_pow y (2 + dj1))) as y1 eqn:Hy1 .
        eapply www with (n := 2%nat); try eassumption.
         simpl; intros dj Hdj.
         rewrite Hn1; [ idtac | assumption ].
         rewrite negb_involutive; reflexivity.

         intros i Hi.
         destruct i; [ assumption | idtac ].
         destruct i; [ assumption | exfalso; omega ].

         intros dj Hdj.
         rewrite Hn2; [ idtac | assumption ].
         rewrite Hy1, negb_involutive; reflexivity.
*)
    assert (2 < S (S (S dj1)))%nat as H by omega.
    apply Hn1 in H; simpl in H.
    rewrite negb_involutive in H.
    unfold I_div in H; simpl in H.
    rewrite Hm in H; simpl in H.
    destruct (I_lt_dec x y) as [H2| H2].
     clear H2; simpl in H.
     destruct (I_lt_dec x (I_div_2 y)) as [H2| H2]; simpl in H.
      destruct (I_lt_dec x (I_div_2 (I_div_2 y))) as [H3| H3]; simpl in H.
       rename H into Hx2.
       simpl in Hb2.
       remember (I_div_lt_pred_i x y dj1) as b eqn:Hb1 .
       symmetry in Hb1.
       destruct b as (b1, x1); simpl in Hb2.
       remember (I_div_2 (I_div_2_pow y dj1)) as y1 eqn:Hy1.
       destruct (I_lt_dec x1 y1) as [H5| H5].
        injection Hb2; clear Hb2; intros; subst b2 x2 y2.
        destruct dj1.
         simpl in Hb1.
         injection Hb1; clear Hb1; intros; subst b1 x1 y1.
         rename Hxj1 into Hx3.
         destruct dj2; [ rewrite Hxj2 in Hx0; discriminate Hx0 | idtac ].
         destruct dj2; [ rewrite Hxj2 in Hx1; discriminate Hx1 | idtac ].
         destruct dj2; [ rewrite Hxj2 in Hx2; discriminate Hx2 | idtac ].
         destruct dj2; [ rewrite Hxj2 in Hx3; discriminate Hx3 | idtac ].
         assert (3 < S (S (S (S dj2))))%nat as H by omega.
         apply Hn2 in H; simpl in H.
         rewrite Hx3, negb_involutive in H.
         symmetry; assumption.

(*3*)
revert Hn1 Hm Hx0 Hx1 Hx2 Hxj1 Hb1 Hy1 Hn2 Hxj2; clear; intros.
    assert (3 < S (S (S (S dj1))))%nat as H by omega.
    apply Hn1 in H; simpl in H.
    rewrite negb_involutive in H.
    unfold I_div in H; simpl in H.
    rewrite Hm in H; simpl in H.
    destruct (I_lt_dec x y) as [H6| H6].
     clear H6; simpl in H.
     destruct (I_lt_dec x (I_div_2 y)) as [H6| H6]; simpl in H.
      clear H6.
      destruct (I_lt_dec x (I_div_2 (I_div_2 y))) as [H6| H6];
       simpl in H.
       clear H6.
       destruct (I_lt_dec x (I_div_2 (I_div_2 (I_div_2 y))))
        as [H6| H6]; simpl in H.
        rename H into Hx3.
        simpl in Hb1.
        remember (I_div_lt_pred_i x y dj1) as b eqn:Hb2 .
        symmetry in Hb2.
        destruct b as (b2, x2); simpl in Hb1.
        remember (I_div_2 (I_div_2_pow y dj1)) as y2 eqn:Hy2.
        destruct (I_lt_dec x2 y2) as [H7| H7].
         injection Hb1; clear Hb1; intros; subst b1 x1 y1.
         destruct dj1.
          simpl in Hb2.
          injection Hb2; clear Hb2; intros; subst b2 x2 y2.
          rename Hxj1 into Hx4.
          destruct dj2; [ rewrite Hxj2 in Hx0; discriminate Hx0 | idtac ].
          destruct dj2; [ rewrite Hxj2 in Hx1; discriminate Hx1 | idtac ].
          destruct dj2; [ rewrite Hxj2 in Hx2; discriminate Hx2 | idtac ].
          destruct dj2; [ rewrite Hxj2 in Hx3; discriminate Hx3 | idtac ].
          destruct dj2; [ rewrite Hxj2 in Hx4; discriminate Hx4 | idtac ].
          assert (4 < S (S (S (S (S dj2)))))%nat as H by omega.
          apply Hn2 in H; simpl in H.
          rewrite Hx4, negb_involutive in H.
          symmetry; assumption.

          Focus 1.
bbb.
  There is a fucking induction somewhere...
  Voir www ci-dessus.
*)

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
  remember (fst_same y I_one 0) as s1 eqn:Hs1 .
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
     remember (fst_same z I_one 0) as s2 eqn:Hs2 .
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
Abort. (* complicated... perhaps could be continued one day...
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
         remember (I_div_lt_pred_i x y dj2) as bx2 eqn:Hbx2 .
         symmetry in Hbx2.
         destruct bx2 as (b2, (x2, y2)); simpl in Ht2.
         destruct (I_lt_dec x2 y2) as [H3| H3]; [ idtac | clear Ht2 ].
          discriminate Ht2.

          destruct dj2.
           simpl in Hbx2.
           injection Hbx2; clear Hbx2; intros; subst b2 x2 y2.
           apply I_lt_nge in H1.
           apply I_ge_le_iff in H3.
           contradiction.

           simpl in Hbx2.
           remember (I_div_lt_pred_i x y dj2) as bx3 eqn:Hbx3 .
           symmetry in Hbx3.
           destruct bx3 as (b3, (x3, y3)); simpl in Hbx2.
           destruct (I_lt_dec x3 y3) as [H4| H4].
            injection Hbx2; clear Hbx2; intros; subst b2 x2 y2.
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
*)

Close Scope Z_scope.
