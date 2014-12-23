(* Division in I = ℝ interval [0..1[ *)

Require Import Utf8 QArith NPeano.
Require Import Real01Add.

Set Implicit Arguments.

Open Scope Z_scope.

Definition I_mul_2 x := {| rm i := x.[S i] |}.
Arguments I_mul_2 x%I.

Definition I_div_2_inc x b :=
  {| rm i := if zerop i then b else x.[i-1] |}.
Arguments I_div_2_inc x%I _.

Fixpoint I_div_eucl_i x y i :=
  match i with
  | O => if I_lt_dec x y then (false, x) else (true, I_sub x y)
  | S i1 =>
      let r := snd (I_div_eucl_i x y i1) in
      let tr := I_mul_2 r in
      if I_lt_dec tr y then (false, tr) else (true, I_sub tr y)
  end.
Arguments I_div_eucl_i x%I y%I i%nat.

Definition I_div_rem_i x y i := snd (I_div_eucl_i x y i).
Arguments I_div_rem_i x%I y%I i%nat.

Definition I_div_i x y i := fst (I_div_eucl_i (I_mul_2 x) y i).
Arguments I_div_i x%I y%I i%nat.

Definition I_div x y := {| rm := I_div_i x y |}.
Arguments I_div x%I y%I.

Notation "x / y" := (I_div x y) : I_scope.

Fixpoint two_power n :=
  match n with
  | O => 1%nat
  | S n1 => (2 * two_power n1)%nat
  end.

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

(* *)

Theorem I_mul_2_0 : (I_mul_2 0 = 0)%I.
Proof.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
rewrite carry_diag; simpl.
rewrite carry_diag; simpl.
reflexivity.
Qed.

Add Parametric Morphism : I_mul_2
  with signature I_eq ==> I_eq
  as I_mul_2_morph.
Proof.
intros x y Hxy.
unfold I_eq in Hxy; simpl in Hxy.
unfold I_eq; simpl; intros i.
pose proof (Hxy (S i)) as H.
unfold I_add_i in H; simpl in H.
do 2 rewrite xorb_false_r in H.
unfold carry in H; simpl in H.
remember (fst_same x 0 (S (S i))) as s3 eqn:Hs3 .
remember (fst_same y 0 (S (S i))) as s4 eqn:Hs4 .
apply fst_same_sym_iff in Hs3; simpl in Hs3.
apply fst_same_sym_iff in Hs4; simpl in Hs4.
unfold I_add_i; simpl.
do 2 rewrite xorb_false_r.
unfold carry; simpl.
remember (fst_same (I_mul_2 x) 0 (S i)) as s1 eqn:Hs1 .
remember (fst_same (I_mul_2 y) 0 (S i)) as s2 eqn:Hs2 .
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

Theorem fold_I_div_rem_i : ∀ x y i,
  snd (I_div_eucl_i x y i) = I_div_rem_i x y i.
Proof. reflexivity. Qed.

Add Parametric Morphism : I_div_rem_i
  with signature I_eq ==> I_eq ==> eq ==> I_eq
  as I_div_rem_i_morph.
Proof.
intros x y Hxy z t Hzt i.
induction i.
 unfold I_div_rem_i; simpl.
 destruct (I_lt_dec x z) as [H1| H1].
  destruct (I_lt_dec y t) as [H2| H2]; [ assumption | idtac ].
  rewrite Hxy, Hzt in H1.
  apply I_lt_nge in H1.
  apply I_ge_le_iff in H2; contradiction.

  rewrite Hxy, Hzt in H1.
  apply I_ge_le_iff in H1.
  destruct (I_lt_dec y t) as [H2| H2].
   apply I_lt_nge in H2; contradiction.

   simpl.
   rewrite Hxy, Hzt; reflexivity.

 unfold I_div_rem_i; simpl.
 do 2 rewrite fold_I_div_rem_i.
 remember (I_div_rem_i x z i) as d1 eqn:Hd1 .
 remember (I_div_rem_i y t i) as d2 eqn:Hd2 .
 destruct (I_lt_dec (I_mul_2 d1) z) as [H1| H1]; simpl.
  destruct (I_lt_dec (I_mul_2 d2) t) as [H2| H2]; simpl.
   rewrite IHi; reflexivity.

   rewrite IHi, Hzt in H1.
   apply I_ge_le_iff in H2.
   apply I_lt_nge in H1; contradiction.

  destruct (I_lt_dec (I_mul_2 d2) t) as [H2| H2]; simpl.
   rewrite IHi, Hzt in H1.
   apply I_ge_le_iff in H1.
   apply I_lt_nge in H2; contradiction.

   rewrite IHi, Hzt; reflexivity.
Qed.

Theorem I_div_rem_i_0_l : ∀ x i, (x ≠ 0)%I → (I_div_rem_i 0 x i = 0)%I.
Proof.
intros x i Hx.
induction i.
 unfold I_div_rem_i; simpl.
 destruct (I_lt_dec 0%I x) as [H1| H1]; [ reflexivity | idtac ].
 apply I_ge_le_iff, I_le_0_r in H1; contradiction.

 unfold I_div_rem_i; simpl.
 rewrite fold_I_div_rem_i.
 remember (I_mul_2 (I_div_rem_i 0 x i)) as y eqn:Hy .
 destruct (I_lt_dec y x) as [H1| H1]; simpl.
  subst y.
  rewrite IHi.
  apply I_mul_2_0.

  subst y.
  rewrite IHi, I_mul_2_0 in H1.
  apply I_ge_le_iff, I_le_0_r in H1; contradiction.
Qed.

Add Parametric Morphism : I_div_2_inc
  with signature I_eq ==> eq ==> I_eq
  as I_div_2_inc_morph.
Proof.
intros x y Hxy b.
unfold I_eq; simpl; intros i.
pose proof (Hxy i) as H; simpl in H.
unfold I_add_i in H; simpl in H.
unfold I_add_i; simpl.
do 2 rewrite xorb_false_r in H.
do 2 rewrite xorb_false_r.
rename H into Hi.
destruct i; simpl.
 f_equal.
 unfold carry; simpl.
 remember (fst_same (I_div_2_inc x b) 0 1) as s1 eqn:Hs1 .
 remember (fst_same (I_div_2_inc y b) 0 1) as s2 eqn:Hs2 .
 destruct s1 as [dj1| ].
  rewrite Nat.sub_0_r.
  remember Hs1 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn1, Ht1); rewrite Nat.sub_0_r in Ht1.
  rewrite Ht1.
  destruct s2 as [dj2| ].
   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn2, Ht2); rewrite Ht2; reflexivity.

   exfalso.
   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rename H into Hn2.
   pose proof (Hn2 dj1) as Hy1.
   rewrite Nat.sub_0_r in Hy1.
   remember Hy1 as H; clear HeqH.
   symmetry in Hxy.
   eapply I_eq_neq_if in H; try eassumption.
   destruct H as [(Hyi, Hxi)| (Hyi, Hxi)]; simpl in Hxi, Hyi.
    unfold carry in Hi; simpl in Hi.
    remember (fst_same x 0 1) as s3 eqn:Hs3 .
    remember (fst_same y 0 1) as s4 eqn:Hs4 .
    destruct s3 as [dj3| ].
     remember Hs3 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn3, Ht3).
     rewrite Ht3, xorb_false_r in Hi.
     destruct s4 as [dj4| ].
      remember Hs4 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn4, Ht4).
      rewrite Ht4, xorb_false_r in Hi.
      destruct dj1.
       rewrite Ht1, Hy1 in Hi; discriminate Hi.

       destruct (lt_eq_lt_dec dj1 dj3) as [[H1| H1]| H1].
        rewrite Hn3 in Ht1; [ discriminate Ht1 | assumption ].

        subst dj3.
        pose proof (Hn2 (S dj4)) as H.
        rewrite Nat.sub_0_r, Ht4 in H; discriminate H.
bbb.

Theorem I_div_0_l : ∀ x, (x ≠ 0)%I → (0 / x = 0)%I.
Proof.
intros x Hx.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
rewrite carry_diag; simpl.
rewrite xorb_false_r.
unfold I_div_i; simpl.
unfold carry; simpl.
remember (fst_same (0 / x) 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1| ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Ht1, xorb_false_r.
 clear dj1 Hn1 Ht1.
 destruct i; simpl.
  destruct (I_lt_dec (I_mul_2 0) x) as [H1| H1]; [ reflexivity | exfalso ].
  rewrite I_mul_2_0 in H1.
  apply I_ge_le_iff in H1.
  apply I_le_0_r in H1; contradiction.

  remember (I_mul_2 0) as r1.
  remember (I_div_eucl_i r1 x i) as r2.
  remember (I_mul_2 (snd r2)) as r3.
  destruct (I_lt_dec r3 x) as [H1| H1]; [ reflexivity | exfalso ].
  apply I_ge_le_iff in H1.
  subst r3 r2 r1.
  unfold I_le in H1.
  apply H1; clear H1.
  apply I_gt_lt_iff.
  rewrite fold_I_div_rem_i, I_mul_2_0.
  rewrite I_div_rem_i_0_l, I_mul_2_0; [ idtac | assumption ].
  apply I_lt_nge; intros H.
  apply I_le_0_r in H; contradiction.

 exfalso.
 pose proof (Hs1 O) as H.
 rewrite Nat.add_0_r in H.
 unfold I_div_i in H.
 simpl in H.
 rewrite fold_I_div_rem_i in H.
 remember (I_div_rem_i (I_mul_2 0) x i) as y.
 destruct (I_lt_dec (I_mul_2 y) x) as [H1| H1]; [ discriminate H | idtac ].
 subst y.
 rewrite I_mul_2_0 in H1.
 rewrite I_div_rem_i_0_l in H1; [ idtac | assumption ].
 rewrite I_mul_2_0 in H1.
 apply I_ge_le_iff in H1.
 apply I_le_0_r in H1; contradiction.
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

Close Scope Z_scope.
