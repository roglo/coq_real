(* Division in I = ℝ interval [0..1[ *)

Require Import Utf8 QArith NPeano.
Require Import Real01Add Real01Cmp.

Set Implicit Arguments.

Open Scope Z_scope.

Fixpoint two_power n :=
  match n with
  | O => 1%nat
  | S n1 => (2 * two_power n1)%nat
  end.

Definition I_div_max_iter_int y :=
  match fst_same y I_ones 0 with
  | Some j => two_power (S j)
  | None => O
  end.
Arguments I_div_max_iter_int y%I.

Definition I_div_2_inc x b :=
  {| rm i := if zerop i then b else x.[i-1] |}.
Arguments I_div_2_inc x%I _.

Definition I_div_2 x := I_div_2_inc x false.
Arguments I_div_2 x%I.

Fixpoint I_div_lt_pred_i x y i :=
  match i with
  | O => (false, (x, I_div_2 y))
  | S i1 =>
      let (x1, y1) := snd (I_div_lt_pred_i x y i1) in
      if I_lt_dec x1 y1 then
        (false, (x1, I_div_2 y1))
      else
        (true, (I_sub x1 y1, I_div_2 y1))
  end.
Arguments I_div_lt_pred_i x%I y%I i%nat.

Definition I_div_lt x y := {| rm i := fst (I_div_lt_pred_i x y (S i)) |}.
Arguments I_div_lt x%I y%I.

Fixpoint I_div_lim m x y :=
  match m with
  | O => (O, I_zero)
  | S m1 =>
      if I_lt_dec x y then
        (O, I_div_lt x y)
      else
        let (xi, xf) := I_div_lim m1 (I_sub x y) y in
        (S xi, xf)
  end.
Arguments I_div_lim m%nat x%I y%I.

Definition I_div x y := snd (I_div_lim (I_div_max_iter_int y) x y).
Arguments I_div x%I y%I.

Notation "x / y" := (I_div x y) : I_scope.

(* *)

Theorem I_div_lt_pred_0_l : ∀ x y b x1 y1 i,
  I_div_lt_pred_i x y i = (b, (x1, y1))
  → (x == 0)%I
  → (x1 == 0)%I.
Proof.
intros x y b x1 y1 i Hi Hx.
revert x y b x1 y1 Hi Hx.
induction i; intros; simpl in Hi.
 injection Hi; intros; subst; assumption.

 remember (I_div_lt_pred_i x y i) as bxy eqn:Hbxy .
 symmetry in Hbxy.
 destruct bxy as (b2, (x2, y2)).
 simpl in Hi.
 destruct (I_lt_dec x2 y2) as [H1| H1].
  injection Hi; clear Hi; intros; subst b x1 y1.
  eapply IHi; eassumption.

  injection Hi; clear Hi; intros; subst b x1 y1.
  remember Hbxy as H; clear HeqH.
  apply IHi in H; try assumption.
  rewrite H in H1.
  apply I_ge_le_iff, I_le_0_r in H1.
  unfold I_eqs, I_compare; simpl.
  remember (fst_same (x2 - y2) (- 0%I) 0) as s1 eqn:Hs1 .
  destruct s1 as [j1| ]; [ exfalso | reflexivity ].
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, Ht1).
  unfold I_add_i in Ht1; simpl in Ht1.
  apply I_zero_iff in H1.
  unfold I_eqs, I_compare in H.
  remember (fst_same x2 (- 0%I) 0) as s2 eqn:Hs2 .
  destruct s2 as [j| ]; [ destruct (x2 .[ j]); discriminate H | idtac ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  clear H.
  rewrite Hs2, xorb_false_l in Ht1.
  unfold carry in Ht1; simpl in Ht1.
  remember (fst_same x2 (- y2) (S j1)) as s3 eqn:Hs3 .
  destruct s3 as [dj3| ].
   apply fst_same_sym_iff in Hs3; simpl in Hs3.
   destruct Hs3 as (Hn3, Ht3).
   rewrite Hs2, xorb_false_r in Ht1.
   destruct H1 as [H1| H1].
    rewrite Hs2, H1 in Ht3; discriminate Ht3.

    rewrite H1 in Ht1; discriminate Ht1.

   apply fst_same_sym_iff in Hs3; simpl in Hs3.
   destruct H1 as [H1| H1].
    rewrite H1 in Ht1; discriminate Ht1.

    pose proof (Hs3 O) as H.
    rewrite H1, Hs2 in H; discriminate H.
Qed.

Theorem I_add_i_diag : ∀ x i, I_add_i x x i = x.[S i].
Proof.
intros x i.
unfold I_add_i; simpl.
rewrite xorb_nilpotent, carry_diag, xorb_false_l.
reflexivity.
Qed.

Theorem I_zero_iff2 : ∀ x, (x = 0)%I ↔ (x == 0)%I ∨ (∀ j, x.[j] = true).
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
  rewrite Hx in Ht1; discriminate Ht1.

  right; assumption.

 apply I_zero_iff.
 destruct Hx as [Hx| Hx].
  left; intros i.
  unfold I_eqs, I_compare in Hx; simpl in Hx.
  remember (fst_same x (- 0%I) 0) as s1 eqn:Hs1 .
  destruct s1 as [dj1| ]; [ idtac | clear Hx ].
   destruct (x .[ dj1]); discriminate Hx.

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

Theorem I_div_lt_pred_r_eqs_0 : ∀ x y i b x1 y1,
  I_div_lt_pred_i x y i = (b, (x1, y1))
  → (y1 == 0)%I
  → (y == 0)%I.
Proof.
intros x y i b x1 y1 Hi Hy.
revert x y b x1 y1 Hi Hy.
induction i; intros; simpl in Hi.
 injection Hi; clear Hi; intros; subst b x1 y1.
 apply I_div_2_eqs_0; assumption.

 remember (I_div_lt_pred_i x y i) as bxy eqn:Hbxy .
 symmetry in Hbxy.
 destruct bxy as (b2, (x2, y2)).
 simpl in Hi.
 destruct (I_lt_dec x2 y2) as [H1| H1].
  injection Hi; clear Hi; intros; subst b x1 y1.
  apply I_div_2_eqs_0 in Hy.
  eapply IHi; eassumption.

  injection Hi; clear Hi; intros; subst b x1 y1.
  apply I_div_2_eqs_0 in Hy.
  eapply IHi; eassumption.
Qed.

Theorem I_div_0_l : ∀ x, (x ≠≠ 0)%I → (0 / x == 0)%I.
Proof.
intros x Hx.
unfold I_eqs, I_compare in Hx.
unfold I_eqs, I_compare.
remember (fst_same (0 / x) (- 0%I) 0) as s1 eqn:Hs1 .
destruct s1 as [j1| ]; [ exfalso | reflexivity ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Hs1).
unfold I_div in Hs1; simpl in Hs1.
remember (I_div_max_iter_int x) as m eqn:Hm .
symmetry in Hm.
destruct m; [ discriminate Hs1 | simpl in Hs1 ].
destruct (I_lt_dec 0%I x) as [H2| H2].
 simpl in Hs1.
 remember (I_div_lt_pred_i 0 x j1) as bxy eqn:Hbxy .
 symmetry in Hbxy.
 destruct bxy as (b, (x1, y1)); simpl in Hs1.
 destruct (I_lt_dec x1 y1) as [H3| H3]; [ discriminate Hs1 | clear Hs1 ].
 remember (fst_same x (- 0%I) 0) as s2 eqn:Hs2 .
 destruct s2 as [j2| ].
  clear Hx.
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  remember Hbxy as H; clear HeqH.
  apply I_div_lt_pred_0_l in H; [ idtac | reflexivity ].
  rewrite H in H3.
  apply I_ge_le_iff, I_le_0_r_eqs_iff in H3.
  apply I_div_lt_pred_r_eqs_0 in Hbxy; [ idtac | assumption ].
  rewrite Hbxy in H2.
  revert H2; apply I_lt_irrefl.

  apply Hx; reflexivity.

 remember (fst_same x (- 0%I) 0) as s2 eqn:Hs2 .
 destruct s2 as [j2| ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  apply I_ge_le_iff, I_le_0_r_eqs_iff in H2.
  rewrite I_zero_eqs_iff in H2.
  rewrite H2 in Ht2; discriminate Ht2.

  apply Hx; reflexivity.
Qed.

Add Parametric Morphism : I_div_2
  with signature I_eqs ==> I_eqs
  as I_div_2_morph.
Proof.
intros x y Hxy.
unfold I_eqs, I_compare in Hxy.
unfold I_eqs, I_compare; simpl.
remember (fst_same (I_div_2 x) (- I_div_2 y) 0) as s1 eqn:Hs1 .
remember (fst_same x (- y) 0) as s2 eqn:Hs2 .
destruct s1 as [dj1| ]; [ exfalso | reflexivity ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
destruct dj1; [ discriminate Ht1 | simpl in Ht1 ].
rewrite Nat.sub_0_r in Ht1.
destruct s2 as [dj2| ]; [ idtac | clear Hxy ].
 destruct (x .[ dj2]); discriminate Hxy.

 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 rewrite Hs2, negb_involutive in Ht1.
 symmetry in Ht1.
 revert Ht1; apply no_fixpoint_negb.
Qed.

Close Scope Z_scope.
