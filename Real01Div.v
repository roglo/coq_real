(* Division in I = ℝ interval [0..1[ *)

Require Import Utf8 QArith NPeano.
Require Import Real01Add Real01Cmp.

Set Implicit Arguments.

Open Scope Z_scope.

(*
Definition I_mul_2 x := {| rm i := x.[S i] |}.
Arguments I_mul_2 x%I.

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
*)

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

Definition I_div_2 x := {| rm i := if zerop i then false else x.[i-1] |}.

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

(*
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
*)

Theorem I_div_lt_pred_0_l : ∀ x y b x1 y1 i,
  I_div_lt_pred_i x y i = (b, (x1, y1))
  → (x == 0)%I
  → (x1 = 0)%I.
Proof.
intros x y b x1 y1 i Hi Hx.
apply I_eqs_eq.
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
  destruct s2 as [j| ]; [ destruct x2 .[ j]; discriminate H | idtac ].
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

Theorem I_div_2_eq_0 : ∀ x, (I_div_2 x = 0)%I → (x = 0)%I.
Proof.
intros x Hx.
apply I_zero_iff in Hx.
destruct Hx as [Hx| Hx].
 apply I_zero_iff.
 left; intros i.
 simpl in Hx.
 pose proof (Hx (S i)) as H; simpl in H.
 rewrite Nat.sub_0_r in H; assumption.

 pose proof (Hx O) as H; discriminate H.
Qed.

Theorem I_div_lt_pred_r_eq_0 : ∀ x y i b x1 y1,
  I_div_lt_pred_i x y i = (b, (x1, y1))
  → (y1 = 0)%I
  → (y = 0)%I.
Proof.
intros x y i b x1 y1 Hi Hy.
revert x y b x1 y1 Hi Hy.
induction i; intros; simpl in Hi.
 injection Hi; clear Hi; intros; subst b x1 y1.
 apply I_div_2_eq_0; assumption.

 remember (I_div_lt_pred_i x y i) as bxy eqn:Hbxy .
 symmetry in Hbxy.
 destruct bxy as (b2, (x2, y2)).
 simpl in Hi.
 destruct (I_lt_dec x2 y2) as [H1| H1].
  injection Hi; clear Hi; intros; subst b x1 y1.
  apply I_div_2_eq_0 in Hy.
  eapply IHi; eassumption.

  injection Hi; clear Hi; intros; subst b x1 y1.
  apply I_div_2_eq_0 in Hy.
  eapply IHi; eassumption.
Qed.

Theorem I_div_0_l : ∀ x, (x ≠≠ 0)%I → (0 / x = 0)%I.
Proof.
intros x Hx.
unfold I_eqs, I_compare in Hx.
remember (fst_same x (- 0%I) 0) as s1 eqn:Hs1 .
destruct s1 as [dj1| ]; [ clear Hx | exfalso; apply Hx; reflexivity ].
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
rewrite carry_diag; simpl.
rewrite xorb_false_r.
unfold carry; simpl.
remember (fst_same (0 / x) 0 (S i)) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s2 as [dj2| ].
 destruct Hs2 as (Hn2, Ht2).
 rewrite Ht2, xorb_false_r.
 unfold I_div; simpl.
 remember (I_div_max_iter_int x) as m eqn:Hm .
 symmetry in Hm.
 destruct m; [ reflexivity | simpl ].
 destruct (I_lt_dec 0%I x) as [H1| H1]; simpl.
  remember (I_div_lt_pred_i 0 x i) as bxy eqn:Hbxy .
  symmetry in Hbxy.
  destruct bxy as (b, (x1, y1)); simpl.
  destruct (I_lt_dec x1 y1) as [H2| H2]; [ reflexivity | exfalso ].
  remember Hbxy as H; clear HeqH.
  apply I_div_lt_pred_0_l in H; [ idtac | reflexivity ].
bbb.

  apply I_div_lt_pred_0_l in H; [ idtac | reflexivity ].
  rewrite H in H2.
  apply I_ge_le_iff, I_le_0_r in H2.
  apply I_div_lt_pred_r_eq_0 in Hbxy; [ contradiction | assumption ].

  apply I_ge_le_iff, I_le_0_r in H1; contradiction.

 pose proof (Hs1 O) as H; simpl in H.
 unfold I_div in H; simpl in H.
 remember (I_div_max_iter_int x) as m eqn:Hm .
 symmetry in Hm.
 destruct m; [ discriminate H | simpl in H ].
 destruct (I_lt_dec 0%I x) as [H1| H1]; simpl in H.
  rewrite Nat.add_0_r in H.
  remember (I_div_lt_pred_i 0 x i) as bxy eqn:Hbxy .
  symmetry in Hbxy.
  destruct bxy as (b, (x1, y1)); simpl in H.
  remember Hbxy as Hi; clear HeqHi.
  apply I_div_lt_pred_0_l in Hi; [ idtac | reflexivity ].
  destruct (I_lt_dec x1 y1) as [H2| H2]; simpl in H.
   destruct (I_lt_dec x1 (I_div_2 y1)) as [H3| H3].
    discriminate H.

    clear H.
    rewrite Hi in H2, H3.
    apply I_ge_le_iff, I_le_0_r in H3.
    apply I_div_2_eq_0 in H3.
    rewrite H3 in H2.
    exfalso; revert H2; apply I_lt_irrefl.

   rewrite Hi in H2.
   apply I_ge_le_iff, I_le_0_r in H2.
   destruct (I_lt_dec (x1 - y1)%I (I_div_2 y1)) as [H3| H3].
    discriminate H.

    clear H.
    apply I_div_lt_pred_r_eq_0 in Hbxy; [ contradiction | assumption ].

  apply I_ge_le_iff, I_le_0_r in H1; contradiction.
Qed.

Close Scope Z_scope.
