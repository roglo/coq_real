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

Definition I_mul_2 x := {| rm i := x.[S i] |}.
Arguments I_mul_2 x%I.

(*
Fixpoint I_div_2_pow x n :=
  match n with
  | O => x
  | S n1 => I_div_2 (I_div_2_pow x n1)
  end.
Arguments I_div_2_pow x%I n%nat.

Fixpoint I_div_lt_pred_i x y i :=
  match i with
  | O => (false, x)
  | S i1 =>
      let x1 := snd (I_div_lt_pred_i x y i1) in
      if I_lt_dec x1 (I_div_2_pow y i) then
        (false, x1)
      else
        (true, I_sub x1 (I_div_2_pow y i))
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
*)

Fixpoint I_div_rem_i x y i :=
  match i with
  | O => x
  | S i1 =>
      let x1 := I_mul_2 (I_div_rem_i x y i1) in
      if I_lt_dec x1 y then x1 else (x1 - y)%I
  end.
Arguments I_div_rem_i x%I y%I i%nat.

Definition I_div_lt_i x y i :=
  if I_lt_dec (I_mul_2 (I_div_rem_i x y i)) y then false else true.
Arguments I_div_lt_i x%I y%I i%nat.

Definition I_div_lt x y := {| rm := I_div_lt_i (I_div_2 x) (I_div_2 y) |}.
Arguments I_div_lt x%I y%I.

Fixpoint I_div_int m x y :=
  match m with
  | O => O
  | S m1 =>
      if I_lt_dec x y then O
      else S (I_div_int m1 (I_sub x y) y)
  end.
Arguments I_div_int m%nat x%I y%I.

Fixpoint I_div_frac m x y :=
  match m with
  | O => 0%I
  | S m1 =>
      if I_lt_dec x y then I_div_lt x y
      else I_div_frac m1 (I_sub x y) y
  end.
Arguments I_div_frac m%nat x%I y%I.

Definition I_div x y := I_div_frac (I_div_max_iter_int y) x y.
Arguments I_div x%I y%I.

Notation "x / y" := (I_div x y) : I_scope.

(* *)

(*
Theorem I_div_lt_pred_0_l : ∀ x y b x1 i,
  I_div_lt_pred_i x y i = (b, x1)
  → (x == 0)%I
  → (x1 == 0)%I.
Proof.
intros x y b x1 i Hi Hx.
revert x y b x1 Hi Hx.
induction i; intros; simpl in Hi.
 injection Hi; intros; subst; assumption.

 remember (I_div_lt_pred_i x y i) as bx eqn:Hbx .
 symmetry in Hbx.
 destruct bx as (b2, x2); simpl in Hi.
 remember (I_div_2 (I_div_2_pow y i)) as y2 eqn:Hy2.
 destruct (I_lt_dec x2 y2) as [H1| H1].
  injection Hi; clear Hi; intros; subst b x1.
  eapply IHi; eassumption.

  injection Hi; clear Hi; intros; subst b x1.
  remember Hbx as H; clear HeqH.
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
*)

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

(*
Theorem I_div_2_pow_eqs_0 : ∀ x n, (I_div_2_pow x n == 0)%I → (x == 0)%I.
Proof.
intros x n Hx.
revert x Hx.
induction n; intros; [ assumption | idtac ].
simpl in Hx.
apply I_div_2_eqs_0 in Hx.
apply IHn; assumption.
Qed.
*)

Theorem two_power_neq_0 : ∀ n, two_power n ≠ O.
Proof.
intros n H.
induction n; [ discriminate H | simpl in H ].
rewrite Nat.add_0_r in H.
apply Nat.eq_add_0 in H.
destruct H as (H, _).
apply IHn; assumption.
Qed.

(*
Theorem I_div_lt_pred_r_eqs_0 : ∀ x y i b x1,
  I_div_lt_pred_i x y i = (b, x1)
  → (y1 == 0)%I
  → (y == 0)%I.
Proof.
intros x y i b x1 y1 Hi Hy.
revert x y b x1 y1 Hi Hy.
induction i; intros; simpl in Hi.
 injection Hi; clear Hi; intros; subst b x1 y1.
 apply I_div_2_eqs_0; assumption.

 remember (I_div_lt_pred_i x y i) as bx eqn:Hbx .
 symmetry in Hbx.
 destruct bx as (b2, (x2, y2)).
 simpl in Hi.
 destruct (I_lt_dec x2 y2) as [H1| H1].
  injection Hi; clear Hi; intros; subst b x1 y1.
  apply I_div_2_eqs_0 in Hy.
  eapply IHi; eassumption.

  injection Hi; clear Hi; intros; subst b x1 y1.
  apply I_div_2_eqs_0 in Hy.
  eapply IHi; eassumption.
Qed.
*)

Add Parametric Morphism : I_mul_2
  with signature I_eqs ==> I_eqs
  as I_mul_2_morph.
Proof.
intros x y Hxy.
rewrite I_eqs_iff in Hxy.
apply I_eqs_iff.
intros i; apply Hxy.
Qed.

Theorem I_mul_2_0 : (I_mul_2 0 == 0)%I.
Proof.
apply I_zero_eqs_iff; intros j; reflexivity.
Qed.

Theorem I_div_rem_i_0_l : ∀ y i, (I_div_rem_i 0 y i == 0)%I.
Proof.
intros y i.
revert y.
induction i; intros; [ reflexivity | simpl ].
remember (I_mul_2 (I_div_rem_i 0 y i)) as x1 eqn:Hx1 .
destruct (I_lt_dec x1 y) as [H1| H1].
 rewrite Hx1, IHi.
 apply I_mul_2_0.

 subst x1.
 rewrite IHi, I_mul_2_0 in H1.
 rewrite IHi, I_mul_2_0.
 apply I_ge_le_iff, I_le_0_r_eqs_iff in H1.
 rewrite H1.
 apply I_sub_diag_eqs.
Qed.

(* division by 0 is 0 here *)
Theorem I_div_0_r : ∀ x y, (y == 0)%I → (x / y == 0)%I.
Proof.
intros x y Hy.
rewrite I_eqs_iff in Hy; simpl in Hy.
apply I_eqs_iff; simpl; intros i.
unfold I_div; simpl.
remember (I_div_max_iter_int y) as m eqn:Hm .
symmetry in Hm.
unfold I_div_max_iter_int in Hm.
remember (fst_same y I_ones 0) as s2 eqn:Hs2 .
destruct s2 as [dj2| ].
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct Hs2 as (Hn2, Ht2).
 rewrite Hy in Ht2; discriminate Ht2.

 subst m; reflexivity.
Qed.

Theorem I_div_0_l : ∀ x, (0 / x == 0)%I.
Proof.
intros x.
bbb.
destruct (I_eqs_dec x 0%I) as [Hx| Hx].
 apply I_div_0_r; assumption.

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
  unfold I_div_lt_i in Hs1.
  remember (I_div_rem_i 0 x j1) as x1 eqn:Hx1 .
  remember (I_div_2_pow x (S j1)) as y1 eqn:Hy1 .
  destruct (I_lt_dec x1 y1) as [H1| H1]; [ discriminate Hs1 | clear Hs1 ].
  subst x1 y1.
  rewrite I_div_rem_i_0_l in H1.
  apply I_ge_le_iff, I_le_0_r_eqs_iff in H1.
  apply I_div_2_pow_eqs_0 in H1.
  rewrite H1 in H2; revert H2; apply I_lt_irrefl.

  apply I_ge_le_iff, I_le_0_r_eqs_iff in H2.
  contradiction.
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

(* mmm... marche pas, j'ai dû me gourer quelque part...
Theorem www : ∀ x y b2 x2 y2 dj1 dj2 m n,
  (∀ dj, (dj < S (S (n + dj1)))%nat
   → x.[dj] = if zerop dj then false else (x / y)%I.[dj-1])
  → I_div_max_iter_int y = S m
  → (∀ i, (i < S n)%nat → x.[i] = false)
  → x .[ S (S (n + dj1))] = false
  → I_div_lt_pred_i x y (S dj1) = (b2, x2)
  → y2 = I_div_2 (I_div_2_pow y (S (n + dj1)))
  → (∀ dj, (dj < dj2)%nat → x2.[dj] = y2.[ dj])
  → x2 .[ dj2] = true
  → y .[ 0] = false.
Proof.
intros x y b2 x2 y2 dj1 dj2 m n.
intros Hn1 Hm Hxi Hxj1 Hb1 Hy2 Hn2 Hxj2.
assert (S n < S (S (n + dj1)))%nat as H by omega.
apply Hn1 in H; simpl in H.
rewrite Nat.sub_0_r in H.
unfold I_div in H; simpl in H.
rewrite Hm in H; simpl in H.
destruct (I_lt_dec x y) as [H3| H3].
 clear H3; simpl in H.
 remember (snd (I_div_lt_pred_i x y n)) as x1 eqn:Hx1 .
 remember (I_div_2 (I_div_2_pow y n)) as y1 eqn:Hy1 .
 destruct (I_lt_dec x1 y1) as [H3| H3]; simpl in H.
  rename H into Hxn.
  simpl in Hb1.
  remember (I_div_lt_pred_i x y dj1) as b eqn:Hb2 .
  symmetry in Hb2.
  destruct b as (b3, x3); simpl in Hb1.
  remember (I_div_2 (I_div_2_pow y dj1)) as y3 eqn:Hy3 .
  destruct (I_lt_dec x3 y3) as [H4| H4].
   injection Hb1; clear Hb1; intros; subst b2 x2.
   destruct dj1.
    simpl in Hb2.
    rename Hxj1 into Hx2.
    injection Hb2; clear Hb2; intros; subst b3 x3.
    destruct dj2.
     rewrite Hxi in Hxj2; [ discriminate Hxj2 | apply Nat.lt_0_succ ].

     assert (0 < S dj2)%nat as H by apply Nat.lt_0_succ.
     apply Hn2 in H; simpl in H.
     rewrite Hxi in H; [ idtac | apply Nat.lt_0_succ ].
     rewrite Hy2 in H; simpl in H.
bbb.
*)

(* second try, fail again, same reason...
Theorem www : ∀ x y b2 x2 y2 dj1 dj2 m n,
  (∀ dj, (dj < S (n + dj1))%nat
   → x .[ dj] = if zerop dj then false else (x / y)%I .[ dj - 1])
  → I_div_max_iter_int y = S m
  → (∀ i, (i < n)%nat → x.[i] = false)
  → x .[S (n + dj1)] = false
  → I_div_lt_pred_i x y (S dj1) = (b2, x2)
  → y2 = I_div_2 (I_div_2_pow y (n + dj1))
  → (∀ dj, (dj < dj2)%nat → x2.[dj] = y2.[ dj])
  → x2 .[ dj2] = true
  → y .[ 0] = false.
Proof.
intros x y b2 x2 y2 dj1 dj2 m n.
intros Hn1 Hm Hxi Hxj1 Hb2 Hy2 Hn2 Hxj2.
simpl in Hb2.
remember (I_div_2 (I_div_2_pow y dj1)) as y1 eqn:Hy1 .
remember (snd (I_div_lt_pred_i x y dj1)) as x1 eqn:Hx1 .
destruct (I_lt_dec x1 y1) as [H1| H1].
 injection Hb2; clear Hb2; intros; subst b2 x2.
 pose proof (Hn1 O (Nat.lt_0_succ (n + dj1))) as H; simpl in H.
 rename H into Hx0.
 destruct dj1.
  simpl in Hx1; subst x1.
  destruct dj2; [ rewrite Hxj2 in Hx0; discriminate Hx0 | idtac ].
  pose proof (Hn2 O (Nat.lt_0_succ dj2)) as H.
  rewrite Hx0, Hy2 in H; simpl in H.
*)

(*
Theorem www : ∀ x y b2 x2 y2 dj1 dj2 m n,
  (∀ dj, (dj < S (S (S (n + dj1))))%nat
   → x.[dj] = if zerop dj then false else (x / y)%I .[ dj - 1])
  → I_div_max_iter_int y = S m
  → (∀ i, (i < S (S n))%nat → x.[i] = false)
  → x .[ S (S (S (n + dj1)))] = false
  → I_div_lt_pred_i x y (S dj1) = (b2, x2)
  → y2 = I_div_2 (I_div_2_pow y (S dj1))
  → (∀ dj, (dj < dj2)%nat
      → x2 .[ dj] = I_div_2 (I_div_2_pow y (S (S (n + dj1)))).[ dj])
  → x2 .[ dj2] = true
  → y .[ 0] = false.
Proof.
intros x y b2 x2 y2 dj1 dj2 m n.
intros Hn1 Hm Hxi Hxj1 Hb2 Hy2 Hn2 Hxj2.
bbb.

destruct n.
 simpl in Hn1, Hxj1.
 assert (2 < S (S (S dj1)))%nat as H by omega.
 apply Hn1 in H; simpl in H.
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
    remember (I_div_2 (I_div_2_pow y dj1)) as y1 eqn:Hy1 .
    destruct (I_lt_dec x1 y1) as [H5| H5].
     injection Hb2; clear Hb2; intros; subst b2 x2 y2.
     revert dj2 Hn1 Hn2 Hm Hb1 Hxi Hx2 Hxj1 Hxj2; clear; intros.
     revert x y m b1 x1 dj2 Hn1 Hn2 Hm Hb1 Hxi Hx2 Hxj1 Hxj2.
     induction dj1; intros.
      simpl in Hb1.
      injection Hb1; clear Hb1; intros; subst b1 x1.
      rename Hxj1 into Hx3.
      destruct dj2; [ rewrite Hxi in Hxj2; auto; discriminate Hxj2 | idtac ].
      destruct dj2; [ rewrite Hxi in Hxj2; auto; discriminate Hxj2 | idtac ].
      destruct dj2; [ rewrite Hx2 in Hxj2; discriminate Hxj2 | idtac ].
      destruct dj2; [ rewrite Hx3 in Hxj2; discriminate Hxj2 | idtac ].
      assert (3 < S (S (S (S dj2))))%nat as H by omega.
      apply Hn2 in H; simpl in H.
      rewrite Hx3 in H.
      symmetry; assumption.

      Focus 1.
bbb.
*)

(*
Theorem www : ∀ x y b1 x1 dj1 dj2 m n,
  (∀ dj, (dj < S (S (n + dj1)))%nat
   → x .[ dj] = if zerop dj then false else (x / y)%I .[ dj - 1])
  → I_div_max_iter_int y = S m
  → (∀ i, (i < S (S (S (S n))))%nat → x.[i] = false)
  → I_div_lt_pred_i x y dj1 = (b1, x1)
  → (∀ dj, (dj < dj2)%nat
     → x1.[dj] = I_div_2 (I_div_2_pow y (S (n + dj1))).[dj])
  → x1.[dj2] = true
  → y.[0] = false.
Proof.
intros x y b1 x1 dj1 dj2 m n Hn1 Hm Hxi Hb1 Hn2 Hxj2.
induction dj1.
 simpl in Hb1.
 injection Hb1; clear Hb1; intros; subst b1 x1.
 assert (0 < S (S (S (S n))))%nat as H by omega.
 destruct dj2; [ rewrite Hxi in Hxj2; auto; discriminate Hxj2 | idtac ].
 clear H.
 assert (1 < S (S (S (S n))))%nat as H by omega.
 destruct dj2; [ rewrite Hxi in Hxj2; auto; discriminate Hxj2 | idtac ].
 clear H.
 assert (2 < S (S (S (S n))))%nat as H by omega.
 destruct dj2; [ rewrite Hxi in Hxj2; auto; discriminate Hxj2 | idtac ].
 clear H.
 assert (3 < S (S (S (S n))))%nat as H by omega.
 destruct dj2; [ rewrite Hxi in Hxj2; auto; discriminate Hxj2 | idtac ].
 clear H.
 assert (3 < S (S (S (S dj2))))%nat as H by omega.
 apply Hn2 in H; simpl in H.
 rewrite Nat.add_0_r in H.
bbb.
*)

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
bbb.
  remember (I_div_lt_pred_i x y dj1) as bx1 eqn:Hb1 .
  symmetry in Hb1.
  destruct bx1 as (b1, x1); simpl in Ht1.
  remember (I_div_2 (I_div_2_pow y dj1)) as y1 eqn:Hy1.
  destruct (I_lt_dec x1 y1) as [H2| H2]; [ discriminate Ht1 | clear Ht1 ].
  unfold I_ge, I_compare in H2.
  remember (fst_same x1 (- y1) 0) as s2 eqn:Hs2 .
  destruct s2 as [dj2| ]; [ idtac | clear H2 ].
   remember (x1 .[ dj2]) as b eqn:Hxj2 .
   destruct b; [ clear H2 | exfalso; apply H2; reflexivity ].
   symmetry in Hxj2.
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   rewrite Hxj2 in Ht2.
   apply negb_sym in Ht2; simpl in Ht2.
   destruct dj1.
    rename Hxj1 into Hx1.
    simpl in Hb1.
    injection Hb1; clear Hb1; intros; subst b1 x1 y1.
    destruct dj2; [ rewrite Hxj2 in Hx0; discriminate Hx0 | idtac ].
    unfold I_div_2 in Ht2; simpl in Ht2.
    rewrite Nat.sub_0_r in Ht2.
    destruct dj2; [ assumption | idtac ].
    assert (1 < S (S dj2))%nat as H by omega.
    apply Hn2 in H; simpl in H.
    rewrite Hx1, negb_involutive in H.
    symmetry; assumption.

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
