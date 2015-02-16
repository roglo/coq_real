(* multiplication in I *)

Require Import Utf8 QArith NPeano Misc Oracle.
Require Import Real01 Real01Add.

Open Scope nat_scope.

Fixpoint summation_loop b len g :=
  match len with
  | O => O
  | S len1 => g b + summation_loop (S b) len1 g
  end.

Definition summation b e g := summation_loop b (S e - b) g.

Notation "'Σ' ( i = b , e ) , g" := (summation b e (λ i, (g)))
  (at level 0, i at level 0, b at level 60, e at level 60, g at level 40).

Definition b2n (b : bool) := if b then 1 else 0.
Definition n2b n := negb (Nat.eqb n 0).

Definition modb n := n mod 2.
Definition divb n := n / 2.

Definition propag_carry_once z i :=
  match fst_not_1 z (S i) with
  | Some di =>
      if zerop (z (S (i + di))) then
        if le_dec (z i) 1 then z i else z i - 2
      else
        if zerop (z i) then 1 else z i - 1
  | None =>
      if zerop (z i) then 1 else z i - 1
   end.

Fixpoint I_propag_carry u n :=
  match n with
  | 0 => u
  | S n1 => propag_carry_once (I_propag_carry u n1)
  end.

Definition I_mul_algo x y i := Σ (j=1,i), (b2n (x.[j-1]) * b2n (y.[i-j])).
Arguments I_mul_algo x%I y%I i%nat.

Definition I_mul_i x y i := n2b (I_propag_carry (I_mul_algo x y) (S i) i).
Definition I_mul x y := {| rm := I_mul_i x y |}.

Notation "x * y" := (I_mul x y) : I_scope.

(* *)

Theorem eq_b2n_0 : ∀ b, b2n b = 0 → b = false.
Proof.
intros b Hb.
destruct b; [ discriminate Hb | reflexivity ].
Qed.

Theorem eq_b2n_1 : ∀ b, b2n b = 1 → b = true.
Proof.
intros b Hb.
destruct b; [ reflexivity | discriminate Hb ].
Qed.

Theorem le_b2n_1 : ∀ b, b2n b ≤ 1.
Proof.
intros b.
destruct b; [ reflexivity | apply Nat.le_0_1 ].
Qed.

Theorem n2b_false_iff : ∀ n, n2b n = false ↔ n = 0.
Proof.
intros n; split; intros Hn; [ idtac | subst n; reflexivity ].
destruct n; [ reflexivity | discriminate Hn ].
Qed.

(* Summation model and theorems borrowed from my proof of Puiseux's theorem,
   file Fsummation.v *)

Theorem summation_loop_compat : ∀ g h b1 b2 len,
  (∀ i, i < len → (g (b1 + i) = h (b2 + i)))
  → summation_loop b1 len g = summation_loop b2 len h.
Proof.
intros g h b1 b2 len Hgh.
revert b1 b2 Hgh.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen with (b2 := S b2).
 f_equal.
 pose proof (Hgh 0 (Nat.lt_0_succ len)) as H.
 do 2 rewrite Nat.add_0_r in H; assumption.

 intros i Hi.
 do 2 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hgh.
 apply Nat.succ_lt_mono in Hi; assumption.
Qed.

Theorem summation_loop_succ_last : ∀ g b len,
  summation_loop b (S len) g =
  summation_loop b len g + g (b + len).
Proof.
intros g b len.
revert b.
induction len; intros.
 simpl.
 do 2 rewrite Nat.add_0_r; reflexivity.

 remember (S len) as x; simpl; subst x.
 rewrite IHlen; simpl.
 rewrite Nat.add_succ_r, Nat.add_assoc; reflexivity.
Qed.

Theorem summation_loop_rev : ∀ b len g,
  summation_loop b len g =
  summation_loop b len (λ i, g (b + len - 1 + b - i)).
Proof.
intros b len g.
revert b.
induction len; intros; [ reflexivity | idtac ].
remember (S len) as x.
rewrite Heqx in |- * at 1; simpl; subst x.
rewrite IHlen.
rewrite summation_loop_succ_last.
rewrite Nat.add_comm; f_equal.
 apply summation_loop_compat.
 intros i Hi; f_equal.
 do 2 rewrite Nat.add_succ_r; reflexivity.

 f_equal.
 rewrite Nat.add_succ_r, Nat.sub_succ, Nat.sub_0_r.
 rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Theorem all_0_summation_loop_0 : ∀ g b len,
  (∀ i, (b ≤ i < b + len) → g i = 0)
  → summation_loop b len (λ i, g i) = 0.
Proof.
intros g b len H.
revert b H.
induction len; intros; [ reflexivity | simpl ].
rewrite H; [ idtac | split; auto ].
 rewrite Nat.add_0_l, IHlen; [ reflexivity | idtac ].
 intros i (Hbi, Hib); apply H.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 split; [ apply Nat.lt_le_incl; auto | auto ].

 rewrite Nat.add_succ_r.
 apply le_n_S, le_plus_l.
Qed.

Theorem all_0_summation_0 : ∀ g i1 i2,
  (∀ i, i1 ≤ i ≤ i2 → g i = 0)
  → Σ (i = i1, i2), g i = 0.
Proof.
intros g i1 i2 H.
apply all_0_summation_loop_0.
intros i (H1, H2).
apply H.
split; [ assumption | idtac ].
destruct (le_dec i1 (S i2)) as [H3| H3].
 rewrite Nat.add_sub_assoc in H2; auto.
 rewrite Nat.add_comm, Nat.add_sub in H2.
 apply Nat.succ_le_mono; assumption.

 apply not_le_minus_0 in H3.
 rewrite H3, Nat.add_0_r in H2.
 apply Nat.nle_gt in H2; contradiction.
Qed.

Theorem summation_only_one : ∀ g n, Σ (i = n, n), g i = g n.
Proof.
intros g n.
unfold summation.
rewrite Nat.sub_succ_l; [ idtac | reflexivity ].
rewrite Nat.sub_diag; simpl.
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem summation_empty : ∀ f b k, k < b → Σ (i = b, k), f i = 0.
Proof.
intros f b k Hkb.
unfold summation.
destruct b; [ exfalso; revert Hkb; apply Nat.nlt_0_r | idtac ].
rewrite Nat.sub_succ.
apply le_S_n in Hkb.
apply Nat.sub_0_le in Hkb; rewrite Hkb; reflexivity.
Qed.

Theorem summation_split_last : ∀ g b k,
  b ≤ S k
  → Σ (i = b, S k), g i = Σ (i = b, k), g i + g (S k).
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ_l; [ idtac | assumption ].
rewrite summation_loop_succ_last.
rewrite Nat.add_sub_assoc; [ f_equal | assumption ].
rewrite Nat.add_comm, Nat.add_sub.
reflexivity.
Qed.

(* commutativity *)

Theorem I_mul_algo_comm : ∀ x y, (∀ i, I_mul_algo x y i = I_mul_algo y x i).
Proof.
intros x y i.
unfold I_mul_algo; simpl.
unfold summation; simpl.
rewrite Nat.sub_0_r.
rewrite summation_loop_rev; simpl.
rewrite Nat.sub_0_r.
apply summation_loop_compat.
intros j Hj.
rewrite Nat.mul_comm; f_equal; f_equal; f_equal; simpl.
 rewrite Nat.add_1_r; simpl.
 rewrite Nat.sub_0_r.
 apply Nat.add_sub_eq_r.
 rewrite Nat.add_sub_assoc; [ idtac | apply Nat.lt_le_incl; assumption ].
 rewrite Nat.add_comm, Nat.add_sub; reflexivity.

 rewrite Nat.add_1_r; simpl.
 rewrite <- Nat.sub_add_distr, Nat.add_comm; reflexivity.
Qed.

Theorem I_propag_carry_mul_algo_comm : ∀ x y i j,
  I_propag_carry (I_mul_algo x y) i j =
  I_propag_carry (I_mul_algo y x) i j.
Proof.
intros x y i j.
revert j.
induction i; intros; simpl; [ apply I_mul_algo_comm | idtac ].
unfold propag_carry_once.
rewrite IHi.
remember (fst_not_1 (I_propag_carry (I_mul_algo x y) i) (S j)) as s1 eqn:Hs1 .
remember (fst_not_1 (I_propag_carry (I_mul_algo y x) i) (S j)) as s2 eqn:Hs2 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Ht1).
 apply fst_not_1_iff in Hs2; simpl in Hs2.
 destruct s2 as [di2| ].
  destruct Hs2 as (Hn2, Ht2).
  destruct (lt_eq_lt_dec di1 di2) as [[H1| H1]| H1].
   apply Hn2 in H1.
   rewrite <- IHi in H1; contradiction.

   subst di2; rewrite IHi; reflexivity.

   apply Hn1 in H1; rewrite IHi in H1; contradiction.

  rewrite IHi, Hs2 in Ht1.
  exfalso; apply Ht1; reflexivity.

 apply fst_not_1_iff in Hs2; simpl in Hs2.
 destruct s2 as [di2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Ht2).
 rewrite <- IHi, Hs1 in Ht2.
 exfalso; apply Ht2; reflexivity.
Qed.

Theorem I_mul_i_comm : ∀ x y i, I_mul_i x y i = I_mul_i y x i.
Proof.
intros x y i.
unfold I_mul_i.
rewrite I_propag_carry_mul_algo_comm.
reflexivity.
Qed.

Theorem I_mul_comm : ∀ x y, (x * y = y * x)%I.
Proof.
intros x y.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
rewrite I_mul_i_comm; f_equal.
apply carry_compat_r.
clear i; intros i.
unfold I_mul; simpl.
apply I_mul_i_comm.
Qed.

(* 0 absorbing element *)

Theorem if_0_propag_carry_0 : ∀ x n,
  (∀ i, x i = 0)
  → ∀ j, I_propag_carry x n j = 0.
Proof.
intros x n Hx j.
revert j.
induction n; intros; simpl; [ apply Hx | idtac ].
unfold propag_carry_once.
remember (fst_not_1 (I_propag_carry x n) (S j)) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ]; [ do 2 rewrite IHn; reflexivity | idtac ].
pose proof (Hs1 0) as H.
rewrite IHn in H; discriminate H.
Qed.

Theorem I_mul_algo_0_l : ∀ x y,
  I_eq_ext x 0
  → ∀ i, I_mul_algo x y i = 0.
Proof.
intros x y Hx i.
unfold I_mul_algo.
apply all_0_summation_0; intros j Hj.
rewrite Hx; reflexivity.
Qed.

Theorem I_mul_i_0_l : ∀ x y,
  I_eq_ext x 0
  → ∀ i, I_mul_i x y i = false.
Proof.
intros x y Hx i.
unfold I_mul_i.
remember (I_propag_carry (I_mul_algo x y) (S i) i) as nb eqn:Hnb .
symmetry in Hnb.
destruct nb; [ reflexivity | exfalso ].
rewrite if_0_propag_carry_0 in Hnb; [ discriminate Hnb | idtac ].
intros j; apply I_mul_algo_0_l; assumption.
Qed.

Theorem I_mul_0_l : ∀ x, (0 * x = 0)%I.
Proof.
intros x.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
rewrite carry_diag; simpl.
rewrite I_mul_i_0_l; [ idtac | reflexivity ].
rewrite xorb_false_l.
unfold carry; simpl.
remember (fst_same (0%I * x) 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1| ].
 destruct Hs1 as (Hn1, Ht1); assumption.

 pose proof (Hs1 0) as H; simpl in H.
 rewrite Nat.add_0_r in H.
 remember (S i) as si.
 unfold I_mul_i in H; subst si.
 rewrite if_0_propag_carry_0 in H; [ discriminate H | idtac ].
 intros j; apply all_0_summation_0; intros k Hk; reflexivity.
Qed.

(* neutral element *)

Theorem divmod_div : ∀ a b, fst (divmod a b 0 b) = (a / S b)%nat.
Proof. intros a b; reflexivity. Qed.

Theorem divmod_mod : ∀ a b, b - snd (divmod a b 0 b) = (a mod S b)%nat.
Proof. intros a b; reflexivity. Qed.

Theorem fold_sub_succ_l : ∀ a b,
  (match a with 0 => S b | S c => b - c end = S b - a)%nat.
Proof. reflexivity. Qed.

Theorem I_eq_ext_dec : ∀ x y, {I_eq_ext x y} + {not(I_eq_ext x y)}.
Proof.
intros x y.
unfold I_eq_ext.
remember (fst_same x (- y) 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Ht).
 right; intros H.
 rewrite H in Ht.
 symmetry in Ht.
 revert Ht; apply no_fixpoint_negb.

 left; intros i.
 rewrite Hs, negb_involutive; reflexivity.
Qed.

(*
Theorem I_mul_i_1_r_0 : ∀ x,
  x.[0] = false ∨ x.[1] = true
  → I_mul_i x 1%I 0 = x .[ 0].
Proof.
intros x Hx01.
unfold I_mul_i; simpl.
unfold I_mul_algo; simpl.
unfold propag_carry_once; simpl.
do 3 rewrite divmod_div.
do 2 rewrite fold_sub_succ_l, divmod_mod.
rewrite summation_only_one; simpl.
do 3 rewrite divmod_div.
do 2 rewrite fold_sub_succ_l, divmod_mod.
rewrite Nat.mul_1_r.
rewrite Nat.div_small; [ idtac | apply le_n_S, le_b2n_1 ].
rewrite Nat.mod_0_l; [ idtac | intros H; discriminate H ].
rewrite Nat.add_0_l.
rewrite Nat.mod_small; [ idtac | apply le_n_S, le_b2n_1 ].
unfold summation; simpl.
do 2 rewrite divmod_div.
do 2 rewrite Nat.mul_1_r.
rewrite Nat.add_0_r.
remember (x .[ 0]) as b0 eqn:Hx0 .
remember (x .[ 1]) as b1 eqn:Hx1 .
symmetry in Hx0, Hx1.
unfold n2b.
destruct b0, b1; try reflexivity; simpl.
destruct Hx01 as [H| H]; discriminate H.
Qed.
*)

Theorem I_mul_algo_1 : ∀ x y, I_mul_algo x y 1 = b2n (x.[0]) * b2n (y.[0]).
Proof.
intros x y.
unfold I_mul_algo, summation; simpl.
apply Nat.add_0_r.
Qed.

Theorem I_mul_algo_1_r : ∀ x i,
  I_mul_algo x 1 i = Σ (k = 1, i), b2n (x.[k-1]).
Proof.
intros x i.
unfold I_mul_algo; simpl.
unfold summation.
apply summation_loop_compat.
intros j Hj.
rewrite Nat.mul_1_r; reflexivity.
Qed.

Theorem I_mul_algo_1_succ : ∀ x i,
  I_mul_algo x 1 (S i) = I_mul_algo x 1 i + b2n (x.[i]).
Proof.
intros x i.
do 2 rewrite I_mul_algo_1_r.
rewrite summation_split_last; [ idtac | apply le_n_S, Nat.le_0_l ].
simpl; rewrite Nat.sub_0_r; reflexivity.
Qed.

Theorem I_mul_1_r : ∀ x, (I_mul x 1 = x)%I.
Proof.
intros x.
unfold I_eq; intros i; simpl.
unfold I_add_i; simpl.
do 2 rewrite xorb_false_r.
destruct i; simpl.
 unfold carry; simpl.
 remember (fst_same (x * 1%I) 0 1) as s1 eqn:Hs1 .
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 remember (fst_same x 0 1) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Ht1).
  rewrite Ht1, xorb_false_r.
  destruct s2 as [di2| ].
   destruct Hs2 as (Hn2, Ht2).
   rewrite Ht2, xorb_false_r.
   unfold I_mul_i; simpl.
   unfold propag_carry_once; simpl.
   remember (fst_not_1 (I_mul_algo x 1) 1) as s3 eqn:Hs3 .
   apply fst_not_1_iff in Hs3; simpl in Hs3.
   symmetry; unfold n2b; simpl.
   destruct s3 as [di3| ]; simpl.
    destruct Hs3 as (Hn3, Ht3).
    destruct (zerop (I_mul_algo x 1 (S di3))) as [H1| H1]; simpl.
     rewrite I_mul_algo_1_r in H1; simpl in H1.
     unfold summation in H1; simpl in H1.
     apply Nat.eq_add_0 in H1.
     destruct H1 as (H1, _).
     apply eq_b2n_0 in H1; assumption.

     remember (I_mul_algo x 1 (S di3)) as m eqn:Hm .
     symmetry in Hm.
     destruct m; [ exfalso; revert H1; apply Nat.nlt_0_r | clear H1 ].
     destruct m; [ exfalso; apply Ht3; reflexivity | clear Ht3 ].
     rewrite I_mul_algo_1_r in Hm; simpl in Hm.
     unfold summation in Hm; simpl in Hm.
     unfold b2n in Hm; simpl in Hm.
     remember (x .[ 0]) as b eqn:Hx0 .
     symmetry in Hx0.
     destruct b; [ reflexivity | simpl in Hm ].
     destruct di3; [ discriminate Hm | simpl in Hm ].
     pose proof (Hn3 0 (Nat.lt_0_succ di3)) as H.
     rewrite I_mul_algo_1_r in H; simpl in H.
     unfold summation in H; simpl in H.
     rewrite Hx0 in H; discriminate H.

    pose proof (Hs3 0) as H.
    rewrite I_mul_algo_1_r in H; simpl in H.
    unfold summation in H; simpl in H.
    rewrite Nat.add_0_r in H.
    apply eq_b2n_1 in H; assumption.

   rewrite xorb_true_r.
   apply negb_sym.
   unfold I_mul_i; simpl.
   unfold propag_carry_once; simpl.
   remember (fst_not_1 (I_mul_algo x 1) 1) as s3 eqn:Hs3 .
   apply fst_not_1_iff in Hs3; simpl in Hs3.
   unfold n2b; simpl.
   destruct s3 as [di3| ]; simpl.
    destruct Hs3 as (Hn3, Ht3).
    destruct (zerop (I_mul_algo x 1 (S di3))) as [H1| H1]; simpl.
     rewrite I_mul_algo_1_r in H1; simpl in H1.
     unfold summation in H1; simpl in H1.
     apply Nat.eq_add_0 in H1.
     destruct H1 as (Hx0, H1).
     apply eq_b2n_0 in Hx0.
     destruct di3; [ clear H1 | simpl in H1 ].
      unfold I_mul_algo in Ht3; simpl in Ht3.
      unfold summation in Ht3; simpl in Ht3.
      rewrite Hx0 in Ht3; simpl in Ht3.
      clear Ht3 Hn3.
      destruct di1.
       clear Hn1.
       unfold I_mul_i in Ht1; simpl in Ht1.
       apply n2b_false_iff in Ht1.
       remember (propag_carry_once (I_mul_algo x 1)) as u eqn:Hu .
       unfold propag_carry_once in Ht1; simpl in Ht1.
       remember (fst_not_1 u 2) as s3 eqn:Hs3 .
       apply fst_not_1_iff in Hs3; simpl in Hs3.
       destruct s3 as [di3| ].
        destruct Hs3 as (Hn3, Ht3).
        destruct (zerop (u (S (S di3)))) as [H2| H2].
         clear Ht3.
         destruct (le_dec (u 1) 1) as [H3| H3].
          clear H3.
          rewrite Hu in Ht1; simpl in Ht1.
          unfold propag_carry_once in Ht1; simpl in Ht1.
          remember (fst_not_1 (I_mul_algo x 1) 2) as s4 eqn:Hs4 .
          apply fst_not_1_iff in Hs4; simpl in Hs4.
          destruct s4 as [di4| ].
           destruct Hs4 as (Hn4, Ht4).
           destruct (zerop (I_mul_algo x 1 (S (S di4)))) as [H3| H3].
            clear Ht4.
            rewrite I_mul_algo_1_r in H3; simpl in H3.
            unfold summation in H3; simpl in H3.
            rewrite Nat.add_comm, Hs2 in H3; discriminate H3.

            rewrite I_mul_algo_1 in Ht1; simpl in Ht1.
            rewrite Hx0 in Ht1; discriminate Ht1.

           rewrite I_mul_algo_1 in Ht1; simpl in Ht1.
           rewrite Hx0 in Ht1; discriminate Ht1.

          apply Nat.nle_gt in H3.
          symmetry in Ht1.
          apply Nat_le_sub_add_r in Ht1; [ simpl in Ht1 | assumption ].
          clear H3.
          rewrite Hu in Ht1; simpl in Ht1.
          unfold propag_carry_once in Ht1; simpl in Ht1.
          remember (fst_not_1 (I_mul_algo x 1) 2) as s4 eqn:Hs4 .
          apply fst_not_1_iff in Hs4; simpl in Hs4.
          destruct s4 as [di4| ].
           destruct Hs4 as (Hn4, Ht4).
           destruct (zerop (I_mul_algo x 1 (S (S di4)))) as [H3| H3].
            clear Ht4.
            rewrite I_mul_algo_1_r in H3; simpl in H3.
            unfold summation in H3; simpl in H3.
            rewrite Nat.add_comm, Hs2 in H3; discriminate H3.

            rewrite I_mul_algo_1 in Ht1; simpl in Ht1.
            rewrite Hx0 in Ht1; discriminate Ht1.

           rewrite I_mul_algo_1 in Ht1; simpl in Ht1.
           rewrite Hx0 in Ht1; discriminate Ht1.

         destruct (zerop (u 1)) as [H3| H3]; [ discriminate Ht1 | idtac ].
         symmetry in Ht1.
         apply Nat_le_sub_add_r in Ht1; [ simpl in Ht1 | assumption ].
         clear H3.
         rewrite Hu in Ht1; simpl in Ht1.
         unfold propag_carry_once in Ht1; simpl in Ht1.
         remember (fst_not_1 (I_mul_algo x 1) 2) as s4 eqn:Hs4 .
         apply fst_not_1_iff in Hs4; simpl in Hs4.
         destruct s4 as [di4| ].
          destruct Hs4 as (Hn4, Ht4).
          destruct (zerop (I_mul_algo x 1 (S (S di4)))) as [H3| H3].
           clear Ht4.
           rewrite I_mul_algo_1_r in H3; simpl in H3.
           unfold summation in H3; simpl in H3.
           rewrite Nat.add_comm, Hs2 in H3; discriminate H3.

           clear Ht1.
           remember (I_mul_algo x 1 (S (S di4))) as m eqn:Hm .
           destruct m; [ exfalso; revert H3; apply Nat.nlt_0_r | clear H3 ].
           destruct m; [ exfalso; apply Ht4; reflexivity | clear Ht4 ].
           symmetry in Hm.
           rewrite I_mul_algo_1_r in Hm; simpl in Hm.
           unfold summation in Hm; simpl in Hm.
           rewrite Hx0 in Hm; simpl in Hm.
bbb.
   remember (S di1) as si.
   unfold I_mul_i in Ht1; simpl in Ht1.
   apply n2b_false_iff in Ht1.
   unfold propag_carry_once in Ht1; simpl in Ht1.
   remember (I_propag_carry (I_mul_algo x 1) si) as u eqn:Hu .
   remember (fst_not_1 u (S si)) as s3 eqn:Hs3 .
   apply fst_not_1_iff in Hs3; simpl in Hs3.
   destruct s3 as [di3| ].
    destruct Hs3 as (Hn3, Ht3).
    destruct (zerop (u (S (si + di3)))) as [H1| H1].
     destruct (le_dec (u si) 1) as [H2| H2].
      rewrite Hu, Heqsi in Ht1.
      simpl in Ht1.
      remember (I_propag_carry (I_mul_algo x 1) di1) as u1 eqn:Hu1 .
      unfold propag_carry_once in Ht1; simpl in Ht1.
      remember (fst_not_1 u1 (S (S di1))) as s4 eqn:Hs4 .
      apply fst_not_1_iff in Hs4; simpl in Hs4.
      destruct s4 as [di4| ].
       destruct Hs4 as (Hn4, Ht4).
       destruct (zerop (u1 (S (S (di1 + di4))))) as [H3| H3].
        destruct (le_dec (u1 (S di1)) 1) as [H4| H4].
         rewrite Hu1 in Ht1; simpl in Ht1.
         destruct di1.
          simpl in Ht1.
          rewrite I_mul_algo_1_r in Ht1.
          rewrite summation_only_one in Ht1; simpl in Ht1.
          apply eq_b2n_0 in Ht1.
          subst si.
          rewrite Ht1; simpl.
          unfold I_mul_i; simpl.
          unfold propag_carry_once; simpl.
          remember (fst_not_1 (I_mul_algo x 1) 1) as s5 eqn:Hs5 .
          apply fst_not_1_iff in Hs5; simpl in Hs5.
          destruct s5 as [di5| ]; [ idtac | reflexivity ].
          destruct Hs5 as (Hn5, Ht5).
          destruct (zerop (I_mul_algo x 1 (S di5))) as [H5| H5].
           rewrite I_mul_algo_1_r in H5; simpl in H5.
           unfold summation in H5; simpl in H5.
           rewrite Ht1 in H5; simpl in H5.
           destruct di5; [ clear H5 | simpl in H5 ].
            clear Ht5 Hn5.
            simpl in H1.
            rewrite Hu in H1; simpl in H1.
            unfold propag_carry_once in H1; simpl in H1.
            remember (fst_not_1 (I_mul_algo x 1) (S (S (S di3)))) as s5
             eqn:Hs5 .
            apply fst_not_1_iff in Hs5; simpl in Hs5.
            destruct s5 as [di5| ].
             destruct Hs5 as (Hn5, Ht5).
             destruct (zerop (I_mul_algo x 1 (S (S (S (di3 + di5))))))
              as [H5| H5].
              rewrite I_mul_algo_1_r in H5; simpl in H5.
              unfold summation in H5; simpl in H5.
              rewrite Ht1, Hs2, Hs2 in H5.
              discriminate H5.

              destruct (zerop (I_mul_algo x 1 (S (S di3)))) as [H6| H6].
               discriminate H1.

               symmetry in H1.
               apply Nat_le_sub_add_r in H1; [ simpl in H1 | assumption ].
               rewrite I_mul_algo_1_r in H1; simpl in H1.
               unfold summation in H1; simpl in H1.
               rewrite Ht1 in H1; simpl in H1.
               rewrite Hs2 in H1; simpl in H1.
               apply Nat.succ_inj in H1.
               destruct di3.
                simpl in H1.
                clear H1.
                simpl in Ht3.
                rewrite Hu1 in H3; simpl in H3.
                rewrite I_mul_algo_1_r in H3; simpl in H3.
                unfold summation in H3; simpl in H3.
                rewrite Nat.add_comm, Hs2 in H3; simpl in H3.
                discriminate H3.

                simpl in H1.
                rewrite Hs2 in H1; discriminate H1.

             destruct (zerop (I_mul_algo x 1 (S (S di3)))) as [H5| H5].
              discriminate H1.

              simpl in Hu, Hu1; subst u1.
              simpl in H3.
              rewrite I_mul_algo_1_r in H3; simpl in H3.
              unfold summation in H3; simpl in H3.
              rewrite Nat.add_comm, Hs2 in H3; discriminate H3.

            rewrite Hs2 in H5; discriminate H5.

           simpl in Hu, Hu1; subst u1.
           rewrite I_mul_algo_1_r in H3; simpl in H3.
           unfold summation in H3; simpl in H3.
           rewrite Nat.add_comm, Hs2 in H3; discriminate H3.

          pose proof (Hn1 0 (Nat.lt_0_succ di1)) as H.
bbb.
     rewrite Hu, Heqsi in H1; simpl in H1.
     remember (I_propag_carry (I_mul_algo x 1) di1) as u1 eqn:Hu1 .
     unfold propag_carry_once in H1; simpl in H1.
     remember (S (S (di1 + di3))) as ssi.
     remember (fst_not_1 u1 (S ssi)) as s4 eqn:Hs4 .
     apply fst_not_1_iff in Hs4; simpl in Hs4.
     destruct s4 as [di4| ].
      destruct Hs4 as (Hn4, Ht4).
      do 2 rewrite <- Nat.add_succ_l in H1.
      rewrite <- Heqssi in H1.
      destruct (zerop (u1 (S (ssi + di4)))) as [H2| H2].
       destruct (le_dec (u1 ssi) 1) as [H3| H3].
bbb.

(* version using I_eq_prop *)
intros x.
apply I_eq_prop.
remember (fst_same (x * 1)%I (- x) 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [i| ].
 Focus 2.
 left; intros i; simpl.
 rewrite Hs, negb_involutive; reflexivity.

 destruct Hs as (Hn, Ht).
 right.
 exists i.
 split.
  intros j Hj; simpl.
  apply Hn in Hj.
  rewrite Hj, negb_involutive; reflexivity.

  split; [ simpl; apply neq_negb; assumption | idtac ].
  destruct i.
   clear Hn; simpl.
   remember (x .[ 0]) as b eqn:Hx0 .
   symmetry in Hx0.
   rewrite Ht.
   destruct b; simpl in Ht; simpl.
    exfalso.
    unfold I_mul_i in Ht; simpl in Ht.
    apply n2b_false_iff in Ht.
    unfold propag_carry_once in Ht; simpl in Ht.
    remember (fst_not_1 (I_mul_algo x 1) 1) as s1 eqn:Hs1 .
    apply fst_not_1_iff in Hs1; simpl in Hs1.
    destruct s1 as [di1| ]; [ idtac | discriminate Ht ].
    destruct (zerop (I_mul_algo x 1 (S di1))) as [H1| H1].
     destruct Hs1 as (Hn1, _).
     destruct di1.
      rewrite I_mul_algo_1, Hx0 in H1; discriminate H1.

      unfold I_mul_algo in H1; simpl in H1.
      unfold summation in H1; simpl in H1.
      rewrite Hx0 in H1; discriminate H1.

     discriminate Ht.

    unfold I_mul_i in Ht; simpl in Ht.
    unfold propag_carry_once in Ht; simpl in Ht.
    remember (fst_not_1 (I_mul_algo x 1) 1) as s1 eqn:Hs1 .
    apply fst_not_1_iff in Hs1; simpl in Hs1.
    destruct s1 as [di1| ].
     destruct (zerop (I_mul_algo x 1 (S di1))) as [H1| H1].
      unfold I_mul_algo in Ht; simpl in Ht.
      unfold summation in Ht; discriminate Ht.

      unfold I_mul_algo in H1; simpl in H1.
      destruct Hs1 as (Hn1, Ht1).
      destruct di1.
       unfold summation in H1; simpl in H1.
       rewrite Hx0 in H1; simpl in H1.
       exfalso; revert H1; apply Nat.nlt_0_r.

       pose proof (Hn1 0 (Nat.lt_0_succ di1)) as H.
       rewrite I_mul_algo_1 in H; simpl in H.
       rewrite Hx0 in H; discriminate H.

     pose proof (Hs1 0) as H; simpl in H.
     rewrite I_mul_algo_1 in H; simpl in H.
     rewrite Hx0 in H; discriminate H.

   right; simpl.
   split; intros di.
    destruct i.
     unfold I_mul_i in Ht.
     simpl in Ht.
     unfold propag_carry_once at 1 in Ht; simpl in Ht.
     remember (propag_carry_once (I_mul_algo x 1)) as z.
     remember (fst_not_1 z 2) as s1 eqn:Hs1 .
     apply fst_not_1_iff in Hs1; simpl in Hs1.
     destruct s1 as [di1| ].
      destruct Hs1 as (Hn1, Ht1).
      apply negb_sym in Ht; rename Ht into Hx1.
      destruct (zerop (z (S (S di1)))) as [H1| H1].
       destruct (le_dec (z 1) 1) as [H2| H2].
        unfold n2b in Hx1; simpl in Hx1.
        rewrite negb_involutive in Hx1.
        remember (z 1) as d eqn:Hd .
        symmetry in Hd.
        destruct d; simpl in Hx1.
         clear Ht1 H2.
         rewrite Heqz in H1; simpl in H1.
         unfold propag_carry_once in H1; simpl in H1.
         remember (fst_not_1 (I_mul_algo x 1) (S (S (S di1)))) as s2 eqn:Hs2 .
         apply fst_not_1_iff in Hs2; simpl in Hs2.
         destruct s2 as [di2| ].
          destruct Hs2 as (Hn2, Ht2).
          destruct (zerop (I_mul_algo x 1 (S (S (S (di1 + di2))))))
           as [H2| H2].
           unfold I_mul_algo in H2; simpl in H2.
           unfold summation in H2; simpl in H2.
           rewrite Nat.add_comm, Hx1 in H2; discriminate H2.

           destruct (zerop (I_mul_algo x 1 (S (S di1)))) as [H3| H3].
            discriminate H1.

            symmetry in H1.
            apply Nat_le_sub_add_r in H1; [ simpl in H1 | assumption ].
            clear H3.
            rewrite I_mul_algo_1_r in H1.
            unfold summation in H1; simpl in H1.
            rewrite Nat.add_comm, Hx1 in H1; simpl in H1.
            apply Nat.succ_inj in H1.
            apply Nat.eq_add_0 in H1.
            destruct H1 as (_, H1).
            apply eq_b2n_0 in H1.
            rename H1 into Hx0.
            remember (I_mul_algo x 1 (S (S (S (di1 + di2))))) as m eqn:Hm .
            symmetry in Hm.
            destruct m; [ exfalso; revert H2; apply Nat.nlt_0_r | clear H2 ].
            destruct m; [ exfalso; apply Ht2; reflexivity | clear Ht2 ].
            rewrite I_mul_algo_1_r in Hm; simpl in Hm.
            unfold summation in Hm; simpl in Hm.
            rewrite Hx0, Hx1 in Hm; simpl in Hm.
            apply Nat.succ_inj in Hm.
            rewrite Heqz in Hd; simpl in Hd.
            unfold propag_carry_once in Hd; simpl in Hd.
            remember (fst_not_1 (I_mul_algo x 1) 2) as s3 eqn:Hs3 .
            apply fst_not_1_iff in Hs3; simpl in Hs3.
            destruct s3 as [di3| ].
             destruct Hs3 as (Hn3, Ht3).
             destruct (zerop (I_mul_algo x 1 (S (S di3)))) as [H4| H4].
              rewrite I_mul_algo_1_r in H4.
              unfold summation in H4; simpl in H4.
              rewrite Nat.add_comm, Hx1 in H4; discriminate H4.

              rewrite I_mul_algo_1 in Hd.
              rewrite Hx0 in Hd; simpl in Hd.
              discriminate Hd.

             rewrite I_mul_algo_1 in Hd; simpl in Hd.
             rewrite Hx0 in Hd; simpl in Hd.
             discriminate Hd.

          destruct (zerop (I_mul_algo x 1 (S (S di1)))) as [H2| H2].
           discriminate H1.

           symmetry in H1.
           apply Nat_le_sub_add_r in H1; [ simpl in H1 | assumption ].
           rewrite I_mul_algo_1_r in H1; simpl in H1.
           unfold summation in H1; simpl in H1.
           rewrite Nat.add_comm, Hx1 in H1; simpl in H1.
           apply Nat.succ_inj in H1.
           apply Nat.eq_add_0 in H1.
           destruct H1 as (_, H1).
           apply eq_b2n_0 in H1.
           rename H1 into Hx0.
           rewrite Heqz in Hd; simpl in Hd.
           unfold propag_carry_once in Hd; simpl in Hd.
           remember (fst_not_1 (I_mul_algo x 1) 2) as s3 eqn:Hs3 .
           apply fst_not_1_iff in Hs3; simpl in Hs3.
           destruct s3 as [di3| ].
            destruct Hs3 as (Hn3, Ht3).
            destruct (zerop (I_mul_algo x 1 (S (S di3)))) as [H4| H4].
             rewrite I_mul_algo_1_r in H4.
             unfold summation in H4; simpl in H4.
             rewrite Nat.add_comm, Hx1 in H4; discriminate H4.

             rewrite I_mul_algo_1 in Hd.
             rewrite Hx0 in Hd; simpl in Hd.
             discriminate Hd.

            rewrite I_mul_algo_1 in Hd; simpl in Hd.
            rewrite Hx0 in Hd; simpl in Hd.
            discriminate Hd.

         apply Nat.succ_le_mono in H2.
         apply Nat.le_0_r in H2; subst d.
         rewrite Heqz in Hd; simpl in Hd.
         unfold propag_carry_once in Hd; simpl in Hd.
         remember (fst_not_1 (I_mul_algo x 1) 2) as s2 eqn:Hs2 .
         apply fst_not_1_iff in Hs2; simpl in Hs2.
         destruct s2 as [di2| ].
          destruct Hs2 as (Hn2, Ht2).
          destruct (zerop (I_mul_algo x 1 (S (S di2)))) as [H2| H2].
           rewrite I_mul_algo_1_r in Hd; simpl in Hd.
           unfold summation in Hd; simpl in Hd.
           rewrite Nat.add_0_r in Hd.
           destruct (le_dec (b2n (x .[ 0]))) as [H3| H3].
            clear H3.
            apply eq_b2n_1 in Hd.
            rename Hd into Hx0.
            rewrite I_mul_algo_1_r in H2.
            unfold summation in H2; simpl in H2.
            rewrite Hx0 in H2; discriminate H2.

            destruct (x .[ 0]); discriminate Hd.

           rewrite I_mul_algo_1_r in Hd; simpl in Hd.
           unfold summation in Hd; simpl in Hd.
           rewrite Nat.add_0_r in Hd; simpl in Hd.
           destruct (zerop (b2n (x .[ 0]))) as [H3| H3].
            clear Hd Ht1.
            apply eq_b2n_0 in H3; rename H3 into Hx0.
            remember (I_mul_algo x 1 (S (S di2))) as m eqn:Hm .
            symmetry in Hm.
            destruct m; [ exfalso; revert H2; apply Nat.nlt_0_r | clear H2 ].
            destruct m; [ exfalso; apply Ht2; reflexivity | clear Ht2 ].
            destruct di2.
             rewrite I_mul_algo_1_r in Hm; simpl in Hm.
             unfold summation in Hm; simpl in Hm.
             rewrite Hx0, Hx1 in Hm; discriminate Hm.

             pose proof (Hn2 0 (Nat.lt_0_succ di2)) as H.
             rewrite I_mul_algo_1_r in H; simpl in H.
             unfold summation in H; simpl in H.
             rewrite Hx0, Hx1 in H; discriminate H.

            symmetry in Hd.
            apply Nat_le_sub_add_r in Hd; [ simpl in Hd | assumption ].
            destruct (x .[ 0]); discriminate Hd.

          rewrite I_mul_algo_1_r in Hd; simpl in Hd.
          unfold summation in Hd; simpl in Hd.
          rewrite Nat.add_0_r in Hd; simpl in Hd.
          destruct (zerop (b2n (x .[ 0]))) as [H2| H2].
           clear Hd.
           apply eq_b2n_0 in H2.
           rename H2 into Hx0.
           pose proof (Hs2 0) as H.
           rewrite I_mul_algo_1_r in H; simpl in H.
           unfold summation in H; simpl in H.
           rewrite Hx0, Hx1 in H; discriminate H.

           symmetry in Hd.
           apply Nat_le_sub_add_r in Hd; [ simpl in Hd | assumption ].
           destruct (x .[ 0]); discriminate Hd.

        apply Nat.nle_gt in H2.
        remember (z 1) as m eqn:Hm .
        symmetry in Hm.
        destruct m; [ exfalso; revert H2; apply Nat.nlt_0_r | clear H2 ].
        simpl in Hx1.
        destruct m; simpl in Hx1.
         rewrite Heqz in H1.
         unfold propag_carry_once in H1; simpl in H1.
         remember (fst_not_1 (I_mul_algo x 1) (S (S (S di1)))) as s2 eqn:Hs2 .
         apply fst_not_1_iff in Hs2; simpl in Hs2.
         destruct s2 as [di2| ].
          destruct Hs2 as (Hn2, Ht2).
          destruct (zerop (I_mul_algo x 1 (S (S (S (di1 + di2))))))
           as [H2| H2].
           rewrite I_mul_algo_1_r in H2.
           unfold summation in H2; simpl in H2.
           rewrite Nat.add_comm, Hx1 in H2; discriminate H2.

           destruct (zerop (I_mul_algo x 1 (S (S di1)))) as [H3| H3].
            discriminate H1.

            symmetry in H1.
            apply Nat_le_sub_add_r in H1; [ simpl in H1 | assumption ].
            clear H3.
            rewrite I_mul_algo_1_r in H1; simpl in H1.
            unfold summation in H1; simpl in H1.
            rewrite Nat.add_comm, Hx1 in H1; simpl in H1.
            apply Nat.succ_inj in H1.
            apply Nat.eq_add_0 in H1.
            destruct H1 as (_, Hx0).
            apply eq_b2n_0 in Hx0.
            rewrite Heqz in Hm; simpl in Hm.
            unfold propag_carry_once in Hm; simpl in Hm.
            remember (fst_not_1 (I_mul_algo x 1) 2) as s3 eqn:Hs3 .
            apply fst_not_1_iff in Hs3; simpl in Hs3.
            rewrite I_mul_algo_1_r in Hm; simpl in Hm.
            unfold summation in Hm; simpl in Hm.
            rewrite Hx0 in Hm; simpl in Hm.
            destruct s3 as [di3| ]; [ idtac | clear Hm ].
             destruct Hs3 as (Hn3, Ht3).
             destruct (zerop (I_mul_algo x 1 (S (S di3)))) as [H3| H3].
              discriminate Hm.

              clear Hm.
              destruct di3.
               rewrite I_mul_algo_1_r in Ht3; simpl in Ht3.
               unfold summation in Ht3; simpl in Ht3.
               rewrite Hx0, Hx1 in Ht3; simpl in Ht3.
               exfalso; apply Ht3; reflexivity.

               destruct di3.
                unfold I_mul_algo in Ht3; simpl in Ht3.
                unfold summation in Ht3; simpl in Ht3.
                rewrite Hx0, Hx1 in Ht3; simpl in Ht3.
                remember (x .[ 2]) as d eqn:Hx2 .
                symmetry in Hx2.
                destruct d; [ clear Ht3 | exfalso; apply Ht3; reflexivity ].
                rewrite Hx1; simpl.
                destruct di.
                 unfold I_mul_i; simpl.
                 unfold propag_carry_once at 1.
                 rewrite <- Heqz.
                 remember (fst_not_1 (propag_carry_once z) 3) as s4 eqn:Hs4 .
                 apply fst_not_1_iff in Hs4; simpl in Hs4.
                 destruct s4 as [di4| ].
                  simpl.
                  destruct Hs4 as (Hn4, Ht4).
                  destruct (zerop (propag_carry_once z (S (S (S di4)))))
                   as [H4| H4].
                   clear Ht4.
                   destruct (le_dec (propag_carry_once z 2) 1) as [H5| H5].
                    remember (propag_carry_once z 2) as m eqn:Hm .
                    symmetry in Hm.
                    destruct m; [ idtac | reflexivity ].
                    clear H5; exfalso.
                    unfold propag_carry_once in Hm; simpl in Hm.
                    remember (fst_not_1 z 3) as s5 eqn:Hs5 .
                    apply fst_not_1_iff in Hs5; simpl in Hs5.
                    destruct s5 as [di5| ].
                     destruct Hs5 as (Hn5, Ht5).
                     destruct (zerop (z (S (S (S di5))))) as [H5| H5].
                      clear Ht5.
                      destruct (le_dec (z 2) 1) as [H6| H6].
                       clear H6.
bbb.
                clear H3.
                clear Hn3 H2 Hn Ht2 di2 Hn2.
                clear z Heqz Hn1 Ht1.

(* compatibility with equality *)

Theorem I_ext_mul_algo_compat_r : ∀ x y z i,
  I_eq_ext x y
  → I_mul_algo x z i = I_mul_algo y z i.
Proof.
intros x y z i Hxy.
unfold I_mul_algo.
unfold summation.
rewrite Nat.sub_succ, Nat.sub_0_r.
apply summation_loop_compat.
intros j Hji.
rewrite Hxy; reflexivity.
Qed.

Theorem I_ext_propag_carry_mul_algo_compat_r : ∀ x y z n i,
  I_eq_ext x y
  → I_propag_carry (I_mul_algo x z) n i =
    I_propag_carry (I_mul_algo y z) n i.
Proof.
intros x y z n i Hxy.
revert i.
induction n; intros; simpl.
 apply I_ext_mul_algo_compat_r; assumption.

 unfold propag_carry_once.
 f_equal; rewrite IHn; reflexivity.
Qed.

Theorem I_ext_mul_compat_r : ∀ x y z, I_eq_ext x y → I_eq_ext (x * z) (y * z).
Proof.
intros x y z Hxy.
unfold I_eq_ext; simpl; intros i.
unfold I_mul_i; simpl.
erewrite I_ext_propag_carry_mul_algo_compat_r; [ idtac | eassumption ].
reflexivity.
Qed.

Theorem I_mul_compat_r : ∀ x y z, (x = y)%I → (x * z = y * z)%I.
Proof.
intros x y z Hxy.
apply I_eq_prop in Hxy.
destruct Hxy as [Hxy| (i, (Hlt, (Heq, Hgt)))].
 apply I_eq_ext_eq, I_ext_mul_compat_r; assumption.

 destruct Hgt as [(Hi, (Hx, Hy))| (Hx, Hy)].
  subst i; clear Hlt.
  unfold I_eq; simpl; intros k.
  unfold I_add_i; simpl.
  do 2 rewrite xorb_false_r.
  unfold I_mul_i.
  remember (I_propag_carry (I_mul_algo x z) (k + 2) k) as nb1 eqn:Hnb1 .
  remember (I_propag_carry (I_mul_algo y z) (k + 2) k) as nb2 eqn:Hnb2 .
  symmetry in Hnb1, Hnb2.
  destruct nb1; simpl.
   destruct nb2; simpl.
    unfold carry; simpl.
    remember (fst_same (x * z) 0 (S k)) as s1 eqn:Hs1 .
    remember (fst_same (y * z) 0 (S k)) as s2 eqn:Hs2 .
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    apply fst_same_sym_iff in Hs2; simpl in Hs2.
    destruct s1 as [dj1| ].
     destruct Hs1 as (Hn1, Ht1).
     rewrite Ht1; simpl.
     destruct s2 as [dj2| ].
      destruct Hs2 as (Hn2, Ht2).
      rewrite Ht2; reflexivity.

      remember (x .[ 0]) as b eqn:Hxi .
      apply neq_negb in Heq.
      symmetry in Hxi; apply negb_sym in Heq.
      rewrite Heq in Hy.
      destruct b; simpl in Hy, Heq.
       pose proof (Hs2 0) as H.
       rewrite Nat.add_0_r in H.
       unfold I_mul_i in H.
       remember (I_propag_carry (I_mul_algo y z) (S k + 2) (S k)) as nb3.
       rename Heqnb3 into Hnb3.
       symmetry in Hnb3.
       destruct nb3; [ discriminate H | clear H ].
       rewrite if_0_propag_carry_0 in Hnb3; [ discriminate Hnb3 | idtac ].
       intros i.
       apply I_mul_algo_0_l; assumption.

       pose proof (Hs2 O) as H.
       rewrite Nat.add_0_r in H.
       unfold I_mul_i in H.
       remember (I_propag_carry (I_mul_algo y z) (S k + 2) (S k)) as nb3.
       rename Heqnb3 into Hnb3.
       symmetry in Hnb3.
       destruct nb3; [ discriminate H | clear H ].
       destruct dj1.
        Focus 2.
        pose proof (Hn1 0 (Nat.lt_0_succ dj1)) as H.
        rewrite Nat.add_0_r in H.
        rewrite I_mul_i_0_l in H; [ discriminate H | assumption ].

        clear Hn1; rewrite Nat.add_0_r in Ht1.
        unfold I_mul_i in Ht1.
        remember (I_propag_carry (I_mul_algo x z) (S k + 2) (S k)) as nb4.
        rename Heqnb4 into Hnb4.
        symmetry in Hnb4.
        destruct nb4; [ clear Ht1 | discriminate Ht1 ].
        move Hnb4 before Hnb3.
        rewrite Nat.add_succ_r in Hnb2; simpl in Hnb2.
        unfold propag_carry_once in Hnb2.
        apply Nat.eq_add_0 in Hnb2.
        destruct Hnb2 as (Hnb5, Hnb2).
        rewrite Nat.add_1_r in Hnb2.
        apply Nat.div_small_iff in Hnb2; [ idtac | intros H; discriminate H ].
        simpl in Hnb2.
bbb.
