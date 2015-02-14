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
      match nat_compare (z i) 1 with
      | Eq => if lt_dec (z (S (i + di))) 2 then z i else 0
      | Lt => if lt_dec (z (S (i + di))) 2 then z i else S (z i)
      | Gt => if lt_dec (z (S (i + di))) 2 then z i - 2 else z i - 1
      end
  | None =>
      match nat_compare (z i) 1 with
      | Eq => 0
      | Lt => S (z i)
      | Gt => z i - 1
      end
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
rewrite IHi; f_equal.
unfold carry; simpl.
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
remember (nat_compare (I_propag_carry x n j) 1) as c eqn:Hc .
apply fst_not_1_iff in Hs1; simpl in Hs1.
symmetry in Hc.
destruct s1 as [di1| ].
 do 2 rewrite IHn; destruct c; reflexivity.

 pose proof (Hs1 0) as H.
 rewrite IHn in H.
 discriminate H.
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

Theorem b2n_le_1 : ∀ b, b2n b ≤ 1.
Proof.
intros b.
destruct b; [ reflexivity | apply Nat.le_0_1 ].
Qed.

Theorem n2b_false_iff : ∀ n, n2b n = false ↔ n = 0.
Proof.
intros n; split; intros Hn; [ idtac | subst n; reflexivity ].
destruct n; [ reflexivity | discriminate Hn ].
Qed.

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
rewrite Nat.div_small; [ idtac | apply le_n_S, b2n_le_1 ].
rewrite Nat.mod_0_l; [ idtac | intros H; discriminate H ].
rewrite Nat.add_0_l.
rewrite Nat.mod_small; [ idtac | apply le_n_S, b2n_le_1 ].
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

Theorem Nat_add_mod_2 : ∀ a b, (a + b) mod 2 = 0 ↔ a mod 2 = b mod 2.
Proof.
intros a b.
split; intros Hab.
 rewrite Nat.add_mod in Hab; [ idtac | intros H; discriminate H ].
 remember (a mod 2) as aa eqn:Ha .
 remember (b mod 2) as bb eqn:Hb .
 symmetry in Ha, Hb.
 destruct aa, bb; try reflexivity.
  rewrite Nat.add_0_l, <- Hb in Hab.
  rewrite Nat.mod_mod in Hab; [ idtac | intros H; discriminate H ].
  rewrite Hb in Hab; discriminate Hab.

  rewrite Nat.add_0_r, <- Ha in Hab.
  rewrite Nat.mod_mod in Hab; [ idtac | intros H; discriminate H ].
  rewrite Ha in Hab; discriminate Hab.

  destruct aa.
   destruct bb; [ reflexivity | idtac ].
   assert (2 ≠ 0) as H by (intros H; discriminate H).
   apply Nat.mod_upper_bound with (a := b) in H.
   rewrite Hb in H.
   apply Nat.nlt_ge in H.
   exfalso; apply H.
   do 2 apply lt_n_S.
   apply Nat.lt_0_succ.

   assert (2 ≠ 0) as H by (intros H; discriminate H).
   apply Nat.mod_upper_bound with (a := a) in H.
   rewrite Ha in H.
   apply Nat.nlt_ge in H.
   exfalso; apply H.
   do 2 apply lt_n_S.
   apply Nat.lt_0_succ.

 rewrite Nat.add_mod; [ idtac | intros H; discriminate H ].
 rewrite Hab; clear a Hab.
 remember (b mod 2) as a; clear b Heqa.
 induction a; [ reflexivity | idtac ].
 rewrite <- Nat.add_1_r.
 rewrite Nat.add_shuffle0.
 do 2 rewrite <- Nat.add_assoc.
 rewrite Nat.add_assoc.
 rewrite Nat.add_mod; [ idtac | intros H; discriminate H ].
 rewrite IHa; reflexivity.
Qed.

Theorem I_mul_algo_1 : ∀ x y, I_mul_algo x y 1 = b2n (x.[0]) * b2n (y.[0]).
Proof.
intros x y.
unfold I_mul_algo, summation; simpl.
apply Nat.add_0_r.
Qed.

Theorem I_add_1_r : ∀ x, (I_mul x 1 = x)%I.
Proof.
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
    remember (x .[ 1]) as b eqn:Hx1 .
    symmetry in Hx1.
    unfold I_mul_i in Ht; simpl in Ht.
    apply n2b_false_iff in Ht.
    unfold propag_carry_once in Ht; simpl in Ht.
    remember (fst_not_1 (I_mul_algo x 1) 1) as s1 eqn:Hs1 .
    apply fst_not_1_iff in Hs1; simpl in Hs1.
    destruct s1 as [di1| ]; [ idtac | discriminate Ht ].
    destruct (lt_dec (I_mul_algo x 1 (S di1)) 2) as [H1| H1].
     destruct Hs1 as (Hn1, Ht1).
     unfold I_mul_algo in Ht1; simpl in Ht1.
     destruct di1.
      unfold summation in Ht1; simpl in Ht1.
      rewrite Hx0 in Ht1; exfalso; apply Ht1; reflexivity.

      unfold I_mul_algo in H1; simpl in H1.
      unfold summation in H1; simpl in H1.
      rewrite Hx0, Hx1 in H1; simpl in H1.
      destruct di1.
       simpl in H1.
       destruct b.
        revert H1; apply Nat.lt_irrefl.

        unfold summation in Ht1; simpl in Ht1.
        rewrite Hx0, Hx1 in Ht1; apply Ht1; reflexivity.

       destruct b.
        assert (1 < S (S di1)) as H by omega.
        apply Hn1 in H; simpl in H.
        unfold I_mul_algo in H; simpl in H.
        unfold summation in H; simpl in H.
        rewrite Hx0, Hx1 in H; simpl in H.
        discriminate H.

        simpl in H1.
        remember (x .[ 2]) as b eqn:Hx2 .
        symmetry in Hx2.
        destruct b.
         simpl in H1.
         do 2 apply lt_S_n in H1.
         revert H1; apply Nat.nlt_0_r.

         unfold summation in Ht1; simpl in Ht1.
         simpl in H1.
         apply lt_S_n in H1.
         apply Nat.lt_1_r in H1.
         rewrite Hx0, Hx1, Hx2, H1 in Ht1; simpl in Ht1.
         apply Ht1; reflexivity.

     discriminate Ht.

    unfold I_mul_i in Ht; simpl in Ht.
    unfold propag_carry_once in Ht; simpl in Ht.
    remember (fst_not_1 (I_mul_algo x 1) 1) as s1 eqn:Hs1 .
    apply fst_not_1_iff in Hs1; simpl in Hs1.
    destruct s1 as [di1| ].
     destruct (lt_dec (I_mul_algo x 1 (S di1)) 2) as [H1| H1].
      unfold I_mul_algo in Ht; simpl in Ht.
      unfold summation in Ht; discriminate Ht.

      unfold I_mul_algo in H1; simpl in H1.
      destruct Hs1 as (Hn1, Ht1).
      destruct di1.
       unfold summation in H1; simpl in H1.
       rewrite Hx0 in H1; simpl in H1.
       exfalso; apply H1, Nat.lt_0_succ.

       pose proof (Hn1 0 (Nat.lt_0_succ di1)) as H.
       unfold I_mul_algo in H; simpl in H.
       unfold summation in H; simpl in H.
       rewrite Hx0 in H; discriminate H.

     pose proof (Hs1 0) as H; simpl in H.
     unfold I_mul_algo in H; simpl in H.
     unfold summation in H; simpl in H.
     rewrite Hx0 in H; discriminate H.

   right; simpl.
   split; intros di.
    exfalso.
    destruct i.
     unfold I_mul_i in Ht.
     simpl in Ht.
     unfold propag_carry_once at 1 in Ht; simpl in Ht.
     remember (propag_carry_once (I_mul_algo x 1)) as z.
     remember (fst_not_1 z 2) as s1 eqn:Hs1 .
     apply fst_not_1_iff in Hs1; simpl in Hs1.
     destruct s1 as [di1| ].
      destruct Hs1 as (Hn1, Ht1).
      remember (nat_compare (z 1) 1) as c1 eqn:Hc1 .
      symmetry in Hc1.
      destruct (lt_dec (z (S (S di1))) 2) as [H1| H1].
       remember (z (S (S di1))) as m eqn:Hz1 .
       symmetry in Hz1.
       destruct m; [ clear Ht1 H1 | idtac ].
        destruct c1.
         apply nat_compare_eq in Hc1.
         rewrite Hc1 in Ht; simpl in Ht.
         unfold n2b in Ht; apply negb_sym in Ht; simpl in Ht.
         rewrite Heqz in Hc1.
         unfold propag_carry_once in Hc1; simpl in Hc1.
         remember (fst_not_1 (I_mul_algo x 1) 2) as s2 eqn:Hs2 .
         apply fst_not_1_iff in Hs2; simpl in Hs2.
         destruct s2 as [di2| ].
          destruct Hs2 as (Hn2, Ht2).
          rewrite I_mul_algo_1 in Hc1; simpl in Hc1.
          rewrite Nat.mul_1_r in Hc1.
          remember (nat_compare (b2n (x .[ 0])) 1) as c2 eqn:Hc2 .
          symmetry in Hc2.
          destruct (lt_dec (I_mul_algo x 1 (S (S di2))) 2) as [H2| H2].
           remember (I_mul_algo x 1 (S (S di2))) as m eqn:Hm2 .
           symmetry in Hm2.
           destruct m; [ clear Ht2 H2 | idtac ].
            unfold I_mul_algo in Hm2; simpl in Hm2.
            unfold summation in Hm2; simpl in Hm2.
            destruct c2.
             rewrite Hc1 in Hm2; discriminate Hm2.

             rewrite Hc1 in Hm2; discriminate Hm2.

             destruct (x .[ 0]); discriminate Hc1.

            destruct m; [ apply Ht2; reflexivity | idtac ].
            do 2 apply Nat.succ_lt_mono in H2.
            revert H2; apply Nat.nlt_0_r.

           destruct c2; [ discriminate Hc1 | idtac | idtac ].
            remember (x .[ 0]) as b eqn:Hx0 .
            destruct b; [ discriminate Hc1 | clear Hc1 ].
            symmetry in Hx0; clear Hc2.
            apply Nat.nlt_ge in H2; clear Ht2.
            destruct di2.
             unfold I_mul_algo in H2; simpl in H2.
             unfold summation in H2; simpl in H2.
             rewrite Hx0, Ht in H2; simpl in H2.
             apply Nat.nlt_ge in H2.
             apply H2, Nat.lt_0_succ.

             pose proof (Hn2 0 (Nat.lt_0_succ di2)) as H.
             unfold I_mul_algo in H; simpl in H.
             unfold summation in H; simpl in H.
             rewrite Hx0, Ht in H; discriminate H.

            destruct (x .[ 0]); discriminate Hc1.
bbb.

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
