(* multiplication in I *)

Require Import Utf8 QArith NPeano Misc.
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

Definition I_mul_algo x y i := Σ (j=1,i), (b2n (x.[j-1]) * b2n (y.[i-j])).
Arguments I_mul_algo x%I y%I i%nat.

Definition propag_carry_once u i := u i mod 2 + u (S i) / 2.

Fixpoint I_propag_carry u n :=
  match n with
  | 0 => u
  | S n1 => propag_carry_once (I_propag_carry u n1)
  end.

Definition I_mul_i x y i :=

  let nb := I_propag_carry (I_mul_algo x y) (i + 2) i in
  if zerop nb then false else true.

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
  I_propag_carry (I_mul_algo y x) i j =
  I_propag_carry (I_mul_algo x y) i j.
Proof.
intros x y i j.
revert j.
induction i; intros; simpl.
 apply I_mul_algo_comm.

 unfold propag_carry_once.
 rewrite IHi; f_equal.
 rewrite IHi; reflexivity.
Qed.

Theorem I_mul_i_comm : ∀ x y i, I_mul_i x y i = I_mul_i y x i.
Proof.
intros x y i.
unfold I_mul_i; simpl.
rewrite Nat.add_succ_r; simpl.
unfold propag_carry_once.
rewrite I_propag_carry_mul_algo_comm, Nat.add_comm.
rewrite I_propag_carry_mul_algo_comm, Nat.add_comm.
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

(* neutral element *)

(* difficulties to prove that...
Theorem I_add_1_r : ∀ x, (I_mul x 1 = x)%I.
Proof.
intros x.
unfold I_eq; simpl; intros i.
unfold I_add_i; simpl.
do 2 rewrite xorb_false_r.
f_equal.
 unfold I_mul_i; simpl.
 bbb.
 rewrite Nat.add_comm; simpl.
 unfold I_mul_algo; simpl.
bbb.
*)

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

Theorem if_0_propag_carry_0 : ∀ x n,
  (∀ i, x i = 0)
  → ∀ j, I_propag_carry x n j = 0.
Proof.
intros x n Hx j.
revert j.
induction n; intros; simpl; [ apply Hx | idtac ].
unfold propag_carry_once.
do 2 rewrite IHn; reflexivity.
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
bbb.
