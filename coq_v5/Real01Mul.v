(* multiplication in I *)

Require Import Utf8 QArith NPeano Misc Oracle.
Require Import Digit Real01 Real01Add Real01AddMono Real01Cmp.

Open Scope nat_scope.

Fixpoint summation_loop b len g :=
  match len with
  | O => O
  | S len1 => g b + summation_loop (S b) len1 g
  end.

Definition summation b e g := summation_loop b (S e - b) g.

Notation "'Σ' ( i = b , e ) , g" := (summation b e (λ i, (g)))
  (at level 0, i at level 0, b at level 60, e at level 60, g at level 40).

Fixpoint int_pow a b :=
  match b with
  | 0 => 1
  | S b1 => a * int_pow a b1
  end.

Fixpoint logn_loop n m a :=
  match m with
  | 0 => 0
  | S m1 =>
      match a with
      | 0 => 0
      | S a1 => S (logn_loop n m1 (a / n))
      end
  end.

Definition logn n a := pred (logn_loop n a a).

Definition base := 2.

Definition d2n d := if Digit.dec d then 1 else 0.
Definition n2d n := match n with 0 => 0%D | S n1 => 1%D end.

(*
Definition modb n := n mod 2.
Definition divb n := n / 2.
*)

Definition I_mul_algo x y i := Σ (j=1,i), (d2n (x.[j-1]) * d2n (y.[i-j])).
Arguments I_mul_algo x%I y%I i%nat.

Definition summation_for_u2z b n u i :=
  Σ (k = 0, n), u (i + k) * int_pow b (n - k).

Definition z_of_u b u i :=
  let n := logn b (i * (b - 1) + b) + 2 in
  n2d (summation_for_u2z b n u i / int_pow b n mod b).

Definition I_mul_i x y := z_of_u base (I_mul_algo x y).
Definition I_mul x y := {| rm := I_mul_i x y |}.

Notation "x * y" := (I_mul x y) : I_scope.

(* *)

Theorem eq_d2n_0 : ∀ b, d2n b = 0 → (b = 0)%D.
Proof.
intros b Hb.
unfold d2n in Hb.
destruct (Digit.dec b); [ discriminate Hb | assumption ].
Qed.

Theorem eq_d2n_1 : ∀ b, d2n b = 1 → (b = 1)%D.
Proof.
intros b Hb.
unfold d2n in Hb.
destruct (Digit.dec b); [ assumption | discriminate Hb ].
Qed.

Theorem le_d2n_1 : ∀ b, d2n b ≤ 1.
Proof.
intros b.
unfold d2n.
destruct (Digit.dec b); [ reflexivity | apply Nat.le_0_l ].
Qed.

Theorem n2d_0_iff : ∀ n, (n2d n = 0)%D ↔ n = 0.
Proof.
intros n; split; intros Hn; [ idtac | subst n; reflexivity ].
unfold n2d in Hn.
destruct n; [ reflexivity | discr_digit Hn ].
Qed.

Theorem n2d_eq : ∀ a b, a = b → (n2d a = n2d b)%D.
Proof. intros; subst; reflexivity. Qed.

Theorem digit_d2n_eq_iff : ∀ d e, (d = e)%D ↔ d2n d = d2n e.
Proof.
intros d e.
split; intros Hde.
 unfold d2n.
 destruct (Digit.dec d) as [H1| H1].
  destruct (Digit.dec e) as [H2| H2]; [ reflexivity | exfalso ].
  rewrite H1, H2 in Hde; discr_digit Hde.

  destruct (Digit.dec e) as [H2| H2]; [ exfalso | reflexivity ].
  rewrite H1, H2 in Hde; discr_digit Hde.

 unfold d2n in Hde.
 destruct (Digit.dec d) as [H1| H1].
  destruct (Digit.dec e) as [H2| H2]; [ clear Hde | discriminate Hde ].
  rewrite H1, H2; reflexivity.

  destruct (Digit.dec e) as [H2| H2]; [ discriminate Hde | clear Hde ].
  rewrite H1, H2; reflexivity.
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

Theorem summation_compat : ∀ g h b e,
  (∀ i, b ≤ i ≤ e → g i = h i)
  → Σ (i = b, e), g i = Σ (i = b, e), h i.
Proof.
intros g h b e H.
apply summation_loop_compat.
intros i Hie.
apply H; omega.
Qed.

Theorem summation_loop_succ_first : ∀ g b len,
  summation_loop b (S len) g =
  g b + summation_loop (S b) len g.
Proof. reflexivity. Qed.

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

Theorem summation_split_first : ∀ g b k,
  b ≤ k
  → Σ (i = b, k), g i = g b + Σ (i = S b, k), g i.
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ.
rewrite <- summation_loop_succ_first.
rewrite <- Nat.sub_succ_l; [ reflexivity | assumption ].
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

Theorem summation_le : ∀ f n, (∀ i, f i ≤ 1) → Σ (i = 1, n), f i ≤ n.
Proof.
intros f n Hf.
induction n; [ reflexivity | idtac ].
rewrite summation_split_last; [ idtac | apply le_n_S, Nat.le_0_l ].
remember 1 as one; rewrite <- Nat.add_1_r; subst one.
apply Nat.add_le_mono; [ assumption | apply Hf ].
Qed.

Theorem summation_split : ∀ b1 e1 f k,
  b1 ≤ k ≤ e1
  → Σ (i = b1, e1), f i =
    Σ (i = b1, k), f i + Σ (i = S k, e1), f i.
Proof.
intros b1 e1 f k (Hb, He).
revert b1 k Hb He.
induction e1; intros.
 apply Nat.le_0_r in He; subst k.
 apply Nat.le_0_r in Hb; subst b1.
 symmetry; rewrite Nat.add_comm.
 rewrite summation_empty; [ reflexivity | apply Nat.lt_0_1 ].

 destruct (le_dec k e1) as [H1| H1].
  rewrite summation_split_last; [ idtac | eapply le_trans; eassumption ].
  rewrite summation_split_last; [ idtac | apply le_n_S; assumption ].
  erewrite IHe1; [ idtac | eassumption | assumption ].
  rewrite Nat.add_assoc; reflexivity.

  apply Nat.nle_gt in H1.
  apply Nat.le_antisymm in He; [ subst k; clear H1 | assumption ].
  symmetry; rewrite Nat.add_comm.
  rewrite summation_empty; [ reflexivity | idtac ].
  apply Nat.lt_succ_r; reflexivity.
Qed.

Theorem summation_split3 : ∀ b1 e1 f k,
  b1 ≤ k < e1
  → Σ (i = b1, e1), f i =
    Σ (i = b1, k), f i + f (S k) + Σ (i = S (S k), e1), f i.
Proof.
intros b1 e1 f k (Hb, He).
rewrite summation_split with (k := k).
 rewrite <- Nat.add_assoc; f_equal.
 apply summation_split_first; assumption.

 split; [ assumption | apply Nat.lt_le_incl; assumption ].
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

Theorem z_of_u_compat_l : ∀ b u v n,
  (∀ i, u i = v i)
  → (z_of_u b u n = z_of_u b v n)%D.
Proof.
intros b u v n Huv.
unfold z_of_u; simpl.
unfold summation_for_u2z; simpl.
apply eq_digit_eq; f_equal; f_equal; f_equal.
apply summation_compat; intros i Hi.
rewrite Huv; reflexivity.
Qed.

Theorem I_mul_i_comm : ∀ x y i, (I_mul_i x y i = I_mul_i y x i)%D.
Proof.
intros x y i.
unfold I_mul_i; simpl.
apply z_of_u_compat_l.
apply I_mul_algo_comm.
Qed.

Theorem I_mul_comm : ∀ x y, (x * y = y * x)%I.
Proof.
intros x y.
unfold I_eq; intros i; simpl.
unfold I_add_i; simpl.
rewrite I_mul_i_comm; f_equal.
apply Digit.add_compat; [ reflexivity | idtac ].
apply carry_compat_r.
clear i; intros i.
unfold I_mul; simpl.
apply I_mul_i_comm.
Qed.

(* 0 absorbing element *)

Theorem I_mul_algo_0_l : ∀ x y,
  I_eqs x 0
  → ∀ i, I_mul_algo x y i = 0.
Proof.
intros x y Hx i.
unfold I_mul_algo.
apply all_0_summation_0; intros j Hj.
unfold I_eqs in Hx.
unfold d2n; simpl.
destruct (Digit.dec (x.[j-1])) as [Hxj|Hxj]; [ simpl | reflexivity ].
rewrite Hx in Hxj; discr_digit Hxj.
Qed.

Theorem int_pow_neq_0 : ∀ a b, a ≠ 0 → int_pow a b ≠ 0.
Proof.
intros a b Ha.
induction b; [ intros H; discriminate H | simpl ].
apply Nat.neq_mul_0; split; assumption.
Qed.

Theorem I_mul_i_0_l : ∀ x y,
  I_eqs x 0
  → ∀ i, (I_mul_i x y i = 0)%D.
Proof.
intros x y Hx i.
unfold I_mul_i.
unfold z_of_u, base; simpl.
rewrite Nat.mul_1_r.
unfold summation_for_u2z.
rewrite fold_sub_succ_l, divmod_mod.
apply n2d_0_iff.
rewrite all_0_summation_0.
 rewrite Nat.div_0_l; [ reflexivity | idtac ].
 apply int_pow_neq_0; intros H; discriminate H.

 intros k Hk.
 apply Nat.eq_mul_0; left.
 apply I_mul_algo_0_l; assumption.
Qed.

Theorem I_mul_0_l : ∀ x, (0 * x = 0)%I.
Proof.
intros x.
unfold I_eq; intros i; simpl.
unfold I_add_i; simpl.
rewrite carry_diag; simpl.
rewrite I_mul_i_0_l; [ idtac | reflexivity ].
rewrite Digit.add_0_l.
unfold carry; simpl.
remember (fst_same (0%I * x) 0 (S i)) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1| ].
 destruct Hs1 as (Hn1, Ht1); assumption.

 exfalso.
 pose proof (Hs1 0) as H; simpl in H.
 rewrite Nat.add_0_r in H.
 remember (S i) as si.
 unfold I_mul_i in H; subst si.
 rewrite z_of_u_compat_l in H; [ idtac | apply I_mul_algo_0_l; reflexivity ].
 unfold z_of_u in H; simpl in H.
 rewrite fold_sub_succ_l, divmod_mod in H.
 rewrite Digit.opp_0 in H.
 apply Digit.not_0_iff_1 in H.
 apply H; clear H.
 apply n2d_0_iff.
 apply Nat.mod_divide; [ intros H; discriminate H | idtac ].
 exists 0; simpl.
 apply Nat.div_small.
 unfold summation_for_u2z; simpl.
 rewrite all_0_summation_0.
  apply Nat.nle_gt; intros H.
  apply Nat.le_0_r in H.
  revert H; apply int_pow_neq_0; intros H; discriminate H.

  intros k Hk; reflexivity.
Qed.

(* compatibility with equality *)

Theorem I_eqs_mul_algo_compat_r : ∀ x y z i,
  (x == y)%I
  → I_mul_algo x z i = I_mul_algo y z i.
Proof.
intros x y z i Hxy.
unfold I_mul_algo.
unfold summation.
rewrite Nat.sub_succ, Nat.sub_0_r.
apply summation_loop_compat.
intros j Hji; unfold d2n; unfold I_eqs in Hxy.
rewrite minus_plus.
destruct (Digit.dec (x.[j])) as [Hx|Hx].
 destruct (Digit.dec (y.[j])) as [Hy|Hy]; [ reflexivity | idtac ].
 rewrite Hxy, Hy in Hx; discr_digit Hx.

 destruct (Digit.dec (y.[j])) as [Hy|Hy]; [ idtac | reflexivity ].
 rewrite Hxy, Hy in Hx; discr_digit Hx.
Qed.

Theorem I_eqs_mul_i_compat_r : ∀ x y z i,
  (x == y)%I
  → (I_mul_i x z i = I_mul_i y z i)%D.
Proof.
intros x y z i Hxy.
unfold I_mul_i.
unfold z_of_u; simpl.
do 2 rewrite fold_sub_succ_l, divmod_mod.
apply n2d_eq; f_equal.
unfold summation_for_u2z; f_equal.
apply summation_compat; intros k Hk; f_equal.
apply I_eqs_mul_algo_compat_r; assumption.
Qed.

Theorem I_eqs_mul_compat_r : ∀ x y z, (x == y)%I → (x * z == y * z)%I.
Proof.
intros x y z Hxy.
intros i; simpl.
apply I_eqs_mul_i_compat_r; assumption.
Qed.

Theorem I_mul_algo_le : ∀ x y i, I_mul_algo x y i ≤ i.
Proof.
intros x y i.
unfold I_mul_algo; simpl.
apply summation_le; intros j; unfold d2n.
destruct (Digit.dec (x.[j-1])); [ idtac | apply Nat.le_0_l ].
destruct (Digit.dec (y.[i-j])); [ reflexivity | apply Nat.le_0_l ].
Qed.

Theorem fold_I_add_i : ∀ x y i, I_add_i x y i = (x + y)%I.[i].
Proof. intros; reflexivity. Qed.

(* compatibility with strong equality (==) *)
Theorem I_mul_add_0_r_eqs : ∀ x y,
  (x ≠≠ 1)%I
  → (y ≠≠ 1)%I
  → ((x + 0) * y == x * y)%I.
Proof.
intros x y Hxn1 Hyn1.
destruct (I_eqs_dec (x + 0)%I x) as [H1| H1].
 apply I_eqs_mul_compat_r; assumption.

 destruct (I_zerop y) as [Hz| Hnz].
  apply I_zero_iff in Hz; simpl in Hz.
  destruct Hz as [Hz| Hz].
   intros i; simpl.
   rewrite I_mul_i_comm.
   rewrite I_mul_i_0_l; [ idtac | assumption ].
   rewrite I_mul_i_comm.
   rewrite I_mul_i_0_l; [ reflexivity | assumption ].

   exfalso; apply Hyn1; clear Hyn1; assumption.

  assert (x + 0 = x)%I as H by apply I_add_0_r.
  apply I_eq_iff in H; simpl in H.
  destruct H as [H| (i, (Hlt, (Heq, Hgt)))].
   exfalso; apply H1; assumption.

   destruct Hgt as [(Hi, (Hx, Hy))| (Hx, Hy)].
    subst i; clear Hlt.
    unfold I_eqs in H1; simpl in H1.
    unfold I_compare in H1; simpl in H1.
    remember (fst_same (x + 0%I) (- x) 0) as s1 eqn:Hs1 .
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    destruct s1 as [dj1| ].
     destruct Hs1 as (Hn1, Ht1).
     clear H1 Heq; rewrite Hx, Hy in Ht1; clear dj1 Hn1.
     destruct (Digit.dec (x .[ 0])) as [H1| H1].
      exfalso; apply Hxn1; clear Hxn1.
      intros i; simpl.
      rewrite Hy, H1; reflexivity.

      rewrite H1, Digit.opp_0 in Ht1.
      unfold I_add_i in Ht1; simpl in Ht1.
      rewrite H1 in Ht1.
      do 2 rewrite Digit.add_0_l in Ht1.
      unfold carry in Ht1; simpl in Ht1.
      remember (fst_same x 0 1) as s2 eqn:Hs2 .
      apply fst_same_sym_iff in Hs2; simpl in Hs2.
      destruct s2 as [dj2| ]; [ idtac | clear Ht1 ].
       destruct Hs2 as (Hn2, Ht2).
       rewrite Ht2 in Ht1; discr_digit Ht1.

       pose proof (Hy 1) as H; rewrite H1, Hs2 in H; discr_digit H.

     exfalso; apply Heq; rewrite Hs1.
     apply Digit.opp_involutive.

    destruct (Digit.dec (x .[ i])) as [H2| H2].
     exfalso; apply Heq; clear Heq.
     unfold I_add_i; simpl; rewrite H2.
     do 2 rewrite Digit.add_1_l.
     apply Digit.opp_1_iff.
     unfold carry; simpl.
     remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
     apply fst_same_sym_iff in Hs1; simpl in Hs1.
     destruct s1 as [dj1| ]; [ destruct Hs1; assumption | exfalso ].
     pose proof (Hs1 0) as H; simpl in H.
     rewrite <- Nat.add_succ_r, Hy, Digit.opp_0 in H.
     exfalso; apply H1; clear H1.
     intros j; simpl.
     destruct (lt_eq_lt_dec j i) as [[H1| H1]| H1].
      apply Hlt; assumption.

      subst j.
      rewrite H2, H; reflexivity.

      rename H into H3.
      pose proof (Hx (j - S i)) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rewrite H, H2; symmetry; clear H.
      pose proof (Hs1 (j - S i)) as H.
      rewrite <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H; assumption.

     rewrite H2 in Heq.
     apply Digit.not_0_iff_1 in Heq.
     assert (∀ di, (x .[ i + S di] = 1)%D) as H by (intros; rewrite Hy; auto).
     clear Hy; rename H into Hy; move Hy before Hx.
     intros j; simpl.
     unfold I_mul_i; simpl.
     unfold I_mul_algo; simpl.
     unfold z_of_u, base; simpl.
     unfold summation_for_u2z; simpl.
     do 2 rewrite fold_sub_succ_l, divmod_mod.
     rewrite Nat.mul_1_r.
     remember (logn 2 (j + 2) + 2) as m eqn:Hm .
     apply eq_digit_eq; do 3 f_equal.
     destruct (lt_dec (j + m) (S i)) as [H3| H3].
      apply summation_compat.
      intros k Hk; f_equal.
      apply summation_compat.
      intros l Hl; f_equal.
      apply digit_d2n_eq_iff, Hlt.
      revert H3 Hk Hl; clear; intros; omega.

      apply Nat.nlt_ge in H3.
      destruct (lt_dec i j) as [H4| H4].
       destruct i.
bbb.
        apply summation_compat.
        intros k (Hk, Hkm); f_equal.
        apply summation_compat.
        intros l (Hl, Hljk); f_equal.

         Focus 2.
         intros k Hk.
         apply Nat.mul_cancel_r.
          apply int_pow_neq_0; intros H; discriminate H.


          apply summation_split with (k := 1).
          split; [ reflexivity | idtac ].
          eapply Nat.le_trans; [ eassumption | idtac ].
          apply Nat.le_sub_le_add_l; rewrite Nat.sub_diag.
          apply Nat.le_0_l.

         simpl.
bbb.

        erewrite summation_compat.
         Focus 2.
         intros k Hk.
        apply Nat.mul_cancel_r.
         apply int_pow_neq_0; intros H; discriminate H.

         destruct i.
          apply summation_split with (k := 1).
          split; [ reflexivity | idtac ].
          eapply Nat.le_trans; [ eassumption | idtac ].
          apply Nat.le_sub_le_add_l; rewrite Nat.sub_diag.
          apply Nat.le_0_l.

          simpl.
          rewrite summation_split3 with (k := i).
simpl.
Show Script.
           apply summation_split3 with (k := i).
bbb.
  ============================
   1 ≤ i < j + k

         apply summation_split with (k := S i).
         split; [ apply le_n_S, Nat.le_0_l | idtac ].
         eapply Nat.le_trans; [ eassumption | idtac ].
         apply Nat.le_sub_le_add_l; rewrite Nat.sub_diag.
         apply Nat.le_0_l.

        simpl; symmetry.
        erewrite summation_compat.
         Focus 2.
         intros k Hk.
         apply Nat.mul_cancel_r.
          apply int_pow_neq_0; intros H; discriminate H.

          apply summation_split with (k := S i).
          split; [ apply le_n_S, Nat.le_0_l | idtac ].
          eapply Nat.le_trans; [ eassumption | idtac ].
          apply Nat.le_sub_le_add_l; rewrite Nat.sub_diag.
          apply Nat.le_0_l.

         simpl.
bbb.

     .   i   .   .
  x  .   1   0   0   0 …
     =   ≠
  y  .   0   1   1   1 …
bbb.

Theorem I_mul_compat_r : ∀ x y z,
  ¬I_eqs x 1
  → ¬I_eqs y 1
  → (x = y)%I
  → (x * z = y * z)%I.
Proof.
intros x y z Hxn1 Hyn1 Hxy.
apply I_eq_iff in Hxy.
destruct Hxy as [Hxy| (i, (Hlt, (Heq, Hgt)))].
 apply I_eqs_eq, I_eqs_mul_compat_r; assumption.

 unfold I_eqs in Hxn1; simpl in Hxn1.
 unfold I_eqs in Hyn1; simpl in Hyn1.
 destruct Hgt as [(Hi, (Hx, Hy))| (Hx, Hy)].
  subst i; clear Hlt.
  remember (x .[ 0]) as b eqn:Hxi .
  apply Digit.neq_eq_opp, Digit.opp_sym in Heq.
  apply eq_digit_eq in Hxi; symmetry in Hxi.
  destruct (Digit.dec b) as [H| H].
   exfalso; apply Hxn1.
   intros i; rewrite Hx; assumption.

   exfalso; apply Hyn1.
   intros i; rewrite Hy, Heq, H; reflexivity.

  remember (x .[ i]) as b eqn:Hxi .
  apply Digit.neq_eq_opp, Digit.opp_sym in Heq.
  apply eq_digit_eq in Hxi; symmetry in Hxi.
  destruct (Digit.dec b) as [H1| H1].
   assert (x == y + 0)%I.
    apply I_eqs_iff; intros j; simpl.
    unfold I_add_i; simpl.
    rewrite Digit.add_0_r; simpl.
    unfold carry; simpl.
    remember (fst_same y 0 (S j)) as s1 eqn:Hs1.
    apply fst_same_sym_iff in Hs1; simpl in Hs1.
    destruct (lt_eq_lt_dec j i) as [[H2| H2]| H2].
     remember H2 as H; clear HeqH.
     apply Hlt in H; rewrite H.
     destruct s1 as [dj1| ].
      destruct Hs1 as (Hn1, Ht1).
      rewrite Ht1, Digit.add_0_r; reflexivity.

      clear H.
      pose proof Hs1 (i - S j) as H.
      rewrite <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rewrite Heq, H1 in H; discr_digit H.

     subst j.
     destruct s1 as [dj1| ].
      destruct Hs1 as (Hn1, Ht1).
      rewrite <- Nat.add_succ_r, Hy, H1 in Ht1; discr_digit Ht1.

      rewrite Hxi, Heq, H1; reflexivity.

     destruct s1 as [dj1| ].
      destruct Hs1 as (Hn1, Ht1).
      pose proof Hy (j + dj1 - i) as H.
      rewrite Nat.add_succ_r in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | omega ].
      rewrite Nat.add_comm, Nat.add_sub, Ht1 in H.
      rewrite H1 in H; discr_digit H.

      pose proof Hx (j - S i) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rewrite H, Heq; clear H.
      pose proof Hy (j - S i) as H.
      rewrite Nat.add_succ_r, <- Nat.add_succ_l in H.
      rewrite Nat.add_sub_assoc in H; [ idtac | assumption ].
      rewrite Nat.add_comm, Nat.add_sub in H.
      rewrite H, Digit.add_comm; reflexivity.

   symmetry.
   rewrite <- oups_I_mul_compat_r; symmetry. (* I_mul_add_0_r *)
   apply I_eqs_eq, I_eqc_eqs_iff.
   apply I_eqs_mul_compat_r.
   apply I_eqc_eqs_iff; assumption.

bbb.

     .   i   .   .
  x  .   1   0   0   0 …
     =   ≠
  y  .   0   1   1   1 …

   apply I_add_i_compat.
   clear k; intros k; simpl.
   unfold I_mul_i; simpl.

bbb.

   exfalso; apply Hyn1; intros k.
   destruct (lt_eq_lt_dec k i) as [[H2| H2]| H2].
    remember H2 as H; clear HeqH.
    apply Hlt in H.
bbb.

  unfold I_eq; simpl; intros k.
  unfold I_add_i; simpl.
  do 2 rewrite xorb_false_r.
  unfold I_mul_i.
  remember (I_propag_carry (I_mul_algo x z) (S k) k) as nb1 eqn:Hnb1 .
  remember (I_propag_carry (I_mul_algo y z) (S k) k) as nb2 eqn:Hnb2 .
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
      pose proof (Hs2 0) as H.
      rewrite Nat.add_0_r in H.
      unfold I_mul_i in H.
      remember (I_propag_carry (I_mul_algo y z) (S (S k)) (S k)) as nb3.
      rename Heqnb3 into Hnb3.
      symmetry in Hnb3.
      destruct nb3; [ discriminate H | clear H ].
      destruct b; simpl in Hy, Heq.
       rewrite if_0_propag_carry_0 in Hnb3; [ discriminate Hnb3 | idtac ].
       intros i.
       apply I_mul_algo_0_l; assumption.

bbb.
       destruct dj1.
        Focus 2.
        pose proof (Hn1 0 (Nat.lt_0_succ dj1)) as H.
        rewrite Nat.add_0_r in H.
        rewrite I_mul_i_0_l in H; [ discriminate H | assumption ].

        clear Hn1; rewrite Nat.add_0_r in Ht1.
        unfold I_mul_i in Ht1.
        remember (I_propag_carry (I_mul_algo x z) (S (S k)) (S k)) as nb4.
        rename Heqnb4 into Hnb4.
        symmetry in Hnb4.
        destruct nb4; [ clear Ht1 | discriminate Ht1 ].
        move Hnb4 before Hnb3.
vvv.
        rewrite Nat.add_succ_r in Hnb2; simpl in Hnb2.
        unfold propag_carry_once in Hnb2.
        apply Nat.eq_add_0 in Hnb2.
        destruct Hnb2 as (Hnb5, Hnb2).
        rewrite Nat.add_1_r in Hnb2.
        apply Nat.div_small_iff in Hnb2; [ idtac | intros H; discriminate H ].
        simpl in Hnb2.
bbb.

(* neutral element *)

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
rewrite Nat.div_small; [ idtac | apply le_n_S, le_d2n_1 ].
rewrite Nat.mod_0_l; [ idtac | intros H; discriminate H ].
rewrite Nat.add_0_l.
rewrite Nat.mod_small; [ idtac | apply le_n_S, le_d2n_1 ].
unfold summation; simpl.
do 2 rewrite divmod_div.
do 2 rewrite Nat.mul_1_r.
rewrite Nat.add_0_r.
remember (x .[ 0]) as b0 eqn:Hx0 .
remember (x .[ 1]) as b1 eqn:Hx1 .
symmetry in Hx0, Hx1.
unfold n2d.
destruct b0, b1; try reflexivity; simpl.
destruct Hx01 as [H| H]; discriminate H.
Qed.

Theorem I_mul_algo_1 : ∀ x y, I_mul_algo x y 1 = d2n (x.[0]) * d2n (y.[0]).
Proof.
intros x y.
unfold I_mul_algo, summation; simpl.
apply Nat.add_0_r.
Qed.

Theorem I_mul_algo_1_r : ∀ x i,
  I_mul_algo x 1 i = Σ (k = 1, i), d2n (x.[k-1]).
Proof.
intros x i.
unfold I_mul_algo; simpl.
unfold summation.
apply summation_loop_compat.
intros j Hj.
rewrite Nat.mul_1_r; reflexivity.
Qed.

Theorem I_mul_algo_1_succ : ∀ x i,
  I_mul_algo x 1 (S i) = I_mul_algo x 1 i + d2n (x.[i]).
Proof.
intros x i.
do 2 rewrite I_mul_algo_1_r.
rewrite summation_split_last; [ idtac | apply le_n_S, Nat.le_0_l ].
simpl; rewrite Nat.sub_0_r; reflexivity.
Qed.

Theorem yyy : ∀ x y u i,
  u = I_mul_algo x y
  → I_propag_carry u (S (S i)) i = I_propag_carry u (S i) i.
Proof.
intros x y u i Hu; simpl.
remember (propag_carry_once (I_propag_carry u i)) as u1 eqn:Hu1 .
unfold propag_carry_once; simpl.
remember (fst_not_1 u1 (S i)) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Ht1).
 destruct (zerop (u1 (S (i + di1)))) as [H1| H1].
  clear Ht1.
  destruct (le_dec (u1 i) 1) as [H2| H2]; [ reflexivity | idtac ].
  apply Nat.nle_gt in H2.
  exfalso.
  rewrite Hu1 in H1; simpl in H1.
  unfold propag_carry_once in H1; simpl in H1.
  remember (I_propag_carry u i) as u2 eqn:Hu2 .
  remember (fst_not_1 u2 (S (S (i + di1)))) as s2 eqn:Hs2 .
  apply fst_not_1_iff in Hs2; simpl in Hs2.
  destruct s2 as [di2| ].
   destruct Hs2 as (Hn2, Ht2).
   destruct (zerop (u2 (S (S (i + di1 + di2))))) as [H3| H3].
    clear Ht2.
    destruct (le_dec (u2 (S (i + di1))) 1) as [H4| H4].
     clear H4.
     rewrite Hu1 in H2; simpl in H2.
     unfold propag_carry_once in H2; simpl in H2.
     remember (fst_not_1 u2 (S i)) as s3 eqn:Hs3 .
     apply fst_not_1_iff in Hs3; simpl in Hs3.
     destruct s3 as [di3| ].
      destruct Hs3 as (Hn3, Ht3).
      destruct (zerop (u2 (S (i + di3)))) as [H4| H4].
       clear Ht3.
       destruct (le_dec (u2 i) 1) as [H5| H5].
        apply Nat.nle_gt in H2; contradiction.

        clear H5.
        apply Nat.lt_add_lt_sub_r in H2; simpl in H2.
bbb.
        subst u2.
        destruct i.
         simpl in H2.
         simpl in H4.
         simpl in H1, H3.
         simpl in Hn1, Hn2, Hn3, Hu1.
         destruct di1.
          clear Hn1; simpl in H3.
          simpl in Hn2.
bbb.

Definition nn_add (u v : nat → nat) i := u i + v i.

Theorem zzz : ∀ u v i,
  I_propag_carry (nn_add u v) (S i) i =
  I_propag_carry u (S i) i + I_propag_carry v (S i) i.
Proof.
intros u v i.
simpl.
unfold propag_carry_once; simpl.
remember (I_propag_carry (nn_add u v) i) as uvi eqn:Huvi .
remember (I_propag_carry u i) as ui eqn:Hui .
remember (I_propag_carry v i) as vi eqn:Hvi .
remember (fst_not_1 uvi (S i)) as s1 eqn:Hs1 .
remember (fst_not_1 ui (S i)) as s2 eqn:Hs2 .
remember (fst_not_1 vi (S i)) as s3 eqn:Hs3 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
apply fst_not_1_iff in Hs2; simpl in Hs2.
apply fst_not_1_iff in Hs3; simpl in Hs3.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Ht1).
 destruct (zerop (uvi (S (i + di1)))) as [H1| H1].
  clear Ht1.
  destruct s2 as [di2| ].
   destruct Hs2 as (Hn2, Ht2).
   destruct s3 as [di3| ].
    destruct Hs3 as (Hn3, Ht3).
    destruct (zerop (ui (S (i + di2)))) as [H2| H2].
     clear Ht2.
     destruct (zerop (vi (S (i + di3)))) as [H3| H3].
      clear Ht3.
      destruct (lt_eq_lt_dec di1 di2) as [[H6| H6]| H6].
       remember H6 as H; clear HeqH.
       apply Hn2 in H.
bbb.
      destruct (le_dec (uvi i) 1) as [H4| H4].
       remember (uvi i) as uv eqn:Huv .
       symmetry in Huv.
       destruct uv.
        clear H4.
        rewrite Huvi in Huv.
        destruct i.
         simpl in Huv.
         unfold nn_add in Huv; simpl in Huv.
         apply Nat.eq_add_0 in Huv.
         destruct Huv as (Hu, Hv).
         rewrite Hui, Hvi; simpl.
         rewrite Hu, Hv; reflexivity.

         simpl in Huv.
         unfold propag_carry_once in Huv.
         remember (I_propag_carry (nn_add u v) i) as uvi1 eqn:Huvi1 .
         remember (fst_not_1 uvi1 (S (S i))) as s4 eqn:Hs4 .
         apply fst_not_1_iff in Hs4; simpl in Hs4.
         destruct s4 as [di4| ].
          destruct Hs4 as (Hn4, Ht4).
          destruct (zerop (uvi1 (S (S i + di4)))) as [H5| H5].
           clear Ht4.
           destruct (le_dec (uvi1 (S i)) 1) as [H6| H6].
            clear H6.
bbb.

intros u v i.
unfold propag_carry_once; simpl.
remember (fst_not_1 (nn_add u v) (S i)) as s1 eqn:Hs1 .
remember (fst_not_1 u (S i)) as s2 eqn:Hs2 .
remember (fst_not_1 v (S i)) as s3 eqn:Hs3 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
apply fst_not_1_iff in Hs2; simpl in Hs2.
apply fst_not_1_iff in Hs3; simpl in Hs3.
destruct s1 as [di1| ].
 unfold nn_add in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Ht1).
 unfold nn_add; simpl.
 destruct (zerop (u (S (i + di1)) + v (S (i + di1)))) as [H1| H1].
  apply Nat.eq_add_0 in H1.
  destruct H1 as (Hu, Hv).
  destruct s2 as [di2| ].
   destruct Hs2 as (Hn2, Ht2).
   destruct s3 as [di3| ].
    destruct Hs3 as (Hn3, Ht3).
    destruct (zerop (u (S (i + di2)))) as [H2| H2].
     clear Ht2.
     destruct (zerop (v (S (i + di3)))) as [H3| H3].
      clear Ht3.
      destruct (le_dec (u i + v i) 1) as [H1| H1].
       remember (u i + v i) as uv eqn:Huv .
       symmetry in Huv.
       destruct uv.
        apply Nat.eq_add_0 in Huv.
        destruct Huv as (Hui, Hvi).
        rewrite Hui, Hvi; reflexivity.

        apply Nat.succ_le_mono in H1.
        apply Nat.le_0_r in H1; subst uv.
        apply Nat.eq_add_1 in Huv.
        destruct Huv as [(Hui, Hvi)| (Hui, Hvi)]; rewrite Hui, Hvi.
         reflexivity.

         reflexivity.

       apply Nat.nle_gt in H1.
       destruct (le_dec (u i) 1) as [H4| H4].
        destruct (le_dec (v i) 1) as [H5| H5].
         clear Ht1.
         destruct (lt_eq_lt_dec di1 di2) as [[H6| H6]| H6].
          remember H6 as H; clear HeqH.
          apply Hn2 in H.
          rewrite Hu in H; discriminate H.

          subst di2.
          destruct (lt_eq_lt_dec di1 di3) as [[H7| H7]| H7].
           remember H7 as H; clear HeqH.
           apply Hn3 in H.
           rewrite Hv in H; discriminate H.

           subst di3.
           destruct di1.
            clear Hn1 Hn2 Hn3.
            rewrite Nat.add_0_r in Hu, Hv, H2, H3.
bbb.

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
   symmetry; unfold n2d; simpl.
   destruct s3 as [di3| ]; simpl.
    destruct Hs3 as (Hn3, Ht3).
    destruct (zerop (I_mul_algo x 1 (S di3))) as [H1| H1]; simpl.
     rewrite I_mul_algo_1_r in H1; simpl in H1.
     unfold summation in H1; simpl in H1.
     apply Nat.eq_add_0 in H1.
     destruct H1 as (H1, _).
     apply eq_d2n_0 in H1; assumption.

     remember (I_mul_algo x 1 (S di3)) as m eqn:Hm .
     symmetry in Hm.
     destruct m; [ exfalso; revert H1; apply Nat.nlt_0_r | clear H1 ].
     destruct m; [ exfalso; apply Ht3; reflexivity | clear Ht3 ].
     rewrite I_mul_algo_1_r in Hm; simpl in Hm.
     unfold summation in Hm; simpl in Hm.
     unfold d2n in Hm; simpl in Hm.
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
    apply eq_d2n_1 in H; assumption.

   rewrite xorb_true_r.
   apply negb_sym.
   unfold I_mul_i; simpl.
   unfold propag_carry_once; simpl.
   remember (fst_not_1 (I_mul_algo x 1) 1) as s3 eqn:Hs3 .
   apply fst_not_1_iff in Hs3; simpl in Hs3.
   unfold n2d; simpl.
   destruct s3 as [di3| ]; simpl.
    destruct Hs3 as (Hn3, Ht3).
    destruct (zerop (I_mul_algo x 1 (S di3))) as [H1| H1]; simpl.
     rewrite I_mul_algo_1_r in H1; simpl in H1.
     unfold summation in H1; simpl in H1.
     apply Nat.eq_add_0 in H1.
     destruct H1 as (Hx0, H1).
     apply eq_d2n_0 in Hx0.
     destruct di3; [ clear H1 | simpl in H1 ].
      unfold I_mul_algo in Ht3; simpl in Ht3.
      unfold summation in Ht3; simpl in Ht3.
      rewrite Hx0 in Ht3; simpl in Ht3.
      clear Ht3 Hn3.
      destruct di1.
       clear Hn1.
       unfold I_mul_i in Ht1; simpl in Ht1.
       apply n2d_0_iff in Ht1.
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
           rewrite Hx0, Hs2 in Hm; simpl in Hm.
           apply Nat.succ_inj in Hm.
           destruct di4; [ discriminate Hm | simpl in Hm ].
           rewrite Hs2 in Hm; simpl in Hm.
           apply Nat.succ_inj in Hm.
           destruct di4; simpl in Hm.
            clear m Hm Hn4.
            remember (u (S (S di3))) as m eqn:Hm .
            destruct m; [ exfalso; revert H2; apply Nat.nlt_0_r | clear H2 ].
            destruct m; [ exfalso; apply Ht3; reflexivity | clear Ht3 ].
            symmetry in Hm.
            rewrite Hu in Hm; simpl in Hm.
            unfold propag_carry_once in Hm; simpl in Hm.
            remember (I_mul_algo x 1) as u1 eqn:Hu1 .
            remember (fst_not_1 u1 (S (S (S di3)))) as s4 eqn:Hs4 .
            apply fst_not_1_iff in Hs4; simpl in Hs4.
            destruct s4 as [di4| ].
             destruct Hs4 as (Hn4, Ht4).
             destruct (zerop (u1 (S (S (S (di3 + di4)))))) as [H1| H1].
              clear Ht4; subst u1.
              rewrite I_mul_algo_1_r in H1; simpl in H1.
              unfold summation in H1; simpl in H1.
              rewrite Nat.add_comm, Hs2 in H1; discriminate H1.

              destruct (zerop (u1 (S (S di3)))) as [H2| H2].
               discriminate Hm.

               symmetry in Hm.
               apply Nat_le_sub_add_r in Hm; [ simpl in Hm | assumption ].
               subst u1.
               rewrite I_mul_algo_1_r in Hm; simpl in Hm.
               unfold summation in Hm; simpl in Hm.
               rewrite Hx0, Hs2 in Hm; simpl in Hm.
               apply Nat.succ_inj in Hm.
               destruct di3; [ discriminate Hm | simpl in Hm ].
               rewrite Hs2 in Hm; simpl in Hm.
               apply Nat.succ_inj in Hm.
               destruct di3; [ discriminate Hm | simpl in Hm ].
               rewrite Hs2 in Hm; simpl in Hm.
               apply Nat.succ_inj in Hm.
               destruct di3; simpl in Hm.
                clear Hm.
                pose proof (Hn3 1 Nat.lt_1_2) as H.
                rewrite Hu in H; simpl in H.
                unfold propag_carry_once in H; simpl in H.
                remember (I_mul_algo x 1) as u1 eqn:Hu1 .
                remember (fst_not_1 u1 4) as s5 eqn:Hs5 .
                apply fst_not_1_iff in Hs5; simpl in Hs5.
                destruct s5 as [di5| ].
                 destruct Hs5 as (Hn5, Ht5).
                 destruct (zerop (u1 (S (S (S (S di5)))))) as [H3| H3].
                  clear Ht5.
                  subst u1.
                  rewrite I_mul_algo_1_r in H3; simpl in H3.
                  unfold summation in H3; simpl in H3.
                  rewrite Nat.add_comm, Hs2 in H3; discriminate H3.

                  destruct (zerop (u1 3)) as [H4| H4].
                   clear H; subst u1.
                   rewrite I_mul_algo_1_r in H4; simpl in H4.
                   unfold summation in H4; simpl in H4.
                   rewrite Nat.add_comm, Hs2 in H4; discriminate H4.

                   clear H.
                   pose proof (Hn3 0 (Nat.lt_0_succ 1)) as H.
                   rewrite Hu in H; simpl in H.
                   unfold propag_carry_once in H; simpl in H.
                   remember (fst_not_1 u1 3) as s6 eqn:Hs6 .
                   apply fst_not_1_iff in Hs6; simpl in Hs6.
                   destruct s6 as [di6| ].
                    destruct Hs6 as (Hn6, Ht6).
                    destruct (zerop (u1 (S (S (S di6))))) as [H5| H5].
                     rewrite Hu1 in H5; simpl in H5.
                     rewrite I_mul_algo_1_r in H5; simpl in H5.
                     unfold summation in H5; simpl in H5.
                     rewrite Nat.add_comm, Hs2 in H5; discriminate H5.

                     destruct (zerop (u1 2)) as [H6| H6].
                      clear H.
                      rewrite Hu1 in H6; simpl in H6.
                      rewrite I_mul_algo_1_r in H6; simpl in H6.
                      unfold summation in H6; simpl in H6.
                      rewrite Hx0, Hs2 in H6; discriminate H6.

                      symmetry in H.
                      apply Nat_le_sub_add_r in H; [ idtac | assumption ].
                      simpl in H; clear H6.
                      rewrite Hu1 in H; simpl in H.
                      rewrite I_mul_algo_1_r in H; simpl in H.
                      unfold summation in H; simpl in H.
                      rewrite Hx0, Hs2 in H; discriminate H.

                    clear H.
                    pose proof (Hs6 0) as H; simpl in H.
                    clear H4.
                    rewrite Hu1 in H; simpl in H.
                    rewrite I_mul_algo_1_r in H; simpl in H.
                    unfold summation in H; simpl in H.
                    rewrite Hx0, Hs2, Hs2 in H; discriminate H.

                 clear H.
                 pose proof (Hs5 0) as H; simpl in H.
                 clear H2.
                 rewrite Hu1 in H; simpl in H.
                 rewrite I_mul_algo_1_r in H; simpl in H.
                 unfold summation in H; simpl in H.
                 rewrite Hx0, Hs2, Hs2 in H; discriminate H.

                assert (2 < S (S (S di3))) as H by omega.
                apply Hn3 in H; simpl in H.
                rewrite Hu in H; simpl in H.
                unfold propag_carry_once in H; simpl in H.
                remember (I_mul_algo x 1) as u1 eqn:Hu1 .
                remember (fst_not_1 u1 5) as s5 eqn:Hs5 .
                apply fst_not_1_iff in Hs5; simpl in Hs5.
                destruct s5 as [di5| ].
                 destruct Hs5 as (Hn5, Ht5).
                 destruct (zerop (u1 (S (S (S (S (S di5))))))) as [H3| H3].
                  clear Ht5.
                  rewrite Hu1 in H3; simpl in H3.
                  rewrite I_mul_algo_1_r in H3; simpl in H3.
                  unfold summation in H3; simpl in H3.
                  rewrite Nat.add_comm, Hs2 in H3; discriminate H3.

                  destruct (zerop (u1 4)) as [H4| H4].
                   clear H; subst u1.
                   rewrite I_mul_algo_1_r in H4; simpl in H4.
                   unfold summation in H4; simpl in H4.
                   rewrite Nat.add_comm, Hs2 in H4; discriminate H4.

                   symmetry in H.
                   apply Nat_le_sub_add_r in H; [ idtac | assumption ].
                   rewrite Hu1 in H; simpl in H.
                   rewrite I_mul_algo_1_r in H; simpl in H.
                   unfold summation in H; simpl in H.
                   rewrite Hx0, Hs2, Hs2, Hs2 in H; discriminate H.

                 clear H.
                 pose proof (Hs5 0) as H; simpl in H.
                 rewrite Hu1 in H; simpl in H.
                 rewrite I_mul_algo_1_r in H; simpl in H.
                 unfold summation in H; simpl in H.
                 rewrite Hx0, Hs2, Hs2 in H; discriminate H.

             pose proof (Hs4 0) as H; simpl in H.
             rewrite Hu1 in H; simpl in H.
             rewrite I_mul_algo_1_r in H; simpl in H.
             unfold summation in H; simpl in H.
             rewrite Hx0, Hs2, Hs2 in H; discriminate H.

            clear m Hm.
            assert (1 < S (S di4)) as H by omega.
            apply Hn4 in H; simpl in H.
            rewrite I_mul_algo_1_r in H; simpl in H.
            unfold summation in H; simpl in H.
            rewrite Hx0, Hs2, Hs2 in H; discriminate H.

          pose proof (Hs4 1) as H; simpl in H.
          rewrite I_mul_algo_1_r in H; simpl in H.
          unfold summation in H; simpl in H.
          rewrite Hx0, Hs2, Hs2 in H; discriminate H.

bbb.
-- ou alors avec Hs3 0... ? --
        destruct (zerop (u 1)) as [H1| H1]; [ discriminate Ht1 | idtac ].
        symmetry in Ht1.
        apply Nat_le_sub_add_r in Ht1; [ idtac | assumption ].
        clear H1.
        rewrite Hu in Ht1; simpl in Ht1.
        unfold propag_carry_once in Ht1; simpl in Ht1.
        remember (I_mul_algo x 1) as u1 eqn:Hu1 .
        remember (fst_not_1 u1 2) as s4 eqn:Hs4 .

bbb.

-- version using I_eq_iff --
intros x.
apply I_eq_iff.
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
    apply n2d_0_iff in Ht.
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
        unfold n2d in Hx1; simpl in Hx1.
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
            apply eq_d2n_0 in H1.
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
           apply eq_d2n_0 in H1.
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
           destruct (le_dec (d2n (x .[ 0]))) as [H3| H3].
            clear H3.
            apply eq_d2n_1 in Hd.
            rename Hd into Hx0.
            rewrite I_mul_algo_1_r in H2.
            unfold summation in H2; simpl in H2.
            rewrite Hx0 in H2; discriminate H2.

            destruct (x .[ 0]); discriminate Hd.

           rewrite I_mul_algo_1_r in Hd; simpl in Hd.
           unfold summation in Hd; simpl in Hd.
           rewrite Nat.add_0_r in Hd; simpl in Hd.
           destruct (zerop (d2n (x .[ 0]))) as [H3| H3].
            clear Hd Ht1.
            apply eq_d2n_0 in H3; rename H3 into Hx0.
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
          destruct (zerop (d2n (x .[ 0]))) as [H2| H2].
           clear Hd.
           apply eq_d2n_0 in H2.
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
            apply eq_d2n_0 in Hx0.
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
*)
