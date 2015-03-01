(* addition modulo 1 in I: a commutative monoid *)

Require Import Utf8 QArith NPeano Misc.
Require Import Digit Real01 Real01Add.

Open Scope nat_scope.

Theorem forall_add_succ_r : ∀ i f x,
  (∀ j, (f (i + S j)%nat = x)%D)
  → id (∀ j, (f (S i + j)%nat = x)%D).
Proof.
intros i f x; unfold id; intros H j.
rewrite Nat.add_succ_l, <- Nat.add_succ_r; apply H.
Qed.

(* opposite *)

Theorem I_sub_diag : ∀ x, (x - x = 0)%I.
Proof.
intros x.
unfold I_eq; intros i; simpl.
unfold I_add_i, carry.
remember (S i) as si; simpl.
rewrite digit_add_0_r.
rewrite fst_same_diag.
remember (fst_same (x - x) 0 si) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); rewrite Hs1, digit_add_0_r.
 unfold I_add_i, carry.
 rewrite <- Heqsi; simpl.
 remember (fst_same x (- x) si) as s2 eqn:Hs2 .
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 do 2 rewrite digit_add_0_r.
 rewrite digit_opp_add_diag_r.
 apply oppd_0_iff.
 destruct s2 as [di2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Hs2); symmetry in Hs2.
 exfalso; revert Hs2; apply no_fixpoint_oppd.

 destruct (digit_eq_dec (x .[ si]) (oppd (x .[ si]))) as [H1| H1].
  symmetry in H1.
  exfalso; revert H1; apply no_fixpoint_oppd.

  apply I_add_inf_1_neq_if in Hs1.
   simpl in Hs1.
   destruct Hs1 as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
   rewrite Ha in Hb.
   exfalso; revert Hb; apply digit_neq_1_0.

   simpl; rewrite digit_opp_involutive; reflexivity.
Qed.

(* associativity *)

Theorem fst_same_inf_after : ∀ x y i di,
  fst_same x y i = None
  → fst_same x y (i + di) = None.
Proof.
intros x y i di Hs.
apply fst_same_iff in Hs.
apply fst_same_iff; intros dj.
rewrite <- Nat.add_assoc.
apply Hs.
Qed.

Theorem I_add_inf_if : ∀ x y i,
  (∀ dj, (I_add_i x y (i + dj) = 1)%D)
  → ∃ j,
    i < j ∧
    (∀ di, (x.[j + S di] = 1)%D) ∧
    (∀ di, (y.[j + S di] = 1)%D).
Proof.
intros x y i Hj.
destruct (digit_eq_dec (x .[ i]) (y .[ i])) as [H1| H1].
 apply I_add_inf_1_eq_if in Hj; auto.
 destruct Hj as (Ha, Hb).
 exists (S i).
 split; [ apply Nat.lt_succ_diag_r | idtac ].
 split; intros di; rewrite Nat.add_succ_l, <- Nat.add_succ_r.
   apply Ha.

   apply Hb.

 apply digit_neq_eq_opp in H1.
 apply I_add_inf_1_neq_if in Hj; auto.
 destruct Hj as (j, (Hij, (Hni, (Ha, (Hb, (Hat, Hbt)))))).
 exists j.
 split; [ assumption | split; assumption ].
Qed.

Theorem carry_sum_3_noI_assoc_l : ∀ z0 x y z i,
  z = (z0 + 0)%I
  → (carry ((x + y) + z)%I 0 i = 0)%D.
Proof.
intros z0 x y z i Hc0.
unfold carry; simpl.
remember (fst_same ((x + y) + z)%I 0 i) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); assumption.

 apply I_add_inf_if in Hs1.
 destruct Hs1 as (j, (Hij, (Haj, Hbj))).
 rewrite Hc0 in Hbj; simpl in Hbj.
 apply forall_add_succ_r in Hbj.
 apply I_add_inf_if in Hbj.
 destruct Hbj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem carry_sum_3_noI_assoc_r : ∀ x0 x y z i,
  x = (x0 + 0)%I
  → (carry (x + (y + z))%I 0 i = 0)%D.
Proof.
intros x0 x y z i Ha0.
unfold carry; simpl.
remember (fst_same (x + (y + z)%I) 0 i) as s1 eqn:Hs1 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1); assumption.

 apply I_add_inf_if in Hs1.
 destruct Hs1 as (j, (Hij, (Haj, Hbj))).
 rewrite Ha0 in Haj; simpl in Haj.
 apply forall_add_succ_r in Haj.
 apply I_add_inf_if in Haj.
 destruct Haj as (k, (Hjk, (Hak, Hbk))).
 simpl in Hbk.
 symmetry; apply Hbk; assumption.
Qed.

Theorem sum_x1_x_sum_0_0 : ∀ x y i,
  (y.[i] = 1)%D
  → (I_add_i x y i = x.[i])%D
  → (x.[S i] = 0)%D
  → (I_add_i x y (S i) = 0)%D.
Proof.
intros y z i Ht5 Hbd Ht6.
remember (y.[i]) as b eqn:Hb5; symmetry in Hb5.
apply digit_not_1_iff_0; intros H.
unfold I_add_i in H; simpl in H.
rewrite Ht6, digit_add_0_l in H.
rename H into Hcc.
remember Hbd as H; clear HeqH.
unfold I_add_i in H; simpl in H.
rewrite Hb5, Ht5, digit_add_1_r in H.
apply digit_move_l_r_1 in H.
rewrite digit_opp_add_diag_l in H.
rename H into Hyz.
remember (S i) as x.
rewrite <- Nat.add_1_r in Hcc.
unfold carry in Hyz.
remember (fst_same y z x) as s1 eqn:Hs1 .
destruct s1 as [di1| ].
 symmetry in Hs1.
 destruct di1.
  rewrite Nat.add_0_r, Ht6 in Hyz.
  revert Hyz; apply digit_neq_0_1.

  assert (0 < S di1) as H by apply Nat.lt_0_succ.
  erewrite carry_before_relay in Hcc; try eassumption.
  rewrite Hyz, digit_add_1_r in Hcc.
  apply oppd_1_iff in Hcc.
  apply fst_same_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, _).
  apply Hn1 in H; rewrite Nat.add_0_r in H.
  rewrite Ht6, Hcc in H.
  exfalso; revert H; apply digit_neq_0_1.

 symmetry in Hs1.
 rewrite carry_before_inf_relay in Hcc; [ idtac | assumption ].
 remember Hs1 as H; clear HeqH.
 apply fst_same_inf_after with (di := 1) in H.
 rewrite Nat.add_1_r in H.
 rename H into Hs2.
 apply fst_same_iff in Hs1.
 pose proof (Hs1 0) as H; apply oppd_sym in H.
 rewrite Nat.add_0_r in H.
 rewrite H, Ht6, digit_add_1_l in Hcc.
 revert Hcc; apply digit_neq_0_1.
Qed.

Theorem carry_succ_negb : ∀ x y i a,
  (carry x y i = a)%D
  → (carry x y (S i) = oppd a)%D
  → (x.[i] = a)%D ∧ (y.[i] = a)%D.
Proof.
intros x y i a Hc1 Hc2.
unfold carry in Hc1; simpl in Hc1.
remember (fst_same x y i) as s1 eqn:Hs1 .
symmetry in Hs1.
replace (S i) with (S i + 0) in Hc2 by apply Nat.add_0_r.
destruct s1 as [di1| ].
 destruct di1.
  apply fst_same_iff in Hs1.
  destruct Hs1 as (_, Hs1).
  rewrite Nat.add_0_r in Hc1, Hs1.
  rewrite Hc1 in Hs1; symmetry in Hs1.
  split; assumption.

  assert (0 < S di1) as H by apply Nat.lt_0_succ.
  eapply carry_before_relay9 in H; try eassumption.
  rewrite <- Nat.add_succ_l in H.
  rewrite Hc2 in H; simpl in H.
  rewrite Hc1 in H.
  exfalso; revert H; apply no_fixpoint_oppd.

 rewrite <- Hc1 in Hc2 |-*; simpl in Hc2.
 rewrite Nat.add_0_r in Hc2.
 unfold carry in Hc2.
 apply fst_same_inf_after with (di := 1) in Hs1.
 rewrite <- Nat.add_1_r, Hs1 in Hc2.
 exfalso; revert Hc2; apply digit_neq_1_0.
Qed.

Theorem sum_11_1_sum_x1 : ∀ x y i di,
  (x .[ i] = 1)%D
  → (y .[ i] = 1)%D
  → (∀ dj, dj ≤ di → (I_add_i x y (i + dj) = x.[i + dj])%D)
  → (y.[i + di] = 1)%D.
Proof.
intros x y i di Ha Hy Hxy.
revert i Ha Hy Hxy.
induction di; intros; [ rewrite Nat.add_0_r; assumption | idtac ].
pose proof (Hxy (S di) (Nat.le_refl (S di))) as H.
unfold I_add_i in H; simpl in H.
rewrite <- digit_add_assoc in H.
apply digit_move_l_r_1 in H.
rewrite digit_add_nilpotent in H.
destruct (digit_eq_dec (y.[i+S di]) 1) as [Hb | Hb]; [ assumption | idtac ].
apply digit_not_1_iff_0 in Hb.
rewrite Hb, digit_add_0_l in H.
rename H into Hd.
pose proof (Hxy di (Nat.le_succ_diag_r di)) as H.
unfold I_add_i in H; simpl in H.
rewrite <- digit_add_assoc in H.
apply digit_move_l_r_1 in H.
rewrite digit_add_nilpotent in H.
rewrite IHdi in H; try assumption.
 rewrite digit_add_1_l in H.
 apply oppd_0_iff in H.
 rewrite Nat.add_succ_r in Hd.
 apply carry_succ_negb in H; [ idtac | assumption ].
 rewrite <- Nat.add_succ_r, Hb in H.
 destruct H as (_, H); exfalso; revert H; apply digit_neq_0_1.

 intros dj Hdj.
 apply Hxy, Nat.le_le_succ_r; assumption.
Qed.

Theorem case_1 : ∀ x y z i,
  (carry x (y + z) i = 1)%D
  → (carry y z i = 1)%D
  → (carry x y i = 0)%D
  → False.
Proof.
intros x y z i Hc3 Hc5 Hc6.
remember Hc6 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x y i) as s6 eqn:Hs6 .
destruct s6 as [di6| ]; [ idtac | exfalso; revert H; apply digit_neq_1_0 ].
remember Hs6 as HH; clear HeqHH.
apply fst_same_sym_iff in HH; simpl in HH.
destruct HH as (Hn6, Ht6).
rewrite H in Ht6; symmetry in Ht6.
rename H into Ha6.
remember Hc5 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same y z i) as s5 eqn:Hs5 .
remember Hs5 as HH; clear HeqHH.
apply fst_same_sym_iff in HH; simpl in HH.
destruct s5 as [di5| ]; [ idtac | clear H ].
 destruct HH as (Hn5, Ht5); rewrite H in Ht5.
 symmetry in Ht5; rename H into Hb5.
 destruct (lt_eq_lt_dec di5 di6) as [[H1| H1]| H1].
  remember Hc3 as H; clear HeqH.
  unfold carry in H; simpl in H.
  remember (fst_same x (y + z) i) as s3 eqn:Hs3 .
  apply fst_same_sym_iff in Hs3; simpl in Hs3.
  destruct s3 as [di3| ]; [ idtac | clear H ].
   destruct Hs3 as (Hn3, Ht3).
   rewrite H in Ht3; symmetry in Ht3.
   rename H into Ha3.
   destruct (lt_eq_lt_dec di3 di5) as [[H2| H2]| H2].
    remember Ht3 as H; clear HeqH.
    unfold I_add_i in H; simpl in H.
    symmetry in Hs5.
    erewrite carry_before_relay9 in H; try eassumption; simpl in H.
    apply Hn5 in H2.
    rewrite H2, digit_opp_add_diag_l, Hb5 in H.
    exfalso; revert H; apply digit_neq_0_1.

    subst di3.
    remember H1 as H; clear HeqH.
    apply Hn6 in H.
    rewrite Ha3, Hb5 in H.
    exfalso; revert H; apply digit_neq_1_0.

    remember H2 as H; clear HeqH.
    apply Hn3 in H.
    rewrite Hn6 in H; [ idtac | assumption ].
    rewrite Hb5 in H.
    apply oppd_sym in H; simpl in H.
    rename H into Hbd.
    destruct (lt_eq_lt_dec di3 di6) as [[H4| H4]| H4].
     remember Ha3 as Hb3; clear HeqHb3.
     rewrite Hn6 in Hb3; [ idtac | assumption ].
     apply oppd_1_iff in Hb3.
     remember (di3 - S di5) as n eqn:Hn .
     apply Nat_sub_add_r in Hn; [ idtac | assumption ].
     rewrite Nat.add_comm in Hn; simpl in Hn.
     subst di3.
     rewrite Nat.add_succ_r in Hb3, Ht3.
     remember H4 as H; clear HeqH; simpl in H.
     apply Nat.lt_succ_l in H; apply Hn6 in H.
     assert (n + di5 < S n + di5) as HH by apply Nat.lt_succ_diag_r.
     rewrite Hn3 in H; [ idtac | assumption ].
     apply oppd_sym in H.
     rewrite digit_opp_involutive in H; symmetry in H; simpl in H.
     rename H into Hyz1.
     erewrite sum_x1_x_sum_0_0 in Ht3; try eassumption.
      exfalso; revert Ht3; apply digit_neq_0_1.

      rewrite Nat.add_assoc, Nat.add_shuffle0.
      apply sum_11_1_sum_x1 with (x := y); try assumption.
      intros dj Hdj.
      simpl; symmetry; rewrite <- Nat.add_assoc, <- digit_opp_involutive.
      rewrite <- Hn6.
       rewrite Hn3; [ rewrite digit_opp_involutive; reflexivity | idtac ].
       rewrite Nat.add_comm; simpl.
       apply le_n_S, Nat.add_le_mono_r; assumption.

       eapply lt_trans; [ idtac | eassumption ].
       rewrite Nat.add_comm.
       apply le_n_S, Nat.add_le_mono_r; assumption.

     subst di3.
     rewrite Ha6 in Ha3; exfalso; revert Ha3; apply digit_neq_0_1.

     remember Ha6 as Hbe; clear HeqHbe.
     rewrite Hn3 in Hbe; [ idtac | assumption ].
     apply oppd_0_iff in Hbe.
     remember (di6 - S di5) as n eqn:Hn .
     apply Nat_sub_add_r in Hn; [ idtac | assumption ].
     rewrite Nat.add_comm in Hn; simpl in Hn; subst di6.
     rewrite Nat.add_succ_r in Hbe, Ht6.
     remember H1 as H; clear HeqH.
     apply Hn6 in H.
     rewrite Hb5 in H; simpl in H.
     rename H into Ha5.
     erewrite sum_x1_x_sum_0_0 in Hbe; try eassumption.
      exfalso; revert Hbe; apply digit_neq_0_1.

      rewrite Nat.add_assoc, Nat.add_shuffle0.
      apply sum_11_1_sum_x1 with (x := y); try assumption.
      intros dj Hdj.
      simpl; symmetry; rewrite <- Nat.add_assoc, <- digit_opp_involutive.
      rewrite <- Hn6.
       rewrite Hn3; [ rewrite digit_opp_involutive; reflexivity | idtac ].
       eapply lt_trans; [ idtac | eassumption ].
       rewrite Nat.add_comm.
       apply le_n_S, Nat.add_le_mono_r; assumption.

       rewrite Nat.add_comm.
       apply le_n_S, Nat.add_le_mono_r; assumption.

      remember H4 as H; clear HeqH.
      eapply lt_trans in H; [ idtac | apply Nat.lt_succ_diag_r ].
      apply Hn3 in H.
      rewrite Hn6 in H; [ idtac | apply Nat.lt_succ_diag_r ].
      apply oppd_sym in H.
      rewrite digit_opp_involutive in H.
      assumption.

   remember Ha6 as Hbe; clear HeqHbe.
   rewrite Hs3 in Hbe.
   apply oppd_0_iff in Hbe.
   remember (di6 - S di5) as n eqn:Hn .
   apply Nat_sub_add_r in Hn; [ idtac | assumption ].
   rewrite Nat.add_comm in Hn; simpl in Hn; subst di6.
   rewrite Nat.add_succ_r in Hbe, Ht6.
   remember H1 as H; clear HeqH.
   apply Hn6 in H.
   rewrite Hb5 in H; simpl in H.
   rename H into Ha5.
   rewrite sum_x1_x_sum_0_0 in Hbe; try assumption.
    exfalso; revert Hbe; apply digit_neq_0_1.

    rewrite Nat.add_assoc, Nat.add_shuffle0.
    apply sum_11_1_sum_x1 with (x := y); try assumption.
    intros dj Hdj.
    simpl; symmetry; rewrite <- Nat.add_assoc, <- digit_opp_involutive.
    rewrite <- Hn6.
     rewrite Hs3; rewrite digit_opp_involutive; reflexivity.

     rewrite Nat.add_comm.
     apply le_n_S, Nat.add_le_mono_r; assumption.

    symmetry; rewrite <- digit_opp_involutive.
    rewrite <- Hn6; [ idtac | apply Nat.lt_succ_diag_r ].
    symmetry; apply oppd_sym, Hs3.

  subst di5; rewrite Ht6 in Hb5; exfalso; revert Hb5; apply digit_neq_0_1.

  remember Hc3 as H; clear HeqH.
  unfold carry in H; simpl in H.
  remember (fst_same x (y + z) i) as s3 eqn:Hs3 .
  destruct s3 as [di3| ]; [ idtac | clear H ].
   rename H into Ha3.
   remember Hs3 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn3, Ht3).
   destruct (lt_eq_lt_dec di3 di6) as [[H2| H2]| H2].
    remember H2 as H; clear HeqH.
    apply Hn6 in H.
    rewrite Ha3 in H; apply oppd_sym in H.
    rename H into Hb3; simpl in Hb3.
    remember H1 as H; clear HeqH.
    eapply lt_trans in H; [ idtac | eassumption ].
    apply Hn5 in H.
    rewrite Hb3 in H; apply oppd_sym in H.
    rename H into Hd3; simpl in Hd3.
    remember Ht3 as H; clear HeqH.
    unfold I_add_i in H; simpl in H.
    rewrite Ha3, Hb3, Hd3, digit_add_1_r, digit_add_1_l in H.
    apply oppd_sym in H; simpl in H.
    symmetry in Hs5.
    remember H1 as HH; clear HeqHH.
    eapply lt_trans in HH; [ idtac | eassumption ].
    erewrite carry_before_relay9 in H; try eassumption.
    simpl in H; rewrite Hb5 in H; exfalso; revert H; apply digit_neq_1_0.

    subst di3; rewrite Ha6 in Ha3; exfalso; revert Ha3; apply digit_neq_0_1.

    remember H2 as H; clear HeqH.
    apply Hn3 in H.
    rewrite Ha6 in H; apply oppd_sym in H; simpl in H.
    unfold I_add_i in H; simpl in H.
    rewrite Ht6, digit_add_0_l in H.
    symmetry in Hs5.
    erewrite carry_before_relay9 in H; try eassumption; simpl in H.
    rewrite Hb5, digit_add_1_r in H.
    rewrite <- Hn5 in H; [ idtac | assumption ].
    rewrite Ht6 in H; exfalso; revert H; apply digit_neq_0_1.

   remember Hs3 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rename H into Ht3.
   pose proof (Ht3 di6) as H.
   rewrite Ha6 in H; apply oppd_sym in H; simpl in H.
   unfold I_add_i in H; simpl in H.
   rewrite Ht6, digit_add_0_l in H.
   symmetry in Hs5.
   erewrite carry_before_relay9 in H; try eassumption; simpl in H.
   rewrite Hb5, digit_add_1_r in H.
   rewrite <- Hn5 in H; [ idtac | assumption ].
   rewrite Ht6 in H; exfalso; revert H; apply digit_neq_0_1.

 rename HH into Ht5.
 remember Hc3 as H; clear HeqH.
 unfold carry in H; simpl in H.
 remember (fst_same x (y + z) i) as s3 eqn:Hs3 .
 destruct s3 as [di3| ]; [ idtac | clear H ].
  rename H into Ha3.
  remember Hs3 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn3, Ht3).
  rewrite Ha3 in Ht3; symmetry in Ht3.
  unfold I_add_i in Ht3; simpl in Ht3.
  rewrite Ht5, digit_opp_add_diag_l, digit_add_1_l in Ht3.
  apply oppd_1_iff in Ht3.
  rewrite <- Nat.add_succ_l in Ht3.
  symmetry in Ht5.
  unfold carry in Ht3; simpl in Ht3.
  remember Hs5 as H; clear HeqH; symmetry in H.
  apply fst_same_inf_after with (di := S di3) in H.
  rewrite Nat.add_succ_r in H; simpl in H.
  rewrite H in Ht3; exfalso; revert Ht3; apply digit_neq_1_0.

  remember Hs3 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  rename H into Ht3.
  rewrite Ht3 in Ha6.
  apply oppd_0_iff in Ha6.
  unfold I_add_i in Ha6.
  rewrite Ht6, digit_add_0_l in Ha6.
  unfold carry in Ha6.
  remember Hs5 as H; clear HeqH; symmetry in H.
  apply fst_same_inf_after with (di := S di6) in H.
  rewrite Nat.add_succ_r in H; simpl in H.
  rewrite H, digit_add_1_r in Ha6.
  rewrite <- Ht5, Ht6 in Ha6; exfalso; revert Ha6; apply digit_neq_0_1.
Qed.

Theorem min_neq_lt : ∀ x xl y m,
  m = List.fold_right min x xl
  → y ∈ [x … xl]
  → y ≠ m
  → m < y.
Proof.
intros x xl y m Hm Hy Hym.
subst m.
apply Nat.nle_gt; intros Hm; apply Hym; clear Hym.
revert x y Hy Hm.
induction xl as [| z]; intros.
 simpl in Hy, Hm; simpl.
 destruct Hy; auto; contradiction.

 simpl in Hy, Hm; simpl.
 destruct Hy as [Hy| [Hy| Hy]].
  subst y.
  apply Nat.min_glb_iff in Hm.
  clear IHxl.
  revert z x Hm.
  induction xl as [| y]; intros.
   simpl in Hm; simpl.
   apply Nat.min_unicity.
   right; split; [ idtac | reflexivity ].
   destruct Hm; assumption.

   simpl in Hm; simpl.
   rewrite <- IHxl.
    apply Nat.min_unicity.
    right; split; [ idtac | reflexivity ].
    destruct Hm; assumption.

    destruct Hm as (Hxz, Hm).
    apply Nat.min_glb_iff; assumption.

  subst z.
  symmetry; apply min_l.
  eapply Nat.min_glb_r; eassumption.

  erewrite <- IHxl; [ idtac | right; eassumption | idtac ].
   apply Nat.min_unicity.
   right; split; [ idtac | reflexivity ].
   eapply Nat.min_glb_l; eassumption.

   erewrite <- IHxl; [ reflexivity | right; eassumption | idtac ].
   eapply Nat.min_glb_r; eassumption.
Qed.

Theorem carry_repeat : ∀ x y z i,
  (carry x y i = 0)%D
  → (carry (x + y) z i = 0)%D
  → (carry y z i = 1)%D
  → ∃ m,
    (carry x y (S (i + m)) = 0)%D ∧
    (carry (x + y) z (S (i + m)) = 0)%D ∧
    (carry y z (S (i + m)) = 1)%D ∧
    (∀ dj, dj ≤ m → (I_add_i x y (i + dj) = oppd (z.[i + dj]))%D).
Proof.
intros x y z i Rxy Rayz Ryz.
rename Rxy into Rxyn.
rename Rayz into Rxy_zn.
rename Ryz into Ryzn.
remember Rxyn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x y i) as sxyn eqn:Hsxyn .
destruct sxyn as [dxyn| ]; [ idtac | exfalso; revert H; apply digit_neq_1_0 ].
rename H into A_p.
symmetry in Hsxyn.
remember Rxy_zn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (x + y) z i) as sxy_zn.
rename Heqsxy_zn into Hsxy_zn.
destruct sxy_zn as [dxy_zn| ]; [ | exfalso; revert H; apply digit_neq_1_0 ].
rename H into AB_p; symmetry in Hsxy_zn.
remember Ryzn as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same y z i) as syzn eqn:Hsyzn .
symmetry in Hsyzn.
destruct syzn as [dyzn| ]; [ idtac | clear H ].
 rename H into B_p.
 remember (List.fold_right min dyzn [dxyn; dxy_zn … []]) as p.
 rename Heqp into Hp.
 destruct (eq_nat_dec dxyn p) as [H| H].
  move H at top; subst dxyn; rename A_p into Ap.
  remember Hsxyn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnxyn, Bp).
  rewrite Ap in Bp; symmetry in Bp.
  remember Hsyzn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnyzn, Htyzn).
  destruct (eq_nat_dec dyzn p) as [H| H].
   move H at top; subst dyzn.
   rewrite B_p in Bp; exfalso; revert Bp; apply digit_neq_1_0.

   eapply min_neq_lt in H; eauto ; try (left; auto).
   rename H into Hpdyzn.
   remember Bp as Cp; clear HeqCp.
   rewrite Hnyzn in Cp; [ idtac | assumption ].
   apply oppd_0_iff in Cp.
   remember Hsxy_zn as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hnxy_zn, Htxy_zn).
   destruct (eq_nat_dec dxy_zn p) as [H| H].
    move H at top; subst dxy_zn.
    rewrite Cp in Htxy_zn.
    rewrite AB_p in Htxy_zn; exfalso; revert Htxy_zn; apply digit_neq_0_1.

    eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
    rename H into Hpdxy_zn.
    pose proof (Hnxy_zn p Hpdxy_zn) as H.
    rewrite Cp in H; simpl in H; rename H into ABp.
    remember ABp as H; clear HeqH.
    unfold I_add_i in H.
    rewrite Ap, Bp, digit_add_0_l in H.
    rename H into Rxyp.
    remember Hsxy_zn as H; clear HeqH.
    eapply carry_before_relay9 in H; [ idtac | eassumption ].
    simpl in H.
    rewrite AB_p in H.
    rename H into Rxy_zp.
    remember Hsyzn as H; clear HeqH.
    eapply carry_before_relay9 in H; [ idtac | eassumption ].
    simpl in H.
    rewrite B_p in H.
    rename H into Ryzp.
    exists p.
    split; [ assumption | idtac ].
    split; [ assumption | idtac ].
    split; [ assumption | idtac ].
    intros dj Hdj.
    eapply Hnxy_zn, le_lt_trans; eassumption.

  exfalso.
  eapply min_neq_lt in H; eauto ; try (right; left; auto).
  rename H into Hpdan.
  remember Hsxyn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnxyn, Htxyn).
  remember Hsxy_zn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnxy_zn, Htxy_zn).
  remember Hsyzn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnyzn, Htyzn).
  rename Htyzn into C_p; rewrite B_p in C_p; symmetry in C_p.
  rename Htxy_zn into C_q; rewrite AB_p in C_q; symmetry in C_q.
  destruct (eq_nat_dec dyzn p) as [H| H].
   move H at top; subst dyzn.
   rename B_p into Bp; rename C_p into Cp.
   destruct (eq_nat_dec dxy_zn p) as [H| H].
    move H at top; subst dxy_zn.
    rewrite Cp in C_q; exfalso; revert C_q; apply digit_neq_1_0.

    eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
    rename H into Hpdxy_zn.
    pose proof (Hnxy_zn p Hpdxy_zn) as H.
    rewrite Cp in H; rename H into ABp; simpl in ABp.
    remember ABp as H; clear HeqH.
    unfold I_add_i in H.
    rewrite Hnxyn in H; [ idtac | assumption ].
    rewrite digit_opp_add_diag_l, digit_add_1_l in H.
    erewrite carry_before_relay9 in H; try eassumption.
    simpl in H; rewrite A_p in H; exfalso; revert H; apply digit_neq_1_0.

   eapply min_neq_lt in H; eauto ; try (left; auto).
   rename H into Hpdyzn.
   destruct (eq_nat_dec dxy_zn p) as [H| H].
    move H at top; subst dxy_zn.
    remember AB_p as H; clear HeqH.
    unfold I_add_i in H; simpl in H.
    rewrite Hnxyn in H; [ idtac | assumption ].
    rewrite digit_opp_add_diag_l, digit_add_1_l in H.
    apply oppd_0_iff in H.
    erewrite carry_before_relay9 in H; try eassumption.
    simpl in H; rewrite A_p in H; exfalso; revert H; apply digit_neq_0_1.

    eapply min_neq_lt in H; eauto ; try (do 2 right; left; auto).
    rename H into Hpdxy_zn; simpl in Hp.
    revert Hp Hpdan Hpdyzn Hpdxy_zn; clear; intros Hp H1 H2 H3.
    destruct (Nat.min_dec dxy_zn dyzn) as [L1| L1].
     rewrite L1 in Hp.
     destruct (Nat.min_dec dxyn dxy_zn) as [L2| L2].
      rewrite L2 in Hp; subst p.
      revert H1; apply Nat.lt_irrefl.

      rewrite L2 in Hp; subst p.
      revert H3; apply Nat.lt_irrefl.

     rewrite L1 in Hp.
     destruct (Nat.min_dec dxyn dyzn) as [L2| L2].
      rewrite L2 in Hp; subst p.
      revert H1; apply Nat.lt_irrefl.

      rewrite L2 in Hp; subst p.
      revert H2; apply Nat.lt_irrefl.

 remember (List.fold_right min dxyn [dxy_zn]) as p eqn:Hp .
 destruct (eq_nat_dec dxyn p) as [H| H].
  move H at top; subst dxyn; rename A_p into Ap.
  remember Hsxyn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnxyn, Bp).
  rewrite Ap in Bp; symmetry in Bp.
  remember Hsyzn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  rename H into Hnyzn.
  remember Bp as Cp; clear HeqCp.
  rewrite Hnyzn in Cp.
  apply oppd_0_iff in Cp.
  remember Hsxy_zn as H; clear HeqH.
  apply fst_same_iff in H; simpl in H.
  destruct H as (Hnxy_zn, Htxy_zn).
  destruct (eq_nat_dec dxy_zn p) as [H| H].
   move H at top; subst dxy_zn.
   rewrite Cp in Htxy_zn.
   rewrite AB_p in Htxy_zn; exfalso; revert Htxy_zn; apply digit_neq_0_1.

   eapply min_neq_lt in H; eauto ; try (right; left; auto).
   rename H into Hpdxy_zn.
   pose proof (Hnxy_zn p Hpdxy_zn) as H.
   rewrite Cp in H; simpl in H.
   unfold I_add_i in H.
   rewrite Ap, Bp, digit_add_0_l in H.
   exists p.
   split; [ assumption | idtac ].
   erewrite carry_before_relay9; try eassumption; simpl.
   split; [ assumption | idtac ].
   erewrite carry_before_inf_relay9; [ idtac | assumption ].
   split; [ reflexivity | idtac ].
   intros dj Hdj; eapply Hnxy_zn, le_lt_trans; eassumption.

  eapply min_neq_lt in H; eauto ; try (left; auto).
  rename H into Hpdxyn.
  destruct (eq_nat_dec dxy_zn p) as [H| H].
   move H at top; subst dxy_zn.
   remember Hsxyn as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hnxyn, B_p).
   rewrite A_p in B_p; symmetry in B_p.
   remember AB_p as H; clear HeqH.
   unfold I_add_i in H.
   rewrite Hnxyn in H; [ idtac | assumption ].
   rewrite digit_opp_add_diag_l, digit_add_1_l in H.
   erewrite carry_before_relay9 in H; try eassumption.
   simpl in H; rewrite A_p in H; exfalso; revert H; apply digit_neq_1_0.

   eapply min_neq_lt in H; eauto ; try (right; left; auto).
   simpl in Hp.
   destruct (Nat.min_dec dxy_zn dxyn) as [L1| L1].
    rewrite L1 in Hp; subst p.
    exfalso; revert H; apply Nat.lt_irrefl.

    rewrite L1 in Hp; subst p.
    exfalso; revert Hpdxyn; apply Nat.lt_irrefl.
Qed.

Definition I_shift_l n x := {| rm i := x.[i+n] |}.
Arguments I_shift_l n%nat x%I.

Theorem fst_same_shift : ∀ x y x' y' i di d,
  fst_same x y i = Some di
  → d ≤ di
  → x' = I_shift_l d x
  → y' = I_shift_l d y
  → fst_same x' y' i = Some (di - d).
Proof.
intros x y x' y' i di d Hs Hd Ha' Hb'.
subst x' y'; simpl.
apply fst_same_iff in Hs; simpl in Hs.
destruct Hs as (Hn, Hs).
apply fst_same_iff; simpl.
split.
 intros dj Hdj.
 rewrite <- Nat.add_assoc; apply Hn.
 eapply Nat.add_lt_le_mono with (p := d) in Hdj; [ idtac | reflexivity ].
 rewrite Nat.sub_add in Hdj; assumption.

 rewrite Nat.add_sub_assoc; [ idtac | assumption ].
 rewrite Nat.sub_add; [ assumption | idtac ].
 eapply le_trans; [ eassumption | idtac ].
 apply Nat.le_sub_le_add_r.
 rewrite Nat.sub_diag.
 apply Nat.le_0_l.
Qed.

Theorem carry_shift : ∀ x y n i,
  carry (I_shift_l n x) (I_shift_l n y) i = carry x y (i + n).
Proof.
intros x y n i.
unfold carry; simpl.
remember (fst_same x y (i + n)) as s1 eqn:Hs1 .
remember (fst_same (I_shift_l n x) (I_shift_l n y) i) as s2 eqn:Hs2 .
apply fst_same_sym_iff in Hs1; simpl in Hs1.
apply fst_same_sym_iff in Hs2; simpl in Hs2.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Hs1).
 destruct s2 as [di2| ].
  destruct Hs2 as (Hn2, Hs2).
  destruct (lt_eq_lt_dec di1 di2) as [[H1| H1]| H1].
   apply Hn2 in H1.
   rewrite Nat.add_shuffle0, Hs1 in H1.
   exfalso; symmetry in H1; revert H1; apply no_fixpoint_oppd.

   subst di2; rewrite Nat.add_shuffle0; reflexivity.

   apply Hn1 in H1.
   rewrite Nat.add_shuffle0, Hs2 in H1.
   exfalso; symmetry in H1; revert H1; apply no_fixpoint_oppd.

  rewrite Nat.add_shuffle0, Hs2 in Hs1.
  exfalso; revert Hs1; apply no_fixpoint_oppd.

 destruct s2 as [di2| ]; [ idtac | reflexivity ].
 destruct Hs2 as (Hn2, Hs2).
 rewrite Nat.add_shuffle0, Hs1 in Hs2.
 exfalso; revert Hs2; apply no_fixpoint_oppd.
Qed.

Theorem I_add_i_shift : ∀ x y i n,
  I_add_i (I_shift_l n x) (I_shift_l n y) i = I_add_i x y (i + n).
Proof.
intros x y i n.
unfold I_add_i; simpl.
rewrite carry_shift; reflexivity.
Qed.

Theorem fst_same_shift_add_l : ∀ x y z n i,
  fst_same (I_shift_l n (x + y)) z i =
  fst_same (I_shift_l n x + I_shift_l n y) z i.
Proof.
intros x y z n i.
apply fst_same_iff; simpl.
remember (fst_same (I_shift_l n x + I_shift_l n y) z i) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Hs).
 split.
  intros dj Hdj.
  apply Hn in Hdj.
  rewrite I_add_i_shift in Hdj; assumption.

  rewrite I_add_i_shift in Hs; assumption.

 intros dj; rewrite <- I_add_i_shift; apply Hs.
Qed.

Theorem carry_shift_add_l : ∀ x y z n i,
  carry (I_shift_l n x + I_shift_l n y) (I_shift_l n z) i =
  carry (x + y) z (i + n).
Proof.
intros x y z n i.
rewrite <- carry_shift.
unfold carry; simpl.
rewrite <- fst_same_shift_add_l.
remember (I_shift_l n (x + y)) as xy'.
remember (I_shift_l n z) as z'.
remember (fst_same xy' z' i) as s eqn:Hs .
subst xy' z'.
destruct s as [di| ]; [ idtac | reflexivity ].
apply I_add_i_shift.
Qed.

Theorem case_2 : ∀ x y z i,
  (carry (x + y) z i = 0)%D
  → (carry y z i = 1)%D
  → (carry x y i = 0)%D
  → False.
Proof.
intros x y z i Hc4 Hc5 Hc6.
remember Hc4 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (x + y) z i) as s eqn:Hs .
destruct s as [di| ]; [ idtac | exfalso; revert H; apply digit_neq_1_0 ].
symmetry in Hs; clear H.
revert x y z i Hc4 Hc5 Hc6 Hs.
induction di as (di, IHdi) using all_lt_all; intros.
remember Hc4 as H; clear HeqH.
apply carry_repeat in H; try assumption.
destruct H as (n, (Rxyn, (Rxy_zn, (Ryzn, Hnxy_z)))).
move Rxyn after Ryzn.
destruct (le_dec di n) as [H1| H1].
 remember Hs as H; clear HeqH.
 apply fst_same_iff in H; simpl in H.
 destruct H as (Hnxy_z2, Hxy_z).
 rewrite Hnxy_z in Hxy_z; [ idtac | assumption ].
 revert Hxy_z; apply no_fixpoint_oppd.

 apply Nat.nle_gt in H1.
 remember (di - S n) as dj.
 apply Nat_sub_add_r in Heqdj; [ idtac | assumption ].
 clear Hc4 Hc5 Hc6.
 rename Rxy_zn into Hc4; rename Ryzn into Hc5; rename Rxyn into Hc6.
 remember (I_shift_l (S n) (x + y)%I) as x'y' eqn:Hxy .
 remember (I_shift_l (S n) z) as z' eqn:Hc .
 eapply fst_same_shift in Hs; try eassumption.
 assert (0 < S n) as Hn by apply Nat.lt_0_succ.
 assert (di - S n < di) as H by (apply Nat.sub_lt; assumption).
 subst x'y'.
 rewrite fst_same_shift_add_l in Hs.
 remember (I_shift_l (S n) x) as x' eqn:Ha .
 remember (I_shift_l (S n) y) as y' eqn:Hb .
 eapply IHdi with (x := x') (y := y') (z := z'); try eassumption.
  subst x' y' z'.
  rewrite carry_shift_add_l, Nat.add_succ_r; assumption.

  subst y' z'.
  rewrite carry_shift.
  rewrite Nat.add_succ_r; assumption.

  subst x' y'.
  rewrite carry_shift.
  rewrite Nat.add_succ_r; assumption.
Qed.

Theorem carry_repeat2 : ∀ x y z i u,
  (carry x (y + z) i = 1)%D
  → (carry (x + y) z i = 0)%D
  → (carry y z i = u)%D
  → (carry x y i = u)%D
  → ∃ m t,
    (carry x (y + z) (S (i + m)) = 1)%D ∧
    (carry (x + y) z (S (i + m)) = 0)%D ∧
    (carry y z (S (i + m)) = t)%D ∧
    (carry x y (S (i + m)) = t)%D ∧
    (∀ dj, dj ≤ m → (I_add_i x y (i + dj) = oppd (z.[ i + dj]))%D).
Proof.
intros x y z i u Hc3 Hc4 Hc5 Hc6.
remember Hc4 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (x + y) z i) as s4 eqn:Hs4 .
symmetry in Hs4; rename H into H4.
destruct s4 as [di4| ]; [ idtac | exfalso; revert H4; apply digit_neq_1_0 ].
remember Hc3 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x (y + z) i) as s3 eqn:Hs3 .
symmetry in Hs3; rename H into H3.
remember Hc5 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same y z i) as s5 eqn:Hs5 .
symmetry in Hs5; rename H into H5.
remember Hc6 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same x y i) as s6 eqn:Hs6 .
symmetry in Hs6; rename H into H6.
destruct s3 as [di3| ]; [ idtac | clear H3 ].
 destruct s5 as [di5| ].
  destruct s6 as [di6| ].
   remember (List.fold_right min di6 [di3; di4; di5 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn3, Ht3).
   rewrite H3 in Ht3; symmetry in Ht3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn5, Ht5).
   rewrite H5 in Ht5; symmetry in Ht5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn6, Ht6).
   rewrite H6 in Ht6; symmetry in Ht6.
   destruct (eq_nat_dec di3 m) as [M3| M3].
    move M3 at top; subst di3.
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     rewrite H3 in H6; move H6 at top; rewrite <- H6 in *; clear H6.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       rewrite Ht4 in Ht5; exfalso; revert Ht5; apply digit_neq_0_1.

       eapply min_neq_lt in M5; [ idtac | eauto  | do 3 right; left; auto ].
       remember Ht3 as H; clear HeqH.
       unfold I_add_i in H.
       rewrite Ht6, Ht4, digit_add_1_l in H.
       apply oppd_1_iff in H.
       erewrite carry_before_relay9 in H; try eassumption.
       simpl in H; rewrite H5 in H; exfalso; revert H; apply digit_neq_1_0.

      eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       clear Hm Ht6.
       remember Ht5 as H; clear HeqH.
       symmetry in H.
       rewrite <- digit_opp_involutive in H; symmetry in H.
       apply oppd_sym in H; simpl in H; symmetry in H.
       rewrite <- Hn4 in H; [ idtac | assumption ].
       rename H into Hxym.
       remember Hxym as H; clear HeqH.
       unfold I_add_i in H; simpl in H.
       rewrite H3, H5, digit_add_nilpotent, digit_add_0_l in H.
       rename H into Hcxym.
       remember Ht3 as H; clear HeqH.
       unfold I_add_i in H.
       rewrite H5, Ht5, digit_add_nilpotent, digit_add_0_l in H.
       rename H into Hcyzm.
       remember Hcxym as H; clear HeqH.
       unfold carry in H; simpl in H.
       remember (fst_same x y (S (i + m))) as sxym eqn:Hsxym .
       destruct sxym as [djxym| ]; [ idtac | exfalso; revert H; apply digit_neq_1_0 ].
       symmetry in Hsxym.
       rename H into Haxym.
       remember Hs4 as H; clear HeqH.
       eapply carry_before_relay9 in H; [ idtac | eassumption ].
       simpl in H; rewrite H4 in H.
       rename H into Hxycm.
       exfalso; eapply case_2; eassumption.

       eapply min_neq_lt in M5; [ idtac | eauto  | do 3 right; left; auto ].
       remember Ht3 as H; clear HeqH.
       unfold I_add_i in H.
       rewrite Hn5 in H; [ idtac | assumption ].
       rewrite digit_opp_add_diag_l, digit_add_1_l in H.
       apply oppd_1_iff in H.
       eapply carry_before_relay9 in Hs5; [ idtac | eassumption ].
       simpl in Hs5; rewrite Hs5, H5 in H.
       exfalso; revert H; apply digit_neq_1_0.

     eapply min_neq_lt in M6; [ idtac | eauto | left; auto ].
     destruct (eq_nat_dec di5 m) as [M5| M5].
      move M5 at top; subst di5.
      remember H3 as H; clear HeqH.
      rewrite Hn6 in H; [ idtac | assumption ].
      apply oppd_1_iff in H.
      rewrite H5 in H; move H at top; rewrite H in *; clear H.
      remember Ht3 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite H5, Ht5, digit_add_0_l in H.
      rename H into Ryzm.
      destruct (eq_nat_dec di4 m) as [M4| M4].
       move M4 at top; subst di4.
       remember H4 as H; clear HeqH.
       unfold I_add_i in H.
       rewrite H3, H5, digit_add_1_l in H.
       apply oppd_0_iff in H.
       erewrite carry_before_relay9 in H; try eassumption.
       simpl in H; rewrite H6 in H; exfalso; revert H; apply digit_neq_0_1.

       eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
       pose proof (Hn4 m M4) as H.
       rewrite Ht5 in H; simpl in H.
       rename H into ABm.
       remember ABm as H; clear HeqH.
       unfold I_add_i in H.
       rewrite H3, H5, digit_add_1_l in H.
       apply oppd_1_iff in H.
       rename H into Rxym.
       remember Hs4 as H; clear HeqH.
       eapply carry_before_relay9 in H; [ idtac | eassumption ].
       simpl in H; rewrite H4 in H.
       rename H into Rxy_zm.
       exfalso; eapply case_2; try eassumption.

      eapply min_neq_lt in M5; [ idtac | eauto  | do 3 right; left; auto ].
      remember H3 as H; clear HeqH.
      rewrite Hn6 in H; [ idtac | assumption ].
      apply oppd_1_iff in H.
      rename H into Bm.
      remember Bm as H; clear HeqH.
      rewrite Hn5 in H; [ idtac | assumption ].
      apply oppd_0_iff in H.
      rename H into Cm.
      remember Hs5 as H; clear HeqH.
      eapply carry_before_relay9 in H; [ idtac | eassumption ].
      simpl in H; rewrite H5 in H.
      rename H into Ryzm.
      remember Ht3 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Bm, Cm, Ryzm, digit_add_0_l, digit_add_1_l in H.
      apply oppd_1_iff in H; move H at top; rewrite H in *; clear H.
      destruct (eq_nat_dec di4 m) as [M4| M4].
       move M4 at top; subst di4.
       rewrite Ht4 in Cm; exfalso; revert Cm; apply digit_neq_0_1.

       eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
       pose proof (Hn4 m M4) as H.
       rewrite Cm in H; simpl in H.
       rename H into ABm.
       remember ABm as H; clear HeqH.
       unfold I_add_i in H.
       rewrite H3, Bm, digit_add_0_r, digit_add_1_l in H.
       apply oppd_0_iff in H.
       erewrite carry_before_relay9 in H; try eassumption.
       simpl in H; rewrite H6 in H; exfalso; revert H; apply digit_neq_0_1.

    eapply min_neq_lt in M3; [ idtac | eauto  | right; left; auto ].
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite H6, Ht6, digit_add_nilpotent, digit_add_0_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_relay9 in H; [ idtac | eassumption ].
      simpl in H; rewrite H3 in H.
      rename H into A_BCm.
      pose proof (Hn3 m M3) as H.
      rewrite H6 in H.
      apply oppd_sym in H.
      unfold I_add_i in H.
      rewrite Ht6, Ht4, digit_add_0_r in H.
      apply digit_move_l_r_1 in H.
      rewrite digit_opp_add_diag_r in H.
      rename H into BCm.
      exfalso; eapply case_1; eassumption.

      eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       exists m, (oppd u).
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split.
        pose proof (Hn3 m M3) as H.
        unfold I_add_i in H.
        rewrite H6, Ht6, Ht5, digit_add_nilpotent, digit_add_0_l in H.
        apply oppd_sym; assumption.

        split.
         pose proof (Hn4 m M4) as H.
         unfold I_add_i in H.
         rewrite H6, Ht6, Ht5, digit_add_nilpotent, digit_add_0_l in H.
         assumption.

         intros dj Hdj; apply Hn4.
         eapply le_lt_trans; eassumption.

       eapply min_neq_lt in M5; [ idtac | eauto  | do 3 right; left; auto ].
       exists m, u.
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split.
        pose proof (Hn3 m M3) as H.
        unfold I_add_i in H.
        rewrite Hn5 in H; [ idtac | assumption ].
        rewrite digit_opp_add_diag_l in H.
        rewrite H6, digit_opp_involutive in H.
        symmetry; assumption.

        split.
         pose proof (Hn4 m M4) as H.
         unfold I_add_i in H.
         rewrite H6, Ht6, digit_add_nilpotent, digit_add_0_l in H.
         rewrite <- Hn5 in H; [ idtac | assumption ].
         rewrite Ht6 in H; assumption.

         intros dj Hdj; apply Hn4.
         eapply le_lt_trans; eassumption.

     eapply min_neq_lt in M6; [ idtac | eauto  | left; auto ].
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Hn6 in H; [ idtac | assumption ].
      rewrite digit_opp_add_diag_l, digit_add_1_l in H.
      apply oppd_0_iff in H.
      rename H into Rxym.
      remember Hs6 as H; clear HeqH.
      eapply carry_before_relay9 in H; [ idtac | eassumption ].
      simpl in H; rewrite Rxym, H6 in H.
      move H at top; rewrite <- H in *; clear H.
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       rewrite Ht4 in Ht5; exfalso; revert Ht5; apply digit_neq_0_1.

       eapply min_neq_lt in M5; eauto ; try (do 3 right; left; auto).
       pose proof (Hn5 m M5) as H.
       rewrite Ht4 in H; simpl in H.
       rename H into Bm.
       pose proof (Hn6 m M6) as H.
       rewrite Bm in H; simpl in H.
       rename H into Am.
       pose proof (Hn3 m M3) as H.
       rewrite Am in H; apply oppd_sym in H; simpl in H.
       rename H into BCm.
       remember BCm as H; clear HeqH.
       unfold I_add_i in H.
       rewrite Bm, Ht4, digit_add_1_l in H.
       apply oppd_1_iff in H.
       erewrite carry_before_relay9 in H; try eassumption.
       simpl in H; rewrite H5 in H; exfalso; revert H; apply digit_neq_1_0.

      eapply min_neq_lt in M4; eauto ; try (do 2 right; left; auto).
      destruct (eq_nat_dec di5 m) as [M5| M5].
       move M5 at top; subst di5.
       exists m, u.
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split; [ erewrite carry_before_relay9; eassumption | idtac ].
       split.
        pose proof (Hn3 m M3) as H.
        unfold I_add_i in H.
        rewrite Hn6 in H; [ idtac | assumption ].
        rewrite H5, Ht5, digit_add_nilpotent, digit_add_0_l in H.
        apply oppd_sym in H.
        rewrite digit_opp_involutive in H; assumption.

        split.
         pose proof (Hn4 m M4) as H.
         unfold I_add_i in H.
         rewrite Hn6 in H; [ idtac | assumption ].
         rewrite digit_opp_add_diag_l, digit_add_1_l, Ht5 in H.
         apply oppd_sym in H; symmetry in H.
         rewrite digit_opp_involutive in H; assumption.

         intros dj Hdj; apply Hn4.
         eapply le_lt_trans; eassumption.

       eapply min_neq_lt in M5; eauto ; try (do 3 right; left; auto).
       simpl in Hm.
       destruct (Nat.min_dec di5 di6) as [L1| L1]; rewrite L1 in Hm.
        destruct (Nat.min_dec di4 di5) as [L2| L2]; rewrite L2 in Hm.
         destruct (Nat.min_dec di3 di4) as [L3| L3]; rewrite L3 in Hm.
          subst m; exfalso; revert M3; apply Nat.lt_irrefl.

          subst m; exfalso; revert M4; apply Nat.lt_irrefl.

         destruct (Nat.min_dec di3 di5) as [L3| L3]; rewrite L3 in Hm.
          subst m; exfalso; revert M3; apply Nat.lt_irrefl.

          subst m; exfalso; revert M5; apply Nat.lt_irrefl.

        destruct (Nat.min_dec di4 di6) as [L2| L2]; rewrite L2 in Hm.
         destruct (Nat.min_dec di3 di4) as [L3| L3]; rewrite L3 in Hm.
          subst m; exfalso; revert M3; apply Nat.lt_irrefl.

          subst m; exfalso; revert M4; apply Nat.lt_irrefl.

         destruct (Nat.min_dec di3 di6) as [L3| L3]; rewrite L3 in Hm.
          subst m; exfalso; revert M3; apply Nat.lt_irrefl.

          subst m; exfalso; revert M6; apply Nat.lt_irrefl.

   move H6 at top; rewrite <- H6 in *; clear H6.
   remember (List.fold_right min di5 [di3; di4 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn3, Ht3).
   rewrite H3 in Ht3; symmetry in Ht3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn5, Ht5).
   rewrite H5 in Ht5; symmetry in Ht5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn6.
   destruct (eq_nat_dec di3 m) as [M3| M3].
    move M3 at top; subst di3.
    destruct (eq_nat_dec di5 m) as [M5| M5].
     move M5 at top; subst di5.
     rewrite Hn6, H5 in H3.
     exfalso; revert H3; apply digit_neq_0_1.

     eapply min_neq_lt in M5; eauto ; try (left; auto).
     remember Ht3 as H; clear HeqH.
     unfold I_add_i in H.
     rewrite Hn5 in H; [ idtac | assumption ].
     rewrite digit_opp_add_diag_l, digit_add_1_l in H.
     apply oppd_1_iff in H.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H; rewrite H5 in H; exfalso; revert H; apply digit_neq_1_0.

    eapply min_neq_lt in M3; eauto ; try (right; left; auto).
    destruct (eq_nat_dec di5 m) as [M5| M5].
     move M5 at top; subst di5.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      rewrite Ht5 in Ht4; exfalso; revert Ht4; apply digit_neq_1_0.

      eapply min_neq_lt in M4; eauto ; try (do 2 right; left; auto).
      exists m, 1%D.
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split.
       pose proof (Hn3 m M3) as H.
       unfold I_add_i in H.
       rewrite Hn6, H5, Ht5, digit_add_0_l in H.
       apply oppd_sym in H; rewrite digit_opp_involutive in H.
       assumption.

       split.
        pose proof (Hn4 m M4) as H.
        unfold I_add_i in H.
        rewrite Hn6, digit_opp_add_diag_l, digit_add_1_l, Ht5 in H.
        apply oppd_sym in H; symmetry in H.
        rewrite digit_opp_involutive in H; assumption.

        intros dj Hdj; apply Hn4.
        eapply le_lt_trans; eassumption.

     eapply min_neq_lt in M5; eauto ; try (left; auto).
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      pose proof (Hn5 m M5) as H.
      rewrite Ht4 in H; simpl in H; rename H into Bm.
      pose proof (Hn6 m) as H.
      rewrite Bm in H; simpl in H; rename H into Am.
      pose proof (Hn3 m M3) as H.
      rewrite Am in H; apply oppd_sym in H; simpl in H.
      rename H into BCm.
      remember BCm as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Bm, Ht4, digit_add_1_l in H.
      apply oppd_1_iff in H.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H; rewrite H5 in H; exfalso; revert H; apply digit_neq_1_0.

      eapply min_neq_lt in M4; eauto ; try (do 2 right; left; auto).
      simpl in Hm.
      destruct (Nat.min_dec di4 di5) as [L1| L1]; rewrite L1 in Hm.
       destruct (Nat.min_dec di3 di4) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M3; apply Nat.lt_irrefl.

        subst m; exfalso; revert M4; apply Nat.lt_irrefl.

       destruct (Nat.min_dec di3 di5) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M3; apply Nat.lt_irrefl.

        subst m; exfalso; revert M5; apply Nat.lt_irrefl.

  move H5 at top; rewrite <- H5 in *; clear u H5.
  destruct s6 as [di6| ]; [ idtac | clear H6 ].
   remember (List.fold_right min di6 [di3; di4 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn3, Ht3).
   rewrite H3 in Ht3; symmetry in Ht3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn6, Ht6).
   rewrite H6 in Ht6; symmetry in Ht6.
   destruct (eq_nat_dec di3 m) as [M3| M3].
    move M3 at top; subst di3.
    remember Ht3 as H; clear HeqH.
    unfold I_add_i in H.
    rewrite Hn5, digit_opp_add_diag_l, digit_add_1_l in H.
    apply oppd_1_iff in H.
    rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
    exfalso; revert H; apply digit_neq_1_0.

    eapply min_neq_lt in M3; eauto ; try (right; left; auto).
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite H6, Ht6, digit_add_nilpotent, digit_add_0_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_relay9 in H; [ idtac | eassumption ].
      simpl in H; rewrite H3 in H.
      rename H into A_BCm.
      pose proof (Hn3 m M3) as H.
      rewrite H6 in H.
      apply oppd_sym in H.
      unfold I_add_i in H.
      rewrite Ht6, Ht4, digit_add_0_r in H.
      apply digit_move_l_r_1 in H.
      rewrite digit_opp_add_diag_r in H.
      rename H into BCm.
      exfalso; eapply case_1; eassumption.

      eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
      exists m, 1%D.
      move H6 at top.
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split.
       pose proof (Hn3 m M3) as H.
       unfold I_add_i in H.
       rewrite H6, Hn5, digit_opp_add_diag_l, digit_opp_involutive in H.
       symmetry; assumption.

       split.
        pose proof (Hn4 m M4) as H.
        unfold I_add_i in H.
        rewrite H6, Hn5, digit_add_1_l in H.
        rewrite digit_opp_involutive in H.
        apply digit_move_l_r_1 in H.
        rewrite digit_opp_add_diag_r in H.
        assumption.

        intros dj Hdj; apply Hn4.
        eapply le_lt_trans; eassumption.

     eapply min_neq_lt in M6; eauto ; try (left; auto).
     destruct (eq_nat_dec di4 m) as [M4| M4].
      move M4 at top; subst di4.
      pose proof (Hn5 m) as H.
      rewrite Ht4 in H; simpl in H.
      rename H into Bm.
      pose proof (Hn6 m M6) as H.
      rewrite Bm in H; simpl in H.
      rename H into Am.
      pose proof (Hn3 m M3) as H.
      rewrite Am in H.
      apply oppd_sym in H; simpl in H.
      unfold I_add_i in H.
      rewrite Bm, Ht4, digit_add_1_l in H.
      apply oppd_1_iff in H.
      rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
      exfalso; revert H; apply digit_neq_1_0.

      eapply min_neq_lt in M4; [ idtac | eauto  | do 2 right; left; auto ].
      simpl in Hm.
      destruct (Nat.min_dec di4 di6) as [L1| L1]; rewrite L1 in Hm.
       destruct (Nat.min_dec di3 di4) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M3; apply Nat.lt_irrefl.

        subst m; exfalso; revert M4; apply Nat.lt_irrefl.

       destruct (Nat.min_dec di3 di6) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M3; apply Nat.lt_irrefl.

        subst m; exfalso; revert M6; apply Nat.lt_irrefl.

   remember (List.fold_right min di4 [di3 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn3, Ht3).
   rewrite H3 in Ht3; symmetry in Ht3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn6.
   destruct (eq_nat_dec di3 m) as [M3| M3].
    move M3 at top; subst di3.
    remember Ht3 as H; clear HeqH.
    unfold I_add_i in H.
    rewrite Hn5, digit_opp_add_diag_l, digit_add_1_l in H.
    apply oppd_1_iff in H.
    rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
    exfalso; revert H; apply digit_neq_1_0.

    eapply min_neq_lt in M3; eauto ; try (right; left; auto).
    destruct (eq_nat_dec di4 m) as [M4| M4].
     move M4 at top; subst di4.
     pose proof (Hn5 m) as H.
     rewrite Ht4 in H; simpl in H.
     rename H into Bm.
     pose proof (Hn6 m) as H.
     rewrite Bm in H; simpl in H.
     rename H into Am.
     pose proof (Hn3 m M3) as H.
     rewrite Am in H.
     apply oppd_sym in H; simpl in H.
     unfold I_add_i in H.
     rewrite Bm, Ht4, digit_add_1_l in H.
     apply oppd_1_iff in H.
     rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     exfalso; revert H; apply digit_neq_1_0.

     eapply min_neq_lt in M4; [ idtac | eauto  | left; auto ].
     simpl in Hm.
     destruct (Nat.min_dec di3 di4) as [L1| L1]; rewrite L1 in Hm.
      subst m; exfalso; revert M3; apply Nat.lt_irrefl.

      subst m; exfalso; revert M4; apply Nat.lt_irrefl.

 destruct s5 as [di5| ].
  destruct s6 as [di6| ].
   remember (List.fold_right min di6 [di4; di5 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn5, Ht5).
   rewrite H5 in Ht5; symmetry in Ht5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn6, Ht6).
   rewrite H6 in Ht6; symmetry in Ht6.
   destruct (eq_nat_dec di5 m) as [M5| M5].
    move M5 at top; subst di5.
    destruct (eq_nat_dec di4 m) as [M4| M4].
     move M4 at top; subst di4.
     rewrite Ht4 in Ht5.
     rewrite <- Ht5 in *; clear u Ht5.
     destruct (eq_nat_dec di6 m) as [M6| M6].
      move M6 at top; subst di6.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite H6, Ht6, digit_add_nilpotent, digit_add_0_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_inf_relay9 in H; simpl in H.
      rename H into A_BCm.
      pose proof (Hn3 m) as H.
      rewrite H6 in H.
      apply oppd_sym in H.
      unfold I_add_i in H.
      rewrite Ht6, Ht4, digit_add_0_r in H.
      apply digit_move_l_r_1 in H.
      rewrite digit_opp_add_diag_r in H.
      rename H into BCm.
      exfalso; eapply case_1; eassumption.

      eapply min_neq_lt in M6; eauto ; try (left; auto).
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Hn6 in H; [ idtac | assumption ].
      rewrite digit_opp_add_diag_l, digit_add_1_l in H.
      apply oppd_0_iff in H.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H; rewrite H6 in H; exfalso; revert H; apply digit_neq_0_1.

     eapply min_neq_lt in M4; eauto ; try (right; left; auto).
     destruct (eq_nat_dec di6 m) as [M6| M6].
      move M6 at top; subst di6.
      exists m, (oppd u).
      split; [ rewrite carry_before_inf_relay9; auto; reflexivity | idtac ].
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split.
       pose proof (Hn3 m) as H.
       unfold I_add_i in H.
       rewrite H6, H5, Ht5, digit_add_nilpotent, digit_add_0_l in H.
       apply oppd_sym in H; assumption.

       split.
        pose proof (Hn4 m M4) as H.
        unfold I_add_i in H.
        rewrite H6, H5, Ht5, digit_add_nilpotent, digit_add_0_l in H.
        assumption.

        intros dj Hdj; apply Hn4.
        eapply le_lt_trans; eassumption.

      eapply min_neq_lt in M6; eauto ; try (left; auto).
      exists m, u.
      split; [ rewrite carry_before_inf_relay9; auto; reflexivity | idtac ].
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split.
       pose proof (Hn3 m) as H.
       unfold I_add_i in H.
       rewrite Hn6 in H; [ idtac | assumption ].
       rewrite H5, Ht5, digit_add_nilpotent, digit_add_0_l in H.
       apply oppd_sym in H; rewrite digit_opp_involutive in H.
       assumption.

       split.
        pose proof (Hn4 m M4) as H.
        unfold I_add_i in H.
        rewrite Hn6 in H; [ idtac | assumption ].
        rewrite digit_opp_add_diag_l, Ht5 in H.
        apply digit_move_l_r_1 in H.
        rewrite digit_opp_involutive in H; assumption.

        intros dj Hdj; apply Hn4.
        eapply le_lt_trans; eassumption.

    eapply min_neq_lt in M5; eauto ; try (do 2 right; left; auto).
    destruct (eq_nat_dec di4 m) as [M4| M4].
     move M4 at top; subst di4.
     destruct (eq_nat_dec di6 m) as [M6| M6].
      move M6 at top; subst di6.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite H6, Ht6, digit_add_nilpotent, digit_add_0_l in H.
      rename H into ABm.
      remember Hs3 as H; clear HeqH.
      eapply carry_before_inf_relay9 in H; simpl in H.
      rename H into A_BCm.
      pose proof (Hn3 m) as H.
      rewrite H6 in H.
      apply oppd_sym in H.
      unfold I_add_i in H.
      rewrite Ht6, Ht4, digit_add_0_r in H.
      apply digit_move_l_r_1 in H.
      rewrite digit_opp_add_diag_r in H.
      rename H into BCm.
      exfalso; eapply case_1; eassumption.

      eapply min_neq_lt in M6; eauto ; try (left; auto).
      pose proof (Hn5 m M5) as Bm.
      rewrite Ht4 in Bm; simpl in Bm.
      pose proof (Hn6 m M6) as Am.
      rewrite Bm in Am; simpl in Am.
      pose proof (Hn3 m) as BCm.
      rewrite Am in BCm; apply oppd_sym in BCm; simpl in BCm.
      remember BCm as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Bm, Ht4, digit_add_1_l in H.
      apply oppd_1_iff in H.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H; rewrite H5 in H.
      rewrite H in *; clear u H.
      remember H4 as H; clear HeqH.
      unfold I_add_i in H.
      rewrite Am, Bm, digit_add_1_l in H.
      apply oppd_0_iff in H.
      erewrite carry_before_relay9 in H; try eassumption.
      simpl in H; rewrite H6 in H. exfalso; revert H; apply digit_neq_0_1.

     eapply min_neq_lt in M4; eauto ; try (right; left; auto).
     destruct (eq_nat_dec di6 m) as [M6| M6].
      move M6 at top; subst di6.
      exists m, u.
      split; [ rewrite carry_before_inf_relay9; auto; reflexivity | idtac ].
      split; [ erewrite carry_before_relay9; eassumption | idtac ].
      split.
       pose proof (Hn3 m) as H.
       unfold I_add_i in H.
       rewrite Hn5 in H; [ idtac | assumption ].
       rewrite H6, digit_opp_add_diag_l, digit_opp_involutive in H.
       symmetry; assumption.

       split.
        pose proof (Hn4 m M4) as H.
        unfold I_add_i in H.
        rewrite Hn5 in H; [ idtac | assumption ].
        rewrite H6, digit_add_shuffle0, digit_add_comm in H.
        apply digit_move_l_r_1 in H.
        rewrite digit_add_nilpotent in H.
        apply digit_eq_add_0 in H; symmetry; assumption.

        intros dj Hdj; apply Hn4.
        eapply le_lt_trans; eassumption.

      eapply min_neq_lt in M6; eauto ; try (left; auto).
      simpl in Hm.
      destruct (Nat.min_dec di5 di6) as [L1| L1]; rewrite L1 in Hm.
       destruct (Nat.min_dec di4 di5) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M4; apply Nat.lt_irrefl.

        subst m; exfalso; revert M5; apply Nat.lt_irrefl.

       destruct (Nat.min_dec di4 di6) as [L2| L2]; rewrite L2 in Hm.
        subst m; exfalso; revert M4; apply Nat.lt_irrefl.

        subst m; exfalso; revert M6; apply Nat.lt_irrefl.

   rewrite <- H6 in *; clear u H6.
   remember (List.fold_right min di5 [di4 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn5, Ht5).
   rewrite H5 in Ht5; symmetry in Ht5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn6.
   destruct (eq_nat_dec di5 m) as [M5| M5].
    move M5 at top; subst di5.
    destruct (eq_nat_dec di4 m) as [M4| M4].
     move M4 at top; subst di4.
     rewrite Ht5 in Ht4; exfalso; revert Ht4; apply digit_neq_1_0.

     eapply min_neq_lt in M4; eauto ; try (right; left; auto).
     exists m, 1%D.
     split; [ rewrite carry_before_inf_relay9; auto; reflexivity | idtac ].
     split; [ erewrite carry_before_relay9; eassumption | idtac ].
     split.
      pose proof (Hn3 m) as H.
      unfold I_add_i in H.
      rewrite Hn6, H5, Ht5, digit_add_1_r, digit_add_0_l in H.
      apply oppd_sym in H; assumption.

      split.
       pose proof (Hn4 m M4) as H.
       unfold I_add_i in H.
       rewrite Hn6, H5, Ht5, digit_add_1_r, digit_opp_involutive in H.
       symmetry in H; apply oppd_sym in H.
       assumption.

       intros dj Hdj; apply Hn4.
       eapply le_lt_trans; eassumption.

    eapply min_neq_lt in M5; eauto ; try (left; auto).
    destruct (eq_nat_dec di4 m) as [M4| M4].
     move M4 at top; subst di4.
     pose proof (Hn5 m M5) as Bm.
     rewrite Ht4 in Bm; simpl in Bm.
     pose proof (Hn6 m) as Am.
     rewrite Bm in Am; simpl in Am.
     pose proof (Hn3 m) as BCm.
     rewrite Am in BCm; apply oppd_sym in BCm; simpl in BCm.
     remember BCm as H; clear HeqH.
     unfold I_add_i in H.
     rewrite Bm, Ht4, digit_add_1_l in H.
     apply oppd_1_iff in H.
     erewrite carry_before_relay9 in H; try eassumption.
     simpl in H; rewrite H5 in H.
     exfalso; revert H; apply digit_neq_1_0.

     eapply min_neq_lt in M4; eauto ; try (right; left; auto).
     simpl in Hm.
     destruct (Nat.min_dec di4 di5) as [L1| L1]; rewrite L1 in Hm.
      subst m; exfalso; revert M4; apply Nat.lt_irrefl.

      subst m; exfalso; revert M5; apply Nat.lt_irrefl.

  rewrite <- H5 in *; clear u H5.
  destruct s6 as [di6| ]; [ idtac | clear H6 ].
   remember (List.fold_right min di6 [di4 … []]) as m eqn:Hm .
   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn6, Ht6).
   rewrite H6 in Ht6; symmetry in Ht6.
   destruct (eq_nat_dec di4 m) as [M4| M4].
    move M4 at top; subst di4.
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     remember H4 as H; clear HeqH.
     unfold I_add_i in H.
     rewrite H6, Ht6, digit_add_nilpotent, digit_add_0_l in H.
     rename H into ABm.
     remember Hs3 as H; clear HeqH.
     eapply carry_before_inf_relay9 in H; simpl in H.
     rename H into A_BCm.
     pose proof (Hn3 m) as H.
     rewrite H6 in H.
     apply oppd_sym in H.
     unfold I_add_i in H.
     rewrite Ht6, Ht4, digit_add_0_r in H.
     apply digit_move_l_r_1 in H.
     rewrite digit_opp_add_diag_r in H.
     rename H into BCm.
     exfalso; eapply case_1; eassumption.

     eapply min_neq_lt in M6; eauto ; try (left; auto).
     pose proof (Hn5 m) as Bm.
     rewrite Ht4 in Bm; simpl in Bm.
     pose proof (Hn6 m M6) as Am.
     rewrite Bm in Am; simpl in Am.
     pose proof (Hn3 m) as BCm; apply oppd_sym in BCm.
     rewrite Am in BCm; simpl in BCm.
     remember BCm as H; clear HeqH.
     unfold I_add_i in H.
     rewrite Bm, Ht4, digit_add_1_l in H.
     apply oppd_1_iff in H.
     rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
     exfalso; revert H; apply digit_neq_1_0.

    eapply min_neq_lt in M4; eauto ; try (right; left; auto).
    destruct (eq_nat_dec di6 m) as [M6| M6].
     move M6 at top; subst di6.
     exists m, 1%D.
     split; [ rewrite carry_before_inf_relay9; auto; reflexivity | idtac ].
     split; [ erewrite carry_before_relay9; eassumption | idtac ].
     split.
      pose proof (Hn3 m) as H.
      unfold I_add_i in H.
      rewrite H6, Hn5, digit_opp_add_diag_l, digit_opp_involutive in H.
      symmetry; assumption.

      split.
       pose proof (Hn4 m M4) as H.
       unfold I_add_i in H.
       rewrite H6, Hn5, digit_add_1_l, digit_opp_involutive in H.
       apply digit_move_l_r_1 in H.
       rewrite digit_opp_add_diag_r in H.
       assumption.

       intros dj Hdj; apply Hn4.
       eapply le_lt_trans; eassumption.

     eapply min_neq_lt in M6; eauto ; try (left; auto).
     simpl in Hm.
     destruct (Nat.min_dec di4 di6) as [L1| L1]; rewrite L1 in Hm.
      subst m; exfalso; revert M4; apply Nat.lt_irrefl.

      subst m; exfalso; revert M6; apply Nat.lt_irrefl.

   remember Hs3 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn3.
   remember Hs4 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   destruct H as (Hn4, Ht4).
   rewrite H4 in Ht4; symmetry in Ht4.
   remember Hs5 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn5.
   remember Hs6 as H; clear HeqH.
   apply fst_same_iff in H; simpl in H.
   rename H into Hn6.
   rename di4 into m.
   pose proof (Hn5 m) as Bm.
   rewrite Ht4 in Bm; simpl in Bm.
   pose proof (Hn6 m) as Am.
   rewrite Bm in Am; simpl in Am.
   pose proof (Hn3 m) as BCm; apply oppd_sym in BCm.
   rewrite Am in BCm; simpl in BCm.
   remember BCm as H; clear HeqH.
   unfold I_add_i in H.
   rewrite Bm, Ht4, digit_add_1_l in H.
   apply oppd_1_iff in H.
   rewrite carry_before_inf_relay9 in H; [ idtac | assumption ].
   exfalso; revert H; apply digit_neq_1_0.
Qed.

Theorem case_3 : ∀ x y z i u,
  (carry x (y + z) i = 1)%D
  → (carry (x + y) z i = 0)%D
  → (carry y z i = u)%D
  → (carry x y i = u)%D
  → False.
Proof.
intros x y z i u Hc3 Hc4 Hc5 Hc6.
remember Hc4 as H; clear HeqH.
unfold carry in H; simpl in H.
remember (fst_same (x + y) z i) as s eqn:Hs .
destruct s as [di| ]; [ idtac | exfalso; revert H; apply digit_neq_1_0 ].
symmetry in Hs; clear H.
revert x y z i u Hc3 Hc4 Hc5 Hc6 Hs.
induction di as (di, IHdi) using all_lt_all; intros.
remember Hc3 as H; clear HeqH.
eapply carry_repeat2 with (y := y) in H; try eassumption.
destruct H as (n, (t, (Rx_yzn, (Rxy_zn, (Ryzn, (Rxyn, Hnxy_z)))))).
remember Hs as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hnxy_z2, Hxy_z).
destruct (le_dec di n) as [H1| H1].
 rewrite Hnxy_z in Hxy_z; [ idtac | assumption ].
 revert Hxy_z; apply no_fixpoint_oppd.

 apply Nat.nle_gt in H1.
 remember (di - S n) as dj.
 apply Nat_sub_add_r in Heqdj; [ idtac | assumption ].
 remember (I_shift_l (S n) (x + y)%I) as x'y' eqn:Hxy .
 remember (I_shift_l (S n) z) as z' eqn:Hc .
 eapply fst_same_shift in Hs; try eassumption.
 assert (0 < S n) as Hn by apply Nat.lt_0_succ.
 assert (di - S n < di) as H by (apply Nat.sub_lt; assumption).
 subst x'y'.
 rewrite fst_same_shift_add_l in Hs.
 remember (I_shift_l (S n) x) as x' eqn:Ha .
 remember (I_shift_l (S n) y) as y' eqn:Hb .
 eapply IHdi with (x := x') (y := y') (z := z'); try eassumption.
  subst x' y' z'.
  rewrite carry_comm.
  rewrite carry_shift_add_l, Nat.add_succ_r.
  rewrite carry_comm; assumption.

  subst x' y' z'.
  rewrite carry_shift_add_l, Nat.add_succ_r; assumption.

  subst y' z'.
  rewrite carry_shift.
  rewrite Nat.add_succ_r; eassumption.

  subst x' y'.
  rewrite carry_shift.
  rewrite Nat.add_succ_r; assumption.
Qed.

Theorem I_add_assoc_norm : ∀ x y z,
  ((x + 0) + ((y + 0) + (z + 0)) = ((x + 0) + (y + 0)) + (z + 0))%I.
Proof.
intros x y z.
rename x into x0; rename y into y0; rename z into z0.
remember (x0 + 0)%I as x.
remember (y0 + 0)%I as y.
remember (z0 + 0)%I as z.
unfold I_eq; intros i; simpl.
unfold I_add_i; simpl.
do 2 rewrite digit_add_0_r.
remember (carry (x + (y + z))%I 0%I (S i)) as c1 eqn:Hc1 .
remember (carry (x + y + z)%I 0%I (S i)) as c2 eqn:Hc2 .
unfold I_add_i; simpl.
remember (carry x (y + z)%I (S i)) as c3 eqn:Hc3 .
remember (carry (x + y)%I z (S i)) as c4 eqn:Hc4 .
unfold I_add_i; simpl.
remember (carry y z (S i)) as c5 eqn:Hc5 .
remember (carry x y (S i)) as c6 eqn:Hc6 .
do 8 rewrite <- digit_add_assoc; f_equal; f_equal; symmetry.
rewrite digit_add_comm, <- digit_add_assoc; f_equal; symmetry.
rewrite digit_add_assoc.
symmetry in Hc1, Hc2, Hc3, Hc4, Hc5, Hc6.
move c2 before c1; move c3 before c2.
move c4 before c3; move c5 before c4.
move c6 before c5.
remember Hc1 as H; clear HeqH.
erewrite carry_sum_3_noI_assoc_r in H; try eassumption.
move H at top; subst c1.
remember Hc2 as H; clear HeqH.
erewrite carry_sum_3_noI_assoc_l in H; try eassumption.
move H at top; subst c2.
do 2 rewrite digit_add_0_r.
destruct c3, c4, c5, c6; try reflexivity; exfalso.
 eapply case_1; eassumption.

 rewrite carry_comm_l in Hc4.
 eapply case_1; rewrite carry_comm; eassumption.

 eapply case_3; eassumption.

 eapply case_3; eassumption.

 rewrite carry_comm_r in Hc3.
 rewrite carry_comm_l in Hc4.
 eapply case_3; rewrite carry_comm; eassumption.

 rewrite carry_comm_r in Hc3.
 rewrite carry_comm_l in Hc4.
 eapply case_3; rewrite carry_comm; eassumption.

 clear Hc1 Hc2.
 eapply case_2; eassumption.

 rewrite carry_comm_r in Hc3.
 eapply case_2; rewrite carry_comm; eassumption.
Qed.

Theorem I_add_assoc : ∀ x y z, (x + (y + z) = (x + y) + z)%I.
Proof.
intros x y z.
pose proof (I_add_assoc_norm x y z) as H.
do 3 rewrite I_add_0_r in H; assumption.
Qed.

(* decidability *)

Theorem I_zerop : ∀ x, {(x = 0)%I} + {(x ≠ 0)%I}.
Proof.
intros x.
remember (fst_same (x + 0%I) I_one 0) as s eqn:Hs .
apply fst_same_sym_iff in Hs; simpl in Hs.
destruct s as [di| ].
 destruct Hs as (Hn, Hs).
 right; intros H.
 unfold I_eq in H; simpl in H.
 pose proof (H di) as HH; simpl in HH.
 rewrite Hs in HH; symmetry in HH.
 unfold I_add_i in HH; simpl in HH.
 unfold carry in HH; simpl in HH.
 rewrite fst_same_diag in HH; discriminate HH.

 left.
 unfold I_eq; intros i; simpl.
 rewrite Hs.
 unfold I_add_i; simpl.
 unfold carry; simpl.
 rewrite fst_same_diag; reflexivity.
Qed.

Theorem I_eq_dec : ∀ x y, {(x = y)%I} + {(x ≠ y)%I}.
Proof.
intros x y.
destruct (I_zerop (x - y)%I) as [Hxy| Hxy].
 left; unfold I_sub in Hxy; rewrite I_add_comm in Hxy.
 eapply I_add_compat with (x := y) in Hxy; [ idtac | reflexivity ].
 rewrite I_add_assoc, fold_I_sub, I_sub_diag, I_add_comm in Hxy.
 do 2 rewrite I_add_0_r in Hxy.
 assumption.

 right; unfold I_sub in  Hxy; intros H; apply Hxy; rewrite H.
 apply I_sub_diag.
Qed.

Theorem I_decidable : ∀ x y, Decidable.decidable (x = y)%I.
Proof.
intros x y.
destruct (I_eq_dec x y); [ left | right ]; assumption.
Qed.

(* morphisms *)

Theorem fst_same_opp_some_some : ∀ x y i dj,
  (x = y)%I
  → fst_same (- x) 0 (S i) = Some 0
  → fst_same (- y) 0 (S i) = Some (S dj)
  → x.[i] = y.[i].
Proof.
intros x y i dj4 Heq Hs3 Hs4.
remember Hs3 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (_, Ht3).
rewrite Nat.add_0_r in Ht3.
apply oppd_0_iff in Ht3.
remember Hs4 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hn4, Ht4).
apply oppd_0_iff in Ht4.
remember Heq as H; clear HeqH.
unfold I_eq in H; simpl in H.
rename H into Hxy.
pose proof (Hxy i) as Hi; simpl in Hi.
unfold I_add_i in Hi; simpl in Hi.
do 2 rewrite digit_add_0_r in Hi.
unfold carry in Hi; simpl in Hi.
remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
remember (fst_same y 0 (S i)) as s2 eqn:Hs2 .
pose proof (Hn4 O (Nat.lt_0_succ dj4)) as H.
rewrite Nat.add_0_r in H.
apply oppd_1_iff in H.
rename H into Hy4.
remember Ht3 as H; clear HeqH.
eapply I_eq_neq_prop in H; try eassumption.
destruct H as [(Hxi, Hyi)| (Hxi, Hyi)]; simpl in Hxi, Hyi.
 rewrite Hyi in Ht4; discriminate Ht4.

 destruct s1 as [dj1| ].
  remember Hs1 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn1, Ht1).
  rewrite Ht1, digit_add_0_r in Hi.
  destruct s2 as [dj2| ].
   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn2, Ht2).
   rewrite Ht2, digit_add_0_r in Hi.
   rewrite Hi; reflexivity.

   exfalso.
   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rename H into Hn2.
   pose proof (Hn2 O) as H.
   rewrite Nat.add_0_r, Hy4 in H; discriminate H.

  remember Hs1 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  rename H into Hn1.
  pose proof (Hxi O) as H.
  rewrite Hn1 in H; discriminate H.
Qed.

Theorem fst_same_opp_some_0_none : ∀ x y i,
  (x = y)%I
  → fst_same (- x) 0 (S i) = Some 0
  → fst_same (- y) 0 (S i) = None
  → x.[i] ≠ y.[i].
Proof.
intros x y i Heq Hs1 Hs2.
apply fst_same_iff in Hs1; simpl in Hs1.
destruct Hs1 as (Hn1, Ht1).
apply fst_same_iff in Hs2; simpl in Hs2.
rewrite Nat.add_0_r in Ht1.
apply oppd_0_iff in Ht1.
clear Hn1.
intros Hxy.
pose proof (Heq i) as Hi; simpl in Hi.
unfold I_add_i in Hi; simpl in Hi.
do 2 rewrite digit_add_0_r in Hi.
rewrite Hxy in Hi.
apply digit_move_l_r_1 in Hi.
rewrite digit_add_assoc in Hi.
rewrite digit_add_nilpotent, digit_add_0_l in Hi.
unfold carry in Hi; simpl in Hi.
remember (fst_same x 0 (S i)) as s3 eqn:Hs3 .
remember (fst_same y 0 (S i)) as s4 eqn:Hs4 .
apply fst_same_sym_iff in Hs3; simpl in Hs3.
apply fst_same_sym_iff in Hs4; simpl in Hs4.
destruct s3 as [dj3| ].
 destruct Hs3 as (Hn3, Ht3).
 rewrite Ht3 in Hi.
 destruct s4 as [dj4| ]; [ idtac | discriminate Hi ].
 destruct Hs4 as (Hn4, Ht4); clear Hi.
 destruct dj3.
  rewrite Nat.add_0_r, Ht1 in Ht3; discriminate Ht3.

  destruct dj4.
   clear Hn4; rewrite Nat.add_0_r in Ht4.
   remember Ht1 as H; clear HeqH.
   eapply I_eq_neq_prop in H; try eassumption.
   destruct H as [(Hxi, Hyi)| (Hxi, Hyi)]; simpl in Hxi, Hyi.
    rewrite Hxi in Ht3; discriminate Ht3.

    pose proof (Hyi O) as H.
    apply oppd_0_iff in H.
    rewrite Hs2 in H; discriminate H.

   pose proof (Hn4 O (Nat.lt_0_succ dj4)) as H.
   apply oppd_0_iff in H.
   rewrite Hs2 in H; discriminate H.

 destruct s4 as [dj4| ].
  destruct Hs4 as (Hn4, Ht4).
  rewrite Ht4 in Hi; discriminate Hi.

  pose proof (Hs2 O) as H.
  rewrite Hs4 in H; discriminate H.
Qed.

Theorem fst_same_some_after : ∀ x y i di,
  fst_same x y i = Some di
  → fst_same x y (i + di) = Some 0.
Proof.
intros x y i di Hdi.
apply fst_same_iff in Hdi; simpl in Hdi.
destruct Hdi as (Hni, Hti).
apply fst_same_iff; simpl.
split; [ idtac | rewrite Nat.add_0_r; assumption ].
intros dj Hdj; exfalso; revert Hdj; apply Nat.nlt_0_r.
Qed.

Theorem fst_same_opp_some_none : ∀ x y i dj,
  (x = y)%I
  → fst_same (- x) 0 (S i) = Some dj
  → fst_same (- y) 0 (S i) = None
  → x.[i] ≠ y.[i].
Proof.
intros x y i dj3 Heq Hs3 Hs4.
remember Hs4 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
rename H into Hn4.
remember Hs3 as H; clear HeqH.
apply fst_same_iff in H; simpl in H.
destruct H as (Hn3, Ht3).
apply oppd_0_iff in Ht3.
pose proof (Heq i) as Hi; simpl in Hi.
unfold I_add_i in Hi; simpl in Hi.
do 2 rewrite digit_add_0_r in Hi.
unfold carry in Hi; simpl in Hi.
remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
remember (fst_same y 0 (S i)) as s2 eqn:Hs2 .
pose proof (Hn4 dj3) as H.
apply oppd_1_iff in H.
rename H into Hy.
remember Ht3 as H; clear HeqH.
eapply I_eq_neq_prop in H; try eassumption.
destruct H as [(Hxi, Hyi)| (Hxi, Hyi)]; simpl in Hxi, Hyi.
 destruct s1 as [dj1| ].
  remember Hs1 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn1, Ht1).
  rewrite Ht1, digit_add_0_r in Hi.
  destruct s2 as [dj2| ].
   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn2, Ht2).
   rewrite Ht2, digit_add_0_r in Hi.
   exfalso.
   destruct dj3.
    rewrite Nat.add_0_r in Hxi, Hyi.
    eapply fst_same_opp_some_0_none in Hs3; try eassumption.
    contradiction.

    remember Hs4 as H; clear HeqH.
    apply fst_same_inf_after with (di := S dj3) in H.
    simpl in H.
    eapply fst_same_opp_some_0_none in H; try eassumption.
     rewrite Nat.add_succ_r in H.
     apply H.
     rewrite <- digit_opp_involutive; apply oppd_sym.
     rewrite Hn3; [ idtac | apply Nat.lt_succ_diag_r ].
     apply Hn4.

     rewrite <- Nat.add_succ_l.
     apply fst_same_some_after; assumption.

   apply digit_neq_eq_opp; assumption.

  destruct s2 as [dj2| ].
   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn2, Ht2).
   rewrite Ht2, digit_add_0_r, digit_add_1_r in Hi.
   apply digit_neq_eq_opp, oppd_sym; symmetry; assumption.

   remember Hs2 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rewrite H in Hy; discriminate Hy.

 pose proof (Hyi O) as H.
 rewrite <- Nat.add_assoc in H.
 apply oppd_0_iff in H.
 rewrite Hn4 in H; discriminate H.
Qed.

Add Parametric Morphism : I_opp
  with signature I_eq ==> I_eq
  as I_opp_morph.
Proof.
intros x y Hxy.
remember Hxy as Heq; clear HeqHeq.
unfold I_eq, I_eq_ext in Hxy; simpl in Hxy.
unfold I_eq; intros i; simpl.
pose proof (Hxy i) as Hi.
unfold I_add_i in Hi; simpl in Hi.
do 2 rewrite digit_add_0_r in Hi.
unfold I_add_i; simpl.
do 2 rewrite digit_add_0_r.
unfold carry in Hi; simpl in Hi.
unfold carry; simpl.
remember (fst_same x 0 (S i)) as s1 eqn:Hs1 .
remember (fst_same y 0 (S i)) as s2 eqn:Hs2 .
remember (fst_same (- x) 0 (S i)) as s3 eqn:Hs3 .
remember (fst_same (- y) 0 (S i)) as s4 eqn:Hs4 .
remember Hs3 as H; clear HeqH.
apply fst_same_sym_iff in H; simpl in H.
destruct s3 as [dj3| ].
 destruct H as (Hn3, Ht3).
 rewrite Ht3, digit_add_0_r.
 apply oppd_0_iff in Ht3.
 destruct s4 as [dj4| ].
  remember Hs4 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn4, Ht4).
  rewrite Ht4, digit_add_0_r.
  apply oppd_sym; symmetry.
  rewrite digit_opp_involutive.
  apply oppd_0_iff in Ht4.
  destruct dj3.
   clear Hn3; rewrite Nat.add_0_r in Ht3.
   destruct dj4.
    clear Hn4; rewrite Nat.add_0_r in Ht4.
    destruct s1 as [dj1| ].
     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, Ht1).
     rewrite Ht1, digit_add_0_r in Hi.
     destruct s2 as [dj2| ].
      remember Hs2 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn2, Ht2).
      rewrite Ht2, digit_add_0_r in Hi.
      rewrite Hi; reflexivity.

      exfalso.
      remember (y .[ i]) as b eqn:Hy .
      symmetry in Hy.
      destruct b; simpl in Hi.
       symmetry in Heq.
       remember Hy as H; clear HeqH.
       eapply I_eq_neq_prop in H; try eassumption.
       destruct H as [(Hyi, Hxi)| (Hyi, Hxi)]; simpl in Hxi, Hyi.
        rewrite <- Nat.add_1_r, Hxi in Ht3; discriminate Ht3.

        pose proof (Hyi O) as H.
        rewrite Nat.add_1_r, Ht4 in H; discriminate H.

       remember Hi as H; clear HeqH.
       eapply I_eq_neq_prop in H; try eassumption.
       destruct H as [(Hxi, Hyi)| (Hxi, Hyi)]; simpl in Hxi, Hyi.
        rewrite <- Nat.add_1_r, Hyi in Ht4; discriminate Ht4.

        pose proof (Hxi O) as H.
        rewrite Nat.add_1_r, Ht3 in H; discriminate H.

     destruct s2 as [dj2| ].
      remember Hs2 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn2, Ht2).
      rewrite Ht2, digit_add_0_r in Hi.
      exfalso.
      remember (x .[ i]) as b eqn:Hx .
      symmetry in Hx, Hi.
      destruct b; simpl in Hi.
       remember Hx as H; clear HeqH.
       eapply I_eq_neq_prop in H; try eassumption.
       destruct H as [(Hxi, Hyi)| (Hxi, Hyi)]; simpl in Hxi, Hyi.
        rewrite <- Nat.add_1_r, Hyi in Ht4; discriminate Ht4.

        pose proof (Hxi O) as H.
        rewrite Nat.add_1_r, Ht3 in H; discriminate H.

       symmetry in Heq.
       remember Hi as H; clear HeqH.
       eapply I_eq_neq_prop in H; try eassumption.
       destruct H as [(Hyi, Hxi)| (Hyi, Hxi)]; simpl in Hxi, Hyi.
        rewrite <- Nat.add_1_r, Hxi in Ht3; discriminate Ht3.

        pose proof (Hyi O) as H.
        rewrite Nat.add_1_r, Ht4 in H; discriminate H.

      apply xorb_move_l_r_2 in Hi.
      rewrite Hi, digit_add_1_r, digit_add_1_r.
      apply digit_opp_involutive.

    symmetry in Hs3, Hs4.
    eapply fst_same_opp_some_some; eassumption.

   destruct dj4.
    clear Hn4; rewrite Nat.add_0_r in Ht4.
    symmetry in Heq; symmetry.
    symmetry in Hs3, Hs4.
    eapply fst_same_opp_some_some; eassumption.

    destruct s1 as [dj1| ].
     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     destruct H as (Hn1, Ht1).
     rewrite Ht1, digit_add_0_r in Hi.
     destruct s2 as [dj2| ].
      remember Hs2 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      destruct H as (Hn2, Ht2).
      rewrite Ht2, digit_add_0_r in Hi; assumption.

      exfalso.
      remember Hs2 as H; clear HeqH.
      apply fst_same_sym_iff in H; simpl in H.
      rename H into Hn2.
      pose proof (Hn4 O (Nat.lt_0_succ dj4)) as H.
      rewrite Hn2 in H; discriminate H.

     exfalso.
     remember Hs1 as H; clear HeqH.
     apply fst_same_sym_iff in H; simpl in H.
     rename H into Hn1.
     pose proof (Hn3 O (Nat.lt_0_succ dj3)) as H.
     rewrite Hn1 in H; discriminate H.

  remember Hs4 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  rename H into Hn4.
  rewrite digit_add_1_r; f_equal.
  apply digit_neq_eq_opp.
  symmetry in Hs3, Hs4.
  eapply fst_same_opp_some_none; eassumption.

 rename H into Hn3.
 destruct s4 as [dj4| ].
  remember Hs4 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  destruct H as (Hn4, Ht4).
  rewrite Ht4, digit_add_0_r.
  apply oppd_0_iff in Ht4.
  rewrite digit_add_1_r; f_equal.
  symmetry; apply digit_neq_eq_opp.
  symmetry in Heq, Hs3, Hs4.
  eapply fst_same_opp_some_none; eassumption.

  remember Hs4 as H; clear HeqH.
  apply fst_same_sym_iff in H; simpl in H.
  rename H into Hn4.
  destruct s1 as [dj1| ].
   remember Hs1 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   destruct H as (Hn1, Ht1).
   rewrite Ht1, digit_add_0_r in Hi.
   destruct s2 as [dj2| ].
    remember Hs2 as H; clear HeqH.
    apply fst_same_sym_iff in H; simpl in H.
    destruct H as (Hn2, Ht2).
    rewrite Ht2, digit_add_0_r in Hi.
    rewrite Hi; reflexivity.

    remember Hs2 as H; clear HeqH.
    apply fst_same_sym_iff in H; simpl in H.
    rename H into Hn2.
    pose proof (Hn4 O) as H.
    rewrite Hn2 in H; discriminate H.

   remember Hs1 as H; clear HeqH.
   apply fst_same_sym_iff in H; simpl in H.
   rename H into Hn1.
   pose proof (Hn3 O) as H.
   rewrite Hn1 in H; discriminate H.
Qed.

Add Parametric Morphism : I_sub
  with signature I_eq ==> I_eq ==> I_eq
  as I_sub_morph.
Proof.
intros x y Hxy z d Hcd.
unfold I_sub.
rewrite Hxy, Hcd; reflexivity.
Qed.

Theorem I_opp_involutive : ∀ x, (- - x = x)%I.
Proof.
intros x.
unfold I_eq; intros i; simpl.
unfold I_add_i; simpl.
do 2 rewrite digit_add_0_r.
rewrite digit_opp_involutive; f_equal.
erewrite carry_compat; [ reflexivity | simpl | simpl ].
 intros j; apply digit_opp_involutive.

 intros j; reflexivity.
Qed.

(* miscellaneous *)

Theorem I_opp_0 : (- 0 = 0)%I.
Proof.
unfold I_eq; intros i; simpl.
unfold I_add_i; simpl.
rewrite carry_diag; simpl.
unfold carry; simpl.
destruct (fst_same (- 0%I) 0 (S i)); reflexivity.
Qed.

Theorem I_add_shuffle0 : ∀ x y z, (x + y + z = x + z + y)%I.
Proof.
intros x y z.
do 2 rewrite <- I_add_assoc.
apply I_add_compat; [ reflexivity | apply I_add_comm ].
Qed.

Theorem I_sub_move_0_r : ∀ x y, (x - y = 0)%I ↔ (x = y)%I.
Proof.
intros x y.
split; intros Hxy.
 apply I_add_compat_r with (z := y) in Hxy.
 unfold I_sub in Hxy.
 rewrite I_add_shuffle0, <- I_add_assoc in Hxy.
 rewrite fold_I_sub, I_sub_diag in Hxy.
 rewrite I_add_0_r, I_add_comm, I_add_0_r in Hxy.
 assumption.

 rewrite Hxy; apply I_sub_diag.
Qed.

Close Scope nat_scope.
