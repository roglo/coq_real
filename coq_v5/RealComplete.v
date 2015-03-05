(* I is complete *)

Require Import Utf8 QArith NPeano Misc.
Require Import Real01 Real01Cmp Real01AddMono Real01Add.
Require Import Digit Real RealAdd RealAddGrp.

Open Scope nat_scope.

Definition I_abs_sub x y := if I_lt_dec x y then (y - x)%I else (x - y)%I.

Definition I_cauchy_sequence u :=
  ∀ ε, (ε ≠ 0)%I → ∃ N, ∀ p q, p > N → q > N → (I_abs_sub (u p) (u q) < ε)%I.

Definition I_converges_to u r :=
  ∀ ε, (ε ≠ 0)%I → ∃ N, ∀ n, n > N → (I_abs_sub r (u n) < ε)%I.

Definition R_cauchy_sequence u :=
  ∀ ε, (ε > 0)%R → ∃ N, ∀ p q, p > N → q > N → (R_abs (u p - u q) < ε)%R.

Axiom functional_choice :
  ∀ A B (P : A → B → Prop),
  (∀ x, ∃ y, P x y)
  → ∃ f, ∀ x, P x (f x).

Theorem R_lt_0_1 : (0 < 1)%R.
Proof.
unfold R_lt, R_compare; simpl.
rewrite carry_diag; simpl.
rewrite b2z_0; reflexivity.
Qed.

Definition R_max x y := if R_lt_dec x y then y else x.
Arguments R_max x%R y%R.

Fixpoint R_max_abs_seq_upto u n :=
  match n with
  | 0 => 0%R
  | S n1 => R_max (R_abs (u n)) (R_max_abs_seq_upto u n1)
  end.

Theorem R_le_max_l : ∀ x y, (x ≤ R_max x y)%R.
Proof.
intros x y.
unfold R_max.
destruct (R_lt_dec x y) as [H1| H1]; [ idtac | apply R_le_refl ].
apply R_lt_le_incl; assumption.
Qed.

Theorem I_eqs_eq_ext : ∀ x y, I_eq_ext x y ↔ (x == y)%I.
Proof.
intros x y.
unfold I_eq_ext, I_eqs, I_compare; simpl.
remember (fst_same x (-y) 0) as s1 eqn:Hs1.
apply fst_same_sym_iff in Hs1; simpl in Hs1.
split; intros Hxy.
 destruct s1 as [j1| ]; [ exfalso | reflexivity ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Hxy in Ht1; symmetry in Ht1.
 revert Ht1; apply Digit.no_fixpoint_opp.

 intros i.
 destruct s1 as [j1| ]; [ idtac | clear Hxy ].
  destruct (Digit.eq_dec (x.[j1]) 1); discriminate Hxy.

  rewrite Hs1; apply Digit.opp_involutive.
Qed.

Theorem carry_0_0_r : ∀ x, (x ≠≠ 1)%I → (carry x 0 0 = 0)%D.
Proof.
intros x Hx.
unfold carry; simpl.
remember (fst_same x 0 0) as s1 eqn:Hs1.
apply fst_same_sym_iff in Hs1; simpl in Hs1.
destruct s1 as [dj1|]; [ idtac | exfalso ].
destruct Hs1 as (Hn1, Ht1); assumption.
apply Hx; unfold I_eq; simpl.
apply I_eqs_eq_ext.
assumption.
Qed.

Theorem I_eq_ext_1 : ∀ x, I_eq_ext x 1 → (∀ i, (x.[i] = 1)%D).
Proof.
intros x Hx i.
apply Hx.
Qed.

Theorem yyy : ∀ x y i, (carry ((x + 0)%I + 0%I) y i = carry (x + 0%I) y i)%D.
Proof.
intros x y i.
unfold carry; simpl.
remember (fst_same ((x + 0)%I + 0%I) y i) as s1 eqn:Hs1.
remember (fst_same (x + 0%I) y i) as s2 eqn:Hs2.
destruct s1 as [dj1| ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Ht1); rewrite Ht1.
 destruct s2 as [dj2| ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2); rewrite Ht2.
  destruct (lt_eq_lt_dec dj1 dj2) as [[H1| H1]| H1].
   remember H1 as H; clear HeqH.
   apply Hn2 in H.
   unfold I_add_i in Ht1; simpl in Ht1.
   rewrite H, Digit.add_0_r in Ht1.
   unfold carry in Ht1; simpl in Ht1.
   remember (fst_same (x + 0%I) 0 (S (i + dj1))) as s3 eqn:Hs3.
   apply fst_same_sym_iff in Hs3; simpl in Hs3.
   destruct s3 as [dj3| ].
    destruct Hs3 as (Hn3, Ht3); rewrite Ht3, Digit.add_0_r in Ht1.
    exfalso; revert Ht1; apply Digit.no_fixpoint_opp.

    clear Ht1.
    unfold I_add_i in H; simpl in H.
    rewrite Digit.add_0_r in H.
    unfold carry in H; simpl in H.
    remember (fst_same x 0 (S (i + dj1))) as s4 eqn:Hs4.
    apply fst_same_sym_iff in Hs4; simpl in Hs4.
    destruct s4 as [dj4| ].
     destruct Hs4 as (Hn4, Ht4); rewrite Ht4, Digit.add_0_r in H.
     pose proof Hs3 dj4 as HH.
     unfold I_add_i in HH; simpl in HH.
     rewrite Ht4 in HH.
     do 2 rewrite Digit.add_0_l in HH; rewrite Digit.opp_0 in HH.
Abort.
  (* putain, ça a pas l'air de le faire, les mecs ;
     mais bon, faut que je regarde un peu plus... *)

Theorem R_norm_add : ∀ x y nx ny,
  nx = R_norm x
  → ny = R_norm y
  → (R_norm (nx + ny) = R_norm nx + R_norm ny)%R.
Proof.
intros x y nx ny Hnx Hny.
unfold R_eq; simpl.
split.
 do 6 rewrite <- Z.add_assoc.
 apply Z.add_cancel_l.
 symmetry; rewrite Z.add_comm; symmetry.
 do 2 rewrite <- Z.add_assoc.
 apply Z.add_cancel_l.
 subst nx ny; simpl.
 do 3 rewrite carry_add_0_0, b2z_0.
 do 2 rewrite Z.add_0_r; rewrite Z.add_0_l.
 rewrite Z.add_comm; f_equal.
 unfold carry; simpl.
 remember ((R_frac x + 0)%I) as nx eqn:Hnx.
 remember ((R_frac y + 0)%I) as ny eqn:Hny.
 remember (fst_same (nx + ny) 0 0) as s1 eqn:Hs1.
 remember (fst_same (nx + 0%I) (ny + 0%I) 0) as s2 eqn:Hs2.
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 apply fst_same_sym_iff in Hs2; simpl in Hs2.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Ht1); rewrite Ht1, b2z_0.
  destruct s2 as [di2| ]; [ idtac | exfalso ].
   destruct Hs2 as (Hn2, Ht2); rewrite Ht2.
   rewrite Hnx, Hny in Ht2.
   do 2 rewrite I_add_i_0_r in Ht2.
   rewrite Hny, I_add_i_0_r.
   destruct (lt_eq_lt_dec di1 di2) as [[H1| H1]| H1].
    apply Hn2 in H1.
    rewrite Hnx, Hny in H1.
    do 2 rewrite I_add_i_0_r in H1.
    rewrite Hnx, Hny in Ht1.
    unfold I_add_i in Ht1; simpl in Ht1.
    rewrite H1 in Ht1.
    rewrite Digit.opp_add_diag_l, Digit.add_1_l in Ht1.
    apply Digit.opp_0_iff in Ht1.
bbb.
   unfold I_add_i in Ht2; simpl in Ht2.
   do 2 rewrite Digit.add_0_r in Ht2.
bbb.

Theorem zzz : ∀ x y z,
  (R_norm x < R_norm y)%R
  → (R_norm x + R_norm z < R_norm y + R_norm z)%R.
Proof.
intros x y z Hxy.
unfold R_lt, R_compare in Hxy.
remember (R_norm x) as nx eqn:Hnx.
remember (R_norm y) as ny eqn:Hny.
remember (R_norm z) as nz eqn:Hnz.
move ny before nx; move nz before ny; move Hnz before Hny.
remember (R_int (R_norm nx) ?= R_int (R_norm ny))%Z as cmp1 eqn:Hcmp1.
symmetry in Hcmp1.
destruct cmp1; [ idtac | clear Hxy | discriminate Hxy ].
 apply Z.compare_eq in Hcmp1.
 remember (R_frac (R_norm nx)) as a.
 remember (R_frac (R_norm ny)) as b.
 remember (fst_same a (-b) 0) as s1 eqn:Hs1; subst a b.
 destruct s1 as [j1| ]; [ idtac | discriminate Hxy ].
 remember (Digit.dec (R_frac (R_norm nx) .[ j1])) as d eqn:Hd.
 destruct d as [H1| H1]; [ discriminate Hxy | clear Hd Hxy ].
 apply fst_same_sym_iff in Hs1; simpl in Hs1.
 destruct Hs1 as (Hn1, Ht1).
 rewrite H1 in Ht1; apply Digit.opp_sym in Ht1; rewrite Digit.opp_0 in Ht1.
 simpl in H1.
 rename H1 into Hx1; rename Ht1 into Hy1; move Hy1 before Hx1.
 simpl in Hcmp1.
 rewrite Hnx in Hcmp1 at 2.
 rewrite Hny in Hcmp1 at 2; simpl in Hcmp1.
 do 2 rewrite carry_add_0_0, b2z_0, Z.add_0_r in Hcmp1.
 rename j1 into i.
 unfold I_add_i in Hx1, Hy1; simpl in Hx1, Hy1.
 rewrite Hnx in Hx1 at 2; simpl in Hx1.
 rewrite Hny in Hy1 at 2; simpl in Hy1.
 rewrite carry_add_0_0 in Hx1, Hy1.
 do 2 rewrite Digit.add_0_r in Hx1, Hy1.
 unfold R_lt, R_compare.
 remember (R_norm (nx + nz)) as nxz eqn:Hnxz.
 remember (R_norm (ny + nz)) as nyz eqn:Hnyz.
 move nyz before nxz.
 remember ((R_int nxz ?= R_int nyz)%Z) as cmp2 eqn:Hcmp2.
 symmetry in Hcmp2.
 destruct cmp2; [ idtac | reflexivity | exfalso ].
  apply Z.compare_eq in Hcmp2.
  remember (fst_same (R_frac nxz) (- R_frac nyz) 0) as s2 eqn:Hs2.
  destruct s2 as [j2| ]; [ idtac | exfalso ].
  remember (Digit.dec (R_frac nxz .[ j2])) as d eqn:Hd.
  destruct d as [H1| H1]; [ exfalso; clear Hd | reflexivity ].
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  rewrite H1 in Ht2; apply Digit.opp_sym in Ht2; rewrite Digit.opp_1 in Ht2.
  rename H1 into Hxz1; rename Ht2 into Hyz1; move Hyz1 before Hxz1.
  rewrite Hnxz, Hnyz in Hcmp2; simpl in Hcmp2.
  rewrite Hcmp1 in Hcmp2.
  do 4 rewrite <- Z.add_assoc in Hcmp2.
  do 2 apply Z.add_cancel_l in Hcmp2.
SearchAbout (R_norm).
bbb.

 unfold R_lt, R_compare.
 remember (R_norm (nx + nz)) as a.
 remember (R_norm (ny + nz)) as b.
 remember (R_int a ?= R_int b)%Z as cmp2 eqn:Hcmp2.
 symmetry in Hcmp2.
 destruct cmp2; [ idtac | reflexivity | exfalso ].
  apply Z.compare_eq in Hcmp2.
  remember (fst_same (R_frac a) (- R_frac b) 0) as s2 eqn:Hs2.
  destruct s2 as [j2| ]; [ idtac | exfalso ].
  destruct (Digit.dec (R_frac a .[ j2])) as [H1| H1]; [ idtac | reflexivity ].
  exfalso; subst a b; simpl in H1, Hcmp2, Hs2.
  apply fst_same_sym_iff in Hs2; simpl in Hs2.
  destruct Hs2 as (Hn2, Ht2).
  simpl in Hcmp1.
  remember (R_frac nz.[j1]) as zi eqn:Hzi.
  symmetry in Hzi; apply eq_digit_eq in Hzi.
  destruct (Digit.dec zi) as [H2| H2]; rewrite H2 in Hzi; clear zi H2.
   Focus 2.
bbb.

Theorem R_lt_add_compat_r : ∀ x y z, (x < y)%R → (x + z < y + z)%R.
Proof.
intros x y z Hxy.
unfold R_lt in Hxy; unfold R_lt.
unfold R_compare in Hxy; unfold R_compare.
remember (R_norm x) as nx eqn:Hnx.
remember (R_norm y) as ny eqn:Hny.
remember (R_norm (x + z)) as nxz eqn:Hnxz.
remember (R_norm (y + z)) as nyz eqn:Hnyz.
remember (R_int nx ?= R_int ny)%Z as cmp1 eqn:Hcmp1.
remember (R_int nxz ?= R_int nyz)%Z as cmp2 eqn:Hcmp2.
symmetry in Hcmp1, Hcmp2.
remember (fst_same (R_frac nx) (- R_frac ny) 0) as s1 eqn:Hs1.
remember (fst_same (R_frac nxz) (- R_frac nyz) 0) as s2 eqn:Hs2.
destruct cmp1; [ idtac | clear Hxy | discriminate Hxy ].
 apply Z.compare_eq in Hcmp1.
 destruct s1 as [j1| ]; [| discriminate Hxy ].
 destruct (Digit.dec (R_frac nx .[ j1])) as [H1| H1].
  discriminate Hxy.

  clear Hxy.
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, Ht1).
  rewrite H1 in Ht1; rename H1 into Hnx1; rename Ht1 into Hny1.
  apply Digit.opp_sym in Hny1; rewrite Digit.opp_0 in Hny1.
bbb.
  destruct cmp2; [ idtac | reflexivity | exfalso ].
   apply Z.compare_eq in Hcmp2.
   destruct s2 as [j2| ]; [ idtac | exfalso ].
    destruct (Digit.dec (R_frac nxz .[ j2])) as [H2| H2].
     2: reflexivity.
     exfalso.
     apply fst_same_sym_iff in Hs2; simpl in Hs2.
     destruct Hs2 as (Hn2, Ht2).
     rewrite H2 in Ht2; rename H2 into Hnxz2; rename Ht2 into Hnyz2.
     apply Digit.opp_sym in Hnyz2; rewrite Digit.opp_1 in Hnyz2.
     subst; simpl in *.
     remember (R_frac x) as xf eqn:Hxf.
     remember (R_frac y) as yf eqn:Hyf.
     remember (R_frac z) as zf eqn:Hzf.
     remember (R_int x) as xi eqn:Hxi.
     remember (R_int y) as yi eqn:Hyi.
     remember (R_int z) as zi eqn:Hzi.
     move xf after zf; move yf after zf.
     move xi before zf; move yi before xi; move zi before yi.
     move Hxf after Hyf; move Hxi before Hzf; move Hyi before Hxi.
     move Hzi before Hyi; move Hcmp1 after Hcmp2; move Hnxz2 after Hnyz2.
     move Hnx1 after Hnxz2; move Hny1 after Hnxz2.
     unfold I_add_i in Hnxz2; simpl in Hnxz2.
     unfold I_add_i in Hnxz2; simpl in Hnxz2.
     rewrite Digit.add_0_r in Hnxz2.
     unfold I_add_i in Hnyz2; simpl in Hnyz2.
     unfold I_add_i in Hnyz2; simpl in Hnyz2.
     rewrite Digit.add_0_r in Hnyz2.
     unfold I_add_i in Hnx1; simpl in Hnx1.
     rewrite Digit.add_0_r in Hnx1.
     unfold I_add_i in Hny1; simpl in Hny1.
     rewrite Digit.add_0_r in Hny1.
     rewrite <- Z.add_assoc, Z.add_comm, Z.add_assoc in Hcmp2.
     symmetry in Hcmp2.
     rewrite <- Z.add_assoc, Z.add_comm, Z.add_assoc in Hcmp2.
     symmetry in Hcmp2.
     apply Z.add_cancel_r in Hcmp2.
     destruct (I_eq_dec xf 1) as [H1| H1].
bbb.
(* --> revoir ce lien entre I_eqs et I_eq_ext ; il faut une seule
   définition et peut-être le fait que I_eqs x y est équivalent à
   ∀ i, (x.[i] = y.[i])%D
 *)

      destruct (I_eq_dec xf 0) as [H2| H2].
       Focus 2.
       rewrite H1 in H2; apply H2; symmetry; apply I_0_eq_1.

       unfold I_eq, I_eq_ext in H1, H2; simpl in H1, H2.

Unfocus.
Focus 2.bbb.
      unfold I_eq, I_eq_ext in H1; simpl in H1.

SearchAbout (0 = 1)%I.
      apply I_eqs_eq_ext in H1.
      unfold I_eqs, I_compare in H1; simpl in H1.

      Focus 2.
      remember H1 as H; clear HeqH.
      apply carry_0_0_r in H.
      rewrite H, b2z_0, Z.add_0_r in Hcmp1.
bbb.
     destruct (I_eqs_dec xf 1) as [H1| H1].
      apply I_eqs_eq_ext in H1; unfold I_eq_ext in H1; simpl in H1.
      rewrite H1 in Hnx1, Hnxz2.
       apply carry_0_0_r.
       intros H; apply H1.
       apply I_eqs_eq.
bbb.
unfold carry in *; simpl in *.
     remember (carry xf 0 0) as c1 eqn:Hc1.
     remember (carry yf 0 0) as c2 eqn:Hc2.
     remember (carry xf zf 0) as c3 eqn:Hc3.
     remember (carry yf zf 0) as c4 eqn:Hc4.
bbb.
     destruct (lt_eq_lt_dec j1 j2) as [[H1| H1]| H1].
      remember H1 as H; clear HeqH.
      apply Hn2 in H; rewrite Digit.opp_involutive in H.
      unfold I_add_i in H; simpl in H.
      rewrite Digit.add_0_r in H.
      unfold I_add_i in H; simpl in H.
bbb.

   Focus 2.
   apply Z.compare_gt_iff in Hc2.
   rewrite Hnyz, Hnxz in Hc2.
   unfold R_norm in Hc2; simpl in Hc2.
   rewrite Hnx, Hny in Hc1; simpl in Hc1.
   do 4 rewrite <- Z.add_assoc in Hc2.
   rewrite Z.add_comm in Hc2; apply Z.lt_gt in Hc2.
   rewrite Z.add_comm in Hc2; apply Z.gt_lt in Hc2.
   do 4 rewrite <- Z.add_assoc in Hc2.
   apply Z.add_lt_mono_l in Hc2.
   do 2 rewrite Z.add_assoc in Hc2.
   rewrite Z.add_shuffle0, <- Z.add_assoc in Hc2.


   rewrite Hc1 in Hc2.
   rewrite Hny in 

SearchAbout (_ = 1)%D.
  remember Hnx1 as H; clear HeqH.
Focus 1.
  eapply I_eq_neq_prop in H; [ idtac | idtac | eassumption ].
bbb.


destruct c1, c2; try reflexivity.
 apply Z.compare_eq in Hc2.
 destruct s1 as [j1| ].
  apply fst_same_sym_iff in Hs1; simpl in Hs1.
  destruct Hs1 as (Hn1, Ht1).
  destruct s2 as [j2| ].
   apply fst_same_sym_iff in Hs2; simpl in Hs2.
   destruct Hs2 as (Hn2, Ht2).
   destruct (Digit.dec (R_frac nx .[ j1])) as [H1| H1].
    destruct (Digit.dec (R_frac nxz .[ j2])) as [H2| H2]; auto; exfalso.
    subst; simpl in *.
    rewrite H2 in Ht2.
    apply Digit.opp_sym in Ht2; rewrite Digit.opp_0 in Ht2.
    rewrite H1 in Ht1.
    apply Digit.opp_sym in Ht1; rewrite Digit.opp_1 in Ht1.
    unfold I_add_i in H1; simpl in H1.
    unfold I_add_i in H2; simpl in H2.
    unfold I_add_i in Ht1; simpl in Ht1.
    unfold I_add_i in Ht2; simpl in Ht2.
    rewrite Digit.add_0_r in H1, H2, Ht1, Ht2.
    unfold I_add_i in H2; simpl in H2.
    unfold I_add_i in Ht2; simpl in Ht2.
    remember (R_frac x) as xf eqn:Hxf.
    remember (R_frac y) as yf eqn:Hyf.
    remember (R_frac z) as zf eqn:Hzf.
    remember (R_int x) as xi eqn:Hxi.
    remember (R_int y) as yi eqn:Hyi.
    remember (R_int z) as zi eqn:Hzi.
    move Hyf before Hxf; move yf before xf; move zf before yf.
    move xi before zf; move yi before xi; move zi before yi.
    move Hxi before Hzf; move Hyi before Hxi; move Hzi before Hyi.
    move H1 after H2; move Hc1 after Hc2.
    do 4 rewrite <- Z.add_assoc in Hc2.
    rewrite Z.add_comm in Hc2; symmetry in Hc2.
    rewrite Z.add_comm in Hc2; symmetry in Hc2.
    do 4 rewrite <- Z.add_assoc in Hc2.
    apply Z.add_reg_l in Hc2.
    rewrite Z.add_comm in Hc2; symmetry in Hc2.
    rewrite Z.add_comm in Hc2; symmetry in Hc2.
    move Ht1 before H1; move Ht2 before H2.
bbb.
*)

Theorem R_compare_add_compat_r : ∀ x y z, (x ?= y)%R = (x + z ?= y + z)%R.
Proof.
intros x y z.
remember (x ?= y)%R as c1 eqn:Hc1.
remember (x + z ?= y + z)%R as c2 eqn:Hc2.
symmetry in Hc1, Hc2.
destruct c1.
 apply R_compare_eq in Hc1.
 destruct c2; [ reflexivity | exfalso | exfalso ].
   apply R_compare_lt in Hc2.
   rewrite Hc1 in Hc2.
   revert Hc2; apply R_lt_irrefl.

   apply R_compare_gt in Hc2.
   rewrite Hc1 in Hc2.
   apply R_gt_lt_iff in Hc2.
   revert Hc2; apply R_lt_irrefl.

  apply R_compare_lt in Hc1.
  destruct c2; [ exfalso | reflexivity | exfalso ].
   apply R_compare_eq in Hc2.
   apply R_add_reg_r in Hc2.
   rewrite Hc2 in Hc1.
   revert Hc1; apply R_lt_irrefl.

   apply R_compare_gt in Hc2.
   apply R_gt_lt_iff in Hc2.
   apply R_lt_nle in Hc2.
   apply Hc2; clear Hc2.
   bbb.
apply R_lt_add_compat_r.

   Focus 2.
   apply R_compare_gt in Hc1.
   destruct c2; [ exfalso | exfalso | reflexivity ].
    apply R_compare_eq in Hc2.
    apply R_add_reg_r in Hc2.
    rewrite Hc2 in Hc1.
    apply R_gt_lt_iff in Hc1.
    revert Hc1; apply R_lt_irrefl.

    apply R_compare_lt in Hc2.


bbb.

SearchAbout R_compare.

Theorem R_lt_sub_lt_add_l : ∀ x y z, (x - y < z)%R ↔ (x < y + z)%R.
Proof.
intros x y z.
split; intros Hxyz.
SearchAbout I_le.
bbb.

Theorem R_le_pos_lt_compat : ∀ x y z, (x ≤ y)%R → (z > 0)%R → (x < y + z)%R.
Proof.
intros x y z Hxy Hz.
eapply R_le_lt_trans; [ eassumption | idtac ].
SearchAbout (_ < _ + _)%Z.
bbb.

Theorem R_cauchy_sequence_bounded : ∀ u,
  R_cauchy_sequence u → ∃ m, ∀ n, (R_abs (u n) < m)%R.
Proof.
intros u Hc.
pose proof R_lt_0_1 as H.
apply R_gt_lt_iff in H.
apply Hc in H.
destruct H as (N, HN).
exists (R_max (R_max_abs_seq_upto u N) (R_abs (u (S N))) + 1)%R.
intros n.
destruct (le_dec n N) as [H1 | H1].
bbb.

(* to be completed *)
Theorem zzz : ∀ u, cauchy_sequence u → ∃ r, converges_to u r.
Proof.
intros u Hc.
unfold cauchy_sequence in Hc.
unfold converges_to.
(*
bbb.
*)

(*
apply functional_choice in Hc.
destruct Hc as (f, Hf).
bbb.
*)
