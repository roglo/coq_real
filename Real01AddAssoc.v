(* Reals between 0 and 1; associativity of addition *)

Require Import Utf8 Arith NPeano Psatz.
Require Import Misc FracReal.

Theorem eq_add_series_18_eq_9 {r : radix} : ∀ x y n,
  (∀ k, freal_add_series x y (n + k + 1) = 2 * (rad - 1))
  → (∀ k, fd2n x (n + k + 1) = rad - 1) ∧ (∀ k, fd2n y (n + k + 1) = rad - 1).
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros Hxy.
split.
-intros.
 specialize (Hxy k).
 unfold freal_add_series, sequence_add in Hxy.
 specialize (digit_lt_radix (freal x (n + k + 1))) as H1.
 specialize (digit_lt_radix (freal y (n + k + 1))) as H2.
 unfold fd2n in Hxy |-*; lia.
-intros.
 specialize (Hxy k).
 unfold freal_add_series, sequence_add in Hxy.
 specialize (digit_lt_radix (freal x (n + k + 1))) as H1.
 specialize (digit_lt_radix (freal y (n + k + 1))) as H2.
 unfold fd2n in Hxy |-*; lia.
Qed.

Theorem eq_add_series_eq_l {r : radix} : ∀ x y n a,
  (∀ k, freal_add_series x y (n + k + 1) = a)
  → (∀ k, fd2n x (n + k + 1) = a)
  → ∀ k, fd2n y (n + k + 1) = 0.
Proof.
intros * Hxy Hx *.
specialize (Hxy k).
specialize (Hx k).
unfold freal_add_series, sequence_add in Hxy; lia.
Qed.

Theorem eq_add_series_eq_r {r : radix} : ∀ x y n a,
  (∀ k, freal_add_series x y (n + k + 1) = a)
  → (∀ k, fd2n y (n + k + 1) = a)
  → ∀ k, fd2n x (n + k + 1) = 0.
Proof.
intros * Hxy Hx *.
specialize (Hxy k).
specialize (Hx k).
unfold freal_add_series, sequence_add in Hxy; lia.
Qed.

Theorem add_assoc_case_11_1 {r : radix } : ∀ x y z i,
  (∀ k, freal_add_series z (freal_unorm_add y x) (i + k + 1) = rad - 1)
  → (∀ k, freal_add_series y z (i + k + 1) = rad - 1)
  → (∀ k, freal_add_series y x (i + k + 1) = 2 * (rad - 1))
  → False.
Proof.
intros * H2 H3 H4.
specialize (eq_add_series_18_eq_9 _ _ _ H4) as Hxy.
destruct Hxy as (Hy, Hx).
specialize (eq_add_series_eq_l _ _ _ _ H3 Hy) as Hz.
unfold freal_unorm_add in H2.
unfold freal_add_to_seq in H2.
unfold freal_add_series at 1 in H2.
unfold sequence_add in H2; simpl in H2.
unfold fd2n at 2 in H2; simpl in H2.
remember (freal_add_series y x) as yx eqn:Hyx.
assert (H5 : ∀ k, d2n (propagate_carries yx) (i + 1 + k) = rad - 1). {
  intros k.
  specialize (H2 k).
  rewrite Hz in H2.
  now replace (i + k + 1) with (i + 1 + k) in H2 by flia.
}
apply not_propagate_carries_all_9 in H5; [ easy | ].
intros k; subst yx; apply freal_add_series_le_twice_pred.
Qed.

Theorem add_assoc_case_11 {r : radix} : ∀ x y z i,
  (∀ k, freal_add_series x (freal_unorm_add y z) (i + k + 1) = rad - 1)
  → (∀ k, freal_add_series z (freal_unorm_add y x) (i + k + 1) = rad - 1)
  → (freal_add_series x (freal_unorm_add y z) i + 1) mod rad =
     (freal_add_series z (freal_unorm_add y x) i + 1) mod rad.
Proof.
intros *.
specialize radix_ge_2 as Hr.
intros H1 H2.
rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
rewrite <- Nat.add_mod_idemp_l; [ symmetry | easy ].
f_equal; f_equal.
unfold freal_add_series, sequence_add.
unfold freal_unorm_add, freal_add_to_seq, fd2n; simpl.
unfold propagate_carries.
remember (rad * (i + 3)) as n1 eqn:Hn1.
remember (n1 - i - 1) as s1 eqn:Hs1.
move s1 before n1.
assert (Hr2s1 : 2 ≤ rad ^ s1). {
  destruct s1.
  -rewrite Hn1 in Hs1.
   destruct rad; [ easy | simpl in Hs1; flia Hs1 ].
  -simpl.
   replace 2 with (2 * 1) by flia.
   apply Nat.mul_le_mono; [ easy | ].
   now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
destruct (LPO_fst (A_ge_1 (freal_add_series y z) i)) as [H3| H3].
-simpl.
 apply A_ge_1_add_all_true_if in H3.
 destruct (LPO_fst (A_ge_1 (freal_add_series y x) i)) as [H4| H4].
 +simpl.
  apply A_ge_1_add_all_true_if in H4.
  *rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
   rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
   unfold freal_add_series at 1 3.
   unfold sequence_add, fd2n.
   do 6 rewrite Nat.add_assoc.
   do 3 rewrite fold_fd2n.
   replace (fd2n z i + fd2n y i + fd2n x i) with
       (fd2n x i + fd2n y i + fd2n z i) by flia.
   rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
   rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
   f_equal; f_equal.
   destruct H3 as [H3| [H3| H3]].
  --rewrite nA_all_9; [ | intros; apply H3 ].
    destruct H4 as [H4| [H4| H4]].
   ++rewrite nA_all_9; [ easy | intros; apply H4 ].
   ++exfalso; now apply (add_assoc_case_11_1 x y z i).
   ++destruct H4 as (j & Hjbef & Hjwhi & Hjaft).
     rewrite <- Hs1.
     rewrite Nat.div_small; [ | flia Hr2s1 ].
     rewrite (nA_9_8_all_18 j); [ | easy | easy | easy ].
     rewrite <- Hs1.
     destruct (le_dec (i + j + 1) (n1 - 1)) as [H4| H4].
    **rewrite Nat.div_small; [ easy | flia Hr2s1 ].
    **rewrite Nat.div_small; [ easy | flia Hr2s1 ].
  --rewrite nA_all_18; [ | apply H3 ].
    rewrite <- Hs1.
    rewrite Nat_div_less_small; [ | flia Hr2s1 ].
    destruct H4 as [H4| [H4| H4]].
   ++exfalso; now apply (add_assoc_case_11_1 z y x i).
   ++rewrite nA_all_18; [ | apply H4 ].
     rewrite <- Hs1.
     rewrite Nat_div_less_small; [ easy | flia Hr2s1 ].
   ++exfalso.
     destruct H4 as (j2 & H2bef & H2whi & H2aft).
     specialize (eq_add_series_18_eq_9 _ _ _ H3) as Hxy.
     destruct Hxy as (Hy, Hx).
     unfold freal_add_series, sequence_add in H2whi.
     rewrite Hy in H2whi; flia Hr H2whi.
  --destruct H3 as (j1 & H1bef & H1whi & H1aft).
    rewrite (nA_9_8_all_18 j1); [ | easy | easy | easy ].
    rewrite <- Hs1.
    rewrite Nat.div_small.
   ++destruct H4 as [H4| [H4| H4]].
    **rewrite nA_all_9; [ | intros; apply H4 ].
      rewrite <- Hs1.
      rewrite Nat.div_small; [ easy | flia Hr2s1 ].
    **exfalso.
      apply eq_add_series_18_eq_9 in H4.
      destruct H4 as (Hy & Hx).
      unfold freal_add_series, sequence_add in H1whi.
      rewrite Hy in H1whi; flia Hr H1whi.
    **destruct H4 as (j2 & H2bef & H2whi & H2aft).
      rewrite (nA_9_8_all_18 j2); [ | easy | easy | easy ].
      rewrite <- Hs1.
      destruct (le_dec (i + j2 + 1) (n1 - 1)) as [H3| H3].
    ---rewrite Nat.div_small; [ easy | flia Hr2s1 ].
    ---rewrite Nat.div_small; [ easy | flia Hr2s1 ].
   ++destruct (le_dec (i + j1 + 1) (n1 - 1)); flia Hr2s1.
  *intros; apply freal_add_series_le_twice_pred.
 +destruct H4 as (j2 & Hjj2 & Hj2); simpl.
  apply A_ge_1_false_iff in Hj2.
  remember (rad * (i + j2 + 3)) as n2 eqn:Hn2.
  remember (n2 - i - 1) as s2 eqn:Hs2.
  move s2 before n2.
  rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
  rewrite Nat.add_mod_idemp_r; [ symmetry | easy ].
  unfold freal_add_series at 1 3.
  unfold sequence_add, fd2n.
  do 5 rewrite Nat.add_assoc.
  do 3 rewrite fold_fd2n.
  replace (fd2n z i + fd2n y i + fd2n x i) with
    (fd2n x i + fd2n y i + fd2n z i) by flia.
  rewrite <- Nat.add_assoc.
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  rewrite <- Nat.add_mod_idemp_r; [ symmetry | easy ].
  f_equal; f_equal.
  destruct H3 as [H3| [H3| H3]].
  *rewrite nA_all_9; [ | intros; apply H3 ].
   rewrite <- Hs1.
   rewrite Nat.div_small; [ | flia Hr2s1 ].
   rewrite Nat.add_0_r.
   destruct (lt_dec (nA i n2 (freal_add_series y x)) (rad ^ s2)) as [H4| H4].
  --exfalso.
    rewrite Nat.mod_small in Hj2; [ | easy ].
    assert (Hx : ∀ k, fd2n x (i + k + 1) = rad - 1). {
      clear - H1 H3.
      specialize radix_ge_2 as Hr.
      intros.
      specialize (H1 k) as H5.
      unfold freal_add_series, sequence_add in H5.
      unfold freal_unorm_add in H5.
      unfold fd2n at 2 in H5; simpl in H5.
      unfold freal_add_to_seq in H5.
      unfold propagate_carries in H5.
      remember (freal_add_series y z) as yz eqn:Hyz.
      rewrite H3 in H5.
      rewrite Nat.sub_add in H5; [ | easy ].
      destruct (LPO_fst (A_ge_1 yz (i + k + 1))) as [H6| H6].
      -simpl in H5.
       rewrite nA_all_9 in H5; cycle 1.
       +intros j Hj.
        replace (i + k + 1 + j) with (i + (k + 1 + j)) by flia.
        apply H3.
       +rewrite Nat.div_small in H5; cycle 1.
        *apply Nat.sub_lt; [ | apply Nat.lt_0_1 ].
         now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
        *rewrite Nat.add_0_r in H5.
         rewrite Nat.mod_same in H5; [ | easy ].
         now rewrite Nat.add_0_r in H5.
      -destruct H6 as (j3 & Hjj3 & Hj3); simpl in H5.
       apply A_ge_1_false_iff in Hj3.
       remember (rad * (i + k + 1 + j3 + 3)) as n3 eqn:Hn3.
       remember (n3 - (i + k + 1) - 1) as s3 eqn:Hs3.
       move s3 before n3.
       rewrite nA_all_9 in Hj3; cycle 1.
       +intros.
        replace (i + k + 1 + j) with (i + (k + 1 + j)) by flia.
        apply H3.
       +rewrite Nat.mod_small in Hj3; cycle 1.
        *rewrite <- Hs3.
         apply Nat.sub_lt; [ | apply Nat.lt_0_1 ].
         now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
        *exfalso.
         apply Nat.nle_gt in Hj3; apply Hj3; clear Hj3.
         rewrite <- Hs3.
         rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
         rewrite <- Nat.pow_add_r.
         replace (S j3 + (s3 - S j3)) with s3; cycle 1.
        --rewrite Hs3, Hn3.
          destruct rad; [ easy | simpl; flia ].
        --apply Nat.sub_le_mono_l.
          now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
    }
    apply Nat.nle_gt in Hj2; apply Hj2; clear Hj2.
    apply le_trans with (m := nA i n2 (fd2n x)).
   ++rewrite nA_all_9; [ | intros j Hj; apply Hx ].
     rewrite <- Hs2.

...

Theorem freal_unorm_add_assoc {r : radix} : ∀ x y z,
  freal_norm_eq
    (freal_unorm_add x (freal_unorm_add y z))
    (freal_unorm_add (freal_unorm_add x y) z).
Proof.
intros.
specialize radix_ge_2 as Hr.
specialize (freal_unorm_add_comm (freal_unorm_add x y) z) as H.
rewrite H; clear H.
specialize (freal_unorm_add_comm x y) as H.
rewrite H; clear H.
unfold freal_norm_eq.
intros i.
unfold freal_unorm_add at 1 3.
unfold fd2n; simpl.
unfold freal_add_to_seq.
remember (freal_unorm_add y z) as yz eqn:Hyz.
remember (freal_unorm_add y x) as yx eqn:Hyx.
move yx before yz.
move Hyx before Hyz.
remember (freal_add_series x yz) as x_yz eqn:Hxyz.
remember (freal_add_series z yx) as z_yx eqn:Hzyx.
move z_yx before x_yz.
unfold propagate_carries.
destruct (LPO_fst (A_ge_1 x_yz i)) as [H1| H1].
-simpl.
 remember (rad * (i + 3)) as n1 eqn:Hn1.
 remember (n1 - i - 1) as s1 eqn:Hs1.
 move s1 before n1.
 assert (Hr2s1 : 2 ≤ rad ^ s1). {
   destruct s1.
   -rewrite Hn1 in Hs1.
    destruct rad; [ easy | simpl in Hs1; flia Hs1 ].
   -simpl.
    replace 2 with (2 * 1) by flia.
    apply Nat.mul_le_mono; [ easy | ].
    now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
 }
 apply A_ge_1_add_all_true_if in H1.
 +destruct (LPO_fst (A_ge_1 z_yx i)) as [H2| H2].
  *simpl.
   apply A_ge_1_add_all_true_if in H2.
  --destruct H1 as [H1| [H1| H1]].
   ++rewrite Nat.div_small.
    **rewrite Nat.add_0_r.
      destruct H2 as [H2| [H2| H2]].
    ---rewrite Nat.div_small.
     +++rewrite Nat.add_0_r.
        (* 11 *)
...
        subst; now apply add_assoc_case_11.
     +++rewrite nA_all_9; [ rewrite <- Hs1; flia Hr2s1 | easy ].
    ---rewrite Nat_div_less_small.
     +++(* 12 *)
        ...
     +++rewrite nA_all_18; [ rewrite <- Hs1; flia Hr2s1 | easy ].
    ---destruct H2 as (j2 & H2bef & H2whi & H2aft).
       rewrite Nat.div_small.
     +++rewrite Nat.add_0_r.
        (* 13 *)
        ...
     +++rewrite (nA_9_8_all_18 j2); [ | easy | easy | easy ].
        rewrite <- Hs1.
        destruct (le_dec (i + j2 + 1) (n1 - 1)); flia Hr2s1.
    **rewrite nA_all_9; [ rewrite <- Hs1; flia Hr2s1 | easy ].
   ++rewrite Nat_div_less_small.
    **destruct H2 as [H2| [H2| H2]].
    ---rewrite Nat.div_small.
     +++rewrite Nat.add_0_r.
        (* 21, symmetric of 12 *)
        ...
     +++rewrite nA_all_9; [ rewrite <- Hs1; flia Hr2s1 | easy ].
    ---rewrite Nat_div_less_small.
     +++(* 22 *)
        ...
     +++rewrite nA_all_18; [ rewrite <- Hs1; flia Hr2s1 | easy ].
    ---destruct H2 as (j2 & H2bef & H2whi & H2aft).
       rewrite Nat.div_small.
     +++rewrite Nat.add_0_r.
        (* 23 *)
        ...
     +++rewrite (nA_9_8_all_18 j2); [ | easy | easy | easy ].
        rewrite <- Hs1.
        destruct (le_dec (i + j2 + 1) (n1 - 1)); flia Hr2s1.
    **rewrite nA_all_18; [ rewrite <- Hs1; flia Hr2s1 | easy ].
   ++destruct H1 as (j1 & H1bef & H1whi & H1aft).
     rewrite Nat.div_small.
    **rewrite Nat.add_0_r.
      destruct H2 as [H2| [H2| H2]].
    ---rewrite Nat.div_small.
     +++rewrite Nat.add_0_r.
        (* 31, symmetric of 13 *)
        ...
     +++rewrite nA_all_9; [ rewrite <- Hs1; flia Hr2s1 | easy ].
    ---rewrite Nat_div_less_small.
     +++(* 32, symmetric of 23 *)
        ...
     +++rewrite nA_all_18; [ rewrite <- Hs1; flia Hr2s1 | easy ].
    ---destruct H2 as (j2 & H2bef & H2whi & H2aft).
       rewrite Nat.div_small.
     +++rewrite Nat.add_0_r.
        (* 33 *)
        ...
     +++rewrite (nA_9_8_all_18 j2); [ | easy | easy | easy ].
        rewrite <- Hs1.
        destruct (le_dec (i + j2 + 1) (n1 - 1)); flia Hr2s1.
    **rewrite (nA_9_8_all_18 j1); [ | easy | easy | easy ].
      rewrite <- Hs1.
      destruct (le_dec (i + j1 + 1) (n1 - 1)); flia Hr2s1.
  --intros k; rewrite Hzyx.
    apply freal_add_series_le_twice_pred.
  *destruct H2 as (j2 & Hjj2 & Hj2); simpl.
   destruct H1 as [H1| [H1| H1]].
  --...
  --...
  --...
 +intros k; rewrite Hxyz.
  apply freal_add_series_le_twice_pred.
-destruct H1 as (j1 & Hjj1 & Hj1); simpl.
 destruct (LPO_fst (A_ge_1 z_yx i)) as [H2| H2].
 +simpl.
  ...
 +destruct H2 as (j2 & Hjj2 & Hj2); simpl.
  ...
Qed.
