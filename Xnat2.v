(* Natural numbers in any radix; second version; without proofs *)
(* Can be regarded as polynomials with natural number coefficients. *)

(* Implemented using lists of nat. *)
(* No constraints of digits having to be less than radix;
   to build a number whose digits are less than radix, use normalization
   by the function xnat_norm *)

Require Import Utf8 Arith Psatz Misc.
Require List.
Import List.ListNotations.
Open Scope list_scope.

Class radix := { rad : nat }.

Definition radix_2 := {| rad := 2 |}.
Definition radix_10 := {| rad := 10 |}.

Record xnat := xn { xnatv : list nat }.

Fixpoint move_carry_end {r : radix} iter carry :=
  match iter with
  | 0 => []
  | S i =>
      if zerop carry then []
      else carry mod rad :: move_carry_end i (carry / rad)
  end.

Fixpoint move_carry {r : radix} carry al :=
  match al with
  | [] => move_carry_end (S carry) carry
  | a :: al' => (carry + a) mod rad :: move_carry ((carry + a) / rad) al'
  end.

Definition list_of_nat {r : radix} carry n :=
  if zerop n then [] else move_carry carry [n].
Definition nat_of_list {r : radix} accu al :=
  List.fold_right (λ a accu, accu * rad + a) accu al.

Definition xnat_of_nat {r : radix} n := xn (list_of_nat 0 n).
Definition nat_of_xnat {r : radix} a := nat_of_list 0 (xnatv a).

Lemma nat_of_list_move_end {r : radix} : ∀ iter n, 2 ≤ rad →
  n < iter
  → nat_of_list 0 (move_carry_end iter n) = n.
Proof.
intros * Hr Hni.
revert n Hni.
induction iter; intros; [ now apply Nat.nlt_0_r in Hni | simpl ].
destruct (zerop n) as [Hn| Hn]; [ easy | simpl ].
rewrite IHiter.
 rewrite Nat.mul_comm; symmetry.
 apply Nat.div_mod; lia.

 apply lt_n_Sm_le in Hni.
 destruct rad as [| m]; [ lia | ].
 destruct m as [| m]; [ lia | ].
 destruct iter; [ lia | ].
 eapply lt_le_trans; [ | eassumption ].
 destruct n; [ easy | clear ].
 apply Nat.div_lt; lia.
Qed.

Lemma nat_of_list_list_of_nat {r : radix} : 2 ≤ rad →
  ∀ n, nat_of_list 0 (list_of_nat 0 n) = n.
Proof.
intros Hr *.
unfold list_of_nat.
destruct (zerop n) as [Hn| Hn]; [ easy | simpl ].
destruct (zerop (n / rad)) as [Hs| Hs].
 apply Nat.div_small_iff in Hs; [ | lia ].
 now rewrite Nat.mod_small.

 simpl.
 rewrite nat_of_list_move_end; [ | easy | now apply Nat.div_lt ].
 remember (n / rad) as nr eqn:Hnr.
 replace (nr / rad * rad) with (rad * (nr / rad)) by lia.
 rewrite <- Nat.div_mod; [ subst nr | lia ].
 rewrite Nat.mul_comm; symmetry.
 apply Nat.div_mod; lia.
Qed.

Fixpoint list_remove_trailing_0s al :=
  match al with
  | [] => []
  | 0 :: al' =>
      match list_remove_trailing_0s al' with
      | [] => []
      | al'' => 0 :: al''
      end
  | a :: al' => a :: list_remove_trailing_0s al'
  end.

Definition list_norm_with_carry {r : radix} c al :=
  list_remove_trailing_0s (move_carry c al).

Definition list_norm {r : radix} := list_norm_with_carry 0.

Definition xnat_norm {r : radix} a := xn (list_norm (xnatv a)).

(*
Lemma nat_of_list_mul {r : radix} : ∀ al,
  nat_of_list 0 al * rad = nat_of_list 0 (0 :: al).
Proof.
intros; simpl.
now rewrite Nat.add_0_r.
Qed.

Lemma nat_of_list_removed_trailing_0s_mul {r : radix} : ∀ a al,
  nat_of_list 0 (list_remove_trailing_0s al) * rad + a =
  nat_of_list 0 (list_remove_trailing_0s (a :: al)).
Proof.
intros; simpl.
remember (list_remove_trailing_0s al) as al' eqn:Hal.
symmetry in Hal.
now destruct a; [ destruct al' | ].
Qed.

Lemma list_norm_0 {r : radix} : list_norm [0] = [].
Proof.
intros.
unfold list_norm, list_norm_with_carry.
specialize (move_carry_0_rep_0 1) as H.
remember move_carry as f; simpl in H; subst f.
now rewrite H.
Qed.
*)

Lemma eq_list_rem_trail_nil : ∀ al,
  list_remove_trailing_0s al = [] ↔ al = List.repeat 0 (length al).
Proof.
intros *.
split; intros Ha.
 induction al as [| a]; [ easy | simpl in Ha; simpl ].
 destruct a; [ | easy ].
 remember (list_remove_trailing_0s al) as al' eqn:Hal'.
 destruct al' as [| a']; [ now f_equal; apply IHal | easy ].

 induction al as [| a]; [ easy | simpl in Ha; simpl ].
 injection Ha; clear Ha; intros Hal Ha; subst a.
 now rewrite IHal.
Qed.

Lemma list_rem_trail_repeat_0 : ∀ n,
  list_remove_trailing_0s (List.repeat 0 n) = [].
Proof.
intros.
apply eq_list_rem_trail_nil.
now rewrite List.repeat_length.
Qed.

(*
Lemma eq_nat_of_list_0_0 {r : radix} : ∀ al, 0 < rad →
  nat_of_list 0 al = 0 ↔ al = List.repeat 0 (length al).
Proof.
intros * Hr.
split; intros Hal.
 induction al as [| a]; [ easy | simpl in Hal; simpl ].
 apply Nat.eq_add_0 in Hal.
 destruct Hal as (Ha, Hal); subst a; f_equal.
 apply Nat.eq_mul_0 in Ha.
 destruct Ha as [Ha| Ha]; [ now apply IHal | lia ].

 induction al as [| a]; [ easy | simpl in Hal; simpl ].
 injection Hal; clear Hal; intros Hal Ha; subst a.
 apply IHal in Hal.
 now rewrite Hal.
Qed.

Lemma eq_nat_of_list_0 {r : radix} : ∀ c al, rad ≠ 0 →
  nat_of_list c al = 0 → c = 0 ∧ al = List.repeat 0 (length al).
Proof.
intros * Hr Hn.
revert c Hn.
induction al as [| a1]; intros; [ easy | ].
simpl in Hn.
apply Nat.eq_add_0 in Hn.
destruct Hn as (Hal, Ha1); subst a1.
apply Nat.eq_mul_0 in Hal.
destruct Hal as [Hal| ]; [ | easy ].
specialize (IHal c Hal).
now split; [ | simpl; f_equal ].
Qed.

Lemma list_norm_cons_0 {r : radix} : ∀ al,
  list_norm al = [] → list_norm (0 :: al) = [].
Proof.
intros * Hal.
destruct (zerop rad) as [Hr| Hr].
 unfold list_norm, list_norm_with_carry in Hal.
 unfold list_norm, list_norm_with_carry; simpl; rewrite Hr; simpl.
 now rewrite Hal.

 unfold list_norm in Hal.
 apply eq_list_rem_trail_nil in Hal.
 apply eq_list_rem_trail_nil; simpl.
 rewrite Nat.mod_0_l; [ | lia ].
 rewrite Nat.div_0_l; [ | lia ].
 now f_equal.
Qed.
*)

Lemma list_rem_trail_rep_0 : ∀ al n,
  list_remove_trailing_0s (al ++ List.repeat 0 n) = list_remove_trailing_0s al.
Proof.
intros.
revert al.
induction n; intros; [ now rewrite List.app_nil_r | simpl ].
rewrite List_cons_comm_app, List.app_assoc.
rewrite IHn; clear.
induction al as [| a]; [ easy | now simpl; rewrite IHal ].
Qed.

Lemma list_rem_trail_iff : ∀ al bl,
  list_remove_trailing_0s al = bl
  ↔ (al = bl ++ List.repeat 0 (length al - length bl)) ∧
     (bl = [] ∨ List.last bl 0 ≠ 0).
Proof.
intros *.
split.
 intros Hb.
 split.
  revert bl Hb.
  induction al as [| a]; intros; [ now subst bl | ].
  subst bl; simpl.
  remember (list_remove_trailing_0s al) as cl eqn:Hcl in |-*.
  symmetry in Hcl.
  rewrite (IHal cl); [ | easy ].
  destruct a; simpl.
   destruct cl; simpl.
    rewrite Nat.sub_0_r.
    now rewrite List.repeat_length.

    rewrite List.app_length, Nat.add_comm, Nat.add_sub.
    now rewrite List.repeat_length.

   rewrite List.app_length, Nat.add_comm, Nat.add_sub.
   now rewrite List.repeat_length.

  revert al Hb.
  induction bl as [| b]; intros; [ now left | right ].
  destruct al as [| a]; [ easy | ].
  simpl in Hb.
  destruct a.
   remember (list_remove_trailing_0s al) as cl eqn:Hcl.
   symmetry in Hcl.
   destruct cl as [| c]; [ easy | ].
   injection Hb; clear Hb; intros Hbl Hb; subst b bl.
   specialize (IHbl al Hcl).
   destruct IHbl as [| IHbl]; [ easy | ].
   now apply last_cons_id.

   injection Hb; clear Hb; intros Hbl Hb; subst b.
   specialize (IHbl al Hbl).
   now destruct IHbl; [ subst bl | apply last_cons_ne ].

   intros (Hab, Hbl).
  destruct Hbl as [| Hbl].
   rewrite Hab; subst bl; simpl.
   apply list_rem_trail_repeat_0.

   rewrite Hab; clear Hab.
   rewrite list_rem_trail_rep_0.
   induction bl as [| b1]; [ easy | ].
   simpl in Hbl; simpl.
   destruct bl as [| b2]; [ now destruct b1 | ].
   specialize (IHbl Hbl); rewrite IHbl.
   now destruct b1.
Qed.

(*
Lemma List_app_rep_0_last : ∀ al m n,
  List.repeat 0 m = al ++ List.repeat 0 n
  → List.last al 0 = 0.
Proof.
intros * Hr.
revert m n Hr.
induction al as [| a]; intros; [ easy | ].
simpl in Hr.
destruct a; [ | now destruct m ].
destruct m; [ easy | simpl in Hr ].
injection Hr; clear Hr; intros Hr; simpl.
destruct al as [| a]; [ easy | ].
eapply IHal; eassumption.
Qed.
*)

Lemma move_carry_end_enough_iter {r : radix} : ∀ carry m n, rad > 1 →
  carry < m → carry < n → move_carry_end m carry = move_carry_end n carry.
Proof.
intros * Hr Hm Hn.
revert carry n Hm Hn.
induction m; intros; [ easy | ].
destruct n; [ easy | simpl ].
destruct (zerop carry) as [Hc| Hc]; [ easy | f_equal ].
apply IHm.
 apply lt_le_trans with (m := carry); [ | lia ].
 now apply Nat.div_lt.

 apply lt_le_trans with (m := carry); [ | lia ].
 now apply Nat.div_lt.
Qed.

(*
Lemma List_repeat_succ : ∀ A (a : A) n,
  List.repeat a (S n) = a :: List.repeat a n.
Proof. easy. Qed.

Lemma List_repeat_succ_app : ∀ A (a : A) n,
  List.repeat a (S n) = List.repeat a n ++ [a].
Proof.
intros; simpl.
induction n; [ easy | simpl ].
now rewrite <- IHn.
Qed.

Lemma move_carry_cons_rep_0 {r : radix} : ∀ a c n, 1 < rad →
  move_carry c (a :: List.repeat 0 n) =
  move_carry c [a] ++ List.repeat 0 (n - logn1 ((c + a) / rad)).
Proof.
intros * Hr; simpl.
destruct (zerop ((c + a) / rad)) as [Hca| Hca].
 rewrite Hca; simpl; f_equal.
 rewrite Nat.sub_0_r. 
 apply move_carry_0_rep_0.

 f_equal.
 rewrite move_carry_rep_0; [ simpl | easy ].
 destruct (zerop ((c + a) / rad)) as [H| H]; [ lia | easy ].
Qed.

Lemma move_carry_cons {r : radix} : ∀ a al c,
  move_carry c (a :: al) = (c + a) mod rad :: move_carry ((c + a) / rad) al.
Proof. easy. Qed.
*)

Lemma last_move_carry_end {r : radix} : ∀ i c, 1 < rad → 0 < c < i →
  List.last (move_carry_end i c) 0 ≠ 0.
Proof.
intros * Hr Hci.
revert c Hci.
induction i; intros; [ easy | simpl ].
destruct (zerop c) as [| Hc]; [ lia | clear Hc ].
destruct (zerop (c mod rad)) as [Hcr| Hcr].
 rewrite Hcr.
 apply last_cons_id.
 apply Nat.mod_divides in Hcr; [ | lia ].
 destruct Hcr as (d, Hd).
 rewrite Nat.mul_comm in Hd; rewrite Hd.
 rewrite Nat.div_mul; [ | lia ].
 destruct (lt_dec d i) as [Hdi| Hdi].
  apply IHi.
  split; [ destruct d; lia | easy ].

  apply Nat.nlt_ge in Hdi.
  assert (d * rad < S d).
   rewrite <- Hd.
   eapply lt_le_trans; [ apply Hci | lia ].

   exfalso; apply lt_not_le in H; apply H; clear H.
   destruct d; [ lia | ].
   destruct rad as [| s]; [ easy | ].
   destruct s; [ lia | ].
   rewrite Nat.mul_comm; simpl; lia.

  destruct (zerop (c / rad)) as [Hc| Hc].
   rewrite Hc; simpl.
   destruct i; simpl; lia.

   apply last_cons_ne; [ lia | ].
   apply IHi.
   split; [ easy | ].
   clear IHi Hcr.
   assert (H : c ≤ i) by lia.
   rename Hc into Hcr.
   clear Hci.
   revert c Hcr H.
   induction i; intros.
    replace c with 0 in Hcr by lia.
    rewrite Nat.div_small in Hcr; [ easy | lia ].

    destruct (Nat.eq_dec c (S i)) as [Hci| Hci].
     subst c.
     destruct rad as [| s]; [ easy | ].
     destruct s; [ lia | ].
     destruct i; [ rewrite Nat.div_small; lia | ].
     apply Nat.div_lt; lia.

     eapply lt_trans; [ | apply Nat.lt_succ_diag_r ].
     apply IHi; [ easy | lia ].
Qed.

Lemma last_move_carry_end' {r : radix} : ∀ i c, 1 < rad → c < i →
  c = 0 ∨ List.last (move_carry_end i c) 0 ≠ 0.
Proof.
intros * Hr Hci.
destruct c; [ now left | right ].
apply last_move_carry_end; [ easy | ].
split; [ lia | easy ].
Qed.

Lemma last_move_carry_single_nz {r : radix} : ∀ a c, 1 < rad → a ≠ 0 →
  List.last (move_carry c [a]) 0 ≠ 0.
Proof.
intros * Hr Ha.
simpl.
remember ((c + a) / rad) as d eqn:Hd.
destruct (zerop d) as [Hzd| Hnzd].
 simpl; subst d.
 apply Nat.div_small_iff in Hzd; [ | lia ].
 rewrite Nat.mod_small; [ lia | easy ].

 destruct (lt_dec (d / rad) d) as [Hdd| Hdd].
  specialize (last_move_carry_end' d (d / rad) Hr Hdd) as H.
  destruct H as [H| H].
   rewrite H; simpl.
   destruct d; [ easy | simpl ].
   intros H'.
   apply Nat.div_small_iff in H; [ | lia ].
   now rewrite Nat.mod_small in H'.

   destruct (zerop (d mod rad)) as [Hdr| Hdr].
    rewrite Hdr.
    now apply last_cons_id.

    apply last_cons_ne; [ lia | easy ].

  exfalso; apply Hdd; clear Hdd.
  now apply Nat.div_lt.
Qed.

(*
Lemma nat_of_list_rep_0 {r : radix} : ∀ c n,
  nat_of_list c (List.repeat 0 n) = c * rad ^ n.
Proof.
intros.
induction n; [ now rewrite Nat.mul_1_r | ].
simpl; rewrite IHn, Nat.add_0_r; lia.
Qed.

Lemma nat_of_list_0_rep_0 {r : radix} : ∀ n,
  nat_of_list 0 (List.repeat 0 n) = 0.
Proof.
intros.
induction n; [ easy | simpl; now rewrite IHn ].
Qed.

Lemma nat_of_list_0_cons_rep_0 {r : radix} : ∀ a n,
  nat_of_list 0 (a :: List.repeat 0 n) = a.
Proof.
intros; simpl.
now rewrite nat_of_list_0_rep_0.
Qed.

Lemma last_cons_move_carry_end {r : radix} : ∀ x y n,
  2 ≤ rad
  → y = (n + x) / rad ^ n
  → 0 < y
  → List.last (y mod rad :: move_carry_end x (y / rad)) 0 ≠ 0.
Proof.
intros * Hr Hy Hyn.
revert y n Hy Hyn.
induction x; intros.
 destruct rad as [| s]; [ easy | ].
 destruct s; [ lia | ].
 rewrite Nat.div_small in Hy; [ lia | ].
 rewrite Nat.add_0_r.
 now apply Nat.pow_gt_lin_r.

 simpl.
 destruct (zerop (y / rad)) as [Hyr1| Hyr1].
  apply Nat.div_small_iff in Hyr1; [ | lia ].
  rewrite Nat.mod_small; [ lia | easy ].

  apply IHx with (n := S n); [ | easy ].
  replace (S n + x) with (n + S x) by lia.
  rewrite Hy; simpl.
  rewrite Nat.mul_comm.
  rewrite Nat.div_div; [ easy | | lia ].
  apply Nat.pow_nonzero; lia.
Qed.

Theorem list_rem_trail_move_carry_0_nz {r : radix} : 1 < rad → ∀ a,
  list_remove_trailing_0s (move_carry 0 [S a]) = move_carry 0 [S a].
Proof.
intros Hr.
intros.
remember (move_carry 0 [S a]) as al eqn:Hal.
symmetry in Hal.
apply list_rem_trail_iff.
rewrite Nat.sub_diag, List.app_nil_r.
split; [ easy | right ].
subst al.
now apply last_move_carry_single_nz.
Qed.

Lemma eq_list_norm_nil_cons {r : radix} : 1 < rad → ∀ al,
  list_norm al = [] → ∀ a, list_norm (a :: al) = list_norm [a].
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros al Hal a.
unfold list_norm, list_norm_with_carry in Hal |-*.
apply list_rem_trail_iff in Hal.
destruct Hal as (Hal, _); simpl in Hal.
rewrite Nat.sub_0_r in Hal.
apply move_carry_0_is_rep_0 in Hal; [ | easy ].
apply list_rem_trail_iff.
split.
 destruct a.
  rewrite Hal; clear Hal; simpl.
  rewrite Nat.mod_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ simpl | easy ].
  now rewrite move_carry_0_rep_0, List.repeat_length.

  rewrite list_rem_trail_move_carry_0_nz; [ rewrite Hal; clear Hal | easy ].
  rewrite move_carry_cons_rep_0; [ | easy ].
  rewrite Nat.add_0_l, List.app_length.
  rewrite Nat.add_comm, Nat.add_sub.
  now rewrite List.repeat_length.

 destruct a.
  left; simpl.
  now rewrite Nat.mod_0_l; [ rewrite Nat.div_0_l | ].

  right.
  rewrite list_rem_trail_move_carry_0_nz; [ | easy ].
  now apply last_move_carry_single_nz.
Qed.

Lemma list_norm_cons_cons {r : radix} : ∀ a1 a2 al, 1 < rad →
  nat_of_list 0 (a1 :: a2 :: al) ≠ 0
  → list_norm (a1 :: a2 :: al) =
     a1 mod rad :: list_norm ((a1 / rad + a2) :: al).
Proof.
intros * Hr.
assert (Hrz : rad ≠ 0) by lia.
intros Hnl.
unfold list_norm, list_norm_with_carry; simpl.
remember (a1 mod rad) as d1 eqn:Hd1.
symmetry in Hd1.
destruct d1; [ | easy ].
remember ((a1 / rad + a2) mod rad) as d2 eqn:Hd2.
symmetry in Hd2.
destruct d2; [ | easy ].
remember ((a1 / rad + a2) / rad) as c2 eqn:Hc2.
remember (list_remove_trailing_0s (move_carry c2 al)) as al2 eqn:Hal2.
symmetry in Hal2.
destruct al2; [ exfalso | easy ].
apply Nat.mod_divides in Hd1; [ | easy ].
destruct Hd1 as (x1, Hx1); rewrite Nat.mul_comm in Hx1.
rewrite Hx1, Nat.div_mul in Hd2, Hc2; [ | easy | easy ].
apply Nat.mod_divides in Hd2; [ | easy ].
destruct Hd2 as (x2, Hx2); rewrite Nat.mul_comm in Hx2.
rewrite Hx2, Nat.div_mul in Hc2; [ subst x2 | easy ].
simpl in Hnl.
apply eq_list_rem_trail_nil in Hal2.
destruct c2.
 apply move_carry_0_is_rep_0 in Hal2; [ | easy ].
 rewrite Hal2 in Hnl.
 rewrite nat_of_list_0_rep_0 in Hnl.
 apply Nat.eq_add_0 in Hx2.
 destruct Hx2; subst x1 a2.
 now subst a1; simpl in Hnl.

 now apply move_nz_carry in Hal2.
Qed.
*)

Lemma move_carry_end_ne_rep_0_succ {r : radix} : ∀ i c al n, 1 < rad →
  c < i
  → move_carry_end i c ≠ al ++ List.repeat 0 (S n).
Proof.
intros * Hr.
assert (Hrz : rad ≠ 0) by lia.
intros Hci.
destruct i; [ easy | simpl ].
destruct (zerop c) as [Hc| Hc]; [ now destruct al | simpl ].
destruct i; [ lia | simpl ].
destruct (zerop (c / rad)) as [Hcr| Hcr].
 destruct al as [| a]; [ | now destruct al ].
 apply Nat.div_small_iff in Hcr; [ | easy ].
 rewrite Nat.mod_small; [ | easy ].
 intros H; injection H; clear H; intros H Hcz.
 now rewrite Hcz in Hc.

 revert c i Hci Hc Hcr.
 induction al as [| a]; intros.
  intros H; injection H; clear H; intros H Hcz.
  revert c i Hci Hc Hcr H Hcz.
  induction n; intros; [ easy | ].
  injection H; clear H; intros H Hcrr.
  destruct i.
   replace c with 1 in Hcz by lia.
   now rewrite Nat.mod_1_l in Hcz.

   simpl in H.
   destruct (zerop (c / rad / rad)) as [Hzcrr| Hzcrr].
    apply Nat.div_small_iff in Hzcrr; [ | easy ].
    rewrite Nat.mod_small in Hcrr; [ | easy ].
    now rewrite Hcrr in Hcr.

    apply IHn with (c := c / rad) (i := i); try easy.
    apply Nat.div_lt_upper_bound; [ easy | ].
    destruct rad as [| s]; [ easy | ].
    destruct s; [ lia | simpl; lia ].

  simpl.
  intros H; injection H; clear H; intros H Ha.
  destruct i.
   replace c with 1 in Hcr by lia.
   now rewrite Nat.div_1_l in Hcr.

   simpl in H.
   destruct (zerop (c / rad / rad)) as [Hzcrr| Hzcrr].
    apply Nat.div_small_iff in Hzcrr; [ | easy ].
    rewrite Nat.mod_small in H; [ | easy ].
    destruct al; [ simpl in H | now destruct al ].
    injection H; clear H; intros H H1.
    now rewrite H1 in Hcr.

    revert H.
    apply IHal; [ | easy | easy ].
    apply Nat.div_lt_upper_bound; [ easy | ].
    destruct rad as [| s]; [ easy | ].
    destruct s; [ lia | simpl; lia ].
Qed.

Lemma fold_move_carry {r : radix} : ∀ c al,
  (fix move_carry (r0 : radix) (carry : nat) (al0 : list nat) {struct al0} :
     list nat :=
     match al0 with
     | [] => move_carry_end (S carry) carry
     | a :: al' => (carry + a) mod rad :: move_carry r0 ((carry + a) / rad) al'
     end) r c al
  = move_carry c al.
Proof. easy. Qed.

Lemma fold_list_norm_with_carry {r : radix} : ∀ c al,
  list_remove_trailing_0s (move_carry c al) = list_norm_with_carry c al.
Proof. easy. Qed.

(*
Lemma list_norm_wc_nil {r : radix} : ∀ c,
  list_norm_with_carry c [] =
  if zerop c then []
  else list_remove_trailing_0s (c mod rad :: move_carry_end c (c / rad)).
Proof.
intros.
unfold list_norm_with_carry; simpl.
now destruct (zerop c).
Qed.

Lemma list_norm_wc_cons_list_rem {r : radix} : ∀ c a al,
  list_norm_with_carry c (a :: al) =
  list_remove_trailing_0s ((c + a) mod rad :: move_carry ((c + a) / rad) al).
Proof. easy. Qed.
*)

Lemma list_norm_wc_cons {r : radix} : ∀ c a al, rad ≠ 0 →
  list_norm_with_carry c (a :: al) =
  match list_norm_with_carry ((c + a) / rad) al with
  | [] => if zerop ((c + a) mod rad) then [] else [(c + a) mod rad]
  | b :: bl => (c + a) mod rad :: b :: bl
  end.
Proof.
intros * Hr.
unfold list_norm_with_carry, move_carry; simpl.
remember ((c + a) mod rad) as d eqn:Hd.
remember ((c + a) / rad) as c1 eqn:Hc1.
destruct d; [ easy | simpl ].
rewrite fold_move_carry.
rewrite fold_list_norm_with_carry.
now destruct (list_norm_with_carry c1 al).
Qed.

Lemma list_of_nat_carry_inv {r : radix} : 2 ≤ rad →
  ∀ c al, list_of_nat 0 (c + nat_of_list 0 al) = list_norm_with_carry c al.
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros.
revert c.
induction al as [| a1]; intros.
 rewrite Nat.add_0_r; simpl.
 unfold list_norm_with_carry; simpl.
 unfold list_of_nat.
 destruct (zerop c) as [Hc| Hc]; [ easy | ].
 symmetry.
 apply list_rem_trail_iff.
 split.
  simpl.
  destruct (zerop (c / rad)) as [Hcr| Hcr].
   rewrite Hcr.
   apply Nat.div_small_iff in Hcr; [ | easy ].
   rewrite Nat.mod_small; [ | easy ].
   now destruct c.

   destruct c; [ easy | simpl ].
   destruct (zerop (S c / rad)) as [H| H]; [ now rewrite H in Hcr | clear H ].
   f_equal; f_equal; simpl.
   rewrite move_carry_end_enough_iter with (n := S c / rad); [ | easy | | ].
    now rewrite Nat.sub_diag, List.app_nil_r.

    apply Nat.div_lt_upper_bound; [ easy | ].
    apply Nat.div_lt_upper_bound; [ easy | ].
    destruct c; [ now rewrite Nat.div_1_l in Hcr | ].
    destruct rad as [| s]; [ easy | ].
    destruct s; [ lia | simpl; lia ].

    now apply Nat.div_lt.

  right.
  now apply last_move_carry_single_nz; [ | intros H; rewrite H in Hc ].

 rewrite list_norm_wc_cons; [ simpl | easy ].
 rewrite <- IHal.
 unfold list_of_nat.
 destruct (zerop (c + (nat_of_list 0 al * rad + a1))) as [Hzna| Hzna].
  apply Nat.eq_add_0 in Hzna.
  destruct Hzna as (Hc, Hzna); subst c.
  apply Nat.eq_add_0 in Hzna.
  destruct Hzna as (Hal, Ha1); subst a1.
  apply Nat.eq_mul_0 in Hal.
  destruct Hal as [Hal| Hra]; [ | easy ].
  rewrite Hal.
  rewrite Nat.div_0_l; [ | easy ].
  now rewrite Nat.mod_0_l.

  destruct (zerop ((c + a1) / rad + nat_of_list 0 al)) as [Hzcan| Hzcan].
   apply Nat.eq_add_0 in Hzcan; simpl.
   destruct Hzcan as (Hcar, Hal); rewrite Hal; simpl.
   rewrite Hcar; simpl.
   apply Nat.div_small_iff in Hcar; [ | easy ].
   rewrite Nat.mod_small; [ simpl | easy ].
   rewrite Hal in Hzna; simpl in Hzna.
   now destruct (zerop (c + a1)) as [H| ]; [ rewrite H in Hzna | ].

   simpl.
   f_equal.
    rewrite Nat.add_comm, <- Nat.add_assoc, Nat.add_comm.
    now rewrite Nat.mod_add; [ rewrite Nat.add_comm | ].

    remember ((c + (nat_of_list 0 al * rad + a1)) / rad) as cn eqn:Hcn.
    rewrite Nat.add_comm, <- Nat.add_assoc, Nat.add_comm in Hcn.
    rewrite Nat.div_add in Hcn; [ | easy ].
    replace (a1 + c) with (c + a1) in Hcn by apply Nat.add_comm.
    rewrite <- Hcn in Hzcan; rewrite <- Hcn.
    destruct cn; [ easy | simpl ].
    f_equal; f_equal.
    destruct (zerop (S cn / rad)) as [| Hzcr]; [ easy | f_equal ].
    apply move_carry_end_enough_iter; [ easy | | now apply Nat.div_lt ].
    apply Nat.div_lt_upper_bound; [ easy | ].
    apply Nat.div_lt_upper_bound; [ easy | ].
    destruct cn; [ now rewrite Nat.div_1_l in Hzcr | ].
    destruct rad as [| s]; [ easy | ].
    destruct s; [ lia | simpl; lia ].
Qed.

Lemma list_of_nat_nat_of_list {r : radix} : 2 ≤ rad →
  ∀ al, list_of_nat 0 (nat_of_list 0 al) = list_norm al.
Proof.
intros Hr *.
now specialize (list_of_nat_carry_inv Hr 0 al) as H.
Qed.

Lemma list_carry_end_digits_lt_radix {r : radix} : rad ≠ 0 →
  ∀ i c, List.Forall (λ a, a < rad) (move_carry_end i c).
Proof.
intros Hr *.
revert c.
induction i; intros; [ constructor | simpl ].
destruct (zerop c) as [Hzc| Hzc]; [ easy | ].
constructor; [ now apply Nat.mod_upper_bound | ].
apply IHi.
Qed.

Lemma list_norm_wc_digits_lt_radix {r : radix} : 1 < rad →
  ∀ al c, List.Forall (λ a, a < rad) (list_norm_with_carry c al).
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros.
remember (list_norm_with_carry c al) as al1 eqn:Hal1.
symmetry in Hal1.
apply list_rem_trail_iff in Hal1.
destruct Hal1 as (Hn, Hal1).
remember (length (move_carry c al) - length al1) as n eqn:Hnd.
symmetry in Hnd.
destruct Hal1 as [Hal1| Hlast]; [ now subst al1 | ].
revert c al Hn Hnd.
induction al1 as [| a1]; intros; [ easy | ].
constructor.
 destruct al as [| a2].
  simpl in Hn.
  destruct (zerop c) as [| Hc]; [ easy | ].
  injection Hn; clear Hn; intros; subst a1.
  now apply Nat.mod_upper_bound.

  simpl in Hn.
  injection Hn; clear Hn; intros; subst a1.
  now apply Nat.mod_upper_bound.

 simpl in Hlast.
 destruct al1 as [| a2]; [ easy | ].
 constructor.
  destruct al as [| a3].
   simpl in Hn.
   destruct (zerop c) as [| Hc]; [ easy | ].
   injection Hn; clear Hn; intros Hn Hca.
   destruct c; [ easy | ].
   simpl in Hnd, Hn.
   destruct (zerop (S c / rad)) as [Hscr| Hscr]; [ easy | ].
   simpl in Hnd, Hn.
   injection Hn; clear Hn; intros; subst a2.
   now apply Nat.mod_upper_bound.

   destruct n.
    simpl in Hn.
    injection Hn; clear Hn; intros Hn Ha1.
    destruct al as [| a4].
     simpl in Hn.
     destruct (zerop ((c + a3) / rad)) as [Hscr| Hscr]; [ easy | ].
     injection Hn; clear Hn; intros; subst a2.
     now apply Nat.mod_upper_bound.

     simpl in Hn.
     injection Hn; clear Hn; intros; subst a2.
     now apply Nat.mod_upper_bound.

    remember (S n) as s; simpl in Hn; subst s.
    destruct al as [| a4].
     simpl in Hn.
     destruct (zerop ((c + a3) / rad)) as [Hscr| Hscr]; [ easy | ].
     injection Hn; clear Hn; intros; subst a2.
     now apply Nat.mod_upper_bound.

     simpl in Hn.
     injection Hn; clear Hn; intros; subst a2.
     now apply Nat.mod_upper_bound.

  destruct al as [| a3].
   simpl in Hnd, Hn.
   destruct (zerop c) as [Hc| Hc]; [ easy | ].
   simpl in Hnd.
   injection Hn; clear Hn; intros Hn Hce.
   destruct n.
    rewrite List.app_nil_r in Hn.
    destruct c; [ easy | ].
    simpl in Hnd, Hn.
    destruct (zerop (S c / rad)) as [Hcr| Hcr]; [ easy | ].
    injection Hn; clear Hn; intros Hn Ha2; rewrite <- Hn.
    now apply list_carry_end_digits_lt_radix.

    rewrite List.app_comm_cons in Hn.
    apply move_carry_end_ne_rep_0_succ in Hn; [ easy | easy | ].
    now apply Nat.div_lt.

   simpl in Hn.
   injection Hn; clear Hn; intros Hn Ha1.
   rewrite List.app_comm_cons in Hn.
   simpl in Hnd.
   specialize (IHal1 Hlast ((c + a3) / rad) al Hn Hnd).
   now apply list_Forall_inv in IHal1.
Qed.

Lemma list_norm_digits_lt_radix {r : radix} : 1 < rad →
  ∀ al, List.Forall (λ a, a < rad) (list_norm al).
Proof.
intros Hr *.
now apply list_norm_wc_digits_lt_radix.
Qed.

(* Conversion from and to nat *)

Theorem nat_of_xnat_inv {r : radix} : 2 ≤ rad →
  ∀ a, nat_of_xnat (xnat_of_nat a) = a.
Proof.
intros Hr *.
unfold xnat_of_nat, nat_of_xnat; simpl.
now apply nat_of_list_list_of_nat.
Qed.

Theorem xnat_of_nat_inv {r : radix} : 2 ≤ rad →
  ∀ a, xnat_of_nat (nat_of_xnat a) = xnat_norm a.
Proof.
intros Hr *.
unfold xnat_of_nat, xnat_norm; f_equal.
now apply list_of_nat_nat_of_list.
Qed.

Theorem xnat_norm_digits_lt_radix {r : radix} : 2 ≤ rad →
  ∀ a, List.Forall (λ a, a < rad) (xnatv (xnat_norm a)).
Proof.
intros Hr *.
unfold xnat_norm; simpl.
now apply list_norm_digits_lt_radix.
Qed.

(* Addition *)

Fixpoint xnatv_add a b :=
  match a with
  | [] => b
  | a₀ :: al =>
      match b with
      | [] => a
      | b₀ :: bl => a₀ + b₀ :: xnatv_add al bl
      end
  end.

Definition xnat_add {r : radix} a b :=
  xn (xnatv_add (xnatv a) (xnatv b)).

Definition xnat_0 {r : radix} := xn [].

Delimit Scope xnat_scope with X.
Notation "a + b" := (xnat_add a b) : xnat_scope.
Notation "a = b" := (xnat_norm a = xnat_norm b) : xnat_scope.
Notation "0" := (xnat_0) : xnat_scope.

Lemma xnatv_add_comm {r : radix} : ∀ al bl,
  xnatv_add al bl = xnatv_add bl al.
Proof.
intros *.
revert bl.
induction al as [| a1]; intros; [ now destruct bl | simpl ].
destruct bl as [| b1]; [ easy | simpl ].
now rewrite Nat.add_comm, IHal.
Qed.

Theorem xnat_add_comm {r : radix} : ∀ a b, (a + b = b + a)%X.
Proof.
intros.
unfold xnat_add; simpl.
now rewrite xnatv_add_comm.
Qed.

Theorem xnat_add_0_l {r : radix} : ∀ a, (0 + a = a)%X.
Proof. easy. Qed.

Lemma list_norm_wc_add_assoc {r : radix} : rad ≠ 0 → ∀ al bl cl carry,
  list_norm_with_carry carry (xnatv_add al (xnatv_add bl cl)) =
  list_norm_with_carry carry (xnatv_add (xnatv_add al bl) cl).
Proof.
intros Hr *.
revert al cl carry.
induction bl as [| b1]; intros; simpl.
 now replace (xnatv_add al []) with (xnatv_add [] al) by apply xnatv_add_comm.

 destruct cl as [| c1]; [ now destruct al | simpl ].
 destruct al as [| a1]; [ easy | simpl ].
 rewrite Nat.add_assoc.
 rewrite list_norm_wc_cons; [ | easy ].
 rewrite list_norm_wc_cons; [ | easy ].
 now rewrite IHbl.
Qed.

Theorem xnat_add_assoc {r : radix} : rad ≠ 0 → ∀ a b c,
  (a + (b + c) = (a + b) + c)%X.
Proof.
intros Hr *.
unfold xnat_add, xnat_norm; simpl; f_equal.
now apply list_norm_wc_add_assoc.
Qed.

(**)

Lemma xnatv_add_rep_0_l {r : radix} : ∀ al n,
  xnatv_add (List.repeat 0 n) al = al ++ List.repeat 0 (n - length al).
Proof.
intros.
revert n.
induction al as [| a]; intros; [ now destruct n | simpl ].
now destruct n; [ rewrite List.app_nil_r | simpl; rewrite IHal ].
Qed.

(* logn1(n) = integer logarithm plus one = number of digits *)
Definition logn1 {r : radix} n := length (move_carry_end (S n) n).

Lemma move_carry_0_rep_0 {r : radix} : ∀ n,
  move_carry 0 (List.repeat 0 n) = List.repeat 0 n.
Proof.
intros.
induction n; [ easy | simpl ].
destruct (zerop rad) as [Hr| Hr].
 rewrite Hr; simpl.
 now f_equal.

 rewrite Nat.mod_0_l; [ f_equal | lia ].
 rewrite Nat.div_0_l; [ easy | lia ].
Qed.

Lemma move_carry_rep_0_end {r : radix} : ∀ n a, 1 < rad →
  move_carry a (List.repeat 0 n) =
  move_carry_end (S a) a ++ List.repeat 0 (n - logn1 a).
Proof.
intros * Hr.
unfold logn1.
revert a.
induction n; intros; simpl.
 now destruct (zerop a); [ | rewrite List.app_nil_r ].

 rewrite Nat.add_0_r.
 destruct (zerop a) as [Ha| Ha].
  subst a.
  rewrite Nat.mod_0_l; [ | lia ].
  rewrite Nat.div_0_l; [ | lia ].
  now rewrite move_carry_0_rep_0.

  simpl; rewrite IHn; f_equal.
  f_equal.
   apply move_carry_end_enough_iter; [ easy | lia | ].
   destruct a; [ easy | ].
   destruct rad as [| s]; [ easy | ].
   destruct s; [ lia | now apply Nat.div_lt ].

   f_equal; f_equal; f_equal.
   apply move_carry_end_enough_iter; [ easy | lia | ].
   destruct a; [ easy | ].
   destruct rad as [| s]; [ easy | ].
   destruct s; [ lia | now apply Nat.div_lt ].
Qed.

Lemma move_carry_rep_0 {r : radix} : ∀ n a, 1 < rad →
  move_carry a (List.repeat 0 n) =
  move_carry a [] ++ List.repeat 0 (n - logn1 a).
Proof.
intros * Hr.
unfold move_carry at 2.
destruct (zerop a) as [Ha| Ha].
 subst a; simpl; rewrite Nat.sub_0_r.
 apply move_carry_0_rep_0.

 now apply move_carry_rep_0_end.
Qed.

Lemma move_carry_app_rep_0 {r : radix} : 1 < rad → ∀ c al n,
  move_carry c (al ++ List.repeat 0 n) =
  move_carry c al ++
  List.repeat 0
    (length (move_carry c (al ++ List.repeat 0 n)) -
     length (move_carry c al)).
Proof.
intros Hr *.
revert c.
induction al as [| a1]; intros.
 simpl.
 rewrite move_carry_rep_0; [ simpl | easy ].
 destruct (zerop c) as [Hc| Hc].
  rewrite Nat.sub_0_r; simpl.
  now rewrite List.repeat_length.

  f_equal; simpl.
  rewrite List.app_length, Nat.add_comm, Nat.add_sub.
 now  rewrite List.repeat_length.

 simpl; f_equal.
 rewrite IHal; f_equal.
 remember (c + a1) as x eqn:Hx.
 rewrite List.app_length, Nat.add_comm, Nat.add_sub.
 now rewrite List.repeat_length.
Qed.

Lemma list_norm_with_carry_app_rep_0 {r : radix} : 1 < rad → ∀ al n c,
  list_norm_with_carry c (al ++ List.repeat 0 n) =
  list_norm_with_carry c al.
Proof.
intros Hr *.
unfold list_norm_with_carry.
rewrite move_carry_app_rep_0; [ | easy ].
now rewrite list_rem_trail_rep_0.
Qed.

Lemma eq_move_carry_end_nil {r : radix} : ∀ i c,
  move_carry_end i c = [] ↔ i = 0 ∨ c = 0.
Proof.
intros.
split; intros H.
 now destruct i; [ left | right; now destruct c ].

 destruct H; [ now subst i | now subst c; destruct i ].
Qed.

Lemma eq_move_carry_nil {r : radix} : ∀ c al,
  move_carry c al = [] ↔ al = [] ∧ move_carry_end (S c) c = [].
Proof.
intros.
split; intros H; [ now destruct al | ].
now destruct H as (Hal, Hmc); rewrite Hal.
Qed.

Lemma move_carry_end_succ_ne_rep_0 {r : radix} : ∀ i c n, 1 < rad →
  0 < c < i
  → move_carry_end i c ≠ List.repeat 0 n.
Proof.
intros * Hr (Hc, Hci).
revert c n Hc Hci.
induction i; intros; [ easy | simpl ].
destruct (zerop c) as [H| H]; [ lia | clear H ].
remember (c mod rad) as c1 eqn:Hc1.
symmetry in Hc1.
destruct c1; [ | now destruct n ].
destruct n; [ easy | ].
simpl; intros H; injection H; clear H; intros H.
apply Nat.mod_divides in Hc1; [ | lia ].
destruct Hc1 as (c1, Hc1).
rewrite Nat.mul_comm in Hc1.
revert H.
rewrite Hc1, Nat.div_mul; [ | lia ].
apply IHi; [ destruct c1; lia | ].
apply Nat.mul_lt_mono_pos_r with (p := rad); [ lia | ].
rewrite <- Hc1.
destruct rad as [| s]; [ easy | ].
destruct s; [ lia | ].
destruct i; [ lia | ].
rewrite Nat.mul_comm; simpl; lia.
Qed.

Lemma list_rem_trail_cons_cons_ne_single {r : radix} : 1 < rad → ∀ a b,
  0 < S a / rad
  → list_remove_trailing_0s
       (S a mod rad :: (S a / rad) mod rad ::
        move_carry_end a (S a / rad / rad)) ≠ [S b].
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Har Hab.
apply list_rem_trail_iff in Hab.
destruct Hab as (Hn, _).
injection Hn; clear Hn; intros Hn Hbrr Hbr.
apply move_carry_end_succ_ne_rep_0 in Hn; [ easy | easy | ].
apply Nat.mod_divides in Hbrr; [ | easy ].
destruct Hbrr as (c, Hc); rewrite Nat.mul_comm in Hc.
split.
 rewrite Hc in Har.
 rewrite Hc, Nat.div_mul; [ | easy ].
 destruct c; [ easy | lia ].

 apply Nat.div_lt_upper_bound; [ easy | ].
 apply Nat.div_lt_upper_bound; [ easy | ].
 destruct a; [ now rewrite Nat.div_1_l in Har | ].
 destruct rad as [| s]; [ easy | ].
 destruct s; [ lia | simpl; lia ].
Qed.

Lemma list_rem_trail_move_carry_end {r : radix} : 1 < rad → ∀ i c,
  c < i
  → list_remove_trailing_0s (move_carry_end i c) = move_carry_end i c.
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hci.
revert c Hci.
induction i; intros; [ easy | simpl ].
destruct (zerop c) as [Hc| Hc]; [ easy | simpl ].
destruct c; [ easy | ].
apply <- Nat.succ_lt_mono in Hci.
destruct (lt_dec (S c / rad) i) as [Hcri| Hcri].
 rewrite IHi; [ | easy ].
 remember (S c mod rad) as d eqn:Hd.
 symmetry in Hd.
 destruct d; [ | easy ].
 destruct i; [ easy | simpl ].
 destruct (zerop (S c / rad)) as [Hcr| Hcr]; [ | easy ].
 now rewrite Nat.mod_small in Hd; [ | apply Nat.div_small_iff in Hcr ].

 destruct c; [ now rewrite Nat.div_1_l in Hcri | ].
 exfalso; apply Hcri; clear Hcri.
 eapply le_lt_trans; [ | eassumption ].
 apply Nat.div_le_upper_bound; [ easy | ].
 destruct rad as [| s]; [ easy | ].
 destruct s; [ lia | simpl; lia ].
Qed.

Lemma move_carry_end_inv {r : radix} : 1 < rad → ∀ a b i j,
  a < i
  → b < j
  → move_carry_end i a = move_carry_end j b
  → a = b.
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hai Hbi Hab.
revert a b j Hai Hbi Hab.
induction i; intros; [ easy | simpl in Hab ].
destruct (zerop a) as [Hza| Hza].
 symmetry in Hab.
 apply eq_move_carry_end_nil in Hab.
 now destruct Hab as [Hj| Hb]; [ rewrite Hj in Hbi | subst a b ].

 destruct j; [ easy | simpl in Hab ].
 destruct (zerop b) as [Hzb| Hzb]; [ easy | ].
 injection Hab; clear Hab; intros Hab Habr.
 apply IHi in Hab.
  rewrite Nat.div_mod with (y := rad); [ symmetry | easy ].
  rewrite Nat.div_mod with (y := rad); [ symmetry | easy ].
  now rewrite Hab, Habr.

  apply Nat.div_lt_upper_bound; [ easy | ].
  destruct rad as [| s]; [ easy | ].
  destruct s; [ lia | simpl; lia ].

  apply Nat.div_lt_upper_bound; [ easy | ].
  destruct rad as [| s]; [ easy | ].
  destruct s; [ lia | simpl; lia ].
Qed.

Lemma list_rem_trail_cons_eq_cons : ∀ a b al bl,
  list_remove_trailing_0s (a :: al) = list_remove_trailing_0s (b :: bl)
  ↔ a = b ∧ list_remove_trailing_0s al = list_remove_trailing_0s bl.
Proof.
intros *.
simpl.
remember (list_remove_trailing_0s al) as al' eqn:Hal'.
remember (list_remove_trailing_0s bl) as bl' eqn:Hbl'.
symmetry in Hal', Hbl'.
split; intros Hab.
 destruct a.
  destruct b; [ | now destruct al' ].
  destruct al' as [| a1]; [ now destruct bl' | ].
  destruct bl' as [| b1]; [ easy | ].
  now injection Hab; intros; subst a1 al'.

  destruct b; [ now destruct bl' | ].
  now injection Hab; intros; subst a.

 now destruct Hab as (H, Hl); rewrite H, Hl.
Qed.

Lemma list_norm_with_carry_inv {r : radix} : 1 < rad → ∀ ca cb al,
  list_norm_with_carry ca al = list_norm_with_carry cb al
  → ca = cb.
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hab.
unfold list_norm_with_carry in Hab; simpl in Hab.
revert ca cb Hab.
induction al as [| a]; intros.
 simpl in Hab.
 destruct (zerop ca) as [Hca| Hca].
  subst ca.
  destruct (zerop cb) as [Hcb| Hcb]; [ easy | exfalso ].
  simpl in Hab; symmetry in Hab.
  remember (move_carry_end cb (cb / rad)) as l eqn:Hl.
  remember (list_remove_trailing_0s l) as al eqn:Hal; subst l.
  symmetry in Hal.
  destruct al as [| a]; [ | now destruct (cb mod rad) ].
  remember (cb mod rad) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; [ clear Hab | easy ].
  apply eq_list_rem_trail_nil in Hal.
  apply move_carry_end_succ_ne_rep_0 in Hal; [ easy | easy | ].
  destruct cb; [ easy | ].
  split; [ | now apply Nat.div_lt ].
  apply Nat.mod_divides in Hc1; [ | easy ].
  destruct Hc1 as (c, Hc); rewrite Nat.mul_comm in Hc.
  rewrite Hc, Nat.div_mul; [ | easy ].
  destruct c; lia.

  destruct (zerop cb) as [Hcb| Hcb].
   subst cb; exfalso.
   unfold list_remove_trailing_0s in Hab at 2.
   apply eq_list_rem_trail_nil in Hab; simpl in Hab.
   injection Hab; clear Hab; intros Hab Hc1.
   apply move_carry_end_succ_ne_rep_0 in Hab; [ easy | easy | ].
   split; [ | now apply Nat.div_lt ].
   apply Nat.mod_divides in Hc1; [ | easy ].
   destruct Hc1 as (c, Hc); rewrite Nat.mul_comm in Hc.
   rewrite Hc, Nat.div_mul; [ | easy ].
   destruct c; lia.

   apply list_rem_trail_cons_eq_cons in Hab.
   destruct Hab as (Habr, Hab).
   destruct ca; [ easy | clear Hca ].
   destruct cb; [ easy | clear Hcb ].
   simpl in Hab.
   destruct (zerop (S ca / rad)) as [Hca| Hca].
    rewrite Nat.mod_small in Habr; [ | now apply Nat.div_small_iff in Hca ].
    destruct (zerop (S cb / rad)) as [Hcb| Hcb].
     now rewrite Nat.mod_small in Habr; [ | apply Nat.div_small_iff in Hcb ].

     symmetry in Hab.
     apply eq_list_rem_trail_nil in Hab; simpl in Hab.
     injection Hab; clear Hab; intros Hab Hb.
     destruct cb; [ now rewrite Nat.div_1_l in Hcb | ].
     apply move_carry_end_succ_ne_rep_0 in Hab; [ easy | easy | ].
     split.
      apply Nat.mod_divides in Hb; [ | easy ].
      destruct Hb as (c, Hc); rewrite Nat.mul_comm in Hc.
      rewrite Hc, Nat.div_mul; [ | easy ].
      destruct c; lia.

      apply Nat.div_lt_upper_bound; [ easy | ].
      apply Nat.div_lt_upper_bound; [ easy | ].
      destruct rad as [| s]; [ easy | ].
      destruct s; [ lia | simpl; lia ].

    destruct (zerop (S cb / rad)) as [Hcb| Hcb].
     apply eq_list_rem_trail_nil in Hab; simpl in Hab.
     injection Hab; clear Hab; intros Hab Ha.
     destruct ca; [ now rewrite Nat.div_1_l in Hca | ].
     apply move_carry_end_succ_ne_rep_0 in Hab; [ easy | easy | ].
     split.
      apply Nat.mod_divides in Ha; [ | easy ].
      destruct Ha as (c, Hc); rewrite Nat.mul_comm in Hc.
      rewrite Hc, Nat.div_mul; [ | easy ].
      destruct c; lia.

      apply Nat.div_lt_upper_bound; [ easy | ].
      apply Nat.div_lt_upper_bound; [ easy | ].
      destruct rad as [| s]; [ easy | ].
      destruct s; [ lia | simpl; lia ].

     f_equal.
     apply list_rem_trail_cons_eq_cons in Hab.
     destruct Hab as (Habrr, Hab).
     rewrite list_rem_trail_move_carry_end in Hab; [ | easy | ].
      rewrite list_rem_trail_move_carry_end in Hab; [ | easy | ].
       simpl in Hab.
       apply move_carry_end_inv in Hab; [ | easy | | ].
        assert (H : S ca / rad = S cb / rad).
         rewrite Nat.div_mod with (y := rad); [ symmetry | easy ].
         rewrite Nat.div_mod with (y := rad); [ symmetry | easy ].
         now rewrite Habrr, Hab.

         apply Nat.succ_inj.
         rewrite Nat.div_mod with (y := rad); [ symmetry | easy ].
         rewrite Nat.div_mod with (y := rad); [ symmetry | easy ].
         now rewrite Habr, H.

        apply Nat.div_lt_upper_bound; [ easy | ].
        apply Nat.div_lt_upper_bound; [ easy | ].
        destruct ca; [ now rewrite Nat.div_1_l in Hca | ].
        destruct rad as [| s]; [ easy | ].
        destruct s; [ lia | simpl; lia ].

        apply Nat.div_lt_upper_bound; [ easy | ].
        apply Nat.div_lt_upper_bound; [ easy | ].
        destruct cb; [ now rewrite Nat.div_1_l in Hcb | ].
        destruct rad as [| s]; [ easy | ].
        destruct s; [ lia | simpl; lia ].

      apply Nat.div_lt_upper_bound; [ easy | ].
      apply Nat.div_lt_upper_bound; [ easy | ].
      destruct cb; [ now rewrite Nat.div_1_l in Hcb | ].
      destruct rad as [| s]; [ easy | ].
      destruct s; [ lia | simpl; lia ].

      apply Nat.div_lt_upper_bound; [ easy | ].
      apply Nat.div_lt_upper_bound; [ easy | ].
      destruct ca; [ now rewrite Nat.div_1_l in Hca | ].
      destruct rad as [| s]; [ easy | ].
      destruct s; [ lia | simpl; lia ].

 simpl in Hab.
 remember ((ca + a) mod rad) as car eqn:Hcar.
 remember ((cb + a) mod rad) as cbr eqn:Hcbr.
 remember (move_carry ((ca + a) / rad) al) as x eqn:Hx.
 remember (list_remove_trailing_0s x) as rca eqn:Hrca; subst x.
 remember (move_carry ((cb + a) / rad) al) as x eqn:Hx.
 remember (list_remove_trailing_0s x) as rcb eqn:Hrcb; subst x.
 symmetry in Hcar, Hcbr, Hrca, Hrcb.
 destruct rca as [| ra ].
  destruct rcb; [ | now destruct car, cbr ].
  generalize Hrca; intros H.
  rewrite <- Hrcb in H.
  apply IHal in H.
  apply eq_list_rem_trail_nil in Hrca.
  apply eq_list_rem_trail_nil in Hrcb.
  destruct car.
   destruct cbr; [ clear Hab | easy ].
   apply Nat.mod_divides in Hcar; [ | easy ].
   apply Nat.mod_divides in Hcbr; [ | easy ].
   destruct Hcar as (car, Hcar); rewrite Nat.mul_comm in Hcar.
   destruct Hcbr as (cbr, Hcbr); rewrite Nat.mul_comm in Hcbr.
   rewrite Hcar, Nat.div_mul in Hrca, H; [ | easy | easy ].
   rewrite Hcbr, Nat.div_mul in Hrcb, H; [ | easy | easy ].
   subst car; lia.

   destruct cbr; [ easy | ].
   injection Hab; clear Hab; intros Hab.
   subst car.
   apply Nat.add_cancel_r with (p := a).
   rewrite Nat.div_mod with (y := rad); [ symmetry | easy ].
   rewrite Nat.div_mod with (y := rad); [ symmetry | easy ].
   now rewrite H, Hcar, <- Hcbr.

  destruct rcb as [| rb]; [ now destruct car, cbr | ].
  assert (H : ra = rb ∧ rca = rcb).
   destruct car, cbr; [ | easy | easy | ]; now injection Hab; intros.

   destruct H as (Hrab, Hrcab).
   subst rb rcb.
   generalize Hrca; intros H.
   rewrite <- Hrcb in H.
   apply IHal in H.
   destruct car.
    destruct cbr; [ clear Hab | easy ].
    apply Nat.mod_divides in Hcar; [ | easy ].
    apply Nat.mod_divides in Hcbr; [ | easy ].
    destruct Hcar as (car, Hcar); rewrite Nat.mul_comm in Hcar.
    destruct Hcbr as (cbr, Hcbr); rewrite Nat.mul_comm in Hcbr.
    rewrite Hcar, Nat.div_mul in Hrca, H; [ | easy | easy ].
    rewrite Hcbr, Nat.div_mul in Hrcb, H; [ | easy | easy ].
    subst car; lia.

    destruct cbr; [ easy | ].
    injection Hab; clear Hab; intros Hab.
    subst car.
    apply Nat.add_cancel_r with (p := a).
    rewrite Nat.div_mod with (y := rad); [ symmetry | easy ].
    rewrite Nat.div_mod with (y := rad); [ symmetry | easy ].
    now rewrite H, Hcar, <- Hcbr.
Qed.

Lemma move_nz_carry {r : radix} : ∀ al n c, 1 < rad → c ≠ 0 →
  move_carry c al ≠ List.repeat 0 n.
Proof.
intros * Hr Hc H.
destruct c; [ easy | clear Hc ].
revert c n H.
induction al as [| a]; intros.
 unfold move_carry in H.
 revert H; apply move_carry_end_succ_ne_rep_0; [ easy | ].
 split; lia.

 destruct n in H; [ easy | simpl in H ].
 injection H; clear H; intros H Hc.
 apply Nat.mod_divides in Hc; [ | lia ].
 destruct Hc as (c1, Hc1).
 rewrite Nat.mul_comm in Hc1.
 rewrite Hc1 in H.
 rewrite Nat.div_mul in H; [ | lia ].
 destruct c1; [ lia | ].
 revert H; apply IHal.
Qed.

Lemma move_carry_0_is_rep_0 {r : radix} : ∀ al n, 1 < rad →
  move_carry 0 al = List.repeat 0 n → al = List.repeat 0 n.
Proof.
intros * Hr Han.
revert al Han.
induction n; intros; [ now destruct al | ].
simpl in Han; simpl.
destruct al as [| a]; [ easy | ].
simpl in Han.
injection Han; clear Han; intros Han Ha.
apply Nat.mod_divides in Ha; [ | lia ].
destruct Ha as (a1, Ha).
rewrite Nat.mul_comm in Ha; subst a.
rewrite Nat.div_mul in Han; [ | lia ].
destruct a1; [ now f_equal; apply IHn | exfalso ].
revert Han.
now apply move_nz_carry.
Qed.

Lemma eq_list_norm_wc_nil {r : radix} : 1 < rad → ∀ c al,
  list_norm_with_carry c al = []
  → c = 0 ∧ al = List.repeat 0 (length (move_carry c al)).
Proof.
intros Hr * Hca.
unfold list_norm_with_carry in Hca.
apply eq_list_rem_trail_nil in Hca.
destruct c; [ now apply move_carry_0_is_rep_0 in Hca | ].
now apply move_nz_carry in Hca.
Qed.

Lemma move_carry_add {r : radix} : 1 < rad → ∀ c al,
  list_norm (move_carry c al) = list_norm (xnatv_add [c] al).
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros *.
rewrite <- list_of_nat_nat_of_list; [ | easy ].
rewrite <- list_of_nat_nat_of_list; [ | easy ].
f_equal.
revert c.
induction al as [| a1]; intros.
 destruct (zerop c) as [Hc| Hc]; [ now subst c | ].
 unfold move_carry.
 rewrite nat_of_list_move_end; [ easy | easy | lia ].

 simpl; rewrite IHal; simpl.
 destruct al as [| a2].
  simpl.
  rewrite Nat.mul_comm; symmetry.
  now apply Nat.div_mod.

  specialize (Nat.div_mod (c + a1) rad Hrz) as H.
  simpl; lia.
Qed.

Lemma list_of_nat_inv {r : radix} : 1 < rad → ∀ c a b,
  list_of_nat c a = list_of_nat c b
  → a = b.
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hab.
unfold list_of_nat in Hab.
destruct (zerop a) as [Ha| Ha]; [ subst a | ].
 destruct (zerop b) as [Hb| Hb]; [ now subst b | easy ].

 destruct (zerop b) as [Hb| Hb]; [ easy | simpl in Hab ].
 injection Hab; clear Hab; intros Hab Hcab.
 destruct (zerop ((c + a) / rad)) as [Hzca| Hzca].
  apply Nat.div_small_iff in Hzca; [ | easy ].
  rewrite Nat.mod_small in Hcab; [ | easy ].
  destruct (zerop ((c + b) / rad)) as [Hzcb| Hzcb]; [ | easy ].
  apply Nat.div_small_iff in Hzcb; [ | easy ].
  rewrite Nat.mod_small in Hcab; [ lia | easy ].

  destruct (zerop ((c + b) / rad)) as [Hzcb| Hzcb]; [ easy | ].
  injection Hab; clear Hab; intros Hab Hcabr.
  apply move_carry_end_inv in Hab; [ | easy | | ].
   specialize (Nat.div_mod ((c + a) / rad) rad Hrz) as Habr.
   rewrite Hab, Hcabr in Habr.
   rewrite <- Nat.div_mod in Habr; [ | easy ].
   specialize (Nat.div_mod (c + a) rad Hrz) as Hapb.
   rewrite Hcab, Habr in Hapb.
   rewrite <- Nat.div_mod in Hapb; [ lia | easy ].

   now apply Nat.div_lt.

   now apply Nat.div_lt.
Qed.

Lemma move_carry_add_eq_compat {r : radix} : 1 < rad → ∀ al bl cl ca cb,
  list_norm (move_carry ca al) = list_norm (move_carry cb bl)
  → list_norm (move_carry ca (xnatv_add al cl)) =
     list_norm (move_carry cb (xnatv_add bl cl)).
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hab.
rewrite <- list_of_nat_nat_of_list; [ | easy ].
rewrite <- list_of_nat_nat_of_list; [ | easy ].
f_equal.
rewrite <- list_of_nat_nat_of_list in Hab; [ | easy ].
rewrite <- list_of_nat_nat_of_list in Hab; [ | easy ].
apply list_of_nat_inv in Hab; [ | easy ].

bbb.

rewrite move_carry_add; [ | easy ].
rewrite move_carry_add; [ | easy ].
rewrite move_carry_add in Hab; [ | easy ].
rewrite move_carry_add in Hab; [ | easy ].
simpl in Hab; simpl.
destruct al as [| a1].
 destruct bl as [| b1].
  destruct cl as [| c1]; [ easy | simpl ].
  unfold list_norm in Hab; simpl in Hab.
  unfold list_norm; simpl.

  unfold list_norm_with_carry in Hab.

bbb.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hab.
rewrite xnatv_add_comm; symmetry.
rewrite xnatv_add_comm; symmetry.
revert ca cb al bl Hab.
induction cl as [| c1]; intros; [ easy | simpl ].
destruct al as [| a1]; simpl.
 destruct bl as [| b1]; simpl.
  simpl in Hab.
  destruct (zerop ca) as [Hca| Hca].
   subst ca.
   now destruct (zerop cb); [ subst cb | ].

   destruct (zerop cb) as [| Hcb]; [ easy | ].
   injection Hab; clear Hab; intros Hab Hcab.
   f_equal.
    specialize (Nat.div_mod ca rad Hrz) as H.
    rewrite Hcab in H.
    rewrite Nat.add_comm, Nat.mul_comm in H.
    rewrite H, Nat.add_shuffle0.
    rewrite Nat.mod_add; [ | easy ].
    now apply Nat.add_mod_idemp_l.

    apply move_carry_end_inv in Hab; [ | easy | | ].
     specialize (Nat.div_mod ca rad Hrz) as H.
     rewrite Hab, Hcab in H.
     rewrite <- Nat.div_mod in H; [ | easy ].
     now subst ca.

     now apply Nat.div_lt.

     now apply Nat.div_lt.

  simpl in Hab.
  destruct (zerop ca) as [| Hca]; [ easy | ].
  injection Hab; clear Hab; intros Hab Hcab.
  remember ((cb + (c1 + b1)) mod rad) as x eqn:Hx.
  rewrite Nat.add_comm, Nat.add_shuffle0, <- Nat.add_assoc in Hx.
  rewrite <- Nat.add_mod_idemp_r in Hx; [ subst x | easy ].
  rewrite <- Hcab, Nat.add_mod_idemp_r; [ | easy ].
  rewrite Nat.add_comm; f_equal.
  destruct ca; [ easy | ].
  rewrite move_carry_end_enough_iter with (n := S (S ca / rad)) in Hab.
   specialize (IHcl (S ca / rad) ((cb + b1) / rad) [] bl Hab) as H.
   rewrite xnatv_add_comm in H; simpl in H.
   destruct cl as [| c2].
    simpl in H; simpl.
    destruct (zerop ((c1 + S ca) / rad)) as [Hccr| Hccr].
     destruct (zerop (S ca / rad)) as [Hcr| Hcr].
      rewrite <- H in Hab.
      apply eq_move_carry_end_nil in Hab.
      destruct Hab as [Har| Har]; [ easy | ].
      symmetry in H.
      apply eq_move_carry_nil in H.
      destruct H as (Hbl, Hmc).
      rewrite Hbl; symmetry.
      apply eq_move_carry_nil.
      split; [ easy | ].
      apply eq_move_carry_end_nil in Hmc.
      destruct Hmc as [Hmc| Hmc]; [ easy | ].
      apply eq_move_carry_end_nil; right.
      apply Nat.div_small_iff in Har; [ | easy ].
      rewrite Nat.mod_small in Hcab; [ | easy ].
      apply Nat.div_small_iff in Hmc; [ | easy ].
      rewrite Nat.mod_small in Hcab; [ | easy ].
      rewrite Nat.add_comm, Nat.add_shuffle0, <- Nat.add_assoc.
      now rewrite <- Hcab.

      destruct bl as [| b2].
       symmetry.
       apply eq_move_carry_nil.
       split; [ easy | ].
       apply eq_move_carry_end_nil; right.
       simpl in Hab.

bbb.

Lemma list_norm_wc_add_eq_compat {r : radix} : 1 < rad → ∀ al bl cl ca cb,
  list_norm_with_carry ca al = list_norm_with_carry cb bl
  → list_norm_with_carry ca (xnatv_add al cl) =
     list_norm_with_carry cb (xnatv_add bl cl).
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hab.
revert bl cl ca cb Hab.
induction al as [| a1]; intros.
 simpl; revert cl ca cb Hab.
 induction bl as [| b1]; intros.
  simpl in Hab; simpl.
  now apply list_norm_with_carry_inv in Hab; [ rewrite Hab | ].

  rewrite list_norm_wc_cons in Hab; [ | easy ].
  rewrite list_norm_wc_nil in Hab.
  remember (list_norm_with_carry ((cb + b1) / rad) bl) as b'l eqn:Hb'l.
  symmetry in Hb'l.
  destruct (zerop ca) as [Hca| Hca].
   subst ca.
   destruct b'l; [ | easy ].
   destruct (zerop ((cb + b1) mod rad)) as [Hzcb| Hzcb]; [ | easy ].
   apply eq_list_norm_wc_nil in Hb'l; [ | easy ].
   destruct Hb'l as (Hcbr, Hbl).
   rewrite Nat.mod_small in Hzcb; [ | now apply Nat.div_small_iff in Hcbr ].
   apply Nat.eq_add_0 in Hzcb.
   destruct Hzcb; subst cb b1.
   rewrite Nat.div_0_l in Hbl; [ simpl in Hbl | easy ].
   rewrite Hbl, <- List_repeat_succ.
   rewrite xnatv_add_rep_0_l.
   now rewrite list_norm_with_carry_app_rep_0.

   destruct b'l as [| b'1].
    apply eq_list_norm_wc_nil in Hb'l; [ | easy ].
    destruct Hb'l as (Hcbr, Hbl).
    destruct (zerop ((cb + b1) mod rad)) as [Hzcb| Hzcb].
     apply eq_list_rem_trail_nil in Hab.
     injection Hab; clear Hab; intros Hab Hcaz.
     rewrite Nat.mod_small in Hzcb; [ | now apply Nat.div_small_iff in Hcbr ].
     apply Nat.eq_add_0 in Hzcb; destruct Hzcb; subst cb b1.
     destruct ca; [ easy | ].
     simpl in Hab.
     destruct (zerop (S ca / rad)) as [Hzcr| Hzcr].
      apply Nat.div_small_iff in Hzcr; [ | easy ].
      now rewrite Nat.mod_small in Hcaz.

      injection Hab; clear Hab; intros Hab Hcrr.
      rewrite Hbl, <- List_repeat_succ.
      rewrite xnatv_add_rep_0_l.
      rewrite list_norm_with_carry_app_rep_0; [ | easy ].
      destruct ca; [ now rewrite Nat.mod_1_l in Hcaz | ].
      apply move_carry_end_succ_ne_rep_0 in Hab; [ easy | easy | ].
      split.
       apply Nat.mod_divides in Hcaz; [ | easy ].
       destruct Hcaz as (c, Hc); rewrite Nat.mul_comm in Hc.
       rewrite Hc, Nat.div_mul; [ | easy ].
       rewrite Hc in Hca.
       rewrite Hc, Nat.div_mul in Hzcr; [ | easy ].
       rewrite Hc, Nat.div_mul in Hcrr; [ | easy ].
       destruct c; [ easy | ].
       apply Nat.mod_divides in Hcrr; [ | easy ].
       destruct Hcrr as (d, Hd); rewrite Nat.mul_comm in Hd.
       rewrite Hd, Nat.div_mul; [ | easy ].
       destruct d; [ easy | lia ].

       apply Nat.div_lt_upper_bound; [ easy | ].
       apply Nat.div_lt_upper_bound; [ easy | ].
       destruct rad as [| s]; [ easy | ].
       destruct s; [ lia | simpl; lia ].

     apply Nat.div_small_iff in Hcbr; [ | easy ].
     rewrite Nat.mod_small in Hzcb; [ | easy ].
     rewrite Nat.mod_small with (a := cb + b1) in Hab; [ | easy ].
     destruct ca; [ easy | clear Hca ].
     destruct cb.
      simpl.
      rewrite Nat.add_0_l in Hcbr, Hbl, Hzcb, Hab.
      unfold list_norm_with_carry.
      rewrite Nat.div_small in Hbl; [ | easy ].
      remember (length (move_carry 0 bl)) as n eqn:Hn.
bbb.
      specialize (move_carry_cons_rep_0 b1 0 n Hr) as (m, Hm).
      rewrite Hbl.
      destruct b1; [ easy | ].
      remember list_remove_trailing_0s as f; simpl; subst f.
      destruct cl as [| c1].
       rewrite Hm, list_rem_trail_rep_0.
       remember list_remove_trailing_0s as f; simpl; subst f.
       remember (S b1 / rad) as x eqn:Hx.
       rewrite Nat.div_small in Hx; [ subst x | easy ].
       remember (S b1 mod rad) as x eqn:Hx.
       rewrite Nat.mod_small in Hx; [ subst x | easy ].
       remember list_remove_trailing_0s as f; simpl; subst f.
       remember list_remove_trailing_0s as f; simpl in Hab; subst f.
       now rewrite Hab.

       rewrite xnatv_add_rep_0_l.
       specialize
         (move_carry_app_rep_0 Hr 0 (S (b1 + c1) :: cl) (n - length cl)) as
         (p, Hp).
       rewrite <- List.app_comm_cons in Hp; rewrite Hp.
       rewrite list_rem_trail_rep_0.
       remember list_remove_trailing_0s as f; simpl; subst f.
       remember list_remove_trailing_0s as f; simpl in Hab; subst f.
       simpl in Hab.
       remember (S ca mod rad) as cr eqn:Hcr; symmetry in Hcr.
       destruct (zerop (S ca / rad)) as [Hzcr| Hzcr].
        destruct cr; [ easy | ].
        injection Hab; clear Hab; intros H; subst cr.
        apply Nat.div_small_iff in Hzcr; [ | easy ].
        rewrite Nat.mod_small in Hcr; [ | easy ].
        now apply Nat.succ_inj in Hcr; subst ca.

        destruct cr.
         now destruct
           (list_remove_trailing_0s
              ((S ca / rad) mod rad ::
               move_carry_end ca (S ca / rad / rad))).

         injection Hab; clear Hab; intros Hab H; subst cr.
         remember ((S ca / rad) mod rad) as car eqn:Hcar.
         symmetry in Hcar.
         destruct car; [ | easy ].
         remember
           (list_remove_trailing_0s (move_carry_end ca (S ca / rad / rad)))
           as al eqn:Hal.
         symmetry in Hal.
         destruct al; [ clear Hab | easy ].
         apply eq_list_rem_trail_nil in Hal.
         destruct ca; [ now rewrite Nat.div_1_l in Hzcr | ].
         apply move_carry_end_succ_ne_rep_0 in Hal; [ easy | easy | ].
         split.
          apply Nat.mod_divides in Hcar; [ | easy ].
          destruct Hcar as (d, Hd); rewrite Nat.mul_comm in Hd.
          rewrite Hd, Nat.div_mul; [ | easy ].
          destruct d; [ simpl in Hd | lia ].
          now rewrite Hd in Hzcr.

          apply Nat.div_lt_upper_bound; [ easy | ].
          apply Nat.div_lt_upper_bound; [ easy | ].
          destruct rad as [| s]; [ easy | ].
          destruct s; [ lia | simpl; lia ].

      simpl in Hab.
      remember (S ca mod rad) as car eqn:Hcar; symmetry in Hcar.
      destruct car.
       now destruct
         (list_remove_trailing_0s
            (if zerop (S ca / rad) then []
             else
               (S ca / rad) mod rad ::
                move_carry_end ca (S ca / rad / rad))).

       injection Hab; clear Hab; intros Hab Hcarb.
       subst car.
       destruct (zerop (S ca / rad)) as [Hcdr| Hcdr].
        apply Nat.div_small_iff in Hcdr; [ | easy ].
        rewrite Nat.mod_small in Hcar; [ | easy ].
        destruct cl as [| c1].
         simpl.
         rewrite list_norm_wc_nil.
         remember list_remove_trailing_0s as f; simpl; subst f.
         rewrite Nat.div_small; [ | easy ].
         remember list_remove_trailing_0s as f; simpl; subst f.
         rewrite Nat.mod_small; [ simpl | easy ].
         rewrite Hcar.
         unfold list_norm_with_carry.
Search (move_carry _ (_ :: _)).
bbb.
         rewrite Hbl.
         rewrite move_carry_cons_rep_0.

Search (list_norm_with_carry _ []).
        
bbb.
      rewrite list_norm_wc_cons_list_rem in Hab.
      simpl in Hab.
      unfold list_norm_with_carry.
bbb.
     apply move_carry_end_succ_ne_rep_0 in Hab; [ easy | easy | ].
     split.
      apply Nat.mod_divides in Hcr; [ | easy ].
      destruct Hcr as (d, Hd); rewrite Nat.mul_comm in Hd.
      rewrite Hd, Nat.div_mul in Hca; [ | easy ].
      rewrite Hd, Nat.div_mul; [ | easy ].
      apply Nat.mod_divides in Hca; [ | easy ].
      destruct Hca as (e, He); rewrite Nat.mul_comm in He.
      rewrite He, Nat.div_mul; [ | easy ].
      destruct e; [ now subst d | lia ].

      remember (S (c + a) / rad) as d eqn:Hd.
      apply Nat.div_lt_upper_bound; [ easy | ].
      destruct d; [ easy | ].
      destruct rad as [| s]; [ easy | ].
      destruct s; [ lia | simpl; lia ].

bbb.

     rewrite Nat.mod_small in Hzcb; [ | now apply Nat.div_small_iff in Hcbr ].
     apply Nat.eq_add_0 in Hzcb.
     destruct Hzcb; subst cb b1.
     rewrite Nat.div_0_l in Hbl; [ simpl in Hbl | easy ].
     rewrite Hbl, <- List_repeat_succ.
     rewrite xnatv_add_rep_0_l.
     rewrite list_norm_with_carry_app_rep_0.


bbb.
 destruct al as [| a2].
  simpl in Hmc.
  destruct (zerop (S (c + a) / rad)) as [Hsr| Hsr].
   now rewrite Nat.mod_small in Hcr; [ | apply Nat.div_small_iff ].

   destruct n; [ easy | simpl in Hmc ].
   injection Hmc; clear Hmc; intros Hmc Hca.
   apply move_carry_end_succ_ne_rep_0 in Hmc; [ easy | easy | ].
   split.
    apply Nat.mod_divides in Hcr; [ | easy ].
    destruct Hcr as (d, Hd); rewrite Nat.mul_comm in Hd.
    rewrite Hd, Nat.div_mul in Hca; [ | easy ].
    rewrite Hd, Nat.div_mul; [ | easy ].
    apply Nat.mod_divides in Hca; [ | easy ].
    destruct Hca as (e, He); rewrite Nat.mul_comm in He.
    rewrite He, Nat.div_mul; [ | easy ].
    destruct e; [ now subst d | lia ].

    remember (S (c + a) / rad) as d eqn:Hd.
    apply Nat.div_lt_upper_bound; [ easy | ].
    destruct d; [ easy | ].
    destruct rad as [| s]; [ easy | ].
    destruct s; [ lia | simpl; lia ].

  destruct n; [ easy | simpl in Hmc ].
  injection Hmc; clear Hmc; intros Hmc Hca.
bbb.

Theorem xnatv_add_eq_compat {r : radix} : ∀ a b c,
  (a = b)%X → (a + c = b + c)%X.
Proof.
intros * Hab.
unfold xnat_norm in Hab.
injection Hab; clear Hab; intros Hab.
unfold xnat_norm; f_equal.
unfold xnat_add; simpl.
unfold list_norm.
bbb.
