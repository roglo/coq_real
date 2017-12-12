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

Lemma eq_move_carry_end_nil {r : radix} : ∀ i c,
  move_carry_end i c = [] ↔ i = 0 ∨ c = 0.
Proof.
intros.
split; intros H.
 now destruct i; [ left | right; now destruct c ].

 destruct H; [ now subst i | now subst c; destruct i ].
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

Lemma nat_of_list_xnatv_add_distr {r : radix} : 1 < rad → ∀ al bl,
  nat_of_list 0 (xnatv_add al bl) = nat_of_list 0 al + nat_of_list 0 bl.
Proof.
intros Hr *.
revert bl.
induction al as [| a1]; intros; [ easy | simpl ].
destruct bl as [| b1]; [ now rewrite Nat.add_0_r | ].
simpl; rewrite IHal; lia.
Qed.

Lemma nat_of_list_add_eq_compat {r : radix} : 1 < rad → ∀ al bl cl,
  nat_of_list 0 al = nat_of_list 0 bl
  → nat_of_list 0 (xnatv_add al cl) = nat_of_list 0 (xnatv_add bl cl).
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hab.
rewrite nat_of_list_xnatv_add_distr; [ | easy ].
rewrite nat_of_list_xnatv_add_distr; [ | easy ].
now rewrite Hab.
Qed.

Theorem xnatv_add_eq_compat {r : radix} : 1 < rad → ∀ a b c,
  (a = b)%X → (a + c = b + c)%X.
Proof.
intros Hr * Hab.
unfold xnat_norm in Hab.
injection Hab; clear Hab; intros Hab.
unfold xnat_norm; f_equal.
unfold xnat_add; simpl.
rewrite <- list_of_nat_nat_of_list; [ | easy ].
rewrite <- list_of_nat_nat_of_list; [ | easy ].
f_equal.
rewrite <- list_of_nat_nat_of_list in Hab; [ | easy ].
rewrite <- list_of_nat_nat_of_list in Hab; [ | easy ].
apply list_of_nat_inv in Hab; [ | easy ].
now apply nat_of_list_add_eq_compat.
Qed.
