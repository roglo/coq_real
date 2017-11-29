(* Natural numbers in any radix; second version; without proofs *)
(* Can be regarded as polynomials with natural number coefficients. *)
(* Implemented using lists of nat. *)

Require Import Utf8 Arith Psatz List.
Import ListNotations.

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
  | [] =>
      if zerop carry then [] else move_carry_end (S carry) carry
  | a :: al' =>
      (carry + a) mod rad :: move_carry ((carry + a) / rad) al'
  end.

Definition list_of_nat {r : radix} carry n :=
  if zerop n then [] else move_carry carry [n].
Definition nat_of_list {r : radix} accu al :=
  List.fold_right (λ a accu, accu * rad + a) accu al.

Definition xnat_of_nat {r : radix} n := xn (list_of_nat 0 n).
Definition nat_of_xnat {r : radix} a := nat_of_list 0 (xnatv a).

Compute (@xnat_of_nat radix_10 0).
Compute (@xnat_of_nat radix_10 1).
Compute (@xnat_of_nat radix_10 2).
Compute (@xnat_of_nat radix_10 9).
Compute (@xnat_of_nat radix_10 10).
Compute (@xnat_of_nat radix_10 239).
Compute (@xnat_of_nat radix_2 0).
Compute (@xnat_of_nat radix_2 1).
Compute (@xnat_of_nat radix_2 2).
Compute (@xnat_of_nat radix_2 3).
Compute (@xnat_of_nat radix_2 4).
Compute (@xnat_of_nat radix_10 10030).
Compute (let n := 0 in let r := radix_2 in @move_carry_end r (S n) n).
Compute (let n := 1 in let r := radix_2 in @move_carry_end r (S n) n).
Compute (let n := 2 in let r := radix_2 in @move_carry_end r (S n) n).
Compute (let n := 3 in let r := radix_2 in @move_carry_end r (S n) n).

Compute (let n := 0 in let r := radix_2 in @nat_of_list r 0 (@move_carry_end r (S n) n)).
Compute (let n := 1 in let r := radix_2 in @nat_of_list r 0 (@move_carry_end r (S n) n)).
Compute (let n := 2 in let r := radix_2 in @nat_of_list r 0 (@move_carry_end r (S n) n)).
Compute (let n := 3 in let r := radix_2 in @nat_of_list r 0 (@move_carry_end r (S n) n)).
Compute (let n := 4 in let r := radix_2 in @nat_of_list r 0 (@move_carry_end r (S n) n)).

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

Lemma nat_of_list_inv {r : radix} : 2 ≤ rad →
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

Theorem nat_of_xnat_inv {r : radix} : 2 ≤ rad →
  ∀ n, nat_of_xnat (xnat_of_nat n) = n.
Proof.
intros Hr *.
now apply nat_of_list_inv.
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

Definition list_norm {r : radix} al :=
  list_remove_trailing_0s (move_carry 0 al).

Definition xnat_norm {r : radix} a := xn (list_norm (xnatv a)).

Compute (@xnat_norm radix_2 (xn [0; 0])).
Compute (@xnat_norm radix_2 (xn [1; 0])).
Compute (@xnat_norm radix_2 (xn [2; 0])).
Compute (@xnat_norm radix_2 (xn [3])).
Compute (@xnat_norm radix_2 (xn [4])).
Compute (@xnat_norm radix_2 (xn [5])).
Compute (@xnat_norm radix_2 (xn [6])).
Compute (@xnat_norm radix_2 (xn [7])).
Compute (@xnat_norm radix_10 (xn [11; 11; 11; 11; 11])).

Compute (@xnat_norm radix_2 (xn [11; 11; 11; 11; 11])).
Compute (@xnat_norm radix_2 (xn [341])).
Compute (@xnat_of_nat radix_2 341).
Compute (11 + 2 * 11 + 4 * 11 + 8 * 11 + 16 * 11).

Compute (@xnat_of_nat radix_10 341).
Compute (@nat_of_xnat radix_10 (@xnat_of_nat radix_10 341)).

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

Lemma move_carry_0_rep_0 {r : radix} : ∀ n,
  move_carry 0 (repeat 0 n) = repeat 0 n.
Proof.
intros.
induction n; [ easy | simpl ].
destruct (zerop rad) as [Hr| Hr].
 rewrite Hr; simpl.
 now f_equal.

 rewrite Nat.mod_0_l; [ f_equal | lia ].
 rewrite Nat.div_0_l; [ easy | lia ].
Qed.

Lemma list_norm_0 {r : radix} : list_norm [0] = [].
Proof.
intros.
unfold list_norm.
specialize (move_carry_0_rep_0 1) as H.
remember move_carry as f; simpl in H; subst f.
now rewrite H.
Qed.

Lemma eq_list_rem_trail_nil : ∀ al,
  list_remove_trailing_0s al = [] ↔ al = repeat 0 (length al).
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
  list_remove_trailing_0s (repeat 0 n) = [].
Proof.
intros.
apply eq_list_rem_trail_nil.
now rewrite List.repeat_length.
Qed.

Lemma eq_nat_of_list_0 {r : radix} : ∀ al, 0 < rad →
  nat_of_list 0 al = 0 ↔ al = repeat 0 (length al).
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

Lemma list_norm_cons_0 {r : radix} : ∀ al,
  list_norm al = [] → list_norm (0 :: al) = [].
Proof.
intros * Hal.
destruct (zerop rad) as [Hr| Hr].
 unfold list_norm in Hal.
 unfold list_norm; simpl; rewrite Hr; simpl.
 now rewrite Hal.

 unfold list_norm in Hal.
 apply eq_list_rem_trail_nil in Hal.
 apply eq_list_rem_trail_nil; simpl.
 rewrite Nat.mod_0_l; [ | lia ].
 rewrite Nat.div_0_l; [ | lia ].
 now f_equal.
Qed.

Theorem List_cons_comm_app : ∀ A (x : A) l l', l ++ x :: l' = l ++ [x] ++ l'.
Proof. easy. Qed.

Lemma list_rem_trail_rep_0 : ∀ al n,
  list_remove_trailing_0s (al ++ repeat 0 n) = list_remove_trailing_0s al.
Proof.
intros.
revert al.
induction n; intros; [ now rewrite List.app_nil_r | simpl ].
rewrite List_cons_comm_app, List.app_assoc.
rewrite IHn; clear.
induction al as [| a]; [ easy | now simpl; rewrite IHal ].
Qed.

Lemma last_cons_cons : ∀ A (a b : A) al d,
  last (a :: b :: al) d = last (b :: al) d.
Proof. easy. Qed.

Lemma last_cons_id : ∀ A (a : A) al,
  last al a ≠ a
  → last (a :: al) a ≠ a.
Proof.
intros * Hal.
now destruct al.
Qed.

Lemma last_cons_ne : ∀ A (a d : A) al,
  a ≠ d
  → last al d ≠ d
  → last (a :: al) d ≠ d.
Proof.
intros * Had Hal.
revert a Had.
induction al as [| a1]; intros; [ easy | ].
rewrite last_cons_cons.
simpl in Hal.
destruct al as [| a2]; [ easy | ].
now rewrite last_cons_cons.
Qed.

Lemma list_rem_trail_iff : ∀ al bl,
  list_remove_trailing_0s al = bl
  ↔ (∃ n, al = bl ++ repeat 0 n) ∧ (bl = [] ∨ List.last bl 0 ≠ 0).
Proof.
intros *.
split.
 intros Hb.
 split.
  revert bl Hb.
  induction al as [| a]; intros; [ now exists 0; subst bl | ].
  subst bl; simpl.
  remember (list_remove_trailing_0s al) as cl eqn:Hcl in |-*.
  symmetry in Hcl.
  specialize (IHal cl Hcl) as (m, Hm); subst al.
  destruct a; [ | now exists m ].
  now destruct cl; [ exists (S m) | exists m ].

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

  intros ((n, Hn), Hbl).
  destruct Hbl as [| Hbl].
   subst al bl; simpl.
   apply list_rem_trail_repeat_0.

   subst al.
   induction bl as [| b]; [ easy | ].
   simpl in Hbl.
bbb.

Search list_remove_trailing_0s.
   apply list_rem_trail_rep_0.

bbb.

  injection Hb; clear Hb; intros Hbl H; subst b.
  specialize (IHal bl Hbl) as (m & Hal & Hm).
  exists m.
  split; [ now rewrite Hal | right ].
  destruct Hm as [Hm| Hm]; [ now rewrite Hm | simpl ].
  now destruct bl.
bbb.
intros *.
split.
 intros Hb.
 revert bl Hb.
 induction al as [| a]; intros.
  subst bl; simpl.
  exists 0.
  split; [ easy | now left ].

  simpl in Hb.
  destruct a.
   remember (list_remove_trailing_0s al) as cl eqn:Hcl in Hb.
   symmetry in Hcl.
   destruct cl as [| c].
    subst bl; simpl.
    apply eq_list_rem_trail_nil in Hcl.
    rewrite Hcl.
    exists (S (length al)).
    split; [ easy | now left ].

    specialize (IHal (c :: cl) Hcl) as (m & Hal & Hm).
    destruct Hm as [Hm| Hm]; [easy | ].
    exists m.
    split; [ now rewrite Hal, <- Hb | right ].
    now subst bl; remember (c :: cl) as dl; simpl; subst dl.

   destruct bl as [| b]; [ easy | ].
   injection Hb; clear Hb; intros Hbl H; subst b.
   specialize (IHal bl Hbl) as (m & Hal & Hm).
   exists m.
   split; [ now rewrite Hal | right ].
   destruct Hm as [Hm| Hm]; [ now rewrite Hm | simpl ].
   now destruct bl.

 intros (n & Hal & Hbl).
 destruct Hbl as [Hbl| Hbl].
  subst al bl; simpl.
  apply eq_list_rem_trail_nil.
  now rewrite repeat_length.

  subst al.
  rewrite list_rem_trail_rep_0.
  induction bl as [| b1]; [ easy | simpl in Hbl; simpl ].
  destruct b1.
   now destruct bl as [| b2]; [ | rewrite IHbl ].
   now destruct bl as [| b2]; [ | rewrite IHbl ].
Qed.

Lemma move_carry_end_succ_ne_rep_0 {r : radix} : ∀ i c n, 1 < rad →
  0 < c < i
  → move_carry_end i c ≠ repeat 0 n.
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

Lemma move_nz_carry {r : radix} : ∀ al n c, 1 < rad → c ≠ 0 →
  move_carry c al ≠ repeat 0 n.
Proof.
intros * Hr Hc H.
destruct c; [ easy | clear Hc ].
revert c n H.
induction al as [| a]; intros.
 unfold move_carry in H.
 remember move_carry_end as f; simpl in H; subst f.
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
  move_carry 0 al = repeat 0 n → al = repeat 0 n.
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

Lemma List_app_rep_0_last : ∀ al m n,
  repeat 0 m = al ++ repeat 0 n
  → last al 0 = 0.
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

Lemma List_repeat_succ_app : ∀ A (a : A) n,
  repeat a (S n) = repeat a n ++ [a].
Proof.
intros; simpl.
induction n; [ easy | simpl ].
now rewrite <- IHn.
Qed.

Lemma move_carry_rep_0_end {r : radix} : ∀ n a, 1 < rad → ∃ m,
  move_carry a (repeat 0 n) = move_carry_end (S a) a ++ repeat 0 m.
Proof.
intros * Hr.
revert a.
induction n; intros; simpl.
 destruct (zerop a); [ now exists 0 | ].
 exists 0; simpl.
 now rewrite List.app_nil_r.

 rewrite Nat.add_0_r.
 destruct (zerop a) as [Ha| Ha].
  subst a.
  rewrite Nat.mod_0_l; [ | lia ].
  rewrite Nat.div_0_l; [ | lia ].
  exists (S n).
  now rewrite move_carry_0_rep_0.

  simpl.
  specialize (IHn (a / rad)) as (m & Hm).
  exists m.
  rewrite Hm.
  f_equal; f_equal.
  apply move_carry_end_enough_iter; [ easy | lia | ].
  destruct a; [ easy | ].
  destruct rad as [| s]; [ easy | ].
  destruct s; [ lia | ].
  now apply Nat.div_lt.
Qed.

Lemma move_carry_rep_0 {r : radix} : ∀ n a, 1 < rad → ∃ m,
  move_carry a (repeat 0 n) = move_carry a [] ++ repeat 0 m.
Proof.
intros * Hr.
unfold move_carry at 2.
destruct (zerop a) as [Ha| Ha].
 exists n; subst a; simpl.
 apply move_carry_0_rep_0.

 now apply move_carry_rep_0_end.
Qed.

Lemma move_carry_cons_rep_0 {r : radix} : ∀ a c n, 1 < rad → ∃ m,
  move_carry c (a :: repeat 0 n) = move_carry c [a] ++ repeat 0 m.
Proof.
intros * Hr; simpl.
destruct (zerop ((c + a) / rad)) as [Hca| Hca].
 exists n; rewrite Hca; simpl; f_equal.
 apply move_carry_0_rep_0.

 specialize (move_carry_rep_0 n ((c + a) / rad) Hr) as (m & Hm).
 exists m; f_equal.
 rewrite Hm; f_equal.
 simpl.
 destruct (zerop ((c + a) / rad)) as [H| H]; [ lia | easy ].
Qed.

Lemma move_carry_cons {r : radix} : ∀ a al c,
  move_carry c (a :: al) = (c + a) mod rad :: move_carry ((c + a) / rad) al.
Proof. easy. Qed.

Lemma last_move_carry_end {r : radix} : ∀ i c, 1 < rad → 0 < c < i →
  last (move_carry_end i c) 0 ≠ 0.
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
  c = 0 ∨ last (move_carry_end i c) 0 ≠ 0.
Proof.
intros * Hr Hci.
destruct c; [ now left | right ].
apply last_move_carry_end; [ easy | ].
split; [ lia | easy ].
Qed.

Lemma last_move_carry_single_nz {r : radix} : ∀ a c, 1 < rad → a ≠ 0 →
  last (move_carry c [a]) 0 ≠ 0.
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

Lemma nat_of_list_0_rep_0 {r : radix} : ∀ n, nat_of_list 0 (repeat 0 n) = 0.
Proof.
intros.
induction n; [ easy | simpl; now rewrite IHn ].
Qed.

Lemma nat_of_list_0_cons_rep_0 {r : radix} : ∀ a n,
  nat_of_list 0 (a :: repeat 0 n) = a.
Proof.
intros; simpl.
now rewrite nat_of_list_0_rep_0.
Qed.

Lemma last_cons_move_carry_end {r : radix} : ∀ x y n,
  2 ≤ rad
  → y = (n + x) / rad ^ n
  → 0 < y
  → last (y mod rad :: move_carry_end x (y / rad)) 0 ≠ 0.
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

Lemma list_of_nat_inv {r : radix} : 2 ≤ rad →
  ∀ al, list_of_nat 0 (nat_of_list 0 al) = list_norm al.
Proof.
intros Hr *.
assert (Hrz : rad ≠ 0) by lia.
induction al as [| a]; [ easy | simpl ].
unfold list_of_nat in IHal; symmetry in IHal.
unfold list_of_nat.
destruct (zerop (nat_of_list 0 al)) as [Ha| Ha].
 rewrite Ha, Nat.mul_0_l, Nat.add_0_l.
 apply eq_nat_of_list_0 in Ha; [ | lia ].
 destruct (zerop a) as [Haz| Hanz].
  subst a; simpl; symmetry.
  now apply list_norm_cons_0.

  rewrite Ha.
  unfold list_norm.
  specialize (move_carry_cons_rep_0 a 0 (length al) Hr) as (m & Hm).
  rewrite Hm, list_rem_trail_rep_0; symmetry.
  apply list_rem_trail_iff.
  exists 0.
  remember move_carry as f; simpl; subst f.
  split; [ now rewrite List.app_nil_r | right ].
  apply last_move_carry_single_nz; [ easy | lia ].

 destruct (zerop (nat_of_list 0 al * rad + a)) as [Hn| Hn].
  apply Nat.eq_add_0 in Hn.
  destruct Hn as (Hn, _).
  apply Nat.eq_mul_0 in Hn.
  destruct Hn; [ lia | easy ].

  unfold list_norm in IHal.
  apply list_rem_trail_iff in IHal.
  destruct IHal as (n & IHal & Hm).
  destruct Hm as [Hm| Hm]; [ now rewrite move_carry_cons in Hm | ].
  symmetry; unfold list_norm.
  apply list_rem_trail_iff.
  rewrite move_carry_cons, Nat.add_0_l.
  simpl.
  rewrite Nat.add_comm.
  rewrite Nat.mod_add; [ f_equal | easy ].
  rewrite Nat.div_add; [ | easy ].
  destruct (zerop (a / rad + nat_of_list 0 al)) as [Han| Han].
   apply Nat.eq_add_0 in Han; lia.

   destruct al as [| a1].
    simpl in Han; simpl.
    rewrite Nat.add_0_r in Han |- *.
    now destruct (zerop (a / rad)).

    simpl in Han; simpl.
    remember ((a / rad + (nat_of_list 0 al * rad + a1)) mod rad) as x eqn:Hx.
    rewrite <- Nat.add_mod_idemp_r in Hx; [ | easy ].
    remember ((nat_of_list 0 al * rad + a1) mod rad) as y eqn:Hy.
    rewrite Nat.add_comm in Hy.
    rewrite Nat.mod_add in Hy; [ subst x y | easy ].
    rewrite Nat.add_mod_idemp_r; [ | easy ].
    simpl in IHal.
    rewrite <- Nat.add_mod_idemp_l in IHal; [ | easy ].
    rewrite Nat.mod_mul in IHal; [ | easy ].
    rewrite Nat.add_0_l in IHal.
    injection IHal; clear IHal; intros IHal.
    rewrite Nat.div_add_l in IHal; [ | easy ].
    destruct (zerop (nat_of_list 0 al + a1 / rad)) as [Hz| Hz].
     apply Nat.eq_add_0 in Hz.
     destruct Hz as (Hna, Hz).
     rewrite Hna, Nat.mul_0_l, Nat.add_0_l.
     rewrite Hz in IHal; simpl in IHal.
     apply move_carry_0_is_rep_0 in IHal; [ | easy ].
     destruct n.
      exists 0.
      rewrite List.app_nil_r.
      simpl in IHal; subst al.
      destruct (zerop ((a / rad + a1) / rad)) as [Har| Har].
       rewrite Har.
       split; [ now destruct (a / rad + a1) | right ].
       simpl in Han, Hn.
       apply Nat.div_small_iff in Har; [ | easy ].
       remember (move_carry_end (a / rad + a1) 0) as al eqn:Hal.
       symmetry in Hal.
       destruct al; [ | now destruct (a / rad + a1) ].
       rewrite Nat.mod_small; [ lia | easy ].

       simpl in Hm.
       rewrite Hz in Hm; simpl in Hm.
       simpl in Ha, Hn, Han.
       remember (a / rad + a1) as x eqn:Hx.
       symmetry in Hx.
       destruct x; [ easy | simpl ].
       destruct (zerop (S x / rad)) as [H| H]; [ lia | clear H ].
       split; [ | right ].
        f_equal; f_equal; f_equal.
        apply move_carry_end_enough_iter; [ easy | now apply Nat.div_lt | ].
        apply lt_le_trans with (m := S x / rad); [ now apply Nat.div_lt | ].
        apply Nat.div_le_upper_bound; [ easy | ].
        destruct rad as [| s]; [ easy | ].
        destruct s; [ easy | ].
        destruct x; [ easy | simpl; lia ].

        apply last_cons_move_carry_end with (n := 1); [ easy | | easy ].
        now rewrite Nat.pow_1_r.

      simpl in Ha, Hn; clear Hm.
      rewrite Hna, Nat.mul_0_l, Nat.add_0_l in Han, Ha, Hn.
      apply Nat.div_small_iff in Hz; [ | easy ].
      specialize (move_carry_rep_0_end (S n) ((a / rad + a1) / rad) Hr) as H.
      destruct H as (m, Hm).
      rewrite <- IHal in Hm; rewrite Hm.
      exists m.
      split; [ | right ].
       f_equal; f_equal; f_equal.
       apply move_carry_end_enough_iter; [ easy | lia | ].
       now apply Nat.div_lt.

       remember (move_carry_end (a / rad + a1) ((a / rad + a1) / rad)) as bl.
       rename Heqbl into Hbl; symmetry in Hbl.
       remember (a / rad + a1) as a2 eqn:Ha2.
       symmetry in Ha2.
       destruct a2; [ easy | clear Han ].
       remember (S a2 / rad) as a3 eqn:Ha3.
       symmetry in Ha3.
       simpl in Hbl; subst bl.
       destruct (zerop a3) as [Hz3| Hz3].
        subst a3.
        apply Nat.div_small_iff in Hz3; [ now rewrite Nat.mod_small | easy ].

        apply last_cons_move_carry_end with (n0 := 1); [ easy | | easy ].
        now rewrite Nat.pow_1_r.

     simpl; simpl in Hn.
     remember (nat_of_list 0 al * rad + a1) as a2 eqn:Ha2.
     destruct al as [| a3].
      simpl in Ha2, Hz; subst a2.
      simpl in IHal; simpl.
      destruct (zerop (a1 / rad)) as [H| H]; [ easy | clear H ].
      remember ((a / rad + a1) / rad) as a3 eqn:Ha3.
      symmetry in Ha3.
      remember (a / rad + a1) as a4 eqn:Ha4.
      symmetry in Ha4.
      destruct a3.
       exists 0; simpl.
       split; [ now destruct a4 | right ].
       destruct a4; [ easy | simpl ].
       apply Nat.div_small_iff in Ha3; [ | easy ].
       now rewrite Nat.mod_small.

       simpl.
       destruct (zerop (S a3 / rad)) as [Haz3 | Haz3].
        generalize Haz3; intros H.
        apply Nat.div_small_iff in Haz3; [ | easy ].
        rewrite Nat.mod_small with (a := S a3); [ | easy ].
        exists 0.
        split.
         destruct a4; [ easy | simpl ].
         rewrite Nat.mod_small with (a := S a3); [ | easy ].
         destruct a4; [ easy | simpl ].
         now rewrite H.

         right.
         destruct a4; [ easy | simpl ].
         destruct a4; [ now rewrite Nat.div_1_l in Ha3 | simpl ].
         rewrite H; simpl.
         now rewrite Nat.mod_small.

        exists 0; simpl; rewrite List.app_nil_r.
        split.
         destruct a4; [ easy | simpl ].
         f_equal; f_equal; f_equal.
         destruct a4; [ now rewrite Nat.div_1_l in Ha3 | simpl ].
         destruct (zerop (S a3 / rad)) as [H| H]; [ lia | clear H ].
         f_equal.
         destruct a4.
          rewrite <- Ha3 in Haz3.
          destruct rad as [| s]; [ easy | ].
          destruct s; [ lia | ].
          destruct s; [ easy | ].
          now rewrite Nat.div_small in Ha3.

          apply move_carry_end_enough_iter; [ easy | | ].
           apply Nat.div_lt_upper_bound; [ easy | ].
           apply Nat.div_lt_upper_bound; [ easy | ].
           destruct rad as [| s]; [ easy | ].
           destruct s; [ lia | ].
           destruct a3; [ easy | ].
           destruct s; [ lia | simpl; lia ].

           rewrite <- Ha3.
           apply Nat.div_lt_upper_bound; [ easy | ].
           apply Nat.div_lt_upper_bound; [ easy | ].
           apply Nat.div_lt_upper_bound; [ easy | ].
           destruct rad as [| s]; [ easy | ].
           destruct s; [ lia | ].
           destruct s; [ lia | simpl; lia ].

         right.
         destruct a4; [ easy | simpl ].
         destruct a4; [ now rewrite Nat.div_1_l in Ha3 | simpl ].
         destruct (zerop (S a3 / rad)) as [H| H]; [ lia | clear H ].
         apply last_cons_move_carry_end with (n0 := 2); [ easy | | easy ].
         simpl; rewrite Nat.mul_1_r.
         now rewrite <- Ha3, Nat.div_div.

      simpl in Ha2.
      simpl in Ha; rewrite <- Ha2 in Ha.
      simpl in Hm; rewrite <- Ha2 in Hm.
      destruct (zerop (a2 / rad)) as [Har2| Har2].
       simpl.
       remember (a / rad + a2) as a4 eqn:Ha4.
       remember ((a / rad + a1) / rad + a3) as a5 eqn:Ha5.
       symmetry in Ha4, Ha5.
       destruct a5.
        rewrite Nat.mod_0_l; [ | easy ].
        rewrite Nat.div_0_l; [ | easy ].
        destruct a4; [ easy | simpl ].
        destruct (S a4 / rad) as [Har4| Har4].
        simpl.
(*
        destruct (Forall_dec (eq 0) (Nat.eq_dec 0) al) as [Haz| Hnaz].
         exists (1 + length al).
         split.
          simpl; f_equal; f_equal; f_equal.
          clear - Hr Hrz Haz.
          induction Haz as [| a al]; [ easy | subst a; simpl ].
          rewrite Nat.mod_0_l; [ | easy ].
          rewrite Nat.div_0_l; [ now f_equal | easy ].

          right.
          apply Nat.eq_add_0 in Ha5.
          destruct Ha5 as (Harr, Ha3); subst a3.
          apply Nat.div_small_iff in Harr; [ | easy ].
          rewrite Nat.mod_small; [ | easy ].
          assert (nat_of_list 0 al = 0).
           clear - Haz.
           induction al as [| a]; [ easy | simpl ].
           inversion_clear Haz; subst a.
           rewrite Nat.add_0_r.
           apply Nat.eq_mul_0; left.
           now apply IHal.

           rewrite H in Ha2; simpl in Ha2; subst a2.
           now rewrite Ha4.

         exfalso.
         apply Exists_Forall_neg in Hnaz.
         apply Exists_exists in Hnaz.
         destruct Hnaz as (x & Hxal & Hx).
         apply List.in_split in Hxal.
         destruct Hxal as (al1 & al2 & Hxal).
         subst al.
bbb.
*)
         exists (1 + List.length al).
bbb.

         destruct al as [| a6]; [ easy | simpl ].


         simpl.
         split; [ easy | right ].
         apply Nat.eq_add_0 in Ha5.
         destruct Ha5 as (Ha5, Ha3); subst a3.
         apply Nat.div_small_iff in Ha5; [ | easy ].
         rewrite Nat.mod_small; [ | easy ].
         simpl in Hz.
         destruct a1; [ now rewrite Nat.div_0_l in Hz | ].
         simpl in Ha2; subst a2.
         now rewrite Ha4.

         simpl.
         destruct a6.
          rewrite Nat.mod_0_l; [ | easy ].
          rewrite Nat.div_0_l; [ | easy ].
          simpl in Ha2, Hz, IHal.
          rewrite Nat.add_0_r in Ha2, Hz, IHal.
          destruct al as [| a7].
           exists 2.
bbb.

Theorem xnat_of_nat_inv {r : radix} : 2 ≤ rad →
  ∀ a, xnat_of_nat (nat_of_xnat a) = xnat_norm a.
Proof.
intros Hr *.
now apply list_of_nat_inv.
Qed.

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
  xnat_norm (xn (xnatv_add (xnatv a) (xnatv b))).

Theorem xnat_of_nat_inv {r : radix} : ∀ a, a = xnat_of_nat (nat_of_xnat a).
bbb.

Compute (xnatv_add [2] [2]).
Compute (@xnat_add radix_10 (xn [4; 2]) (xn [11])).
Compute (@xnat_add radix_2 (xn [4; 2]) (xn [11])).
