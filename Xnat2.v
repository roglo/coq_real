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

Lemma list_norm_0 {r : radix} : list_norm [0] = [].
Proof.
intros.
unfold list_norm, list_norm_with_carry.
specialize (move_carry_0_rep_0 1) as H.
remember move_carry as f; simpl in H; subst f.
now rewrite H.
Qed.

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

Lemma list_rem_trail_repeat_0 : ∀ n,
  list_remove_trailing_0s (List.repeat 0 n) = [].
Proof.
intros.
apply eq_list_rem_trail_nil.
now rewrite List.repeat_length.
Qed.

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

Theorem List_cons_comm_app : ∀ A (x : A) l l', l ++ x :: l' = l ++ [x] ++ l'.
Proof. easy. Qed.

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

Lemma last_cons_cons : ∀ A (a b : A) al d,
  List.last (a :: b :: al) d = List.last (b :: al) d.
Proof. easy. Qed.

Lemma last_cons_id : ∀ A (a : A) al,
  List.last al a ≠ a
  → List.last (a :: al) a ≠ a.
Proof.
intros * Hal.
now destruct al.
Qed.

Lemma last_cons_ne : ∀ A (a d : A) al,
  a ≠ d
  → List.last al d ≠ d
  → List.last (a :: al) d ≠ d.
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
  ↔ (∃ n, al = bl ++ List.repeat 0 n) ∧ (bl = [] ∨ List.last bl 0 ≠ 0).
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
   rewrite list_rem_trail_rep_0.
   induction bl as [| b1]; [ easy | ].
   simpl in Hbl; simpl.
   destruct bl as [| b2]; [ now destruct b1 | ].
   specialize (IHbl Hbl); rewrite IHbl.
   now destruct b1.
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

Fixpoint logn_loop {r : radix} iter a :=
  match iter with
  | 0 => 0
  | S i => if zerop a then 0 else S (logn_loop i (a / rad))
  end.

Definition logn {r : radix} a := logn_loop a a - 1.

Lemma logn_loop_div_small {r : radix} : ∀ n i,
  n < rad → logn_loop i n - 1 = 0.
Proof.
intros * Hnr.
revert n Hnr.
induction i; intros; [ easy | simpl ].
destruct (zerop n) as [Hn| Hn]; [ easy | ].
 assert (Hnrr : n / rad < rad).
  apply Nat.div_lt_upper_bound; [ now destruct rad | ].
  destruct rad; [ easy | simpl; lia ].

  specialize (IHi (n / rad) Hnrr ) as H.
  remember (logn_loop i (n / rad)) as m eqn:Hm; symmetry in Hm.
  destruct m; [ easy | ].
  simpl in H; simpl.
  exfalso; rewrite Nat.sub_0_r in H; subst m.
  destruct i; [ easy | ].
  simpl in Hm.
  destruct (zerop (n / rad)); [ easy | ].
  apply Nat.div_small in Hnr.
  now rewrite Hnr in l.
Qed.

Lemma logn_small {r : radix} : ∀ n, n < rad → logn n = 0.
Proof.
intros * Hnr.
unfold logn.
now apply logn_loop_div_small.
Qed.

Lemma logn_loop_enough_iter {r : radix} : 1 < rad → ∀ n i j,
  n ≤ i
  → n ≤ j
  → logn_loop i n = logn_loop j n.
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hni Hnj.
revert n j Hni Hnj.
induction i; intros.
 apply Nat.le_0_r in Hni; subst n.
 now destruct j.

 destruct n; [ now destruct j | simpl ].
 destruct (le_dec (S n) i) as [Hsni| Hsni].
  symmetry.
  rewrite <- IHi; [ | easy | easy ].
  clear - Hr Hrz Hsni.
  revert n Hsni.
  induction i; intros; [ easy | simpl ].
  destruct (zerop (S n / rad)) as [Hsnr| Hsnr].
   now rewrite Hsnr; destruct i.

   f_equal.
   remember (S n / rad) as m eqn:Hm; symmetry in Hm.
   destruct m; [ easy | ].
   apply IHi.
   rewrite <- Hm.
   apply Nat.div_le_upper_bound; [ easy | ].
   eapply Nat.le_trans; [ eassumption | ].
   destruct i.
    apply Nat.succ_le_mono in Hsni.
    apply Nat.le_0_r in Hsni; subst n.
    now rewrite Nat.div_1_l in Hm.

    destruct rad as [| s]; [ easy | ].
    destruct s; [ lia | simpl; lia ].

  apply Nat.nle_gt in Hsni.
  unfold lt in Hsni.
  apply Nat.le_antisymm in Hsni; [ | easy ].
  destruct j; [ easy | simpl ].
  f_equal.
  destruct i.
   apply Nat.succ_le_mono in Hni.
   apply Nat.succ_inj in Hsni; subst n; simpl.
   rewrite Nat.div_1_l; [ | easy ].
   now destruct j.

   apply IHi.
    apply Nat.div_le_upper_bound; [ easy | ].
    eapply Nat.le_trans; [ apply Hni | ].
    destruct rad as [| s]; [ easy | ].
    destruct s; [ lia | simpl; lia ].

    apply Nat.div_le_upper_bound; [ easy | ].
    destruct j; [ lia | ].
    eapply Nat.le_trans; [ apply Hnj | ].
    destruct rad as [| s]; [ easy | ].
    destruct s; [ lia | simpl; lia ].
Qed.

Lemma logn_succ {r : radix} : ∀ n,
  logn (S n) = if zerop (S n mod rad) then S (logn n) else logn n.
Proof.
intros.
destruct (zerop (S n mod rad)) as [Hnr| Hnr].
 rewrite Nat.mod_divides in Hnr.
 destruct Hnr as (d, Hd); rewrite Nat.mul_comm in Hd.
 rewrite Hd.

Lemma logn_loop_mul_rad_r {r : radix} : 1 < rad → ∀ n i j, n ≠ 0 →
  n * rad ≤ i → n ≤ j →
  logn_loop i (n * rad) - 1 = logn_loop j n.
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hn Hni Hnj.
revert n j Hn Hni Hnj.
induction i; intros.
 apply Nat.le_0_r in Hni.
 apply Nat.eq_mul_0 in Hni.
 now destruct Hni.

 simpl.
 destruct (zerop (n * rad)) as [Hnr| Hnr].
  apply Nat.eq_mul_0 in Hnr.
  now destruct Hnr.

  rewrite Nat.div_mul; [ | easy ].
  rewrite Nat.sub_succ, Nat.sub_0_r.
  apply logn_loop_enough_iter; [ easy | | easy ].
  apply Nat.succ_le_mono.
  eapply Nat.le_trans; [ | eassumption ].
  rewrite Nat.mul_comm.
  destruct n; [ easy | ].
  destruct rad as [| s]; [ easy | ].
  destruct s; [ lia | simpl; lia ].
Qed.

Lemma logn_mul_rad_r {r : radix} : ∀ n, n ≠ 0 →
  logn (n * rad) = S (logn n).
Proof.
intros * Hn.
unfold logn; simpl.
rewrite <- Nat.sub_succ_l.
 2: destruct n; [ easy | simpl; lia ].
 rewrite Nat.sub_succ, Nat.sub_0_r.
 apply logn_loop_mul_rad_r.
bbb.


destruct n; [ easy | clear Hn ].
unfold logn.
remember (S n) as sn; simpl; subst sn.
bbb.

Lemma logn_div_rad_r {r : radix} : rad ≠ 0 → ∀ n, logn (n / rad) = logn n - 1.
Proof.
intros Hr *.
destruct n; [ now unfold logn; rewrite Nat.div_0_l | ].
rewrite logn_succ.
destruct (zerop (S n mod rad)) as [Hnr| Hnr].
 rewrite Nat.mod_divides in Hnr.
 destruct Hnr as (d, Hd); rewrite Nat.mul_comm in Hd.
 rewrite Hd, Nat.div_mul.
 rewrite Nat.sub_succ, Nat.sub_0_r.
 destruct d; [ easy | ].

bbb.

unfold logn.
Lemma logn_loop_div_rad_r {r : radix} : rad ≠ 0 → ∀ n i j,
  n / rad ≤ i
  → n ≤ j
  → logn_loop i (n / rad) = logn_loop j n - 1.
Proof.
intros Hr * Hni Hnj.
revert j n Hni Hnj.
induction i; intros.
 simpl.
 destruct j; [ easy | simpl ].
 destruct (zerop n) as [Hn| Hn]; [ easy | ].
 apply Nat.le_0_r in Hni.
 apply Nat.div_small_iff in Hni.
 simpl.
bbb.

; [ rewrite logn_loop_div_small | ].

 simpl.
 destruct (zerop (n / rad)) as [Hznr| Hznr].
  rewrite logn_loop_div_small.

bbb.

now rewrite logn_loop_div_rad_r with (j := n).
bbb.

Lemma logn_div_rad_r {r : radix} : ∀ n, n ≠ 0 → logn n = S (logn (n / rad)).
Proof.
intros * Hn.
unfold logn.
Lemma logn_loop_div_rad_r {r : radix} : ∀ n i j,
  n ≠ 0 → logn_loop i n - 1 = S (logn_loop j n - 1).
Proof.
intros * Hn.
revert n j Hn.
induction i; intros.
 simpl.
bbb.

(*
Lemma logn_div : ∀ n a b, b ≠ 0 → logn n (a / b) = logn n a - logn n b.
Proof.
intros * Hb.
revert b Hb.
induction a; intros; [ now rewrite Nat.div_0_l | ].

Lemma logn_succ : ∀ n a,
  logn n (S a) = if zerop (S a mod n) then logn n a else S (logn n a).
Proof.
intros.
destruct (zerop (S a mod n)) as [Han| Han].
 destruct n.
  now destruct a; [ | destruct a ].

  apply Nat.mod_divides in Han; [ | easy ].
  destruct Han as (c, Hc).
  rewrite Hc.
  unfold logn.
  simpl.
bbb.
*)

Lemma move_carry_rep_0_end {r : radix} : 1 < rad → ∀ n a,
  move_carry a (List.repeat 0 n) =
  move_carry_end (S a) a ++ List.repeat 0 (n - logn rad a).
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros.
revert a.
induction n; intros.
 now simpl; destruct (zerop a); [ | rewrite List.app_nil_r ].

 remember minus as f; simpl; subst f.
 rewrite Nat.add_0_r.
 destruct (zerop a) as [Ha| Ha].
  subst a.
  rewrite Nat.mod_0_l; [ | lia ].
  rewrite Nat.div_0_l; [ | lia ].
  now rewrite move_carry_0_rep_0.

  remember minus as f; simpl; subst f.
  rewrite IHn; f_equal.
  f_equal.
   apply move_carry_end_enough_iter; [ easy | lia | ].
   destruct a; [ easy | ].
   destruct rad as [| s]; [ easy | ].
   destruct s; [ lia | now apply Nat.div_lt ].

   f_equal.
   rewrite <- Nat.sub_succ.
   now rewrite <- logn_div_rad_r.
bbb.
   specialize (Nat.div_mod a rad Hrz) as H.
   rewrite Nat.add_comm, Nat.mul_comm in H.
   rewrite H at 1.
   rewrite Nat.div_add; [ | easy ].
   rewrite Nat.div_small; [ | now apply Nat.mod_upper_bound ].
   rewrite Nat.add_0_l.
  n - logn rad (a / rad) = S n - logn rad a
bbb.

Search (S _ - _).

   f_equal; f_equal; f_equal.
   apply move_carry_end_enough_iter; [ easy | lia | ].
   destruct a; [ easy | ].
   destruct rad as [| s]; [ easy | ].
   destruct s; [ lia | now apply Nat.div_lt ].
Qed.
bbb.

Lemma move_carry_rep_0_end {r : radix} : ∀ n a, 1 < rad →
  move_carry a (List.repeat 0 n) =
  move_carry_end (S a) a ++
    List.repeat 0 (n - length (move_carry_end (S a) a)).
Proof.
intros * Hr.
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
  move_carry a [] ++ List.repeat 0 (n - length (move_carry a [])).
Proof.
intros * Hr.
unfold move_carry at 2.
destruct (zerop a) as [Ha| Ha].
 subst a; simpl; rewrite Nat.sub_0_r.
 apply move_carry_0_rep_0.

 now apply move_carry_rep_0_end.
Qed.

Lemma move_carry_cons_rep_0 {r : radix} : ∀ a c n, 1 < rad →
  move_carry c (a :: List.repeat 0 n) =
  move_carry c [a] ++ List.repeat 0 (S n - length (move_carry c [a])).
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

Lemma nat_of_list_rep_0 {r : radix} : ∀ c n,
  nat_of_list c (List.repeat 0 n) = c * rad ^ n.
Proof.
intros.
induction n; [ now rewrite Nat.mul_1_r | ].
simpl; rewrite IHn, Nat.add_0_r; lia.
Qed.

Lemma nat_of_list_0_rep_0 {r : radix} : ∀ n, nat_of_list 0 (List.repeat 0 n) = 0.
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
split; [ now exists 0; rewrite List.app_nil_r | right ].
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
destruct Hal as ((m, Hm) & _); simpl in Hm.
apply move_carry_0_is_rep_0 in Hm; [ | easy ].
apply list_rem_trail_iff.
split.
 destruct a.
  subst al; simpl.
  rewrite Nat.mod_0_l; [ | easy ].
  rewrite Nat.div_0_l; [ simpl | easy ].
  exists (S m).
  now rewrite move_carry_0_rep_0.

  rewrite list_rem_trail_move_carry_0_nz; [ subst al | easy ].
  rewrite move_carry_cons_rep_0; [ | easy ].
  now exists (S m - length (move_carry 0 [S a])).

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
   exists 0.
   now destruct c.

   destruct c; [ easy | simpl ].
   destruct (zerop (S c / rad)) as [H| H]; [ now rewrite H in Hcr | clear H ].
   exists 0; f_equal; f_equal; rewrite List.app_nil_r.
   apply move_carry_end_enough_iter; [ easy | | now apply Nat.div_lt ].
   apply Nat.div_lt_upper_bound; [ easy | ].
   apply Nat.div_lt_upper_bound; [ easy | ].
   destruct c; [ now rewrite Nat.div_1_l in Hcr | ].
   destruct rad as [| s]; [ easy | ].
   destruct s; [ lia | simpl; lia ].

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

Lemma list_of_nat_inv {r : radix} : 2 ≤ rad →
  ∀ al, list_of_nat 0 (nat_of_list 0 al) = list_norm al.
Proof.
intros Hr *.
now specialize (list_of_nat_carry_inv Hr 0 al) as H.
Qed.

(*
Lemma move_carry_digits_lt_radix {r : radix} : ∀ c al,
  List.Forall (λ a, a < rad) (move_carry c al).
Proof.
intros.
revert c.
induction al as [| a1]; intros.
 simpl.
 destruct (zerop c) as [Hzc| Hzc]; [ easy | ].
 constructor.
Abort.
*)

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
destruct Hal1 as ((n & Hn), Hal1).
destruct Hal1 as [Hal1| Hlast]; [ now subst al1 | ].
revert c al Hn.
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
   destruct n.
    simpl in Hn.
    destruct (zerop (S c / rad)) as [Hscr| Hscr]; [ easy | ].
    injection Hn; clear Hn; intros; subst a2.
    now apply Nat.mod_upper_bound.

    simpl in Hn.
    destruct (zerop (S c / rad)) as [Hscr| Hscr]; [ easy | ].
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
   simpl in Hn.
   destruct (zerop c) as [Hc| Hc]; [ easy | ].
   injection Hn; clear Hn; intros Hn Hce.
   destruct n.
    rewrite List.app_nil_r in Hn.
    destruct c; [ easy | ].
    simpl in Hn.
    destruct (zerop (S c / rad)) as [Hcr| Hcr]; [ easy | ].
    injection Hn; clear Hn; intros Hn Ha2; rewrite <- Hn.
    now apply list_carry_end_digits_lt_radix.

    rewrite List.app_comm_cons in Hn.
    apply move_carry_end_ne_rep_0_succ in Hn; [ easy | easy | ].
    now apply Nat.div_lt.

   simpl in Hn.
   injection Hn; clear Hn; intros Hn Ha1.
   rewrite List.app_comm_cons in Hn.
   specialize (IHal1 Hlast ((c + a3) / rad) al Hn).
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
  ∀ a, xnat_of_nat (nat_of_xnat a) = xnat_norm a.
Proof.
intros Hr *.
unfold xnat_of_nat, xnat_norm; f_equal.
now apply list_of_nat_inv.
Qed.

Theorem xnat_of_nat_inv {r : radix} : 2 ≤ rad →
  ∀ a, xnat_of_nat (nat_of_xnat a) = xnat_norm a.
Proof.
intros Hr *.
unfold xnat_of_nat, xnat_norm; f_equal.
now apply list_of_nat_inv.
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

Lemma xnatv_add_rep_0_l {r : radix} : ∀ al n,
  xnatv_add (List.repeat 0 n) al = al ++ List.repeat 0 (n - length al).
Proof.
intros.
revert n.
induction al as [| a]; intros; [ now destruct n | simpl ].
now destruct n; [ rewrite List.app_nil_r | simpl; rewrite IHal ].
Qed.

Lemma move_carry_app_rep_0 {r : radix} : 1 < rad → ∀ c al n,
  move_carry c (al ++ List.repeat 0 n) =
  move_carry c al ++ List.repeat 0 (n - length (move_carry_end (S c) c)).
Proof.
intros Hr *.
revert c.
induction al as [| a1]; intros.
 rewrite List.app_nil_l.
 now apply move_carry_rep_0_end.

 remember move_carry_end as f; simpl; subst f.
 rewrite IHal.
 f_equal; f_equal.
bbb.

 
 specialize (IHal ((c + a1) / rad)) as (m & Hm).
 now exists m; simpl; rewrite Hm.
Qed.

Lemma move_carry_app_rep_0 {r : radix} : 1 < rad → ∀ c al n,
  ∃ m,
  move_carry c (al ++ List.repeat 0 n) =
  move_carry c al ++ List.repeat 0 m.
Proof.
intros Hr *.
revert c.
induction al as [| a1]; intros.
 rewrite List.app_nil_l.
 rewrite move_carry_rep_0_end; [ | easy ].
 now exists (n - length (move_carry_end (S c) c)).

 specialize (IHal ((c + a1) / rad)) as (m & Hm).
 now exists m; simpl; rewrite Hm.
Qed.

Lemma list_norm_with_carry_app_rep_0 {r : radix} : 1 < rad → ∀ al n c,
  list_norm_with_carry c (al ++ List.repeat 0 n) =
  list_norm_with_carry c al.
Proof.
intros Hr *.
unfold list_norm_with_carry.
specialize (move_carry_app_rep_0 Hr c al n) as (m & Hm).
now rewrite Hm, list_rem_trail_rep_0.
Qed.

Lemma eq_move_carry_end_nil {r : radix} : ∀ i c,
  move_carry_end i c = [] ↔ i = 0 ∨ c = 0.
Proof.
intros.
split; intros H.
 now destruct i; [ left | right; now destruct c ].

 destruct H; [ now subst i | now subst c; destruct i ].
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
destruct Hab as ((n, Hn), Hb).
simpl in Hn.
destruct n; [ easy | simpl in Hn ].
injection Hn; clear Hn; intros Hn Hbrr Hbr.
destruct n.
 apply eq_move_carry_end_nil in Hn.
 destruct Hn as [Hn| Hc]; [ now subst a; rewrite Nat.div_1_l in Har | ].
 rewrite Nat.mod_small in Hbrr; [ | now apply Nat.div_small_iff in Hc ].
 now rewrite Hbrr in Har.

 apply move_carry_end_succ_ne_rep_0 in Hn; [ easy | easy | ].
 split.
  apply Nat.mod_divides in Hbrr; [ | easy ].
  destruct Hbrr as (c, Hc); rewrite Nat.mul_comm in Hc.
  rewrite Hc, Nat.div_mul; [ | easy ].
  destruct c; lia.

  apply Nat.div_lt_upper_bound; [ easy | ].
  apply Nat.div_lt_upper_bound; [ easy | ].
  destruct a; [ easy | ].
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
 rewrite list_norm_with_carry_cons; [ | easy ].
 rewrite list_norm_with_carry_cons; [ | easy ].
 now rewrite IHbl.
Qed.

Theorem xnat_add_assoc {r : radix} : rad ≠ 0 → ∀ a b c,
  (a + (b + c) = (a + b) + c)%X.
Proof.
intros Hr *.
unfold xnat_add, xnat_norm; simpl; f_equal.
now apply list_norm_wc_add_assoc.
Qed.
