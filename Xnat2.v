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

Lemma list_rem_trail_iff : ∀ al bl,
  list_remove_trailing_0s al = bl
  ↔ ∃ n, al = bl ++ repeat 0 n ∧ (bl = [] ∨ List.last bl 0 ≠ 0).
Proof.
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

(*
Lemma list_rem_trail_move_carry_comm {r : radix} : ∀ c al, 1 < rad →
  list_remove_trailing_0s (move_carry c al) =
  move_carry c (list_remove_trailing_0s al).
Proof.
intros carry * Hr.
remember (list_remove_trailing_0s (move_carry carry al)) as bl eqn:Hml.
remember (list_remove_trailing_0s al) as cl eqn:Hnl.
symmetry in Hml, Hnl.
apply list_rem_trail_iff in Hml.
apply list_rem_trail_iff in Hnl.
destruct Hml as (m & Ham & Hbl).
destruct Hnl as (n & Han & Hcl).
subst al; symmetry.
destruct Hbl as [Hbl| Hbl].
 subst bl; simpl in Ham.
 destruct Hcl as [Hcl| Hcl].
  subst cl; simpl in Ham.
  simpl.
  destruct (zerop carry) as [| Hc]; [ easy | exfalso ].
  destruct carry; [ easy | clear Hc ].
  now revert Ham; apply move_nz_carry.

  rename cl into al.
  destruct carry; [ | now exfalso; revert Ham; apply move_nz_carry ].
  apply move_carry_0_is_rep_0 in Ham; [ | easy ].
  exfalso; apply Hcl; clear Hcl; symmetry in Ham.
  eapply List_app_rep_0_last; eassumption.

 destruct Hcl as [Hcl| Hcl].
  subst cl; simpl in Ham.
bbb.
destruct bl as [| b1]; [ easy | ].
assert (Hnn : b1 :: bl ≠ []) by easy.
apply (app_removelast_last 0) in Hnn.
rewrite Hnn in Ham.
remember (b1 :: bl) as cl eqn:Hcl.
clear b1 bl Hcl.
rewrite Hnn; clear Hnn.
remember (removelast cl) as bl eqn:Hcl.
remember (last cl 0) as bn eqn:Hbn.
clear cl Hcl Hbn.
revert carry m n bn Ham Hbl.
induction bl as [| b1]; intros.
 simpl in Ham.
 destruct carry.
  rewrite move_carry_0_rep_0 in Ham.
  destruct n; [ easy | simpl in Ham ].
  injection Ham; clear Ham; intros Ham H.
  now symmetry in H.

Search move_carry.
bbb.
destruct n; simpl in Ham; simpl.
destruct (zerop carry) as [Hc| Hc].
 destruct m; [ now rewrite app_nil_r in Ham | simpl in Ham ].
 now destruct bl.

 destruct m; [ now rewrite app_nil_r in Ham | ].
 simpl in Ham.
 destruct bl as [| b1]; [ easy | ].
  simpl in Ham.
  injection Ham; clear Ham; intros Ham Hb1.
  rewrite Hb1; f_equal.
  exfalso.
subst b1.
induction bl as [| b2]; simpl in Hbl.
simpl in Ham.
replace (0 :: repeat 0 m) with (repeat 0 (S m)) in Ham by easy.
destruct (zerop (carry / rad)) as [Hcr| Hcr].
 rewrite Hcr in Ham.
 now destruct carry.
revert Ham.
apply move_carry_end_succ_ne_rep_0; [ easy | ].
split; [easy|].
Focus 2.
destruct bl as [| b3].
simpl in Ham.
simpl in IHbl.
bbb.


 simpl.
bbb.
  destruct carry.
   rewrite move_carry_rep_0 in Ham.
   exfalso; apply Hbl; clear Hbl.
   eapply List_app_rep_0_last; eassumption.

   revert carry Ham.
   induction m; intros.
    simpl in Ham.
    rewrite List.app_nil_r in Ham.
    revert bl carry Hbl Ham.
    induction n; intros; [ easy | ].
    simpl in Ham.
    rewrite Nat.add_0_r in Ham.
    destruct bl as [| b1]; [ easy | ].
     injection Ham; clear Ham; intros Hb1 Ham; simpl.
     rewrite Ham; f_equal.
     remember (S carry / rad) as c1 eqn:Hc1.
     simpl in Hbl.
     destruct bl as [| b2].
      destruct c1; [ easy | now destruct n ].

      clear IHn.
      destruct c1; [ exfalso | ].
       revert b2 bl carry Hbl Hb1 Hc1 Ham.
       induction n; intros; [ easy | ].
       simpl in Hb1.
       rewrite Nat.mod_0_l in Hb1; [ | lia ].
       rewrite Nat.div_0_l in Hb1; [ | lia ].
       injection Hb1; clear Hb1; intros Hb1 H; subst b2.
       simpl in Hbl.
       destruct bl as [| b3]; [ easy | ].
       now specialize (IHn b3 bl carry Hbl Hb1 Hc1 Ham).

       revert b2 bl carry Hbl Hb1 Hc1 Ham.
       induction n; intros.
        simpl in Hb1.
        injection Hb1; clear Hb1; intros Hb2 Hb1.
        rewrite Hb1; f_equal.
        destruct (zerop (S c1 / rad)) as [Hc| Hc].
         subst bl; simpl in Hbl.
         now rewrite Hc; destruct carry.

         destruct carry; [ now rewrite Nat.div_1_l in Hc1 | simpl; f_equal ].
         destruct (zerop (S c1 / rad)) as [H| H]; [ lia | clear H ].
         rewrite <- Hb2; f_equal.
         destruct carry.
          destruct rad as [| s]; [ easy | ].
          destruct s; [ lia | ].
          destruct s; [ | now rewrite Nat.div_small in Hc1 ].
          now apply Nat.succ_inj in Hc1; subst c1.

          apply move_carry_end_enough_iter; [ easy | | ].
           rewrite Hc1.
           clear - Hr.
           destruct rad as [| s]; [ easy | ].
           destruct s; [ lia | clear Hr ].
           apply le_lt_n_Sm.
bbb.
           destruct s.
            destruct carry; [ easy | ].
            destruct carry; [ simpl; lia | ].
            destruct carry; [ simpl; lia | ].
            destruct carry; [ simpl; lia | ].
            destruct carry; [ simpl; lia | ].
bbb.

           apply Nat.mul_le_mono_pos_r with (p := S (S s)); [ lia | ].
           rewrite Nat.mul_comm.
           eapply le_trans; [ now apply Nat.div_mul_le | ].
           rewrite Nat.mul_comm.
           rewrite Nat.div_mul; [ | easy ].
           apply Nat.mul_le_mono_pos_r with (p := S (S s)); [ lia | ].
           rewrite Nat.mul_comm.
           eapply le_trans; [ now apply Nat.div_mul_le | ].
           rewrite Nat.mul_comm.
           rewrite Nat.div_mul; [ | easy ].
           apply Nat.mul_le_mono_pos_r with (p := S (S s)); [ lia | ].
           rewrite Nat.mul_comm.
           eapply le_trans; [ now apply Nat.div_mul_le | ].
           rewrite Nat.mul_comm.
           rewrite Nat.div_mul; [ | easy ].
destruct s.
destruct carry; simpl.


bbb.
   revert m n carry Ham.
   induction bl as [| b1]; intros; [ easy | ].
   simpl in Hbl.
   destruct bl as [| b2].
    destruct n.
     clear IHbl.
     simpl in Ham; simpl.
     injection Ham; clear Ham; intros Ham Hb1.
     subst b1; f_equal.
     destruct (zerop (S carry / rad)) as [Hcr| Hcr]; [ easy | exfalso ].
revert carry Hbl Hcr Ham.
induction m; intros; [ easy | simpl in Ham ].
injection Ham; clear Ham; intros Ham H.
apply Nat.mod_divides in H; [ | lia ].
destruct H as (c, Hc).
rewrite Nat.mul_comm in Hc; rewrite Hc in Hcr, Ham.
rewrite Nat.div_mul in Ham; [ | lia ].
destruct c; [ easy | ].
destruct carry.
 rewrite Nat.div_1_l in Hc; [ lia | easy ].

 simpl in Ham.
 rewrite <- Hc in Hcr.
 specialize (IHm (S carry) Hbl Hcr).
 apply IHm; clear IHm.
bbb.

 destruct m; [ easy | simpl in Ham ].
 injection Ham; clear Ham; intros Ham H.
 apply Nat.mod_divides in H; [ | lia ].
 destruct H as (c1, Hc1).
 rewrite Nat.mul_comm in Hc1; rewrite Hc1 in Hcr, Ham.
 rewrite Nat.div_mul in Ham; [ | lia ].
 destruct c1; [ easy | ].
 destruct carry.
  destruct rad as [| s]; [ easy | ].
  destruct s; [ easy | now destruct s ].

bbb.
     destruct m; [ easy | simpl in Ham ].
     injection Ham; clear Ham; intros Ham H.
     apply Nat.mod_divides in H; [ | lia ].
     destruct H as (c, Hc).
     rewrite Nat.mul_comm in Hc; rewrite Hc in Hcr, Ham.
     rewrite Nat.div_mul in Ham; [ | lia ].
     destruct c; [ easy | ].
     destruct carry.
      rewrite Nat.div_1_l in Hc; [ lia | easy ].

      destruct m; [ easy | simpl in Ham ].
      injection Ham; clear Ham; intros Ham H.
      apply Nat.mod_divides in H; [ | lia ].
      destruct H as (c1, Hc1).
      rewrite Nat.mul_comm in Hc1; rewrite Hc1 in Hcr, Ham.
      rewrite Nat.div_mul in Ham; [ | lia ].
      destruct c1; [ easy | ].
      destruct carry.
       destruct rad as [| s]; [ easy | ].
       destruct s; [ easy | now destruct s ].

       simpl in Ham.
       destruct m; [ easy | simpl in Ham ].
       injection Ham; clear Ham; intros Ham Hc2.
       apply Nat.mod_divides in Hc2; [ | lia ].
       destruct Hc2 as (c2, Hc2).
       rewrite Nat.mul_comm in Hc2; rewrite Hc2 in Ham.
       rewrite Nat.div_mul in Ham; [ | lia ].
       destruct c2; [ easy | ].
       destruct carry.
        destruct rad as [| s]; [ easy | ].
        destruct s; [ easy | ].
        destruct s; [ easy | now destruct s ].

        simpl in Ham.
bbb.
*)

(*
Lemma list_norm_action_comm {r : radix} : ∀ al, rad ≠ 0 →
  list_norm al = move_carry 0 (list_remove_trailing_0s al).
Proof.
intros * Hr; unfold list_norm.
bbb.
induction al as [| a]; [ easy | simpl ].
rewrite Nat.add_0_r.
destruct a.
 rewrite Nat.mod_0_l; [ | easy ].
 rewrite Nat.div_0_l; [ | easy ].
 rewrite IHal.
 remember (list_remove_trailing_0s al) as bl eqn:Hbl.
 symmetry in Hbl.
 destruct bl as [| b]; [ easy | simpl ].
 rewrite Nat.add_0_r.
 rewrite Nat.mod_0_l; [ | easy ].
 rewrite Nat.div_0_l; [ | easy ].
 now rewrite Nat.add_0_r.

 simpl; rewrite Nat.add_0_r.
 destruct (zerop (S a mod rad)) as [Har| Har].
  rewrite Har.
  apply Nat.mod_divides in Har; [ | easy ].
  destruct Har as (c, Hc).
  rewrite Hc, Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].

bbb.
*)

(*
Lemma glop {r : radix} : ∀ al c, 1 < rad →
  list_remove_trailing_0s (move_carry c (al ++ [0])) =
  list_remove_trailing_0s (move_carry c al).
Proof.
intros * Hr.
apply list_rem_trail_iff.
exists 1; simpl.
split.
Print move_carry.

bbb.
intros * Hr.
revert c.
induction al as [| a1]; intros.
 simpl; rewrite Nat.add_0_r.
 remember (c mod rad) as c1 eqn:Hc1.
 symmetry in Hc1.
 destruct c1.
  apply Nat.mod_divides in Hc1; [ | lia ].
  destruct Hc1 as (c1, Hc1).
  rewrite Nat.mul_comm in Hc1; subst c.
  rewrite Nat.div_mul; [ | lia ].
  destruct (zerop c1) as [Hc1| Hc1]; [ now subst c1 | ].
  simpl.
  remember (c1 mod rad) as c2 eqn:Hc2.
  symmetry in Hc2.
  destruct c2.
   apply Nat.mod_divides in Hc2; [ | lia ].
   destruct Hc2 as (c2, Hc2).
    rewrite Nat.mul_comm in Hc2.
    rewrite Hc2, Nat.div_mul; [ | lia ].
    rewrite <- Hc2.
    remember (list_remove_trailing_0s (move_carry_end c1 c2)) as bl eqn:Hbl.
    symmetry in Hbl.
(**)
destruct (zerop (c1 * rad)) as [Hcr| Hcr].
 apply Nat.eq_mul_0 in Hcr; lia.

bbb.
    destruct bl as [| b1].
     exfalso.
     apply eq_list_rem_trail_nil in Hbl; simpl in Hbl.
     remember (move_carry_end c1 c2) as al eqn:Hal.
     symmetry in Hal.
     assert (Hcc : 0 < c2 < c1).
      split; [ destruct c2; lia | ].
      rewrite Hc2.
      destruct rad as [| s]; [ lia | ].
      destruct s; [ lia | ].
      destruct c2; [ lia | ].
      rewrite Nat.mul_comm; simpl; lia.

      clear Hc2.
      revert c1 c2 Hc1 Hcc Hal.
      induction al as [| a]; intros.
       revert Hal; rewrite Hbl.
       apply move_carry_end_succ_ne_rep_0; [ lia | easy ].

       simpl in Hbl.
       injection Hbl; clear Hbl; intros Hbl Ha; subst a.
       specialize (IHal Hbl).
       destruct c1; [ easy | ].
       simpl in Hal.
       destruct (zerop c2) as [Hzc2| Hnzc2]; [ easy | ].
       injection Hal; clear Hal; intros Hcr Hal.
       destruct c1; [ lia | ].
       apply Nat.mod_divides in Hal; [ | lia ].
       destruct Hal as (c3, Hc3).
       destruct c3; [ lia | ].
       revert Hcr.
       apply IHal; [ lia | ].
       split.
        rewrite Hc3, Nat.mul_comm.
        rewrite Nat.div_mul; lia.

        apply Nat.lt_le_trans with (m := c2); [ | lia ].
        destruct c2; [ easy | ].
        destruct rad as [| s]; [ easy | ].
        destruct s; [ lia | ].
        now apply Nat.div_lt.

     destruct (zerop (c1 * rad)) as [Hcr| Hcr]; [ exfalso | ].
      apply Nat.eq_mul_0 in Hcr; lia.

      simpl.
bbb.
(* essayer aussi en commençant par list_rem_trail_iff *)
*)

Lemma list_norm_app_0 {r : radix} : ∀ al, 1 < rad →
  list_norm (al ++ [0]) = list_norm al.
Proof.
intros * Hr.
induction al as [| a]; [ apply list_norm_0 | simpl ].
unfold list_norm; simpl.
remember (a mod rad) as c1 eqn:Hc1.
symmetry in Hc1.
destruct c1.
 remember (al ++ [0]) as bl eqn:Hbl.
 remember (list_remove_trailing_0s (move_carry (a / rad) al)) as al1 eqn:Hal1.
 remember (list_remove_trailing_0s (move_carry (a / rad) bl)) as bl1 eqn:Hbl1.
 symmetry in Hal1, Hbl1.
 apply list_rem_trail_iff in Hal1.
 apply list_rem_trail_iff in Hbl1.
 destruct Hal1 as (n & Ha & Hal1).
 destruct Hbl1 as (m & Hb & Hbl1).
 destruct Hal1 as [Hal1| Hal1].
  subst al1; simpl in Ha.
  destruct Hbl1 as [Hbl1| Hbl1]; [ now subst bl1 | exfalso ].
  apply Nat.mod_divides in Hc1; [ | lia ].
  destruct Hc1 as (c1 & Hc1).
  rewrite Nat.mul_comm in Hc1.
  rewrite Hc1 in Ha, Hb.
  rewrite Nat.div_mul in Ha; [ | lia ].
  rewrite Nat.div_mul in Hb; [ | lia ].
  destruct c1.
   apply move_carry_0_is_rep_0 in Ha; [ | easy ].
   subst al.
   replace (repeat 0 n ++ [0]) with (repeat 0 (S n)) in Hbl.
    subst bl.
    rewrite move_carry_0_rep_0 in Hb.
    simpl in Hb.
    destruct bl1 as [| b1]; [ easy | ].
    injection Hb; clear Hb; intros Hb Hb1; subst b1.
    clear IHal.
    revert n Hb.
    induction bl1 as [| b1]; intros; [ easy | ].
    simpl in Hb.
    destruct n; [ easy | ].
    simpl in Hb.
    injection Hb; clear Hb; intros Hb Hb1; subst b1.
    now apply IHbl1 with (n := n).

    clear; simpl.
    induction n; [ easy | now simpl; rewrite IHn ].

   exfalso; revert Ha.
   apply move_nz_carry; [ lia | easy ].

  destruct Hbl1 as [Hbl1| Hbl1].
   subst bl1; simpl in Hb.
   destruct al1 as [| a1]; [ easy | exfalso ].
   apply Nat.mod_divides in Hc1; [ | lia ].
   destruct Hc1 as (c1 & Hc1).
   rewrite Nat.mul_comm in Hc1.
   rewrite Hc1 in Ha, Hb.
   rewrite Nat.div_mul in Ha; [ | lia ].
   rewrite Nat.div_mul in Hb; [ | lia ].
   destruct c1.
    apply move_carry_0_is_rep_0 in Hb; [ | easy ].
    subst bl.
    destruct m; [ now apply List.app_eq_nil in Hb | ].
    replace al with (repeat 0 m) in Ha.
     rewrite move_carry_0_rep_0 in Ha.
     simpl in Ha.
     destruct m; [ easy | simpl in Ha ].
     injection Ha; clear Ha; intros Ha Ha1; subst a1.
     clear IHal Hb.
     revert m n Ha.
     induction al1 as [| a1]; intros; [ easy | ].
     simpl in Ha.
     destruct m; [ easy | simpl in Ha ].
     injection Ha; clear Ha; intros Ha Ha1; subst a1.
     now revert Ha; apply IHal1.

     clear - Hb; simpl in Hb.
     revert al Hb.
     induction m; intros.
      simpl in Hb.
      apply List.app_eq_unit in Hb.
      now destruct Hb.

      simpl.
      destruct al as [| a1]; [ easy | ].
      simpl in Hb.
      injection Hb; clear Hb; intros Hb Ha; subst a1.
      f_equal.
      now apply IHm.

    simpl.
    exfalso; revert Hb.
    apply move_nz_carry; [ lia | easy ].

   apply Nat.mod_divides in Hc1; [ | lia ].
   destruct Hc1 as (c1 & Hc1).
   rewrite Nat.mul_comm in Hc1.
   rewrite Hc1 in Ha, Hb.
   rewrite Nat.div_mul in Ha; [ | lia ].
   rewrite Nat.div_mul in Hb; [ | lia ].
   destruct al1 as [| a1]; [ now destruct bl1 | ].
(**)
   assert (Hal : a1 :: al1 ≠ []) by easy.
   apply exists_last in Hal.
   destruct Hal as (al2 & a2 & Hal).
   rewrite Hal in Ha, Hal1; rewrite Hal.
   clear a1 al1 Hal.
Lemma List_last_app : ∀ A (al bl : list A) d, bl ≠ []
  → last (al ++ bl) d = last bl d.
Proof.
intros * Hbl.
revert bl Hbl.
induction al as [| a1] using rev_ind; intros; [ easy | simpl ].
rewrite <- List.app_assoc.
now rewrite IHal; [ destruct bl | ].
Qed.

Lemma List_last_app_single : ∀ A al (a : A) d, last (al ++ [a]) d = a.
Proof.
intros.
now apply List_last_app.
Qed.

Show.
   rewrite List_last_app_single in Hal1.
   destruct bl1 as [| b1]; [ easy | f_equal ].
   assert (Hbl2 : b1 :: bl1 ≠ []) by easy.
   apply exists_last in Hbl2.
   destruct Hbl2 as (bl2 & b2 & Hbl2).
   rewrite Hbl2 in Hb, Hbl1; rewrite Hbl2.
   clear b1 bl1 Hbl2.
   rewrite List_last_app_single in Hbl1.
clear a Hc1.
destruct al as [| a1].
 destruct bl as [| b1]; [ easy | ].
  simpl in Hbl.
  injection Hbl; clear Hbl; intros Hbl Hb1; subst b1 bl.
  simpl in Ha, Hb.
  rewrite Nat.add_0_r in Hb.
  destruct (zerop c1) as [Hc1| Hc1]; [ now destruct al2 | ].
  destruct (zerop (c1 / rad)) as [Hcr| Hcr].
   destruct bl2; [ | now destruct bl2 ].
   simpl in Hb.
   injection Hb; clear Hb; intros Hb Hb2; subst b2; simpl.
   rewrite Hcr in Ha.
   destruct al2 as [| a3]; [ now injection Ha; intros; subst a2 | ].
   exfalso; simpl in Ha.
   destruct c1; [ easy | clear Hc1 ].
   injection Ha; clear Ha; intros Hal Ha; clear a3 Ha.
   now destruct al2.

   destruct c1; [ easy | ].
   simpl in Ha.
   destruct (zerop (S c1 / rad)) as [Hc| Hc]; [ lia | clear Hc ].
   destruct al2 as [| a3].
    destruct bl2 as [| b3].
     simpl in Ha, Hb.
     injection Ha; clear Ha; intros Hal Ha; subst a2.
     injection Hb; clear Hb; intros Hbl Hb; subst b2.
     easy.

     exfalso.
     simpl in Ha.
     injection Ha; clear Ha; intros Hal Ha; subst a2.
     injection Hb; clear Hb; intros Hbl Hb; subst b3.
     clear Hc1.
     destruct n; [ easy | simpl in Hal ].
     injection Hal; clear Hal; intros Hal Ha.
     rewrite Ha in Hbl.
Abort.
(*
bbb.
   destruct bl1 as [| b1]; [ easy | f_equal ].
   simpl in Ha, Hb.
   clear a Hc1.
   destruct al as [| a2].
    simpl in Hbl; subst bl.
    simpl in Ha, Hb; clear IHal.
    rewrite Nat.add_0_r in Hb.
    injection Hb; clear Hb; intros Hb Hb1; subst b1.
    destruct (zerop c1) as [Hc1| Hc1]; [ easy | ].
    injection Ha; clear Ha; intros Ha Ha1; subst a1; f_equal.
    destruct (zerop (c1 / rad)) as [Hcr| Hcr].
     rewrite Hcr in Ha.
     destruct m; [ | now destruct bl1 ].
     simpl in Hb; rewrite List.app_nil_r in Hb; subst bl1.
     simpl in Hbl1, Hal1.
     apply Nat.div_small_iff in Hcr; [ | lia ].
     destruct al1 as [| a1]; [ easy | exfalso ].
     now destruct c1.

     destruct m.
      simpl in Hb; rewrite List.app_nil_r in Hb.
      symmetry in Hb.
      destruct c1; [ easy | clear Hc1 ].
      simpl in Ha.
      destruct (zerop (S c1 / rad)) as [H| H]; [ lia | clear H ].
      destruct n.
       simpl in Ha; rewrite List.app_nil_r in Ha.
       symmetry in Ha.
       rewrite Ha, Hb; f_equal.
       apply move_carry_end_enough_iter; [ easy | now apply Nat.div_lt | ].
       destruct c1; [ now rewrite Nat.div_1_l in Hcr | ].
Search (_ ++ [_]).
bbb.
exists_last:
  ∀ (A : Type) (l : list A), l ≠ [] → {l' : list A & {a : A | l = l' ++ [a]}}
bbb.
   apply move_carry_0_is_rep_0 in Ha; [ | easy ].
   subst bl.
   destruct m; [ now apply List.app_eq_nil in Hb | ].
   replace al with (repeat 0 m) in Ha.
    rewrite move_carry_0_rep_0 in Ha.
    simpl in Ha.
    destruct m; [ easy | simpl in Ha ].
    injection Ha; clear Ha; intros Ha Ha1; subst a1.
    clear IHal Hb.
    revert m n Ha.
    induction al1 as [| a1]; intros; [ easy | ].
    simpl in Ha.
    destruct m; [ easy | simpl in Ha ].
    injection Ha; clear Ha; intros Ha Ha1; subst a1.
    now revert Ha; apply IHal1.
bbb.
*)

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

Lemma list_of_nat_inv {r : radix} : 2 ≤ rad →
  ∀ al, list_of_nat 0 (nat_of_list 0 al) = list_norm al.
Proof.
intros Hr *.
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
  destruct Hn; lia.

  unfold list_norm in IHal.
  apply list_rem_trail_iff in IHal.
  destruct IHal as (n & IHal & Hm).
  destruct Hm as [Hm| Hm]; [ now rewrite move_carry_cons in Hm | ].
  symmetry; unfold list_norm.
  apply list_rem_trail_iff.
  rewrite move_carry_cons, Nat.add_0_l.
  exists 0.
  split.
   simpl.
   rewrite Nat.add_comm.
   rewrite Nat.mod_add; [ f_equal | lia ].
   rewrite Nat.div_add; [ | lia ].
   destruct (zerop (a / rad + nat_of_list 0 al)) as [Han| Han].
    apply Nat.eq_add_0 in Han; lia.

    rewrite List.app_nil_r.
    destruct al as [| a1].
     simpl in Han; simpl.
     rewrite Nat.add_0_r in Han |- *.
     destruct (zerop (a / rad)) as [Har| Har]; [ lia | easy ].

     simpl in Han; simpl.
     symmetry; rewrite <- Nat.add_mod_idemp_r; [ | lia ].
     remember ((nat_of_list 0 al * rad + a1) mod rad) as x eqn:Hx.
     rewrite Nat.add_comm in Hx.
     rewrite Nat.mod_add in Hx; [ subst x | lia ].
     rewrite Nat.add_mod_idemp_r; [ f_equal | lia ].
     simpl in IHal.
     rewrite <- Nat.add_mod_idemp_l in IHal; [ | lia ].
     rewrite Nat.mod_mul in IHal; [ | lia ].
     rewrite Nat.add_0_l in IHal.
     injection IHal; clear IHal; intros IHal.
     rewrite Nat.div_add_l in IHal; [ | lia ].
     destruct (zerop (nat_of_list 0 al + a1 / rad)) as [Hz| Hz].
      apply Nat.eq_add_0 in Hz.
      destruct Hz as (Hna, Hz).
      rewrite Hna, Nat.mul_0_l, Nat.add_0_l.
      rewrite Hz in IHal; simpl in IHal.
      apply move_carry_0_is_rep_0 in IHal; [ | easy ].
      destruct n.
       simpl in IHal; subst al.
       destruct (zerop ((a / rad + a1) / rad)) as [Har| Har].
        rewrite Har.
        now destruct (a / rad + a1).

        simpl in Hm.
        rewrite Hz in Hm; simpl in Hm.
        simpl in Ha.
        simpl in Hn.
        simpl in Han.
simpl.
destruct (a / rad + a1); [ easy | ].
simpl.
destruct (zerop (S n / rad)); [ easy | ].
f_equal.
apply move_carry_end_enough_iter; [ easy | | ].
(* trop bordélique mais faut peut-être insister ? *)

bbb.
  simpl.
  destruct (zerop (a / rad)) as [Har| Har].
   intros H.
   apply Nat.mod_divides in H; [ | lia ].
   apply Nat.div_small_iff in Har; [ | lia ].
   destruct H as (c & Hc).
   destruct c; [ rewrite Nat.mul_comm in Hc; lia | subst a ].
   apply lt_not_le in Har; apply Har; clear Har.
   rewrite Nat.mul_comm; simpl; lia.

   remember (a / rad / rad) as arr eqn:Harr.
   rewrite move_carry_end_enough_iter with (n := S arr); [ | lia | | lia ].
    simpl.
    destruct (zerop arr) as [Hz| Hnz].
     subst arr.
     intros H.
     apply Nat.mod_divides in H; [ | lia ].
     apply Nat.div_small_iff in Hz; [ | lia ].
     destruct H as (c & Hc).
     destruct c; [ rewrite Nat.mul_comm in Hc; lia | rewrite Hc in Hz ].
     apply lt_not_le in Hz; apply Hz; clear Hz.
     rewrite Nat.mul_comm; simpl; lia.
bbb.
Inspect 1.
  rewrite move_carry_rep_0

bbb.
  destruct a; [ easy | ].
Inspect 1.
  specialize (move_carry_succ_rep_0 (length al)) as H.


bbb.
Search move_carry.
Lemma glop {r : radix} : ∀ a c n, ∃ m, move_carry c (a :: repeat 0 n) = move_carry c [a] ++ repeat 0 m.
Proof.
intros.
revert a c.
induction n; intros.
simpl.
destruct (zerop ((c + a) / rad)) as [Hcr| Hcr]; [ now exists 0 | ].
exists 0; simpl.
now rewrite List.app_nil_r.

exists (S n).
rewrite List_repeat_succ_app.
simpl.
destruct (zerop ((c + a) / rad)) as [Hcr| Hcr].
 rewrite Hcr, <- List_repeat_succ_app.
 now rewrite move_carry_0_rep_0.

 f_equal.
 rewrite <- List_repeat_succ_app.
bbb.

 remember ((c + a) / rad) as ca eqn:Hca.
 symmetry in Hca.
 destruct ca; [ easy | clear Hcr ].
 simpl.
 rewrite Nat.add_0_r.
 f_equal.

Search (repeat _ _ ++ _).
Check move_carry_rep_0.
 specialize (move_carry_rep_0
 rewrite <- move_carry_rep_0.
bbb.

 remember ((c + a) / rad) as cr eqn:Hcar.
 symmetry in Hcar.
 destruct cr; [ easy | clear Hcr ].
 simpl.
Search (move_carry).
bbb.

 destruct (zerop (S cr / rad)) as [Hcr| hcr].
  simpl.


bbb.

  simpl.
destruct (zerop (a / rad)) as [Har| Har].

  remember (length al) as n eqn:Hn.
  clear - Hr Hanz.
  rewrite list_norm_cons_repeat_0s.

bbb.

 simpl; rewrite Ha; simpl; symmetry.
 destruct (zerop a) as [Haz| Hanz].
  subst a; simpl.
  now apply list_norm_cons_0.

  rewrite Nat.add_0_r.
  destruct (zerop (a / rad)) as [Har| Har].
   apply Nat.div_small_iff in Har; [ | lia ].
   rewrite Nat.mod_small; [ | easy ].
   apply eq_nat_of_list_0 in Ha; [ | lia ].
   rewrite Ha; simpl.
   unfold list_norm; simpl.
   rewrite Nat.add_0_r.
   remember (a mod rad) as b eqn:Hb.
   symmetry in Hb.
   destruct b; simpl.
    exfalso; apply Nat.mod_divides in Hb; [ | lia ].
    destruct Hb as (b, Hb); subst a.
    destruct b; [ lia | ].
    rewrite Nat.mul_comm in Har; simpl in Har; lia.

    rewrite Nat.mod_small in Hb; [ subst a | easy ].
    rewrite Nat.div_small; [ | easy ].
    rewrite move_carry_repeat_0.
    now rewrite list_rem_trail_repeat_0.

   simpl.
bbb.

   apply Nat.mod_divides in Hb; [ | lia ].


Search list_remove_trailing_0s.
bbb.

 symmetry.
 induction al as [| a]; [ easy | simpl in Ha ].
 apply Nat.eq_add_0 in Ha.
 destruct Ha as (Hn, Ha); subst a.
 apply list_norm_cons_0, IHal.
 apply Nat.eq_mul_0 in Hn.
 destruct Hn as [Hn| Hn]; [ easy | lia ].

 simpl.
 rewrite Nat.add_0_r.
 destruct (zerop (nat_of_list 0 al / rad)) as [Hnr| Hnr].
  apply Nat.div_small_iff in Hnr; [ | lia ].
  rewrite Nat.mod_small; [ | easy ].
  induction al as [| a]; [ easy | ].
  simpl in Ha, Hnr; simpl.
  remember (nat_of_list 0 al) as n eqn:Hn.
  symmetry in Hn.
  destruct n.
   simpl in Ha, Hnr; simpl.
   unfold list_norm; simpl.
   rewrite Nat.add_0_r.
   rewrite Nat.mod_small; [ | easy ].
   destruct a; [ easy | ].
   f_equal; symmetry.
   rewrite Nat.div_small; [ | easy ].
   apply eq_nat_of_list_0 in Hn; [ | lia ].
   rewrite Hn; simpl.
   remember (length al) as n; clear.
   rewrite move_carry_repeat_0.
   apply eq_list_rem_trail_nil.
   induction n; [ easy | now simpl; f_equal ].

   exfalso; clear - Hnr.
   apply lt_not_le in Hnr; apply Hnr; clear Hnr.
   destruct rad as [| v]; [ apply Nat.le_0_l | simpl; lia ].

  unfold list_norm.
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
