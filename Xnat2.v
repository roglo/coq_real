(* Natural numbers in any radix; second version; without proofs *)
(* Can be regarded as polynomials with natural number coefficients. *)

Require Import Utf8 Arith Psatz List.
Import ListNotations.

Lemma List_cons_inv : ∀ A (a b : A) al bl,
  a :: al = b :: bl → a = b ∧ al = bl.
Proof.
intros * Hab.
now inversion Hab.
Qed.

Class radix := { rad : nat }.

Definition radix_2 := {| rad := 2 |}.
Definition radix_10 := {| rad := 10 |}.

Record xnat := xn { xnatv : list nat }.

Fixpoint move_carry_end {r : radix} iter carry :=
  match iter with
  | 0 => [42]
  | S i =>
      if zerop carry then []
      else carry mod rad :: move_carry_end i (carry / rad)
  end.

Fixpoint move_carry {r : radix} carry al :=
  match al with
  | [] =>
      if zerop carry then [] else move_carry_end (S carry) carry
  | a :: al' =>
      (a + carry) mod rad :: move_carry ((a + carry) / rad) al'
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
rewrite Nat.add_0_r.
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

Lemma move_carry_repeat_0 {r : radix} : ∀ n,
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
specialize (move_carry_repeat_0 1) as H.
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
 apply List_cons_inv in Ha.
 destruct Ha as (Ha, Hal); subst a.
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
 apply List_cons_inv in Hal.
 destruct Hal as (Ha, Hal); subst a.
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

Lemma move_carry_end_succ {r : radix} : ∀ i c,
  move_carry_end (S i) (S c) = S c mod rad :: move_carry_end i (S c / rad).
Proof. easy. Qed.

Lemma list_rem_trail_if : ∀ al bl,
  list_remove_trailing_0s al = bl
  → ∃ n, al = bl ++ repeat 0 n ∧ (bl = [] ∨ List.last bl 0 ≠ 0).
Proof.
intros * Hb.
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
  apply List_cons_inv in Hb.
  destruct Hb as (Hab, Hbl); subst b.
  specialize (IHal bl Hbl) as (m & Hal & Hm).
  exists m.
  split; [ now rewrite Hal | right ].
  destruct Hm as [Hm| Hm]; [ now rewrite Hm | simpl ].
  now destruct bl.
Qed.

Lemma move_nz_carry {r : radix} : ∀ al n c, rad ≠ 0 → c ≠ 0 →
  move_carry c al ≠ repeat 0 n.
Proof.
intros * Hr Hc.
bbb.

Lemma list_rem_trail_move_carry_comm {r : radix} : ∀ c al, rad ≠ 0 →
  list_remove_trailing_0s (move_carry c al) =
  move_carry c (list_remove_trailing_0s al).
Proof.
intros carry * Hr.
remember (list_remove_trailing_0s (move_carry carry al)) as bl eqn:Hbl.
remember (list_remove_trailing_0s al) as cl eqn:Hcl.
symmetry in Hbl, Hcl.
apply list_rem_trail_if in Hbl.
apply list_rem_trail_if in Hcl.
destruct Hbl as (b & Hab & Hbl).
destruct Hcl as (c & Hac & Hcl).
destruct Hbl as [Hbl| Hbl].
 subst bl; simpl in Hab.
 destruct Hcl as [Hcl| Hcl].
  subst cl; simpl in Hac; simpl.
  destruct (zerop carry) as [| Hc]; [ easy | exfalso ].
  destruct carry; [ easy | clear Hc ].
  subst al; revert Hab.
  now apply move_nz_carry.

bbb.

  destruct c; simpl in Hab.
   destruct b; [ easy | simpl in Hab ].
   apply List_cons_inv in Hab.
   destruct Hab as (Hcr, Hab).
   apply Nat.mod_divides in Hcr; [ | easy ].
   destruct Hcr as (c, Hcr).
   rewrite Nat.mul_comm in Hcr; rewrite Hcr in Hab.
   rewrite Nat.div_mul in Hab; [ | easy ].
   destruct c; [ easy | simpl in Hab ].
   destruct b; [ easy | simpl in Hab ].

bbb.

intros * Hr.
revert c.
induction al as [| a]; intros; simpl.
 destruct (zerop c) as [Hc| Hc]; [ easy | simpl ].
 destruct (zerop (c mod rad)) as [Hcr| Hcr].
  rewrite Hcr; simpl.
  apply Nat.mod_divides in Hcr; [ | easy ].
  destruct Hcr as (d, Hd); subst c.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul; [ | easy ].
  destruct d; [ lia | ].
  remember rad as s eqn:Hs; symmetry in Hs.
  rewrite <- Hs in Hr.
  destruct s as [| s]; [ lia | ].
  remember (S d * S s) as ds eqn:Hds.
  simpl in Hds; subst ds.
  rewrite move_carry_end_succ.
  remember list_remove_trailing_0s as f; simpl; subst f.
  remember (move_carry_end (s + d * S s) (S d / rad)) as al eqn:Hal.
  remember (list_remove_trailing_0s (S d mod rad :: al)) as bl eqn:Hbl.
  symmetry in Hbl.
  destruct bl as [| b].
   exfalso.
   apply eq_list_rem_trail_nil in Hbl; simpl in Hbl.
   apply List_cons_inv in Hbl.
   destruct Hbl as (Hdr, Ha).
   apply Nat.mod_divides in Hdr; [ | lia ].
   destruct Hdr as (e, He); rewrite Nat.mul_comm in He.
   rewrite He, Nat.div_mul in Hal; [ | easy ].
   destruct e; [ easy | ].
Print move_carry_end.
bbb.

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

Lemma list_norm_app_0 {r : radix} : ∀ al,
  list_norm (al ++ [0]) = list_norm al.
Proof.
intros.
do 2 rewrite list_norm_action_comm.

bbb.
intros.
induction al as [| a]; [ apply list_norm_0 | simpl ].
unfold list_norm.
remember list_remove_trailing_0s as f; simpl; subst f.
rewrite Nat.add_0_r.
bbb.

Lemma List_repeat_succ_app : ∀ A (a : A) n,
  repeat a (S n) = repeat a n ++ [a].
Proof.
intros; simpl.
induction n; [ easy | simpl ].
now rewrite <- IHn.
Qed.

Lemma list_norm_cons_repeat_0 {r : radix} : ∀ a n,
  list_norm (a :: repeat 0 n) = list_norm [a].
Proof.
intros.
induction n; [ easy | ].
destruct a.
 rewrite list_norm_0 in IHn.
 rewrite list_norm_0.
 now apply list_norm_cons_0.

 rewrite <- IHn.
 rewrite List_repeat_succ_app.

bbb.

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
