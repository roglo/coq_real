(* natura numbers in any radix; second version; without proofs *)

Require Import Utf8 Arith Psatz List.
Import ListNotations.

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

(*
Lemma list_remove_heading_cons : ∀ al bl,
  list_remove_heading_0s (al ++ bl) =
  match list_remove_heading_0s al with
  | [] => list_remove_heading_0s bl
  | a :: al' => a :: al' ++ bl
  end.
Proof.
intros.
induction al as [| a al]; [ easy | simpl ].
now destruct a.
Qed.
*)

Lemma nat_of_list_removed_trailing_0s_mul {r : radix} : ∀ a al,
  nat_of_list 0 (list_remove_trailing_0s al) * rad + a =
  nat_of_list 0 (list_remove_trailing_0s (a :: al)).
Proof.
intros; simpl.
remember (list_remove_trailing_0s al) as al' eqn:Hal.
symmetry in Hal.
now destruct a; [ destruct al' | ].
Qed.

(*
Lemma list_rem_head_app_succ : ∀ al₁ al₂ a,
  list_remove_heading_0s (al₁ ++ S a :: al₂) =
  list_remove_heading_0s al₁ ++ S a :: al₂.
Proof.
intros.
induction al₁ as [| a₁]; [ easy | simpl ].
now destruct a₁.
Qed.

Lemma nat_of_list_app {r : radix} : ∀ a al,
  nat_of_list 0 (al ++ [a]) =
  nat_of_list 0 al + rad ^ length al * a.
Proof.
intros.
induction al as [| a₁]; simpl; [ lia | ].
rewrite IHal; lia.
Qed.

Lemma nat_of_list_norm_cons {r : radix} : ∀ a al,
  nat_of_list 0 (list_norm al) * rad + a = nat_of_list 0 (list_norm (a :: al)).
Proof.
intros.
unfold list_norm.
rewrite nat_of_list_removed_trailing_0s_mul.
bbb.

Lemma nat_of_list_norm_eq {r : radix} : ∀ al, 2 ≤ rad →
  nat_of_list 0 al = nat_of_list 0 (list_norm al).
Proof.
intros * Hr.
induction al as [| a al]; [ easy | simpl ].
rewrite IHal; clear IHal.
bbb.
*)

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

Lemma list_cons_inv : ∀ A (a b : A) al bl,
  a :: al = b :: bl → a = b ∧ al = bl.
Proof.
intros * Hab.
now inversion Hab.
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
 apply list_cons_inv in Ha.
 destruct Ha as (Ha, Hal); subst a.
 now rewrite IHal.
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
 apply list_cons_inv in Hal.
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

Lemma list_of_nat_inv {r : radix} : 2 ≤ rad →
  ∀ al, list_of_nat 0 (nat_of_list 0 al) = list_norm al.
Proof.
intros Hr *.
unfold list_of_nat.
destruct (zerop (nat_of_list 0 al)) as [Ha| Ha].
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
