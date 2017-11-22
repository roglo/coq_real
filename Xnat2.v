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

Definition list_spread {r : radix} al := move_carry 0 al.

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
  list_remove_trailing_0s (list_spread al).

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

Lemma nat_of_list_rem_tr_cons {r : radix} : ∀ a al, 2 ≤ rad →
  nat_of_list 0 (list_remove_trailing_0s (a :: list_spread al)) =
  nat_of_list 0 (list_remove_trailing_0s (list_spread (a :: al))).
Proof.
intros * Hr.
unfold list_spread; simpl.
rewrite Nat.add_0_r.
unfold list_remove_trailing_0s; simpl.
destruct a.
 rewrite Nat.mod_0_l; [ | lia ].
 rewrite Nat.div_0_l; [ easy | lia ].

 rewrite list_rem_head_app_succ; simpl.
 rewrite List.rev_unit; simpl.
 destruct (zerop (S a mod rad)) as [Ha| Ha].
  rewrite Ha.
bbb.

intros * Hr.
unfold list_spread; simpl.
rewrite Nat.add_0_r.
unfold list_remove_trailing_0s; simpl.
destruct al as [| a₁ al]; simpl.
 destruct a; simpl.
  rewrite Nat.div_0_l; [ simpl | lia ].
  rewrite Nat.mod_0_l; [ easy | lia ].

  destruct (zerop (S a / rad)) as [Ha| Ha]; simpl.
   apply Nat.div_small_iff in Ha; [ | lia ].
   now rewrite Nat.mod_small.

   rewrite <- List.app_assoc; simpl.

bbb.

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

Theorem list_spread_0 {r : radix} : list_spread [0] = [0].
Proof.
unfold list_spread; simpl.
destruct (zerop rad) as [Hr| Hr]; [ now rewrite Hr | ].
rewrite Nat.mod_0_l; [ | lia ].
rewrite Nat.div_0_l; [ easy | lia ].
Qed.

Theorem list_norm_0 {r : radix} : list_norm [0] = [].
Proof.
intros.
unfold list_norm.
now rewrite list_spread_0.
Qed.

Lemma list_norm_cons_0 {r : radix} : ∀ al,
  list_norm al = [] → list_norm (0 :: al) = [].
Proof.
intros * Hal.
destruct (zerop rad) as [Hr| Hr].
 unfold list_norm; simpl.
 unfold list_norm, list_spread in Hal.
 now rewrite Hr; simpl; rewrite Hal.

 induction al as [| a]; [ apply list_norm_0 | ].
 unfold list_norm, list_spread in Hal.
 remember list_remove_trailing_0s as f; simpl in Hal; subst f.
 rewrite Nat.add_0_r in Hal.
 unfold list_norm, list_spread.
 remember list_remove_trailing_0s as f; simpl; subst f.
 rewrite Nat.mod_0_l; [ | lia ].
 rewrite Nat.div_0_l; [ | lia ].
 rewrite Nat.add_0_r.
bbb.

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
 apply Nat.eq_mul_0 in Hn.
 destruct Hn as [Hn| Hn].
  specialize (IHal Hn).
  clear Hn.

bbb.

  unfold list_norm; simpl.
  rewrite Nat.mod_0_l; [ | lia ].
  rewrite Nat.div_0_l; [ | lia ].

   simpl in Hn.
   apply Nat.eq_add_0 in Hn.
   destruct Hn as (Hn, Ha); subst a.

intros Hr *.
unfold list_norm, list_spread.
induction al as [| a]; [ easy | simpl ].
Print list_of_nat.

rewrite Nat.add_0_r.
remember (a mod rad) as n eqn:Hn; symmetry in Hn.
destruct n.
 apply Nat.mod_divides in Hn; [ | lia ].
 destruct Hn as (n, Hn); rewrite Nat.mul_comm in Hn.
 subst a.
 rewrite Nat.div_mul; [ | lia ].
 remember (list_remove_trailing_0s (move_carry n al)) as al' eqn:Hal'.
 symmetry in Hal'.
 destruct al' as [| a'].
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
