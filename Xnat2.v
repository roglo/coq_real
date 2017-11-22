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
  move_carry carry [n].
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

(*
Theorem move_carry_cons {r : radix} : ∀ a al carry iter,
  move_carry (S iter) carry (a :: al) =
  (a + carry) mod rad :: move_carry iter ((a + carry) / rad) al.
Proof. easy. Qed.
*)

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
intros Hr *; simpl.
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

(*
Definition iter_sup al := List.length al + List.fold_left max al 1.
*)
Definition list_spread {r : radix} al := move_carry 0 al.

Fixpoint list_remove_heading_0s al :=
  match al with
  | 0 :: al' => list_remove_heading_0s al'
  | _ => al
  end.

Definition list_remove_trailing_0s {r : radix} al :=
  List.rev (list_remove_heading_0s (List.rev al)).

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

Lemma nat_of_list_removed_trailing_0s_mul {r : radix} : ∀ a al,
  nat_of_list 0 (list_remove_trailing_0s al) * rad + a =
  nat_of_list 0 (list_remove_trailing_0s (a :: al)).
Proof.
intros.
unfold list_remove_trailing_0s; simpl.
rewrite list_remove_heading_cons; simpl.
remember(list_remove_heading_0s (rev al)) as bl eqn:Hbl.
symmetry in Hbl.
destruct bl as [| b bl]; [ now destruct a | simpl ].
now rewrite List.rev_app_distr.
Qed.

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

Lemma list_of_nat_inv {r : radix} : 2 ≤ rad →
  ∀ al, list_of_nat 0 (nat_of_list 0 al) = list_norm al.
Proof.
intros Hr *.
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
