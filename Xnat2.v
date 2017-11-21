(* natura numbers in any radix; second version; without proofs *)

Require Import Utf8 Arith Psatz List.
Import ListNotations.

Class radix := { rad : nat }.

Definition radix_2 := {| rad := 2 |}.
Definition radix_10 := {| rad := 10 |}.

Record xnat := xn { xnatv : list nat }.

Fixpoint move_carry {r : radix} iter carry al :=
  match iter with
  | 0 => [42]
  | S i =>
      match al with
      | [] =>
          if zerop carry then []
          else carry mod rad :: move_carry i (carry / rad) []
      | a :: al' =>
          (a + carry) mod rad :: move_carry i ((a + carry) / rad) al'
      end
  end.

Definition list_of_nat {r : radix} carry n :=
  move_carry (n + 2) carry [n].
Definition nat_of_list {r : radix} accu al :=
  List.fold_right (λ a accu, accu * rad + a) accu al.

Definition xnat_of_nat {r : radix} n := xn (list_of_nat 0 n).
Definition nat_of_xnat {r : radix} a := nat_of_list 0 (xnatv a).

Compute (@xnat_of_nat radix_10 0).
Compute (@xnat_of_nat radix_10 10030).

Theorem move_carry_cons {r : radix} : ∀ a al carry iter,
  move_carry (S iter) carry (a :: al) =
  (a + carry) mod rad :: move_carry iter ((a + carry) / rad) al.
Proof. easy. Qed.

Lemma nat_of_list_inv {r : radix} : 2 ≤ rad →
  ∀ n, nat_of_list 0 (list_of_nat 0 n) = n.
Proof.
intros Hr *.
unfold list_of_nat.
symmetry.
remember (n + 2) as m eqn:Hm.
assert (H : n + 2 ≤ m) by lia.
clear Hm; rename H into Hm.
revert n Hm.
induction m; intros; simpl; [ lia | ].
rewrite Nat.add_0_r.
destruct m; [ lia | simpl ].
destruct (zerop (n / rad)) as [Hs| Hs].
 apply Nat.div_small_iff in Hs; [ simpl | lia ].
 now rewrite Nat.mod_small.

 replace (n / rad) with (n / rad + 0) by lia.
 rewrite <- move_carry_cons.
 rewrite <- IHm.
  rewrite Nat.mul_comm.
  apply Nat.div_mod; lia.

  assert (Hnm : n ≤ m) by lia; clear Hm.
  rewrite Nat.add_comm; simpl.
  apply -> Nat.succ_le_mono.
  eapply Nat.le_trans; [ | eassumption ].
  apply -> Nat.div_str_pos_iff in Hs; [ | lia ].
  clear - Hr Hs.
  destruct rad as [| m]; [ lia | ].
  destruct m as [| m]; [ lia | clear Hr ].
  apply Nat.div_lt; lia.
Qed.

Theorem nat_of_xnat_inv {r : radix} : 2 ≤ rad →
  ∀ n, nat_of_xnat (xnat_of_nat n) = n.
Proof.
intros Hr *.
now apply nat_of_list_inv.
Qed.

Definition iter_sup al := List.length al + List.fold_left max al 1.
Definition list_spread {r : radix} al := move_carry (iter_sup al) 0 al.

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

Lemma nat_of_list_removed_trailing_0_s_mul {r : radix} : ∀ a al,
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

Lemma nat_of_list_rem_tr_cons {r : radix} : ∀ a al,
  nat_of_list 0 (list_remove_trailing_0s (a :: list_spread al)) =
  nat_of_list 0 (list_remove_trailing_0s (list_spread (a :: al))).
Proof.
intros.
unfold list_spread.
remember (iter_sup al) as n eqn:Hn.
remember (iter_sup (a :: al)) as m eqn:Hm.
symmetry in Hm, Hn.
unfold iter_sup in Hn, Hm.
remember fold_left as f; simpl in Hm; subst f.
remember 1 as x; simpl in Hm; subst x.
destruct m; [ easy | ].
apply Nat.succ_inj in Hm; simpl.
rewrite Nat.add_0_r.
destruct (lt_dec a rad) as [Har| Har].
 rewrite Nat.mod_small; [ | easy ].
 rewrite Nat.div_small; [ | easy ].

 (* prouver que iter_sup fait suffisamment d'itérations *)
bbb.
 revert n m Hn Hm.
 induction al as [| b al]; intros.
  simpl in Hn; subst n.
  remember 1 as x; simpl in Hm; subst x.
  destruct m; [ now destruct a | easy ].

  destruct m; [ easy | ].
  destruct n; [ easy | ].
  simpl.
  rewrite Nat.add_0_r.

bbb.

intros.
unfold list_spread.
remember (iter_sup (a :: al)) as n eqn:Hn.
symmetry in Hn; simpl in Hn.
destruct n.
 unfold iter_sup in Hn.
 now apply Nat.eq_add_0 in Hn.

 rewrite move_carry_cons.
 rewrite Nat.add_0_r.
 rewrite <- nat_of_list_removed_trailing_0_s_mul.
 rewrite <- nat_of_list_removed_trailing_0_s_mul.
 destruct (lt_dec a rad) as [Har| Har].
  rewrite Nat.mod_small; [ f_equal; f_equal | easy ].
  rewrite Nat.div_small; [ | easy ].
  destruct n.
   exfalso.
   unfold iter_sup in Hn; simpl in Hn.
   apply Nat.succ_inj in Hn.
   apply Nat.eq_add_0 in Hn.
   destruct Hn as (Hn, Ha).
   apply length_zero_iff_nil in Hn; subst al.
   now destruct a.

   simpl.
   destruct al as [| b al]; [ easy | ].
   rewrite Nat.add_0_r; simpl.
   rewrite <- nat_of_list_removed_trailing_0_s_mul.
   rewrite <- nat_of_list_removed_trailing_0_s_mul.
   rewrite Nat.add_0_r.
   destruct b.
    rewrite Nat.div_0_l; [ | lia ].
    rewrite Nat.mod_0_l; [ | lia ].
    f_equal; f_equal.
    destruct n.
     exfalso.
     unfold iter_sup in Hn; simpl in Hn.
     do 2 apply Nat.succ_inj in Hn.
     apply Nat.eq_add_0 in Hn.
     destruct Hn as (Hn, Ha).
     apply length_zero_iff_nil in Hn; subst al.
     now destruct a.

     simpl.
bbb.

Lemma nat_of_list_norm_cons {r : radix} : ∀ a al,
  nat_of_list 0 (list_norm al) * rad + a = nat_of_list 0 (list_norm (a :: al)).
Proof.
intros.
unfold list_norm.
rewrite nat_of_list_removed_trailing_0_s_mul.
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
