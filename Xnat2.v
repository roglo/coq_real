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

Definition iter_sup al := List.length al + List.fold_left max al 1.

Definition num_with_dig {r : radix} a :=
  xn (move_carry (iter_sup (xnatv a)) 0 (xnatv a)).

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

Theorem nat_of_xnat_inv {r : radix} : 2 ≤ rad →
  ∀ n, n = nat_of_xnat (xnat_of_nat n).
Proof.
intros Hr *.
unfold nat_of_xnat, xnat_of_nat; simpl.
induction n; simpl.
 rewrite Nat.div_0_l; [ | lia ].
 rewrite Nat.mod_0_l; [ easy | lia ].

 rewrite Nat.add_0_r.
 replace (n + 2) with (1 + n + 1) by lia; simpl.
 remember (S n / rad) as carry eqn:Hc.
 destruct (zerop carry) as [Hs| Hs].
  rewrite Nat.mod_small; [ easy | ].
  subst carry.
  rewrite Nat.div_small_iff in Hs; [ easy | lia ].

  replace carry with (0 + carry) by easy.
  rewrite <- move_carry_cons.
  rewrite Nat.add_1_r; simpl.
  destruct (zerop (carry / rad)) as [Hs1| Hs1].
   apply Nat.div_small_iff in Hs1; [ | lia ].
   rewrite Nat.mod_small; [ simpl | easy ].
   subst carry; rewrite Nat.mul_comm.
   apply Nat.div_mod; lia.

   remember (carry / rad) as c eqn:Hc2; subst carry.
   replace c with (0 + c) by easy.
   rewrite <- move_carry_cons.
   remember (S n / rad) as c3 eqn:Hc3.
   destruct n.
    subst c3.
    rewrite Nat.div_1_l in Hs; [ easy | lia ].

    simpl.
    destruct (zerop (c / rad)) as [Hs2| Hs2].
     apply Nat.div_small_iff in Hs2; [ | lia ].
     rewrite Nat.mod_small; [ simpl | easy ].
     subst c3.
     remember (S (S n)) as s.
     remember (c * rad + (s / rad) mod rad) as t.
     rewrite Hc2, Nat.mul_comm in Heqt.
     rewrite <- Nat.div_mod in Heqt; [ | lia ].
     subst t.
     rewrite Nat.mul_comm.
     apply Nat.div_mod; lia.
bbb.

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
  num_with_dig (xn (xnatv_add (xnatv a) (xnatv b))).

Theorem xnat_of_nat_inv {r : radix} : ∀ a, a = xnat_of_nat (nat_of_xnat a).
bbb.

Compute (xnatv_add [2] [2]).
Compute (@xnat_add radix_10 (xn [4; 2]) (xn [11])).
Compute (@xnat_add radix_2 (xn [4; 2]) (xn [11])).
Compute (@num_with_dig radix_2 (xn [0; 0])).
Compute (@num_with_dig radix_2 (xn [1; 0])).
Compute (@num_with_dig radix_2 (xn [2; 0])).
Compute (@num_with_dig radix_2 (xn [3])).
Compute (@num_with_dig radix_2 (xn [4])).
Compute (@num_with_dig radix_2 (xn [5])).
Compute (@num_with_dig radix_2 (xn [6])).
Compute (@num_with_dig radix_2 (xn [7])).
Compute (@num_with_dig radix_10 (xn [11; 11; 11; 11; 11])).

Compute (@num_with_dig radix_2 (xn [11; 11; 11; 11; 11])).
Compute (@num_with_dig radix_2 (xn [341])).
Compute (@xnat_of_nat radix_2 341).
Compute (11 + 2 * 11 + 4 * 11 + 8 * 11 + 16 * 11).

Compute (@xnat_of_nat radix_10 341).
Compute (@nat_of_xnat radix_10 (@xnat_of_nat radix_10 341)).
