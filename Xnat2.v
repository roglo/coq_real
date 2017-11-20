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

Definition xnat_of_nat {r : radix} n := num_with_dig (xn [n]).
Definition nat_of_xnat {r : radix} a :=
  List.fold_right (λ d accu, accu * rad + d) 0 (xnatv a).

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
induction n.
 unfold nat_of_xnat; simpl.
 rewrite Nat.div_0_l; [ | lia ].
 rewrite Nat.mod_0_l; [ easy | lia ].

 unfold nat_of_xnat, xnat_of_nat; simpl.
 rewrite Nat.add_0_r.
 destruct (zerop (S n / rad)) as [Hs| Hs].
  apply Nat.div_small_iff in Hs; [ | lia ].
  now rewrite Nat.mod_small.

  remember (S n / rad) as carry eqn:Hc.
  replace carry with (0 + carry) by lia.
  rewrite <- move_carry_cons.
  remember (move_carry (S n) carry [0]) as x eqn:Hx.
  simpl in Hx.
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
