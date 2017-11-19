(* natura numbers in any radix; second version; without proofs *)

Require Import Utf8 Arith List.
Import ListNotations.

Class radix := { rad : nat }.

Definition radix_2 := {| rad := 2 |}.
Definition radix_10 := {| rad := 10 |}.

Record xnat := xn { xnatv : list nat }.

Fixpoint move_carry {r : radix} iter al carry :=
  match iter with
  | 0 => []
  | S i =>
      match al with
      | [] =>
          if zerop carry then []
          else carry mod rad :: move_carry i [] (carry / rad)
      | a :: al' =>
          (a + carry) mod rad :: move_carry i al' ((a + carry) / rad)
      end
  end.

Definition num_with_dig {r : radix} a :=
  xn (move_carry (List.fold_left max (xnatv a) 0) (xnatv a) 0).

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

Compute (xnatv_add [2] [2]).
Compute (@xnat_add radix_10 (xn [4; 2]) (xn [11])).
Compute (@xnat_add radix_2 (xn [4; 2]) (xn [11])).
Compute (@num_with_dig radix_2 (xn [0])).
Compute (@num_with_dig radix_2 (xn [1])).
Compute (@num_with_dig radix_2 (xn [2])).
Compute (@num_with_dig radix_2 (xn [3])).
