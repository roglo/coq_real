(* rationals where num and den always common primes *)

Require Import Utf8.
Require Import Arith.

Record GQ :=
  GQmake
    { GQnum1 : nat; GQden1 : nat;
      GQprop : Nat.gcd (S GQnum1) (S GQden1) = 1 }.

Theorem glop : ∀ n d (g := Nat.gcd n d),
  Nat.gcd (S (n / g - 1)) (S (d / g - 1)) = 1.
Proof.
intros *.
rewrite <- Nat.sub_succ_l.
-rewrite <- Nat.sub_succ_l.
 +do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
  rewrite Nat.gcd_div_gcd; [ easy | | easy ].
  subst g; intros H.
  apply Nat.gcd_eq_0 in H.
...

Definition GCadd x y :=
  let n := S (GQnum1 x) * S (GQden1 y) + S (GQnum1 y) * S (GQnum1 y) in
  let d := S (GQden1 x) * S (GQden1 y) in
  let g := Nat.gcd n d in
  GQmake (Nat.div n g - 1) (Nat.div d g - 1) (glop n d).

Print GCadd.

Definition div_gcd x y := Nat.div x (Nat.gcd x y).

(* y a-t-il une fonction qui fait Nat.div x (Nat.gcd x y) ?
   car c'est toujours divisible ! *)
 
(* mais en un seul coup, sans "vraie" division et sans "vrai" pgcd,
   c'est possible ? *)

Print Nat.gcd.
