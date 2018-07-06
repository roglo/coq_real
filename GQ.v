(* rationals where num and den always common primes *)

Require Import Utf8.
Require Import Arith.

Record GQ :=
  GQmake
    { GQnum1 : nat; GQden1 : nat;
      GQprop : Nat.gcd (S GQnum1) (S GQden1) = 1 }.

Theorem Pouet : ∀ n d g,
  g = Nat.gcd (S n) (S d)
  → Nat.gcd (Nat.div (S n) g) (Nat.div (S d) g) = 1.
Proof.
intros * Hg.
rewrite Nat.gcd_div_gcd; [ easy | | easy ].
subst g; intros H.
now apply Nat.gcd_eq_0 in H.
Qed.

Definition GCadd x y :=
  let n := S (GQnum1 x) * S (GQden1 y) + S (GQnum1 y) * S (GQnum1 y) - 1 in
  let d := S (GQden1 x) * S (GQden1 y) - 1 in
  let g := Nat.gcd n d in
  GQmake (Nat.div n g) (Nat.div d g).
...

 (Pouet n d g).

Print GCadd.

Print GCadd.

Definition div_gcd x y := Nat.div x (Nat.gcd x y).

(* y a-t-il une fonction qui fait Nat.div x (Nat.gcd x y) ?
   car c'est toujours divisible ! *)
 
(* mais en un seul coup, sans "vraie" division et sans "vrai" pgcd,
   c'est possible ? *)

Print Nat.gcd.
