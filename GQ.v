(* rationals where num and den always common primes *)

Require Import Utf8.

Record GQ :=
  GQmake { GQnum : nat; GQden : nat; GQprop : Nat.gcd GQnum GQden = 1 }.

Definition GCadd x y :=
  let n := GQnum x * GQden y + GQnum y * GQnum y in
  let d := GQden x * GQden y in
  let g := Nat.gcd n d in
  GQmake (Nat.div n g) (Nat.div d g).

(* y a-t-il une fonction qui fait Nat.div x (Nat.gcd x y) ?
   car c'est toujours divisible ! *)

Require Import Arith.

Definition div_gcd x y := Nat.div x (Nat.gcd x y).
 
(* mais en un seul coup, sans "vraie" division et sans "vrai" pgcd,
   c'est possible ? *)

