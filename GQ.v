(* rationals where num and den always common primes *)

Require Import Utf8.
Require Import Arith.

Record GQ :=
  GQmake
    { GQnum1 : nat; GQden1 : nat;
      GQprop : Nat.gcd (S GQnum1) (S GQden1) = 1 }.

Theorem GCadd_prop : ∀ x y
  (n := S (GQnum1 x) * S (GQden1 y) + S (GQnum1 y) * S (GQnum1 y))
  (d := S (GQden1 x) * S (GQden1 y))
  (g := Nat.gcd n d),
  Nat.gcd (S (n / g - 1)) (S (d / g - 1)) = 1.
Proof.
intros.
rewrite <- Nat.sub_succ_l.
-rewrite <- Nat.sub_succ_l.
 +do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
  rewrite Nat.gcd_div_gcd; [ easy | | easy ].
  subst g; intros H.
  now apply Nat.gcd_eq_0 in H.
 +specialize (Nat.gcd_divide_r n d) as H.
  fold g in H.
  unfold Nat.divide in H.
  destruct H as (c & Hc).
  rewrite Hc, Nat.div_mul.
  *destruct c; [ easy | apply Nat.lt_0_succ ].
  *now intros H; rewrite Nat.mul_comm, H in Hc.
-specialize (Nat.gcd_divide_l n d) as H.
 fold g in H.
 unfold Nat.divide in H.
 destruct H as (c & Hc).
 rewrite Hc, Nat.div_mul.
 *destruct c; [ easy | apply Nat.lt_0_succ ].
 *now intros H; rewrite Nat.mul_comm, H in Hc.
Qed.

Definition GCadd x y :=
  let n := S (GQnum1 x) * S (GQden1 y) + S (GQnum1 y) * S (GQnum1 y) in
  let d := S (GQden1 x) * S (GQden1 y) in
  let g := Nat.gcd n d in
  GQmake (Nat.div n g - 1) (Nat.div d g - 1) (GCadd_prop x y).

...

Definition div_gcd x y := Nat.div x (Nat.gcd x y).

(* y a-t-il une fonction qui fait Nat.div x (Nat.gcd x y) ?
   car c'est toujours divisible ! *)
 
(* mais en un seul coup, sans "vraie" division et sans "vrai" pgcd,
   c'est possible ? *)

Print Nat.gcd.
