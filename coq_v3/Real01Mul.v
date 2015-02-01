(* multiplication in I *)

Require Import Utf8.
Require Import Real01.

Fixpoint summation_aux b len g :=
  match len with
  | O => 0
  | S len₁ => g b + summation_aux (S b) len₁ g
  end.

Definition summation b e g := summation_aux b (S e - b) g.

Notation "'Σ' ( i = b , e ) , g" := (summation b e (λ i, (g)))
  (at level 0, i at level 0, b at level 60, e at level 60, g at level 40).

Definition b2n (b : bool) := if b then 1 else 0.

(* just sequence of convolution products, but no carry computed yet. *)
Definition I_mul_i x y i := Σ (j=1,i), (b2n (x.[j-1]) * b2n (y.[i-j])).
