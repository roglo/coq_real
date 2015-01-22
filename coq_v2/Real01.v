Require Import Utf8.

Set Implicit Arguments.

(* I = interval [0..1] of ℝ *)
Record I := { idig : nat → bool }.

(* I represention by sequences of natural *)
Record Iwn := { inat : nat → nat }.
