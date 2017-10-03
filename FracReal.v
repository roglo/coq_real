(* Real between 0 and 1, i.e. fractional part of a real. *)

Require Import Utf8.

Class digit := {

Record FracReal := { freal : nat → digit }.