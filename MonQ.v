Require Import Utf8.
Require Import Arith.

Delimit Scope MQ_scope with MQ.

Record MQ := MQmake { MQsign : bool; MQnum : nat; MQden : nat }.
Arguments MQsign x%MQ : rename.
Arguments MQnum x%MQ : rename.
Arguments MQden x%MQ : rename.

(*
Require Import QArith.
Set Printing All.
Check 0%Q.
About 0.

Close Scope Q.
About 0%Q.

About "<="%Q.
Print Qle.
*)

Definition MQadd_sign x y :=
  if MQsign x then
    if MQsign y then true
    else if lt_dec (MQnum x * MQden y) (MQnum y * MQden x) then false
    else true
  else if MQsign y then
    if lt_dec (MQnum x * MQden y) (MQnum y * MQden x) then true
    else false
   else false.

Definition MQadd_num x y :=
  if MQsign x then
    if MQsign y then MQnum x * MQden y + MQnum y * MQden x
    else if lt_dec (MQnum x * MQden y) (MQnum y * MQden x) then
      MQnum y * MQden x - MQnum x * MQden y
    else
      MQnum x * MQden y - MQnum y * MQden x
  else if MQsign y then
    if lt_dec (MQnum x * MQden y) (MQnum y * MQden x) then
      MQnum y * MQden x - MQnum x * MQden y
    else
      MQnum x * MQden y - MQnum y * MQden x
  else MQnum x * MQden y + MQnum y * MQden x.
Definition MQadd_den x y := MQden x * MQden y.

Definition MQadd x y :=
  MQmake (MQadd_sign x y) (MQadd_num x y) (MQadd_den x y).
Arguments MQadd x%MQ y%MQ.

Definition MQopp x := MQmake (negb (MQsign x)) (MQnum x) (MQden x).
Definition MQsub x y := MQadd x (MQopp y).
Arguments MQopp x%MQ.

Definition MQzerop x := zerop (MQnum x).
Definition MQnorm x := if zerop (MQnum x) then MQmake true 0 1 else x.
Definition MQnorm_sign x := if zerop (MQnum x) then true else MQsign x.
Arguments MQnorm_sign x%MQ.

Definition MQeq x y :=
  if MQnorm_sign x then
    if MQnorm_sign y then MQnum x * MQden y = MQnum y * MQden x else False
  else
    if MQnorm_sign y then False else MQnum x * MQden y = MQnum y * MQden x.

Definition MQabs x := MQmake true (MQnum x) (MQden x).
Definition MQabs_lt x y := MQnum x * MQden y < MQnum y * MQden x.
Definition MQabs_le x y := MQnum x * MQden y ≤ MQnum y * MQden x.
Definition MQlt x y :=
  if MQsign x then
    if MQsign y then MQabs_lt x y else False
  else
    if MQsign y then True else MQabs_lt y x.
Definition MQle x y :=
  if MQsign x then
    if MQsign y then MQabs_le x y else False
  else
    if MQsign y then True else MQabs_le y x.

Notation "0" := (MQmake true 0 1) : MQ_scope.
Notation "- x" := (MQopp x) : MQ_scope.
Notation "x == y" := (MQeq x y) (at level 70) : MQ_scope.
Notation "x + y" := (MQadd x y) : MQ_scope.
Notation "x - y" := (MQsub x y) : MQ_scope.
Notation "x < y" := (MQlt x y) : MQ_scope.
Notation "x ≤ y" := (MQle x y) : MQ_scope.
Notation "x > y" := (¬ MQle x y) : MQ_scope.
Notation "x ≥ y" := (¬ MQlt x y) : MQ_scope.

Theorem MQlt_le_dec : ∀ x y : MQ, {(x < y)%MQ} + {(y ≤ x)%MQ}.
Proof.
intros (xs, xn, xd) (ys, yn, yd).
unfold MQlt, MQle, MQabs_lt, MQabs_le; simpl.
destruct xs, ys.
-destruct (lt_dec (xn * yd) (yn * xd)) as [H1| H1]; [ now left | ].
 now right; apply Nat.nlt_ge.
-now right.
-now left.
-destruct (lt_dec (yn * xd) (xn * yd)) as [H1| H1]; [ now left | ].
 now right; apply Nat.nlt_ge.
Qed.
