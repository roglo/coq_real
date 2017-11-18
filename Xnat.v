(* Natural numbers in any radix. *)

Require Import Utf8 Arith Psatz.

(* Radix *)

Class radix := { rad : nat; rad_ge_2 : rad ≥ 2 }.

Theorem radix_gt_0 {r : radix} : 0 < rad.
Proof.
destruct r as (rad, radi); simpl; lia.
Qed.

Theorem radix_gt_1 {r : radix} : 1 < rad.
Proof.
destruct r as (rad, radi); simpl; lia.
Qed.

Theorem radix_ne_0 {r : radix} : rad ≠ 0.
Proof.
destruct r as (rad, radi); simpl; lia.
Qed.

Hint Resolve radix_gt_0 radix_gt_1 radix_ne_0.

(* Digits *)

Record digit {r : radix} := mkdig { dig : nat; dig_lt_rad : dig < rad }.

Delimit Scope digit_scope with D.

Definition digit_0 {r : radix} := mkdig _ 0 radix_gt_0.
Definition digit_eq {r : radix} (a b : digit) := dig a = dig b.

Notation "0" := (digit_0) : digit_scope.
Notation "a = b" := (digit_eq a b) : digit_scope.
Notation "a ≠ b" := (¬ digit_eq a b) : digit_scope.

(* Positive number in radix r.
   Example: 4639 (when r = 10):
    rI 9 (rI 3 (rI 6 (rH 4))) *)

Record pdigit {r : radix} :=
  mkpdig { pdig : nat; pdig_lt_rad : pdig < rad; pdig_ne_0 : pdig ≠ 0 }.

Inductive rpositive {r : radix} :=
  | rH : pdigit → rpositive
  | rI : digit → rpositive → rpositive.

(* Number in radix r: 0 (I0) or positive number (Ipos rpositive) *)

Inductive xnat {r : radix} :=
  | I0 : xnat
  | Ipos : rpositive → xnat.

Fixpoint rpositive_of_nat {r : digit} n :=
  match lt_dec (S n) rad with
  | left P => rH (mkpdig _ (S n) P (Nat.neq_succ_0 n))
  | right _ => rI (S n mod rad) (rpositive_of_nat ((S n - rad) / rad))
  end.

Definition int_of_nat n :=
  match n with
  | 0 => I0
  | S n => Ipos (rpositive_of_int n)
  end.
