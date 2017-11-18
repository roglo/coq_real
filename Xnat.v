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

Inductive xpositive {r : radix} :=
  | rH : pdigit → xpositive
  | rI : digit → xpositive → xpositive.

(* Number in radix r: 0 (I0) or positive number (Ipos rpositive) *)

Inductive xnat {r : radix} :=
  | I0 : xnat
  | Ipos : xpositive → xnat.

Definition pdigit_1 {r : radix} := mkpdig _ 1 radix_gt_1 (Nat.neq_succ_0 0).

Fixpoint rpon {r : radix} iter n :=
  match iter with
  | 0 => rH pdigit_1
  | S i =>
     match lt_dec (S n) rad with
     | left P => rH (mkpdig _ (S n) P (Nat.neq_succ_0 n))
     | right _ =>
         let Sn_lt_rad := Nat.mod_upper_bound (S n) rad radix_ne_0 in
         let d := mkdig _ (S n mod rad) Sn_lt_rad in
         rI d (rpon i ((S n - rad) / rad))
     end
  end.

Definition xpositive_of_nat {r : radix} n := rpon n n.

Definition xnat_of_nat {r : radix} n :=
  match n with
  | 0 => I0
  | S n => Ipos (xpositive_of_nat n)
  end.

Lemma ten_ge_two : 10 ≥ 2.
Proof.
apply -> Nat.succ_le_mono.
apply -> Nat.succ_le_mono.
apply Nat.le_0_l.
Qed.

Definition radix_10 := {| rad := 10; rad_ge_2 := ten_ge_two |}.
Compute (@xnat_of_nat radix_10 4639).

Lemma nz_add_nz a b : a ≠ 0 → a + b ≠ 0.
Proof.
intros.
destruct a.
 exfalso; apply H; reflexivity.
 simpl; apply Nat.neq_succ_0.
Qed.

Fixpoint xpositive_add {r : radix} a b :=
  match a with
  | rH apd =>
      match b with
      | rH bpd =>
          let pd := pdig apd + pdig bpd in
          match lt_dec pd rad with
          | left lt =>
              let ne0 := nz_add_nz (pdig apd) (pdig bpd) (pdig_ne_0 apd) in
              rH (mkpdig _ pd lt ne0)
          | right _ => (* not impl *) rH pdigit_1
          end
      | rI bd b' => (* not impl *) rH pdigit_1
      end
  | rI ad a' => (* not impl *) rH pdigit_1
  end.

Fixpoint xnat_add {r : radix} a b :=
  match a with
  | I0 => b
  | Ipos ap =>
       match b with
       | I0 => a
       | Ipos bp => Ipos (xpositive_add ap bp)
       end
  end.

Compute (@xnat_of_nat radix_10 2).
Compute (@xnat_add radix_10 (xnat_of_nat 2) (xnat_of_nat 2)).
