(* Natural numbers in any radix. *)

Require Import Utf8 Arith Psatz List.
Import ListNotations.

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
    xI 9 (xI 3 (xI 6 (xH 4))) *)

Record pdigit {r : radix} :=
  mkpdig { pdig : nat; pdig_lt_rad : pdig < rad; pdig_ne_0 : pdig ≠ 0 }.

Inductive xpositive {r : radix} :=
  | xH : pdigit → xpositive
  | xI : digit → xpositive → xpositive.

(* Number in radix r: 0 (x0) or positive number (xpos rpositive) *)

Inductive xnat {r : radix} :=
  | x0 : xnat
  | xpos : xpositive → xnat.

Definition pdigit_1 {r : radix} := mkpdig _ 1 radix_gt_1 (Nat.neq_succ_0 0).

Fixpoint rpon {r : radix} iter n :=
  match iter with
  | 0 => xH pdigit_1
  | S i =>
     match lt_dec (S n) rad with
     | left P => xH (mkpdig _ (S n) P (Nat.neq_succ_0 n))
     | right _ =>
         let Sn_lt_rad := Nat.mod_upper_bound (S n) rad radix_ne_0 in
         let d := mkdig _ (S n mod rad) Sn_lt_rad in
         xI d (rpon i ((S n - rad) / rad))
     end
  end.

Definition xpositive_of_nat {r : radix} n := rpon n n.

Definition xnat_of_nat {r : radix} n :=
  match n with
  | 0 => x0
  | S n => xpos (xpositive_of_nat n)
  end.

Lemma ten_ge_two : 10 ≥ 2.
Proof.
apply -> Nat.succ_le_mono.
apply -> Nat.succ_le_mono.
apply Nat.le_0_l.
Qed.

Lemma two_ge_two : 2 ≥ 2.
Proof. lia. Qed.

Definition radix_2 := {| rad := 2; rad_ge_2 := two_ge_two |}.
Definition radix_10 := {| rad := 10; rad_ge_2 := ten_ge_two |}.

Lemma nz_add_nz : ∀ a b, a ≠ 0 → a + b ≠ 0.
Proof.
intros.
destruct a.
 exfalso; apply H; reflexivity.
 simpl; apply Nat.neq_succ_0.
Qed.

Lemma lt_lt_add_lt : ∀ a b c, a < c → b < c → a + b - c < c.
Proof.
intros * Ha Hb; lia.
Qed.

Fixpoint xpositive_add {r : radix} a b :=
  match a with
  | xH apd =>
      match b with
      | xH bpd =>
          let pd := pdig apd + pdig bpd in
          match lt_dec pd rad with
          | left ltp =>
              let nzp := nz_add_nz (pdig apd) (pdig bpd) (pdig_ne_0 apd) in
              xH (mkpdig _ pd ltp nzp)
          | right gep =>
              let pd := pdig apd + pdig bpd - rad in
              let ltp :=
                lt_lt_add_lt (pdig apd) (pdig bpd) rad (pdig_lt_rad apd)
                  (pdig_lt_rad bpd)
              in
              xI (mkdig _ pd ltp) (xH pdigit_1)
          end
      | xI bd b' => (* not impl *) xH pdigit_1
      end
  | xI ad a' => (* not impl *) xH pdigit_1
  end.

Fixpoint xnat_add {r : radix} a b :=
  match a with
  | x0 => b
  | xpos ap =>
       match b with
       | x0 => a
       | xpos bp => xpos (xpositive_add ap bp)
       end
  end.

Fixpoint list_of_xpositive {r : radix} a :=
  match a with
  | xH pd => [pdig pd]
  | xI d xp => list_of_xpositive xp ++ [dig d]
  end.

Definition list_of_xnat {r : radix} a :=
  match a with
  | x0 => [0]
  | xpos ap => list_of_xpositive ap
  end.

Delimit Scope xnat_scope with X.
Notation "a + b" := (xnat_add a b) : xnat_scope.

Compute (@list_of_xnat radix_10 (xnat_of_nat 4649)).
Compute (@list_of_xnat radix_10 (xnat_of_nat 2 + xnat_of_nat 2)%X).
Compute (@list_of_xnat radix_10 (xnat_of_nat 6 + xnat_of_nat 7)%X).
Compute (@list_of_xnat radix_2 (xnat_of_nat 1 + xnat_of_nat 1)%X).
Compute (@list_of_xnat radix_2 (xnat_of_nat 1 + xnat_of_nat 2)%X).
