Require Import Utf8 NPeano.
Require Import Oracle.

(* I = interval [0..1] of ℝ *)
Record I := { rm : nat → bool }.

Definition I_zero := {| rm i := false |}.
Definition I_one := {| rm i := true |}.

Notation "s .[ i ]" := (rm s i) (at level 15, i at level 200).

Delimit Scope I_scope with I.
Notation "0" := I_zero : I_scope.
Notation "1" := I_one : I_scope.

Definition d2n (d : bool) := if d then 1 else 0.
Definition n2d (n : nat) := negb (Nat.eqb n 0).

Record SeqNat := { sn : nat → nat }.

Definition modb n := n mod 2.
Definition divb n := n / 2.

Definition test_not_1 u i j := negb (Nat.eqb (sn u (i + j)) 1).
Definition fst_not_1 u i := first_true (test_not_1 u i).

Definition carry u i :=
  match fst_not_1 u (S i) with
  | Some di => divb (sn u (S (i + di)))
  | None => 1 (* I can put 0 if there are problems with I_eq_ext; in that
                 case, I must implement a normalisation function using the
                 oracle. *)
  end.

Definition I_propag_carry_once u := {| sn i := modb (sn u i) + carry u i |}.

Fixpoint I_propag_carry n u :=
  match n with
  | 0 => u
  | S n1 => I_propag_carry_once (I_propag_carry n1 u)
  end.

Definition I_eq_ext x y := ∀ i, x.[i] = y.[i].
Arguments I_eq_ext x%I y%I.

Theorem fst_not_1_iff : ∀ u i odi, odi = fst_not_1 u i ↔
  match odi with
  | Some di => (∀ dj, dj < di → sn u (i + dj) = 1) ∧ sn u (i + di) ≠ 1
  | None => ∀ dj, sn u (i + dj) = 1
  end.
Proof.
intros u i odi.
bbb.
