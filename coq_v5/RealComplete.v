(* ℝ is complete *)

Require Import Utf8 QArith NPeano Misc.
Require Import Real01 Real RealAdd RealAddGrp.

Open Scope nat_scope.

Definition cauchy_sequence u :=
  ∀ ε, (ε > 0)%R → ∃ N, ∀ p q, p > N → q > N → (R_abs (u p - u q) < ε)%R.

Definition converges_to u r :=
  (∃ N, ∀ n, n > N → R_int r = R_int (u n)) ∧
  (∀ i, ∃ N, ∀ n, n > N → R_frac r.[i] = R_frac (u n).[i]).

Theorem zzz : ∀ u, cauchy_sequence u → ∃ r, converges_to u r.
Proof.
bbb.
