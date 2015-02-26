(* ℝ is complete *)

Require Import Utf8 QArith NPeano Misc.
Require Import Real01 Real RealAdd RealAddGrp.

Open Scope nat_scope.

Definition cauchy_sequence u :=
  ∀ ε, (ε > 0)%R → ∃ N, ∀ p q, p > N → q > N → (R_abs (u p - u q) < ε)%R.

Definition converges_to u r :=
  ∀ ε, (ε > 0)%R → ∃ N, ∀ n, n > N → (R_abs (r - u n) < ε)%R.

Definition cauchy_sequence_limit u :=
  {| R_int :=
     R_frac i := |}.

Theorem zzz : ∀ u, cauchy_sequence u → ∃ r, converges_to u r.
Proof.
intros u Hc.
unfold cauchy_sequence in Hc.
unfold converges_to.
bbb.
