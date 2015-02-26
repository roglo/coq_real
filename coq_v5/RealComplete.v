(* ℝ is complete *)

Require Import Utf8 QArith NPeano Misc.
Require Import Real01 Real RealAdd RealAddGrp.

Open Scope nat_scope.

Definition cauchy_sequence u :=
  ∀ ε, (ε > 0)%R → ∃ N, ∀ p q, p > N → q > N → (R_abs (u p - u q) < ε)%R.

Definition converges_to u r :=
  ∀ ε, (ε > 0)%R → ∃ N, ∀ n, n > N → (R_abs (r - u n) < ε)%R.

Theorem zzz : ∀ u, cauchy_sequence u → ∃ r, converges_to u r.
Proof.
intros u Hc.
unfold cauchy_sequence in Hc.
unfold converges_to.
assert (1 > 0)%R as H.
 Focus 2.
 apply Hc in H.
 destruct H as (N, HN).
 exists (mkre (R_int (u (S N))) 0).
 intros ε Hε.
 exists N; intros n Hn.
 remember Hε as H; clear HeqH.
 apply Hc in H.
 destruct H as (N1, HN1).
bbb.
