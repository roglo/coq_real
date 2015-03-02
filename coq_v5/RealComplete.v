(* I is complete *)

Require Import Utf8 QArith NPeano Misc.
Require Import Real01 Real01Cmp Real01Add.

Open Scope nat_scope.

Definition I_abs_sub x y := if I_lt_dec x y then (y - x)%I else (x - y)%I.

Definition cauchy_sequence u :=
  ∀ ε, (ε ≠ 0)%I → ∃ N, ∀ p q, p > N → q > N → (I_abs_sub (u p) (u q) < ε)%I.

Definition converges_to u r :=
  ∀ ε, (ε ≠ 0)%I → ∃ N, ∀ n, n > N → (I_abs_sub r (u n) < ε)%I.

Axiom functional_choice :
  ∀ A B (P : A → B → Prop),
  (∀ x, ∃ y, P x y)
  → ∃ f, ∀ x, P x (f x).

(* to be completed *)
Theorem zzz : ∀ u, cauchy_sequence u → ∃ r, converges_to u r.
Proof.
intros u Hc.
unfold cauchy_sequence in Hc.
unfold converges_to.
(*
bbb.
*)

(*
apply functional_choice in Hc.
destruct Hc as (f, Hf).
bbb.
*)
