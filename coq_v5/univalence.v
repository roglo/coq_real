(* experimentations on axiom of univalence *)

Require Import Utf8.

Definition equiv A B :=
  ∃ f : A → B, ∃ g : B → A,
  (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y).

Notation "A ≃ B" := (equiv A B) (at level 60).

Axiom univalence : ∀ A B, (A ≃ B) ≃ (A = B).

Inductive glop := toto : glop | titi : glop.

Theorem bool_eq_glop : @eq Type bool glop.
Proof.
pose proof univalence bool glop as H.
unfold equiv at 1 in H.
destruct H as (f, (g, (Hx, Hy))).
apply f.
unfold equiv.
exists (λ b : bool, if b then toto else titi).
exists (λ b : glop, if b then true else false).
split; intros x; destruct x; reflexivity.
Qed.
