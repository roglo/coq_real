(* experimentations on axiom of univalence *)

Require Import Utf8.

Definition equiv A B :=
  ∃ f : A → B, ∃ g : B → A,
  (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y).

Notation "A ≃ B" := (equiv A B) (at level 60).

Axiom univalence : ∀ A B : Set, (A ≃ B) ≃ (A = B).

Inductive t := foo : t | bar : t.

Theorem bool_eq_t : bool = t.
Proof.
apply univalence.
unfold equiv.
exists (λ b : bool, if b then foo else bar).
exists (λ b : t, if b then true else false).
split; intros x; destruct x; reflexivity.
Defined.

Definition negt : t → t.
Proof.
rewrite <- bool_eq_t.
apply negb.
Defined.

Theorem aaa : negt foo = bar.
Proof.
unfold negt.
unfold negb; simpl.
unfold eq_rec; simpl.
unfold eq_rect; simpl.
bbb.

unfold bool_eq_t.
remember (univalence bool t) as v eqn:Hv.
destruct v as (f, H); simpl.
destruct H as (g, (H1, H2)).
bbb.
