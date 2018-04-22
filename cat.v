(* jeu avec les catégories *)

Require Import Utf8.

Definition is_surjective {A B} (f : A → B) := ∀ y, ∃ x, f x = y.
Definition is_epimorphism {A B} (u : A → B) :=
  ∀ C (v w : B → C), (∀ x, v (u x) = w (u x)) → (∀ x, v x = w x).

Theorem is_surjective_is_epimorphism :
  ∀ A B (f : A → B), is_surjective f → is_epimorphism f.
Proof.
intros * Hs.
unfold is_surjective in Hs.
intros C v w He y.
specialize (Hs y) as (x, Hx).
subst y; apply He.
Qed.

Definition has_decidable_equality A := ∀ x y : A, {x = y} + {x ≠ y}.

Theorem is_epimorphism_is_surjective :
  ∀ A B (f : A → B),
  has_decidable_equality B → is_epimorphism f → is_surjective f.
Proof.
intros A B u EqB He.
unfold has_decidable_equality in EqB.
unfold is_epimorphism in He.
intros y.
set (v (b : B) := if EqB b y then 1 else 0).
set (w (b : B) := 0).
specialize (He _ v w) as H1.
assert (Hn : ¬ (∀ x, u x ≠ y)). {
  intros H2.
  assert (Hx : ∀ x : A, v (u x) = w (u x)). {
    intros x.
    unfold v, w; simpl.
    destruct (EqB (u x) y) as [H3| H3]; [ | easy ].
    now specialize (H2 x).
  }
  specialize (H1 Hx y).
  unfold v, w in H1.
  now destruct (EqB y y).
}
(* I need an axiom (or an hypothesis) allowing me to transform
   this ¬∀ into ∃ *)
