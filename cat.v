(* jeu avec les catégories *)

Require Import Utf8.

Definition compose {A B C} (f : A → B) (g : B → C) := λ x, g (f x).
Notation "g 'o' f" := (compose f g) (at level 40).
Notation "f '==' g" := (∀ x, f x = g x) (at level 70).

(* surjection vs epimorphism *)

Definition is_surjection {A B} (f : A → B) := ∀ y, ∃ x, f x = y.
Definition is_epimorphism {A B} (u : A → B) :=
  ∀ C (v w : B → C), v o u == w o u → v == w.

Definition has_decidable_equality A := ∀ x y : A, {x = y} + {x ≠ y}.
Definition not_not_exist_imp_exist A :=
  ∀ (P : A → Prop), (¬ ¬ ∃ x, P x) → ∃ x, P x.

Theorem is_surjection_is_epimorphism :
  ∀ A B (f : A → B), is_surjection f → is_epimorphism f.
Proof.
intros * Hs.
unfold is_surjection in Hs.
intros C v w He y.
specialize (Hs y) as (x, Hx).
subst y; apply He.
Qed.

Theorem is_epimorphism_is_surjection :
  ∀ A B (f : A → B),
  has_decidable_equality B →
  not_not_exist_imp_exist A →
  is_epimorphism f → is_surjection f.
Proof.
intros A B u EqB NNE He.
unfold is_epimorphism in He.
intros y.
set (v (b : B) := if EqB b y then 1 else 0).
set (w (b : B) := 0).
specialize (He _ v w) as H1.
assert (Hn : ¬ (∀ x, u x ≠ y)). {
  intros H2.
  assert (Hx : v o u == w o u). {
    intros x.
    unfold v, w, "o"; simpl.
    destruct (EqB (u x) y) as [H3| H3]; [ | easy ].
    now specialize (H2 x).
  }
  specialize (H1 Hx y).
  unfold v, w in H1.
  now destruct (EqB y y).
}
apply NNE.
intros H2.
apply Hn; intros x H3.
apply H2.
now exists x.
Qed.

(* injection vs monomorphism *)

Definition is_injection {A B} (f : A → B) := ∀ x y, f x = f y → x = y.
Definition is_monomorphism {A B} (u : A → B) :=
  ∀ C (v w : C → A), u o v == u o w → v == w.

Theorem is_injection_is_monomorphism :
  ∀ A B (f : A → B), is_injection f → is_monomorphism f.
Proof.
intros A B u Hi C v w Hu c.
unfold is_injection in Hi.
specialize (Hi (v c) (w c)) as H1.
now specialize (H1 (Hu c)).
Qed.

Theorem is_monomorphism_is_injection :
  ∀ A B (f : A → B), is_monomorphism f → is_injection f.
Proof.
intros A B u Hm x y Hu.
unfold is_monomorphism in Hm.
set (v i := match i with 0 => x | _ => y end).
set (w (_ : nat) := y).
specialize (Hm _ v w) as H1.
assert (H : u o v == u o w). {
  unfold v, w, "o".
  intros i; simpl.
  now destruct i.
}
specialize (H1 H 0); clear H.
now unfold v, w in H1.
Qed.
