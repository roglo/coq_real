(* jeu avec les catégories *)

Require Import Utf8.
(*
Set Universe Polymorphism.
*)

Definition compose {A B C} (f : A → B) (g : B → C) := λ x, g (f x).
Notation "g '◦' f" := (compose f g) (at level 40).
Notation "f '==' g" := (∀ x, f x = g x) (at level 70).

(* surjection vs epimorphism *)

Definition is_surjection {A B} (f : A → B) := ∀ y, ∃ x, f x = y.
Definition is_epimorphism {A B} (u : A → B) :=
  ∀ C (v w : B → C), v ◦ u == w ◦ u → v == w.

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
Defined.

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
  assert (Hx : v ◦ u == w ◦ u). {
    intros x.
    unfold v, w, "◦"; simpl.
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
Defined.

(* injection vs monomorphism *)

Definition is_injection {A B} (f : A → B) := ∀ x y, f x = f y → x = y.
Definition is_monomorphism {A B} (u : A → B) :=
  ∀ C (v w : C → A), u ◦ v == u ◦ w → v == w.

Theorem is_injection_is_monomorphism :
  ∀ A B (f : A → B), is_injection f → is_monomorphism f.
Proof.
intros A B u Hi C v w Hu c.
unfold is_injection in Hi.
specialize (Hi (v c) (w c)) as H1.
now specialize (H1 (Hu c)).
Defined.

Definition is_injection_is_monomorphism2 :
    ∀ A B (f : A → B), is_injection f → is_monomorphism f :=
  λ A B u Hi C v w Hu c, Hi (v c) (w c) (Hu c).

Theorem is_monomorphism_is_injection :
  ∀ A B (f : A → B), is_monomorphism f → is_injection f.
Proof.
intros A B u Hm x y Hu.
unfold is_monomorphism in Hm.
set (v (_ : True) := x).
set (w (_ : True) := y).
specialize (Hm _ v w) as H1.
assert (H : u ◦ v == u ◦ w) by easy.
specialize (H1 H); clear H.
now unfold v, w in H1; apply H1.
Show Proof.
Defined.

Definition is_monomorphism_is_injection2 :
    ∀ A B (f : A → B), is_monomorphism f → is_injection f :=
  λ A B f Hm x y Hu, Hm _ (λ _, x) (λ _, y) (λ _, Hu) I.

(* sections and retractions *)

Definition has_section {A B} (f : A → B) := ∃ s, f ◦ s == λ y, y.
Definition has_retraction {A B} (f : A → B) := ∃ r, r ◦ f == λ x, x.

Theorem has_section_is_epimorphism : ∀ A B (f : A → B),
  has_section f → is_epimorphism f.
Proof.
intros A B u HS.
destruct HS as (s, HS).
unfold is_epimorphism.
intros C v w Hu y.
specialize (HS y) as H1.
rewrite <- H1.
unfold compose.
apply Hu.
Qed.

Theorem has_retraction_is_monomorphism : ∀ A B (f : A → B),
  has_retraction f → is_monomorphism f.
Proof.
intros A B u HR.
destruct HR as (r, HR).
unfold is_monomorphism.
intros C v w Hu c.
rewrite <- HR; symmetry.
rewrite <- HR; symmetry.
unfold "◦" in Hu.
unfold "◦".
now rewrite Hu.
Qed.

(* snake lemma *)

Definition is_initial_object I := ∀ C, ∃! f, ...

Definition is_zero_object A := is_initial_object A ∧ is_terminal_object A.

Lemma snake :
  ∀ A B C A' B' C' Z (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
     (a : A → A') (b : B → B') (c : C → C')
     (cz : C → Z) (za' : Z → A'), is_zero_object Z → False.
Proof.

...

(* digression sur Yoneda *)

Lemma Yoneda : ∀ A : Prop, (∀ C : Prop, (A → C) → C) ↔ A.
Proof.
intros.
split.
-intros HC.
 specialize (HC A).
 now apply HC.
-intros * HC C HA.
 now apply HA.
Qed.

(* tiens, au fait, qu'est-ce que l'univalence en pense ? *)

Definition isequiv {A B : Type} (f : A → B) :=
  {g : B → A & (∀ a, g (f a) = a) & (∀ b, f (g b) = b)}.

Definition equivalence (A B : Type) := { f : A → B & isequiv f}.
Notation "A ≃ B" := (equivalence A B) (at level 70).

Theorem happly : ∀ A B (f g : ∀ (x : A), B x), f = g → ∀ (x : A), f x = g x.
Proof.
intros * p.
now destruct p.
Defined.

Definition extensionality := ∀ A B f g, isequiv (happly A B f g).

Theorem are_equiv_inj_mono : ∀ A B (f : A → B),
  extensionality
  → is_injection f ≃ is_monomorphism f.
Proof.
intros * HF.
exists (is_injection_is_monomorphism2 A B f).
unfold isequiv.
exists (is_monomorphism_is_injection2 A B f); [ easy | ].
intros HM.
unfold is_monomorphism_is_injection2.
unfold is_injection_is_monomorphism2.
unfold is_monomorphism in HM.
apply HF; intros C.
apply HF; intros g.
apply HF; intros h.
apply HF; intros HU.
apply HF; intros c.
specialize (HM _ _ _ HU) as H1.
specialize (HF _ _ g h) as H2.
unfold happly in H2.
unfold isequiv in H2.
simpl in H2.
destruct H2 as (H3, H4, H5).
clear H4 H5.
specialize (H3 H1).
subst g.

(* ouais, chais pas *)

...

Theorem are_equiv_surj_epi : ∀ A B (f : A → B),
  has_decidable_equality B
  → not_not_exist_imp_exist A
  → is_surjection f ≃ is_epimorphism f.
Proof.
intros * EqB NNE.
exists (is_surjection_is_epimorphism A B f).
unfold isequiv.
exists (is_epimorphism_is_surjection A B f EqB NNE).
-intros HS.
 unfold is_epimorphism_is_surjection.
...
