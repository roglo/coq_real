Require Import Utf8.

Definition is_set (A : Type) := ∀ (a b : A) (p q : a = b), p = q.

Record pre_cat :=
  { obj : Type;
    morph : obj → obj → Type;
    comp : ∀ a b c, morph b c → morph a b → morph a c;
    id : ∀ a : obj, morph a a;
    unit_l : ∀ (a b : obj) (f : morph a b), comp _ _ _ (id _) f = f;
    unit_r : ∀ (a b : obj) (f : morph a b), comp _ _ _ f (id _) = f;
    assoc : ∀ (a b c d : obj) (h : morph c d) (g : morph b c) (f : morph a b),
        comp _ _ _ h (comp _ _ _ g f) = comp _ _ _ (comp _ _ _ h g) f;
    homset : ∀ a b : obj, is_set (morph a b) }.

Coercion obj : pre_cat >-> Sortclass.

Record is_isomorph {c : pre_cat} {a b : obj c} (f : morph c a b) :=
  { g : morph c b a;
    f_g : comp _ _ _ _ f g = id _ _;
    g_f : comp _ _ _ _ g f = id _ _ }.

Definition isomorphism {C : pre_cat} (a b : C) := { f : morph C a b & is_isomorph f }.

Definition isequiv {A B : Type} (f : A → B) :=
  {g : B → A & (∀ a, g (f a) = a) & (∀ b, f (g b) = b)}.

Definition equivalence (A B : Type) := { f : A → B & isequiv f}.
Notation "A ≃ B" := (equivalence A B) (at level 70).

Record cat :=
  { pcat : pre_cat;
    univalent : ∀ a b : pcat, isomorphism a b ≃ (a = b) }.
