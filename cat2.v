Require Import Utf8.

Definition is_set (A : Type) := ∀ (a b : A) (p q : a = b), p = q.

Class pre_cat :=
  { obj : Type;
    morph : obj → obj → Type;
    comp : ∀ {a b c}, morph a b → morph b c → morph a c;
    id : ∀ {a}, morph a a;
    unit_l : ∀ {a b} (f : morph a b), comp id f = f;
    unit_r : ∀ {a b} (f : morph a b), comp f id = f;
    assoc : ∀ {a b c d} (f : morph a b) (g : morph b c) (h : morph c d),
      comp f (comp g h) = comp (comp f g) h;
    homset : ∀ {a b}, is_set (morph a b) }.

Arguments morph [_].
Notation "g '◦' f" := (comp f g) (at level 40, left associativity).
Coercion obj : pre_cat >-> Sortclass.

Record is_isomorph {C : pre_cat} {a b : C} (f : morph a b) :=
  { inv : morph b a;
    comp_inv_l : comp inv f = id;
    comp_inv_r : comp f inv = id }.

Definition isomorphism {C : pre_cat} (a b : C) := { f : morph a b & is_isomorph f }.

Definition isequiv {A B : Type} (f : A → B) :=
  {g : B → A & (∀ a, g (f a) = a) & (∀ b, f (g b) = b)}.

Definition equivalence (A B : Type) := { f : A → B & isequiv f}.
Notation "A ≃ B" := (equivalence A B) (at level 70).

Record cat :=
  { pcat : pre_cat;
    univalent : ∀ a b : pcat, isomorphism a b ≃ (a = b) }.

(* *)

Definition catTyp A :=
  {| obj := A;
     morph a b := ... |}.
