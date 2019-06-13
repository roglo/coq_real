Require Import Utf8.

Definition is_set (A : Type) := ∀ (a b : A) (p q : a = b), p = q.

Class pre_cat :=
  { obj : Type;
    morph : obj → obj → Type;
    comp : ∀ {A B C}, morph A B → morph B C → morph A C;
    id : ∀ {A}, morph A A;
    unit_l : ∀ {A B} (f : morph A B), comp id f = f;
    unit_r : ∀ {A B} (f : morph A B), comp f id = f;
    assoc : ∀ {A B C D} (f : morph A B) (g : morph B C) (h : morph C D),
      comp f (comp g h) = comp (comp f g) h;
    homset : ∀ {A B}, is_set (morph A B) }.

Arguments morph [_].
Notation "g '◦' f" := (comp f g) (at level 40, left associativity).
Coercion obj : pre_cat >-> Sortclass.

Theorem homset_type : ∀ A B, is_set (A → B).
Proof.
intros * f g Hp Hq.
...

Definition cTyp :=
  {| obj := Type;
     morph A B := A → B;
     comp A B C f g := λ x, g (f x);
     id _ a := a;
     unit_l _ _ _ := eq_refl;
     unit_r _ _ _ := eq_refl;
     assoc _ _ _ _ _ _ _ := eq_refl;
     homset := eq_refl |}.

Print cTyp.

...

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
