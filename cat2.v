Require Import Utf8.

Definition is_set (A : Type) := ∀ (a b : A) (p q : a = b), p = q.

Class cat :=
  { obj : Type;
    morph : obj → obj → Type;
    comp : ∀ {A B C}, morph A B → morph B C → morph A C;
    id : ∀ {A}, morph A A;
    unit_l : ∀ {A B} (f : morph A B), comp id f = f;
    unit_r : ∀ {A B} (f : morph A B), comp f id = f;
    assoc : ∀ {A B C D} (f : morph A B) (g : morph B C) (h : morph C D),
      comp f (comp g h) = comp (comp f g) h }.

Arguments morph [_].
Notation "g '◦' f" := (comp f g) (at level 40, left associativity).
Coercion obj : cat >-> Sortclass.

(* *)

Definition cTyp :=
  {| obj := Type;
     morph A B := A → B;
     comp A B C f g := λ x, g (f x);
     id _ A := A;
     unit_l _ _ _ := eq_refl;
     unit_r _ _ _ := eq_refl;
     assoc _ _ _ _ _ _ _ := eq_refl |}.

(* *)

Definition is_initial {C : cat} (_0 : obj) :=
  ∀ c : obj, ∀ f g : morph _0 c, f = g.
Definition is_final {C : cat} (_1 : obj) :=
  ∀ c : obj, ∀ f g : morph c _1, f = g.

Record functor (C D : cat) :=
  { f_obj : C → D;
    f_arr {a b} : morph a b → morph (f_obj a) (f_obj b);
    f_comp {a b c} (f : morph a b) (g : morph b c) :
      f_arr (g ◦ f) = f_arr g ◦ f_arr f;
    f_id {a} : @f_arr a _ id = id }.

(* A cone to a functor D(J,C) consists of an object c in C and a family of
   arrows in C *)
(* http://angg.twu.net/tmp/2016-optativa/awodey__category_theory.pdf
   page 100 *)

Record cone {J C} (D : functor J C) :=
  { c_obj : @obj C }.

...

(* A limit for a functor D : J → C is a terminal object in Cone(D) *)

