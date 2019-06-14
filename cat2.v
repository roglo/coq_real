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

(* tentative de faire Mat, mais c'est fatigant

Require List.
Import List.ListNotations.
Open Scope list_scope.

Definition vect n A := { v : list A | List.length v = n }.
Record mat nrow ncol A := { mel : vect nrow (vect ncol A) }.

Check (let l := [3; 4; 5] in (exist (λ l, List.length l = 3) l eq_refl) : vect _ _).

Definition mat_mul A zero_A a b c (M : mat a b A) (N : mat b c A) (*: mat a c A*) : vect a A :=
  exist (λ l, @List.length A l = a)
    (List.repeat zero_A a) (List.repeat_length zero_A a).

...

Definition cMat A :=
  {| obj := nat;
     morph := mat A;
     comp a b c M N := mat_mul A a b c M N |}.
*)
