(* categories *)
(* http://angg.twu.net/tmp/2016-optativa/awodey__category_theory.pdf *)

Require Import Utf8.

Definition is_set (A : Type) := ∀ (a b : A) (p q : a = b), p = q.

Class cat :=
  { Obj : Type;
    Hom : Obj → Obj → Type;
    comp : ∀ {A B C}, Hom A B → Hom B C → Hom A C;
    id : ∀ {A}, Hom A A;
    unit_l : ∀ {A B} (f : Hom A B), comp id f = f;
    unit_r : ∀ {A B} (f : Hom A B), comp f id = f;
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D),
      comp f (comp g h) = comp (comp f g) h }.

Arguments Hom [_].
Notation "g '◦' f" := (comp f g) (at level 40, left associativity).
Coercion Obj : cat >-> Sortclass.

Definition dom {C : cat} {O1 O2 : C} (f : Hom O1 O2) := O1.
Definition cod {C : cat} {O1 O2 : C} (f : Hom O1 O2) := O2.

(* *)

Definition cTyp :=
  {| Obj := Type;
     Hom A B := A → B;
     comp A B C f g := λ x, g (f x);
     id _ A := A;
     unit_l _ _ _ := eq_refl;
     unit_r _ _ _ := eq_refl;
     assoc _ _ _ _ _ _ _ := eq_refl |}.

Definition cDiscr T :=
  {| Obj := T;
     Hom t1 t2 := t1 = t2;
     comp _ _ _ f g := match g with eq_refl => f end;
     id _ := eq_refl;
     unit_l _ _ f := match f with eq_refl => eq_refl end;
     unit_r _ _ f := eq_refl;
     assoc _ _ _ _ _ _ f := match f with eq_refl => eq_refl end |}.

Definition cTwo := cDiscr (unit + unit).

(* *)

Definition is_initial {C : cat} (_0 : Obj) :=
  ∀ c : Obj, ∀ f g : Hom _0 c, f = g.
Definition is_terminal {C : cat} (_1 : Obj) :=
  ∀ c : Obj, ∀ f g : Hom c _1, f = g.

Class functor (C D : cat) :=
  { f_map_obj : C → D;
    f_map_arr {a b} : Hom a b → Hom (f_map_obj a) (f_map_obj b);
    f_comp {a b c} (f : Hom a b) (g : Hom b c) :
      f_map_arr (g ◦ f) = f_map_arr g ◦ f_map_arr f;
    f_id {a} : @f_map_arr a _ id = id }.

Arguments f_map_obj [_] [_] [_].
Arguments f_map_arr [_] [_] _ [_] [_].

Definition is_isomorphism {C : cat} {A B : C} (f : Hom A B) :=
  ∃ g : Hom B A, g ◦ f = id ∧ f ◦ g = id.

(* *)

Theorem two_functor_map_arr (C : cat) D1 D2 :
  ∀ (b1 b2 : cTwo) (f : Hom b1 b2),
  Hom (if b1 then D1 else D2) (if b2 then D1 else D2).
Proof.
intros.
intros.
destruct b1, b2; [ apply id | discriminate f | discriminate f | apply id ].
Defined.

Theorem two_functor_comp C D1 D2 :
  ∀ (a b c : cTwo) (f : Hom a b) (g : Hom b c),
  two_functor_map_arr C D1 D2 a c (g ◦ f) =
  two_functor_map_arr C D1 D2 b c g ◦ two_functor_map_arr C D1 D2 a b f.
Proof.
intros.
unfold two_functor_map_arr.
destruct a as [a| a], b as [b| b], c as [c| c].
-now rewrite unit_l.
-now rewrite unit_l.
-discriminate f.
-discriminate f.
-discriminate f.
-discriminate f.
-now rewrite unit_l.
-now rewrite unit_l.
Qed.

Theorem two_functor_id C D1 D2 :
  ∀ a : cTwo, two_functor_map_arr C D1 D2 a a id = id.
Proof.
intros.
now destruct a.
Qed.

Definition two_functor {C : cat} (D1 D2 : C) :=
  {| f_map_obj (b : cTwo) := if b then D1 else D2;
     f_map_arr := two_functor_map_arr C D1 D2;
     f_comp := two_functor_comp C D1 D2;
     f_id := two_functor_id C D1 D2 |}.

(* A cone to a functor D(J,C) consists of an object c in C and a
   family of arrows in C : cj : c → Dj one for each object j ∈ J, such
   that for each arrow α : i → j in J, the following triangle
   commutes. *)

Class cone {J C} (D : functor J C) :=
  { c_obj : C;
    c_fam : ∀ j : J, Hom c_obj (f_map_obj j);
    c_commute : ∀ i j (α : Hom i j), c_fam j = f_map_arr D α ◦ c_fam i }.

Arguments c_obj [_] [_] [_].

(* category of cones *)

Definition Cone {J C} (D : functor J C) :=
  {| Obj := cone D;
     Hom cn cn' := C → C |}.

(* peut-être faudrait-il justement définir un prédicat sur Hom pour
   préciser le sous-type (= sous-ensemble) concerné *)

...

Definition Cone_Hom {J C} (D : functor J C) c c' :=
  { δ |
    ∀ j (cj : arr_fam (c_obj c) j) (c'j : arr_fam (c_obj c') j),
      cj = c'j ◦ δ }.

Definition Cone_comp {J C} (D : functor J C) (c c1 c' : cone D)
  (f : Cone_Hom D c c1) (g : Cone_Hom D c1 c') : Cone_Hom D c c' :=
  exist _ (proj1_sig g ◦ proj1_sig f)
        ((λ _ j cj c'j,
          eq_trans
            (proj2_sig f j cj (c'j ◦ proj1_sig g))
            (assoc (proj1_sig f) (proj1_sig g) c'j))
           (proj1_sig g)).

Definition Cone_id {J C} (D : functor J C) (c : cone D) :=
  exist
    (λ δ, ∀ j (cj c'j : arr_fam (c_obj c) j), cj = c'j ◦ δ)
    id
    (λ j (cj c'j : arr_fam (c_obj c) j),
     eq_sym
       (eq_trans (c_commute j j id cj (c'j ◦ id))
                 (eq_trans (f_equal (comp cj) f_id) (unit_r cj)))).

Definition Cone_unit_l {J C} (D : functor J C) :
  ∀ (A B : cone D) (f : Cone_Hom D A B),
  Cone_comp D A A B (Cone_id D A) f = f.
Proof.
intros.
destruct f as (f & Hf).
unfold Cone_comp, Cone_id; cbn.
apply eq_exist_uncurried.
exists (unit_l f).
unfold eq_rect.
...

Definition Cone {J C} (D : functor J C) :=
  {| Obj := cone D;
     Hom := Cone_Hom D;
     comp := Cone_comp D;
     id := Cone_id D;
     unit_l := 42 |}.

...

(* A limit for a functor D : J → C is a terminal object in Cone(D) *)

Definition is_limit {J C} {D : functor J C} (Cn : Cone D) :=
  is_terminal (c_obj Cn).

Definition limit {J C} {D : functor J C} (Cn : cone D) :=
  { p | p = c_obj Cn & is_terminal p }.

Print limit.

(* ouais chais pas *)
