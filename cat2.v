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

(*
Coercion Obj : cat >-> Sortclass.
*)

Definition dom {C : cat} {O1 O2 : Obj} (f : Hom O1 O2) := O1.
Definition cod {C : cat} {O1 O2 : Obj} (f : Hom O1 O2) := O2.

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
  { f_map_obj : @Obj C → @Obj D;
    f_map_arr {a b} : Hom a b → Hom (f_map_obj a) (f_map_obj b);
    f_comp {a b c} (f : Hom a b) (g : Hom b c) :
      f_map_arr (g ◦ f) = f_map_arr g ◦ f_map_arr f;
    f_id {a} : @f_map_arr a _ id = id }.

Arguments f_map_obj [_] [_] [_].
Arguments f_map_arr [_] [_] _ [_] [_].

Definition is_isomorphism {C : cat} {A B : Obj} (f : Hom A B) :=
  ∃ g : Hom B A, g ◦ f = id ∧ f ◦ g = id.

(* *)

Theorem two_functor_map_arr (C : cat) D1 D2 :
  ∀ (b1 b2 : @Obj cTwo) (f : Hom b1 b2),
  Hom (if b1 then D1 else D2) (if b2 then D1 else D2).
Proof.
intros.
intros.
destruct b1, b2; [ apply id | discriminate f | discriminate f | apply id ].
Defined.

Theorem two_functor_comp C D1 D2 :
  ∀ (a b c : @Obj cTwo) (f : Hom a b) (g : Hom b c),
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
  ∀ a : @Obj cTwo, two_functor_map_arr C D1 D2 a a id = id.
Proof.
intros.
now destruct a.
Qed.

Definition two_functor {C : cat} (D1 D2 : Obj) :=
  {| f_map_obj (b : @Obj cTwo) := if b then D1 else D2;
     f_map_arr := two_functor_map_arr C D1 D2;
     f_comp := two_functor_comp C D1 D2;
     f_id := two_functor_id C D1 D2 |}.

(* A cone to a functor D(J,C) consists of an object c in C and a
   family of arrows in C : cj : c → Dj one for each object j ∈ J, such
   that for each arrow α : i → j in J, the following triangle
   commutes. *)

Record cone {J C} (D : functor J C) :=
  { c_root : @Obj C;
    c_fam : ∀ j, Hom c_root (f_map_obj j);
    c_commute : ∀ i j (α : Hom i j), c_fam j = f_map_arr D α ◦ c_fam i }.

(* category of cones *)

Record cCone_Hom {J C} {D : functor J C} (cn cn' : cone D) :=
  { ch_map_root : @Obj C → @Obj C;
    ch_root : ch_map_root (c_root D cn) = c_root D cn' }.

Definition cCone_comp {J C} {D : functor J C} {cn1 cn2 cn3 : cone D}
  (ch12 : cCone_Hom cn1 cn2) (ch23 : cCone_Hom cn2 cn3) : cCone_Hom cn1 cn3 :=
  {| ch_map_root c := ch_map_root _ _ ch23 (ch_map_root _ _ ch12 c);
     ch_root :=
       eq_trans
         (f_equal (ch_map_root cn2 cn3 ch23) (ch_root cn1 cn2 ch12))
         (ch_root cn2 cn3 ch23) |}.

Definition cCone_id {J C} {D : functor J C} (cn : cone D) : cCone_Hom cn cn :=
  {| ch_map_root c := c;
     ch_root := eq_refl |}.

Theorem cCone_unit_l {J C} {D : functor J C} :
  ∀ cn1 cn2 (f : cCone_Hom cn1 cn2), cCone_comp (cCone_id cn1) f = f.
Proof.
intros.
unfold cCone_comp; cbn.
destruct f as (f & Hf); cbn.
apply f_equal.
now destruct Hf.
Qed.

Theorem cCone_unit_r {J C} {D : functor J C} :
  ∀ cn1 cn2 (f : cCone_Hom cn1 cn2), cCone_comp f (cCone_id cn2) = f.
Proof.
intros.
unfold cCone_comp; cbn.
destruct f as (f & Hf); cbn.
apply f_equal.
now destruct Hf.
Qed.

Theorem cCone_assoc {J C} {D : functor J C} {cn1 cn2 cn3 cn4 : cone D} :
  ∀ (f : cCone_Hom cn1 cn2) (g : cCone_Hom cn2 cn3) (h : cCone_Hom cn3 cn4),
    cCone_comp f (cCone_comp g h) = cCone_comp (cCone_comp f g) h.
Proof.
intros.
unfold cCone_comp; cbn.
apply f_equal.
destruct f as (f & Hf).
destruct g as (g & Hg).
destruct h as (h & Hh); cbn.
now destruct Hf, Hg, Hh.
Qed.

Definition cCone {J C} (D : functor J C) :=
  {| Obj := cone D;
     Hom := cCone_Hom;
     comp _ _ _ := cCone_comp;
     id := cCone_id;
     unit_l := cCone_unit_l;
     unit_r := cCone_unit_r;
     assoc _ _ _ _ := cCone_assoc |}.

(* A limit for a functor D : J → C is a terminal object in Cone(D) *)

Definition is_limit {J C} {D : functor J C} cn :=
  @is_terminal (cCone D) cn.

... euh...

Definition limit {J C} {D : functor J C} (cn : cCone D) :=
  { p | p = c_root D cn & is_terminal p }.

Definition limit {J C} {D : functor J C} (cn : cone D) :=
  { p | p = c_root D cn & is_terminal p }.
