(* categories *)
(* http://angg.twu.net/tmp/2016-optativa/awodey__category_theory.pdf *)

Require Import Utf8.

Axiom extensionality : ∀ A B (f g : ∀ x : A, B x), (∀ x, f x = g x) → f = g.

Definition is_set (A : Type) := ∀ (a b : A) (p q : a = b), p = q.

Class category :=
  { Obj : Type;
    Hom : Obj → Obj → Type;
    comp : ∀ {A B C}, Hom A B → Hom B C → Hom A C;
    id : ∀ {A}, Hom A A;
    unit_l : ∀ {A B} (f : Hom A B), comp id f = f;
    unit_r : ∀ {A B} (f : Hom A B), comp f id = f;
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D),
      comp f (comp g h) = comp (comp f g) h;
    Hom_set x y : is_set (Hom x y) }.

Arguments Hom [_].
Notation "g '◦' f" := (comp f g) (at level 40, left associativity).

(*
Coercion Obj : cat >-> Sortclass.
*)

Definition dom {C : category} {O1 O2 : Obj} (f : Hom O1 O2) := O1.
Definition cod {C : category} {O1 O2 : Obj} (f : Hom O1 O2) := O2.

(* *)

(*
Definition cTyp :=
  {| Obj := Type;
     Hom A B := A → B;
     comp A B C f g := λ x, g (f x);
     id _ A := A;
     unit_l _ _ _ := eq_refl;
     unit_r _ _ _ := eq_refl;
     assoc _ _ _ _ _ _ _ := eq_refl |}.
*)

(*
Definition cDiscr T :=
  {| Obj := T;
     Hom t1 t2 := t1 = t2;
     comp _ _ _ f g := match g with eq_refl => f end;
     id _ := eq_refl;
     unit_l _ _ f := match f with eq_refl => eq_refl end;
     unit_r _ _ f := eq_refl;
     assoc _ _ _ _ _ _ f := match f with eq_refl => eq_refl end |}.

Definition cTwo := cDiscr (unit + unit).
*)

(* *)

Definition is_initial {C : category} (_0 : Obj) :=
  ∀ c : Obj, ∀ f g : Hom _0 c, f = g.
Definition is_terminal {C : category} (_1 : Obj) :=
  ∀ c : Obj, ∀ f g : Hom c _1, f = g.

Class functor (C D : category) :=
  { f_map_obj : @Obj C → @Obj D;
    f_map_arr {a b} : Hom a b → Hom (f_map_obj a) (f_map_obj b);
    f_comp {a b c} (f : Hom a b) (g : Hom b c) :
      f_map_arr (g ◦ f) = f_map_arr g ◦ f_map_arr f;
    f_id {a} : @f_map_arr a _ id = id }.

Arguments f_map_obj [_] [_] [_].
Arguments f_map_arr [_] [_] _ [_] [_].

Definition is_isomorphism {C : category} {A B : Obj} (f : Hom A B) :=
  ∃ g : Hom B A, g ◦ f = id ∧ f ◦ g = id.

(* *)

(*
Theorem two_functor_map_arr (C : category) D1 D2 :
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

Definition two_functor {C : category} (D1 D2 : Obj) :=
  {| f_map_obj (b : @Obj cTwo) := if b then D1 else D2;
     f_map_arr := two_functor_map_arr C D1 D2;
     f_comp := two_functor_comp C D1 D2;
     f_id := two_functor_id C D1 D2 |}.
*)

(* A cone to a functor D(J,C) consists of an object c in C and a
   family of arrows in C : cj : c → Dj one for each object j ∈ J, such
   that for each arrow α : i → j in J, the following triangle
   commutes. *)

Record cone {J C} (D : functor J C) :=
  { c_top : @Obj C;
    c_fam : ∀ j, Hom c_top (f_map_obj j);
    c_commute : ∀ i j (α : Hom i j), c_fam j = f_map_arr D α ◦ c_fam i }.

(* category of cones *)

Definition cCone_Hom {J C} {D : functor J C} (cn cn' : cone D) :=
  { ϑ | ∀ j, c_fam D cn j = c_fam D cn' j ◦ ϑ }.

Definition cCone_comp {J C} {D : functor J C} (c c' c'' : cone D)
  (ch : cCone_Hom c c') (ch' : cCone_Hom c' c'') : cCone_Hom c c'' :=
  exist
    (λ ϑ, ∀ j, c_fam D c j = c_fam D c'' j ◦ ϑ)
    (proj1_sig ch' ◦ proj1_sig ch)
    (λ j,
       eq_trans
         (eq_trans (proj2_sig ch j)
            (f_equal (comp (proj1_sig ch)) (proj2_sig ch' j)))
         (assoc (proj1_sig ch) (proj1_sig ch') (c_fam D c'' j))).

Definition cCone_id {J C} {D : functor J C} (c : cone D) : cCone_Hom c c :=
   exist (λ ϑ, ∀ j, c_fam D c j = c_fam D c j ◦ ϑ) id
     (λ j, eq_sym (unit_l (c_fam D c j))).

Theorem cCone_unit_l {J C} {D : functor J C} :
  ∀ (c c' : cone D) (f : cCone_Hom c c'),
  cCone_comp c c c' (cCone_id c) f = f.
Proof.
intros.
unfold cCone_comp; cbn.
destruct f as (f & Hf); cbn.
apply eq_exist_uncurried.
exists (unit_l _).
apply extensionality.
intros j.
apply Hom_set.
Defined.

Theorem cCone_unit_r {J C} {D : functor J C} :
  ∀ (c c' : cone D) (f : cCone_Hom c c'),
  cCone_comp c c' c' f (cCone_id c') = f.
Proof.
intros.
unfold cCone_comp; cbn.
destruct f as (f & Hf); cbn.
apply eq_exist_uncurried.
exists (unit_r _).
apply extensionality.
intros j.
apply Hom_set.
Defined.

Theorem cCone_assoc {J C} {D : functor J C} :
  ∀ (c c' c'' c''' : cone D) (f : cCone_Hom c c') (g : cCone_Hom c' c'')
    (h : cCone_Hom c'' c'''),
    cCone_comp c c' c''' f (cCone_comp c' c'' c''' g h) =
    cCone_comp c c'' c''' (cCone_comp c c' c'' f g) h.
Proof.
intros.
unfold cCone_comp; cbn.
apply eq_exist_uncurried.
exists (assoc _ _ _).
apply extensionality.
intros j.
apply Hom_set.
Defined.

Theorem cCone_Hom_set {J C} {D : functor J C} :
  ∀ c c' : cone D, is_set (cCone_Hom c c').
Proof.
intros * f g p q.
destruct f as (f & Hf).
destruct g as (g & Hg).
move g before f.
injection p; intros Hp.
injection q; intros Hq.
...
specialize (Hom_set (c_top D c) (c_top D c') f g Hp Hq) as H2.
...
destruct p.
destruct H2.
subst f.
injection p.
subst Hp.
unfold is_set in H2.
specialize (H2 Hp Hq).
destruct H2.
destruct Hp.
injection p.
...

Definition cCone {J C} (D : functor J C) :=
  {| Obj := cone D;
     Hom := cCone_Hom;
     comp := cCone_comp;
     id := cCone_id;
     unit_l := cCone_unit_l;
     unit_r := cCone_unit_r;
     assoc := cCone_assoc;
     Hom_set := 42 |}.

...

(* A limit for a functor D : J → C is a terminal object in Cone(D) *)

Definition is_limit {J C} {D : functor J C} (cn : cone D) :=
  @is_terminal (cCone D) cn.

(* Spelling out the definition, the limit of a diagram D has the
   following UMP: given any cone (C, cj) to D, there is a unique
   arrow u : C → lim←−j Dj such that for all j,
     pj ◦ u = cj .
*)

Theorem limit_UMP {J C} {D : functor J C} (cc := cCone D) :
  ∀ p c : cone D, is_limit p →
  exists! u, ∀ j, c_fam _ p j ◦ u = c_fam _ c j.
Proof.
intros * Hlim.
unfold unique.
unfold is_limit in Hlim.
unfold is_terminal in Hlim.
Print cCone_Hom.
(* c'est moi qui la crée, la catégorie des cônes, c'est moi qui en crée,
   qui en décide les morphismes ; je peux imposer qu'il y en ait un entre
   chaque racine ; quoique... faut voir... car le morphisme doit respecter
   la règle cj = c'j ◦ ϑ *)
Print cCone.
...
