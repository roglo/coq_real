(* categories *)
(* http://angg.twu.net/tmp/2016-optativa/awodey__category_theory.pdf *)

Require Import Utf8.
Set Nested Proofs Allowed.

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
  { ϑ & ∀ j, c_fam D cn j = c_fam D cn' j ◦ ϑ }.

Definition cCone_comp {J C} {D : functor J C} (c c' c'' : cone D)
  (ch : cCone_Hom c c') (ch' : cCone_Hom c' c'') : cCone_Hom c c'' :=
  existT
    (λ ϑ, ∀ j, c_fam D c j = c_fam D c'' j ◦ ϑ)
    (projT1 ch' ◦ projT1 ch)
    (λ j,
       eq_trans
         (eq_trans (projT2 ch j)
            (f_equal (comp (projT1 ch)) (projT2 ch' j)))
         (assoc (projT1 ch) (projT1 ch') (c_fam D c'' j))).

Definition cCone_id {J C} {D : functor J C} (c : cone D) : cCone_Hom c c :=
   existT (λ ϑ, ∀ j, c_fam D c j = c_fam D c j ◦ ϑ) id
     (λ j, eq_sym (unit_l (c_fam D c j))).

Theorem cCone_unit_l {J C} {D : functor J C} :
  ∀ (c c' : cone D) (f : cCone_Hom c c'),
  cCone_comp c c c' (cCone_id c) f = f.
Proof.
intros.
unfold cCone_comp; cbn.
destruct f as (f & Hf); cbn.
apply eq_existT_uncurried.
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
apply eq_existT_uncurried.
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
apply eq_existT_uncurried.
exists (assoc _ _ _).
apply extensionality.
intros j.
apply Hom_set.
Defined.

Definition isProp (A : Type) := ∀ (x y : A), x = y.

Definition isContr A := {a : A & ∀ x : A, a = x }.

Fixpoint isnType A n :=
  match n with
  | 0 => isProp A
  | S p' => ∀ x y : A, isnType (x = y) p'
  end.

Definition compose {A} {x y z : A} : x = y → y = z → x = z :=
  λ p, match p with eq_refl _ => λ x, x end.

Theorem compose_cancel_l {A} {x y z : A} (p : x = y) (q r : y = z) :
  compose p q = compose p r → q = r.
Proof. intros; now destruct p. Qed.

Theorem compose_eq_refl : ∀ A (x : A) (p : x = x), compose p eq_refl = p.
Proof. now intros; destruct p. Qed.

Theorem isProp_isSet {A} : ∀ (f : isProp A) (x y : A) (p q : x = y), p = q.
Proof.
intros f *.
apply (compose_cancel_l (f x x)).
apply @compose with (y := f x y); [ now destruct p, (f x x) | ].
now destruct p, q, (f x x).
Qed.

Theorem isnType_isSnType {A} n : isnType A n → isnType A (S n).
Proof.
intros * f.
revert A f.
induction n; intros; [ intros x y p q; now apply isProp_isSet | ].
intros p q.
apply IHn, f.
Qed.

Definition transport {A} P {x y : A} (p : x = y) : P x → P y :=
  match p with
  | eq_refl _ => λ x, x
  end.

Definition isequiv {A B : Type} (f : A → B) :=
  {g : B → A & (∀ a, g (f a) = a) & (∀ b, f (g b) = b)}.

Definition equivalence (A B : Type) := { f : A → B & isequiv f}.
Notation "A ≃ B" := (equivalence A B) (at level 70).

Theorem equiv_eq : ∀ A B (f : A → B) (g : B → A) x y,
  (∀ b, f (g b) = b) → g x = g y → x = y.
Proof.
intros * Hfg H.
apply @compose with (y := f (g y)); [ | apply Hfg ].
destruct H; symmetry; apply Hfg.
Defined.

Lemma isnType_if_equiv : ∀ A B n, A ≃ B → isnType A n → isnType B n.
Proof.
intros * HAB HA.
revert A B HAB HA.
induction n; intros. {
  destruct HAB as (f, Hf).
  destruct Hf as (g, Hgf, Hfg).
  cbn in HA |-*.
  unfold isProp in HA |-*.
  intros x y.
  rewrite <- Hfg; symmetry.
  rewrite <- Hfg; symmetry.
  f_equal.
  apply HA.
}
destruct HAB as (f, Hf).
destruct Hf as (g, Hgf, Hfg).
cbn in HA |-*.
intros x y.
apply (IHn (g x = g y) (x = y)); [ | apply HA ].
exists (equiv_eq A B f g x y Hfg).
unfold isequiv.
exists (@f_equal _ _ g x y). {
  intros p.
  assert (H : x = y). {
    transitivity (f (g x)); [ symmetry; apply Hfg | ].
    transitivity (f (g y)); [ | apply Hfg ].
    now f_equal.
  }
  remember (equiv_eq A B f g x y Hfg p) as q eqn:Hq.
  destruct q; cbn.
  unfold equiv_eq in Hq.
  destruct (Hfg x); cbn in Hq.
  rewrite compose_eq_refl in Hq.
...
}
intros p.
subst y; cbn.
unfold equiv_eq_2.
now destruct (Hfg x).
...

Theorem isnType_isnType_sigT (A : Type) : ∀ n P,
  (∀ x, isProp (P x)) → isnType A n → isnType (@sigT A P) n.
Proof.
intros * HP Hn.
revert A P HP Hn.
induction n; intros. {
  cbn in Hn; cbn.
  unfold isProp in Hn |-*.
  intros H1 H2.
  destruct H1 as (a & Ha).
  destruct H2 as (b & Hb).
  move b before a.
  apply eq_existT_uncurried.
  assert (p : a = b) by apply Hn.
  exists p.
  apply HP.
}
intros Ha Hb.
destruct Ha as (a, Ha).
destruct Hb as (b, Hb).
move b before a.
specialize (IHn (a = b)) as H4.
remember (λ p : a = b, transport P p Ha = Hb) as Q.
specialize (H4 Q).
assert (H : ∀ p : a = b, isProp (Q p)). {
  intros p.
  subst Q.
  destruct p.
  cbn.
  specialize (HP a) as H1.
  specialize (isProp_isSet H1 Ha Hb) as H2.
  intros r s.
  apply H2.
}
specialize (H4 H); clear H.
cbn in Hn.
specialize (H4 (Hn a b)).
subst Q.
...

Check {p : a = b & transport P p Ha = Hb}.
Check (existT P a Ha = existT P b Hb).
...

Theorem is_set_is_set_sigT (A : Type) : ∀ P, is_set A → is_set (@sigT A P).
Proof.
intros * HP.
now apply (glop A 1 P).
Qed.

Theorem cCone_Hom_set {J C} {D : functor J C} :
  ∀ c c' : cone D, is_set (cCone_Hom c c').
Proof.
intros.
unfold cCone_Hom.
apply is_set_is_set_sigT.
apply Hom_set.
...
intros * f g p q.
destruct f as (f & Hf).
destruct g as (g & Hg).
move g before f.
injection p; intros Hp.
injection q; intros Hq.
...
specialize (Hom_set (c_top D c) (c_top D c') f g Hp Hq) as H1.
apply Hom_set.
...
Require Import Arith.
apply Eqdep_dec.UIP_dec.
intros c1 c2.
destruct c1 as (c1, Hc1).
destruct c2 as (c2, Hc2).
move c2 before c1.
(* bin ouais mais faudrait que c1=c2 soit décidable *)
specialize (Hom_set _ _ c1 c2) as H1.
...
Search (exist _ _ _ = exist _ _ _).
Check Eqdep_dec.UIP_dec.
Check Eqdep_dec.UIP_refl.
...
About UIP.
...
specialize EqdepFacts.eq_sig_eq_dep as H1.
specialize (EqdepFacts.eq_sig_eq_dep _ _ f g Hf Hg) as H1.
apply Eqdep_dec.UIP_dec.
...
Check Eqdep_dec.eq_dep_eq_dec.
apply Eqdep_dec.eq_dep_eq_dec.
...
Check Eqdep_dec.UIP_dec.
left.
destruct c1 as (c1, Hc1).
destruct c2 as (c2, Hc2).
move c2 before c1.
apply eq_exist_uncurried.
specialize (Hom_set _ _ c1 c2) as H1.
Search (exist _ _ _ = exist _ _ _ → _).
(*
Require Import ssrfun.
*)

About le_unique.
...
EqdepFacts.eq_sig_snd:
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
