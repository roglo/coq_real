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
(*

Fixpoint ispType A p :=
  match p with
  | 0 => isProp A
  | S p' => ∀ x y : A, ispType (x = y) p'
  end.
*)

Definition isContr A := {a : A & ∀ x : A, a = x }.

Fixpoint isnType A n :=
  match n with
  | 0 => isProp A
  | S p' => ∀ x y : A, isnType (x = y) p'
  end.

Definition compose {A} {x y z : A} : x = y → y = z → x = z :=
  λ p,
  match p with
  | eq_refl _ => λ x, x
  end.

Definition invert {A} {x y : A} (p : x = y) : y = x :=
  match p with
  | eq_refl _ => eq_refl x
  end.

Theorem hott_2_1_4_i_1 {A} {x y : A} : ∀ (p : x = y),
    p = compose p (eq_refl y).
Proof. intros; now destruct p. Qed.

Theorem hott_2_1_4_i_2 {A} {x y : A} : ∀ (p : x = y),
    p = compose (eq_refl x) p.
Proof. intros; now destruct p. Qed.

Theorem dotl {A} {a b c : A} {r s : b = c}
  (q : a = b) (β : r = s) : compose q r = compose q s.
Proof.
destruct q.
specialize (@hott_2_1_4_i_2 A a c r) as H2.
apply invert in H2.
eapply compose; [ apply H2 | idtac ].
specialize (@hott_2_1_4_i_2 A a c s) as H4.
eapply compose; [ apply β | apply H4 ].
Qed.

Theorem dotr {A} {a b c : A} {p q : a = b}
  (r : b = c) (α : p = q) : compose p r = compose q r.
Proof.
destruct r.
specialize (@hott_2_1_4_i_1 A a b p) as H1.
apply invert in H1.
eapply compose; [ apply H1 | idtac ].
pose proof (@hott_2_1_4_i_1 A a b q) as H3.
eapply compose; [ apply α | apply H3 ].
Qed.

Theorem compose_assoc {A} {x y z w : A} :
  ∀ (p : x = y) (q : y = z) (r : z = w),
  compose p (compose q r) = compose (compose p q) r.
Proof.
intros p q r; now destruct p.
Qed.

Theorem lu {A} {b c : A} (r : b = c) : r = compose (eq_refl b) r.
Proof. apply hott_2_1_4_i_2. Qed.

Theorem ru {A} {a b : A} (p : a = b) : p = compose p (eq_refl b).
Proof. apply hott_2_1_4_i_1. Qed.

Theorem compose_invert_l {A} {x y : A} :
  ∀ (p : x = y), compose (invert p) p = eq_refl y.
Proof. now intros p; destruct p. Qed.

Theorem compose_cancel_l {A} {x y z : A} (p : x = y) (q r : y = z) :
  compose p q = compose p r → q = r.
Proof.
intros H.
eapply (dotl (invert p)) in H.
eapply compose. {
  eapply compose; [ | apply H ].
  eapply compose; [ | eapply invert, compose_assoc ].
  eapply compose; [ apply lu | apply dotr ].
  apply invert, compose_invert_l.
}
eapply compose; [ eapply compose_assoc | ].
eapply compose; [ | eapply invert, lu ].
apply dotr, compose_invert_l.
Qed.

Theorem transport {A} P {x y : A} (p : x = y) : P x → P y.
Proof. now intros; destruct p. Defined.

Theorem apd {A P} f {x y : A} (p : x = y) : transport P p (f x) = f y.
Proof. now destruct p. Qed.

Theorem compose_insert {A x} (f : ∀ y : A, x = y) {y z} (p : y = z) :
  compose (f y) p = f z.
Proof.
eapply compose; [ | apply (apd f p) ].
eapply invert; destruct p; simpl; apply ru.
Qed.

Theorem isnType_isSnType {A} n : isnType A n → isnType A (S n).
Proof.
intros * f.
revert A f.
induction n; intros. {
  intros x y p q.
  apply (compose_cancel_l (f x x)).
  eapply compose; [ eapply (compose_insert (f x)) | ].
  apply invert, compose_insert.
}
intros p q.
apply IHn, f.
Qed.

Theorem is_ntype_is_ntype_sigT (A : Type) : ∀ n P,
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
apply isnType_isSnType.
apply IHn; [ easy | ].
cbn in Hn.
...
cbn in Hn; cbn.
intros Ha Hb.
destruct Ha as (a, Ha).
destruct Hb as (b, Hb).
move b before a.
Set Printing Implicit.
...
specialize (IHn (a = a)) as H1.
assert (Q : (a = a) → Type). {
...
specialize (HP a) as H1.
specialize (HP b) as H2.
unfold isProp in H1, H2.
specialize (IHn (a = b)) as H2.
assert (H : a = b).
...
apply isnType_isSnType.
apply IHn; [ easy | ].

cbn in Hn.
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
