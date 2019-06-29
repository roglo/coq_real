(* categories *)
(* http://angg.twu.net/tmp/2016-optativa/awodey__category_theory.pdf *)

Require Import Utf8.
Set Nested Proofs Allowed.

Axiom extensionality : ∀ A B (f g : ∀ x : A, B x), (∀ x, f x = g x) → f = g.

Definition isSet (A : Type) := ∀ (a b : A) (p q : a = b), p = q.

Class category :=
  { Obj : Type;
    Hom : Obj → Obj → Type;
    comp : ∀ {A B C}, Hom A B → Hom B C → Hom A C;
    hid : ∀ {A}, Hom A A;
    unit_l : ∀ {A B} (f : Hom A B), comp hid f = f;
    unit_r : ∀ {A B} (f : Hom A B), comp f hid = f;
    assoc : ∀ {A B C D} (f : Hom A B) (g : Hom B C) (h : Hom C D),
      comp f (comp g h) = comp (comp f g) h;
    Hom_set x y : isSet (Hom x y) }.

Arguments Hom [_].
Notation "g '◦' f" := (comp f g) (at level 40, left associativity).

Coercion Obj : category >-> Sortclass.

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

Definition is_initial {C : category} (c : @Obj C) :=
  ∀ d, ∃ f : Hom c d, ∀ g, f = g.
Definition is_terminal {C : category} (c : @Obj C) :=
  ∀ d, ∃ f : Hom d c, ∀ g, f = g.

Class functor (C D : category) :=
  { f_map_obj : @Obj C → @Obj D;
    f_map_arr {a b} : Hom a b → Hom (f_map_obj a) (f_map_obj b);
    f_comp {a b c} (f : Hom a b) (g : Hom b c) :
      f_map_arr (g ◦ f) = f_map_arr g ◦ f_map_arr f;
    f_id {a} : @f_map_arr a _ hid = hid }.

Arguments f_map_obj [_] [_] [_].
Arguments f_map_arr [_] [_] _ [_] [_].

Definition is_isomorphism {C : category} {A B : Obj} (f : Hom A B) :=
  ∃ g : Hom B A, g ◦ f = hid ∧ f ◦ g = hid.

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
   existT (λ ϑ, ∀ j, c_fam D c j = c_fam D c j ◦ ϑ) hid
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

(**)

Definition mid {A} (x : A) := x.

Notation "'Σ' ( x : A ) , B" :=
  ({ x : A & B }) (at level 0, x at level 0, B at level 100, only parsing).
Notation "'Π' ( x : A ) , B" :=
  (∀ x : A, B) (at level 0, x at level 0, B at level 100, only parsing).

Definition homotopy {A B} (f g : A → B) := Π (x : A), (f x = g x).
Notation "f '∼' g" := (homotopy f g) (at level 70).

Definition composite {A B C} (f : A → B) (g : B → C) x := g (f x).
Notation "g '◦◦' f" := (composite f g) (at level 40, left associativity).

Definition isequiv {A B : Type} f :=
  ((Σ (g : B → A), (f ◦◦ g ∼ mid)) * (Σ (h : B → A), (h ◦◦ f ∼ mid)))%type.

Definition equivalence (A B : Type) := Σ (f : A → B), isequiv f.
Notation "A ≃ B" := (equivalence A B) (at level 70).

Definition ap {A B x y} (f : A → B) (p : x = y) : f x = f y :=
  match p with
  | eq_refl _ => eq_refl (f x)
  end.

Definition invert {A} {x y : A} (p : x = y) : y = x :=
  match p with
  | eq_refl _ => eq_refl x
  end.
Notation "p '⁻¹'" := (invert p)
  (at level 8, left associativity, format "'[v' p ']' ⁻¹").

Definition compose {A} {x y z : A} : x = y → y = z → x = z :=
  λ p,
  match p with
  | eq_refl _ => mid
  end.
Notation "p • q" := (compose p q) (at level 40, left associativity).

Definition qinv {A B} (f : A → B) :=
  Σ (g : B → A), ((f ◦◦ g ∼ mid) * (g ◦◦ f ∼ mid))%type.

Definition isequiv_qinv {A B} (f : A → B) : isequiv f → qinv f :=
  λ p,
  match p with
  | (existT _ g Hg, existT _ h Hh) =>
      existT _ g (Hg, λ x, ((ap h (Hg (f x)))⁻¹ • Hh (g (f x)))⁻¹ • Hh x)
  end.

Definition qinv_isequiv {A B} (f : A → B) : qinv f → isequiv f.
Proof.
intros p.
destruct p as (g, (α, β)).
split; exists g; assumption.
Defined.

Definition hott_2_1_4_i_1 {A} {x y : A} : ∀ (p : x = y),
    p = p • eq_refl y
 := (λ (p : x = y),
     match p return (p = p • eq_refl _) with
     | eq_refl _ => eq_refl (eq_refl x • eq_refl x)
     end).

Definition hott_2_1_4_i_2 {A} {x y : A} : ∀ (p : x = y),
    p = eq_refl x • p
 := (λ (p : x = y),
   match p return (p = eq_refl _ • p) with
   | eq_refl _ => eq_refl (eq_refl x • eq_refl x)
   end).

Definition lu {A} {b c : A} (r : b = c) : r = eq_refl b • r :=
  hott_2_1_4_i_2 r.

Definition ru {A} {a b : A} (p : a = b) : p = p • eq_refl b :=
  hott_2_1_4_i_1 p.

Definition dotl {A} {a b c : A} {r s : b = c}
  (q : a = b) (β : r = s) : (q • r = q • s).
Proof.
destruct q.
pose proof (@hott_2_1_4_i_2 A a c r) as H2.
apply invert in H2.
eapply compose; [ apply H2 | idtac ].
pose proof (@hott_2_1_4_i_2 A a c s) as H4.
eapply compose; [ apply β | apply H4 ].
Defined.

Definition dotr {A} {a b c : A} {p q : a = b}
  (r : b = c) (α : p = q) : (p • r = q • r).
Proof.
destruct r.
pose proof (@hott_2_1_4_i_1 A a b p) as H1.
apply invert in H1.
eapply compose; [ apply H1 | idtac ].
pose proof (@hott_2_1_4_i_1 A a b q) as H3.
eapply compose; [ apply α | apply H3 ].
Defined.

Lemma compose_invert_l {A} {x y : A} : ∀ (p : x = y), p⁻¹ • p = eq_refl y.
Proof.
intros p; destruct p; reflexivity.
Qed.

Definition compose_invert_r {A} {x y : A} : ∀ (p : x = y), p • p⁻¹ = eq_refl x
  := λ p, match p with eq_refl _ => eq_refl (eq_refl x) end.

Lemma compose_assoc {A} {x y z w : A} :
  ∀ (p : x = y) (q : y = z) (r : z = w),
  p • (q • r) = (p • q) • r.
Proof.
intros p q r; destruct p; reflexivity.
Qed.

Definition hott_2_4_3 {A B x y} (f g : A → B) (H : f ∼ g) (p : x = y)
  : H x • ap g p = ap f p • H y
  := match p with
     | eq_refl _ =>
         match
           match H x as q return (q = q • eq_refl _) with
           | eq_refl _ => eq_refl (eq_refl (f x) • eq_refl (f x))
           end
         with
         | eq_refl _ => eq_refl (id (H x))
         end
     end.

Definition ap_composite {A B C x y}
  : ∀ (f : A → B) (g : B → C) (p : x = y),
    ap g (ap f p) = ap (g ◦◦ f) p
  := λ f g p,
     match p with eq_refl _ => eq_refl (ap g (ap f (eq_refl x))) end.

Definition hott_2_2_2_iv A (x y : A) : ∀ (p : x = y), ap mid p = p
  := λ p, match p with eq_refl _ => eq_refl (eq_refl x) end.

Theorem hott_2_11_1 {A B} : ∀ (f : A → B), isequiv f → ∀ (a a' : A),
  (a = a') ≃ (f a = f a').
Proof.
intros f Hf a a'.
exists (@ap A B a a' f).
apply isequiv_qinv in Hf.
destruct Hf as (f₁, (α, β)).
apply qinv_isequiv.
unfold qinv.
set (g := λ r, (β a)⁻¹ • ap f₁ r • β a').
unfold "◦◦", mid in g; simpl in g.
exists g; subst g.
unfold "◦◦", "∼", id; simpl.
split; intros q.
-set (r := @compose _ _ _ a' (@invert _ (f₁ (f a)) a (β a) • ap f₁ q) (β a')).
 apply (@compose _ _ ((α (f a))⁻¹ • α (f a) • ap f r)).
 +eapply compose; [ apply lu | idtac ].
  apply dotr, invert, compose_invert_l.
 +eapply compose; [ eapply invert, compose_assoc | idtac ].
  unfold mid, composite; simpl.
  pose proof (hott_2_4_3 ((f ◦◦ f₁) ◦◦ f) f (λ a, α (f a)) r) as H.
  unfold "◦" in H; simpl in H.
  eapply compose; [ eapply dotl, H | simpl ].
  apply (@compose _ _ ((α (f a))⁻¹ • (ap f (ap f₁ (ap f r)) • α (f a')))).
  *apply dotl, dotr.
   apply (@compose _ _ (ap (f ◦◦ f₁ ◦◦ f) r)); [ reflexivity | idtac ].
   eapply invert, compose; [ idtac | eapply ap_composite ].
   eapply compose; [ apply (ap_composite f₁ f (ap f r)) | reflexivity ].
  *eapply compose; [ apply compose_assoc | idtac ].
   rewrite (ap_composite f f₁ r).
   apply (@compose _ _ ((α (f a))⁻¹ • ap f (β a • r • (β a')⁻¹) • α (f a'))).
  --apply dotr, dotl, ap.
    rewrite r; simpl.
    rewrite <- ru, compose_invert_r.
    reflexivity.
  --apply (@compose _ _ ((α (f a))⁻¹ • ap f (ap f₁ q) • α (f a'))).
   **apply dotr, dotl, ap; subst r.
     do 2 rewrite compose_assoc.
     rewrite compose_invert_r; simpl.
     unfold mid; simpl.
     rewrite <- compose_assoc.
     rewrite compose_invert_r; simpl.
     rewrite <- ru; reflexivity.
   **assert (H1 : α (f a) • q = ap (f ◦◦ f₁) q • α (f a')). {
       rewrite <- (hott_2_4_3 (f ◦◦ f₁) mid α q).
       apply dotl, invert, hott_2_2_2_iv.
     }
     unfold mid, composite; simpl.
     pose proof (@ap_composite B A B (f a) (f a') f₁ f q) as H2.
     rewrite H2.
     rewrite <- compose_assoc.
     unfold mid, composite in H1; simpl in H1.
     unfold composite; simpl.
     rewrite <- H1.
     rewrite compose_assoc, compose_invert_l.
     reflexivity.
-rewrite (ap_composite f f₁ q).
 destruct q; simpl.
 unfold "◦◦", "∼", id in β; simpl in β.
 unfold "◦◦"; simpl; rewrite β; reflexivity.
Defined.

Definition quasi_inv {A B} : A ≃ B → B ≃ A :=
  λ eqf,
  match eqf with
  | existT _ f (existT _ g Hg, existT _ h Hh) =>
      existT isequiv g
        (existT _ f (λ x, (Hh (g (f x)))⁻¹ • ap h (Hg (f x)) • Hh x),
         existT _ f Hg)
 end.

(**)

Definition isProp (A : Type) := ∀ (x y : A), x = y.

Definition isContr A := {a : A & ∀ x : A, a = x }.

Fixpoint isnType A n :=
  match n with
  | 0 => isProp A
  | S p' => ∀ x y : A, isnType (x = y) p'
  end.

Theorem compose_cancel_l {A} {x y z : A} (p : x = y) (q r : y = z) :
  compose p q = compose p r → q = r.
Proof. intros; now destruct p. Qed.

Theorem compose_eq_refl : ∀ A (x : A) (p : x = x), compose p eq_refl = p.
Proof. now intros; destruct p. Qed.

Theorem isProp_isSet {A} : isProp A → isSet A.
Proof.
intros f x y p q.
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
  destruct Hf as ((g, Hfg), (h, Hhf)).
(*
  destruct Hf as (g, Hgf, Hfg).
*)
  move h before g.
  unfold mid, "◦◦", "∼" in Hfg, Hhf.
  cbn in HA |-*.
  unfold isProp in HA |-*.
  intros x y.
  rewrite <- Hfg; symmetry.
  rewrite <- Hfg; symmetry.
  f_equal.
  apply HA.
}
destruct HAB as (f, Hf).
destruct Hf as ((g, Hfg), (h, Hhf)).
(*
destruct Hf as (g, Hgf, Hfg).
*)
cbn in HA |-*.
move h before g.
unfold mid, "◦◦", "∼" in Hfg, Hhf.
intros x y.
apply (IHn (g x = g y) (x = y)); [ | apply HA ].
apply quasi_inv.
apply hott_2_11_1.
split.
-exists f.
 unfold "◦◦", "∼", mid.
 intros z.
 rewrite <- Hhf.
 clear - Hfg Hhf.
 f_equal. (* bizarre que ça marche *)
-exists f.
 unfold "◦◦", "∼", mid.
 apply Hfg.
Qed.

Definition lift {A P} {x y : A} (u : P x) (p : x = y)
  : existT _ x u = existT _ y (transport P _ u)
  := match p with
     | eq_refl _ => eq_refl (existT P x (transport P (eq_refl x) u))
     end.

Theorem pair_transport_eq_existT {A} {P : A → Type} :
  ∀ a b (Ha : P a) (Hb : P b),
  {p : a = b & transport P p Ha = Hb} → existT P a Ha = existT P b Hb.
Proof.
intros * (p, Hp).
now destruct p, Hp.
Defined.

Theorem eq_existT_pair_transport {A} {P : A → Type} :
  ∀ a b (Ha : P a) (Hb : P b),
  existT P a Ha = existT P b Hb → {p : a = b & transport P p Ha = Hb}.
Proof.
intros * Hee.
inversion_sigma.
destruct Hee0.
now exists eq_refl.
Defined.

Theorem pair_transport_equiv_eq_existT {A : Type} : ∀ (P : A → Type),
  (∀ x, isProp (P x))
  → ∀ a b (Ha : P a) (Hb : P b),
  {p : a = b & transport P p Ha = Hb} ≃ (existT P a Ha = existT P b Hb).
Proof.
intros.
unfold "≃".
exists (pair_transport_eq_existT a b Ha Hb).
split. {
  exists (eq_existT_pair_transport a b Ha Hb).
  unfold "◦◦", "∼", mid.
  intros p.
  inversion_sigma.
  destruct p0.
  cbn in p1; cbn.
  now destruct p1.
}
exists (eq_existT_pair_transport a b Ha Hb).
unfold "◦◦", "∼", mid.
intros (p, Hp).
now destruct p, Hp.
Qed.

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
eapply isnType_if_equiv; [ | apply H4 ].
now apply pair_transport_equiv_eq_existT.
Qed.

Theorem is_set_is_set_sigT {A} {P : A → Type} :
  (∀ x, isProp (P x)) → isSet A → isSet (@sigT A P).
Proof.
intros * HP HS.
now apply (isnType_isnType_sigT A 1 P).
Qed.

Theorem cCone_Hom_set {J C} {D : functor J C} :
  ∀ c c' : cone D, isSet (cCone_Hom c c').
Proof.
intros.
unfold cCone_Hom.
apply is_set_is_set_sigT; [ | apply Hom_set ].
intros f.
intros p q.
apply extensionality.
intros x.
apply Hom_set.
Qed.

Definition cCone {J C} (D : functor J C) :=
  {| Obj := cone D;
     Hom := cCone_Hom;
     comp := cCone_comp;
     hid := cCone_id;
     unit_l := cCone_unit_l;
     unit_r := cCone_unit_r;
     assoc := cCone_assoc;
     Hom_set := cCone_Hom_set |}.

(* A limit for a functor D : J → C is a terminal object in Cone(D) *)

Definition is_limit {J C} {D : functor J C} (cn : cone D) :=
  @is_terminal (cCone D) cn.

(* Spelling out the definition, the limit of a diagram D has the
   following UMP: given any cone (C, cj) to D, there is a unique
   arrow u : C → lim←−j Dj such that for all j,
     pj ◦ u = cj .
*)

Theorem limit_UMP {J C} {D : functor J C} :
  ∀ l : cone D, is_limit l →
  ∀ c : cone D, exists! u, ∀ j, c_fam _ l j ◦ u = c_fam _ c j.
Proof.
intros * Hlim c.
unfold unique.
unfold is_limit in Hlim.
unfold is_terminal in Hlim.
specialize (Hlim c) as H1.
destruct H1 as (f, H1).
exists (projT1 f).
split. {
  intros j.
  destruct f as (f, Hf).
  now symmetry.
}
intros h Hh.
assert (Hh' : ∀ j : J, c_fam D c j = c_fam D l j ◦ h). {
  intros j; specialize (Hh j).
  now symmetry.
}
remember
  (existT
     (λ ϑ : Hom (c_top D c) (c_top D l),
      ∀ j : J, c_fam D c j = c_fam D l j ◦ ϑ) h Hh') as hh.
now rewrite (H1 hh); subst hh.
Qed.
