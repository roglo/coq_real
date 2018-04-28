(* jeu avec les catégories *)

Require Import Utf8.
(*
Set Universe Polymorphism.
*)

Definition compose {A B C} (f : A → B) (g : B → C) := λ x, g (f x).
Notation "g '◦' f" := (compose f g) (at level 40).
Notation "f '==' g" := (∀ x, f x = g x) (at level 70).

(* surjection vs epimorphism *)

Definition is_surjection {A B} (f : A → B) := ∀ y, ∃ x, f x = y.
Definition is_epimorphism {A B} (u : A → B) :=
  ∀ C (v w : B → C), v ◦ u == w ◦ u → v == w.

Definition has_decidable_equality A := ∀ x y : A, {x = y} + {x ≠ y}.
Definition not_not_exist_imp_exist A :=
  ∀ (P : A → Prop), (¬ ¬ ∃ x, P x) → ∃ x, P x.

Theorem is_surjection_is_epimorphism :
  ∀ A B (f : A → B), is_surjection f → is_epimorphism f.
Proof.
intros * Hs.
unfold is_surjection in Hs.
intros C v w He y.
specialize (Hs y) as (x, Hx).
subst y; apply He.
Defined.

Theorem is_epimorphism_is_surjection :
  ∀ A B (f : A → B),
  has_decidable_equality B →
  not_not_exist_imp_exist A →
  is_epimorphism f → is_surjection f.
Proof.
intros A B u EqB NNE He.
unfold is_epimorphism in He.
intros y.
set (v (b : B) := if EqB b y then 1 else 0).
set (w (b : B) := 0).
specialize (He _ v w) as H1.
assert (Hn : ¬ (∀ x, u x ≠ y)). {
  intros H2.
  assert (Hx : v ◦ u == w ◦ u). {
    intros x.
    unfold v, w, "◦"; simpl.
    destruct (EqB (u x) y) as [H3| H3]; [ | easy ].
    now specialize (H2 x).
  }
  specialize (H1 Hx y).
  unfold v, w in H1.
  now destruct (EqB y y).
}
apply NNE.
intros H2.
apply Hn; intros x H3.
apply H2.
now exists x.
Defined.

(* injection vs monomorphism *)

Definition is_injection {A B} (f : A → B) := ∀ x y, f x = f y → x = y.
Definition is_monomorphism {A B} (u : A → B) :=
  ∀ C (v w : C → A), u ◦ v == u ◦ w → v == w.

Theorem is_injection_is_monomorphism :
  ∀ A B (f : A → B), is_injection f → is_monomorphism f.
Proof.
intros A B u Hi C v w Hu c.
unfold is_injection in Hi.
specialize (Hi (v c) (w c)) as H1.
now specialize (H1 (Hu c)).
Defined.

Definition is_injection_is_monomorphism2 :
    ∀ A B (f : A → B), is_injection f → is_monomorphism f :=
  λ A B u Hi C v w Hu c, Hi (v c) (w c) (Hu c).

Theorem is_monomorphism_is_injection :
  ∀ A B (f : A → B), is_monomorphism f → is_injection f.
Proof.
intros A B u Hm x y Hu.
unfold is_monomorphism in Hm.
set (v (_ : True) := x).
set (w (_ : True) := y).
specialize (Hm _ v w) as H1.
assert (H : u ◦ v == u ◦ w) by easy.
specialize (H1 H); clear H.
now unfold v, w in H1; apply H1.
Show Proof.
Defined.

Definition is_monomorphism_is_injection2 :
    ∀ A B (f : A → B), is_monomorphism f → is_injection f :=
  λ A B f Hm x y Hu, Hm _ (λ _, x) (λ _, y) (λ _, Hu) I.

(* sections and retractions *)

Definition has_section {A B} (f : A → B) := ∃ s, f ◦ s == λ y, y.
Definition has_retraction {A B} (f : A → B) := ∃ r, r ◦ f == λ x, x.

Theorem has_section_is_epimorphism : ∀ A B (f : A → B),
  has_section f → is_epimorphism f.
Proof.
intros A B u HS.
destruct HS as (s, HS).
unfold is_epimorphism.
intros C v w Hu y.
specialize (HS y) as H1.
rewrite <- H1.
unfold compose.
apply Hu.
Qed.

Theorem has_retraction_is_monomorphism : ∀ A B (f : A → B),
  has_retraction f → is_monomorphism f.
Proof.
intros A B u HR.
destruct HR as (r, HR).
unfold is_monomorphism.
intros C v w Hu c.
rewrite <- HR; symmetry.
rewrite <- HR; symmetry.
unfold "◦" in Hu.
unfold "◦".
now rewrite Hu.
Qed.

(* snake lemma *)

Require List.
Import List.ListNotations.
Open Scope list_scope.

Record ZF := mkZF
  { zfset : Type;
    zfelm : Type;
    zfmem : zfelm → zfset → Prop;
    zfext : ∀ A B, (∀ x, zfmem x A ↔ zfmem x B) → A = B }.

Notation "x '∈' S" := (zfmem _ x S) (at level 60).

Record set1 T := mkset { setp : T → Prop }.
Arguments mkset [T] _.
Arguments setp [T] _ _.
Axiom ext1 : ∀ T (A B : set1 T), (∀ x, setp A x ↔ setp B x) → A = B.
Definition set T := mkZF (set1 T) T (λ e s, setp s e) (ext1 T).

...

Record set T := mkset { setp : T → Prop }.
Arguments mkset [T] _.
Arguments setp [T] _ _.

Notation "x '∈' S" := (setp S x) (at level 60).
Definition set_incl {T} (A B : set T) := ∀ x, x ∈ A → x ∈ B.
Notation "A '⊆' B" := (set_incl A B) (at level 70).
Definition set_eq {T} (A B : set T) := A ⊆ B ∧ B ⊆ A.
Notation "A '≡' B" := (set_eq A B) (at level 70).

Record category {U} := mkcat
  { ob : set U;
    mor : set (U * U);
    src : ∀ f, f ∈ mor → ∃ A, A ∈ ob ∧ fst f = A;
    dst : ∀ f, f ∈ mor → ∃ B, B ∈ ob ∧ snd f = B }.

...

Record element {T} (S : set T) :=
  { el_val : T; in_set : el_val ∈ S }.

Record group {T} := mkgr
  { gr_set : set T;
    gr_zero : element gr_set }.

Definition zero {T} (A : @group T) := el_val (gr_set A) (gr_zero _).

Record gmorph {T} A B := mkgm
  { gm_fun : T → T;
    gr_prop : ∀ x, x ∈ gr_set A → gm_fun x ∈ gr_set B }.

Definition Im {T} (A : group) (B : group) (f : T → T) :=
  mkset (λ b, b ∈ gr_set B ∧ ∃ a, a ∈ gr_set A ∧ f a = b).
Definition Ker {T} (A : group) (B : group) (f : T → T) :=
  mkset (λ a, a ∈ gr_set A ∧ f a = zero B).

Inductive sequence {T} (A : @group T) :=
  | Seq1 : sequence A
  | Seq2 : ∀ B (f : gmorph A B), sequence B → sequence A.

Fixpoint exact_sequence {T} (A : @group T) (S : sequence A) :=
  match S with
  | Seq1 _ => True
  | Seq2 _ f B S' =>
      match S' with
      | Seq1 _ => True
      | Seq2 _ g C S'' => Im A B f ≡ Ker A B g ∧ exact_sequence B S'
      end
  end.

Arguments Seq1 {T} G.
Arguments Seq2 {T} G f H.

Lemma snake {T} :
  ∀ A B C A' B' C' (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
     (a : A → A') (b : B → B') (c : C → C')
     (cz : C → False) (za' : False → A')
  (s : exact_sequence (Seq2 f (Seq2 g (Seq2 cz Seq1))))
  (s' : exact_sequence (Seq2 za' (Seq2 f' (Seq2 g' Seq1)))),
  False.
Proof.
intros.

Lemma snake :
  ∀ A B C A' B' C' (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
     (a : A → A') (b : B → B') (c : C → C')
     (cz : C → False) (za' : False → A')
  (s : exact_sequence (Seq2 f (Seq2 g (Seq2 cz Seq1))))
  (s' : exact_sequence (Seq2 za' (Seq2 f' (Seq2 g' Seq1)))),
  False.
Proof.
intros.

...

(* digression sur Yoneda *)

Lemma Yoneda : ∀ A : Prop, (∀ C : Prop, (A → C) → C) ↔ A.
Proof.
intros.
split.
-intros HC.
 specialize (HC A).
 now apply HC.
-intros * HC C HA.
 now apply HA.
Qed.

(* tiens, au fait, qu'est-ce que l'univalence en pense ? *)

Definition isequiv {A B : Type} (f : A → B) :=
  {g : B → A & (∀ a, g (f a) = a) & (∀ b, f (g b) = b)}.

Definition equivalence (A B : Type) := { f : A → B & isequiv f}.
Notation "A ≃ B" := (equivalence A B) (at level 70).

Theorem happly : ∀ A B (f g : ∀ (x : A), B x), f = g → ∀ (x : A), f x = g x.
Proof.
intros * p.
now destruct p.
Defined.

Definition extensionality := ∀ A B f g, isequiv (happly A B f g).

Theorem are_equiv_inj_mono : ∀ A B (f : A → B),
  extensionality
  → is_injection f ≃ is_monomorphism f.
Proof.
intros * HF.
exists (is_injection_is_monomorphism2 A B f).
unfold isequiv.
exists (is_monomorphism_is_injection2 A B f); [ easy | ].
intros HM.
unfold is_monomorphism_is_injection2.
unfold is_injection_is_monomorphism2.
unfold is_monomorphism in HM.
apply HF; intros C.
apply HF; intros g.
apply HF; intros h.
apply HF; intros HU.
apply HF; intros c.
specialize (HM _ _ _ HU) as H1.
specialize (HF _ _ g h) as H2.
unfold happly in H2.
unfold isequiv in H2.
simpl in H2.
destruct H2 as (H3, H4, H5).
clear H4 H5.
specialize (H3 H1).
subst g.

(* ouais, chais pas *)

...

Theorem are_equiv_surj_epi : ∀ A B (f : A → B),
  has_decidable_equality B
  → not_not_exist_imp_exist A
  → is_surjection f ≃ is_epimorphism f.
Proof.
intros * EqB NNE.
exists (is_surjection_is_epimorphism A B f).
unfold isequiv.
exists (is_epimorphism_is_surjection A B f EqB NNE).
-intros HS.
 unfold is_epimorphism_is_surjection.
...
