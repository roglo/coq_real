(* experimentations on HoTT *)

Require Import Utf8 QArith.

(*Set Implicit Arguments.*)

Open Scope nat_scope.

(* hott section 1.12 *)

Inductive Id {A} : A → A → Type :=
  | refl : ∀ x : A, Id x x.

Notation "x == y" := (Id x y) (at level 70).

Theorem indiscernability : ∀ A C,
  ∃ (f : ∀ (x y : A) (p : x == y), C x → C y),
  ∀ x, f x x (refl x) = id.
Proof.
intros A C.
exists
  (λ _ _ p,
   match p with
   | refl _ => id
   end).
reflexivity.
Qed.

(* hott section 1.12.1 *)

Theorem path_induction : ∀ A C c,
  ∃ (f : ∀ (x y : A) (p : x == y), C x y p),
  ∀ x, f x x (refl x) = c x.
Proof.
intros A C c.
(*
exists (Id_rect A C c).
intros x.
reflexivity.
*)
exists
  (λ _ _ p,
   match p return (C _ _ p) with
   | refl a => c a
   end).
reflexivity.
Qed.

Theorem based_path_induction : ∀ A a C c,
  ∃ (f : ∀ (x : A) (p : a == x), C x p),
  f a (refl a) = c.
Proof.
intros A a C c.
exists
  (λ _ p,
   match p return (∀ D, D _ (refl _) → D _ p) with
   | refl _ => λ _ d, d
   end C c).
reflexivity.
Qed.

(* hott section 1.12.2 *)

Theorem path_based_path_induction_iff :
  (∀ A (x : A) C c,
   ∃ (f : ∀ (x y : A) (p : x == y), C x y p),
   ∀ x, f x x (refl x) = c x)
  ↔
  (∀ A a C c,
   ∃ (f : ∀ (x : A) (p : a == x), C x p),
   f a (refl a) = c).
Proof.
split.
 intros H A a C c.
 pose proof H A a as HH.
 clear H; rename HH into H.
 Focus 2.
 intros H A x C c.
 remember (C x) as C'.
 remember (c x) as c'.
 clear Heqc'.
 rewrite <- HeqC' in c'.
 pose proof H A x C' c' as H1.
 destruct H1 as (g, Hg).
Abort. (*
bbb.

exists
  (λ _ _ p,
   match p return (C _ _ p) with
   | refl a => c a
   end).
bbb.
 exists (λ u y (p : Id x y), g y p).

 exists
   (λ x p,
    match p as q in (Id u v) return (∀ D, D u (refl u) → D v q) with
    | refl _ => λ _ d, d
    end (C a) d).
  mais c'est de la triche :-)
bbb.
 exists (f a).
 rewrite Hf.
bbb.

Check path_induction.
Check based_path_induction.
path_induction
     : ∀ (A : Type) (C : ∀ x x0 : A, Id x x0 → Type)
       (c : ∀ x : A, C x x (refl x)),
       ∃ f : ∀ (x y : A) (p : Id x y), C x y p, ∀ x : A, f x x (refl x) = c x
based_path_induction
     : ∀ (A : Type) (a : A) (C : ∀ x : A, Id a x → Type)
       (c : C a (refl a)),
       ∃ f : ∀ (x : A) (p : Id a x), C x p, f a (refl a) = c
*)

(* hott section 2.1 *)

Definition invert {A} {x y : A} (p : x == y) : y == x :=
  match p with
  | refl x => refl x
  end.
Notation "p '⁻¹'" := (invert p) (at level 10).

Lemma hott_2_1_1 : ∀ A (x : A), refl x = (refl x)⁻¹.
Proof. reflexivity. Qed.

Definition compose {A} {x y z : A} (p : x == y) : y == z → x == z :=
  match p with
  | refl _ => id
  end.
Notation "p • q" := (compose p q) (at level 40, left associativity).

Lemma hott_2_1_2 : ∀ A (x : A), refl x = refl x • refl x.
Proof. reflexivity. Qed.

Inductive andt (A B : Type) : Type := conjt : A → B → andt A B.
Notation "u '∧∧' v" := (andt u v) (at level 80, right associativity).

Lemma hott_2_1_4_i :
  ∀ A (x y z w : A) (p : x == y) (q : y == z) (r : z == w),
  p == p • refl y ∧∧ p == refl x • p.
Proof.
intros A x y z w p q r.
destruct p; split; constructor.
Qed.

Lemma hott_2_1_4_ii :
  ∀ A (x y z w : A) (p : x == y) (q : y == z) (r : z == w),
  p⁻¹ • p == refl y ∧∧ p • p⁻¹ == refl x.
Proof.
intros A x y z w p q r.
destruct p; split; constructor.
Qed.

Lemma hott_2_1_4_iii :
  ∀ A (x y z w : A) (p : x == y) (q : y == z) (r : z == w),
  (p⁻¹)⁻¹ == p.
Proof.
intros A x y z w p q r.
destruct p; constructor.
Qed.

Lemma hott_2_1_4_iv :
  ∀ A (x y z w : A) (p : x == y) (q : y == z) (r : z == w),
  p • (q • r) == (p • q) • r.
Proof.
intros A x y z w p q r.
destruct p; constructor.
Qed.

(* *)

Definition pi_type (A : Prop) (B : A → Prop) := ∀ x : A, B x.

Notation "'Π' ( x : A ) , B" :=
  (pi_type A (λ x, B)) (at level 100, x at level 0, B at level 100).

Definition homotopy {A : Prop} {B} (f g : A → B) := Π (x : A), (f x = g x).

Notation "f '~~' g" := (homotopy f g) (at level 110, g at level 110).

Theorem homotopy_refl {A B} : reflexive _ (@homotopy A B).
Proof. intros f x; reflexivity. Qed.

Theorem homotopy_symm {A B} : symmetric _ (@homotopy A B).
Proof. intros f g H x; symmetry; apply H. Qed.

Theorem homotopy_trans {A B} : transitive _ (@homotopy A B).
Proof.
intros f g h Hfg Hgh x.
transitivity (g x); [ apply Hfg | apply Hgh ].
Qed.

Add Parametric Relation {A B} : _ (@homotopy A B)
 reflexivity proved by homotopy_refl
 symmetry proved by homotopy_symm
 transitivity proved by homotopy_trans
 as homotopy_equivalence.

Lemma hott_2_4_3 : ∀ (A : Prop) B (f g : A → B) (H : f ~~ g)
  (eq_A : A → A → Prop) x y (p : eq_A x y),
  H x . g p = f p . H y.

