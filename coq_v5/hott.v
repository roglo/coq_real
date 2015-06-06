(* experimentations on HoTT *)

Require Import Utf8 QArith.

Set Implicit Arguments.

Open Scope nat_scope.

(* hott section 1.12 *)

Inductive paths {A} : A -> A -> Type :=
  | idpath : ∀ x, paths x x.

Inductive Id {A} : A → A → Type :=
  | refl : ∀ x : A, Id x x.

Theorem option_is : ∀ A (x : option A), x = None ∨ ∃ y, x = Some y.
Proof.
intros A x.
destruct x as [y| ]; [ right; exists y; reflexivity | idtac ].
left; reflexivity.
Qed.

Definition indisc_fun {A} (C : A → Set) x y (p : Id x y) cx :=
  match p in (Id a b) return (C a → C b) with
  | refl _ => id
  end cx.

Theorem indiscernability : ∀ A (C : A → Set),
  ∃ (f : ∀ x y (p : Id x y), C x → C y),
  ∀ x, f x x (refl x) = id.
Proof.
intros A C.
exists (indisc_fun C).
intros x; reflexivity.
Qed.

(* hott section 1.12.1 *)

Print Id_ind.

Theorem my_Id_ind : ∀ A (P : ∀ x y : A, Id x y → Prop),
  (∀ a : A, P a a (refl a))
  → ∀ x y (p : Id x y), P x y p.
Proof.
intros A P Hr x y p.
destruct p.
apply Hr.
Qed.

Theorem path_induction0 :
  ∀ A,
  ∀ (C : A → A → Prop),
  ∀ (c : ∀ x, C x x),
  ∃ (f : ∀ x y : A, C x y),
  ∀ x, f x x = c x.
Proof.
intros A C c.
bbb.

Theorem path_induction :
  ∀ A,
  ∀ (C : ∀ x y : A, Id x y → Prop),
  ∀ (c : ∀ x, C x x (refl x)),
  ∃ (f : ∀ x y : A, ∀ p : Id x y, C x y p),
  ∀ x, f x x (refl x) = c x.
Proof.
intros A C c.
generalize c; intros d.
eapply my_Id_ind in c.

exists (λ x y p, c x).
bbb.

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

