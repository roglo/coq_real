(* experimentations on axiom of univalence *)

Require Import Utf8.

(* version Jérémy *)

Definition is_equiv {A B : Set} (f : A → B) :=
 ∃ g : B → A,
 (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y).

Definition equiv (A B : Set) := ∃ f : A → B, is_equiv f.
Notation "A ≃ B" := (equiv A B) (at level 60).

Definition eq_to_equiv A B : A = B → A ≃ B.
Proof.
intros H.
subst B.
unfold equiv, is_equiv.
exists (λ x, x), (λ x, x).
split; intros x; reflexivity.
Defined.

Print eq_to_equiv.

Axiom univalence : ∀ A B, is_equiv (eq_to_equiv A B).

Inductive t := foo : t | bar : t.

Theorem bool_equiv_t : bool ≃ t.
Proof.
exists (λ b : bool, if b then foo else bar).
exists (λ b : t, if b then true else false).
split; intros x; destruct x; reflexivity.
Defined.

Theorem bool_eq_t : bool = t.
Proof.
apply univalence.
apply bool_equiv_t.
Defined.

Print bool_eq_t.

Definition negt : t → t.
Proof.
rewrite <- bool_eq_t.
apply negb.
Defined.

Theorem aaa : negt foo = bar.
Proof.
unfold negt.
unfold negb; simpl.
unfold eq_rec; simpl.
unfold eq_rect; simpl.
unfold bool_eq_t.
unfold bool_equiv_t.
remember (univalence bool t) as v eqn:Hv.
destruct v as (v, (f, g)).
bbb.

(* ma version initiale *)

Definition equiv A B :=
  ∃ f : A → B, ∃ g : B → A,
  (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y).

Notation "A ≃ B" := (equiv A B) (at level 60).

Axiom univalence : ∀ A B : Set, (A ≃ B) ≃ (A = B).

Inductive t := foo : t | bar : t.

Theorem bool_equiv_t : bool ≃ t.
Proof.
exists (λ b : bool, if b then foo else bar).
exists (λ b : t, if b then true else false).
split; intros x; destruct x; reflexivity.
Defined.

Theorem bool_eq_t : bool = t.
Proof.
apply univalence, bool_equiv_t.
Defined.

Definition negt : t → t.
Proof.
rewrite <- bool_eq_t.
apply negb.
Defined.

Theorem aaa : negt foo = bar.
Proof.
unfold negt.
unfold negb; simpl.
unfold eq_rec; simpl.
unfold eq_rect; simpl.
bbb.

unfold bool_eq_t.
remember (univalence bool t) as v eqn:Hv.
destruct v as (f, H); simpl.
destruct H as (g, (H1, H2)).
bbb.
