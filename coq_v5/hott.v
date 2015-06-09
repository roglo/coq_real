(* experimentations on HoTT *)

Require Import Utf8 QArith.

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
Abort. (* to be done *)

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

Lemma hott_2_1_4_i {A} {x y z w : A} :
  ∀ (p : x == y) (q : y == z) (r : z == w),
  p == p • refl y ∧∧ p == refl x • p.
Proof.
intros p q r.
destruct p; split; constructor.
Qed.

Lemma hott_2_1_4_ii {A} {x y z w : A} :
  ∀ (p : x == y) (q : y == z) (r : z == w),
  p⁻¹ • p == refl y ∧∧ p • p⁻¹ == refl x.
Proof.
intros p q r.
destruct p; split; constructor.
Qed.

Lemma hott_2_1_4_iii {A} {x y z w : A} :
  ∀ (p : x == y) (q : y == z) (r : z == w),
  (p⁻¹)⁻¹ == p.
Proof.
intros p q r.
destruct p; constructor.
Qed.

Lemma hott_2_1_4_iv {A} {x y z w : A} :
  ∀ (p : x == y) (q : y == z) (r : z == w),
  p • (q • r) == (p • q) • r.
Proof.
intros p q r.
destruct p; constructor.
Qed.

Definition Ω {A} (a : A) := (a == a).
Definition Ω2 {A} (a : A) := (refl a == refl a).

(*
Section omega.

Parameter A : Type.
Parameter a b c : A.
Parameter p q : a == b.
Parameter r s : b == c.
*)

(* whiskering *)
Definition dotr {A} (a b c : A)
  (p : a == b) (q : a == b) (r : b == c) (α : p == q) : (p • r == q • r).
Proof.
induction r as (b).
pose proof (@hott_2_1_4_i A a b a b p (p ⁻¹) p) as (H1, H2).
apply invert in H1.
eapply compose; [ apply H1 | idtac ].
pose proof (@hott_2_1_4_i A a b a b q (q ⁻¹) q) as (H3, H4).
eapply compose; [ apply α | apply H3 ].
Defined.

(* whiskering *)
Definition dotl {A} (a b c : A)
  (q : a == b) (r : b == c) (s : b == c) (β : r == s) : (q • r == q • s).
Proof.
induction q as (b).
pose proof (@hott_2_1_4_i A b c b c r (r⁻¹) r) as (H1, H2).
apply invert in H2.
eapply compose; [ apply H2 | idtac ].
pose proof (@hott_2_1_4_i A b c b c s (s⁻¹) s) as (H3, H4).
eapply compose; [ apply β | apply H4 ].
Qed.

(* (α •r r) • (q •l β) : p == q → r == s → p • r == q • s *)
(*
Definition star α β := dotr p q r s α β • dotl p q r s α β.
Notation "α ★ β" := (star α β) (at level 40).
*)

Definition ru {A} (a b c : A) (p : a == b) (r : b == c) :=
  match hott_2_1_4_i p (refl b) r with
  | conjt x _ => x
  end.

Definition ru2 {A} (a b c : A) (p : a == b) q (r : b == c) :=
  match hott_2_1_4_i p q r with
  | conjt x _ => x
  end.

Print ru2.

Check (λ a b c p q r α, (ru a b c p r)⁻¹ • α • ru a b c q r).
(* ∀ (a b c : A) (p q : a == b), b == c → p == q
   → p • refl b == q • refl b *)
Check @dotr.
(* ∀ (A : Type) (a b c : A) (p q : a == b) (r : b == c), p == q
   → p • r == q • r *)

Check ru.
(* ∀ (a b c : A) (p : a == b), b == c
   → p == p • refl b *)

Theorem aaa : ∀ A (a b : A) p q r α,
  dotr a b b p q (refl b) α =
  (ru2 a b b p (refl b) r)⁻¹ • α • ru2 a b b p q r.
Proof.
bbb.

Theorem aaa : ∀ A (a b : A) p q r α,
  dotr a b b p q (refl b) α =
  (ru a b b p r)⁻¹ • α • ru a b b q r.
Proof.

Definition dotr2 A (a b c : A) p q r α :=
  (ru a b c p r)⁻¹ • α • ru a b c q r.

Print dotr2.

intros.
unfold dotr; simpl.
unfold ru; simpl.
bbb.

(* mmm... *)
Theorem aaa : ∀ a b c p q r s α β,
  dotr a b c p q r r α (*refl b*)β = (ru a b c p r)⁻¹ • α • ru a b c q r.

Theorem aaa : ∀ α, dotr a b b p q r s α (refl b) = rup⁻¹ • α • ruq.
Proof.
bbb.

(* chais pas... *)
Definition star' α β := dotr a b c q p s r α β • dotl a b c q p s r α β.
Check star'.

bbb.

Theorem hott_2_1_6 {A} : ∀ (a : A) (α β : Ω2 a), α • β == β • α.
Proof.
intros a α β.
Check @star.
unfold Ω2 in α, β.

bbb.

(* hott, later... *)

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

