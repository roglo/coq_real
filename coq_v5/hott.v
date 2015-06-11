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

Print compose.

Theorem fold_compose : ∀ A (x y z : A) p,
  (λ p,
   match p in (a == a0) return (a0 == z → a == z) with
   | refl x0 => id
   end) p = @compose A x y z p.
Proof. reflexivity. Qed.

Lemma hott_2_1_2 : ∀ A (x : A), refl x = refl x • refl x.
Proof. reflexivity. Qed.

Inductive andt (A B : Type) : Type := conjt : A → B → andt A B.
Notation "u '∧∧' v" := (andt u v) (at level 80, right associativity).

Lemma hott_2_1_4_i {A} {x y : A} : ∀ (p : x == y),
  p == p • refl y ∧∧ p == refl x • p.
Proof.
intros p.
destruct p; split; constructor.
Defined.

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

(* Theorem 2.1.6 (Eckmann-Hilton) *)

Definition Ω {A} (a : A) := (a == a).
Definition Ω2 {A} (a : A) := (refl a == refl a).

(* whiskering *)
Definition dotr {A} (a b c : A)
  (p : a == b) (q : a == b) (r : b == c) (α : p == q) : (p • r == q • r).
Proof.
induction r as (b).
pose proof (@hott_2_1_4_i A a b p) as (H1, H2).
apply invert in H1.
eapply compose; [ apply H1 | idtac ].
pose proof (@hott_2_1_4_i A a b q) as (H3, H4).
eapply compose; [ apply α | apply H3 ].
Defined.

(* whiskering *)
Definition dotl {A} (a b c : A)
  (q : a == b) (r : b == c) (s : b == c) (β : r == s) : (q • r == q • s).
Proof.
induction q as (b).
pose proof (@hott_2_1_4_i A b c r) as (H1, H2).
apply invert in H2.
eapply compose; [ apply H2 | idtac ].
pose proof (@hott_2_1_4_i A b c s) as (H3, H4).
eapply compose; [ apply β | apply H4 ].
Defined.

(*
Definition star α β := dotr a b c p q r α • dotl a b c q r s β.
Notation "α ★ β" := (star α β) (at level 40).
*)

Definition star {A} (a b c : A) p q r s α β :=
  dotr a b c p q r α • dotl a b c q r s β.

Definition star' {A} (a b c : A) p q r s α β :=
  dotl a b c p r s β • dotr a b c p q s α.

Definition ru {A} (a b : A) (p : a == b) :=
  match hott_2_1_4_i p with
  | conjt x _ => x
  end.

Check @ru.
(* ru
     : ∀ (A : Type) (a b : A) (p : a == b) → p == p • refl b *)

Check (λ A a b p q α, (@ru A a b p)⁻¹ • α • (@ru A a b q)).
(* p • refl b == q • refl b *)

Definition lu {A} (b c : A) (r : b == c) :=
  match hott_2_1_4_i r with
  | conjt _ x => x
  end.

Check @lu.

(* lu
     : ∀ (A : Type) (b c : A) (r : b == c), r == refl b • r *)

bbb.

Check (λ A a b c p q r β, (@lu A a b c p r)⁻¹ • β • (@lu A a b c q r)).
(* refl a • p == refl a • q *)

(*
Bug in hott page 69
  α •_r refl_b is ill typed
Indeed,
  Check (λ A a b c p q α, @dotr A a b c p q (refl b) α).
Coq answer
  The term "refl b" has type "b == b" while it is expected to have type
   "b == c".

Actually, we must start with the hypothesis that a ≡ b ≡ c supposed later
(below in the same page).
*)

Theorem step3 {A} : ∀ (a : A)
    (p := refl a) (q := p) (r := p) (s := p) (α : p == q) (β : r == s),
  α • β ==
    (refl (refl a))⁻¹ • α • (refl (refl a)) •
    (refl (refl a))⁻¹ • β • (refl (refl a)).
Proof.
intros.
remember ((refl (refl a)) ⁻¹ • α • refl (refl a) • (refl (refl a)) ⁻¹ • β).
apply @compose with (y := i); [ subst i | eapply hott_2_1_4_i; apply i ].
apply dotr; simpl; unfold id.
eapply @compose; [ idtac | apply hott_2_1_4_iv ].
simpl; unfold id.
eapply hott_2_1_4_i; constructor.
Qed.

(*
Theorem step2 {A} : ∀ (a : A)
    (p := refl a) (q := p) (r := p) (s := p) (α : p == q) (β : r == s),
  α • β ==
    (ru (refl a))⁻¹ • α • (ru (refl a)) •
    (lu (refl a))⁻¹ • β • (lu (refl a)).
Proof.
intros.
bbb.

Check @ru.
Check @lu.
*)

(*
Theorem agaga4 {A} : ∀ (a : A)
    (p := refl a) (q := refl a) (r := refl a) (s := refl a)
    (α : p == q) (β : r == s),
  α • β == β • α.
Proof.
intros.
subst q r s.
bbb.

Theorem agaga2 {A} : ∀ (a : A)
    (p : a == a) (q := p) (r := p) (s := p) (α : p == q) (β : r == s),
  α • β == β • α.
Proof.
intros.
bbb.

(* autre expérimentation perso... *)
Theorem agaga1 {A} : ∀ (a : A) (p : a == a) (α : p == p) (β : p == p),
  α • β == β • α.
Proof.
intros a p α β.
induction p as (b).
bbb.

Definition glop {A} (a : A) p s (αβ : p == s) :=
  (ru a a a p p) ⁻¹ • refl p • αβ.

Theorem q_refl_a_r {A} : ∀ (a : A) p s α β,
  star a a a p (refl a) (refl a) s α β == glop a p s (α • β).
Proof.
intros.
unfold star.
bbb.
unfold glop.
unfold ru.
unfold dotr, dotl; simpl.
unfold hott_2_1_4_i; simpl.
unfold compose; simpl.
unfold id; simpl.
(* pas de la tarte ! *)
bbb.
*)

(* *)

(*
Theorem hott_2_1_6 {A} : ∀ (a : A) (α β : Ω2 a), α • β == β • α.
Proof.
intros a α β.
Check @star.
unfold Ω2 in α, β.
*)

(* hott section 2.2 *)

Definition ap {A B} (f : A → B) x y (p : x == y) :=
  match p in (y1 == y2) return (f y1 == f y2) with
  | refl x => refl (f x)
  end.

Print ap.

Theorem hott_2_2_1 {A B} : ∀ (f : A → B) x, ap f x x (refl x) = refl (f x).
Proof. constructor. Qed.

Theorem hott_2_2_2_i {A B} : ∀ (f : A → B) x y z (p : x == y) (q : y == z),
  ap f x z (p • q) = ap f x y p • ap f y z q.
Proof. induction p, q; constructor. Qed.

Theorem hott_2_2_2_ii {A B} : ∀ (f : A → B) x y (p : x == y),
  ap f y x (p⁻¹) = (ap f x y p)⁻¹.
Proof. induction p; constructor. Qed.

Definition compose_function {A B C} (f : B → C) (g : A → B) x := f (g x).
Notation "f 'o' g" := (compose_function f g) (at level 40).

Theorem hott_2_2_2_iii {A B C} : ∀ (f : A → B) (g : B → C) x y p,
  ap g (f x) (f y) (ap f x y p) = ap (g o f) x y p.
Proof. induction p; constructor. Qed.

Theorem hott_2_2_2_iv {A} : ∀ (x y : A) p, ap id x y p = p.
Proof. induction p; constructor. Qed.

(* hott section 2.3 *)

Definition transport {A} P (x y : A) (p : x == y) :=
  match p in (y1 == y2) return (P y1 → P y2) with
  | refl x => id
  end.

Print transport.

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

