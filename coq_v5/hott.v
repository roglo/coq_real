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
Arguments conjt {A B} _ _.

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
Definition dotr {A} {a b c : A} {p q : a == b}
  (α : p == q) (r : b == c) : (p • r == q • r).
Proof.
induction r as (b).
pose proof (@hott_2_1_4_i A a b p) as (H1, H2).
apply invert in H1.
eapply compose; [ apply H1 | idtac ].
pose proof (@hott_2_1_4_i A a b q) as (H3, H4).
eapply compose; [ apply α | apply H3 ].
Defined.

Notation "α '•r' r" := (dotr α r) (at level 50).

(* whiskering *)
Definition dotl {A} {a b c : A} {r s : b == c}
  (q : a == b) (β : r == s) : (q • r == q • s).
Proof.
induction q as (b).
pose proof (@hott_2_1_4_i A b c r) as (H1, H2).
apply invert in H2.
eapply compose; [ apply H2 | idtac ].
pose proof (@hott_2_1_4_i A b c s) as (H3, H4).
eapply compose; [ apply β | apply H4 ].
Defined.

Notation "q '•l' β" := (dotl q β) (at level 50).

Definition ru {A} {a b : A} (p : a == b) :=
  match hott_2_1_4_i p with
  | conjt x _ => x
  end.

Check @ru.
(* ru
     : ∀ (A : Type) (a b : A) (p : a == b) → p == p • refl b *)

Theorem dotr_rupq {A} {a b : A} : ∀ (p q : a == b) α,
  α •r refl b == (ru p)⁻¹ • α • (ru q).
Proof.
intros.
induction p as (b), α as (p); simpl.
unfold ru; simpl.
destruct (hott_2_1_4_i p) as (α, β); simpl.
unfold id; simpl.
apply dotr, ru.
Qed.

Definition lu {A} {b c : A} (r : b == c) :=
  match hott_2_1_4_i r with
  | conjt _ x => x
  end.

Check @lu.
(* lu
     : ∀ (A : Type) (b c : A) (r : b == c), r == refl b • r *)

Theorem dotl_lurs {A} {b c : A} : ∀ (r s : b == c) β,
  refl b •l β == (lu r)⁻¹ • β • (lu s).
Proof.
intros.
induction r as (b), β as (r); simpl.
unfold lu; simpl.
destruct (hott_2_1_4_i r) as (α, β); simpl.
unfold id; simpl.
apply dotr, ru.
Qed.

Definition star {A} {a b c : A} {p q : a == b} {r s : b == c} α β
  : p • r == q • s
  := (α •r r) • (q •l β).

Notation "α ★ β" := (star α β) (at level 40).

Theorem star_dot {A} {a : A} : ∀ (α β : refl a == refl a), α ★ β == α • β.
Proof.
intros.
unfold "★"; simpl; unfold id.
eapply compose; [ apply hott_2_1_4_iv | idtac ].
remember (α • refl (refl a) • β) as p.
pose proof @hott_2_1_4_i (a == a) (refl a) (refl a) p as H.
destruct H as (γ, δ); eapply invert.
eapply compose; [ idtac | eassumption ].
subst; apply dotr, ru.
Qed.

Definition star' {A} {a b c : A} {p q : a == b} {r s : b == c} α β
  : p • r == q • s
  := (p •l β) • (α •r s).

Notation "α ★' β" := (star' α β) (at level 40).

Theorem star'_dot {A} {a : A} : ∀ (α β : refl a == refl a), α ★' β == β • α.
Proof.
intros.
unfold "★'"; simpl; unfold id.
eapply compose; [ apply hott_2_1_4_iv | idtac ].
remember (β • refl (refl a) • α) as p.
pose proof @hott_2_1_4_i (a == a) (refl a) (refl a) p as H.
destruct H as (γ, δ); eapply invert.
eapply compose; [ idtac | eassumption ].
subst; apply dotr, ru.
Qed.

Theorem gen_star_star' {A} {a b c : A} {p q : a == b} {r s : b == c} : ∀ α β,
  @star A a b c p q r s α β == @star' A a b c p q r s α β.
Proof.
intros.
induction α as (p).
induction β as (r).
induction p, r.
unfold "★", "★'"; simpl.
constructor.
Qed.

Check @compose.

Theorem eckmann_hilton {A} {a : A} : ∀ α β : refl a == refl a,
  @compose (a == a) (refl a) (refl a) (refl a) α β ==
  @compose (a == a) (refl a) (refl a) (refl a) β α.
Proof.
intros.
eapply compose; [ eapply invert, star_dot | idtac ].
eapply compose; [ idtac | apply star'_dot ].
induction α as (p).
induction β as (q).
induction i as (b).
induction p as (c).

Theorem aaa : ∀ A (c : A) (q : @Id A c c),
   @Id (@Id (@Id A c c) (@compose A c c c q q) (@compose A c c c q q))
     (@star A c c c q q q q (@refl (@Id A c c) q) (@refl (@Id A c c) q))
     (@star' A c c c q q q q (@refl (@Id A c c) q) (@refl (@Id A c c) q)).
Proof.
intros.
Abort. (* bon, ça marche pas, faut voir...
induction q.

(*
Toplevel input, characters 0-11:
Error: Abstracting over the terms "c0", "c0" and "q" leads to a term
"λ (c0 c1 : A) (q : c0 == c1), refl q ★ refl q == refl q ★' refl q"
which is ill-typed.
*)

bbb.

Theorem eckmann_hilton {A} {a : A} : ∀ (α β : refl a == refl a),
  α • β == β • α.
Proof.
intros.
eapply compose; [ eapply invert, star_dot | idtac ].
eapply compose; [ idtac | apply star'_dot ].
apply star_star'.
Qed.

Check @eckmann_hilton.

bbb.
*)

(* *)

(* hott section 2.2 *)

Definition ap {A B} (f : A → B) {x y} (p : x == y) :=
  match p in (y1 == y2) return (f y1 == f y2) with
  | refl x => refl (f x)
  end.

Print ap.

Theorem hott_2_2_1 {A B} : ∀ (f : A → B) x, ap f (refl x) = refl (f x).
Proof. constructor. Qed.

Theorem hott_2_2_2_i {A B} : ∀ (f : A → B) x y z (p : x == y) (q : y == z),
  ap f (p • q) = ap f (*x y*) p • ap f (*y z*) q.
Proof. induction p, q; constructor. Qed.

Theorem hott_2_2_2_ii {A B} : ∀ (f : A → B) x y (p : x == y),
  ap f (p⁻¹) = (ap f p)⁻¹.
Proof. induction p; constructor. Qed.

Definition compose_function {A B C} (f : B → C) (g : A → B) x := f (g x).
Notation "f 'o' g" := (compose_function f g) (at level 40).

Theorem hott_2_2_2_iii {A B C} : ∀ (f : A → B) (g : B → C) (x y : A) p,
  ap g (@ap A B f x y p) = ap (g o f) p.
Proof. induction p; constructor. Qed.

Theorem hott_2_2_2_iv {A} : ∀ (x y : A) p, @ap A A id x y p = p.
Proof. induction p; constructor. Qed.

(* hott section 2.3 *)

(* p* = transport P p *)
Definition transport {A} P {x y : A} (p : x == y) : P x → P y :=
  match p in (y1 == y2) return (P y1 → P y2) with
  | refl x => id
  end.

Check @transport.
(* transport =
     : ∀ (A : Type) (P : A → Type) (x y : A), x == y → P x → P y *)

(* lemma 2.3.2 *)

(* moi pas comprendre..
Definition lift {A P} {x y : A} (u : P x) (p : x == y)
  : (x, u) == (y, @transport A P x y p u).

Toplevel input, characters 69-96:
Error: In environment
A : Type
P : A → Type
x : A
y : A
u : P x
p : x == y
The term "(y, transport p u)" has type "(A * P y)%type"
 while it is expected to have type "(A * P x)%type".
*)

(* lemma 2.3.4 *)
Lemma dependent_map {A P} : ∀ (f : ∀ (x : A), P x),
  ∀ x y (p : x == y), transport P p (f x) == f y.
Proof. induction p; constructor. Qed.

Definition dependent_map_proof_term {A P} f (x y : A) (p : x == y) :=
  match p in (y1 == y2) return (transport P p (f y1) == f y2) with
  | refl x => refl (f x)
  end.

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

