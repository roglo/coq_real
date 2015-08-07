(* experimentations on HoTT *)
(* requires coq 8.5 *)

Require Import Utf8 QArith.
Require Import NPeano.
Notation "⊥" := False.

Open Scope nat_scope.

(* hott section 1.12 *)

Inductive Id {A} x : A → Type :=
  | refl : Id x x.

Notation "x == y" := (Id x y) (at level 70).
Notation "x ≠≠ y" := (¬Id x y) (at level 70).

Definition indiscernability {A} C (x y : A) (p : x == y) :=
  match p return (C x → C _) with
  | refl _ => id
  end.

Check @indiscernability.
(* indiscernability
     : ∀ (A : Type) (C : A → Type) (x y : A), x == y → C x → C y *)

Theorem indiscernability_prop : ∀ A C (x : A),
  indiscernability C x x (refl x) = id.
Proof. reflexivity. Qed.

(* hott section 1.12.1 *)

Theorem path_induction0 : ∀ A C c,
  ∃ (f : ∀ (x y : A) (p : x == y), C x y p),
  ∀ x, f x x (refl x) = c x.
Proof.
intros A C c.
exists
  (λ a _ p,
   match p return (C _ _ p) with
   | refl _ => c a
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
   | refl _ => λ _, id
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

(* hott chapter 1 exercises *)

(* Exercise 1.1. Given functions f : A → B and g : B → C, define their
  composite g o f : A → C.
    Show that we have h o (g o f ) ≡ (h o g) o f. *)

Definition composite {A B C} (f : A → B) (g : B → C) x := g (f x).
Notation "g '◦' f" := (composite f g) (at level 40).
(* composite : ∀ A B C : Type, (A → B) → (B → C) → A → C *)

Theorem composite_assoc {A B C D} : ∀ (f : A → B) (g : B → C) (h : C → D),
  h ◦ (g ◦ f) = (h ◦ g) ◦ f.
Proof. reflexivity. Qed.

(* Exercise 1.2. Derive the recursion principle for products rec_{AxB}
   using only the projections, and verify that the definitional
   equalities are valid. Do the same for Σ-types. *)

Definition AxB_pr₁ {A B} (x : A * B) := match x with (a, _) => a end.
Definition AxB_pr₂ {A B} (x : A * B) := match x with (_, b) => b end.

Definition rec_AxB {A B C} (g : A → B → C) x := g (AxB_pr₁ x) (AxB_pr₂ x).

Theorem verif_rec_AxB_eq_def : ∀ A B C (g : A → B → C) a b,
  rec_AxB g (a, b) = g a b.
Proof. reflexivity. Qed.

Definition Σ_pr₁ {A B} (x : { y : A & B y }) : A :=
  match x with existT _ a _ => a end.
Definition Σ_pr₂ {A B} (x : { y : A & B y }) : B (Σ_pr₁ x) :=
  match x with existT _ _ b => b end.

Definition rec_Σ {A B C} (g : ∀ x : A, B x → C) x := g (Σ_pr₁ x) (Σ_pr₂ x).

Theorem verif_rec_Σ_eq_def : ∀ A B C (g : ∀ x : A, B x → C) a b,
  rec_Σ g (existT B a b) = g a b.
Proof. reflexivity. Qed.

(* Exercise 1.3. Derive the induction principle for products ind_{AxB},
   using only the projections and the propositional uniqueness principle
   uppt. Verify that the definitional equalities are valid. Generalize
   uppt to Σ-types, and do the same for Σ-types. (This requires concepts
   from Chapter 2.) *)

Definition uupt {A B} (x : A * B) :=
  let (a, b) return ((AxB_pr₁ x, AxB_pr₂ x) == x) := x in
  refl (a, b).

Definition ind_AxB {A B} C (g : ∀ x y, C (x, y)) (x : A * B) :=
  match uupt x return (C _ → C _) with
  | refl _ => id
  end (g (AxB_pr₁ x) (AxB_pr₂ x)).

Theorem verif_ind_AxB_eq_def : ∀ A B C (g : ∀ x y, C (x, y)) (a : A) (b : B),
  ind_AxB C g (a, b) = g a b.
Proof. reflexivity. Qed.

Definition Σ_uupt {A B} (x : {y : A & B y}) :=
 let (a, b) return (existT _ (Σ_pr₁ x) (Σ_pr₂ x) == x) := x in
 refl (existT _ a b).

Definition ind_Σ {A B} C (g : ∀ a (b : B a), C (existT _ a b))
    (x : {y : A & B y}) :=
  match Σ_uupt x with
  | refl _ => id
  end (g (Σ_pr₁ x) (Σ_pr₂ x)).

Theorem verif_ind_Σ_eq_def : ∀ A B C g (a : A) (b : B),
  ind_Σ C g (existT _ a b) = g a b.
Proof. reflexivity. Qed.

(* Exercise 1.4. Assuming as given only the 'iterator' for natural numbers
         iter : Π (C : U) C → (C → C) → ℕ → C
   with the defining equations
             iter(C, c₀, cs, 0) :≡ c₀,
       iter(C, c₀, cs, succ(n)) :≡ cs(iter(C, c₀, cs, n)),

   derive a function having the type of the recursor rec_ℕ. Show that
   the defining equations of the recursor hold propositionally for this
   function, using the induction principle for ℕ. *)

Fixpoint iter {C} c₀ (cs : C → C) m :=
  match m with
  | 0 => c₀
  | S n => cs (iter c₀ cs n)
  end.

(* iter : ∀ C : Type, C → (C → C) → nat → C *)

(* iter C c₀ cs n ≡ cs (cs (cs (cs … (cs c₀)))) with 'n' cs *)
(* rec_ℕ C c₀ cs n ≡ cs n (cs (n-1) (cs (n-2) … (cs 0 c₀))) with 'n' cs *)

Definition iter_f {A B} (cs : _ → _ → B) (r : nat * A) :=
  (S (fst r), cs (fst r) (snd r)).

Definition rec_ℕ' {C} (c₀ : C) (cs : nat → C → C) (n : nat) :=
  snd (iter (0, c₀) (iter_f cs) n).

Eval compute in rec_ℕ' nil (λ n l, cons n (cons 7 l)) 5.

Theorem rec_ℕ_0 : ∀ C (c₀ : C) cs, rec_ℕ' c₀ cs 0 = c₀.
Proof. reflexivity. Qed.

Theorem rec_ℕ_succ : ∀ C (c₀ : C) cs n,
  rec_ℕ' c₀ cs (S n) = cs n (rec_ℕ' c₀ cs n).
Proof.
intros.
unfold rec_ℕ'; simpl; f_equal.
induction n; [ reflexivity | simpl ].
rewrite IHn; reflexivity.
Qed.

(* Exercise 1.5. Show that if we define A + B :≡ Σ (x:2) rec₂(U,A,B,x),
   then we can give a definition of ind_A+B for which the definitional
   equalities stated in §1.7 hold. *)

Notation "'Σ' ( x : A ) , B" :=
  ({ x : A & B }) (at level 0, x at level 0, B at level 100, only parsing).
Notation "'Π' ( x : A ) , B" :=
  (∀ x : A, B) (at level 0, x at level 0, B at level 100, only parsing).
Definition U := Type.

Definition rec₂ C (c₀ c₁ : C) (b : bool) := if b then c₀ else c₁.

Inspect 1.

Definition ApB A B := Σ (x : bool), rec₂ U A B x.

Definition ApB_inl (A B : U) (a : A) := existT (rec₂ U A B) true a.
Definition ApB_inr (A B : U) (b : B) := existT (rec₂ U A B) false b.

(* definition by tactics *)
Definition ind_ApB_1 {A B : U} :
  Π (C : ApB A B → U),
    (Π  (a : A), C (ApB_inl A B a)) →
    (Π  (b : B), C (ApB_inr A B b)) →
    Π (x : ApB A B), C x.
Proof.
intros C HA HB x.
induction x as (b, x).
destruct b; [ apply HA | apply HB ].
Qed.

Check ind_ApB_1.

(* same definition, by value *)
Definition ind_ApB_2 {A B : U} (C : Π (_ : ApB A B), U)
    (HA : Π (a : A), C (ApB_inl A B a))
    (HB : Π (b : B), C (ApB_inr A B b))
    (x : ApB A B) :=
  let (v, u) as s return (C s) := x in
  (if v return Π (z : _), C (existT _ v z) then HA else HB) u.

Check @ind_ApB_1.
(* ind_ApB_1
     : Π (A : U),
       Π (B : U),
       Π (C : Π (_ : ApB A B), U),
       Π (_ : Π (a : A), C (ApB_inl A B a)),
       Π (_ : Π (b : B), C (ApB_inr A B b)), Π (x : ApB A B), C x *)
Check @ind_ApB_2.
(* ind_ApB_2
     : Π (A : U),
       Π (B : U),
       Π (C : Π (_ : ApB A B), U),
       Π (_ : Π (a : A), C (ApB_inl A B a)),
       Π (_ : Π (b : B), C (ApB_inr A B b)), Π (x : ApB A B), C x *)

(* Exercise 1.6. Show that if we define AxB :≡ Π (x:2) rec₂(U,A,B,x),
   then we can give a definition of ind_AxB for which the definitional
   equalities stated in §1.5 hold propositionally (i.e. using equality
   types). (This requires the function extensionality axiom, which is
   introduced in §2.9.) *)

Definition AxB' A B := Π (x : bool), rec₂ U A B x.

Definition AxB'_pair {A B} (a : A) (b : B) : AxB' A B :=
  λ x,
  match x return if x then A else B with
  | true => a
  | false => b
  end.

Definition AxB'_pr₁ {A B} (x : AxB' A B) : A := x true.
Definition AxB'_pr₂ {A B} (x : AxB' A B) : B := x false.

Axiom function_extensionality : ∀ A B (f g : ∀ x : A, B x),
  (∀ x, f x == g x) → f == g.

Theorem AxB'_pair_proj {A B} : ∀ x : AxB' A B,
  AxB'_pair (AxB'_pr₁ x) (AxB'_pr₂ x) == x.
Proof.
intros x.
apply function_extensionality.
intros b.
destruct b; reflexivity.
Qed.

(* definition by tactics *)
Definition ind_AxB'_1 {A B : U} :
  Π (C : AxB' A B → U),
    (Π  (x : A), Π  (y : B), C (AxB'_pair x y))
    →  Π (x : AxB' A B), C x.
Proof.
intros C H x.
pose proof AxB'_pair_proj x as Hx.
rewrite <- Hx; apply H.
Qed.

(* same definition, by value *)
Definition ind_AxB'_2 {A B : U} C
     (H : Π (x : A), Π (y : B), C (AxB'_pair x y)) x :=
  match AxB'_pair_proj x in (_ == y) return (C y) with
  | refl _ => H (AxB'_pr₁ x) (AxB'_pr₂ x)
  end.

(* ind_AxB'_1
     : Π (A : U),
       Π (B : U),
       Π (C : Π (_ : AxB' A B), U),
       Π (_ : Π (x : A), Π (y : B), C (AxB'_pair x y)), Π (x : AxB' A B), C x
*)
(* ind_AxB'_2
     : Π (A : U),
       Π (B : U),
       Π (C : Π (_ : AxB' A B), Type),
       Π (_ : Π (x : A), Π (y : B), C (AxB'_pair x y)), Π (x : AxB' A B), C x
*)

(* Exercise 1.7. Give an alternative derivation of ind'_=A from ind_=A
   which avoids the use of universes. (This is easiest using concepts
   from later chapters.) *)

(* definition from §1.12.1 *)
Definition ind_eqA {A} :
  Π (C : Π (x : A), Π (y : A), (x == y) → U),
    (Π (x : A), C x x (refl x))
    → Π (x : A), Π (y : A), Π (p : x == y), C x y p
  := λ C c x y p,
     match p with
     | refl _ => c x
     end.

Theorem ind_eqA_def_eq {A} : ∀ C c (x : A), ind_eqA C c x x (refl x) = c x.
Proof. reflexivity. Qed.

(* definition from §1.12.1 *)
Definition ind'_eqA {A} :
  Π (a : A),
  Π (C : Π (x : A), (a == x) → U), C a (refl a)
  → Π (x : A), Π (p : a == x), C x p
  := λ a C P x p,
     match p with
     | refl _ => λ _ y, y
     end C P.

Theorem ind'_eqA_def_eq {A} : ∀ (a : A) C c, ind'_eqA a C c a (refl a) = c.
Proof. reflexivity. Qed.

(* alternative definition from ind_eqA *)
Definition ind'_eqA_bis {A} :
  Π (a : A),
  Π (C : Π (x : A), (a == x) → U), C a (refl a)
  → Π (x : A), Π (p : a == x), C x p.
Proof.
Abort. (* not obvious, see that later *)

(* exercise abandoned... *)

(* Exercise 1.8. Define multiplication and exponentiation using rec_ℕ.
   Verify that (ℕ, +, 0, ×, 1) is a semiring using only ind_ℕ. You will
   probably also need to use symmetry and transitivity of equality,
   Lemmas 2.1.1 and 2.1.2. *)

(* doing more: playing with hypeoperations... *)
Definition ℕ_add x := rec_ℕ' x (λ _, S).
Definition ℕ_mul x := rec_ℕ' 0 (λ _, ℕ_add x).
Definition ℕ_exp x := rec_ℕ' 1 (λ _, ℕ_mul x).
Definition ℕ_tet x := rec_ℕ' 1 (λ _, ℕ_exp x).
Definition ℕ_pen x := rec_ℕ' 1 (λ _, ℕ_tet x).

Eval vm_compute in (ℕ_add 3 7).
Eval vm_compute in (ℕ_mul 3 7).
Eval vm_compute in (ℕ_exp 2 9).
Eval vm_compute in (ℕ_tet 2 3).

Fixpoint ind_ℕ (C : nat → U) P0 Pn n :=
  match n return C n with
  | 0 => P0
  | S n' => Pn n' (ind_ℕ C P0 Pn n')
  end.

Theorem ℕ_add_comm : ∀ x y, ℕ_add x y = ℕ_add y x.
Proof.
intros.
revert y.
apply ind_ℕ with (n := x).
 intros y.
 apply ind_ℕ with (n := y); [ reflexivity | idtac ].
 clear x y; intros x y.
 unfold ℕ_add; simpl.
 unfold rec_ℕ'; simpl; f_equal.
 assumption.

 clear x; intros x IHx y.
 unfold ℕ_add; simpl.
 unfold rec_ℕ'; simpl; f_equal.
 unfold ℕ_add in IHx.
 unfold rec_ℕ' in IHx; rewrite <- IHx.
 apply ind_ℕ with (n := y); [ reflexivity | simpl ].
 clear y; intros y IHy; f_equal.
 apply IHy.
Qed.

Definition pair_succ r := (S (fst r), S (snd r)).

Definition ℕ_add_comm_2 x y :=
  ind_ℕ _
    (ind_ℕ _ eq_refl
       (λ x (H : ℕ_add 0 x = ℕ_add x 0),
        eq_trans
          (f_equal (λ f, f (snd (iter (0, 0) pair_succ x))) eq_refl)
          (f_equal S H)))
    (λ x0 IHx y0,
     eq_ind
       (snd (iter (0, x0) pair_succ y0))
       (λ n, snd (iter (0, S x0) pair_succ y0) = S n)
       (ind_ℕ
          (λ y1,
           snd (iter (0, S x0) pair_succ y1) =
           S (snd (iter (0, x0) pair_succ y1)))
          eq_refl
          (λ y1 IHy,
           eq_trans
             (f_equal (λ f, f (snd (iter (0, S x0) pair_succ y1))) eq_refl)
             (f_equal S IHy))
           y0)
       (snd (iter (0, y0) pair_succ x0)) (IHx y0))
    x y.

Check ℕ_add_comm_2.

(* bon, mais après ça, j'arrête cet exo paskeu j'ai déjà fait des
   preuves de ce genre, c'est long et casse-couilles *)

(* Exercise 1.9. Define the type family Fin : ℕ → U mentioned at the
   end of §1.3, and the dependent function fmax: Π (n : ℕ) Fin(n + 1)
   mentioned in §1.4. *)

Inductive Fin n := elem : ∀ i, i < n → Fin n.
Definition fmax n := elem (n + 1) n (Nat.lt_add_pos_r 1 n Nat.lt_0_1).

Check fmax.
(* fmax
     : ∀ n : nat, Fin (n + 1) *)

(* Exercise 1.10. Show that the Ackermann function ack : ℕ → ℕ → ℕ
   is definable using only rec_ℕ satisfying the following equations:
                 ack(0,n) ≡ succ(n),
           ack(succ(m),0) ≡ ack(m,1),
      ack(succ(m),succ(n) ≡ ack(m,ack(succ(m),n)). *)

Fixpoint rec_ℕ {C} (c₀ : C) cs n :=
  match n with
  | 0 => c₀
  | S n' => cs n (rec_ℕ c₀ cs n')
  end.

Fixpoint ack m n :=
  match m with
  | 0 => S n
  | S m' => rec_ℕ (ack m' 1) (λ n r, ack m' r) n
  end.

(* not sure it is what is required since a Fixpoint is used even so
   and two recursive calls but I don't know how to do it without
   Fixpoint at all (i.e. using Definition) and only rec_ℕ (perhaps
   two rec_ℕs, one for m and one for n). However this rec_ℕ is
   mandatory, otherwise Coq would not accept a recursive call with
   (S m) in"ack (S m) n": what means that the simple definition of
   ack with Fixpoint and recursive calls cannot be written in Coq *)

Theorem ack_0 : ∀ n, ack 0 n = S n.
Proof. reflexivity. Qed.

Theorem ack_succ_0 : ∀ m, ack (S m) 0 = ack m 1.
Proof. reflexivity. Qed.

Theorem ack_succ_succ : ∀ m n, ack (S m) (S n) = ack m (ack (S m) n).
Proof. reflexivity. Qed.

(* Exercise 1.11. Show that for any type A, we have ¬¬¬A → ¬A *)

(* solution with tactics *)
Theorem not_not_not_1 : ∀ A, ¬¬¬A → ¬A.
Proof.
intros A Hnnn a.
apply Hnnn; intros HnA.
apply HnA; assumption.
Qed.

(* solution with proof term *)
Definition not_not_not_2 A (Hnnn : ¬¬¬A) : ¬A := λ a, Hnnn (λ HnA, HnA a).

Check not_not_not_1.
Check not_not_not_2.

(* this was on Prop; solutions on Types: *)

(* with tactics *)
Theorem not_not_not_3 : ∀ A, notT (notT (notT A)) → notT A.
Proof.
intros A Hnnn a.
apply Hnnn; intros HnA.
apply HnA; assumption.
Qed.

(* with proof term *)
Definition not_not_not_4 A (Hnnn : notT (notT (notT A))) : notT A :=
  λ a, Hnnn (λ HnA, HnA a).

Check not_not_not_3.
Check not_not_not_4.

(* Exercise 1.12. Using the propositions as types interpretation,
   derive the following tautologies.
     (i) If A, then (if B then A).
    (ii) If A, then not (not A).
   (iii) If (not A or not B), then not (A and B). *)

Inductive andT A B := conjT : A → B → andT A B.
Inductive orT A B :=
  | orT_introl : A → orT A B
  | orT_intror : B → orT A B.

Definition hott_ex_1_12_i : ∀ A B, A → B → A := λ A B HA HB, HA.
Definition hott_ex_1_12_ii : ∀ A, A → notT (notT A) := λ A HA HnA, HnA HA.
Definition hott_ex_1_12_iii : ∀ A B, orT (notT A) (notT B) → notT (andT A B) :=
  λ A B Hor Hand,
  match Hor with
  | orT_introl _ _ Hna => Hna (andT_rect A B (λ _, A) (λ a _, a) Hand)
  | orT_intror _ _ Hnb => Hnb (andT_rect A B (λ _, B) (λ _ b, b) Hand)
  end.

(* Exercise 1.13. Using propositions-as-types, derive the double negation
   of the principle of excluded middle, i.e. prove not (not (P or not P)). *)

Definition hott_ex_1_13 : (∀ P, orT P (notT P))
    → ∀ P, notT (notT (orT P (notT P)))
  := λ Hem P Hno, Hno (Hem P).

(* Exercise 1.14. Why do the induction principles for identity types
   not allow us to construct a function f : Π (x:A) Π (p:x=x) (p=refl x)
   with the defining equation
          f(x,refl_x) :≡ refl_{refl_x}    ? *)

(* Wrong explanation: I suppose it is because if there is y such that
   x = y, then there is another proof that x = x, because x = y
   implies y = x by symmetry and x = x, by transitivity, which creates
   another proof that x = x, ...
   ... which is different from refl <- no, it is equal! *)

(* not sure *)

(* à voir... *)

(* Exercise 1.15. Show that indiscernability of identicals follows
   from path induction. *)

Definition path_induction {A} (C : Π (x : A), Π (y : A), Π (p : x == y), U)
    (c : Π (x : A), C x x (refl x)) (x y : A) (p : x == y) : C x y p :=
  match p return (C _ _ p) with
  | refl _ => c x
  end.

Theorem path_induction_def : ∀ A (x : A) C c,
  path_induction C c x x (refl x) = c x.
Proof. reflexivity. Qed.

Theorem path_induction_indiscernability {A} :
  Π (C : A → U), Π (x : A), Π (y : A), x == y → C x → C y.
Proof.
intros C x y p px.
apply (path_induction (λ x y _, C x → C y) (λ _, id) x y p).
assumption.
Qed.

(* Chapter 2 *)

(* hott section 2.1 *)

Definition invert {A} {x y : A} (p : x == y) : y == x :=
  match p with
  | refl _ => refl x
  end.
Notation "p '⁻¹'" := (invert p)
  (at level 8, left associativity, format "'[v' p ']' ⁻¹").

Lemma hott_2_1_1 : ∀ A (x : A), refl x = (refl x)⁻¹.
Proof. reflexivity. Qed.

Definition compose {A} {x y z : A} (p : x == y) : y == z → x == z :=
  match p with
  | refl _ => id
  end.
Notation "p • q" := (compose p q) (at level 40, left associativity).

(* same theorem with another proof *)
Definition compose2 {A} {x y z : A} (p : x == y) : y == z → x == z :=
  λ q,
  match p with
  | refl _ =>
      match q in (_ == t) return (x == t) with
      | refl _ => p
      end
 end.

(* proof that the proofs are equal *)
Definition compose_compose2 {A} {x y z : A} : ∀ (p : x == y) (q : y == z),
    compose p q = compose2 p q :=
  λ p q,
  match q return (p • q = compose2 p q) with
  | refl _ =>
      match p return (p • refl _ = compose2 p (refl _)) with
      | refl _ => eq_refl
      end
  end.

Theorem fold_compose : ∀ A (x y z : A) p,
   match p with
   | refl _ => id
   end = @compose A x y z p.
Proof. reflexivity. Qed.

Lemma hott_2_1_2 : ∀ A (x : A), refl x = refl x • refl x.
Proof. reflexivity. Qed.

Inductive andt (A B : Type) : Type := conjt : A → B → andt A B.
Notation "u '∧∧' v" := (andt u v) (at level 80, right associativity).
Arguments conjt {A B} _ _.

Definition hott_2_1_4_i_1 {A} {x y : A} : ∀ (p : x == y),
    p == p • refl y
 := (λ (p : x == y),
     match p return (p == p • refl _) with
     | refl _ => refl (refl x • refl x)
     end).

Definition hott_2_1_4_i_2 {A} {x y : A} : ∀ (p : x == y),
    p == refl x • p
 := (λ (p : x == y),
   match p return (p == refl _ • p) with
   | refl _ => refl (refl x • refl x)
   end).

(* Lemma hott_2.1.4 ii_1 *)

Lemma invert_compose {A} {x y : A} : ∀ (p : x == y), p⁻¹ • p == refl y.
Proof.
intros p; destruct p; reflexivity.
Qed.

(* Lemma 2.1.4 ii_2 *)

Lemma compose_invert {A} {x y : A} : ∀ (p : x == y), p • p⁻¹ == refl x.
Proof.
intros p; destruct p; reflexivity.
Qed.

Lemma hott_2_1_4_iii {A} {x y : A} : ∀ (p : x == y), (p⁻¹)⁻¹ == p.
Proof.
intros p; destruct p; reflexivity.
Qed.

(* Lemma hott_2_1_4_iv *)

Lemma compose_assoc {A} {x y z w : A} :
  ∀ (p : x == y) (q : y == z) (r : z == w),
  p • (q • r) == (p • q) • r.
Proof.
intros p q r; destruct p; reflexivity.
Qed.

Definition hott_2_1_4 A (x y z w : A)
    (p : x == y) (q : y == z) (r : z == w) :=
  ((@hott_2_1_4_i_1 A x y p, @hott_2_1_4_i_2 A x y p),
   (@compose_invert A x y p, @invert_compose A x y p),
   @hott_2_1_4_iii A x y p,
   @compose_assoc A x y z w p q r).

(* Theorem 2.1.6 (Eckmann-Hilton) *)

Definition Ω {A} (a : A) := (a == a).
Definition Ω2 {A} (a : A) := (refl a == refl a).

(* whiskering *)
Definition dotr {A} {a b c : A} {p q : a == b}
  (α : p == q) (r : b == c) : (p • r == q • r).
Proof.
destruct r.
pose proof (@hott_2_1_4_i_1 A a b p) as H1.
apply invert in H1.
eapply compose; [ apply H1 | idtac ].
pose proof (@hott_2_1_4_i_1 A a b q) as H3.
eapply compose; [ apply α | apply H3 ].
Defined.

Notation "α '•r' r" := (dotr α r) (at level 50).

(* whiskering *)
Definition dotl {A} {a b c : A} {r s : b == c}
  (q : a == b) (β : r == s) : (q • r == q • s).
Proof.
destruct q.
pose proof (@hott_2_1_4_i_2 A a c r) as H2.
apply invert in H2.
eapply compose; [ apply H2 | idtac ].
pose proof (@hott_2_1_4_i_2 A a c s) as H4.
eapply compose; [ apply β | apply H4 ].
Defined.

Notation "q '•l' β" := (dotl q β) (at level 50).

Definition ru {A} {a b : A} (p : a == b) : p == p • refl b :=
  hott_2_1_4_i_1 p.

Check @ru.
(* ru
     : ∀ (A : Type) (a b : A) (p : a == b) → p == p • refl b *)

Theorem dotr_rupq {A} {a b : A} : ∀ (p q : a == b) α,
  α •r refl b == (ru p)⁻¹ • α • (ru q).
Proof.
intros.
destruct p, α; simpl.
reflexivity.
Qed.

Definition lu {A} {b c : A} (r : b == c) : r == refl b • r :=
  hott_2_1_4_i_2 r.

Check @lu.
(* lu
     : ∀ (A : Type) (b c : A) (r : b == c), r == refl b • r *)

Theorem dotl_lurs {A} {b c : A} : ∀ (r s : b == c) β,
  refl b •l β == (lu r)⁻¹ • β • (lu s).
Proof.
intros.
destruct r, β; simpl.
reflexivity.
Qed.

Definition star {A} {a b c : A} {p q : a == b} {r s : b == c} α β
  : p • r == q • s
  := (α •r r) • (q •l β).

Notation "α ★ β" := (star α β) (at level 40).

Theorem star_dot {A} {a : A} : ∀ (α β : refl a == refl a), α ★ β == α • β.
Proof.
intros.
unfold "★"; simpl; unfold id.
eapply compose; [ apply compose_assoc | idtac ].
remember (α • refl (refl a) • β) as p.
pose proof @hott_2_1_4_i_1 (a == a) (refl a) (refl a) p as H.
eapply invert.
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
eapply compose; [ apply compose_assoc | idtac ].
remember (β • refl (refl a) • α) as p.
pose proof @hott_2_1_4_i_1 (a == a) (refl a) (refl a) p as H.
eapply invert.
eapply compose; [ idtac | eassumption ].
subst; apply dotr, ru.
Qed.

Theorem gen_star_star' {A} {a b c : A} {p q : a == b} {r s : b == c} : ∀ α β,
  @star A a b c p q r s α β == @star' A a b c p q r s α β.
Proof.
intros.
destruct α as (p).
destruct β as (r).
destruct p, r.
unfold "★", "★'"; simpl.
constructor.
Qed.

Theorem star_star' {A} {a : A} : ∀ (α β : refl a == refl a),
  star α β == star' α β.
Proof. apply gen_star_star'. Qed.

Theorem eckmann_hilton {A} {a : A} : ∀ (α β : refl a == refl a),
  α • β == β • α.
Proof.
intros.
eapply compose; [ eapply invert, star_dot | idtac ].
eapply compose; [ idtac | apply star'_dot ].
apply star_star'.
Qed.

Check @eckmann_hilton.

(* *)

(* hott section 2.2 *)

Definition ap {A B x y} (f : A → B) (p : x == y) : f x == f y :=
  match p with
  | refl _ => refl (f x)
  end.

Theorem hott_2_2_1 {A B} : ∀ (f : A → B) x, ap f (refl x) = refl (f x).
Proof. constructor. Qed.

(* Lemma 2.2.2 i *)

Theorem ap_compose {A B} : ∀ (f : A → B) x y z (p : x == y) (q : y == z),
  ap f (p • q) = ap f p • ap f q.
Proof. destruct p, q; constructor. Qed.

Theorem hott_2_2_2_ii {A B} : ∀ (f : A → B) x y (p : x == y),
  ap f (p⁻¹) = (ap f p)⁻¹.
Proof. destruct p; constructor. Qed.

(* Lemma 2.2.2 iii *)

Definition ap_composite {A B C x y}
  : ∀ (f : A → B) (g : B → C) (p : x == y),
    ap g (ap f p) == ap (g ◦ f) p
  := λ f g p,
     match p with refl _ => refl (ap g (ap f (refl x))) end.

Definition hott_2_2_2_iv {A} {x y : A} : ∀ (p : x == y), ap id p == p
  := λ p, match p with refl _ => refl (refl x) end.

(* hott section 2.3 *)

(* p* = transport P p *)
Definition transport {A} P {x y : A} (p : x == y) : P x → P y :=
  match p with
  | refl _ => id
  end.

Check @transport.
(* transport =
     : ∀ (A : Type) (P : A → Type) (x y : A), x == y → P x → P y *)

Notation "p '⁎'" := (transport _ p)
  (at level 8, left associativity, format "'[v' p ']' ⁎", only parsing).

(* lemma 2.3.2 path lifting property *)

Definition lift {A P} {x y : A} (u : P x) (p : x == y)
  : existT _ x u == existT _ y (transport P _ u)
  := match p with
     | refl _ => refl (existT P x (transport P (refl x) u))
     end.

Check @lift.

(* lift
     : ∀ (A : Type) (P : A → Type) (x y : A) (u : P x) (p : x == y),
       existT x u == existT y (transport P p u) *)

Check projT1.
(* projT1
     : ∀ (A : Type) (P : A → Type), sigT P → A *)

Check @ap.
(* ap
     : ∀ (A B : Type) (f : A → B) (x y : A), x == y → f x == f y *)

(*
Mystery in hott book:

Lemma path_lifting_property : ∀ A P (x y : A) (u : P x) (p : x == y),
  @projT1 A P (lift u p) == p.

Toplevel input, characters 103-111:
Error: In environment
A : Type
P : A → Type
x : A
y : A
u : P x
p : x == y
The term "lift u p" has type "existT x u == existT y (transport P p u)"
 while it is expected to have type "sigT ?1330".
*)

(* lemma 2.3.4 *)

Definition apd {A P} f {x y : A} (p : x == y) : transport P p (f x) == f y :=
  match p with
  | refl _ => refl (f x)
  end.

(* lemma hott_2_3_5 *)

Definition transportconst {A : U} {x y : A}
  : ∀ B (P := λ _, B) (p : x == y) (b : B), transport P p b == b
  := λ B (P := λ _, B) p b,
     match p return (transport P p b == b) with
     | refl _ => refl b
     end.

Check @transportconst.
(* transportconst
     : ∀ (A : U) (x y : A) (B : Type) (P:=λ _ : A, B)
       (p : x == y) (b : B), transport P p b == b *)

(* ap
     : ∀ (A B : Type) (f : A → B) (x y : A)
       (p : x == y), f x == f y *)
(* apd
     : ∀ (A : Type) (P : A → Type) (f : ∀ x : A, P x) (x y : A)
       (p : x == y), transport P p (f x) == f y *)

Definition hott_2_3_8 A B (P := λ _ : A, B) (f : A → B) x y (p : x == y)
  : apd f p == transportconst B p (f x) • ap f p
  := match p with refl _ => refl (apd f (refl x)) end.

Definition hott_2_3_9 {A x y z} :
    ∀ (P : A → U) (p : x == y) (q : y == z) (u : P x),
    transport P q (transport P p u) == transport P (p • q) u :=
  λ P p q u,
  match q with
  | refl _ =>
      match p with
      | refl _ => refl (transport P (refl x • refl x) u)
      end
  end.

Definition hott_2_3_10 {A B x y} :
    ∀ (f : A → B) (P : B → U) (p : x == y) (u : P (f x)),
    transport (P ◦ f) p u == transport P (ap f p) u
 := λ f P p u,
    match p with
    | refl _ => refl (transport P (ap f (refl x)) u)
    end.

Definition hott_2_3_11 {A x y} : ∀ (P Q : A → U) (f : Π (x : A), P x → Q x),
  ∀ (p : x == y) (u : P x), transport Q p (f x u) == f y (transport P p u)
  := λ P Q f p u,
     match p with
     | refl _ => refl (f x (transport P (refl x) u))
     end.

(* hott section 2.4 - Homotopies and Equivalences *)

Definition homotopy {A B} (f g : A → B) := Π (x : A), (f x == g x).

Notation "f '~~' g" := (homotopy f g) (at level 70).

Definition homotopy_refl {A B} : reflexive _ (@homotopy A B) :=
  λ _ _, refl _.

Definition homotopy_refl2 {A B} : Π (f : A → B), (f ~~ f) :=
  λ _ _, refl _.

Definition homotopy_sym {A B} : symmetric _ (@homotopy A B) :=
  λ f g (p : f ~~ g) x,
  match p x with refl _ => refl (f x) end.

Definition homotopy_sym2 {A B} : Π (f : A → B), Π (g : A → B),
    (f ~~ g) → (g ~~ f) :=
  λ f g (p : f ~~ g) x,
  match p x with refl _ => refl (f x) end.

Definition homotopy_trans {A B} : transitive _ (@homotopy A B) :=
  λ f g h (p : f ~~ g) (q : g ~~ h) x,
  match q x with
  | refl _ => p x
  end.

Definition homotopy_trans2 {A B}
  : Π (f : A → B), Π (g : A → B), Π (h : A → B),
    (f ~~ g) → (g ~~ h) → (f ~~ h)
  := λ f g h (p : f ~~ g) (q : g ~~ h) x,
     match q x with
     | refl _ => p x
     end.

Add Parametric Relation {A B} : _ (@homotopy A B)
 reflexivity proved by homotopy_refl2
 symmetry proved by homotopy_sym2
 transitivity proved by homotopy_trans2
 as homotopy_equivalence.

Definition hott_2_4_3 {A B x y}
  : ∀ (f g : A → B) (H : f ~~ g) (p : x == y), H x • ap g p == ap f p • H y
  := λ f g H p,
     match p with
     | refl _ =>
         match
           match H x as q return (q == q • refl _) with
           | refl _ => refl (refl (f x) • refl (f x))
           end
         with
         | refl _ => refl (id (H x))
         end
     end.

Definition hott_2_4_4 {A x}
  : ∀ (f : A → A) (H : f ~~ id), H (f x) == ap f (H x).
Proof.
intros.
assert (ap f (H x) • H x == H (f x) • H x) as p.
 eapply invert, compose; [ idtac | apply hott_2_4_3 ].
 apply dotl, invert, hott_2_2_2_iv.

 apply dotr with (r := (H x) ⁻¹) in p.
 eapply compose in p; [ idtac | apply compose_assoc ].
 eapply compose in p.
  unfold id in p; simpl in p.
  eapply compose in p; [ idtac | apply hott_2_1_4_i_1 ].
  eapply invert, compose in p; [ idtac | apply compose_assoc ].
  eapply compose in p.
   eapply compose in p; [ eassumption | apply hott_2_1_4_i_1 ].

   eapply dotl, invert.
   eapply compose_invert; reflexivity.

  eapply dotl, invert.
  eapply compose_invert; reflexivity.
Qed.

(* quasi-inverse *)

Definition qinv {A B} (f : A → B) :=
  Σ (g : B → A), ((f ◦ g ~~ id) * (g ◦ f ~~ id))%type.

Example ex_2_4_7 A : qinv (id : A → A) := existT _ id (refl, refl).

Print ex_2_4_7.

Example ex_2_4_8_i_tac A : ∀ x y z : A, ∀ (p : x == y),
  qinv (λ (q : y == z), p • q).
Proof.
intros.
apply (existT _ (λ q, p⁻¹ • q)); split.
 intros t; unfold id, "◦"; simpl.
 eapply compose; [ idtac | eapply invert, hott_2_1_4_i_2 ].
 eapply compose; [ apply compose_assoc | apply dotr ].
 apply compose_invert.

 intros t; unfold id, "◦"; simpl.
 eapply compose; [ idtac | eapply invert, hott_2_1_4_i_2 ].
 eapply compose; [ apply compose_assoc | apply dotr ].
 apply invert_compose.
Qed.

Example ex_2_4_8_i A : ∀ x y z : A, ∀ (p : x == y),
  qinv (λ (q : y == z), p • q)
  := λ x y z p,
     existT _ (compose p⁻¹)
       (λ t : x == z,
        compose_assoc p p⁻¹ t • (compose_invert p •r t)
        • (hott_2_1_4_i_2 t)⁻¹,
        λ t : y == z,
        compose_assoc p⁻¹ p t • (invert_compose p •r t)
        • (hott_2_1_4_i_2 t)⁻¹).

Example ex_2_4_8_ii_tac A : ∀ x y z : A, ∀ (p : x == y),
  qinv (λ (q : z == x), q • p).
Proof.
intros.
apply (existT _ (λ q, q • p⁻¹)); split.
 intros t; unfold id, "◦"; simpl.
 eapply compose; [ idtac | eapply invert, hott_2_1_4_i_1 ].
 eapply compose; [ eapply invert, compose_assoc | apply dotl ].
 eapply invert_compose.

 intros t; unfold id, "◦"; simpl.
 eapply compose; [ idtac | eapply invert, hott_2_1_4_i_1 ].
 eapply compose; [ eapply invert, compose_assoc | apply dotl ].
 eapply compose_invert.
Defined.

Example ex_2_4_8_ii A : ∀ x y z : A, ∀ (p : x == y),
  qinv (λ (q : z == x), q • p)
  := λ x y z p,
     existT _ (λ q, q • p⁻¹)
       (λ t : z == y,
        (compose_assoc t p⁻¹ p)⁻¹ • (t •l invert_compose p)
        • (hott_2_1_4_i_1 t)⁻¹,
        λ t : z == x,
        (compose_assoc t p p⁻¹)⁻¹ • (t •l compose_invert p)
        • (hott_2_1_4_i_1 t)⁻¹).

Example ex_2_4_9_tac A x y : ∀ (p : x == y) (P : A → U), qinv (transport P p).
Proof.
intros.
apply (existT _ (transport P (p⁻¹))); split.
 intros z; unfold id, "◦"; simpl.
 eapply compose; [ apply hott_2_3_9 | idtac ].
 destruct p; reflexivity.

 intros z; unfold id, "◦"; simpl.
 eapply compose; [ apply hott_2_3_9 | idtac ].
 destruct p; reflexivity.
Qed.

Example ex_2_4_9 A x y : ∀ (p : x == y) (P : A → U), qinv (transport P p) :=
  λ p P,
  existT _ (transport P p⁻¹)
  (λ z : P y,
   hott_2_3_9 P p⁻¹ p z
   • match p return (∀ t, transport P (p⁻¹ • p) t == t) with
     | refl _ => λ z0 : P x, refl z0
     end z,
   λ z : P x,
   hott_2_3_9 P p p⁻¹ z
   • match p return (transport P (p • p⁻¹) z == z) with
     | refl _ => refl z
     end).

Definition equiv_prop {A B} isequiv :=
  ∀ f : A → B,
  (qinv f → isequiv f) ∧∧
  (isequiv f → qinv f) ∧∧
  (∀ e₁ e₂ : isequiv f, e₁ == e₂).

Definition isequiv {A B} f :=
  ((Σ (g : B → A), (f ◦ g ~~ id)) * (Σ (h : B → A), (h ◦ f ~~ id)))%type.

Definition qinv_isequiv {A B} (f : A → B) : qinv f → isequiv f.
Proof.
intros p.
destruct p as (g, (α, β)).
split; apply (existT _ g); assumption.
Defined.

Definition isequiv_qinv_tac {A B} (f : A → B) : isequiv f → qinv f.
Proof.
intros p.
destruct p as ((g, Hg), (h, Hh)).
econstructor; split; [ eassumption | idtac ].
intros x.
unfold "◦", homotopy, id in Hg, Hh.
unfold "◦", homotopy, id.
(**)
assert (∀ x, g x == h x) as H.
 intros y.
 apply (@compose _ _ (id (g y))); [ reflexivity | idtac ].
 apply (@compose _ _ (h (f (g y)))); [ idtac | apply ap, Hg ].
 symmetry; apply Hh.

 apply (@compose _ _ (h (f x))); [ apply H | apply Hh ].
(*
eapply compose; [ idtac | apply Hh ].
apply invert.
eapply compose; [ | apply Hh ].
apply invert, ap, Hg.
*)
Defined.

Definition isequiv_qinv2 {A B} (f : A → B) : isequiv f → qinv f :=
  λ eqf,
  match eqf with
  | (existT _ g Hg, existT _ h Hh) =>
      existT _ g
       (Hg,
        λ x : A,
        refl (g (f x))
        • match Hh (g (f x)) with
          | refl _ => refl (h (f (g (f x))))
          end
        • ap h (Hg (f x))
        • Hh x)
  end.

Definition isequiv_qinv {A B} (f : A → B) : isequiv f → qinv f :=
  λ p,
  match p with
  | (existT _ g Hg, existT _ h Hh) =>
      existT _ g (Hg, λ x, ((ap h (Hg (f x)))⁻¹ • Hh (g (f x)))⁻¹ • Hh x)
  end.

Definition equivalence_isequiv {A B} : equiv_prop (@isequiv A B).
Proof.
unfold equiv_prop; intros f.
split; [ apply qinv_isequiv | idtac ].
split; [ apply isequiv_qinv | intros ].
unfold isequiv in e₁, e₂.
destruct e₁ as (H1, H2).
destruct e₂ as (H3, H4).
destruct H1 as (g1, p1).
destruct H2 as (h1, q1).
destruct H3 as (g2, p2).
destruct H4 as (h2, q2).
unfold "~~", id in p1, q1, p2, q2.
unfold "~~", id.
Admitted. (* proof postponed, they say, to sections §2.6, §2.7 and §4.3...
bbb.
*)

Definition equivalence A B := Σ (f : A → B), isequiv f.
Notation "A ≃ B" := (equivalence A B) (at level 70).

(* Lemma 2.4.12 i *)

Definition ideqv A : A ≃ A :=
  existT isequiv id (existT _ id refl, existT _ id refl).

(* quasi-inverse : lemma 2.4.12 ii *)

Definition composite_cancel {A B C} {x y : B → C} {z t : A → B} :
  (x ~~ y) → (z ~~ t) → (x ◦ z ~~ y ◦ t).
Proof.
intros p q a.
transitivity (y (z a)); [ apply p | unfold "◦"; apply ap, q ].
Defined.

Definition quasi_inv_tac {A B} : A ≃ B → B ≃ A.
Proof.
intros eqf.
destruct eqf as (f, ((g, Hg), (h, Hh))).
apply (existT _ g).
split; [ idtac | apply (existT _ f), Hg ].
apply (existT _ f).
unfold "~~", "◦", id in Hg, Hh |-*; intros x.
apply (@compose _ _ (h (f x))); [ idtac | apply Hh ].
apply (@compose _ _ (h (f (g (f x))))); [ apply invert, Hh | apply ap, Hg ].
Defined.

Definition quasi_inv {A B} : A ≃ B → B ≃ A :=
  λ eqf,
  match eqf with
  | existT _ f (existT _ g Hg, existT _ h Hh) =>
      existT isequiv g
        (existT _ f (λ x, (Hh (g (f x)))⁻¹ • ap h (Hg (f x)) • Hh x),
         existT _ f Hg)
 end.

Notation "f '⁻⁻¹'" := (quasi_inv f)
  (at level 8, left associativity, format "'[v' f ']' ⁻⁻¹").

(* Lemma 2.4.12 iii *)

Lemma equiv_compose_tac {A B C} : ∀ (f : A ≃ B) (g : B ≃ C), A ≃ C.
Proof.
intros eqf eqg.
destruct eqf as (f, ((f₁, eqf₁), (f₂, eqf₂))).
destruct eqg as (g, ((g₁, eqg₁), (g₂, eqg₂))).
unfold equivalence.
apply (existT _ (g ◦ f)).
split.
 apply (existT _ (f₁ ◦ g₁)).
 intros c; unfold "◦"; simpl.
 transitivity (g (g₁ c)); [ apply ap, eqf₁ | apply eqg₁ ].

 apply (existT _ (f₂ ◦ g₂)).
 intros a; unfold "◦"; simpl.
 transitivity (f₂ (f a)); [ apply ap, eqg₂ | apply eqf₂ ].
Defined.

Definition equiv_compose {A B C} : A ≃ B → B ≃ C → A ≃ C :=
  λ eqf eqg,
  match eqf with
  | existT _ f (existT _ f₁ eqf₁, existT _ f₂ eqf₂) =>
      match eqg with
      | existT _ g (existT _ g₁ eqg₁, existT _ g₂ eqg₂) =>
          existT _ (g ◦ f)
            (existT (λ h, (g ◦ f) ◦ h ~~ id) (f₁ ◦ g₁)
               (λ c,
                match eqg₁ c with
                | refl _ => ap g (eqf₁ (g₁ c))
                end),
             existT (λ h, h ◦ (g ◦ f) ~~ id) (f₂ ◦ g₂)
               (λ a,
                match eqf₂ a with
                | refl _ => ap f₂ (eqg₂ (f a))
                end))
      end
  end.

Notation "g '◦◦' f" := (equiv_compose f g) (at level 40).

(* 2.5 The higher groupoid structure of type formers *)

Theorem transport_pair_tac : ∀ A B C (x y : A) (p : x == y) b c,
  transport (λ z, (B z * C z)%type) p (b, c) ==
  (transport B p b, transport C p c).
Proof.
intros.
destruct p; reflexivity.
Qed.

Definition transport_pair {A} B C x y (p : x == y) b c
  : transport (λ z : A, (B z * C z)%type) p (b, c) ==
    (transport B p b, transport C p c)
  := match p with
     | refl _ => refl (transport B (refl x) b, transport C (refl x) c)
     end.

(* 2.6 Cartesian product types *)

Module cartesian.

(* shortcuts *)
Definition pr₁ {A B} := @AxB_pr₁ A B.
Definition pr₂ {A B} := @AxB_pr₂ A B.

Theorem hott_2_6_1 {A B} : ∀ x y : A * B,
  (x == y) → (pr₁ x == pr₁ y) * (pr₂ x == pr₂ y).
Proof.
intros x y p.
split; destruct p; reflexivity.
Defined.

Theorem pair_eq_tac {A B} {x y : A * B} :
  (pr₁ x == pr₁ y) * (pr₂ x == pr₂ y) → (x == y).
Proof.
intros p.
destruct x as (a, b).
destruct y as (a', b').
simpl in p.
destruct p as (p, q).
destruct p, q; reflexivity.
Defined.

Definition pair_eq {A B} {x y : A * B} :
  (pr₁ x == pr₁ y) * (pr₂ x == pr₂ y) → (x == y)
:=
   let (a, b)
   return ((pr₁ x == pr₁ y) * (pr₂ x == pr₂ y) → x == y) := x in
   let (_, _)
   return ((pr₁ (a, b) == pr₁ y) * (pr₂ (a, b) == pr₂ y) → (a, b) == y)
   := y in
   λ p,
   match pr₁ p with
   | refl _ =>
       match pr₂ p with
       | refl _ => refl (a, b)
       end
   end.

Notation "'pair⁼'" := pair_eq.

Theorem hott_2_6_2 {A B} : ∀ x y : A * B,
  (pr₁ x == pr₁ y) * (pr₂ x == pr₂ y) ≃ (x == y).
Proof.
intros.
set (f := hott_2_6_1 x y).
set (g := @pair_eq A B x y).
apply quasi_inv.
apply existT with (x := f).
apply qinv_isequiv.
apply (existT _ g); split.
 intros r; unfold id; simpl.
 destruct r as (p, q).
 destruct x as (a, b).
 destruct y as (a', b').
 simpl in p, q, f, g.
 destruct p, q; reflexivity.

 intros p; unfold id; simpl.
 destruct p, x; reflexivity.
Qed.

Definition ap_pr₁ {A B} {x y : A * B} : x == y → pr₁ x == pr₁ y :=
  λ p,
  match p in (_ == z) return (pr₁ x == pr₁ z) with
  | refl _ => refl (pr₁ x)
  end.

Definition ap_pr₂ {A B} {x y : A * B} : x == y → pr₂ x == pr₂ y :=
  λ p,
  match p in (_ == z) return (pr₂ x == pr₂ z) with
  | refl _ => refl (pr₂ x)
  end.

Theorem ap_pr₁_pair {A B} : ∀ (x y : A * B) (p : pr₁ x == pr₁ y) q,
  ap_pr₁ (pair_eq (p, q)) == p.
Proof.
intros.
destruct x as (a, b).
destruct y as (a', b').
simpl in p, q.
destruct p, q; reflexivity.
Qed.

Theorem ap_pr₂_pair {A B} : ∀ (x y : A * B) p (q : pr₂ x == pr₂ y),
  ap_pr₂ (pair_eq (p, q)) == q.
Proof.
intros.
destruct x as (a, b).
destruct y as (a', b').
simpl in p, q.
destruct p, q; reflexivity.
Qed.

Theorem pair_uniqueness {A B}  {x y : A * B} : ∀ (r : x == y),
  r == pair_eq (ap_pr₁ r, ap_pr₂ r).
Proof.
intros.
destruct r; simpl.
destruct x as (a, b); reflexivity.
Qed.

Theorem refl_pair_eq {A B} : ∀ z : A * B,
  refl z == pair_eq (refl (pr₁ z), refl (pr₂ z)).
Proof.
intros.
destruct z as (x, y); reflexivity.
Qed.

Theorem inv_pair_eq {A B} {x y : A * B} : ∀ p : x == y,
  p⁻¹ == pair_eq (ap_pr₁ p⁻¹, ap_pr₂ p⁻¹).
Proof.
intros.
destruct p; simpl.
destruct x as (a, b); reflexivity.
Qed.

Theorem comp_pair_eq {A B} {x y z : A * B} : ∀ (p : x == y) (q : y == z),
  p • q == pair_eq (ap_pr₁ p • ap_pr₁ q, ap_pr₂ p • ap_pr₂ q).
Proof.
intros.
destruct p, q; simpl.
destruct x; reflexivity.
Qed.

Theorem hott_2_6_4 {Z} {A B : Z → U} : ∀ (z w : Z) (p : z == w) x,
  transport (λ y, (A y * B y)%type) p x ==
  (transport A p (pr₁ x), transport B p (pr₂ x)).
Proof.
intros.
destruct p; simpl.
destruct x; reflexivity.
Qed.

Definition pair_eq_ap {A B A' B' x y} (f : A * B → A' * B') :=
  @pair_eq A' B' (f x) (f y).

Theorem hott_2_6_5 {A B A' B'} :
  ∀ (g : A → A') (h : B → B') (f := λ x, (g (pr₁ x), h (pr₂ x)))
    (x y : A * B) (p : pr₁ x == pr₁ y) (q : pr₂ x == pr₂ y),
  ap f (pair_eq (p, q)) == pair_eq_ap f (ap g p, ap h q).
Proof.
intros; unfold pair_eq_ap.
destruct x as (a, b).
destruct y as (c, d).
simpl in p, q.
destruct p, q; simpl.
reflexivity.
Qed.

End cartesian.

(* 2.7 Σ-types *)

Module Σ_type.

Definition pr₁ {A B} := @Σ_pr₁ A B.
Definition pr₂ {A B} := @Σ_pr₂ A B.

Definition transport_eq {A P} : ∀ (w w' : Σ (x : A), P x) (p : w == w'),
  (ap pr₁ p)⁎ (pr₂ w) == pr₂ w'
:=
  λ w w' p,
  match p with
  | refl _ => refl (pr₂ w)
  end.

Definition depend_eq {A P} : ∀ (w w' : Σ (x : A), P x) (p : w == w'),
  P (pr₁ w) == P (pr₁ w')
:=
  λ w w' p, ap P (ap pr₁ p).

Remark hott_2_7_1 {A P} : ∀ (w w' : Σ (x : A), P x) (p : w == w'),
  (ap pr₁ p)⁎ (pr₂ w) == pr₂ w'.
Proof.
intros w w' p.
destruct p.
reflexivity.
Defined.

Lemma hott_2_7_2_f {A} : ∀ P (w w' : Σ (x : A), P x),
  w == w' → Σ (p : pr₁ w == pr₁ w'), p⁎ (pr₂ w) == pr₂ w'.
Proof.
intros P w w' p.
destruct p; simpl.
apply (existT _ (refl _)); reflexivity.
Defined.

Lemma hott_2_7_2_g {A} : ∀ P (w w' : Σ (x : A), P x),
  (Σ (p : pr₁ w == pr₁ w'), p⁎ (pr₂ w) == pr₂ w') → w == w'.
Proof.
intros P w w' p.
destruct w as (w₁, w₂).
destruct w' as (w'₁, w'₂); simpl.
simpl in p.
destruct p as (p, q).
destruct p, q; reflexivity.
Defined.

Theorem hott_2_7_2 {A} : ∀ (P : A → U) (w w' : Σ (x : A), P x),
  (w == w') ≃ Σ (p : pr₁ w == pr₁ w'), p⁎ (pr₂ w) == pr₂ w'.
Proof.
intros.
apply (existT _ (hott_2_7_2_f P w w')).
apply qinv_isequiv.
apply (existT _ (hott_2_7_2_g P w w')); split.
 intros r; unfold id; simpl.
 destruct r as (p, q).
 destruct w as (a, b).
 destruct w' as (a', b').
 simpl in p, q; simpl.
 destruct p, q; simpl.
 unfold hott_2_7_2_f; simpl.
 unfold hott_2_7_2_g; simpl.
 unfold "◦"; simpl.
 reflexivity.

 intros r; unfold id; simpl.
 destruct r.
 destruct w as (a, b); simpl.
 unfold hott_2_7_2_f; simpl.
 unfold hott_2_7_2_g; simpl.
 unfold "◦"; simpl.
 reflexivity.
Qed.

(* I don't see in what it is a corollary of 2.7.2... *)

Corollary hott_2_7_3 {A} : ∀ P (z : Σ (x : A), P x),
  z == existT P (pr₁ z) (pr₂ z).
Proof.
intros; destruct z as (x, y); reflexivity.
Qed.

Definition pair_eq {A} {P : A → U} {x y : A} {u : P x} {v : P y} :
  ∀ (p : x == y), p⁎ u == v → existT _ x u == existT _ y v
:=
  λ p q,
  match p with
  | refl _ =>
      λ (w : P x) (r : transport P (refl x) u == w),
      match r in (_ == t) return (existT P x u == existT P x t) with
      | refl _ => refl (existT P x (transport P (refl x) u))
      end
  end v q.

Notation "'pair⁼'" := pair_eq.

Definition pair_eq_def {A} {P : A → U} (x y : A) (u : P x) (p : x == y) :
  existT P x u == existT P y (transport P p u)
:=
  pair_eq p (refl (p⁎ u)).

Definition tfam {A} P (Q : (Σ (x : A), P x) → U) (x : A) :=
  Σ (u : P x), Q (existT _ x u).

Definition hott_2_7_4 {A} P Q (x y : A) (p : x == y) (uz : tfam P Q x) :
  let u := projT1 uz in
  let z := projT2 uz in
  ∀ (k : P y → Q (existT (λ x : A, P x) y (transport P p u))),
  p⁎ uz == existT _ (p⁎ u) (k (p⁎ u)).
Proof.
intros.
destruct p.
simpl.
unfold id; simpl.
subst u z; simpl.
bbb.

Check k.
Check (p⁎ u).
(* k
     : Q (existT (λ x : A, P x) y (transport P p u)) *)
(* @pair_eq
     : ∀ (A : Type) (P : A → U) (x y : A) (u : P x) 
       (v : P y) (p : x == y),
       transport P p u == v → existT P x u == existT P y v *)
Check (@pair_eq A P x y u (p⁎ u) p (refl _) :
   Q (existT (λ x : A, P x) y (transport P p u))).


   Q (existT (λ x : A, P x) y (transport P p u))
Check (λ q,
  (@pair_eq A P x y u (p⁎ u) p q :
   Q (existT (λ x : A, P x) y (transport P p u)))).

Check (existT _ (p⁎ u) ((pair⁼ p (refl (p⁎ u)))⁎ (z))).

transport (tfam P Q) p uz
     : tfam P Q y

(transport P p u,
transport Q (pair⁼ p (refl (transport (λ x : A, P x) p u))) z)
     : P y * Q (existT (λ x : A, P x) y (transport (λ x : A, P x) p u))

  p⁎ uz == (p⁎ u, (pair⁼ p (refl (p⁎ u)))⁎ (z)).


Definition hott_2_7_4 {A} P Q (x y : A) (p : x == y) :
  tfam P Q x → tfam P Q y
:=
  λ uz, match p with refl _ => uz end.

bbb.

hott_2_7_4 = 
λ (A : Type) (P : A → Type) (Q : {x : A & P x} → U) 
(x y : A) (p : x == y) (uz : tfam P Q x),
match p in (_ == a) return (tfam P Q a) with
| refl _ => uz
end
     : ∀ (A : Type) (P : A → Type) (Q : {x : A & P x} → U) 
       (x y : A), x == y → tfam P Q x → tfam P Q y

Argument A is implicit and maximally inserted
Argument scopes are [type_scope _ _ _ _ _ _]

bbb.


Theorem hott_2_7_4 {A} : ∀ P Q (x y : A) (p : x == y) (uz : tfam P Q x),
∀ yyy,
  transport (tfam P Q) p uz ==
  existT _ (p⁎ (projT1 uz)) yyy.
Proof.
intros.
Check (transport (tfam P Q) p uz).
(* tfam P Q y *)
Check existT.
Check (@existT (P x)).
(* existT (A:=P x)
     : ∀ (P0 : P x → Type) (x0 : P x), P0 x0 → {x : P x & P0 x} *)
Check (@existT (P x) (λ u, A)).
bbb.

P0 : ∀ x, Q (existT _ x u)
P0 := λ x,

Check (λ A P u p, @existT A P u p).
Check (existT _ (p⁎ (projT1 uz)) bool).
Check (Q _ == bool).

?T x : Q (existT _ y (p⁎ (projT1 uz)))

yyy
     : Q (existT (λ x : A, P x) y (transport P p (projT1 uz)))

  @pair_eq A x y P p ==
  pair_eq p.
intros.
Check (@pair_eq A x y P p).

  @pair_eq A x y P p (refl (p⁎ (projT1 uz))) ==
  @pair_eq A x y P p (refl (p⁎ (projT1 uz))).

  transport (tfam P Q) p uz ==
  existT (tfam P Q) (p⁎ (projT1 uz))
    ((pair_eq _ (refl (p⁎ (projT1 uz))))⁎ (projT2 uz)).
bbb.

Set Printing All.

Toplevel input, characters 177-178:
Error:
In environment
A : Type
P : forall _ : A, U
Q : forall _ : @sigT A (fun x : A => P x), U
x : A
y : A
p : @Id A x y
uz : @sigT (P x) (fun u : P x => Q (@existT A (fun x : A => P x) x u))
The term "p" has type "@Id A x y" while it is expected to have type
 "@Id (@sigT ?A0 (fun z : ?A0 => ?B0 z)) ?x0 ?y0".


 (uz : foo P Q x)
    (vt : foo P Q y)
    (u := pr₁ uz) (z := pr₂ uz)
    (zzz : (λ v : P y, Q (existT P y v)) (transport P p u)),
  transport (foo P Q) p uz ==
  existT _ (@transport _ P x y p u) zzz.
Proof.
bbb.

Theorem hott_2_7_4 {A} : ∀ (P : A → U) (Q : (Σ (x : A), P x) → U),
  ∀ (x y : A) (p : x == y) (uz : foo P Q x)
    (vt : foo P Q y)
    (u := pr₁ uz) (z := pr₂ uz)
    (zzz : (λ v : P y, Q (existT P y v)) (transport P p u)),
  transport (foo P Q) p uz ==
  existT _ (@transport _ P x y p u) zzz.
Proof.
intros.
bbb.

Abort. (* 1/ not sure how to do that, 2/ don't know what zzz should b
          3/ I don't understand the whole thing → I give up for the moment

1 subgoals, subgoal 1 (ID 4136)
  
  A : Type
  P : A → U
  Q : {x : A & P x} → U
  x : A
  y : A
  p : x == y
  uz : foo P Q x
  vt : foo P Q y
  u := pr₁ uz : P x
  z := pr₂ uz : (λ u0 : P x, Q (existT P x u0)) (Σ_pr₁ uz)
  zzz : (λ u0 : P y, Q (existT P y u0)) (transport P p u)
  ============================
   transport (λ x0 : A, {u0 : P x0 & Q (existT P x0 u0)}) p uz ==
   existT (λ u0 : P y, Q (existT P y u0)) (transport P p u) zzz
*)

End Σ_type.

(* 2.8 The unit type *)

Theorem hott_2_8_1 : ∀ x y : unit, (x == y) ≃ unit.
Proof.
intros.
destruct x, y.
set (f := λ _ : tt == tt, tt).
set (g := λ _ : unit, refl tt).
unfold equivalence.
apply (existT _ f), qinv_isequiv.
apply (existT _ g); split.
 subst f g; simpl.
 unfold "◦"; simpl.
 intros x; destruct x; reflexivity.

 subst f g; simpl.
 unfold "◦"; simpl.
 intros x.
 refine (match x with refl _ => _ end).
 reflexivity.
Qed.

Definition unit_intro : unit := tt.
Definition unit_elim : unit → unit := id.
Definition unit_comp : unit → unit := id.
Definition unit_transport := @transportconst unit tt tt.
Print unit_transport.

(* 2.9 Π-types and the function extensionality axiom *)

Module Π_type.

Definition happly {A B} {f g : Π (x : A), B x}
  : f == g → Π (x : A), f x == g x
  := λ p,
     match p with
     | refl _ => λ y, refl (f y)
     end.

Axiom extensionality : ∀ {A B} f g, isequiv (@happly A B f g).

Definition funext_tac {A B} {f g : Π (x : A), B x}
  : (∀ x, f x == g x) → (f == g).
Proof.
intros p.
pose proof @extensionality A B f g as H.
apply isequiv_qinv in H.
destruct H as (h, α, β).
apply h, p.
Defined.

Definition funext {A B} {f g : ∀ x : A, B x}
  : (∀ x : A, f x == g x) → f == g
  := λ p,
     match isequiv_qinv happly (extensionality f g) with
     | existT _ h _ => h p
     end.

Theorem funext_quasi_inverse_of_happly_tac {A B} :
  ∀ (f g : Π (x : A), B x) (h : ∀ x, f x == g x) x,
  happly (funext h) x == h x.
Proof.
intros.
unfold funext; simpl.
set (p := isequiv_qinv happly (extensionality f g)).
destruct p as (k, (α, β)).
unfold "◦" in α.
pose proof α h as H; simpl in H.
eapply happly in H.
eassumption.
Defined.

Definition funext_quasi_inverse_of_happly {A B}
  : ∀ (f g : Π (x : A), B x) (h : ∀ x, f x == g x) (x : A),
    happly (funext h) x == h x
  := λ f g h x,
     match isequiv_qinv happly (extensionality f g) as q
     return (happly match q with existT _ k _ => k h end x == h x)
     with
     | existT _ k (α, _) => happly (α h) x
     end.

Theorem funext_prop_uniq_princ {A B} : ∀ (f g : Π (x : A), B x) (p : f == g),
  p == funext (happly p).
Proof.
intros.
unfold funext; simpl.
set (q := isequiv_qinv happly (extensionality f g)).
destruct q as (k, (α, β)).
apply invert, β.
Defined.

Theorem funext_identity {A B} : ∀ (f : Π (x : A), B x),
  refl f == funext (λ x, refl (f x)).
Proof.
intros.
unfold funext; simpl.
set (p := isequiv_qinv happly (extensionality f f)).
destruct p as (k, (α, β)).
apply invert, (β (refl f)).
Defined.

Theorem funext_invert {A B} {f g : Π (x : A), B x} : ∀ (α : f == g),
  α⁻¹ == funext (λ x, (happly α x)⁻¹).
Proof.
intros.
destruct α; simpl.
apply funext_identity.
Qed.

Theorem funext_compose {A B} {f g h : Π (x : A), B x} :
    ∀ (α : f == g) (β : g == h),
  α • β == funext (λ x, happly α x • happly β x).
Proof.
intros.
destruct α, β; simpl.
unfold id; simpl.
apply funext_identity.
Qed.

Definition hott_2_9_4 {X A B} {x y : X}
  : ∀ (p : x == y) (f : A x → B x),
     transport (λ x, A x → B x) p f ==
     λ a, transport B p (f (transport A p⁻¹ a))
  := λ p f,
     match p with
     | refl _ => refl _
     end.

Definition pr₁ {A B} := @Σ_pr₁ A B.
Definition pr₂ {A B} := @Σ_pr₂ A B.

Definition pair_eq {A B} {x y : A} (p : x == y)
  : ∀ u, existT B x u == existT B y (transport B p u)
  := λ u,
     match p with
     | refl _ => refl (existT B x (transport B (refl x) u))
     end.

Notation "'pair⁼'" := pair_eq.

Notation "'Π' A ( B )" := (λ x, Π (a : A x), B x a) (at level 0, A at level 0).
Notation "B ^" := (λ w, B (pr₁ w) (pr₂ w)) (at level 0).

Definition hott_2_9_5 {X} {A : X → U} {B : Π (x : X), A x → U} {x y : X}
  : ∀ (p : x == y) (f : ∀ a : A x, B x a),
      transport (Π A (B)) p f ==
      λ a, transport B^ (pair⁼ p⁻¹ a)⁻¹ (f (transport A p⁻¹ a))
  := λ p f,
     match p with
     | refl _ => refl _
     end.

Lemma hott_2_9_6_i {X} {A B : X → U} {x y : X} (p : x == y) :
  ∀ (f : A x → B x) (g : A y → B y),
  (transport (λ z, A z → B z) p f == g) ≃
  Π (a : A x), (transport B p (f a) == g (transport A p a)).
Proof.
intros.
destruct p; simpl.
unfold id; simpl.
unfold equivalence.
apply existT with (x := happly).
apply extensionality.
Qed.

Definition hott_2_9_6_ii {X} {A B : X → U} {x y : X} (p : x == y)
  : ∀ (f : A x → B x) (g : A y → B y) (a : A x)
      (q : transport (λ z, A z → B z) p f == g),
    transport (λ z, A z → B z) p f (transport A p a) ==
    g (transport A p a)
  := λ f g a q,
     happly q (transport A p a).

Definition hott_2_9_6_iii {X} {A B : X → U} {x y : X} (p : x == y)
  : ∀ (f : A x → B x) (g : A y → B y) (a : A x)
      (q : transport (λ z, A z → B z) p f == g),
    transport (λ z, A z → B z) p f (p⁎ a) ==
    transport B p (f ((p⁻¹)⁎ (p⁎ a))).
Proof.
intros; destruct p; reflexivity.
Qed.

Definition hott_2_9_6_iv {X} {A B : X → U} {x y : X} (p : x == y)
  : ∀ (f : A x → B x) (g : A y → B y) (a : A x)
      (q : transport (λ z, A z → B z) p f == g),
    transport (λ z, A z → B z) p f (p⁎ a) ==
    p⁎ (f a).
Proof.
intros; destruct p; reflexivity.
Qed.

Definition hott_2_9_6_v {X} {A B : X → U} {x y : X}
  : ∀ (p : x == y) (f : A x → B x) (g : A y → B y) (a : A x)
      (q : transport (λ z, A z → B z) p f == g),
    transport (λ z, A z → B z) p f (p⁎ a) ==
    g (p⁎ a).
Proof.
intros; destruct p, q; reflexivity.
Qed.

Lemma hott_2_9_7 {X} {A : X → U} {B : Π (x : X), A x → U} {x y : X} :
  ∀ (p : x == y) (f : Π (a : A x), B x a) (g : Π (a : A y), B y a),
  (transport (λ x, ∀ a : A x, B x a) p f == g) ≃
  (Π (a : A x), transport B^ (pair⁼ p a) (f a) == g (transport A p a)).
Proof.
intros.
destruct p; simpl.
unfold id; simpl.
unfold equivalence.
apply existT with (x := happly).
apply extensionality.
Qed.

End Π_type.

(* 2.10 Universes and the univalence axiom *)

(* lemma 2.10.1 *)

Definition idtoeqv_tac {A B : U} : A == B → A ≃ B.
Proof.
intros p.
set (q := transport id p).
apply (existT _ q).
destruct p.
subst q; simpl.
apply qinv_isequiv, ex_2_4_7.
Defined.

Definition isequiv_transport {A B} : ∀ (p : A == B), isequiv (transport id p)
  := λ p,
     match p with
     | refl _ => (existT _ id refl, existT _ id refl)
     end.

Definition idtoeqv {A B : U} : A == B → A ≃ B :=
  λ p,
  existT isequiv (transport id p) (isequiv_transport p).

Axiom univalence : ∀ A B : U, isequiv (@idtoeqv A B).

Theorem univalence2 : ∀ A B : U, (A == B) ≃ (A ≃ B).
Proof.
intros.
pose proof (@univalence A B) as p.
esplit; eassumption.
Defined.

(* funny thing about univalence axiom: it is equivalent to the axiom
   where the middle ≃ is replaced by equality *)

Theorem univ_eq : (∀ A B, (A ≃ B) ≃ (A == B)) → (∀ A B, (A ≃ B) == (A == B)).
Proof.
intros H A B.
apply H.
apply H.
Qed.

Theorem eq_univ : (∀ A B, (A ≃ B) == (A == B)) → (∀ A B, (A ≃ B) ≃ (A == B)).
Proof.
intros H A B.
rewrite H.
rewrite H.
reflexivity.
Qed.

(* introduction rule *)

Definition ua_tac {A B} : A ≃ B → A == B.
Proof.
intros p.
set (q := isequiv_qinv idtoeqv (univalence A B)).
destruct q as (f, _).
apply f, p.
Defined.

Definition ua {A B} : A ≃ B → A == B :=
  match isequiv_qinv idtoeqv (univalence A B) with
  | existT _ f _ => f
  end.

(* elimination rule = idtoeqv *)
(* ... *)

(* propositional computation rule *)
(* how the eliminator idtoeqv acts on the constructor A == B *)

Definition idtoeqv_ua {A B} : ∀ (f : A ≃ B), idtoeqv (ua f) == f.
Proof.
intros.
unfold ua; simpl.
set (q := isequiv_qinv idtoeqv (univalence A B)).
destruct q as (g, (α, β)).
apply α.
Defined.

Definition ua_pcr {A B}
  : ∀ (f : A ≃ B) (x : A), transport id (ua f) x == projT1 f x
  := λ f x,
     match idtoeqv_ua f with
     | refl _ => refl (projT1 (idtoeqv (ua f)) x)
     end.

(* propositional uniqueness principle *)

Definition ua_idtoeqv {A B} : ∀ (p : A == B), ua (idtoeqv p) == p.
Proof.
intros.
unfold ua; simpl.
set (q := isequiv_qinv idtoeqv (univalence A B)).
destruct q as (f, (α, β)).
apply β.
Defined.

Definition ua_pup {A B}
  : ∀ (p : A == B),
    p == ua (existT isequiv (transport id p) (isequiv_transport p))
  := λ (p : A == B),
     match p return
       (ua (idtoeqv p) == p
        → p == ua (existT isequiv (transport id p) (isequiv_transport p)))
     with
     | refl _ =>
         λ q,
         match q in (_ == r) return (r == ua (ideqv A)) with
         | refl _ => refl _
         end
     end (ua_idtoeqv p).

(* reflexivity *)

Definition idtoeqv_refl (A : U) : ideqv A == idtoeqv (refl A) :=
  refl (idtoeqv (refl A)).

Definition ua_refl_tac : ∀ A, refl A == ua (ideqv A).
Proof.
intros.
rewrite idtoeqv_refl, ua_idtoeqv.
reflexivity.
Defined.

Definition ua_refl : ∀ A, refl A == ua (ideqv A) :=
  λ A,
  (λ p,
   match p with
   | refl _ =>
       match ua_idtoeqv (refl A) in (_ == p) return (_ == p → _) with
       | refl _ => id
       end (refl (refl A))
   end)
  (idtoeqv_refl A).

(* concatenation *)

Definition idtoeqv_concat {A B C} : ∀ (p : A == B) (q : B == C),
  idtoeqv (p • q) == idtoeqv q ◦◦ idtoeqv p.
Proof.
intros.
destruct p, q; reflexivity.
Defined.

Definition ua_concat {A B C} : ∀ (f : A ≃ B) (g : B ≃ C),
  ua f • ua g == ua (g ◦◦ f).
Proof.
intros.
set (p := ua f).
set (q := ua g).
transitivity (ua (idtoeqv q ◦◦ idtoeqv p)).
 transitivity (ua (idtoeqv (p • q))); [ apply invert, ua_idtoeqv | idtac ].
 apply ap, idtoeqv_concat.

 subst p q.
 do 2 rewrite idtoeqv_ua; reflexivity.
Defined.

(* inverse *)

Definition idtoeqv_inv {A B} : ∀ (f : A == B), ua (idtoeqv f)⁻⁻¹ == f⁻¹.
Proof.
intros.
destruct f; simpl.
unfold ua.
set (q := univalence A A).
destruct q as ((g, Hg), (h, Hh)); simpl.
unfold "◦", "~~", id in Hg, Hh.
pose proof Hh (refl A) as H.
unfold id in H.
rewrite <- H; simpl.
unfold idtoeqv; simpl.
assert (g ~~ h) as Hgh.
 intros x; set (y := g x).
 apply (@compose _ _ (h (idtoeqv y))); [ apply invert, Hh | apply ap, Hg ].

 apply Hgh.
Defined.

Definition ua_inverse {A B} : ∀ f : A ≃ B, (ua f)⁻¹ == ua f⁻⁻¹.
Proof.
intros eqf.
symmetry.
transitivity (ua (idtoeqv (ua eqf))⁻⁻¹).
 rewrite idtoeqv_ua; reflexivity.

 apply idtoeqv_inv.
Defined.

Lemma hott_2_10_5_i {A} {B : A → U} {x y : A} : ∀ (p : x == y) (u : B x),
  transport B p u = transport id (ap B p) u.
Proof.
intros.
destruct p; reflexivity.
Defined.

Lemma hott_2_10_5_ii {A} {B : A → U} {x y : A} : ∀ (p : x == y) (u : B x),
  transport id (ap B p) u == projT1 (idtoeqv (ap B p)) u.
Proof. reflexivity. Qed.

Lemma hott_2_10_5 {A} {B : A → U} {x y : A} : ∀ (p : x == y) (u : B x),
  transport B p u == projT1 (idtoeqv (ap B p)) u.
Proof. intros; destruct p; reflexivity. Qed.

(* 2.11 Identity type *)

(* Theorem 2.11.1 *)

Theorem hott_2_11_1 {A B} : ∀ (f : A → B), isequiv f → ∀ (a a' : A),
  (a == a') ≃ (f a == f a').
Proof.
intros f Hf a a'.
apply (existT _ (@ap A B a a' f)).
apply isequiv_qinv in Hf.
destruct Hf as (f₁, (α, β)).
apply qinv_isequiv.
unfold qinv.
set (g := λ r, (β a)⁻¹ • ap f₁ r • β a').
unfold "◦", id in g; simpl in g.
apply (existT _ g); subst g.
unfold "◦", "~~", id; simpl.
split; intros q.
 set (r := @compose _ _ _ a' (@invert _ (f₁ (f a)) a (β a) • ap f₁ q) (β a')).
 apply (@compose _ _ ((α (f a))⁻¹ • α (f a) • ap f r)).
  eapply compose; [ apply lu | idtac ].
  apply dotr, invert, invert_compose.

  eapply compose; [ eapply invert, compose_assoc | idtac ].
  unfold id, composite; simpl.
  pose proof (hott_2_4_3 ((f ◦ f₁) ◦ f) f (λ a, α (f a)) r) as H.
  unfold "◦" in H; simpl in H.
  eapply compose; [ eapply dotl, H | simpl ].
  apply (@compose _ _ ((α (f a))⁻¹ • (ap f (ap f₁ (ap f r)) • α (f a')))).
   apply dotl, dotr.
   apply (@compose _ _ (ap (f ◦ f₁ ◦ f) r)); [ reflexivity | idtac ].
   eapply invert, compose; [ idtac | eapply ap_composite ].
   eapply compose; [ apply (ap_composite f₁ f (ap f r)) | reflexivity ].

   eapply compose; [ apply compose_assoc | idtac ].
   rewrite (ap_composite f f₁ r).
   apply (@compose _ _ ((α (f a))⁻¹ • ap f (β a • r • (β a')⁻¹) • α (f a'))).
    apply dotr, dotl, ap.
    rewrite r; simpl.
    rewrite <- ru, compose_invert.
    reflexivity.

    apply (@compose _ _ ((α (f a))⁻¹ • ap f (ap f₁ q) • α (f a'))).
     apply dotr, dotl, ap; subst r.
     do 2 rewrite compose_assoc.
     rewrite compose_invert; simpl.
     unfold id; simpl.
     rewrite <- compose_assoc.
     rewrite compose_invert; simpl.
     rewrite <- ru; reflexivity.

     assert (H1 : α (f a) • q == ap (f ◦ f₁) q • α (f a')).
      rewrite <- (hott_2_4_3 (f ◦ f₁) id α q).
      apply dotl, invert, hott_2_2_2_iv.

      unfold id, composite; simpl.
      pose proof (@ap_composite B A B (f a) (f a') f₁ f q) as H2.
      rewrite H2.
      rewrite <- compose_assoc.
      unfold id, composite in H1; simpl in H1.
      unfold composite; simpl.
      rewrite <- H1.
      rewrite compose_assoc, invert_compose.
      reflexivity.

 rewrite (ap_composite f f₁ q).
 destruct q; simpl.
 unfold "◦", "~~", id in β; simpl in β.
 unfold "◦"; simpl; rewrite β; reflexivity.
Defined.

Module cartesian2.

(* Paths p = q, where p,q : w =_{AxB} w', are equivalent to pairs of
   paths
       ap_{pr₁} p =_{pr₁ w =_A pr₁ w'} ap_{pr₁} q
       ap_{pr₂} p =_{pr₂ w =_A pr₂ w'} ap_{pr₂} q *)

Definition pr₁ {A B} := @AxB_pr₁ A B.
Definition pr₂ {A B} := @AxB_pr₂ A B.

Definition pair_eq_split {A B} : ∀ (a b : A) (c d : B),
  (a, c) == (b, d) → (a == b) * (c == d)
:= λ a b c d H, (cartesian.ap_pr₁ H, cartesian.ap_pr₂ H).

Definition split_pair_eq {A B} : ∀ (a b : A) (c d : B),
  (a == b) * (c == d) → (a, c) == (b, d)
:= λ a b c d H,
   match pr₁ H with
   | refl _ =>
       match pr₂ H with
       | refl _ => refl (a, c)
       end
   end.

Definition split_pair_eq_id {A B} : ∀ (a b : A) (c d : B),
  split_pair_eq a b c d ◦ pair_eq_split a b c d ~~ id
:= λ a b c d p,
   match p in (_ == q)
     return
     ((let (b0, d0) as x return ((a, c) == x → Type) := q in
       λ p2,
       split_pair_eq a b0 c d0 (pair_eq_split a b0 c d0 p2) == p2) p)
   with
   | refl _ => refl (refl (a, c))
   end.

Definition pair_eq_split_id {A B} : ∀ (a b : A) (c d : B),
  pair_eq_split a b c d ◦ split_pair_eq a b c d ~~ id
:= λ a b c d p,
   let (q, r) as p0
   return (pair_eq_split a b c d (split_pair_eq a b c d p0) == p0) := p in
   match q with
   | refl _ =>
       match r with
       | refl _ => refl (refl a, refl c)
       end
   end.

Theorem cart_pr₁ {A B} : @cartesian.pr₁ A B == pr₁.
Proof. reflexivity. Qed.
Theorem cart_pr₂ {A B} : @cartesian.pr₂ A B == pr₂.
Proof. reflexivity. Qed.

Theorem equiv_pair {A B} {w w' : A * B} : ∀ (p q : w == w'),
  (p == q) ≃ ((ap pr₁ p, ap pr₂ p) == (ap pr₁ q, ap pr₂ q)).
Proof.
intros.
set (f := λ p : w == w', (ap pr₁ p, ap pr₂ p)).
assert (isequiv f) as Hf; [ idtac | apply (hott_2_11_1 f Hf p q) ].
set (g := @cartesian.pair_eq A B w w').
apply qinv_isequiv.
unfold qinv.
apply (existT _ g); split.
 subst f g.
 unfold "◦", "~~", id; intros (v, v').
 apply split_pair_eq; split.
  apply cartesian.ap_pr₁_pair.

  apply cartesian.ap_pr₂_pair.

 subst f g.
 unfold "◦", "~~", id; intros r.
 apply invert, cartesian.pair_uniqueness.
Defined.

Theorem pair_equiv {A B} {w w' : A * B} : ∀ (p q : w == w'),
  (p == q) ≃ (ap pr₁ p == ap pr₁ q) * (ap pr₂ p == ap pr₂ q).
Proof.
intros.
eapply equiv_compose; [ apply equiv_pair | idtac ].
set (u₁ := ap pr₁ p).
set (u₂ := ap pr₂ p).
set (v₁ := ap pr₁ q).
set (v₂ := ap pr₂ q).
apply quasi_inv.
apply (existT _ (split_pair_eq u₁ v₁ u₂ v₂)).
apply qinv_isequiv.
unfold qinv.
apply (existT _ (pair_eq_split u₁ v₁ u₂ v₂)); split.
 apply split_pair_eq_id.

 apply pair_eq_split_id.
Defined.

End cartesian2.

Module Σ_type2.

(* Paths p = q, where p,q : f =_{Π(x:A)B(x)} g, are equivalent to
   homotopies
       Π (x : A) (happly (p) (x) =_{f(x)=g(x)} happly (q) (x)). *)

Definition pr₁ {A B} := @Σ_pr₁ A B.
Definition pr₂ {A B} := @Σ_pr₂ A B.
Definition happly {A B f g} := @Π_type.happly A B f g.

Theorem dep_fun_equiv {A B} {f g : Π (x : A), B x} : ∀ (p q : f == g),
  (p == q) ≃ Π (x : A), (happly p x == happly q x).
Proof.
intros p q.
pose proof hott_2_11_1 happly (Π_type.extensionality f g) p q as H.
eapply equiv_compose; [ eapply H | idtac ].
apply (existT _ happly), Π_type.extensionality.
Defined.

(* the same, but putting function extensionality as hypothesis instead
   of using axiom *)

Theorem dep_fun_equiv2 {A B} {f g : Π (x : A), B x} : ∀ (p q : f == g),
  isequiv (@happly _ _ f g)
  → isequiv (@happly _ _ (happly p) (happly q))
  → (p == q) ≃ Π (x : A), (happly p x == happly q x).
Proof.
intros p q Hf Hg.
pose proof hott_2_11_1 happly Hf p q as H.
eapply equiv_compose; [ eapply H | idtac ].
apply (existT _ happly), Hg.
Defined.

(* transport in families of paths *)

Lemma hott_2_1_12_i {A} : ∀ (a x₁ x₂ : A) (p : x₁ == x₂) (q : a == x₁),
  transport (λ x, a == x) p q = q • p.
Proof. intros; destruct p, q; reflexivity. Defined.

Lemma hott_2_1_12_ii {A} : ∀ (a x₁ x₂ : A) (p : x₁ == x₂) (q : x₁ == a),
  transport (λ x, x == a) p q = p⁻¹ • q.
Proof. intros; destruct p; reflexivity. Defined.

Lemma hott_2_1_12_iii {A} : ∀ (a x₁ x₂ : A) (p : x₁ == x₂) (q : x₁ == x₁),
  transport (λ x, x == x) p q = p⁻¹ • q • p.
Proof. intros; destruct p; simpl; destruct q; reflexivity. Defined.

(* they pretend that this needs 2.3.10 and 2.11.2 but it can be proved
   directly by induction: *)

Theorem hott_2_11_3 {A B} : ∀ (f g : A → B) a a'
  (p : a == a') (q : f a == g a),
  transport (λ x, f x == g x) p q == (ap f p)⁻¹ • q • ap g p.
Proof. intros; destruct p; simpl; destruct q; reflexivity. Defined.

Theorem hott_2_11_4 {A B} : ∀ (f g : Π (x : A), B x) a a'
  (p : a == a') (q : f a == g a),
  transport (λ x, f x == g x) p q ==
  (apd f p)⁻¹ • ap (transport B p) q • apd g p.
Proof. intros; destruct p; simpl; destruct q; reflexivity. Defined.

Theorem hott_2_11_5 {A} {a a' : A} :
  ∀ (p : a == a') (q : a == a) (r : a' == a'),
  (transport (λ x, x == x) p q == r) ≃ (q • p == p • r).
Proof.
intros.
destruct p; simpl.
unfold id; simpl.
rewrite <- ru.
apply ideqv.
Defined.

(* 2.12 Coproducts *)

(* my proof *)

Definition inl_inversion {A B} (a₁ a₂ : A) :
  @Id (A + B) (inl a₁) (inl a₂) → (a₁ == a₂)
:= ap (λ a, match a with inl a₁ => a₁ | inr _ => a₁ end).

Definition inr_inversion {A B} (b₁ b₂ : B) :
  @Id (A + B) (inr b₁) (inr b₂) → (b₁ == b₂)
:= ap (λ a, match a with inl _ => b₁ | inr b₁ => b₁ end).

Definition inl_equal {A B} (a₁ a₂ : A) :
  (a₁ == a₂) → @Id (A + B) (inl a₁) (inl a₂)
:= λ H : a₁ == a₂,
   match H in (_ == a) return (inl a₁ == inl a) with
    refl _ => refl (inl a₁ : A + B)
   end.

Definition inr_equal {A B} (b₁ b₂ : B) :
  (b₁ == b₂) → @Id (A + B) (inr b₁) (inr b₂)
:= λ H : b₁ == b₂,
   match H in (_ == b) return (inr b₁ == inr b) with
    refl _ => refl (inr b₁ : A + B)
   end.

(* Expression 2.12.1 *)

Definition inl_eq_equiv {A B} (a₁ a₂ : A) :
  @Id (A + B) (inl a₁) (inl a₂) ≃ (a₁ == a₂).
Proof.
apply (existT _ (inl_inversion a₁ a₂)).
apply qinv_isequiv.
apply (existT _ (inl_equal a₁ a₂)).
split; [ intros p; destruct p; reflexivity | idtac ].
intros p; simpl.
unfold "◦", "~~", id; simpl.
refine (match p with refl _ => _ end).
reflexivity.
Defined.

(* Expression 2.12.2 *)

Definition inr_eq_equiv {A B} (b₁ b₂ : B) :
  @Id (A + B) (inr b₁) (inr b₂) ≃ (b₁ == b₂).
Proof.
apply (existT _ (inr_inversion b₁ b₂)).
apply qinv_isequiv.
apply (existT _ (inr_equal b₁ b₂)).
split; [ intros p; destruct p; reflexivity | idtac ].
intros p; simpl.
unfold "◦", "~~", id; simpl.
refine (match p with refl _ => _ end).
reflexivity.
Defined.

(* Expression 2.12.3 *)

Definition inl_inr_equiv {A B} (a : A) (b : B) : inl a == inr b ≃ ⊥.
Proof.
assert (inl a == inr b → ⊥) as f.
 intros p.
 change (match (inl a : A + B) with inl _ => False | inr _ => True end).
 rewrite p; constructor.

 apply (existT _ f), qinv_isequiv.
 assert (⊥ → inl a == inr b) as g by (intros H; contradiction).
 apply (existT _ g); split; intros x; contradiction.
Defined.

(* Expression 2.12.4 *)

Definition inl_family {A B a₀} (x : A + B) : U := inl a₀ == x.
Definition inr_family {A B b₀} (x : A + B) : U := inr b₀ == x.

Definition code {A B} a₀ : A + B → U :=
  λ x,
  match x with
  | inl a => a₀ == a
  | inr b => ⊥
  end.

(* I did it the reverse way they did: that 2.12.1 and 2.12.3 imply 2.12.5: *)

Theorem hott_2_12_5 {A B} a₀ : ∀ x : A + B, (inl a₀ == x) ≃ code a₀ x.
Proof.
intros.
destruct x; [ apply inl_eq_equiv | apply inl_inr_equiv ].
Defined.

(* let's see 'their' proof... *)

Definition encode {A B} a₀ (x : A + B) : ∀ (p : inl a₀ == x), code a₀ x :=
  λ p, transport (code a₀) p (refl a₀).

Definition decode {A B} a₀ (x : A + B) : ∀ (c : code a₀ x), (inl a₀ == x) :=
  match x return (code a₀ x → inl a₀ == x) with
  | inl a => ap inl
  | inr b => λ f, match f return inl a₀ == inr b with end
  end.

Definition encode_decode {A B} a₀ (x : A + B) :
  encode a₀ x ◦ decode a₀ x ~~ id.
Proof. intros y; destruct x, y; reflexivity. Defined.

Definition decode_encode {A B} a₀ (x : A + B) :
  decode a₀ x ◦ encode a₀ x ~~ id.
Proof. intros y; destruct x, y; reflexivity. Defined.

Theorem hott_2_12_5_bis {A B} a₀ : ∀ x : A + B, (inl a₀ == x) ≃ code a₀ x.
Proof.
intros.
apply (existT _ (encode a₀ x)), qinv_isequiv.
apply (existT _ (decode a₀ x)).
split; [ apply encode_decode | apply decode_encode ].
Defined.

(* 2.12.1 again *)

Definition inl_eq_equiv_bis {A B} (a₁ a₂ : A) :
  @Id (A + B) (inl a₁) (inl a₂) ≃ (a₁ == a₂).
Proof.
eapply equiv_compose; [ apply hott_2_12_5_bis | apply ideqv ].
Defined.

(* 2.12.3 again *)

Definition inl_inr_equiv_bis {A B} (a : A) (b : B) : inl a == inr b ≃ ⊥.
Proof.
eapply equiv_compose; [ apply hott_2_12_5_bis | apply ideqv ].
Defined.

(* and what about 2.12.2 ? *)

Definition code_r {A B} b₀ : A + B → U :=
  λ x,
  match x with
  | inl a => ⊥
  | inr b => b₀ == b
  end.

Definition encode_r {A B} b₀ (x : A + B) (p : inr b₀ == x) : code_r b₀ x :=
  transport (code_r b₀) p (refl b₀).

Definition decode_r {A B} b₀ (x : A + B) (c : code_r b₀ x) : (inr b₀ == x) :=
  match x return (code_r b₀ x → inr b₀ == x) with
  | inl a => λ f, match f return inr b₀ == inl a with end
  | inr b => ap inr
  end c.

Definition encode_r_decode_r {A B} b₀ (x : A + B) :
  encode_r b₀ x ◦ decode_r b₀ x ~~ id.
Proof. intros y; destruct x, y; reflexivity. Defined.

Definition decode_r_encode_r {A B} b₀ (x : A + B) :
  decode_r b₀ x ◦ encode_r b₀ x ~~ id.
Proof. intros y; destruct x, y; reflexivity. Defined.

Theorem hott_2_12_5_ter {A B} b₀ : ∀ x : A + B, (inr b₀ == x) ≃ code_r b₀ x.
Proof.
intros.
apply (existT _ (encode_r b₀ x)), qinv_isequiv.
apply (existT _ (decode_r b₀ x)).
split; [ apply encode_r_decode_r | apply decode_r_encode_r ].
Defined.

Definition inr_eq_equiv_bis {A B} (b₁ b₂ : B) :
  @Id (A + B) (inr b₁) (inr b₂) ≃ (b₁ == b₂).
Proof.
eapply equiv_compose; [ apply hott_2_12_5_ter | apply ideqv ].
Defined.

(* In particular, theorem 2.12.5 implies *)

Definition encode_inl_inl {A B} a₀
  : ∀ a, (@Id (A + B) (inl a₀) (inl a)) → (a₀ == a)
  := λ a, encode a₀ (inl a).

Definition encode_inl_inr {A B} a₀
  : ∀ b, (@Id (A + B) (inl a₀) (inr b)) → ⊥
  := λ b, encode a₀ (inr b).

(* Remark 2.12.6. In particular, since the two-element type 2 is
   equivalent to 1+1, we have 0₂ ≠ 1₂ *)

Definition bool_unit_unit : bool → unit + unit :=
  λ b, match b with true => inr tt | false => inl tt end.

Definition hott_2_12_6 : false ≠≠ true :=
  λ p, encode_inl_inr tt tt (ap bool_unit_unit p).

(* action of transport in coproduct types *)

Definition transport_coprod_l {X} {x₁ x₂ : X} (p : x₁ == x₂) {A B} : ∀ a,
  transport (λ x, (A x + B x)%type) p (inl a) == inl (transport A p a)
:= λ a,
   match p with
   | refl _ => refl (inl (transport A (refl x₁) a))
   end.

Definition transport_coprod_r {X} {x₁ x₂ : X} (p : x₁ == x₂) {A B} : ∀ b,
  transport (λ x, (A x + B x)%type) p (inr b) == inr (transport B p b)
:= λ b,
   match p with
   | refl _ => refl (inr (transport B (refl x₁) b))
   end.

(* 2.13 Natural numbers *)

Module ℕ.

Fixpoint code m n : U :=
  match (m, n) with
  | (0, 0) => unit
  | (S m, 0) => ⊥
  | (0, S n) => ⊥
  | (S m, S n) => code m n
  end.

Fixpoint r n : code n n :=
  match n with
  | 0 => tt
  | S m => r m
  end.

Definition encode (m n : nat) : m == n → code m n :=
  λ p, transport (code m) p (r m).

Definition decode (m n : nat) : code m n → m == n.
Proof.
revert m n.
fix 1; rename decode0 into IHn.
intros m n p.
destruct m.
 destruct n; [ reflexivity | refine (match p with end) ].

 destruct n; [ refine (match p with end) | simpl in p ].
 apply ap, IHn, p.
Defined.

Theorem decode_encode {m n} : ∀ p, decode m n (encode m n p) == p.
Proof.
intros p.
destruct p; simpl; unfold id; simpl.
induction m; [ reflexivity | simpl ].
apply (ap (ap S)) in IHm; assumption.
Defined.

Theorem encode_decode {m n} : ∀ c, encode m n (decode m n c) == c.
Proof.
intros c.
revert n c; induction m; intros.
 simpl in c.
 destruct n, c; reflexivity.

 simpl in c.
 destruct n; [ refine (match c with end) | simpl ].
 unfold encode.
 rewrite <- (hott_2_3_10 S (code (S m)) (decode m n c)).
 apply IHm.
Defined.

Theorem hott_2_13_1 : ∀ m n, (m == n) ≃ code m n.
Proof.
intros.
apply (existT _ (encode m n)), qinv_isequiv.
apply (existT _ (decode m n)).
unfold "◦", "~~", id; simpl.
split; intros p; [ apply encode_decode | apply decode_encode ].
Defined.

Definition hott_2_13_2 {m} : S m == 0 → ⊥ := encode (S m) 0.

Definition hott_2_13_3 m n : (S m == S n) → (m == n) :=
  λ p, decode m n (encode (S m) (S n) p).

End ℕ.

(* 2.14 Example: equality of structures *)

Definition SemigroupStr A :=
  Σ (m : A → A → A), Π (x : A), Π (y : A), Π (z : A),
  m x (m y z) == m (m x y) z.

Definition Semigroup := Σ (A : U), SemigroupStr A.

(* 2.14.1 Lifting equivalences *)

Check (λ A B (e : A ≃ B), transport SemigroupStr (ua e)).
(* λ (A B : Type) (e : A ≃ B), transport SemigroupStr (ua e)
     : ∀ A B : Type, A ≃ B → SemigroupStr A → SemigroupStr B *)

(* hott_2_1_4
     : ∀ (A : Type) (x y z w : A) (p : x == y) (q : y == z)
       (r : z == w),
       (p == p • refl y) * (p == refl x • p) *
       ((p • p⁻¹ == refl x) * (p⁻¹ • p == refl y)) *
       (p⁻¹⁻¹ == p) * (p • (q • r) == p • q • r) *)

(* @hott_2_3_9
     : ∀ (A : Type) (x y z : A) (P : A → U) (p : x == y)
       (q : y == z) (u : P x),
       transport P q (transport P p u) == transport P (p • q) u *)

Definition SemigroupStr_equiv {A B} : A ≃ B → SemigroupStr A ≃ SemigroupStr B.
Proof.
intros e.
eapply (existT _ (transport SemigroupStr (ua e))), qinv_isequiv.
eapply (existT _ (transport SemigroupStr (ua e)⁻¹)).
split; intros g.
 eapply compose; [ apply hott_2_3_9 | idtac ].
 rewrite invert_compose; reflexivity.

 eapply compose; [ apply hott_2_3_9 | idtac ].
 rewrite compose_invert; reflexivity.
Defined.

Definition Assoc X m :=
  Π (x : X), Π (y : X), Π (z : X), m x (m y z) == m (m x y) z.

Check (λ A B (e : A ≃ B), Π_type.pair_eq (ua e) (refl _)).

Check
  (λ A B (e : A ≃ B) m a,
   transport SemigroupStr (ua e) (existT _ m a)).

Print cartesian.pair_eq.

(* @cartesian.pair_eq
     : ∀ (A B : Type) (x y : A * B),
       (cartesian.pr₁ x == cartesian.pr₁ y) *
       (cartesian.pr₂ x == cartesian.pr₂ y) → x == y *)
(* @Π_type.pair_eq
     : ∀ (A : Type) (B : A → Type) (x y : A) (p : x == y)
       (u : B x), existT B x u == existT B y (transport B p u) *)

Definition titi {A B} (e : A ≃ B) (m : A → A → A) (a : Assoc A m) :
  let m' : B → B → B := transport (λ X, X → X → X) (ua e) m in
(*
  let a' := transport _ (Π_type.pair_eq (ua e) (refl m')) a in
*)
  ∃ a' : Assoc B m',
(**)
  transport SemigroupStr (ua e) (existT _ m a) == existT _ m' a'.
Proof.
intros.
Check @ex_2_4_9.
(* ex_2_4_9
     : ∀ (A : Type) (x y : A) (p : x == y) (P : A → U), qinv (transport P p) *)
Check (@ex_2_4_9 U A B (ua e) id).
(* ex_2_4_9 U A B (ua e) id
     : qinv (transport id (ua e)) *)
set (p := @ex_2_4_9 U A B (ua e) id).
assert (∀ b₁ b₂,
  m' b₁ b₂ ==
  transport id (ua e)
    (m (transport id (ua e)⁻¹ b₁) (transport id (ua e)⁻¹ b₂))).
intros b₁ b₂.
subst m'.
Focus 2.
Check ex_2_7_4.

bbb. je comprends que dalle, chuis complètement largué...

generalize p; intros q.
destruct q as (f, (α, β)).
unfold "◦", "~~" in α, β.
rewrite α.
bbb.

destruct p as (f, Hf).

Check (transport SemigroupStr).
Check (existT (Assoc B) m').
set (cartesian.pair_eq (cartesian.pr₁ (A, B) == cartesian.pr₂ (A, B), _)).
simpl in x.
Check (λ x, cartesian.pair_eq (ua e, x)).

The term "(ua e, x)" has type "((A == B) * ?B0)%type"
while it is expected to have type
 "((cartesian.pr₁ ?x == cartesian.pr₁ ?y) *
   (cartesian.pr₂ ?x == cartesian.pr₂ ?y))%type".
Check (Π_type.pair_eq (ua e) (refl m')).
pose proof @transport as H1.
Check (@transport (B → B → B) (Assoc B) m' m' (refl m')).
Check (@transport).
Check (@transport (A → A → A) (Assoc A) m m (refl m) a).
Check (λ A P x y, @transport A P x y).
Check (λ A B x y p, @Π_type.pair_eq (A → A → A) B x y p Assoc).
bbb.

Check (refl m').
(* Π_type.pair_eq = 
     : ∀ (A : Type) (B : A → Type) (x y : A) (p : x == y) 
       (u : B x), existT B x u == existT B y (transport B p u)

Arguments A, B, x, y are implicit and maximally inserted
*)
pose proof (Assoc B m').
pose proof @Π_type.pair_eq.
pose proof (@Π_type.pair_eq U id A B (ua e)).
bbb.

Definition titi {A B} (e : A ≃ B) (m : A → A → A) (a : Assoc A m) :
  let m' : B → B → B := transport (λ X, X → X → X) (ua e) m in
  ∃ a' : Assoc B m',
  transport SemigroupStr (ua e) (existT _ m a) == existT _ m' a'.
Proof.
intros; subst m'.
bbb.

Definition titi {A B} (e : A ≃ B) (m : A → A → A) (a : Assoc A m) :
  let m' : B → B → B := transport (λ X, X → X → X) (ua e) m in
  let a' := transport _ (Π_type.pair_eq (ua e) (refl m')) a in
  transport SemigroupStr (ua e) (existT _ m a) == existT _ m' a'.

Definition titi {A B} (e : A ≃ B) (m : A → A → A)
    (a : ∀ x y z : A, m (m x y) z == m x (m y z)) :=
  let m' : B → B → B := transport (λ X, X → X → X) (ua e) m in
  let a' : ∀ x y z : B, m' (m' x y) z == m' x (m' y z)
    := transport _ (Π_type.pair_eq (ua e) (refl m')) aaa in
  transport SemigroupStr (ua e) (existT _ m a) == existT _ m' a'.

Definition titi {A B} (e : A ≃ B) (m : A → A → A) (a : Assoc A m) :
  let m' : B → B → B := transport (λ X, X → X → X) (ua e) m in
  ∃ a' : Assoc B (transport (λ X : Type, X → X → X) (ua e) m),
  transport SemigroupStr (ua e) (existT _ m a) == existT _ m' a'.
Proof.
intros.
subst m'; simpl.
Check (Assoc B (transport (λ X : Type, X → X → X) (ua e) m)).



Toplevel input, characters 0-370:
Error:
In environment
A : ?X3674
B : ?X3675
e : A ≃ B
m : A → A → A
aaa : ?X3676
a : ∀ x y z : A, m (m x y) z == m x (m y z)
m' := transport (λ X : ?X3678, X → X → X) (ua e) m : B → B → B
Unable to unify "?B" with "?B".

Proof.
intros.
subst m'; simpl.
bbb.

(* test *)

Theorem toto {A B} {f g : A → B} : f ~~ g → f == g.
Proof.
intros p.
bbb.
