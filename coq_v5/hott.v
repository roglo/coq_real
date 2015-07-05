(* experimentations on HoTT *)

Require Import Utf8 QArith.
Require Import NPeano.

Open Scope nat_scope.

(* hott section 1.12 *)

(*
Axiom random : ∀ A, A → A → bool.

Inductive Id {A} : A → A → Type :=
  | refl : ∀ x : A, Id x x
  | phony : ∀ x y : A, random A x y = true → Id x y.
*)
Inductive Id {A} x : A → Type :=
  | refl : Id x x.
(**)

Notation "x == y" := (Id x y) (at level 70).

(*
Definition indiscernability {A} C (x y : A) (p : x == y) : C x → C y.
Proof.
induction p as [| x y p]; [ intros H; assumption | idtac ].
intros H.
bbb.
*)

Definition indiscernability {A} C (x y : A) (p : x == y) :=
  match p return (C x → C _) with
  | refl => id
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
   | refl => c a
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
   | refl => λ _, id
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
Notation "g 'o' f" := (composite f g) (at level 40).
(* composite : ∀ A B C : Type, (A → B) → (B → C) → A → C *)

Theorem composite_assoc {A B C D} : ∀ (f : A → B) (g : B → C) (h : C → D),
  h o (g o f) = (h o g) o f.
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
  match x with existT a _ => a end.
Definition Σ_pr₂ {A B} (x : { y : A & B y }) : B (Σ_pr₁ x) :=
  match x with existT _ b => b end.

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
  | refl => id
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
  | refl => id
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
  (∀ x, f x = g x) → f = g.

Theorem AxB'_pair_proj {A B} : ∀ x : AxB' A B,
  AxB'_pair (AxB'_pr₁ x) (AxB'_pr₂ x) = x.
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
  match AxB'_pair_proj x in (_ = y) return (C y) with
  | eq_refl => H (AxB'_pr₁ x) (AxB'_pr₂ x)
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
     | refl => c x
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
     | refl => λ _ y, y
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
  | orT_introl Hna => Hna (andT_rect A B (λ _, A) (λ a _, a) Hand)
  | orT_intror Hnb => Hnb (andT_rect A B (λ _, B) (λ _ b, b) Hand)
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
  | refl => c x
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
  | refl => refl x
  end.
Notation "p '⁻¹'" := (invert p) (at level 10).

Lemma hott_2_1_1 : ∀ A (x : A), refl x = (refl x)⁻¹.
Proof. reflexivity. Qed.

Definition compose {A} {x y z : A} (p : x == y) : y == z → x == z :=
  match p with
  | refl => id
  end.
Notation "p • q" := (compose p q) (at level 40, left associativity).

(* same theorem with another proof *)
Definition compose2 {A} {x y z : A} (p : x == y) : y == z → x == z :=
  λ q,
  match p with
  | refl =>
      match q in (_ == t) return (x == t) with
      | refl => p
      end
 end.

(* proof that the proofs are equal *)
Definition compose_compose2 {A} {x y z : A} : ∀ (p : x == y) (q : y == z),
    compose p q = compose2 p q :=
  λ p q,
  match q return (p • q = compose2 p q) with
  | refl =>
      match p return (p • refl _ = compose2 p (refl _)) with
      | refl => eq_refl
      end
  end.

Theorem fold_compose : ∀ A (x y z : A) p,
   match p with
   | refl => id
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
     | refl => refl (refl x • refl x)
     end).

Definition hott_2_1_4_i_2 {A} {x y : A} : ∀ (p : x == y),
    p == refl x • p
 := (λ (p : x == y),
   match p return (p == refl _ • p) with
   | refl => refl (refl x • refl x)
   end).

Lemma hott_2_1_4_ii_1 {A} {x y z w : A} :
  ∀ (p : x == y) (q : y == z) (r : z == w),
  p⁻¹ • p == refl y.
Proof.
intros p q r.
induction p; constructor.
Qed.

Lemma hott_2_1_4_ii_2 {A} {x y z w : A} :
  ∀ (p : x == y) (q : y == z) (r : z == w),
  p • p⁻¹ == refl x.
Proof.
intros p q r.
induction p; constructor.
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
induction r.
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
induction q.
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
induction p, α; simpl.
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
induction r, β; simpl.
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
eapply compose; [ apply hott_2_1_4_iv | idtac ].
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
eapply compose; [ apply hott_2_1_4_iv | idtac ].
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
induction α as (p).
induction β as (r).
induction p, r.
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
  | refl => refl (f x)
  end.

Theorem hott_2_2_1 {A B} : ∀ (f : A → B) x, ap f (refl x) = refl (f x).
Proof. constructor. Qed.

Theorem hott_2_2_2_i {A B} : ∀ (f : A → B) x y z (p : x == y) (q : y == z),
  ap f (p • q) = ap f p • ap f q.
Proof. induction p, q; constructor. Qed.

Theorem hott_2_2_2_ii {A B} : ∀ (f : A → B) x y (p : x == y),
  ap f (p⁻¹) = (ap f p)⁻¹.
Proof. induction p; constructor. Qed.

Definition hott_2_2_2_iii {A B C x y}
  : ∀ (f : A → B) (g : B → C) (p : x == y),
    ap g (ap f p) == ap (g o f) p
  := λ f g p,
     match p with refl => refl (ap g (ap f (refl x))) end.

Definition hott_2_2_2_iv {A} {x y : A} : ∀ (p : x == y), ap id p == p
  := λ p, match p with refl => refl (refl x) end.

(* hott section 2.3 *)

(* p* = transport P p *)
Definition transport {A} P {x y : A} (p : x == y) : P x → P y :=
  match p with
  | refl => id
  end.

Check @transport.
(* transport =
     : ∀ (A : Type) (P : A → Type) (x y : A), x == y → P x → P y *)

(* Notation "p _*" := (transport _ p) (at level 5). *)

(* lemma 2.3.2 path lifting property *)

Definition lift {A P} {x y : A} (u : P x) (p : x == y)
  : existT _ x u == existT _ y (transport P _ u)
  := match p with
     | refl => refl (existT P x (transport P (refl x) u))
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
  | refl => refl (f x)
  end.

(* lemma hott_2_3_5 *)

Definition transportconst {A : U} {x y : A}
  : ∀ B (P := λ _, B) (p : x == y) (b : B), transport P p b == b
  := λ B (P := λ _, B) p b,
     match p return (transport P p b == b) with
     | refl => refl b
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
  := match p with refl => refl (apd f (refl x)) end.

Print hott_2_3_8.

Definition hott_2_3_9 {A x y z} :
    ∀ (P : A → U) (p : x == y) (q : y == z) (u : P x),
    transport P q (transport P p u) == transport P (p • q) u :=
  λ P p q u,
  match q with
  | refl =>
      match p with
      | refl => refl (transport P (refl x • refl x) u)
      end
  end.

Definition hott_2_3_10 {A B x y} :
    ∀ (f : A → B) (P : B → U) (p : x == y) (u : P (f x)),
    transport (P o f) p u == transport P (ap f p) u
 := λ f P p u,
    match p with
    | refl => refl (transport P (ap f (refl x)) u)
    end.

Definition hott_2_3_11 {A x y} : ∀ (P Q : A → U) (f : Π (x : A), P x → Q x),
  ∀ (p : x == y) (u : P x), transport Q p (f x u) == f y (transport P p u)
  := λ P Q f p u,
     match p with
     | refl => refl (f x (transport P (refl x) u))
     end.

(* hott section 2.4 - Homotopies and Equivalences *)

Definition homotopy {A B} (f g : A → B) := Π (x : A), (f x == g x).

Notation "f '~~' g" := (homotopy f g) (at level 110, g at level 110).

Definition homotopy_refl {A B} : reflexive _ (@homotopy A B) :=
  λ _ _, refl _.

Definition homotopy_refl2 {A B} : Π (f : A → B), (f ~~ f) :=
  λ _ _, refl _.

Definition homotopy_sym {A B} : symmetric _ (@homotopy A B) :=
  λ f g (p : f ~~ g) x,
  match p x with refl => refl (f x) end.

Definition homotopy_sym2 {A B} : Π (f : A → B), Π (g : A → B),
    (f ~~ g) → (g ~~ f) :=
  λ f g (p : f ~~ g) x,
  match p x with refl => refl (f x) end.

Definition homotopy_trans {A B} : transitive _ (@homotopy A B) :=
  λ f g h (p : f ~~ g) (q : g ~~ h) x,
  match q x with
  | refl => p x
  end.

Definition homotopy_trans2 {A B}
  : Π (f : A → B), Π (g : A → B), Π (h : A → B),
    (f ~~ g) → (g ~~ h) → (f ~~ h)
  := λ f g h (p : f ~~ g) (q : g ~~ h) x,
     match q x with
     | refl => p x
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
     | refl =>
         match
           match H x as q return (q == q • refl _) with
           | refl => refl (refl (f x) • refl (f x))
           end
         with
         | refl => refl (id (H x))
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
 eapply compose in p; [ idtac | apply hott_2_1_4_iv ].
 eapply compose in p.
  unfold id in p; simpl in p.
  eapply compose in p; [ idtac | apply hott_2_1_4_i_1 ].
  eapply invert, compose in p; [ idtac | apply hott_2_1_4_iv ].
  eapply compose in p.
   eapply compose in p; [ eassumption | apply hott_2_1_4_i_1 ].

   eapply dotl, invert.
   eapply hott_2_1_4_ii_2; reflexivity.

  eapply dotl, invert.
  eapply hott_2_1_4_ii_2; reflexivity.
Qed.

(* quasi-inverse *)

Inductive qinv {A B} (f : A → B) : Type :=
  qi : ∀ (g : B → A) (α : (f o g) ~~ id) (β : (g o f) ~~ id), qinv f.

Example ex_2_4_7 A : qinv (id : A → A) := qi id id refl refl.
Print ex_2_4_7.

Example ex_2_4_8_i A : ∀ x y z : A, ∀ (p : x == y),
  qinv (λ (q : y == z), p • q).
Proof.
intros.
apply qi with (g := λ q, p⁻¹ • q).
 intros t; unfold id, "o"; simpl.
 eapply compose; [ idtac | apply invert, hott_2_1_4_i_2 ].
 eapply compose; [ apply hott_2_1_4_iv | apply dotr ].
 eapply hott_2_1_4_ii_2; reflexivity.

 intros t; unfold id, "o"; simpl.
 eapply compose; [ idtac | apply invert, hott_2_1_4_i_2 ].
 eapply compose; [ apply hott_2_1_4_iv | apply dotr ].
 eapply hott_2_1_4_ii_1; reflexivity.
Qed.

Example ex_2_4_8_i_bis A : ∀ x y z : A, ∀ (p : x == y),
  qinv (λ (q : y == z), p • q)
  := λ x y z p,
     qi (λ q : y == z, p • q) (λ q : x == z, p ⁻¹ • q)
       (λ t : x == z,
        hott_2_1_4_iv p (p ⁻¹) t • (hott_2_1_4_ii_2 p (refl y) (refl y) •r t)
        • (hott_2_1_4_i_2 t) ⁻¹)
       (λ t : y == z,
        hott_2_1_4_iv (p ⁻¹) p t • (hott_2_1_4_ii_1 p (refl y) (refl y) •r t)
        • (hott_2_1_4_i_2 t) ⁻¹).

Example ex_2_4_8_ii A : ∀ x y z : A, ∀ (p : x == y),
  qinv (λ (q : z == x), q • p).
Proof.
intros.
apply qi with (g := λ q, q • p⁻¹).
 intros t; unfold id, "o"; simpl.
 eapply compose; [ idtac | apply invert, hott_2_1_4_i_1 ].
 eapply compose; [ eapply invert, hott_2_1_4_iv | apply dotl ].
 eapply hott_2_1_4_ii_1; reflexivity.

 intros t; unfold id, "o"; simpl.
 eapply compose; [ idtac | apply invert, hott_2_1_4_i_1 ].
 eapply compose; [ eapply invert, hott_2_1_4_iv | apply dotl ].
 eapply hott_2_1_4_ii_2; reflexivity.
Qed.

Example ex_2_4_8_ii_bis A : ∀ x y z : A, ∀ (p : x == y),
  qinv (λ (q : z == x), q • p)
  := λ x y z p,
     qi (λ q : z == x, q • p) (λ q : z == y, q • p ⁻¹)
       (λ t : z == y,
        (hott_2_1_4_iv t (p ⁻¹) p) ⁻¹
        • (t •l hott_2_1_4_ii_1 p (refl y) (refl y)) •
        (hott_2_1_4_i_1 t) ⁻¹)
       (λ t : z == x,
        (hott_2_1_4_iv t p (p ⁻¹)) ⁻¹
        • (t •l hott_2_1_4_ii_2 p (refl y) (refl y)) •
        (hott_2_1_4_i_1 t) ⁻¹).

Example ex_2_4_9 A x y : ∀ (p : x == y) (P : A → U), qinv (transport P p).
Proof.
intros.
apply qi with (g := transport P (p⁻¹)).
 intros z; unfold id, "o"; simpl.
 eapply compose; [ apply hott_2_3_9 | idtac ].
 induction p; reflexivity.

 intros z; unfold id, "o"; simpl.
 eapply compose; [ apply hott_2_3_9 | idtac ].
 induction p; reflexivity.
Qed.

Example ex_2_4_9_bis A x y : ∀ (p : x == y) (P : A → U), qinv (transport P p)
  := λ p P,
 qi (transport P p) (transport P (p ⁻¹))
   (λ z : P y,
    hott_2_3_9 P (p ⁻¹) p z
    • match p return (∀ t, transport P (p ⁻¹ • p) t == t) with
      | refl => refl
      end z)
   (λ z : P x,
    hott_2_3_9 P p (p ⁻¹) z
    • match p return (∀ t, transport P (p • p ⁻¹) t == t) with
      | refl => refl
      end z).

Definition equiv_prop {A B} isequiv :=
  ∀ f : A → B,
  (qinv f → isequiv f) ∧∧
  (isequiv f → qinv f) ∧∧
  (∀ e₁ e₂ : isequiv f, e₁ == e₂).

Check @equiv_prop.

Definition isequiv {A B} f :=
  ((Σ (g : B → A), (f o g ~~ id)) * (Σ (h : B → A), (h o f ~~ id)))%type.

Definition equivalence_isequiv_1 {A B} : equiv_prop (@isequiv A B).
Proof.
unfold equiv_prop; intros f.
split; [ idtac | split ].
 intros H; unfold isequiv; simpl.
 refine (match H with qi _ _ _ => _ end).
 split; econstructor; eassumption.

 intros H; unfold isequiv in H; simpl in H.
 destruct H as (Hg, Hh).
 destruct Hg as (g, p).
 destruct Hh as (h, q).
 econstructor; [ eassumption | idtac ].
 intros x.
  unfold homotopy in p, q.
  assert (∀ y, (h o f o g) y == g y) as H1 by (intros; apply q).
  assert (∀ y, (h o f o g) y == h y) as H2.
   intros; rewrite <- composite_assoc.
   unfold "o"; apply ap, p.

   transitivity ((h o f) x); [ idtac | apply q ].
   assert (∀ y, g y == h y) as H3; [ idtac | apply H3 ].
   intros.
   transitivity ((h o f o g) y); [ symmetry; apply H1 | apply H2 ].

 intros.
 unfold isequiv in e₁, e₂.
 destruct e₁ as (H1, H2).
 destruct e₂ as (H3, H4).
 induction H1 as (g1, p1).
 induction H2 as (h1, q1).
 induction H3 as (g2, p2).
 induction H4 as (h2, q2).
 unfold "~~", id in p1, q1, p2, q2.
 unfold "~~", id.
Admitted. (* proof postponed, they say, to sections §2.6, §2.7 and §4.3...
bbb.
*)

Check isequiv.

Definition equivalence A B := Σ (f : A → B), isequiv f.

Print Grammar constr.

Notation "A ≃ B" := (equivalence A B) (at level 70).

Lemma hott_2_4_12_i : ∀ A, A ≃ A.
Proof.
intros.
apply existT with (x := id).
split; apply existT with (x := id); reflexivity.
Qed.

Definition hott_2_4_12_i_bis : ∀ A, A ≃ A :=
  λ A,
  existT isequiv id
  (existT (λ g, id o g ~~ id) id refl, existT (λ h, h o id ~~ id) id refl).

Lemma hott_2_4_12_ii : ∀ A B, A ≃ B → B ≃ A.
Proof.
intros A B f.
induction f as (f, H).
pose proof (@equivalence_isequiv_1 A B f) as Heq.
destruct Heq as (Hqe, (Heq, Hee)).
generalize H; intros finv.
apply Heq in finv.
destruct finv as (finv, α, β).
apply existT with (x := finv).
split; apply existT with (x := f); assumption.
Qed.

Definition quasi_inv {A B} (f : A ≃ B) : B ≃ A :=
  sigT_rect (λ _, B ≃ A)
    (λ g H,
     match equivalence_isequiv_1 g with
     | conjt _ (conjt Heq _) =>
         match Heq H with
         | qi finv1 α β =>
             existT isequiv finv1
               (existT (λ g, finv1 o g ~~ id) g β,
                existT (λ h, h o finv1 ~~ id) g α)
         end
      end) f.

Print sigT_rect. (* à faire… *)

Lemma hott_2_4_12_iii : ∀ A B C, A ≃ B → B ≃ C → A ≃ C.
Proof.
intros A B C eqf eqg.
destruct eqf as (f, eqf).
destruct eqg as (g, eqg).
pose proof (@equivalence_isequiv_1 A B f) as H.
destruct H as (Hfqe, (Hfeq, Hfee)).
apply Hfeq in eqf.
induction eqf as (f¹, αf, βf).
pose proof (@equivalence_isequiv_1 B C g) as H.
destruct H as (Hgqe, (Hgeq, Hgee)).
apply Hgeq in eqg.
induction eqg as (g¹, αg, βg).
unfold equivalence.
apply existT with (x := g o f).
unfold isequiv.
split.
 apply existT with (x := f¹ o g¹).
 intros c.
 pose proof αf (g¹ c) as H.
 apply (ap g) in H.
 unfold id in H; simpl in H.
 transitivity (g (g¹ c)); [ assumption | apply αg ].

 apply existT with (x := f¹ o g¹).
 intros a.
 pose proof βg (f a) as H.
 apply (ap f¹) in H.
 unfold id in H; simpl in H.
 transitivity (f¹ (f a)); [ assumption | apply βf ].
Qed.

(* 2.5 The higher groupoid structure of type formers *)

Check @transport.
(* transport
     : ∀ (A : Type) (P : A → Type) (x y : A), x == y → P x → P y *)
Check transport.
(* transport
     : ∀ (P : ?3610 → Type) (x y : ?3610), x == y → P x → P y *)

Theorem transport_pair : ∀ A B C (x y : A) (p : x == y) b c,
  transport (λ z, (B z * C z)%type) p (b, c) ==
  (transport B p b, transport C p c).
Proof.
intros.
destruct p; reflexivity.
Qed.

Definition transport_pair_bis {A} B C x y (p : x == y) b c
  : transport (λ z : A, (B z * C z)%type) p (b, c) ==
    (transport B p b, transport C p c)
  := match p with
     | refl => refl (transport B (refl x) b, transport C (refl x) c)
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

Theorem pair_eq {A B} {x y : A * B} :
  (pr₁ x == pr₁ y) * (pr₂ x == pr₂ y) → (x == y).
Proof.
intros p.
destruct x as (a, b).
destruct y as (a', b').
simpl in p.
destruct p as (p, q).
destruct p, q; reflexivity.
Defined.

Theorem hott_2_6_2 {A B} : ∀ x y : A * B,
  (pr₁ x == pr₁ y) * (pr₂ x == pr₂ y) ≃ (x == y).
Proof.
intros.
set (f := hott_2_6_1 x y).
set (g := @pair_eq A B x y).
apply hott_2_4_12_ii.
apply existT with (x := f).
pose proof (equivalence_isequiv_1 f) as H.
destruct H as (H, _); apply H; clear H.
apply (qi f) with (g := g).
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
  | refl => refl (pr₁ x)
  end.

Definition ap_pr₂ {A B} {x y : A * B} : x == y → pr₂ x == pr₂ y :=
  λ p,
  match p in (_ == z) return (pr₂ x == pr₂ z) with
  | refl => refl (pr₂ x)
  end.

Theorem ap_pr₁_pair {A B} : ∀ (x y : A * B) (p : pr₁ x == pr₁ y) q,
  ap_pr₁ (pair_eq (p, q)) == p.
Proof.
intros.
destruct x as (a, b).
destruct y as (a', b').
simpl in p, q.
induction p, q; reflexivity.
Qed.

Theorem ap_pr₂_pair {A B} : ∀ (x y : A * B) p (q : pr₂ x == pr₂ y),
  ap_pr₂ (pair_eq (p, q)) == q.
Proof.
intros.
destruct x as (a, b).
destruct y as (a', b').
simpl in p, q.
induction p, q; reflexivity.
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

Theorem hott_2_7_2 {A} : ∀ (P : A → U) (w w' : Σ (x : A), P x),
  (w == w') ≃ Σ (p : pr₁ w == pr₁ w'), transport P p (pr₂ w) == pr₂ w'.
Proof.
intros.
assert (w == w' → Σ (p : pr₁ w == pr₁ w'), transport P p (pr₂ w) == pr₂ w')
  as f.
 intros p.
 destruct p; simpl.
 apply existT with (x := refl (pr₁ w)); reflexivity.

  assert ((Σ (p : pr₁ w == pr₁ w'), transport P p (pr₂ w) == pr₂ w') → w == w')
    as g.
   intros p.
   destruct w as (w₁, w₂).
   destruct w' as (w'₁, w'₂); simpl.
   simpl in p.
   destruct p as (p, q).
   destruct p, q; reflexivity.

   apply existT with (x := f).
   pose proof (equivalence_isequiv_1 f) as H.
   destruct H as (H, _); apply H; clear H.
   apply (qi f) with (g := g).
    intros r; unfold id; simpl.
    destruct r as (p, q).
    destruct w as (a, b).
    destruct w' as (a', b').
    simpl in p, q, f, g; simpl.
    destruct p, q; simpl.
    simpl in f, g.
bbb.

 intros p; unfold id; simpl.
 destruct p, x; reflexivity.

bbb.
 destruct w as (a, r).
 destruct w' as (b, s); simpl.
 simpl in f.
