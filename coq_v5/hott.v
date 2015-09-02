(* experimentations on HoTT *)
(* requires coq 8.5 *)

Require Import Utf8 QArith.
Require Import NPeano.

(* no default implicit without arguments *)
Arguments eq_refl [A] x.

Notation "⊥" := False.
Notation "( x , y ) '_{' P }" := (existT P x y)
  (at level 0, format "'[' ( x ,  y ) _{ P } ']'", only parsing).

Open Scope nat_scope.

(* hott section 1.12 *)

Definition indiscernability {A} C (x y : A) (p : x = y) :
  C x → C y
:=
  match p return (C x → C _) with
  | eq_refl _ => id
  end.

Theorem indiscernability_prop : ∀ A C (x : A),
  indiscernability C x x (eq_refl x) = id.
Proof. reflexivity. Qed.

(* hott section 1.12.1 *)

Theorem path_induction0 : ∀ A C c,
  ∃ (f : ∀ (x y : A) (p : x = y), C x y p),
  ∀ x, f x x (eq_refl x) = c x.
Proof.
intros A C c.
exists
  (λ a _ p,
   match p return (C _ _ p) with
   | eq_refl _ => c a
   end).
reflexivity.
Qed.

Theorem based_path_induction : ∀ A a C c,
  ∃ (f : ∀ (x : A) (p : a = x), C x p),
  f a (eq_refl a) = c.
Proof.
intros A a C c.
exists
  (λ _ p,
   match p return (∀ D, D _ (eq_refl _) → D _ p) with
   | eq_refl _ => λ _, id
   end C c).
reflexivity.
Qed.

(* hott section 1.12.2 *)

Theorem path_based_path_induction_iff :
  (∀ A (x : A) C c,
   ∃ (f : ∀ (x y : A) (p : x = y), C x y p),
   ∀ x, f x x (eq_refl x) = c x)
  ↔
  (∀ A a C c,
   ∃ (f : ∀ (x : A) (p : a = x), C x p),
   f a (eq_refl a) = c).
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
  let (a, b) return ((AxB_pr₁ x, AxB_pr₂ x) = x) := x in
  eq_refl (a, b).

Definition ind_AxB {A B} C (g : ∀ x y, C (x, y)) (x : A * B) :=
  match uupt x return (C _ → C _) with
  | eq_refl _ => id
  end (g (AxB_pr₁ x) (AxB_pr₂ x)).

Theorem verif_ind_AxB_eq_def : ∀ A B C (g : ∀ x y, C (x, y)) (a : A) (b : B),
  ind_AxB C g (a, b) = g a b.
Proof. reflexivity. Qed.

Definition Σ_uupt {A B} (x : {y : A & B y}) :=
 let (a, b) return (existT _ (Σ_pr₁ x) (Σ_pr₂ x) = x) := x in
 eq_refl (existT _ a b).

Definition ind_Σ {A B} C (g : ∀ a (b : B a), C (existT _ a b))
    (x : {y : A & B y}) :=
  match Σ_uupt x with
  | eq_refl _ => id
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

Axiom simple_function_extensionality : ∀ A B (f g : ∀ x : A, B x),
  (∀ x, f x = g x) → f = g.

(* when need of extensionality and its reverse, rather consider using
   Π_type.funext, defined later, than this function_extensionality as
   extensionality axiom *)

Theorem AxB'_pair_proj {A B} : ∀ x : AxB' A B,
  AxB'_pair (AxB'_pr₁ x) (AxB'_pr₂ x) = x.
Proof.
intros x.
apply simple_function_extensionality.
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
  | eq_refl _ => H (AxB'_pr₁ x) (AxB'_pr₂ x)
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
  Π (C : Π (x : A), Π (y : A), (x = y) → U),
    (Π (x : A), C x x (eq_refl x))
    → Π (x : A), Π (y : A), Π (p : x = y), C x y p
  := λ C c x y p,
     match p with
     | eq_refl _ => c x
     end.

Theorem ind_eqA_def_eq {A} : ∀ C c (x : A), ind_eqA C c x x (eq_refl x) = c x.
Proof. reflexivity. Qed.

(* definition from §1.12.1 *)
Definition ind'_eqA {A} :
  Π (a : A),
  Π (C : Π (x : A), (a = x) → U), C a (eq_refl a)
  → Π (x : A), Π (p : a = x), C x p
  := λ a C P x p,
     match p with
     | eq_refl _ => λ _ y, y
     end C P.

Theorem ind'_eqA_def_eq {A} : ∀ (a : A) C c, ind'_eqA a C c a (eq_refl a) = c.
Proof. reflexivity. Qed.

(* alternative definition from ind_eqA *)
Definition ind'_eqA_bis {A} :
  Π (a : A),
  Π (C : Π (x : A), (a = x) → U), C a (eq_refl a)
  → Π (x : A), Π (p : a = x), C x p.
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
   not allow us to construct a function f : Π (x:A) Π (p:x=x) (p=eq_refl x)
   with the defining equation
          f(x,eq_refl_x) :≡ eq_refl_{eq_refl_x}    ? *)

(* Wrong explanation: I suppose it is because if there is y such that
   x = y, then there is another proof that x = x, because x = y
   implies y = x by symmetry and x = x, by transitivity, which creates
   another proof that x = x, ...
   ... which is different from eq_refl <- no, it is equal! *)

(* not sure *)

(* à voir... *)

(* Exercise 1.15. Show that indiscernability of identicals follows
   from path induction. *)

Definition path_induction {A} (C : Π (x : A), Π (y : A), Π (p : x = y), U)
    (c : Π (x : A), C x x (eq_refl x)) (x y : A) (p : x = y) : C x y p :=
  match p return (C _ _ p) with
  | eq_refl _ => c x
  end.

Theorem path_induction_def : ∀ A (x : A) C c,
  path_induction C c x x (eq_refl x) = c x.
Proof. reflexivity. Qed.

Theorem path_induction_indiscernability {A} :
  Π (C : A → U), Π (x : A), Π (y : A), x = y → C x → C y.
Proof.
intros C x y p px.
apply (path_induction (λ x y _, C x → C y) (λ _, id) x y p).
assumption.
Qed.

(* Chapter 2 *)

(* hott section 2.1 *)

Definition invert {A} {x y : A} (p : x = y) : y = x :=
  match p with
  | eq_refl _ => eq_refl x
  end.
Notation "p '⁻¹'" := (invert p)
  (at level 8, left associativity, format "'[v' p ']' ⁻¹").

Lemma hott_2_1_1 : ∀ A (x : A), eq_refl x = (eq_refl x)⁻¹.
Proof. reflexivity. Qed.

(* Lemma 2.1.2 *)

Definition compose {A} {x y z : A} : x = y → y = z → x = z :=
  λ p,
  match p with
  | eq_refl _ => id
  end.
Notation "p • q" := (compose p q) (at level 40, left associativity).

(* same theorem with another proof *)
Definition compose2 {A} {x y z : A} (p : x = y) : y = z → x = z :=
  λ q,
  match p with
  | eq_refl _ =>
      match q in (_ = t) return (x = t) with
      | eq_refl _ => p
      end
 end.

(* proof that the proofs are equal *)
Definition compose_compose2 {A} {x y z : A} : ∀ (p : x = y) (q : y = z),
    compose p q = compose2 p q :=
  λ p q,
  match q return (p • q = compose2 p q) with
  | eq_refl _ =>
      match p return (p • eq_refl _ = compose2 p (eq_refl _)) with
      | eq_refl _ => eq_refl _
      end
  end.

Theorem fold_compose : ∀ A (x y z : A) p,
   match p with
   | eq_refl _ => id
   end = @compose A x y z p.
Proof. reflexivity. Qed.

Lemma hott_2_1_2_def : ∀ A (x : A), eq_refl x = eq_refl x • eq_refl x.
Proof. reflexivity. Qed.

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

(* Lemma hott_2.1.4 ii_1 *)

Lemma compose_invert_l {A} {x y : A} : ∀ (p : x = y), p⁻¹ • p = eq_refl y.
Proof.
intros p; destruct p; reflexivity.
Qed.

(* Lemma 2.1.4 ii_2 *)

Definition compose_invert_r {A} {x y : A} : ∀ (p : x = y), p • p⁻¹ = eq_refl x
  := λ p, match p with eq_refl _ => eq_refl (eq_refl x) end.

Lemma hott_2_1_4_iii {A} {x y : A} : ∀ (p : x = y), (p⁻¹)⁻¹ = p.
Proof.
intros p; destruct p; reflexivity.
Qed.

(* Lemma hott_2_1_4_iv *)

Lemma compose_assoc {A} {x y z w : A} :
  ∀ (p : x = y) (q : y = z) (r : z = w),
  p • (q • r) = (p • q) • r.
Proof.
intros p q r; destruct p; reflexivity.
Qed.

Definition hott_2_1_4 A (x y z w : A)
    (p : x = y) (q : y = z) (r : z = w) :=
  ((@hott_2_1_4_i_1 A x y p, @hott_2_1_4_i_2 A x y p),
   (@compose_invert_r A x y p, @compose_invert_l A x y p),
   @hott_2_1_4_iii A x y p,
   @compose_assoc A x y z w p q r).

(* Theorem 2.1.6 (Eckmann-Hilton) *)

Definition Ω {A} (a : A) := (a = a).
Definition Ω2 {A} (a : A) := (eq_refl a = eq_refl a).

(* whiskering *)
Definition dotr {A} {a b c : A} {p q : a = b}
  (α : p = q) (r : b = c) : (p • r = q • r).
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

Notation "q '•l' β" := (dotl q β) (at level 50).

Definition ru {A} {a b : A} (p : a = b) : p = p • eq_refl b :=
  hott_2_1_4_i_1 p.

Check @ru.
(* ru
     : ∀ (A : Type) (a b : A) (p : a = b) → p = p • eq_refl b *)

Theorem dotr_rupq {A} {a b : A} : ∀ (p q : a = b) α,
  α •r eq_refl b = (ru p)⁻¹ • α • (ru q).
Proof.
intros.
destruct p, α; simpl.
reflexivity.
Qed.

Definition lu {A} {b c : A} (r : b = c) : r = eq_refl b • r :=
  hott_2_1_4_i_2 r.

Check @lu.
(* lu
     : ∀ (A : Type) (b c : A) (r : b = c), r = eq_refl b • r *)

Theorem dotl_lurs {A} {b c : A} : ∀ (r s : b = c) β,
  eq_refl b •l β = (lu r)⁻¹ • β • (lu s).
Proof.
intros.
destruct r, β; simpl.
reflexivity.
Qed.

Definition star {A} {a b c : A} {p q : a = b} {r s : b = c} α β
  : p • r = q • s
  := (α •r r) • (q •l β).

Notation "α ★ β" := (star α β) (at level 40).

Theorem star_dot {A} {a : A} : ∀ (α β : eq_refl a = eq_refl a), α ★ β = α • β.
Proof.
intros.
unfold "★"; simpl; unfold id.
eapply compose; [ apply compose_assoc | idtac ].
remember (α • eq_refl (eq_refl a) • β) as p.
pose proof @hott_2_1_4_i_1 (a = a) (eq_refl a) (eq_refl a) p as H.
eapply invert.
eapply compose; [ idtac | eassumption ].
subst; apply dotr, ru.
Qed.

Definition star' {A} {a b c : A} {p q : a = b} {r s : b = c} α β
  : p • r = q • s
  := (p •l β) • (α •r s).

Notation "α ★' β" := (star' α β) (at level 40).

Theorem star'_dot {A} {a : A} : ∀ (α β : eq_refl a = eq_refl a), α ★' β = β • α.
Proof.
intros.
unfold "★'"; simpl; unfold id.
eapply compose; [ apply compose_assoc | idtac ].
remember (β • eq_refl (eq_refl a) • α) as p.
pose proof @hott_2_1_4_i_1 (a = a) (eq_refl a) (eq_refl a) p as H.
eapply invert.
eapply compose; [ idtac | eassumption ].
subst; apply dotr, ru.
Qed.

Theorem gen_star_star' {A} {a b c : A} {p q : a = b} {r s : b = c} : ∀ α β,
  @star A a b c p q r s α β = @star' A a b c p q r s α β.
Proof.
intros.
destruct α as (p).
destruct β as (r).
destruct p, r.
unfold "★", "★'"; simpl.
constructor.
Qed.

Theorem star_star' {A} {a : A} : ∀ (α β : eq_refl a = eq_refl a),
  star α β = star' α β.
Proof. apply gen_star_star'. Qed.

Theorem eckmann_hilton {A} {a : A} : ∀ (α β : eq_refl a = eq_refl a),
  α • β = β • α.
Proof.
intros.
eapply compose; [ eapply invert, star_dot | idtac ].
eapply compose; [ idtac | apply star'_dot ].
apply star_star'.
Qed.

Check @eckmann_hilton.

(* *)

(* hott section 2.2 *)

Definition ap {A B x y} (f : A → B) (p : x = y) : f x = f y :=
  match p with
  | eq_refl _ => eq_refl (f x)
  end.

Theorem hott_2_2_1 {A B} : ∀ (f : A → B) x, ap f (eq_refl x) = eq_refl (f x).
Proof. constructor. Qed.

(* personnal add *)

Definition apf {A B} {f g : A → B} {x y} : f = g → x = y → f x = g y :=
  λ p q, match p with eq_refl _ => ap f q end.

(* Lemma 2.2.2 i *)

Theorem ap_compose {A B} : ∀ (f : A → B) x y z (p : x = y) (q : y = z),
  ap f (p • q) = ap f p • ap f q.
Proof. destruct p, q; constructor. Qed.

Theorem hott_2_2_2_ii {A B} : ∀ (f : A → B) x y (p : x = y),
  ap f (p⁻¹) = (ap f p)⁻¹.
Proof. destruct p; constructor. Qed.

(* Lemma 2.2.2 iii *)

Definition ap_composite {A B C x y}
  : ∀ (f : A → B) (g : B → C) (p : x = y),
    ap g (ap f p) = ap (g ◦ f) p
  := λ f g p,
     match p with eq_refl _ => eq_refl (ap g (ap f (eq_refl x))) end.

Definition hott_2_2_2_iv {A} {x y : A} : ∀ (p : x = y), ap id p = p
  := λ p, match p with eq_refl _ => eq_refl (eq_refl x) end.

(* hott section 2.3 *)

(* p* = transport P p *)
Definition transport {A} P {x y : A} (p : x = y) : P x → P y :=
  match p with
  | eq_refl _ => id
  end.

Check @transport.
(* transport =
     : ∀ (A : Type) (P : A → Type) (x y : A), x = y → P x → P y *)

Notation "p '⁎'" := (transport _ p)
  (at level 8, left associativity, format "'[v' p ']' ⁎", only parsing).

(* lemma 2.3.2 path lifting property *)

Definition lift {A P} {x y : A} (u : P x) (p : x = y)
  : existT _ x u = existT _ y (transport P _ u)
  := match p with
     | eq_refl _ => eq_refl (existT P x (transport P (eq_refl x) u))
     end.

Check @lift.

(* lift
     : ∀ (A : Type) (P : A → Type) (x y : A) (u : P x) (p : x = y),
       existT x u = existT y (transport P p u) *)

Check projT1.
(* projT1
     : ∀ (A : Type) (P : A → Type), sigT P → A *)

Check @ap.
(* ap
     : ∀ (A B : Type) (f : A → B) (x y : A), x = y → f x = f y *)

(*
Mystery in hott book:

Lemma path_lifting_property : ∀ A P (x y : A) (u : P x) (p : x = y),
  @projT1 A P (lift u p) = p.

Toplevel input, characters 103-111:
Error: In environment
A : Type
P : A → Type
x : A
y : A
u : P x
p : x = y
The term "lift u p" has type "existT x u = existT y (transport P p u)"
 while it is expected to have type "sigT ?1330".
*)

(* lemma 2.3.4 *)

Definition apd {A P} f {x y : A} (p : x = y) : transport P p (f x) = f y :=
  match p with
  | eq_refl _ => eq_refl (f x)
  end.

(* lemma hott_2_3_5 *)

Definition transportconst {A : U} {x y : A}
  : ∀ B (P := λ _, B) (p : x = y) (b : B), transport P p b = b
  := λ B (P := λ _, B) p b,
     match p return (transport P p b = b) with
     | eq_refl _ => eq_refl b
     end.

Check @transportconst.
(* transportconst
     : ∀ (A : U) (x y : A) (B : Type) (P:=λ _ : A, B)
       (p : x = y) (b : B), transport P p b = b *)

(* ap
     : ∀ (A B : Type) (f : A → B) (x y : A)
       (p : x = y), f x = f y *)
(* apd
     : ∀ (A : Type) (P : A → Type) (f : ∀ x : A, P x) (x y : A)
       (p : x = y), transport P p (f x) = f y *)

Definition hott_2_3_6 {A B} {x y : A} (p : x = y) (f : A → B) :
  f x = f y → p⁎ (f x) = f y
:=
  λ q, transportconst B p (f x) • q.

Definition hott_2_3_6_alt {A B} {x y : A} (p : x = y) (f : A → B) :
  f x = f y → p⁎ (f x) = f y
:=
  λ _, apd f p.

Definition hott_2_3_7 {A B} {x y : A} (p : x = y) (f : A → B) :
  p⁎ (f x) = f y → f x = f y
:=
  λ q, (transportconst B p (f x))⁻¹ • q.

Definition hott_2_3_7_alt {A B} {x y : A} (p : x = y) (f : A → B) :
  p⁎ (f x) = f y → f x = f y
:=
  λ _, ap f p.

Definition hott_2_3_8 A B (P := λ _ : A, B) (f : A → B) x y (p : x = y)
  : apd f p = transportconst B p (f x) • ap f p
  := match p with eq_refl _ => eq_refl (apd f (eq_refl x)) end.

(* Lemma 2.3.9 *)

Definition transport_compose {A x y z} :
    ∀ (P : A → U) (p : x = y) (q : y = z) (u : P x),
    transport P q (transport P p u) = transport P (p • q) u :=
  λ P p q u,
  match q with
  | eq_refl _ =>
      match p with
      | eq_refl _ => eq_refl (transport P (eq_refl x • eq_refl x) u)
      end
  end.

Definition hott_2_3_10 {A B x y} :
    ∀ (f : A → B) (P : B → U) (p : x = y) (u : P (f x)),
    transport (P ◦ f) p u = transport P (ap f p) u
 := λ f P p u,
    match p with
    | eq_refl _ => eq_refl (transport P (ap f (eq_refl x)) u)
    end.

Definition hott_2_3_11 {A x y} : ∀ (P Q : A → U) (f : Π (x : A), P x → Q x),
  ∀ (p : x = y) (u : P x), transport Q p (f x u) = f y (transport P p u)
  := λ P Q f p u,
     match p with
     | eq_refl _ => eq_refl (f x (transport P (eq_refl x) u))
     end.

(* hott section 2.4 - Homotopies and Equivalences *)

Definition homotopy {A B} (f g : A → B) := Π (x : A), (f x = g x).

Notation "f '~~' g" := (homotopy f g) (at level 70).

Definition homotopy_eq_refl {A B} : reflexive _ (@homotopy A B) :=
  λ _ _, eq_refl _.

Definition homotopy_eq_refl2 {A B} : Π (f : A → B), (f ~~ f) :=
  λ _ _, eq_refl _.

Definition homotopy_sym {A B} : symmetric _ (@homotopy A B) :=
  λ f g (p : f ~~ g) x,
  match p x with eq_refl _ => eq_refl (f x) end.

Definition homotopy_sym2 {A B} : Π (f : A → B), Π (g : A → B),
    (f ~~ g) → (g ~~ f) :=
  λ f g (p : f ~~ g) x,
  match p x with eq_refl _ => eq_refl (f x) end.

Definition homotopy_trans {A B} : transitive _ (@homotopy A B) :=
  λ f g h (p : f ~~ g) (q : g ~~ h) x,
  match q x with
  | eq_refl _ => p x
  end.

Definition homotopy_trans2 {A B}
  : Π (f : A → B), Π (g : A → B), Π (h : A → B),
    (f ~~ g) → (g ~~ h) → (f ~~ h)
  := λ f g h (p : f ~~ g) (q : g ~~ h) x,
     match q x with
     | eq_refl _ => p x
     end.

Add Parametric Relation {A B} : _ (@homotopy A B)
 reflexivity proved by homotopy_eq_refl2
 symmetry proved by homotopy_sym2
 transitivity proved by homotopy_trans2
 as homotopy_equivalence.

Definition hott_2_4_3 {A B x y}
  : ∀ (f g : A → B) (H : f ~~ g) (p : x = y), H x • ap g p = ap f p • H y
  := λ f g H p,
     match p with
     | eq_refl _ =>
         match
           match H x as q return (q = q • eq_refl _) with
           | eq_refl _ => eq_refl (eq_refl (f x) • eq_refl (f x))
           end
         with
         | eq_refl _ => eq_refl (id (H x))
         end
     end.

Definition hott_2_4_4 {A x}
  : ∀ (f : A → A) (H : f ~~ id), H (f x) = ap f (H x).
Proof.
intros.
assert (ap f (H x) • H x = H (f x) • H x) as p.
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
   eapply compose_invert_r; reflexivity.

  eapply dotl, invert.
  eapply compose_invert_r; reflexivity.
Qed.

(* quasi-inverse *)

Definition qinv {A B} (f : A → B) :=
  Σ (g : B → A), ((f ◦ g ~~ id) * (g ◦ f ~~ id))%type.

Example ex_2_4_7 A : qinv (id : A → A) :=
 existT _ id (reflexivity id, reflexivity id).

Example ex_2_4_8_i_tac A : ∀ x y z : A, ∀ (p : x = y),
  qinv (λ (q : y = z), p • q).
Proof.
intros.
apply (existT _ (λ q, p⁻¹ • q)); split.
 intros t; unfold id, "◦"; simpl.
 eapply compose; [ idtac | eapply invert, hott_2_1_4_i_2 ].
 eapply compose; [ apply compose_assoc | apply dotr ].
 apply compose_invert_r.

 intros t; unfold id, "◦"; simpl.
 eapply compose; [ idtac | eapply invert, hott_2_1_4_i_2 ].
 eapply compose; [ apply compose_assoc | apply dotr ].
 apply compose_invert_l.
Qed.

Example ex_2_4_8_i A : ∀ x y z : A, ∀ (p : x = y),
  qinv (λ (q : y = z), p • q)
  := λ x y z p,
     existT _ (compose p⁻¹)
       (λ t : x = z,
        compose_assoc p p⁻¹ t • (compose_invert_r p •r t)
        • (hott_2_1_4_i_2 t)⁻¹,
        λ t : y = z,
        compose_assoc p⁻¹ p t • (compose_invert_l p •r t)
        • (hott_2_1_4_i_2 t)⁻¹).

Example ex_2_4_8_ii_tac A : ∀ x y z : A, ∀ (p : x = y),
  qinv (λ (q : z = x), q • p).
Proof.
intros.
apply (existT _ (λ q, q • p⁻¹)); split.
 intros t; unfold id, "◦"; simpl.
 eapply compose; [ idtac | eapply invert, hott_2_1_4_i_1 ].
 eapply compose; [ eapply invert, compose_assoc | apply dotl ].
 eapply compose_invert_l.

 intros t; unfold id, "◦"; simpl.
 eapply compose; [ idtac | eapply invert, hott_2_1_4_i_1 ].
 eapply compose; [ eapply invert, compose_assoc | apply dotl ].
 eapply compose_invert_r.
Defined.

Example ex_2_4_8_ii A : ∀ x y z : A, ∀ (p : x = y),
  qinv (λ (q : z = x), q • p)
  := λ x y z p,
     existT _ (λ q, q • p⁻¹)
       (λ t : z = y,
        (compose_assoc t p⁻¹ p)⁻¹ • (t •l compose_invert_l p)
        • (hott_2_1_4_i_1 t)⁻¹,
        λ t : z = x,
        (compose_assoc t p p⁻¹)⁻¹ • (t •l compose_invert_r p)
        • (hott_2_1_4_i_1 t)⁻¹).

Example ex_2_4_9_tac A x y : ∀ (p : x = y) (P : A → U), qinv (transport P p).
Proof.
intros.
apply (existT _ (transport P (p⁻¹))); split.
 intros z; unfold id, "◦"; simpl.
 eapply compose; [ apply transport_compose | idtac ].
 destruct p; reflexivity.

 intros z; unfold id, "◦"; simpl.
 eapply compose; [ apply transport_compose | idtac ].
 destruct p; reflexivity.
Qed.

Example ex_2_4_9 A x y : ∀ (p : x = y) (P : A → U), qinv (transport P p) :=
  λ p P,
  existT _ (transport P p⁻¹)
  (λ z : P y,
   transport_compose P p⁻¹ p z
   • match p return (∀ t, transport P (p⁻¹ • p) t = t) with
     | eq_refl _ => λ z0 : P x, eq_refl z0
     end z,
   λ z : P x,
   transport_compose P p p⁻¹ z
   • match p return (transport P (p • p⁻¹) z = z) with
     | eq_refl _ => eq_refl z
     end).

Definition equiv_prop {A B} isequiv :=
  ∀ f : A → B,
  (qinv f → isequiv f) *
  (isequiv f → qinv f) *
  (∀ e₁ e₂ : isequiv f, e₁ = e₂).

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
assert (∀ x, g x = h x) as H.
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
        eq_refl (g (f x))
        • match Hh (g (f x)) with
          | eq_refl _ => eq_refl (h (f (g (f x))))
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
split; [ split; [ apply qinv_isequiv | apply isequiv_qinv ] | intros ].
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

Definition eqv_eq_refl A : A ≃ A :=
  existT isequiv id
    (qinv_isequiv id (existT _ id (reflexivity id, reflexivity id))).

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
                | eq_refl _ => ap g (eqf₁ (g₁ c))
                end),
             existT (λ h, h ◦ (g ◦ f) ~~ id) (f₂ ◦ g₂)
               (λ a,
                match eqf₂ a with
                | eq_refl _ => ap f₂ (eqg₂ (f a))
                end))
      end
  end.

Notation "g '◦◦' f" := (equiv_compose f g) (at level 40).

(* 2.5 The higher groupoid structure of type formers *)

Theorem transport_pair_tac : ∀ A B C (x y : A) (p : x = y) b c,
  transport (λ z, (B z * C z)%type) p (b, c) =
  (transport B p b, transport C p c).
Proof.
intros.
destruct p; reflexivity.
Qed.

Definition transport_pair {A} B C x y (p : x = y) b c
  : transport (λ z : A, (B z * C z)%type) p (b, c) =
    (transport B p b, transport C p c)
  := match p with
     | eq_refl _ =>
         eq_refl (transport B (eq_refl x) b, transport C (eq_refl x) c)
     end.

(* 2.6 Cartesian product types *)

Module cartesian.

(* shortcuts *)
Definition pr₁ {A B} := @AxB_pr₁ A B.
Definition pr₂ {A B} := @AxB_pr₂ A B.

Theorem hott_2_6_1 {A B} : ∀ x y : A * B,
  (x = y) → (pr₁ x = pr₁ y) * (pr₂ x = pr₂ y).
Proof.
intros x y p.
split; destruct p; reflexivity.
Defined.

Theorem pair_eq_tac {A B} {x y : A * B} :
  (pr₁ x = pr₁ y) * (pr₂ x = pr₂ y) → (x = y).
Proof.
intros p.
destruct x as (a, b).
destruct y as (a', b').
simpl in p.
destruct p as (p, q).
destruct p, q; reflexivity.
Defined.

Definition pair_eq {A B} {x y : A * B} :
  (pr₁ x = pr₁ y) * (pr₂ x = pr₂ y) → (x = y)
:=
   let (a, b)
   return ((pr₁ x = pr₁ y) * (pr₂ x = pr₂ y) → x = y) := x in
   let (_, _)
   return ((pr₁ (a, b) = pr₁ y) * (pr₂ (a, b) = pr₂ y) → (a, b) = y)
   := y in
   λ p,
   match pr₁ p with
   | eq_refl _ =>
       match pr₂ p with
       | eq_refl _ => eq_refl (a, b)
       end
   end.

Notation "'pair⁼'" := pair_eq.

Theorem hott_2_6_2 {A B} : ∀ x y : A * B,
  (pr₁ x = pr₁ y) * (pr₂ x = pr₂ y) ≃ (x = y).
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

Definition ap_pr₁ {A B} {x y : A * B} : x = y → pr₁ x = pr₁ y :=
  λ p,
  match p in (_ = z) return (pr₁ x = pr₁ z) with
  | eq_refl _ => eq_refl (pr₁ x)
  end.

Definition ap_pr₂ {A B} {x y : A * B} : x = y → pr₂ x = pr₂ y :=
  λ p,
  match p in (_ = z) return (pr₂ x = pr₂ z) with
  | eq_refl _ => eq_refl (pr₂ x)
  end.

Theorem ap_pr₁_pair {A B} : ∀ (x y : A * B) (p : pr₁ x = pr₁ y) q,
  ap_pr₁ (pair⁼ (p, q)) = p.
Proof.
intros.
destruct x as (a, b).
destruct y as (a', b').
simpl in p, q.
destruct p, q; reflexivity.
Qed.

Theorem ap_pr₂_pair {A B} : ∀ (x y : A * B) p (q : pr₂ x = pr₂ y),
  ap_pr₂ (pair⁼ (p, q)) = q.
Proof.
intros.
destruct x as (a, b).
destruct y as (a', b').
simpl in p, q.
destruct p, q; reflexivity.
Qed.

Theorem pair_uniqueness {A B}  {x y : A * B} : ∀ (r : x = y),
  r = pair⁼ (ap_pr₁ r, ap_pr₂ r).
Proof.
intros.
destruct r; simpl.
destruct x as (a, b); reflexivity.
Qed.

Theorem eq_refl_pair_eq {A B} : ∀ z : A * B,
  eq_refl z = pair⁼ (eq_refl (pr₁ z), eq_refl (pr₂ z)).
Proof.
intros.
destruct z as (x, y); reflexivity.
Qed.

Theorem inv_pair_eq {A B} {x y : A * B} : ∀ p : x = y,
  p⁻¹ = pair⁼ ((ap_pr₁ p)⁻¹, (ap_pr₂ p)⁻¹).
Proof.
intros.
destruct p; simpl.
destruct x as (x₁, x₂); reflexivity.
Qed.

Theorem comp_pair_eq {A B} {x y z : A * B} : ∀ (p : x = y) (q : y = z),
  p • q = pair⁼ (ap_pr₁ p • ap_pr₁ q, ap_pr₂ p • ap_pr₂ q).
Proof.
intros.
destruct p, q; simpl.
destruct x; reflexivity.
Qed.

Theorem hott_2_6_4 {Z} {A B : Z → U} : ∀ (z w : Z) (p : z = w) x,
  transport (λ y, (A y * B y)%type) p x =
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
    (x y : A * B) (p : pr₁ x = pr₁ y) (q : pr₂ x = pr₂ y),
  ap f (pair_eq (p, q)) = pair_eq_ap f (ap g p, ap h q).
Proof.
intros.
destruct x as (x₁, x₂).
destruct y as (y₁, y₂).
simpl in p, q.
destruct p, q; reflexivity.
Qed.

End cartesian.

(* 2.7 Σ-types *)

Definition transport_compat {A P} {x₁ y₁ : A} {x₂ : P x₁}
: ∀ (p q : x₁ = y₁), p = q → transport P p x₂ = transport P q x₂
:=
  λ p q r,
  match r with
  | eq_refl _ => eq_refl (transport P p x₂)
  end.

Module Σ_type.

Definition pr₁ {A B} := @Σ_pr₁ A B.
Definition pr₂ {A B} := @Σ_pr₂ A B.

Definition depend_eq {A P} : ∀ (w w' : Σ (x : A), P x) (p : w = w'),
  P (pr₁ w) = P (pr₁ w')
:=
  λ w w' p, ap P (ap pr₁ p).

(* remark 2.7.1 *)

(* (W) duplication of ap_pr₂ (defined later) *)
Remark transport_ap {A P} {w w' : Σ (x : A), P x} : ∀ (p : w = w'),
  (ap pr₁ p)⁎ (pr₂ w) = pr₂ w'.
Proof.
intros p.
destruct p.
reflexivity.
Defined.

Lemma hott_2_7_2_f {A} : ∀ P (w w' : Σ (x : A), P x),
  w = w' → Σ (p : pr₁ w = pr₁ w'), p⁎ (pr₂ w) = pr₂ w'.
Proof.
intros P w w' p.
destruct p; simpl.
apply (existT _ (eq_refl _)); reflexivity.
Defined.

Lemma hott_2_7_2_g {A} : ∀ P (w w' : Σ (x : A), P x),
  (Σ (p : pr₁ w = pr₁ w'), p⁎ (pr₂ w) = pr₂ w') → w = w'.
Proof.
intros P w w' p.
destruct w as (w₁, w₂).
destruct w' as (w'₁, w'₂); simpl.
simpl in p.
destruct p as (p, q).
destruct p, q; reflexivity.
Defined.

Theorem hott_2_7_2 {A} : ∀ (P : A → U) (w w' : Σ (x : A), P x),
  (w = w') ≃ Σ (p : pr₁ w = pr₁ w'), p⁎ (pr₂ w) = pr₂ w'.
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

(* Corollary 2.7.3... but I don't see in what it is a corollary... *)

Definition pair_uniqueness {A B} (z : {x : A & B x}) :
  z = existT B (pr₁ z) (pr₂ z)
:=
  let (z₁, z₂) return (z = existT B (pr₁ z) (pr₂ z)) := z in
  eq_refl (existT B z₁ z₂).

Definition pair_eq {A} {P : A → U} {x y : A} {u : P x} {v : P y} :
  Π (p : x = y), p⁎ u = v → existT _ x u = existT _ y v
:=
  λ p q,
  match p with
  | eq_refl _ =>
      λ (w : P x) (r : transport P (eq_refl x) u = w),
      match r in (_ = t) return (existT P x u = existT P x t) with
      | eq_refl _ => eq_refl (existT P x (transport P (eq_refl x) u))
      end
  end v q.

Notation "'pair⁼'" := pair_eq.

Definition pair_eq_def {A} {P : A → U} (x y : A) (u : P x) (p : x = y) :
  existT P x u = existT P y (p⁎ u)
:=
  pair_eq p (eq_refl (p⁎ u)).

Definition tfam {A} P (Q : (Σ (x : A), P x) → U) (x : A) :=
  Σ (u : P x), Q (existT P x u).

Definition pair_map {A P Q} {x : A} (a : P x) (b : Q (existT P x a))
    : {u : P x & Q (existT P x u)} :=
  existT (λ u, Q (existT P x u)) a b.

Definition hott_2_7_4 {A P Q} {x y : A} (p : x = y) u z :
  transport (tfam P Q) p (pair_map u z) =
  pair_map (p⁎ u) ((pair⁼ p (eq_refl (p⁎ u)))⁎ z).
Proof.
destruct p.
reflexivity.
Defined.

(* 2.7.5 = generalisation of 2.6.5 *)

Definition transport_pair {A B A' B'} {x y : Σ (z : A), B z}
    (g : A → A') (h : Π (x : A), B x → B' (g x))
    (p : pr₁ x = pr₁ y) (q : p⁎ (pr₂ x) = pr₂ y) :
  transport B' (ap g p) (h (pr₁ x) (pr₂ x)) = h (pr₁ y) (pr₂ y)
:=
   match q with
   | eq_refl _ =>
       match
         p in (_ = z)
         return
           (transport B' (ap g p) (h (pr₁ x) (pr₂ x)) =
            h z (transport B p (pr₂ x)))
       with
       | eq_refl _ => eq_refl (h (pr₁ x) (transport B (eq_refl (pr₁ x)) (pr₂ x)))
       end
   end.

Definition hott_2_7_5 {A B A' B'} (x y : Σ (z : A), B z)
    (g : A → A') (h : Π (x : A), B x → B' (g x))
    (f := λ x, existT _ (g (pr₁ x)) (h (pr₁ x) (pr₂ x)))
    (p : pr₁ x = pr₁ y) (q : p⁎ (pr₂ x) = pr₂ y) :
  ap f (pair⁼ p q) = pair⁼ (ap g p) (transport_pair g h p q).
Proof.
destruct x as (x₁, x₂); simpl.
destruct y as (y₁, y₂); simpl.
simpl in p, q.
destruct p, q; reflexivity.
Defined.

(* reflexivity *)

Definition eq_refl_pair_eq {A B} : ∀ (z : Σ (x : A), B x),
  eq_refl z
  = transport (λ t, t = t) (pair_uniqueness z)⁻¹
       (pair⁼ (eq_refl (pr₁ z)) (eq_refl (pr₂ z))).
Proof.
intros.
destruct z as (x, y); reflexivity.
Defined.

(* inverse *)

Definition ap_pr₁ {A B} {x y : Σ (z : A), B z}
: x = y → pr₁ x = pr₁ y
:=
  λ p,
  match p in (_ = z) return (pr₁ x = pr₁ z) with
  | eq_refl _ => eq_refl (pr₁ x)
  end.

(* (W) duplication of transport_ap (defined before) *)
Definition ap_pr₂ {A B} {x y : Σ (z : A), B z}
: ∀ (p : x = y), transport B (ap_pr₁ p) (pr₂ x) = pr₂ y
:=
  λ p,
  match p in (_ = z) return (transport B (ap_pr₁ p) (pr₂ x) = pr₂ z) with
  | eq_refl _ => eq_refl (pr₂ x)
  end.

Definition transport_invert {A B} {x y : Σ (z : A), B z}
: ∀ (p : pr₁ x = pr₁ y), p⁎ (pr₂ x) = pr₂ y
  → p⁻¹⁎ (pr₂ y) = pr₂ x
:=
  λ p q,
  ap (transport B p⁻¹) q⁻¹
  • (transport_compose B p p⁻¹ (pr₂ x)
     • (transport_compat (p • p⁻¹) (eq_refl (pr₁ x)) (compose_invert_r p)
        • eq_refl (pr₂ x))).

Definition inv_pair_eq {A B} {x y : Σ (z : A), B z}
: ∀ p : x = y,
  p⁻¹ =
    pair_uniqueness y
    • pair⁼ (ap_pr₁ p)⁻¹ (transport_invert (ap_pr₁ p) (ap_pr₂ p))
    • (pair_uniqueness x)⁻¹.
Proof.
intros.
destruct p; simpl.
destruct x as (x₁, x₂); simpl.
reflexivity.
Defined.

(* composition *)

Definition invert_compose {A} (x y z : A) (p : x = y) (q : y = z)
: (p • q)⁻¹ = q⁻¹ • p⁻¹
:=
  match q with
  | eq_refl _ =>
      match p with
      | eq_refl _ => eq_refl ((eq_refl x)⁻¹ • (eq_refl x)⁻¹)
      end
  end.

Theorem comp_pair_eq {A B} {x y z : Σ (t : A), B t}
: ∀ (p : x = y) (q : y = z),
  p • q =
    pair_uniqueness x
    • pair⁼ (ap pr₁ p • ap pr₁ q)
        ((transport_compose B (ap pr₁ p) (ap pr₁ q) (pr₂ x))⁻¹ •
         ap (transport B (ap pr₁ q)) (transport_ap p) •
         transport_ap q)
    • (pair_uniqueness z)⁻¹.
Proof.
destruct p, q; simpl.
destruct x as (x₁, x₂); reflexivity.
Defined.

End Σ_type.

(* 2.8 The unit type *)

Theorem hott_2_8_1 : ∀ x y : unit, (x = y) ≃ unit.
Proof.
intros.
destruct x, y.
set (f := λ _ : tt = tt, tt).
set (g := λ _ : unit, eq_refl tt).
unfold equivalence.
apply (existT _ f), qinv_isequiv.
apply (existT _ g); split.
 subst f g; simpl.
 unfold "◦"; simpl.
 intros x; destruct x; reflexivity.

 subst f g; simpl.
 unfold "◦"; simpl.
 intros x.
 refine (match x with eq_refl _ => _ end).
 reflexivity.
Qed.

Definition unit_intro : unit := tt.
Definition unit_elim : unit → unit := id.
Definition unit_comp : unit → unit := id.
Definition unit_transport := @transportconst unit tt tt.
Print unit_transport.

(* 2.9 Π-types and the function extensionality axiom *)

Definition hap {A B} {f g : A → B}
  : f = g → Π (x : A), f x = g x
  := λ p,
     match p with
     | eq_refl _ => λ y, eq_refl (f y)
     end.

Module Π_type.

Definition happly {A B} {f g : Π (x : A), B x}
  : f = g → Π (x : A), f x = g x
  := λ p,
     match p with
     | eq_refl _ => λ y, eq_refl (f y)
     end.

(* Axiom 2.9.3 *)

Axiom extensionality : ∀ {A B} f g, isequiv (@happly A B f g).

Definition funext_tac {A B} {f g : Π (x : A), B x}
  : (∀ x, f x = g x) → (f = g).
Proof.
intros p.
pose proof @extensionality A B f g as H.
apply isequiv_qinv in H.
destruct H as (h, α, β).
apply h, p.
Defined.

Definition funext {A B} {f g : Π (x : A), B x}
  : (∀ x : A, f x = g x) → f = g
  := λ p,
     match isequiv_qinv happly (extensionality f g) with
     | existT _ h _ => h p
     end.

Theorem funext_quasi_inverse_of_happly_tac {A B} :
  ∀ (f g : Π (x : A), B x) (h : ∀ x, f x = g x) x,
  happly (funext h) x = h x.
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
  : ∀ (f g : Π (x : A), B x) (h : ∀ x, f x = g x) (x : A),
    happly (funext h) x = h x
  := λ f g h x,
     match isequiv_qinv happly (extensionality f g) as q
     return (happly match q with existT _ k _ => k h end x = h x)
     with
     | existT _ k (α, _) => happly (α h) x
     end.

Theorem funext_prop_uniq_princ {A B} : ∀ (f g : Π (x : A), B x) (p : f = g),
  p = funext (happly p).
Proof.
intros.
unfold funext; simpl.
set (q := isequiv_qinv happly (extensionality f g)).
destruct q as (k, (α, β)).
apply invert, β.
Defined.

Theorem funext_identity {A B} : ∀ (f : Π (x : A), B x),
  eq_refl f = funext (λ x, eq_refl (f x)).
Proof.
intros.
unfold funext; simpl.
set (p := isequiv_qinv happly (extensionality f f)).
destruct p as (k, (α, β)).
apply invert, (β (eq_refl f)).
Defined.

Theorem funext_invert {A B} {f g : Π (x : A), B x} : ∀ (α : f = g),
  α⁻¹ = funext (λ x, (happly α x)⁻¹).
Proof.
intros.
destruct α; simpl.
apply funext_identity.
Qed.

Theorem funext_compose {A B} {f g h : Π (x : A), B x} :
    ∀ (α : f = g) (β : g = h),
  α • β = funext (λ x, happly α x • happly β x).
Proof.
intros.
destruct α, β; simpl.
unfold id; simpl.
apply funext_identity.
Qed.

Definition hott_2_9_4 {X A B} {x y : X}
  : ∀ (p : x = y) (f : A x → B x),
     transport (λ x, A x → B x) p f =
     λ a, transport B p (f (transport A p⁻¹ a))
  := λ p f,
     match p with
     | eq_refl _ => eq_refl _
     end.

Definition pr₁ {A B} := @Σ_pr₁ A B.
Definition pr₂ {A B} := @Σ_pr₂ A B.

Definition pair_eq {A B} {x y : A} (p : x = y)
  : ∀ u, existT B x u = existT B y (transport B p u)
  := λ u,
     match p with
     | eq_refl _ => eq_refl (existT B x (transport B (eq_refl x) u))
     end.

Notation "'pair⁼'" := pair_eq.

Notation "'Π' A ( B )" := (λ x, Π (a : A x), B x a) (at level 0, A at level 0).
Notation "B ^" := (λ w, B (pr₁ w) (pr₂ w)) (at level 0).

Definition hott_2_9_5 {X} {A : X → U} {B : Π (x : X), A x → U} {x y : X}
  : ∀ (p : x = y) (f : ∀ a : A x, B x a),
      transport (Π A (B)) p f =
      λ a, transport B^ (pair⁼ p⁻¹ a)⁻¹ (f (transport A p⁻¹ a))
  := λ p f,
     match p with
     | eq_refl _ => eq_refl _
     end.

Lemma hott_2_9_6_i {X} {A B : X → U} {x y : X} (p : x = y) :
  ∀ (f : A x → B x) (g : A y → B y),
  (transport (λ z, A z → B z) p f = g) ≃
  Π (a : A x), (transport B p (f a) = g (transport A p a)).
Proof.
intros.
destruct p; simpl.
unfold id; simpl.
unfold equivalence.
apply existT with (x := happly).
apply extensionality.
Qed.

Definition hott_2_9_6_ii {X} {A B : X → U} {x y : X} (p : x = y)
  : ∀ (f : A x → B x) (g : A y → B y) (a : A x)
      (q : transport (λ z, A z → B z) p f = g),
    transport (λ z, A z → B z) p f (transport A p a) =
    g (transport A p a)
  := λ f g a q,
     happly q (transport A p a).

Definition hott_2_9_6_iii {X} {A B : X → U} {x y : X} (p : x = y)
  : ∀ (f : A x → B x) (g : A y → B y) (a : A x)
      (q : transport (λ z, A z → B z) p f = g),
    transport (λ z, A z → B z) p f (p⁎ a) =
    transport B p (f ((p⁻¹)⁎ (p⁎ a))).
Proof.
intros; destruct p; reflexivity.
Qed.

Definition hott_2_9_6_iv {X} {A B : X → U} {x y : X} (p : x = y)
  : ∀ (f : A x → B x) (g : A y → B y) (a : A x)
      (q : transport (λ z, A z → B z) p f = g),
    transport (λ z, A z → B z) p f (p⁎ a) =
    p⁎ (f a).
Proof.
intros; destruct p; reflexivity.
Qed.

Definition hott_2_9_6_v {X} {A B : X → U} {x y : X}
  : ∀ (p : x = y) (f : A x → B x) (g : A y → B y) (a : A x)
      (q : transport (λ z, A z → B z) p f = g),
    transport (λ z, A z → B z) p f (p⁎ a) =
    g (p⁎ a).
Proof.
intros; destruct p, q; reflexivity.
Qed.

Lemma hott_2_9_7 {X} {A : X → U} {B : Π (x : X), A x → U} {x y : X} :
  ∀ (p : x = y) (f : Π (a : A x), B x a) (g : Π (a : A y), B y a),
  (transport (λ x, ∀ a : A x, B x a) p f = g) ≃
  (Π (a : A x), transport B^ (pair⁼ p a) (f a) = g (transport A p a)).
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

Definition idtoeqv_tac {A B : U} : A = B → A ≃ B.
Proof.
intros p.
set (q := transport id p).
apply (existT _ q).
destruct p.
subst q; simpl.
apply qinv_isequiv, ex_2_4_7.
Defined.

Definition isequiv_transport {A B} : ∀ (p : A = B), isequiv (transport id p)
:=
  λ p,
  match p with
  | eq_refl _ =>
      (existT (λ g : id A → id A, transport id (eq_refl _) ◦ g ~~ id) id
         (reflexivity id),
       existT (λ h : id A → id A, h ◦ transport id (eq_refl _) ~~ id) id
         (reflexivity id))
  end.

Definition idtoeqv {A B : U} : A = B → A ≃ B :=
  λ p,
  existT isequiv (transport id p) (isequiv_transport p).

Axiom univalence : ∀ A B : U, isequiv (@idtoeqv A B).

Theorem univalence2 : ∀ A B : U, (A = B) ≃ (A ≃ B).
Proof.
intros.
pose proof (@univalence A B) as p.
esplit; eassumption.
Defined.

(* funny thing about univalence axiom: it is equivalent to the axiom
   where the middle ≃ is replaced by equality *)

Definition univ_eq :
  (∀ A B, (A ≃ B) ≃ (A = B))
  → (∀ A B, (A ≃ B) = (A = B))
:=
  λ H A B,
  let (f, _) := H (A ≃ B) (A = B) in f (H A B).

Definition eq_univ :
  (∀ A B, (A ≃ B) = (A = B))
  → (∀ A B, (A ≃ B) ≃ (A = B))
:=
  λ H A B,
  match H A B  in (_ = C) return ((A ≃ B) ≃ C) with
  | eq_refl _ => eqv_eq_refl (A ≃ B)
  end.

(* introduction rule *)

Definition ua_tac {A B} : A ≃ B → A = B.
Proof.
intros p.
set (q := isequiv_qinv idtoeqv (univalence A B)).
destruct q as (f, _).
apply f, p.
Defined.

Definition ua {A B} : A ≃ B → A = B :=
  match isequiv_qinv idtoeqv (univalence A B) with
  | existT _ f _ => f
  end.

(* elimination rule = idtoeqv *)
(* ... *)

(* propositional computation rule *)
(* how the eliminator idtoeqv acts on the constructor A = B *)

Definition idtoeqv_ua {A B} : ∀ (f : A ≃ B), idtoeqv (ua f) = f.
Proof.
intros.
unfold ua; simpl.
set (q := isequiv_qinv idtoeqv (univalence A B)).
destruct q as (g, (α, β)).
apply α.
Defined.

Definition ua_pcr {A B}
  : ∀ (f : A ≃ B) (x : A), transport id (ua f) x = projT1 f x
  := λ f x,
     match idtoeqv_ua f with
     | eq_refl _ => eq_refl (projT1 (idtoeqv (ua f)) x)
     end.

(* propositional uniqueness principle *)

Definition ua_idtoeqv {A B} : ∀ (p : A = B), ua (idtoeqv p) = p.
Proof.
intros.
unfold ua; simpl.
set (q := isequiv_qinv idtoeqv (univalence A B)).
destruct q as (f, (α, β)).
apply β.
Defined.

Definition ua_pup {A B}
  : ∀ (p : A = B),
    p = ua (existT isequiv (transport id p) (isequiv_transport p))
  := λ (p : A = B),
     match p return
       (ua (idtoeqv p) = p
        → p = ua (existT isequiv (transport id p) (isequiv_transport p)))
     with
     | eq_refl _ =>
         λ q,
         match q in (_ = r) return (r = ua (eqv_eq_refl A)) with
         | eq_refl _ => eq_refl _
         end
     end (ua_idtoeqv p).

(* reflexivity *)

Definition idtoeqv_eq_refl (A : U) : eqv_eq_refl A = idtoeqv (eq_refl A) :=
  eq_refl (idtoeqv (eq_refl A)).

Definition ua_eq_refl_tac : ∀ A, eq_refl A = ua (eqv_eq_refl A).
Proof.
intros.
rewrite idtoeqv_eq_refl, ua_idtoeqv.
reflexivity.
Defined.

Definition ua_eq_refl : ∀ A, eq_refl A = ua (eqv_eq_refl A) :=
  λ A,
  (λ p,
   match p with
   | eq_refl _ =>
       match ua_idtoeqv (eq_refl A) in (_ = p) return (_ = p → _) with
       | eq_refl _ => id
       end (eq_refl (eq_refl A))
   end)
  (idtoeqv_eq_refl A).

(* concatenation *)

Definition idtoeqv_concat {A B C} : ∀ (p : A = B) (q : B = C),
  idtoeqv (p • q) = idtoeqv q ◦◦ idtoeqv p.
Proof.
intros.
destruct p, q; reflexivity.
Defined.

Definition ua_concat {A B C} : ∀ (f : A ≃ B) (g : B ≃ C),
  ua f • ua g = ua (g ◦◦ f).
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

Definition idtoeqv_inv {A B} : ∀ (f : A = B), ua (idtoeqv f)⁻⁻¹ = f⁻¹.
Proof.
intros.
destruct f; simpl.
unfold ua.
set (q := univalence A A).
destruct q as ((g, Hg), (h, Hh)); simpl.
unfold "◦", "~~", id in Hg, Hh.
pose proof Hh (eq_refl A) as H.
unfold id in H.
rewrite <- H; simpl.
unfold idtoeqv; simpl.
assert (g ~~ h) as Hgh.
 intros x; set (y := g x).
 apply (@compose _ _ (h (idtoeqv y))); [ apply invert, Hh | apply ap, Hg ].

 apply Hgh.
Defined.

Definition ua_inverse {A B} : ∀ f : A ≃ B, (ua f)⁻¹ = ua f⁻⁻¹.
Proof.
intros eqf.
symmetry.
transitivity (ua (idtoeqv (ua eqf))⁻⁻¹).
 rewrite idtoeqv_ua; reflexivity.

 apply idtoeqv_inv.
Defined.

(* ua_pcr_inv: personnal add *)

Definition ua_pcr_inv {A B}
  : ∀ (f : A ≃ B) (x : B), transport id (ua f)⁻¹ x = projT1 f⁻⁻¹ x.
Proof.
intros.
eapply compose; [ idtac | apply ua_pcr ].
apply apf; [ idtac | reflexivity ].
apply apf; [ reflexivity | apply ua_inverse ].
Defined.

Lemma hott_2_10_5_i {A} {B : A → U} {x y : A} : ∀ (p : x = y) (u : B x),
  transport B p u = transport id (ap B p) u.
Proof.
intros.
destruct p; reflexivity.
Defined.

Lemma hott_2_10_5_ii {A} {B : A → U} {x y : A} : ∀ (p : x = y) (u : B x),
  transport id (ap B p) u = projT1 (idtoeqv (ap B p)) u.
Proof. reflexivity. Qed.

Lemma hott_2_10_5 {A} {B : A → U} {x y : A} : ∀ (p : x = y) (u : B x),
  transport B p u = projT1 (idtoeqv (ap B p)) u.
Proof. intros; destruct p; reflexivity. Qed.

(* 2.11 Identity type *)

(* Theorem 2.11.1 *)

Theorem hott_2_11_1 {A B} : ∀ (f : A → B), isequiv f → ∀ (a a' : A),
  (a = a') ≃ (f a = f a').
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
  apply dotr, invert, compose_invert_l.

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
    rewrite <- ru, compose_invert_r.
    reflexivity.

    apply (@compose _ _ ((α (f a))⁻¹ • ap f (ap f₁ q) • α (f a'))).
     apply dotr, dotl, ap; subst r.
     do 2 rewrite compose_assoc.
     rewrite compose_invert_r; simpl.
     unfold id; simpl.
     rewrite <- compose_assoc.
     rewrite compose_invert_r; simpl.
     rewrite <- ru; reflexivity.

     assert (H1 : α (f a) • q = ap (f ◦ f₁) q • α (f a')).
      rewrite <- (hott_2_4_3 (f ◦ f₁) id α q).
      apply dotl, invert, hott_2_2_2_iv.

      unfold id, composite; simpl.
      pose proof (@ap_composite B A B (f a) (f a') f₁ f q) as H2.
      rewrite H2.
      rewrite <- compose_assoc.
      unfold id, composite in H1; simpl in H1.
      unfold composite; simpl.
      rewrite <- H1.
      rewrite compose_assoc, compose_invert_l.
      reflexivity.

 rewrite (ap_composite f f₁ q).
 destruct q; simpl.
 unfold "◦", "~~", id in β; simpl in β.
 unfold "◦"; simpl; rewrite β; reflexivity.
Defined.

Section cartesian2.

(* Paths p = q, where p,q : w =_{AxB} w', are equivalent to pairs of
   paths
       ap_{pr₁} p =_{pr₁ w =_A pr₁ w'} ap_{pr₁} q
       ap_{pr₂} p =_{pr₂ w =_A pr₂ w'} ap_{pr₂} q *)

Definition pr₁ {A B} := @AxB_pr₁ A B.
Definition pr₂ {A B} := @AxB_pr₂ A B.

Definition pair_eq_split {A B} : ∀ (a b : A) (c d : B),
  (a, c) = (b, d) → (a = b) * (c = d)
:= λ a b c d H, (cartesian.ap_pr₁ H, cartesian.ap_pr₂ H).

Definition split_pair_eq {A B} : ∀ (a b : A) (c d : B),
  (a = b) * (c = d) → (a, c) = (b, d)
:= λ a b c d H,
   match pr₁ H with
   | eq_refl _ =>
       match pr₂ H with
       | eq_refl _ => eq_refl (a, c)
       end
   end.

Definition split_pair_eq_id {A B} : ∀ (a b : A) (c d : B),
  split_pair_eq a b c d ◦ pair_eq_split a b c d ~~ id
:= λ a b c d p,
   match p in (_ = q)
     return
     ((let (b0, d0) as x return ((a, c) = x → Type) := q in
       λ p2,
       split_pair_eq a b0 c d0 (pair_eq_split a b0 c d0 p2) = p2) p)
   with
   | eq_refl _ => eq_refl (eq_refl (a, c))
   end.

Definition pair_eq_split_id {A B} : ∀ (a b : A) (c d : B),
  pair_eq_split a b c d ◦ split_pair_eq a b c d ~~ id
:= λ a b c d p,
   let (q, r) as p0
   return (pair_eq_split a b c d (split_pair_eq a b c d p0) = p0) := p in
   match q with
   | eq_refl _ =>
       match r with
       | eq_refl _ => eq_refl (eq_refl a, eq_refl c)
       end
   end.

Theorem cart_pr₁ {A B} : @cartesian.pr₁ A B = pr₁.
Proof. reflexivity. Qed.
Theorem cart_pr₂ {A B} : @cartesian.pr₂ A B = pr₂.
Proof. reflexivity. Qed.

Theorem equiv_pair {A B} {w w' : A * B} : ∀ (p q : w = w'),
  (p = q) ≃ ((ap pr₁ p, ap pr₂ p) = (ap pr₁ q, ap pr₂ q)).
Proof.
intros.
set (f := λ p : w = w', (ap pr₁ p, ap pr₂ p)).
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

Theorem pair_equiv {A B} {w w' : A * B} : ∀ (p q : w = w'),
  (p = q) ≃ (ap pr₁ p = ap pr₁ q) * (ap pr₂ p = ap pr₂ q).
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

Theorem dep_fun_equiv {A B} {f g : Π (x : A), B x} : ∀ (p q : f = g),
  (p = q) ≃ Π (x : A), (happly p x = happly q x).
Proof.
intros p q.
pose proof hott_2_11_1 happly (Π_type.extensionality f g) p q as H.
eapply equiv_compose; [ eapply H | idtac ].
apply (existT _ happly), Π_type.extensionality.
Defined.

(* the same, but putting function extensionality as hypothesis instead
   of using axiom *)

Theorem dep_fun_equiv2 {A B} {f g : Π (x : A), B x} : ∀ (p q : f = g),
  isequiv (@happly _ _ f g)
  → isequiv (@happly _ _ (happly p) (happly q))
  → (p = q) ≃ Π (x : A), (happly p x = happly q x).
Proof.
intros p q Hf Hg.
pose proof hott_2_11_1 happly Hf p q as H.
eapply equiv_compose; [ eapply H | idtac ].
apply (existT _ happly), Hg.
Defined.

(* transport in families of paths *)

Lemma hott_2_11_2_i {A} : ∀ (a x₁ x₂ : A) (p : x₁ = x₂) (q : a = x₁),
  transport (λ x, a = x) p q = q • p.
Proof. intros; destruct p, q; reflexivity. Defined.

Lemma hott_2_11_2_ii {A} : ∀ (a x₁ x₂ : A) (p : x₁ = x₂) (q : x₁ = a),
  transport (λ x, x = a) p q = p⁻¹ • q.
Proof. intros; destruct p; reflexivity. Defined.

Lemma hott_2_11_2_iii {A} : ∀ (a x₁ x₂ : A) (p : x₁ = x₂) (q : x₁ = x₁),
  transport (λ x, x = x) p q = p⁻¹ • q • p.
Proof. intros; destruct p; simpl; destruct q; reflexivity. Defined.

(* they pretend that this needs 2.3.10 and 2.11.2 but it can be proved
   directly by induction: *)

Theorem hott_2_11_3 {A B} : ∀ (f g : A → B) a a'
  (p : a = a') (q : f a = g a),
  transport (λ x, f x = g x) p q = (ap f p)⁻¹ • q • ap g p.
Proof. intros; destruct p; simpl; destruct q; reflexivity. Defined.

Theorem hott_2_11_4 {A B} : ∀ (f g : Π (x : A), B x) a a'
  (p : a = a') (q : f a = g a),
  transport (λ x, f x = g x) p q =
  (apd f p)⁻¹ • ap (transport B p) q • apd g p.
Proof. intros; destruct p; simpl; destruct q; reflexivity. Defined.

Theorem hott_2_11_5 {A} {a a' : A} :
  ∀ (p : a = a') (q : a = a) (r : a' = a'),
  (transport (λ x, x = x) p q = r) ≃ (q • p = p • r).
Proof.
intros.
destruct p; simpl.
unfold id; simpl.
rewrite <- ru.
apply eqv_eq_refl.
Defined.

(* 2.12 Coproducts *)

(* my proof *)

Definition inl_inversion {A B} (a₁ a₂ : A) :
  @eq (A + B) (inl a₁) (inl a₂) → (a₁ = a₂)
:= ap (λ a, match a with inl a₁ => a₁ | inr _ => a₁ end).

Definition inr_inversion {A B} (b₁ b₂ : B) :
  @eq (A + B) (inr b₁) (inr b₂) → (b₁ = b₂)
:= ap (λ a, match a with inl _ => b₁ | inr b₁ => b₁ end).

Definition inl_equal {A B} {a₁ a₂ : A} :
  (a₁ = a₂) → @eq (A + B) (inl a₁) (inl a₂)
:= λ H : a₁ = a₂,
   match H in (_ = a) return (inl a₁ = inl a) with
    eq_refl _ => eq_refl (inl a₁ : A + B)
   end.

Definition inr_equal {A B} {b₁ b₂ : B} :
  (b₁ = b₂) → @eq (A + B) (inr b₁) (inr b₂)
:= λ H : b₁ = b₂,
   match H in (_ = b) return (inr b₁ = inr b) with
    eq_refl _ => eq_refl (inr b₁ : A + B)
   end.

(* Expression 2.12.1 *)

Definition inl_eq_equiv {A B} (a₁ a₂ : A) :
  @eq (A + B) (inl a₁) (inl a₂) ≃ (a₁ = a₂).
Proof.
apply (existT _ (inl_inversion a₁ a₂)).
apply qinv_isequiv.
apply (existT _ (@inl_equal _ _ a₁ a₂)).
split; [ intros p; destruct p; reflexivity | idtac ].
intros p; simpl.
unfold "◦", "~~", id; simpl.
refine (match p with eq_refl _ => _ end).
reflexivity.
Defined.

(* Expression 2.12.2 *)

Definition inr_eq_equiv {A B} (b₁ b₂ : B) :
  @eq (A + B) (inr b₁) (inr b₂) ≃ (b₁ = b₂).
Proof.
apply (existT _ (inr_inversion b₁ b₂)).
apply qinv_isequiv.
apply (existT _ (@inr_equal _ _ b₁ b₂)).
split; [ intros p; destruct p; reflexivity | idtac ].
intros p; simpl.
unfold "◦", "~~", id; simpl.
refine (match p with eq_refl _ => _ end).
reflexivity.
Defined.

(* Expression 2.12.3 *)

Definition inl_inr_equiv {A B} (a : A) (b : B) : inl a = inr b ≃ ⊥.
Proof.
assert (inl a = inr b → ⊥) as f.
 intros p.
 change (match (inl a : A + B) with inl _ => False | inr _ => True end).
 rewrite p; constructor.

 apply (existT _ f), qinv_isequiv.
 assert (⊥ → inl a = inr b) as g by (intros H; contradiction).
 apply (existT _ g); split; intros x; contradiction.
Defined.

(* Expression 2.12.4 *)

Definition inl_family {A B a₀} (x : A + B) : U := inl a₀ = x.
Definition inr_family {A B b₀} (x : A + B) : U := inr b₀ = x.

Definition code {A B} a₀ : A + B → U :=
  λ x,
  match x with
  | inl a => a₀ = a
  | inr b => ⊥
  end.

(* I did it the reverse way they did: that 2.12.1 and 2.12.3 imply 2.12.5: *)

Theorem hott_2_12_5 {A B} a₀ : ∀ x : A + B, (inl a₀ = x) ≃ code a₀ x.
Proof.
intros.
destruct x; [ apply inl_eq_equiv | apply inl_inr_equiv ].
Defined.

(* let's see 'their' proof... *)

Definition encode {A B} a₀ (x : A + B) : ∀ (p : inl a₀ = x), code a₀ x :=
  λ p, transport (code a₀) p (eq_refl a₀).

Definition decode {A B} a₀ (x : A + B) : ∀ (c : code a₀ x), (inl a₀ = x) :=
  match x return (code a₀ x → inl a₀ = x) with
  | inl a => ap inl
  | inr b => λ f, match f return inl a₀ = inr b with end
  end.

Definition encode_decode {A B} a₀ (x : A + B) :
  encode a₀ x ◦ decode a₀ x ~~ id.
Proof. intros y; destruct x, y; reflexivity. Defined.

Definition decode_encode {A B} a₀ (x : A + B) :
  decode a₀ x ◦ encode a₀ x ~~ id.
Proof. intros y; destruct x, y; reflexivity. Defined.

Theorem hott_2_12_5_bis {A B} a₀ : ∀ x : A + B, (inl a₀ = x) ≃ code a₀ x.
Proof.
intros.
apply (existT _ (encode a₀ x)), qinv_isequiv.
apply (existT _ (decode a₀ x)).
split; [ apply encode_decode | apply decode_encode ].
Defined.

(* 2.12.1 again *)

Definition inl_eq_equiv_bis {A B} (a₁ a₂ : A) :
  @eq (A + B) (inl a₁) (inl a₂) ≃ (a₁ = a₂).
Proof.
eapply equiv_compose; [ apply hott_2_12_5_bis | apply eqv_eq_refl ].
Defined.

(* 2.12.3 again *)

Definition inl_inr_equiv_bis {A B} (a : A) (b : B) : inl a = inr b ≃ ⊥.
Proof.
eapply equiv_compose; [ apply hott_2_12_5_bis | apply eqv_eq_refl ].
Defined.

(* and what about 2.12.2 ? *)

Definition code_r {A B} b₀ : A + B → U :=
  λ x,
  match x with
  | inl a => ⊥
  | inr b => b₀ = b
  end.

Definition encode_r {A B} b₀ (x : A + B) (p : inr b₀ = x) : code_r b₀ x :=
  transport (code_r b₀) p (eq_refl b₀).

Definition decode_r {A B} b₀ (x : A + B) (c : code_r b₀ x) : (inr b₀ = x) :=
  match x return (code_r b₀ x → inr b₀ = x) with
  | inl a => λ f, match f return inr b₀ = inl a with end
  | inr b => ap inr
  end c.

Definition encode_r_decode_r {A B} b₀ (x : A + B) :
  encode_r b₀ x ◦ decode_r b₀ x ~~ id.
Proof. intros y; destruct x, y; reflexivity. Defined.

Definition decode_r_encode_r {A B} b₀ (x : A + B) :
  decode_r b₀ x ◦ encode_r b₀ x ~~ id.
Proof. intros y; destruct x, y; reflexivity. Defined.

Theorem hott_2_12_5_ter {A B} b₀ : ∀ x : A + B, (inr b₀ = x) ≃ code_r b₀ x.
Proof.
intros.
apply (existT _ (encode_r b₀ x)), qinv_isequiv.
apply (existT _ (decode_r b₀ x)).
split; [ apply encode_r_decode_r | apply decode_r_encode_r ].
Defined.

Definition inr_eq_equiv_bis {A B} (b₁ b₂ : B) :
  @eq (A + B) (inr b₁) (inr b₂) ≃ (b₁ = b₂).
Proof.
eapply equiv_compose; [ apply hott_2_12_5_ter | apply eqv_eq_refl ].
Defined.

(* In particular, theorem 2.12.5 implies *)

Definition encode_inl_inl {A B} a₀
  : ∀ a, (@eq (A + B) (inl a₀) (inl a)) → (a₀ = a)
  := λ a, encode a₀ (inl a).

Definition encode_inl_inr {A B} a₀
  : ∀ b, (@eq (A + B) (inl a₀) (inr b)) → ⊥
  := λ b, encode a₀ (inr b).

(* Remark 2.12.6. In particular, since the two-element type 2 is
   equivalent to 1+1, we have 0₂ ≠ 1₂ *)

Definition bool_unit_unit : bool → unit + unit :=
  λ b, match b with true => inr tt | false => inl tt end.

Definition hott_2_12_6 : false ≠ true :=
  λ p, encode_inl_inr tt tt (ap bool_unit_unit p).

(* action of transport in coproduct types *)

Definition transport_coprod_l {X} {x₁ x₂ : X} (p : x₁ = x₂) {A B} : ∀ a,
  transport (λ x, (A x + B x)%type) p (inl a) = inl (transport A p a)
:= λ a,
   match p with
   | eq_refl _ => eq_refl (inl (transport A (eq_refl x₁) a))
   end.

Definition transport_coprod_r {X} {x₁ x₂ : X} (p : x₁ = x₂) {A B} : ∀ b,
  transport (λ x, (A x + B x)%type) p (inr b) = inr (transport B p b)
:= λ b,
   match p with
   | eq_refl _ => eq_refl (inr (transport B (eq_refl x₁) b))
   end.

End Σ_type2.

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

Definition encode (m n : nat) : m = n → code m n :=
  λ p, transport (code m) p (r m).

Definition decode (m n : nat) : code m n → m = n.
Proof.
revert m n.
fix 1; rename decode into IHn.
intros m n p.
destruct m.
 destruct n; [ reflexivity | refine (match p with end) ].

 destruct n; [ refine (match p with end) | simpl in p ].
 apply ap, IHn, p.
Defined.

Theorem decode_encode {m n} : ∀ p, decode m n (encode m n p) = p.
Proof.
intros p.
destruct p; simpl; unfold id; simpl.
induction m; [ reflexivity | simpl ].
apply (ap (ap S)) in IHm; assumption.
Defined.

Theorem encode_decode {m n} : ∀ c, encode m n (decode m n c) = c.
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

Theorem hott_2_13_1 : ∀ m n, (m = n) ≃ code m n.
Proof.
intros.
apply (existT _ (encode m n)), qinv_isequiv.
apply (existT _ (decode m n)).
unfold "◦", "~~", id; simpl.
split; intros p; [ apply encode_decode | apply decode_encode ].
Defined.

Definition hott_2_13_2 {m} : S m = 0 → ⊥ := encode (S m) 0.

Definition hott_2_13_3 m n : (S m = S n) → (m = n) :=
  λ p, decode m n (encode (S m) (S n) p).

End ℕ.

(* 2.14 Example: equality of structures *)

Module EqStr.

Import Σ_type.

Definition Assoc X m :=
  Π (x : X), Π (y : X), Π (z : X), m x (m y z) = m (m x y) z.

Definition SemigroupStr A := Σ (m : A → A → A), Assoc A m.
Definition Semigroup := Σ (A : U), SemigroupStr A.

(* 2.14.1 Lifting equivalences *)

(* they say:
     transport C (α) is always an equivalence with inverse
     transport C (α⁻¹), see Lemmas 2.1.4 and 2.3.9
   we have:
   - Lemma 2.1.4 ii 1 = compose_invert_l
   - Lemma 2.1.4 ii 2 = compose_invert_r
   - Lemma 2.3.9 = transport_compose
*)

Definition ap_equiv_tac {A B} (C : U → U) : A ≃ B → C A ≃ C B.
Proof.
intros p.
apply (existT _ (transport C (ua p))), qinv_isequiv.
apply (existT _ (transport C (ua p)⁻¹)).
split; intros g; unfold id; simpl.
 eapply compose; [ apply transport_compose | idtac ].
 eapply compose.
  apply transport_compat, compose_invert_l; reflexivity.

  reflexivity.

 eapply compose; [ apply transport_compose | idtac ].
 eapply compose.
  apply transport_compat, compose_invert_r; reflexivity.

  reflexivity.
Defined.

Definition transp_ap_inv_l {A B} (C : U → U) (e : A ≃ B) (g : C B)
: transport C (ua e) (transport C (ua e)⁻¹ g) = g
:=
  transport_compose C (ua e)⁻¹ (ua e) g
  • transport_compat ((ua e)⁻¹ • ua e) (eq_refl B) (compose_invert_l (ua e)).

Definition transp_ap_inv_r {A B} (C : U → U) (e : A ≃ B) (g : C A)
:=
  transport_compose C (ua e) (ua e)⁻¹ g
  • transport_compat (ua e • (ua e)⁻¹) (eq_refl A) (compose_invert_r (ua e)).

Definition ap_equiv {A B} (C : U → U) : A ≃ B → C A ≃ C B
:=
  λ e,
  existT _ (transport C (ua e))
    (qinv_isequiv (transport C (ua e))
       (existT _ (transport C (ua e)⁻¹)
          (transp_ap_inv_l C e, transp_ap_inv_r C e))).

(* applied to Semigroups *)

Definition SemigroupStr_equiv {A B} :
  A ≃ B → SemigroupStr A ≃ SemigroupStr B
:=
  ap_equiv SemigroupStr.

(* First, because SemigroupStr (X) is defined to be a Σ-type, by
   Theorem 2.7.4, *)

Definition transport_semigroup {A B} (p : A = B) m (a : Assoc A m) :
  let m' : B → B → B := transport (λ X : U, X → X → X) p m in
  let a' : Assoc B m' :=
    transport (λ xu, Assoc (pr₁ xu) (pr₂ xu)) (pair⁼ p (eq_refl m')) a
  in
  transport SemigroupStr p (existT _ m a) = existT _ m' a'.
Proof.
apply
  (@hott_2_7_4 U (λ X, X → X → X) (λ xu, Assoc (pr₁ xu) (pr₂ xu)) A B p m a).
Defined.

(* had formula 2.14.2 *)

(* By applying (2.9.4) twice, we have that m'(b1, b2) is equal to *)
(* (personal remark: provable also with "destruct p") *)

Definition transport_op_1_tac {A B} (p : A = B) m b₁ b₂ :
  transport (λ X : U, X → X → X) p m b₁ b₂ =
  transport id p (m (transport id p⁻¹ b₁) (transport id p⁻¹ b₂)).
Proof.
eapply compose.
 eapply hap, hap.
 apply (@Π_type.hott_2_9_4 _ _ (λ X, X → X) _ _ p m).
 apply (hap (Π_type.hott_2_9_4 p (m (transport id p⁻¹ b₁)))).
Defined.

Definition transport_op_1 {A B} (p : A = B) m b₁ b₂ :
  transport (λ X : U, X → X → X) p m b₁ b₂ =
  transport id p (m (transport id p⁻¹ b₁) (transport id p⁻¹ b₂))
:=
  hap (hap (@Π_type.hott_2_9_4 _ _ (λ X : U, X → X) _ _ p m) b₁) b₂
  • hap (Π_type.hott_2_9_4 p (m (transport id p⁻¹ b₁))) b₂.

Definition transport_op_2_tac {A B} (p : A = B) m b₁ b₂ :
  transport (λ X : U, X → X → X) p m b₁ b₂ =
  transport id p (m (transport id p⁻¹ b₁) (transport id p⁻¹ b₂)).
Proof.
destruct p; reflexivity.
Defined.

Definition transport_op_2 {A B} (p : A = B) m b₁ b₂ :
  transport (λ X : U, X → X → X) p m b₁ b₂ =
  transport id p (m (transport id p⁻¹ b₁) (transport id p⁻¹ b₂))
:=
  match p in (_ = X) return
    (∀ b₁ b₂ : X,
     transport (λ X : U, X → X → X) p m b₁ b₂ =
     transport id p (m (transport id p⁻¹ b₁) (transport id p⁻¹ b₂)))
  with
  | eq_refl _ =>
      λ b₁ b₂ : A,
      eq_refl
        (transport id (eq_refl A)
           (m (transport id (eq_refl A)⁻¹ b₁) (transport id (eq_refl A)⁻¹ b₂)))
  end b₁ b₂.

(* Then, because ua is quasi-inverse to transport^(X→X), this is equal to *)

Definition transport_op_tac {A B} (e : A ≃ B) m b₁ b₂ :
  transport (λ X : U, X → X → X) (ua e) m  b₁ b₂ =
  pr₁ e (m (pr₁ e⁻⁻¹ b₁) (pr₁ e⁻⁻¹ b₂)).
Proof.
eapply compose; [ eapply transport_op_1 | idtac ].
eapply compose; [ apply ua_pcr | apply ap ].
eapply apf.
 eapply apf; [ reflexivity | apply ua_pcr_inv ].

 eapply compose; [ apply ua_pcr_inv | reflexivity ].
Defined.

Definition transport_op {A B} (e : A ≃ B) m b₁ b₂ :
  transport (λ X : U, X → X → X) (ua e) m b₁ b₂ =
  pr₁ e (m (pr₁ e⁻⁻¹ b₁) (pr₁ e⁻⁻¹ b₂))
:=
  transport_op_1 (ua e) m b₁ b₂
  • ua_pcr e (m (transport id (ua e)⁻¹ b₁) (transport id (ua e)⁻¹ b₂))
  • ap (pr₁ e)
      (apf
         (apf (eq_refl m) (ua_pcr_inv e b₁))
         (ua_pcr_inv e b₂ • eq_refl (pr₁ e⁻⁻¹ b₂))).

(* misc theorems *)

Definition quasi_inv_l_eq_r_tac {A B} (f : A → B) (g h : B → A) :
  f ◦ g ~~ id
  → h ◦ f ~~ id
  → g ~~ h.
Proof.
intros Hfg Hhf x.
unfold "◦", "~~", id in Hfg, Hhf.
pose proof Hfg x as H.
apply (ap h) in H.
eapply compose; [ idtac | eassumption ].
apply invert, Hhf.
Defined.

Definition quasi_inv_l_eq_r {A B} (f : A → B) (g h : B → A) :
  f ◦ g ~~ id
  → h ◦ f ~~ id
  → g ~~ h
:=
  λ Hfg Hhf x, (Hhf (g x))⁻¹ • ap h (Hfg x).

Definition quasi_inv_comp_l {A B} (e : A ≃ B) : pr₁ e⁻⁻¹ ◦ pr₁ e ~~ id.
Proof.
intros x.
destruct e as (f, ((g, Hg), (h, Hh))); simpl.
pose proof quasi_inv_l_eq_r f g h Hg Hh as H.
unfold "~~" in H.
eapply compose; [ apply H | apply Hh ].
Defined.

Definition quasi_inv_comp_r {A B} (e : A ≃ B) : pr₁ e ◦ pr₁ e⁻⁻¹ ~~ id.
Proof.
intros x.
destruct e as (f, ((g, Hg), (h, Hh))); simpl.
apply Hg.
Defined.

(* one can calculate that the induced proof that m' is associative
  (see 2.14.2) is equal to a function sending b1, b2, b3 : B to a
  path given by the following steps: *)

Definition pre_hott_2_14_3_tac {A B} (e : A ≃ B) m (a : Assoc A m) b₁ b₂ b₃ :
  let m' : B → B → B := transport (λ X : U, X → X → X) (ua e) m in
  m' (m' b₁ b₂) b₃ = m' b₁ (m' b₂ b₃).
Proof.
simpl; set (m' := transport (λ X : U, X → X → X) (ua e) m).
(* m'(m'(b₁, b₂), b₃) = e(m(e⁻¹(m'(b₁, b₂)), e⁻¹(b₃))) *)
eapply compose; [ apply transport_op | idtac ].
(*                    = e(m(e⁻¹(e(m(e⁻¹(b₁), e⁻¹(b₂)))), e⁻¹(b₃))) *)
eapply compose; [ eapply ap, hap, ap, ap, transport_op | idtac ].
(*                    = e(m(m(e⁻¹(b₁), e⁻¹(b₂)), e⁻¹(b₃))) *)
eapply compose; [ eapply ap, hap, ap, quasi_inv_comp_l | unfold id ].
(*                    = e(m(e⁻¹(b₁), m(e⁻¹(b₂), e⁻¹(b₃)))) *)
eapply compose; [ eapply ap, invert, a | idtac ].
(*                    = e(m(e⁻¹(b₁), e⁻¹(e(m(e⁻¹(b₂), e⁻¹(b₃)))))) *)
eapply compose; [ eapply ap, ap, invert, (quasi_inv_comp_l e) | unfold "◦" ].
(*                    = e(m(e⁻¹(b₁), e⁻¹(m'(b₂, b3)))) *)
eapply compose; [ eapply ap, ap, ap, invert, transport_op | idtac ].
(*                    = m'(b₁,m'(b₂, b₃)) *)
eapply compose; [ eapply invert, transport_op | reflexivity ].
Defined.

Definition pre_hott_2_14_3 {A B} (e : A ≃ B) m (a : Assoc A m) b₁ b₂ b₃ :
  let m' : B → B → B := transport (λ X : U, X → X → X) (ua e) m in
  m' (m' b₁ b₂) b₃ = m' b₁ (m' b₂ b₃)
:=
  let m' : B → B → B := transport (λ X : U, X → X → X) (ua e) m in
  transport_op e m (m' b₁ b₂) b₃
  • ap (pr₁ e)
      (hap (ap m (ap (pr₁ e⁻⁻¹) (transport_op e m b₁ b₂))) (pr₁ e⁻⁻¹ b₃))
  • ap (pr₁ e)
      (hap (ap m (quasi_inv_comp_l e (m (pr₁ e⁻⁻¹ b₁) (pr₁ e⁻⁻¹ b₂))))
         (pr₁ e⁻⁻¹ b₃))
  • ap (pr₁ e) (a (pr₁ e⁻⁻¹ b₁) (pr₁ e⁻⁻¹ b₂) (pr₁ e⁻⁻¹ b₃))⁻¹
  • ap (pr₁ e)
      (ap (m (pr₁ e⁻⁻¹ b₁))
         (quasi_inv_comp_l e (m (pr₁ e⁻⁻¹ b₂) (pr₁ e⁻⁻¹ b₃)))⁻¹)
  • ap (pr₁ e)
      (ap (m (pr₁ e⁻⁻¹ b₁)) (ap (pr₁ e⁻⁻¹) (transport_op e m b₂ b₃)⁻¹))
  • (transport_op e m b₁ (m' b₂ b₃))⁻¹.

Definition hap_invert {A B} (f g : A → B) (p : f = g) (x : A) :
  hap p⁻¹ x = (hap p x)⁻¹.
Proof. destruct p; reflexivity. Defined.

(* true definition of 2.14.3: a' is supposed to be equal to this proof
   above *)

Definition hott_2_14_3 {A B} (e : A ≃ B) m (a : Assoc A m) :
  let m' : B → B → B := transport (λ X : U, X → X → X) (ua e) m in
  let a' : Assoc B m' :=
    transport (λ xu, Assoc (pr₁ xu) (pr₂ xu)) (pair⁼ (ua e) (eq_refl m')) a
  in
  a' = λ b₁ b₂ b₃, (pre_hott_2_14_3 e m a b₁ b₂ b₃)⁻¹.
Proof.
intros; simpl in a'.
eapply Π_type.funext; intros b₁.
eapply Π_type.funext; intros b₂.
eapply Π_type.funext; intros b₃.
unfold pre_hott_2_14_3.
subst m'.
set (m' := transport (λ X : U, X → X → X) (ua e) m : B → B → B) in *.
simpl in m'.
do 6 rewrite invert_compose.
rewrite hott_2_1_4_iii.
do 5 rewrite compose_assoc.
set (t := {X : Type & X → X → X}) in *.
set (u := λ X : U, X → X → X) in *.
set (P (xu : t) := Assoc (@pr₁ Type u xu) (@pr₂ Type u xu)) in *.
set (p := @pair_eq Type u _ _ _ _ (ua e) (eq_refl m')) in a'.
subst m' a'.
do 8 rewrite <- hott_2_2_2_ii.
do 3 rewrite hott_2_1_4_iii.
do 2 rewrite <- hap_invert.
do 3 rewrite <- hott_2_2_2_ii.
set (E := pr₁ e).
set (E₁ := pr₁ e⁻⁻¹).
Abort. (* don't know how to prove it and the book says: " we do not
  show the proof" *)

(* 2.14.2 Equality of semigroups *)

Definition semigroup_path_type {A B} m a m' a' :
  (A, (m, a)_{Assoc A})_{SemigroupStr} =
  (B, (m', a')_{Assoc B})_{SemigroupStr}
  ≃ Σ (p₁ : A = B),
    transport SemigroupStr p₁ (existT _ m a) = existT _ m' a'.
Proof.
apply hott_2_7_2.
Defined.

(* other formulation *)

Definition semigroup_path_type2 {A B} m a m' a' :
  let w := existT SemigroupStr A (existT (Assoc A) m a) in
  let w' := existT SemigroupStr B (existT (Assoc B) m' a') in
  w = w' ≃ Σ (p : pr₁ w = pr₁ w'), p⁎ (pr₂ w) = pr₂ w'.
Proof.
intros.
apply hott_2_7_2.
Defined.

(* pr₁ and pr₂ on semigroups *)

Check (pr₁ : Semigroup → U).
(* pr₁ : Semigroup → U *)

Check (pr₂ : Π (x : Semigroup), (_ ◦ pr₁) x).
(* pr₂ : ∀ x : Semigroup, (SemigroupStr ◦ pr₁) x *)

(* equality in semigroup str *)

Theorem eq_pair_dep_pair : ∀ A B C D,
  (A ≃ C)
  → (∀ (a : A), B a ≃ D)
  → (Σ (a : A), B a) ≃ (C * D).
Proof.
intros A B C D HAC HBD.
unfold equivalence.
set (f xy := (pr₁ HAC (pr₁ xy), pr₁ (HBD (pr₁ xy)) (pr₂ xy))).
apply (existT _ f), qinv_isequiv.
set
 (g xy :=
    existT B (pr₁ HAC⁻⁻¹ (fst xy))
      (pr₁ (HBD (pr₁ HAC⁻⁻¹ (fst xy)))⁻⁻¹ (snd xy))).
apply (existT _ g); split; unfold "◦", "~~", id.
 intros (x, y).
 subst f g; simpl.
 destruct HAC as (f, ((g, Hg), (h, Hh))); simpl.
 unfold "◦", id in Hg; rewrite Hg.
 pose proof quasi_inv_comp_r (HBD (g x)) as H.
 unfold "◦", id in H; rewrite H; reflexivity.

 intros (x, y).
 subst f g; simpl.
 destruct HAC as (f, ((g, Hg), (h, Hh))); simpl.
 pose proof quasi_inv_l_eq_r f g h Hg Hh as H.
 unfold "◦", "~~", id in Hh, H.
 rewrite H, Hh.
 destruct (HBD x) as (f₁, ((g₁, Hg₁), (h₁, Hh₁))); simpl.
 pose proof quasi_inv_l_eq_r f₁ g₁ h₁ Hg₁ Hh₁ as H₁.
 unfold "◦", "~~", id in H₁, Hh₁.
 rewrite H₁, Hh₁; reflexivity.
Defined.

Definition semigroupstr_path_type_initial_version {A B} m a m' a'
    (ma := existT (Assoc A) m a)
    (ma' := existT (Assoc B) m' a')
    (p₁ : A = B) :
  (transport SemigroupStr p₁ ma = ma')
   ≃ {p : pr₁ (transport SemigroupStr p₁ ma) = m' &
      transport (Assoc B) p (pr₂ (transport SemigroupStr p₁ ma)) = a'}.
Proof.
apply hott_2_7_2.
Defined.

Definition semigroup_path_fun_tac {A B} m a m' a'
    (ma := existT (Assoc A) m a)
    (ma' := existT (Assoc B) m' a')
    (p₁ : A = B)
    (e := idtoeqv p₁) :
  pr₁ (transport SemigroupStr p₁ ma) = pr₁ ma'
  → (∀ y₁ y₂ : B, pr₁ e (m (pr₁ e⁻⁻¹ y₁) (pr₁ e⁻⁻¹ y₂)) = m' y₁ y₂).
Proof.
subst ma ma' e.
intros p y₁ y₂.
destruct p₁; simpl in p; simpl; unfold id.
apply Π_type.happly with (x := y₂).
apply Π_type.happly with (x := y₁).
apply p.
Defined.

Definition semigroup_path_inv_tac {A B} m a m' a'
    (ma := existT (Assoc A) m a)
    (ma' := existT (Assoc B) m' a')
    (p₁ : A = B)
    (e := idtoeqv p₁) :
  (∀ y₁ y₂ : B, pr₁ e (m (pr₁ e⁻⁻¹ y₁) (pr₁ e⁻⁻¹ y₂)) = m' y₁ y₂)
  → pr₁ (transport SemigroupStr p₁ ma) = pr₁ ma'.
Proof.
subst ma ma' e.
destruct p₁.
intros p; simpl in p; simpl.
apply Π_type.funext; intros y₁.
apply Π_type.funext; intros y₂.
apply p.
Defined.

Definition semigroup_path_fun {A B} m a m' a'
    (ma := existT (Assoc A) m a)
    (ma' := existT (Assoc B) m' a')
    (p₁ : A = B)
    (e := idtoeqv p₁) :
  pr₁ (transport SemigroupStr p₁ ma) = pr₁ ma'
  → (∀ y₁ y₂ : B, pr₁ e (m (pr₁ e⁻⁻¹ y₁) (pr₁ e⁻⁻¹ y₂)) = m' y₁ y₂)
:=
  match p₁ in (_ = X) return
    ∀ m₁ a₁,
    pr₁ (transport SemigroupStr p₁ (existT (Assoc A) m a)) =
    pr₁ (existT (Assoc X) m₁ a₁)
    → ∀ x₁ x₂ : X,
      pr₁ (idtoeqv p₁) (m (pr₁ (idtoeqv p₁)⁻⁻¹ x₁) (pr₁ (idtoeqv p₁)⁻⁻¹ x₂)) =
      m₁ x₁ x₂
  with
  | eq_refl _ => λ m₁ a₁ p x₁ x₂, Π_type.happly (Π_type.happly p x₁) x₂
  end m' a'.

Definition semigroup_path_inv {A B} m a m' a'
    (ma := existT (Assoc A) m a)
    (ma' := existT (Assoc B) m' a')
    (p₁ : A = B)
    (e := idtoeqv p₁) :
  (∀ y₁ y₂ : B, pr₁ e (m (pr₁ e⁻⁻¹ y₁) (pr₁ e⁻⁻¹ y₂)) = m' y₁ y₂)
  → pr₁ (transport SemigroupStr p₁ ma) = pr₁ ma'
:=
  match
    p₁ in (_ = X) return
      ∀ m' a',
       (∀ y₁ y₂,
        pr₁ (idtoeqv p₁) (m (pr₁ (idtoeqv p₁)⁻⁻¹ y₁)
          (pr₁ (idtoeqv p₁)⁻⁻¹ y₂)) =
        m' y₁ y₂)
       → pr₁ (transport SemigroupStr p₁ (existT (Assoc A) m a)) =
         pr₁ (existT (Assoc X) m' a')
  with
  | eq_refl _ => λ m' a' p, Π_type.funext (λ y₁, Π_type.funext (p y₁))
  end m' a'.

Definition semigroupstr_path_type {A B} m a m' a'
    (ma := existT (Assoc A) m a)
    (ma' := existT (Assoc B) m' a')
    (p₁ : A = B)
    (e := idtoeqv p₁)
(**)
    (m₁ := transport (λ X, X → X → X) (ua e) m)
    (a₁ :=
       transport (λ xu, Assoc (pr₁ xu) (pr₂ xu)) (pair⁼ (ua e) (eq_refl m₁)) a)
(**)
:
  (transport SemigroupStr p₁ ma = ma') ≃
  (Π (y₁ : B), Π (y₂ : B), pr₁ e (m (pr₁ e⁻⁻¹ y₁) (pr₁ e⁻⁻¹ y₂)) = m' y₁ y₂)
(**)
  * (a₁ = (λ b₁ b₂ b₃, (pre_hott_2_14_3 e m a b₁ b₂ b₃)⁻¹)).
(**)
Proof.
(* a₁ = pre_hott_2_14_3 ... is put here instead of a = hott_2_14_3...
   because the proof of hott_2_14 has not been done, the book does not
   say how to prove it. But it prevents this proof to be completed :-( *)
eapply equiv_compose; [ eapply hott_2_7_2 | idtac ].
apply eq_pair_dep_pair.
 apply (existT _ (semigroup_path_fun m a m' a' p₁)), qinv_isequiv.
 apply (existT _ (semigroup_path_inv m a m' a' p₁)).
 split; simpl.
  unfold semigroup_path_fun, semigroup_path_inv; simpl.
  subst e; destruct p₁; simpl.
  unfold "◦", "~~", id; intros f.
  apply Π_type.funext; intros y₁.
  apply Π_type.funext; intros y₂.
  do 2 rewrite Π_type.funext_quasi_inverse_of_happly.
  reflexivity.

  unfold semigroup_path_fun, semigroup_path_inv; simpl.
  subst e; destruct p₁; simpl.
  unfold "◦", "~~", id; intros f.
  destruct f; simpl.
  eapply invert, compose; [ apply Π_type.funext_identity | idtac ].
  apply ap, Π_type.funext; intros x.
  apply Π_type.funext_identity.

 intros q; simpl in q.
Abort. (* not done; see remark above *)

End EqStr.

(* rest of §2.14 given up because of missing proof of 2.14.2 *)

Module UnivProp.

Import cartesian.

(* 2.15 Universal properties *)

Definition hott_2_15_1 {X A B} : (X → A * B) → (X → A) * (X → B) :=
  λ f, (pr₁ ◦ f, pr₂ ◦ f).

Definition fun_prod_prod {X A B} : (X → A) * (X → B) → (X → A * B) :=
  λ p x, (pr₁ p x, pr₂ p x).

(* "Theorem 2.15.2. (2.15.1) is an equivalence." *)

(* their proof requires 2.6.2 but I did not use it *)
Definition hott_2_15_2_tac {X A B} : (X → A * B) ≃ (X → A) * (X → B).
Proof.
apply (existT _ hott_2_15_1), qinv_isequiv.
apply (existT _ fun_prod_prod).
unfold hott_2_15_1, fun_prod_prod, "◦", "~~", id; simpl.
split; [ intros (Ha, Hb); reflexivity | idtac ].
intros p.
eapply Π_type.funext; intros x.
destruct (p x); reflexivity.
Defined.

Definition hott_2_15_2 {X A B} : (X → A * B) ≃ (X → A) * (X → B) :=
  existT isequiv hott_2_15_1
    (qinv_isequiv hott_2_15_1
       (existT _
          fun_prod_prod
          ((λ x : (X → A) * (X → B),
              let (Ha, Hb) return (pr₁ x, pr₂ x) = x := x in
              eq_refl (Ha, Hb)),
           (λ p : X → A * B,
            Π_type.funext
              (λ x,
               let (a, b) as p1 return (pr₁ p1, pr₂ p1) = p1 := p x in
               eq_refl (a, b)))))).

Definition hott_2_15_4 {X A B} :
  (Π (x : X), (A x * B x)) → (Π (x : X), A x) * (Π (x : X), B x) :=
  λ f, ((λ x, (pr₁ (f x))), (λ x, (pr₂ (f x)))).

Definition fun_dep_fun_prod_prod {X A B} :
    (Π (x : X), A x) * (Π (x : X), B x) → (Π (x : X), (A x * B x)) :=
  λ p x, (pr₁ p x, pr₂ p x).

(* "Theorem 2.15.5. (2.15.4) is an equivalence." *)

(* proof 'left to the reader', I do what I want :-) *)
Definition hott_2_15_5_tac {X A B} :
  (Π (x : X), (A x * B x)) ≃ (Π (x : X), A x) * (Π (x : X), B x).
Proof.
apply (existT _ hott_2_15_4), qinv_isequiv.
apply (existT _ fun_dep_fun_prod_prod).
unfold hott_2_15_4, fun_dep_fun_prod_prod, "◦", "~~", id; simpl.
split; [ intros (Ha, Hb); reflexivity | idtac ].
intros p.
eapply Π_type.funext; intros x.
destruct (p x); reflexivity.
Defined.

Definition hott_2_15_5 {X A B} :
   (Π (x : X), (A x * B x)) ≃ (Π (x : X), A x) * (Π (x : X), B x) :=
  existT isequiv hott_2_15_4
    (qinv_isequiv hott_2_15_4
       (existT _
          fun_dep_fun_prod_prod
          ((λ x : (∀ x : X, A x) * (∀ x : X, B x),
              let (Ha, Hb) return (pr₁ x, pr₂ x) = x := x in
              eq_refl (Ha, Hb)),
           (λ p : ∀ x : X, A x * B x,
              Π_type.funext
                (λ x,
                 let (a, b) as p1 return (pr₁ p1, pr₂ p1) = p1 := p x in
                 eq_refl (a, b)))))).

(* "Just as Σ-types are a generalization of cartesian products, they
    satisfy a generalized version of this universal property. Jumping
    right to the dependently typed version, suppose we have a type X
    and type families A : X → U and P : Π (x:X) A(x) → U. Then we have
    a function" *)

Definition hott_2_15_6 {X A} P :
  (Π (x : X), Σ (a : A x), P x a) →
  (Σ (g : Π (x : X), A x), Π (x : X), P x (g x))
:=
  λ f,
  existT (λ g, Π (x : X), P x (g x))
    (λ x, Σ_type.pr₁ (f x))
    (λ x, Σ_type.pr₂ (f x)).

Definition fun_dep_prod_prod  {X A} P :
    (Σ (g : Π (x : X), A x), Π (x : X), P x (g x)) →
    (Π (x : X), Σ (a : A x), P x a) :=
  λ p x, existT _ (Σ_type.pr₁ p x) (Σ_type.pr₂ p x).

(* "Theorem 2.15.7. (2.15.6) is an equivalence." *)

(* their proof requires 2.7.3 but I did not use it *)
Definition hott_2_15_7 {X A} P :
  (Π (x : X), Σ (a : A x), P x a) ≃
  (Σ (g : Π (x : X), A x), Π (x : X), P x (g x)).
Proof.
apply (existT _ (hott_2_15_6 P)), qinv_isequiv.
apply (existT _ (fun_dep_prod_prod P)).
unfold hott_2_15_6, fun_dep_prod_prod, "◦", "~~", id; simpl.
split; [ intros (Ha, Hb); reflexivity | idtac ].
intros p.
eapply Π_type.funext; intros x.
destruct (p x); reflexivity.
Defined.

(* "This is noteworthy because the propositions-as-types interpretation
    of (2.15.6) is “the axiom of choice”." *)

(* @hott_2_15_6
     : ∀ (X : Type) (A : X → Type) (P : ∀ x : X, A x → Type),
       (∀ x : X, {a : A x & P x a})
       → {g : ∀ x : X, A x & ∀ x : X, P x (g x)}
 *)

(* "In the case of cartesian products, the nondependent version simply
    expresses the cartesian closure adjunction:" *)

Definition cart_clos_adjun {A B C} : ((A * B) → C) ≃ (A → (B → C)).
Proof.
apply (existT _ (λ g a b, g (a, b))), qinv_isequiv.
apply (existT _ (λ f x, f (pr₁ x) (pr₂ x))).
unfold "◦", "~~", id; simpl.
split.
 intros x.
 apply Π_type.funext; intros a.
 apply Π_type.funext; intros b.
 reflexivity.

 intros f.
 apply Π_type.funext; intros x.
 destruct x; reflexivity.
Defined.

(* "The dependent version of this is formulated for a type family
    C : A x B → U:" *)

Definition dep_clos_adjun {A B C} :
  (Π (w : A * B), C w) ≃ (Π (x : A), Π (y : B), C (x, y)).
Proof.
apply (existT _ (λ g a b, g (a, b))), qinv_isequiv.
apply (existT _ (λ f (w : A * B), let (a, b) return (C _) := w in f a b)).
unfold "◦", "~~", id; simpl.
split.
 intros f.
 apply Π_type.funext; intros a.
 apply Π_type.funext; intros b.
 reflexivity.

 intros f.
 apply Π_type.funext; intros x.
 destruct x; reflexivity.
Defined.

(* "There is also a version for Σ-types: (2.15.9)" *)

Definition Σ_clos_adjun {A B C} :
  (Π (w : Σ (x : A), B x), C w) ≃ (Π (x : A), Π (y : B x), C (existT _ x y)).
Proof.
apply (existT _ (λ f a (b : B a), f (existT _ a b))), qinv_isequiv.
apply
  (existT _
     (λ f (w : Σ (x : A), B x), let (a, b) return (C _) := w in f a b)).
unfold "◦", "~~", id; simpl.
split.
 intros f.
 apply Π_type.funext; intros a.
 apply Π_type.funext; intros b.
 reflexivity.

 intros f.
 apply Π_type.funext; intros x.
 destruct x; reflexivity.
Defined.

(* "path induction is the right-to-left direction of an equivalence as
    follows: (2.5.10)" *)

Definition path_ind_equiv {A} a B :
  (Π (x : A), Π (p : a = x), B x p) ≃ B a (eq_refl a).
Proof.
apply (existT _ (λ f : ∀ x p, B x p, f a (eq_refl a))), qinv_isequiv.
apply
  (existT _
     (λ p x q, match q in (_ = y) return (B y q) with eq_refl _ => p end)).
unfold "◦", "~~", id; simpl.
split; [ reflexivity | idtac ].
intros f.
apply Π_type.funext; intros x.
apply Π_type.funext; intros q.
destruct q; reflexivity.
Defined.

(* "the expected explicit construction works: given f : A → C and
    g : B → C, we define (2.15.11)" *)

Definition hott_2_15_11 {A B C} (f : A → C) (g : B → C) :=
  Σ (a : A), Σ (b : B), (f a = g b).

(* this type is not necessarily inhabited since A (or B) can be empty *)

End UnivProp.

(* "Exercise 2.1. Show that the three obvious proofs of Lemma 2.1.2 are
    pairwise equal." *)

(* Quote from §2.1: "Lemma 2.1.2 has three obvious proofs: we could do
   induction over p, induction over q, or induction over both of
   them. If we proved it three different ways, we would have three
   different elements of the same type. It’s not hard to show that
   these three elements are equal (see Exercise 2.1), but as they are
   not definitionally equal, there can still be reasons to prefer one
   over another." *)

Definition hott_2_1_2_proof_1_tac {A} {x y z : A} : x = y → y = z → x = z.
Proof.
intros p q.
destruct p; assumption.
Defined.

Definition hott_2_1_2_proof_2_tac {A} {x y z : A} : x = y → y = z → x = z.
Proof.
intros p q.
destruct q; assumption.
Defined.

Definition hott_2_1_2_proof_3_tac {A} {x y z : A} : x = y → y = z → x = z.
Proof.
intros p q.
destruct p, q; reflexivity.
Defined.

(* the same proofs as expressions *)

Definition hott_2_1_2_proof_1 {A} {x y z : A} : x = y → y = z → x = z :=
  λ p q,
  match p with
  | eq_refl _ => id
  end q.

Definition hott_2_1_2_proof_2 {A} {x y z : A} : x = y → y = z → x = z :=
  λ p q,
  match q with
  | eq_refl _ => p
  end.

Definition hott_2_1_2_proof_3 {A} {x y z : A} : x = y → y = z → x = z :=
  λ p q,
  match p with
  | eq_refl _ =>
      λ r : x = z,
      match r with
      | eq_refl _ => eq_refl x
      end
  end q.

Definition hott_2_1_2_proof_1_eq_proof_2_tac {A} {x y z : A}
    (p : x = y) (q : y = z) :
  hott_2_1_2_proof_1 p q = hott_2_1_2_proof_2 p q.
Proof.
unfold hott_2_1_2_proof_1, hott_2_1_2_proof_2.
destruct p, q; reflexivity.
Defined.

Definition hott_2_1_2_proof_2_eq_proof_3_tac {A} {x y z : A}
    (p : x = y) (q : y = z) :
  hott_2_1_2_proof_2 p q = hott_2_1_2_proof_3 p q.
Proof.
unfold hott_2_1_2_proof_2, hott_2_1_2_proof_3.
destruct p; reflexivity.
Defined.

Definition hott_2_1_2_proof_3_eq_proof_1_tac {A} {x y z : A}
    (p : x = y) (q : y = z) :
  hott_2_1_2_proof_3 p q = hott_2_1_2_proof_1 p q.
Proof.
unfold hott_2_1_2_proof_3, hott_2_1_2_proof_1.
destruct p, q; reflexivity.
Defined.

Definition hott_2_1_2_proof_1_eq_proof_2 {A} {x y z : A}
    (p : x = y) (q : y = z) :
  hott_2_1_2_proof_1 p q = hott_2_1_2_proof_2 p q
:=
  match p in (_ = t) return
    ∀ r : t = z,
    match p with eq_refl _ => id end r =
    match r with eq_refl _ => p end
  with
  | eq_refl _ => λ r, match r with eq_refl _ => eq_refl (eq_refl x) end
  end q.

Definition hott_2_1_2_proof_2_eq_proof_3 {A} {x y z : A}
    (p : x = y) (q : y = z) :
  hott_2_1_2_proof_2 p q = hott_2_1_2_proof_3 p q
:=
  match p return
    ∀ r,
    match r with eq_refl _ => p end =
    match p with
    | eq_refl _ => λ r : x = z, match r with eq_refl _ => eq_refl x end
    end r
  with
  | eq_refl _ => λ r : x = z, eq_refl (match r with eq_refl _ => eq_refl x end)
  end q.

Definition hott_2_1_2_proof_3_eq_proof_1 {A} {x y z : A}
    (p : x = y) (q : y = z) :
  hott_2_1_2_proof_3 p q = hott_2_1_2_proof_1 p q
:=
  match p return
    ∀ r,
    match p with
    | eq_refl _ => λ r : x = z, match r with eq_refl _ => eq_refl x end
    end r =
    match p with eq_refl _ => id end r
  with
  | eq_refl _ => λ r : x = z, match r with eq_refl _ => eq_refl (eq_refl x) end
  end q.

(* "Exercise 2.2. Show that the three equalities of proofs constructed
    in the previous exercise form a commutative triangle. In other
    words, if the three definitions of concatenation are denoted by
    (p •₁ q), (p •₂ q), and (p •₃ q), then the concatenated equality
          (p •₁ q) = (p •₂ q) = (p •₃ q)
    is equal to the equality
          (p •₁ q) = (p •₃ q)" *)

Notation "p '•₁' q" := (hott_2_1_2_proof_1_eq_proof_2 p q) (at level 50).
Notation "p '•₂' q" := (hott_2_1_2_proof_2_eq_proof_3 p q) (at level 50).
Notation "p '•₃' q" := (hott_2_1_2_proof_3_eq_proof_1 p q) (at level 50).

(* not sure it is what is required, their notations being incoherent,
   I think *)

Definition ex_2_2 {A} {x y z : A} (p : x = y) (q : y = z) : 
  (p •₁ q) • (p •₂ q) = (p •₃ q)⁻¹.
Proof.
destruct p, q; simpl.
reflexivity.
Defined.

(* "Exercise 2.3. Give a fourth, different, proof of Lemma 2.1.2, and
    prove that it is equal to the others. *)

(* with induction on q before the induction on p *)

Definition hott_2_1_2_proof_4_tac {A} {x y z : A} : x = y → y = z → x = z.
Proof.
intros p q.
destruct q, p; reflexivity.
Defined.

Definition hott_2_1_2_proof_4 {A} {x y z : A} : x = y → y = z → x = z :=
  λ p q,
  match q with
  | eq_refl _ =>
      match p with
      | eq_refl _ => eq_refl x
      end
  end.

(* implied by proof 3 *)

Definition hott_2_1_2_proof_3_eq_proof_4_tac {A} {x y z : A}
    (p : x = y) (q : y = z) :
  hott_2_1_2_proof_3 p q = hott_2_1_2_proof_4 p q.
Proof.
unfold hott_2_1_2_proof_3, hott_2_1_2_proof_4.
destruct p; reflexivity.
Defined.

(* implies proof 1 *)

Definition hott_2_1_2_proof_4_eq_proof_1_tac {A} {x y z : A}
    (p : x = y) (q : y = z) :
  hott_2_1_2_proof_4 p q = hott_2_1_2_proof_1 p q.
Proof.
unfold hott_2_1_2_proof_4, hott_2_1_2_proof_1.
destruct p, q; reflexivity.
Defined.

(* same proofs as above but with the proof expressions *)

Definition hott_2_1_2_proof_3_eq_proof_4 {A} {x y z : A}
    (p : x = y) (q : y = z) :
  hott_2_1_2_proof_3 p q = hott_2_1_2_proof_4 p q
:=
  match p in (_ = t) return
    ∀ r : t = z,
    match p with
    | eq_refl _ => λ r : x = z, match r with eq_refl _ => eq_refl x end
    end r =
    match r with
    | eq_refl _ => match p with eq_refl _ => eq_refl x end
    end
  with
  | eq_refl _ => λ r, eq_refl (match r with eq_refl _ => eq_refl x end)
  end q.

Definition hott_2_1_2_proof_4_eq_proof_1 {A} {x y z : A}
    (p : x = y) (q : y = z) :
  hott_2_1_2_proof_4 p q = hott_2_1_2_proof_1 p q
:=
  match p in (_ = t) return
    ∀ r : t = z,
    match r with eq_refl _ => match p with eq_refl _ => eq_refl x end end =
    match p with eq_refl _ => id end r
  with
  | eq_refl _ => λ r, match r with eq_refl _ => eq_refl (eq_refl x) end
  end q.

(* "Exercise 2.4. Define, by induction on n, a general notion of
    n-dimensional path in a type A, simultaneously with the type
    of boundaries for such paths." *)

(* borrowed to Adam Chlipala's code found in the Web *)
Inductive ilist A : nat → Type :=
  | Nil : ilist A 0
  | Cons : ∀ n, A → ilist A n → ilist A (S n).
Arguments Nil [A].
Arguments Cons [A] [n] x l.

Fixpoint n_dim_path' {A nx ny} (x : ilist A nx) (y : ilist A ny) :=
  match x with
  | Nil => tt = tt
  | Cons x₁ x₂ =>
      match y with
      | Nil => tt = tt
      | Cons y₁ y₂ => (x₁ = y₁) ∧ n_dim_path' x₂ y₂
      end
  end.

Definition n_dim_path {A n} (x y : ilist A n) := n_dim_path' x y.

(* Not sure it it good, since it does not use type dependent matching
   and I fear that some extra proofs are then required to be sure that
   all equalities in x and y are taken into account. Well, let's go to
   the next exercise... *)

(* "Exercise 2.5. Prove that the functions (2.3.6) and (2.3.7) are
    inverse equivalences." *)

Definition ex_2_5_tac {A B} {x y : A} (p : x = y) (f : A → B) :
  (f x = f y) ≃ (p⁎ (f x) = f y).
Proof.
apply (existT _ (hott_2_3_6 p f)), qinv_isequiv.
apply (existT _ (hott_2_3_7 p f)).
unfold hott_2_3_6, hott_2_3_7.
unfold "◦", "~~", id; simpl.
split.
 intros q.
 eapply compose; [ eapply compose_assoc | idtac ].
 eapply compose; [ eapply dotr, compose_invert_r | apply lu ].

 intros q.
 eapply compose; [ eapply compose_assoc | idtac ].
 eapply compose; [ eapply dotr, compose_invert_l | apply lu ].
Defined.

Definition ex_2_5 {A B} {x y : A} (p : x = y) (f : A → B) :
  (f x = f y) ≃ (p⁎ (f x) = f y)
:=
  existT _
    (hott_2_3_6 p f)
    (qinv_isequiv (hott_2_3_6 p f)
       (existT _ (hott_2_3_7 p f)
          (λ q,
           compose_assoc (transportconst B p (f x))
             (transportconst B p (f x))⁻¹ q
           • (compose_invert_r (transportconst B p (f x)) •r q)
           • lu (eq_refl (transport (λ _ : A, B) p (f x)) • q),
           λ q : f x = f y,
           compose_assoc (transportconst B p (f x))⁻¹ 
             (transportconst B p (f x)) q
           • (compose_invert_l (transportconst B p (f x)) •r q)
           • lu (eq_refl (f x) • q)))).

(* "Exercise 2.6. Prove that if p : x = y, then the function
        (p • -) : (y = z) → ( x = z)
    is an equivalence." *)

Definition fun_2_6 {A} {x y z : A} (p : x = y) :
  y = z → x = z
:=
  λ q : y = z, p • q.

Definition ex_2_6_tac {A} {x y z : A} (p : x = y) : (y = z) ≃ (x = z).
Proof.
apply (existT _ (λ q, p • q)), qinv_isequiv.
apply (existT _ (λ q, p⁻¹ • q)).
unfold "◦", "~~", id.
split.
 intros q.
 eapply compose; [ eapply compose_assoc | idtac ].
 eapply compose; [ eapply dotr, compose_invert_r | apply lu ].

 intros q.
 eapply compose; [ eapply compose_assoc | idtac ].
 eapply compose; [ eapply dotr, compose_invert_l | apply lu ].
Defined.

Definition ex_2_6 {A} {x y z : A} (p : x = y) : (y = z) ≃ (x = z)
:=
  existT isequiv (λ q : y = z, p • q)
    (qinv_isequiv _
       (existT _ (λ q : x = z, p⁻¹ • q)
          (λ q : x = z,
           compose_assoc p p⁻¹ q • (compose_invert_r p •r q)
           • lu (eq_refl x • q),
           λ q : y = z,
           compose_assoc p⁻¹ p q • (compose_invert_l p •r q)
           • lu (eq_refl y • q)))).

(* "Exercise 2.7. State and prove a generalization of Theorem 2.6.5
    from cartesian products to Σ-types." *)

(* already done: see hott_2_7_5 *)

(* "Exercise 2.8. State and prove an analogue of Theorem 2.6.5 for
    coproducts." *)

Section ex_2_8.

Import Σ_type2.

Definition ex_2_8_tac {A B A' B'} (x₁ y₁ : A) (x₂ y₂ : B)
    (g : A → A') (h : B → B')
    (f := λ x, match x with inl a => inl (g a) | inr b => inr (h b) end)
    (p : x₁ = y₁) (q : x₂ = y₂) :
  (ap f (inl_equal p) = inl_equal (ap g p)) *
  (ap f (inr_equal q) = inr_equal (ap h q)).
Proof.
split; [ destruct p | destruct q ]; reflexivity.
Defined.

Definition ex_2_8 {A B A' B'} (x₁ y₁ : A) (x₂ y₂ : B)
    (g : A → A') (h : B → B')
    (f := λ x, match x with inl a => inl (g a) | inr b => inr (h b) end)
    (p : x₁ = y₁) (q : x₂ = y₂) :
  (ap f (inl_equal p) = inl_equal (ap g p)) *
  (ap f (inr_equal q) = inr_equal (ap h q))
:=
  let f x := match x with inl a => inl (g a) | inr b => inr (h b) end in
  pair
    match p in (_ = y) return (ap f (inl_equal p) = inl_equal (ap g p)) with
    | eq_refl _ => eq_refl (inl_equal (ap g (eq_refl x₁)))
    end
    match q in (_ = y) return (ap f (inr_equal q) = inr_equal (ap h q))
    with
    | eq_refl _ => eq_refl (inr_equal (ap h (eq_refl x₂)))
    end.

End ex_2_8.

(* "Exercise 2.9. Prove that coproducts have the expected universal
    property,
           (A + B → X) ≃ (A → X) x (B → X).
    Can you generalize this to an equivalence involving dependent
    functions?" *)

Section ex_2_9.

Import cartesian.

Definition coproduct_map {A B C} f g (x : A + B) : C :=
  match x with inl a => f a | inr b => g b end.

(* OK, but I had to use function extensionality; is it normal? *)
Definition ex_2_9_tac {X A B} : (A + B → X) ≃ (A → X) * (B → X).
Proof.
apply (existT _ (λ f, (f ◦ inl, f ◦ inr))), qinv_isequiv.
apply (existT _ (λ f x, coproduct_map (pr₁ f) (pr₂ f) x)).
unfold "◦", "~~", id; simpl.
split; [ intros (f, g); reflexivity | intros f ].
apply Π_type.funext; intros x.
destruct x as [a| b]; reflexivity.
Defined.

Definition ex_2_9 {X A B} : (A + B → X) ≃ (A → X) * (B → X)
:=
  existT isequiv (λ f, (f ◦ inl, f ◦ inr))
    (qinv_isequiv (λ f, (f ◦ inl, f ◦ inr))
       (existT _ (λ f x, coproduct_map (pr₁ f) (pr₂ f) x)
          (λ x : (A → X) * (B → X),
           let (f, g) return ((pr₁ x, pr₂ x) = x) := x in
           eq_refl (f, g),
           λ f : A + B → X,
           Π_type.funext
             (λ x,
              match x with
              | inl a => eq_refl (f (inl a))
              | inr b => eq_refl (f (inr b))
              end)))).

Definition dep_fun_map {A B X} f g (x : A + B) : X x :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Definition ex_2_9_dep_fun_tac {A B X} :
  (Π (x : A + B), X x) ≃ (Π (x : A), X (inl x)) * (Π (x : B), X (inr x)).
Proof.
apply (existT _ (λ f, (λ a, f (inl a), λ b, f (inr b)))), qinv_isequiv.
apply
  (existT _
     (λ (fg : (∀ a, X (inl a)) * (∀ b, X (inr b))) x,
      let (f, g) := fg in
      dep_fun_map f g x)).
unfold "◦", "~~", id; simpl.
split; [ intros (f, g); reflexivity | intros f ].
apply Π_type.funext; intros x.
destruct x as [a| b]; reflexivity.
Defined.

Definition ex_2_9_dep_fun {A B X} :
  (Π (x : A + B), X x) ≃ (Π (x : A), X (inl x)) * (Π (x : B), X (inr x))
:=
existT isequiv (λ f, (λ a, f (inl a), λ b, f (inr b)))
  (qinv_isequiv (λ f, (λ a, f (inl a), λ b, f (inr b)))
     (existT _
        (λ (fg : (∀ a : A, X (inl a)) * (∀ b : B, X (inr b))) x,
         let (f, g) := fg in dep_fun_map f g x)
        (λ fg : (∀ x : A, X (inl x)) * (∀ x : B, X (inr x)),
         let (f, g) as p return
           ((λ a : A, let (f, _) := p in f a,
            λ b : B, let (_, g) := p in g b) = p) := fg in
         eq_refl (f, g),
         λ f : ∀ x : A + B, X x,
         Π_type.funext
           (λ x : A + B,
            match x with
            | inl a => eq_refl (f (inl a))
            | inr b => eq_refl (f (inr b))
            end)))).

End ex_2_9.

(* "Exercise 2.10. Prove that Σ-types are “associative”, in that for
    any A : U and families B : A → U and C : (Σ (x : A), B x) → U, we
    have
       (Σ (x : A), Σ (y : B x), C (x, y)) ≃ Σ (p : Σ (x : A), B x), C p *)

Definition ex_2_10 {A B C} :
  (Σ (x : A), Σ (y : B x), C (existT _ x y)) ≃ (Σ (p : Σ (x : A), B x), C p).
Proof.
apply
  (existT _
    (λ xyf,
     match xyf with
     | existT _ x (existT _ y f) => existT C (existT B x y) f
     end)).
apply qinv_isequiv.
apply
  (existT _
     (λ xyf : {p : {x : A & B x} & C p},
      match xyf with
      | existT _ (existT _ x y) f =>
          (λ f : C (existT B x y), existT _ x (existT _ y f)) f
      end)).
unfold "◦", "~~", id; simpl.
split; [ intros ((x, y), f) | intros (x, (y, f)) ]; reflexivity.
Defined.

(* "Exercise 2.11: A (homotopy) commutative square
                   h
               P ----→ A
               |       |
             k |       | f
               ↓       ↓
               B ----→ C
                   g
    consists of functions f, g, h, and k as shown, together with a
    path f ◦ h = g ◦ k. Note that this is exactly an element of the
    pullback (P → A) x_{P→C} (P → B) as defined in (2.15.11). A
    commutative square is called a (homotopy) pullback square if
    for any X, the induced map
            (X → P) → (X → A) x_{X→C} (X → B)
    is an equivalence. Prove that the pullback P :≡ A x_C B defined
    in (2.15.11) is the corner of a pullback square." *)

(* same definition as hott_2_15_11, but renamed 'pullback' *)
Definition pullback {A B C} (f : A → C) (g : B → C) :=
  Σ (a : A), Σ (b : B), (f a = g b).

(* Well, I am confused. I don't understand what they are talking about.
   I give up. *)

(* "Exercise 2.12. Suppose given two commutative squares..." *)

(* Still a game with pullbacks; I don't know what are those things...
   I see that later. *)

(* "Exercise 2.13. Show that (2 ≃ 2) ≃ 2." *)

(* idea: associate e.g.
   - the bijection id/id to true
   - the bijection negb/negb to false.
   This is a bijection *)


Definition uip_refl_bool {b : bool} : ∀ (p : b = b), p = eq_refl b.
Proof.
intros.
destruct b; refine (match p with eq_refl _ => _ end); reflexivity.
Defined.
(* actually already in Coq library as Eqdep_dec.UIP_refl_bool, but
   done again for sport. *)

Definition bool_eq_bool_id : bool ≃ bool :=
  existT isequiv id
    (qinv_isequiv id (existT _ id (λ _, eq_refl _, λ _, eq_refl _))).

Definition bool_eq_bool_negb : bool ≃ bool :=
  existT isequiv negb
    (qinv_isequiv negb
       (existT (λ g, ((negb ◦ g ~~ id) * (g ◦ negb ~~ id))%type) negb
          (λ b : bool,
           if b return (negb (negb b) = b) then eq_refl true
           else eq_refl false,
          λ b : bool,
          if b return (negb (negb b) = b) then eq_refl true
          else eq_refl false))).

Definition ex_2_13_tac : (bool ≃ bool) ≃ bool.
Proof.
apply (existT _ (λ p : bool ≃ bool, Π_type.pr₁ p true)).
apply qinv_isequiv.
apply
 (existT _ (λ b : bool, if b then bool_eq_bool_id else bool_eq_bool_negb)).
unfold bool_eq_bool_id, bool_eq_bool_negb.
unfold "◦", "~~", id; simpl.
split; [ intros x; destruct x; reflexivity |  ].
intros (f, ((g, Hg), (h, Hh))); simpl.
pose proof (EqStr.quasi_inv_l_eq_r f g h Hg Hh) as Hgh.
unfold "◦", "~~", id in Hg, Hh, Hgh.
pose proof (EqStr.quasi_inv_l_eq_r f g h Hg Hh) as H.
set (b := f true).
assert (Hb : f true = b) by (subst b; reflexivity).
destruct b.
 assert (H1 : f ~~ id).
  intros b.
  destruct b; [ assumption | unfold id ].
  destruct (bool_dec (f false) false) as [H1| H1]; [ assumption | ].
  apply not_false_is_true in H1.
  pose proof (Hg false) as H2.
  destruct (g false); [  | assumption ].
  rewrite Hb in H2; discriminate H2.

  assert (H2 : g ~~ id).
   intros b.
   destruct (bool_dec (g b) b) as [H2| H2]; [ assumption |  ].
   destruct b.
    apply not_true_is_false in H2.
    pose proof (Hh true) as H3.
    rewrite Hb in H3.
    rewrite H, H3 in H2.
    discriminate H2.

    apply not_false_is_true in H2.
    pose proof (Hg false) as H3.
    rewrite H2, Hb in H3.
    discriminate H3.

   assert (H3 : h ~~ id).
    eapply homotopy_trans2; [  | apply H2 ].
    apply homotopy_sym2; assumption.

    apply Π_type.funext in H1.
    apply Π_type.funext in H2.
    apply Π_type.funext in H3.
    subst f g h; unfold id; simpl.
    apply apf; [ reflexivity |  ].
    apply apf.
     apply apf; [ reflexivity |  ].
     apply apf; [ reflexivity |  ].
     apply Π_type.funext; intros b.
     symmetry; apply uip_refl_bool.
     apply apf; [ reflexivity | ].
     apply Π_type.funext; intros b.
     symmetry; apply uip_refl_bool.

 assert (H1 : f ~~ negb).
  intros b.
  destruct b; [ assumption |  ].
  destruct (bool_dec (f false) true) as [H1| H1]; [ assumption | ].
  apply not_true_is_false in H1.
  pose proof (Hg true) as H2.
  destruct (g true); [  | assumption ].
  rewrite Hb in H2; discriminate H2.

  assert (H2 : g ~~ negb).
   intros b.
   destruct (bool_dec (g b) (negb b)) as [H2| H2]; [ assumption |  ].
   destruct b.
    apply not_false_is_true in H2.
    pose proof (Hg true) as H3.
    rewrite H2, Hb in H3; discriminate H3.

    apply not_true_is_false in H2.
    pose proof (Hh true) as H3.
    rewrite Hb, <- H, H2 in H3; discriminate H3.

   assert (H3 : h ~~ negb).
    eapply homotopy_trans2; [  | apply H2 ].
    apply homotopy_sym2; assumption.

    apply Π_type.funext in H1.
    apply Π_type.funext in H2.
    apply Π_type.funext in H3.
    subst f g h; unfold id; simpl.
    apply apf; [ reflexivity | ].
    apply apf.
     apply apf; [ reflexivity |  ].
     apply apf; [ reflexivity |  ].
     apply Π_type.funext; intros b.
     destruct b; symmetry; apply Eqdep_dec.UIP_refl_bool.

     apply apf; [ reflexivity | ].
     apply Π_type.funext; intros b.
     destruct b; symmetry; apply Eqdep_dec.UIP_refl_bool.
Defined.

(* "Exercise 2.14. Suppose we add to type theory the 'equality
    reflection rule' which says that if there is an element p : x = y,
    then in fact x ≡ y. Prove that for any p : x = x we have p ≡ reflx.
    (This implies that every type is a set in the sense to be
    introduced in §3.1; see §7.2.)" *)

(* Not easy to prove in Coq since there is no way to set x ≡ y as a
   proposition. We must define a model of a type theory and reason
   with it. I give up. *)

(* "Exercise 2.15. Show that Lemma 2.10.5 can be strengthened to
        transport^B(p, -) =_{B(x)→ B(y)} idtoeqv(ap_{B}(p))
    without using function extensionality. (In this and other similar
    cases, the apparently weaker formulation has been chosen for
    readability and consistency.) *)

Print hott_2_10_5.

(* Well, it seems that my implementation did not use function
   extensionality anyway, but just induction of p. Perhaps I should
   look for a version with function extensionality to understand what
   was the initial idea? *)

(* "Exercise 2.16. Suppose that rather than function extensionality
    (Axiom 2.9.3), we suppose only the existence of an element
        funext : Π (A:U), Π (B:A→U), Π (f,g:Π(x:A),B(x)), (f~g) → (f=g)
    (with no relationship to happly assumed). Prove that in fact, this
    is sufficient to imply the whole function extensionality axiom
    (that happly is an equivalence). This is due to Voevodsky; its
    proof is tricky and may require concepts from later chapters." *)

Axiom funext2 :
  Π (A:U), Π (B:A→U), Π (f:Π(x:A),B x), Π (g:Π(x:A),B x),
  (∀ x, f x = g x) → (f = g).

Check @Π_type.happly.

Definition ex_2_16 {A B} (f g : Π (x : A), B x) : (f = g) ≃ (∀ x, f x = g x).
Proof.
apply
  (existT _
     (λ (p : f = g) (x : A),
      match p in (_ = h) return (f x = h x) with
      | eq_refl _ => eq_refl _
      end)).
apply qinv_isequiv.
apply (existT _ (funext2 A B f g)).
unfold "◦", "~~", id.
split.
 intros h.
 apply funext2; intros x.
Abort.
(* The proof is tricky, they say, and may require concept from later
   chapters. In that case, I wonder why they propose it as exercise
   in the present chapter. I give up. *)

(* "Exercise 2.17.
    (i) Show that if A≃A' and B≃B', then (A x B) ≃ (A' x B').
    (ii) Give two proofs of this fact, one using univalence and one
         not using it, and show that the two proofs are equal.
    (iii) Formulate and prove analogous results for the other type
          formers: Σ, →, Π, and +." *)

Section ex_2_17.

Import cartesian.

(* with univalence *)
Definition ex_2_17_ua_tac {A B A' B'} : A ≃ A' → B ≃ B' → A * B ≃ A' * B'.
Proof.
intros p q.
apply ua in p.
apply ua in q.
subst A B.
apply eqv_eq_refl.
Defined.

Definition ex_2_17_ua {A B A' B'} : A ≃ A' → B ≃ B' → A * B ≃ A' * B' :=
  λ (p : A ≃ A') (q : B ≃ B'),
  match
    match ua p in (_ = A') return (A' = A) with
    | eq_refl _ => eq_refl A
    end
  with
  | eq_refl _ =>
      match
        match ua q in (_ = B') return (B' = B) with
        | eq_refl _ => eq_refl B
        end
      with
      | eq_refl _ => eqv_eq_refl (A' * B')
      end
  end.

(* without univalence *)
Definition ex_2_17_not_ua_tac {A B A' B'} : A ≃ A' → B ≃ B' → A * B ≃ A' * B'.
Proof.
intros (f, ((f₁, Hf₁), (f₂, Hf₂))) (g, ((g₁, Hg₁), (g₂, Hg₂))).
apply (existT _ (λ x : A * B, (f (pr₁ x), g (pr₂ x)))).
apply qinv_isequiv.
apply (existT _ (λ x' : A' * B', (f₁ (pr₁ x'), g₁ (pr₂ x')))).
unfold "◦", "~~", id; simpl.
split.
 intros (a', b'); simpl.
 apply split_pair_eq.
 split; [ apply Hf₁ | apply Hg₁ ].

 intros (a, b); simpl.
 apply split_pair_eq.
 split.
  generalize Hf₂; intros H.
  eapply EqStr.quasi_inv_l_eq_r in H; [ | apply Hf₁ ].
  eapply compose; [ apply H | apply Hf₂ ].

  generalize Hg₂; intros H.
  eapply EqStr.quasi_inv_l_eq_r in H; [ | apply Hg₁ ].
  eapply compose; [ apply H | apply Hg₂ ].
Defined.

Definition ex_2_17_not_ua {A B A' B'} : A ≃ A' → B ≃ B' → A * B ≃ A' * B' :=
  λ (p : A ≃ A') (q : B ≃ B'),
  match p with
  | existT _ f (existT _ f₁ Hf₁, existT _ f₂ Hf₂) =>
      match q with
      | existT _ g (existT _ g₁ Hg₁, existT _ g₂ Hg₂) =>
          existT isequiv
             (λ x : A * B, (f (pr₁ x), g (pr₂ x)))
            (qinv_isequiv (λ x : A * B, (f (pr₁ x), g (pr₂ x)))
               (existT _
                  (λ x' : A' * B', (f₁ (pr₁ x'), g₁ (pr₂ x')))
                  (λ x : A' * B',
                   let (a', b') as p return
                     ((f (f₁ (pr₁ p)), g (g₁ (pr₂ p))) = p) := x
                   in
                   split_pair_eq (f (f₁ a')) a' (g (g₁ b')) b'
                     (Hf₁ a', Hg₁ b'),
                   λ x : A * B,
                   let (a, b) as p return
                     ((f₁ (f (pr₁ p)), g₁ (g (pr₂ p))) = p) := x in
                   split_pair_eq (f₁ (f a)) a (g₁ (g b)) b
                     (EqStr.quasi_inv_l_eq_r f f₁ f₂ Hf₁ Hf₂ (f a) • Hf₂ a,
                      EqStr.quasi_inv_l_eq_r g g₁ g₂ Hg₁ Hg₂ (g b) • Hg₂ b))))
      end
  end.

Definition ex_2_17_eq : @ex_2_17_ua = @ex_2_17_not_ua.
Proof.
unfold ex_2_17_ua, ex_2_17_not_ua.
apply Π_type.funext; intros A.
apply Π_type.funext; intros B.
apply Π_type.funext; intros A'.
apply Π_type.funext; intros B'.
apply Π_type.funext; intros (f, ((f₁, Hf₁), (f₂, Hf₂))).
apply Π_type.funext; intros (g, ((g₁, Hg₁), (g₂, Hg₂))); simpl.
unfold eq_rect_r; simpl.
unfold eq_rect; simpl.
unfold eq_sym; simpl.
(* seems complicated; I am not surprised *)
Abort.

(* remaining to do:
   (iii) Formulate and prove analogous results for the other type
         formers: Σ, →, Π, and +
   but I am tired, I do that later, I prefer attack chapter 3
*)

End ex_2_17.

(* Chapter 3 - Sets and logic *)

(* 3.1 Sets and n-types *)

(* Definition 3.1 *)

Definition isSet A := ∀ (x y : A) (p q : x = y), p = q.

(* personal solution *)
Definition ex_3_1_2_tac : isSet unit.
Proof.
intros x y p q.
destruct x, y.
refine (match p with eq_refl _ => _ end).
refine (match q with eq_refl _ => _ end).
reflexivity.
Defined.

Definition ex_3_1_2 : isSet unit :=
  λ (x y : unit),
  match x with
  | tt =>
      match y with
      | tt =>
          λ p q,
          match p with
          | eq_refl _ => match q with eq_refl _ => eq_refl _ end
          end
      end
  end.

(* "For by Theorem 2.8.1, for any x, y : 1 the type (x = y) is
    equivalent to 1. Since any two elements of 1 are equal, this
    implies that any two elements of x = y are equal." *)

(* hott_2_8_1 : ∀ x y : unit, (x = y) ≃ unit *)

Definition ex_3_1_2_alt_tac : isSet unit.
Proof.
intros x y p q.
pose proof hott_2_8_1 x y as r.
destruct r as (f, ((g, Hg), (h, Hh))).
unfold "◦", "~~", id in Hg, Hh.
pose proof Hh p as Hp.
pose proof Hh q as Hq.
destruct (f p), (f q).
subst p q; reflexivity.
Defined.

(* "Example 3.1.3. The type 0 is a set, for given any x, y : 0 we may
    deduce anything we like, by the induction principle of 0. *)

Definition ex_3_1_3_tac : isSet False.
Proof.
intros x y p q.
destruct x.
Defined.

Definition ex_3_1_3 : isSet False := λ x y, match x with end.

(* "Example 3.1.4. The type ℕ of natural numbers is also a set. This
    follows from Theorem 2.13.1, since all equality types x =_{ℕ} y
    are equivalent to either 1 or 0, and any two inhabitants of 1 or 0
    are equal. We will see another proof of this fact in Chapter 7. *)

(* ℕ.hott_2_13_1 : ∀ m n : nat, (m = n) ≃ ℕ.code m n *)

Print or.

Definition ℕ_code_equiv_1_or_0 m n :
  (ℕ.code m n ≃ unit) + (ℕ.code m n ≃ False).
Proof.
destruct (eq_nat_dec m n) as [H1| H1].
 left; subst m.
 apply (existT _ (λ c, tt)), qinv_isequiv.
 apply (existT _ (λ _, ℕ.r n)).
 unfold "◦", "~~", id; simpl.
 split; [ intros u; destruct u; reflexivity | ].
 intros c.
 induction n; [ destruct c; reflexivity | apply IHn ].

 right.
 apply (existT _ (λ c, H1 (ℕ.decode m n c))), qinv_isequiv.
 apply (existT _ (λ p : False, match p with end)).
 unfold "◦", "~~", id.
 split; [ intros p; destruct p | ].
 intros c; destruct (H1 (ℕ.decode m n c)).
Defined.

Definition ex_3_1_4_tac : isSet nat.
Proof.
intros m n p q.
pose proof ℕ.hott_2_13_1 m n as r.
pose proof ℕ_code_equiv_1_or_0 m n as s.
destruct s as [s| s].
 eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 unfold "◦", "~~", id in Hg, Hh.
 pose proof Hh p as Hp.
 pose proof Hh q as Hq.
 destruct (f p), (f q).
 subst p q; reflexivity.

 eapply equiv_compose in s; [ | apply r ].
 destruct s as (f, ((g, Hg), (h, Hh))).
 exfalso; apply f, p.
Defined.

Definition ex_3_1_4 : isSet nat :=
  λ (m n : nat) (p q : m = n),
  match ℕ_code_equiv_1_or_0 m n with
  | inl s =>
      match s ◦◦ ℕ.hott_2_13_1 m n with
      | existT _ f (existT _ g Hg, existT _ h Hh) =>
          match f p with
          | tt =>
              λ (Hp0 : h tt = p),
              match f q as u1 return (h u1 = q → p = q) with
              | tt =>
                  λ Hq0 : h tt = q,
                  eq_ind (h tt) (λ p0 : m = n, p0 = q)
                    (eq_ind (h tt)
                       (λ q0 : m = n, h tt = q0) (eq_refl _) q Hq0) p
                    Hp0
              end (Hh q)
          end (Hh p)
      end
  | inr s =>
      match s ◦◦ ℕ.hott_2_13_1 m n with
      | existT _ f _ => match f p with end
      end
  end.

(* "Example 3.1.5. If A and B are sets, then so is A × B." *)

(* not sure of what I've done in this proof, but I completed it;
   perhaps simplifiable, understandable? *)
Definition ex_3_1_5 {A B} : isSet A → isSet B → isSet (A * B).
Proof.
intros r s x y p q.
pose proof cartesian.hott_2_6_2 x y as e.
destruct x as (xa, xb).
destruct y as (ya, yb); simpl in e.
apply quasi_inv in e.
destruct e as (f, ((g, Hg), (h, Hh))).
unfold "◦", "~~", id in Hg, Hh.
pose proof Hh p as Hhp.
pose proof Hh q as Hhq.
destruct (f p) as (fpa, fpb).
destruct (f q) as (fqa, fqb).
pose proof r xa ya fpa fqa as Hra.
pose proof s xb yb fpb fqb as Hrb.
destruct Hra, Hrb.
destruct Hhp; assumption.
Defined.

(* "Similarly, if A is a set and B : A → U is such that each B(x) is a
    set, then Σ(x:A),B(x) is a set." *)

(* just like ex_3_1_5 above, not sure of what I've done in this proof,
   but I completed it; perhaps simplifiable, understandable too? *)
Definition ex_3_1_5_bis {A B} :
  isSet A → (Π (x : A), isSet (B x)) → isSet (Σ (x : A), B x).
Proof.
intros r s x y p q.
pose proof Σ_type.hott_2_7_2 B x y as e.
destruct x as (xa, xb).
destruct y as (ya, yb); simpl in e.
destruct e as (f, ((g, Hg), (h, Hh))).
unfold "◦", "~~", id in Hg, Hh.
pose proof Hh p as Hhp.
pose proof Hh q as Hhq.
destruct (f p) as (fpa, fpb).
destruct (f q) as (fqa, fqb).
pose proof r xa ya fpa fqa as Hra.
destruct Hhp.
subst fpa.
rewrite <- Hhq.
apply ap, ap, s.
Defined.

(* "Example 3.1.6. If A is any type and B : A → U is such that each
    B(x) is a set, then the type Π (x:A), B(x) is a set." *)

Section ex_3_1_6.

Import Π_type.

Definition ex_3_1_6 {A B} : (Π (a : A), isSet (B a)) → isSet (Π (a : A), B a).
Proof.
intros r f g p q.
unfold isSet in r.
pose proof funext_prop_uniq_princ f g p as Hp.
pose proof funext_prop_uniq_princ f g q as Hq.
assert (∀ x : A, happly p x = happly q x) as Hx by (intros; apply r).
apply funext in Hx.
rewrite Hp, Hq, Hx.
reflexivity.
Defined.

End ex_3_1_6.

(* "Definition 3.1.7. A type A is a 1-type if for all x, y : A and p,
    q : x = y and r, s : p = q, we have r = s. *)

Definition is1Type A := ∀ (x y : A) (p q : x = y) (r s : p = q), r = s.

(* "Lemma 3.1.8. If A is a set (that is, isSet(A) is inhabited), then
    A is a 1-type." *)

Section lemma_3_1_8.

Import Σ_type2.

Check @compose.

(* required, but general purpose lemma, tac and exp versions *)
Definition compose_cancel_l_tac {A} {x y z : A} (p : x = y) (q r : y = z) :
  p • q = p • r
  → q = r.
Proof.
intros H.
eapply (dotl p⁻¹) in H.
eapply compose.
 eapply compose; [ | apply H ].
 eapply compose; [ | eapply invert, compose_assoc ].
 eapply compose; [ apply lu | apply dotr ].
 apply invert, compose_invert_l.

 eapply compose; [ eapply compose_assoc | ].
 eapply compose; [ | eapply invert, lu ].
 apply dotr, compose_invert_l.
Defined.

Definition compose_cancel_l {A} {x y z : A} (p : x = y) (q r : y = z) :
  p • q = p • r
  → q = r
:=
  λ s,
  lu q • ((compose_invert_l p)⁻¹ •r q) • (compose_assoc p⁻¹ p q)⁻¹ •
  (p⁻¹ •l s) •
  compose_assoc p⁻¹ p r • (compose_invert_l p •r r) • (lu r)⁻¹.

(* magic lemma to prove isSet → is1Type and also used later for
   ispType → isSpType *)
Definition compose_insert_tac {A x} (f : Π (y : A), x = y) {y z} (p : y = z) :
  f y • p = f z.
Proof.
pose proof apd f p as h.
eapply compose; [ | eassumption ].
eapply invert; destruct p; simpl; unfold id; apply ru.
Defined.

Definition compose_insert {A x} (f : Π (y : A), x = y) {y z} (p : y = z) :
  f y • p = f z
:=
  match p return f y • p = transport (eq x) p (f y) with
  | eq_refl _ => (ru (f y))⁻¹
  end
  • apd f p.

Print ru.

(* done but not obvious at all; I had to look at the way they did it,
   and I am sure I don't understand the point *)
Definition hott_3_1_8_tac {A} : isSet A → is1Type A.
Proof.
intros f x y p q r s.
apply (compose_cancel_l (f x y p p)).
eapply compose; [ eapply (compose_insert (f x y p)) | ].
apply invert, compose_insert.
Defined.

Definition hott_3_1_8 {A} : isSet A → is1Type A :=
  λ f x y p q r s,
  compose_cancel_l (f x y p p) r s
    (compose_insert (f x y p) r • (compose_insert (f x y p) s)⁻¹).

End lemma_3_1_8.

(* generalization *)

Definition isProp A := Π (x : A), Π (y : A), x = y.

Fixpoint ispType A p :=
  match p with
  | 0 => isProp A
  | S p' => ∀ x y : A, ispType (x = y) p'
  end.

(* A n-type has property 'ispType A (S n)', because the n of n-types
   start at -1 *)

Definition ispType_isSpType_tac {A} n : ispType A n → ispType A (S n).
Proof.
intros f x y.
revert A f x y.
induction n; intros.
 intros p q.
 apply (compose_cancel_l (f x x)).
 eapply compose; [ eapply (compose_insert (f x)) | ].
 apply invert, compose_insert.

 intros p q; apply IHn, f.
Defined.

Definition ispType_isSpType {A} n : ispType A n → ispType A (S n) :=
  nat_ind
    (λ n, ∀ A, ispType A n → ispType A (S n))
    (λ A f x y p q,
     compose_cancel_l (f x x) p q
       (compose_insert (f x) p • (compose_insert (f x) q)⁻¹))
    (λ n IHn A f x y, IHn (x = y) (f x y))
    n A.

(* "Example 3.1.9. The universe U is not a set." *)

Definition ex_3_1_9 : ¬isSet U.
Proof.
intros r.
unfold isSet in r.
pose proof r bool bool (ua bool_eq_bool_id) (ua bool_eq_bool_negb) as s.
apply (ap idtoeqv) in s.
eapply compose in s; [ | eapply invert, idtoeqv_ua ].
eapply invert, compose in s; [ | eapply invert, idtoeqv_ua ].
unfold bool_eq_bool_id, bool_eq_bool_negb in s.
simpl in s.
injection s; intros H _ _.
assert (negb true = true) as H1; [ rewrite H; reflexivity | ].
revert H1; apply Σ_type2.hott_2_12_6.
Defined.

(* 3.2 Propositions as types? *)

Section hott_3_2_2.
Import Σ_type.
Import Π_type.

(* "Theorem 3.2.2. It is not the case that for all A : U we have ¬(¬A)→A." *)

Definition hott_3_2_2_tac : notT (∀ A, notT (notT A) → A).
Proof.
intros f.
set (e := bool_eq_bool_negb).
set (u (g : notT bool) := g true).
set (nn A := notT (notT A)).
assert (p : pr₁ e (f _ u) = f _ u).
 eapply compose; [ eapply invert, ua_pcr | ].
 eapply compose; [ | apply (happly (apd f (ua e))) ].
 eapply invert, compose.
  apply (happly (@hott_2_9_4 _ nn id _ _ (ua e) (f bool)) u).

  apply ap, ap, funext; intros g; destruct (g true).

 eapply no_fixpoint_negb, p.
Defined.

Definition hott_3_2_2 : notT (∀ A : U, notT (notT A) → A)
:=
  λ f,
  let e := bool_eq_bool_negb in
  let u (x : notT bool) := x true in
  let nn A := notT (notT A) in
  no_fixpoint_negb (f bool u)
    ((ua_pcr e (f bool u))⁻¹
      • (happly (@hott_2_9_4 _ nn id _ _ (ua e) (f bool)) u
         • ap ((ua e)⁎ ◦ f bool)
             (funext (λ (x : notT bool), match x true with end)))⁻¹
      • happly (apd f (ua e)) u).

End hott_3_2_2.

(* "Corollary 3.2.7. It is not the case that for all A : U we have A+(¬A)." *)

Definition hott_3_2_7_tac : notT (∀ A, A + notT A).
Proof.
intros g.
apply hott_3_2_2; intros A u.
destruct (g A) as [a| w]; [ apply a | destruct (u w) ].
Defined.

Definition hott_3_2_7 : notT (∀ A, A + notT A)
:=
  λ g,
  hott_3_2_2
    (λ A u,
     match g A with
     | inl a => a
     | inr w => match u w with end
     end).

(* "3.3 Mere propositions" *)

(* "Definition 3.3.1. A type P is a mere proposition if for all x, y :
    P we have x = y." *)

Print isProp.

(* "Lemma 3.3.2. If P is a mere proposition and x0 : P, then P ≃ 1." *)

Definition hott_3_3_2_tac P : isProp P → ∀ x₀ : P, P ≃ unit.
Proof.
intros HP x₀.
apply (existT _ (λ _, tt)), qinv_isequiv.
apply (existT _ (λ _, x₀)).
split; intros x; [ destruct x; reflexivity | apply HP ].
Defined.

Definition hott_3_3_2 P : isProp P → ∀ x₀ : P, P ≃ unit
:=
  λ (HP : isProp P) (x₀ : P),
  existT isequiv (λ _, tt)
    (qinv_isequiv (λ _, tt)
       (existT _ (λ _, x₀)
          (λ x, match x with tt => eq_refl (id tt) end,  λ x, HP _ x))).

(* "Lemma 3.3.3. If P and Q are mere propositions such that P → Q and
    Q → P, then P ≃ Q." *)

Definition hott_3_3_3_tac P Q :
  isProp P → isProp Q → (P → Q) → (Q → P) → P ≃ Q.
Proof.
intros p q f g.
apply (existT _ f), qinv_isequiv, (existT _ g).
split; intros x; [ apply q | apply p ].
Defined.

Definition hott_3_3_3 P Q : isProp P → isProp Q → (P → Q) → (Q → P) → P ≃ Q
:=
  λ (p : isProp P) (q : isProp Q) (f : P → Q) (g : Q → P),
  existT isequiv f (qinv_isequiv f (existT _ g (λ y, q _ y, λ x, p _ x))).

Definition isContractible P := (isProp P * (P ≃ unit))%type.

(* "Lemma 3.3.4. Every mere proposition is a set." *)

Definition hott_3_3_4 A : isProp A → isSet A := ispType_isSpType 0.

(* "Lemma 3.3.5. For any type A, the types isProp(A) and isSet(A)
    are mere propositions." *)

Section Lemma_3_3_5.

Import Π_type.

Definition hott_3_3_5_i_tac A : isProp (isProp A).
Proof.
intros f g.
eapply funext; intros x.
eapply funext; intros y.
apply (hott_3_3_4 _ f).
Defined.

Definition hott_3_3_5_i A : isProp (isProp A) :=
  λ f g, funext (λ x, funext (λ y, hott_3_3_4 A f x y (f x y) (g x y))).

Definition hott_3_3_5_ii_tac A : isProp (isSet A).
Proof.
intros f g.
eapply funext; intros x.
eapply funext; intros y.
eapply funext; intros p.
eapply funext; intros q.
apply (ispType_isSpType 1), f.
Defined.

Definition hott_3_3_5_ii A : isProp (isSet A) :=
  λ f g,
  funext
    (λ x,
     funext
       (λ y,
        funext
          (λ p,
           funext
             (λ q, ispType_isSpType 1 f x y p q (f x y p q) (g x y p q))))).

Definition isequiv_mere_prop {A B} (f : A → B) :
  @equiv_prop A B isequiv → isProp (isequiv f).
Proof.
intros p e₁ e₂.
pose proof p f as pf.
destruct pf as ((qi, iq), eqv).
apply eqv.
Defined.

End Lemma_3_3_5.

(* "3.4 Classical vs. intuitionistic logic" *)

(* "law of excluded middle in homotopy type theory:
       LEM : Π (A:U), (isProp(A) → (A + ¬A))      (3.4.1)" *)

Definition LEM := Π (A : U), (isProp A → (A + notT A)).

(* "law of double negation
       Π (A:U), (isProp A → (¬¬A → A))            (3.4.2)" *)

Definition LDN := Π (A : U), (isProp A → (notT (notT A) → A)).

(* LEM and LDN are logically equivalent (ex 3.18) *)

Definition isProp_notT_tac A : isProp (A → ⊥).
Proof.
intros x y.
apply Π_type.funext; intros z; destruct (x z).
Defined.

Definition isProp_notT A : isProp (A → ⊥) :=
  λ x y : A → ⊥, Π_type.funext (λ (z : A), match x z with end).

Definition LEM_LDN : (LEM → LDN) * (LDN → LEM).
Proof.
split.
 intros HLEM A HP HNA.
 destruct (HLEM A HP) as [x| x]; [ apply x | destruct (HNA x) ].

 intros HLDN A HPA.
 apply HLDN.
 intros x y.
 destruct x as [x| x].
  destruct y as [y| y]; [ apply Σ_type2.inl_equal, HPA | destruct (y x) ].

  destruct y as [y| y]; [ destruct (x y) | ].
  apply Σ_type2.inr_equal.
  apply HLDN; [ apply (ispType_isSpType 0), isProp_notT | ].
  intros HNE; apply HNE, isProp_notT.

  intros HNA; apply HNA.
  right; intros HA; apply HNA.
  left; apply HA.
Defined.

(* "For emphasis, the proper version (3.4.1) may be denoted LEM-₁" *)

Definition LEM_p p := Π (A : U), (ispType A p → (A + notT A)).
Definition LEM_inf := Π (A : U), (A + notT A).

(* "Definition 3.4.3.
      (i) A type A is called decidable if A + ¬A.
     (ii) Similarly, a type family B : A → U is decidable if
              Π(a:A)(B(a) + ¬B(a)).
    (iii) In particular, A has decidable equality if
              Π(a,b:A)((a = b) + ¬(a = b))." *)

Definition isDecidable A := (A + notT A)%type.
Definition isDecidableFamily A B := Π (a : A), (B a + notT (B a)).
Definition hasDecidableEq A := Π (a : A), Π (b : A), ((a = b) + notT (a = b)).

(* "3.5 Subsets and propositional resizing" *)

Section hott_3_5.

Import Σ_type.

(* "Lemma 3.5.1. Suppose P : A → U is a type family such that P(x) is
    a mere proposition for all x : A. If u, v : Σ(x:A) P(x) are such
    that pr₁(u) = pr₁(v), then u = v." *)

Definition hott_3_5_1_my_proof_tac {A} (P : A → U) :
  (Π (x : A), isProp (P x))
  → ∀ u v : (Σ (x : A), P x),
  pr₁ u = pr₁ v
  → u = v.
Proof.
intros HP u v p.
destruct u as (ua, up); simpl in p.
destruct v as (va, vp); simpl in p.
eapply compose; [ eapply (pair_eq p), HP | reflexivity ].
Defined.

Definition hott_3_5_1_my_proof {A} (P : A → U) :
  (Π (x : A), isProp (P x))
  → ∀ u v : (Σ (x : A), P x),
  pr₁ u = pr₁ v
  → u = v
:=
  λ HP u v,
  match u with existT _ ua up =>
    match v with existT _ va vp =>
    λ p, pair⁼ p (HP va (transport P p up) vp)
    end
  end.

(* their proof *)

Definition hott_3_5_1_tac {A} (P : A → U) :
  (Π (x : A), isProp (P x))
  → ∀ u v : (Σ (x : A), P x),
  pr₁ u = pr₁ v
  → u = v.
Proof.
intros HP u v p.
pose proof @hott_2_7_2 A P u v as H.
destruct H as (f, ((g, Hg), (h, Hh))).
apply g, (existT _ p), HP.
Defined.

Definition hott_3_5_1 {A} (P : A → U) :
  (Π (x : A), isProp (P x))
  → ∀ u v : (Σ (x : A), P x),
  pr₁ u = pr₁ v
  → u = v
:=
  λ HP u v p,
  match hott_2_7_2 P u v with
  | existT _ _ (existT _ g _, _) =>
      g (existT _ p (HP (pr₁ v) (p⁎ (pr₂ u)) (pr₂ v)))
  end.

Definition SetU := {A : U & isSet A}.
Definition PropU := {A : U & isProp A}.

Definition SetU_equiv_eq A B s t :
  (existT isSet A s = existT isSet B t) ≃ (A = B).
Proof.
apply
  (existT _
     (λ p : existT isSet A s = existT isSet B t,
      match p in (_ = s0) return (let (b, _) := s0 in A = b) with
      | eq_refl _ => eq_refl A
      end)).
apply qinv_isequiv.
apply
  (existT _
     (λ p,
      hott_3_5_1 isSet hott_3_3_5_ii (existT isSet A s)
        (existT isSet B t) p)).
unfold "◦", "~~", id; simpl.
split.
 intros p.
 unfold hott_3_5_1; simpl.
 destruct (hott_2_7_2 isSet (existT isSet A s) (existT isSet B t)) as (f, H).
 destruct H as ((g, Hg), (h, Hh)).
 unfold hott_3_3_5_ii; simpl.
 destruct p; simpl.
 (* equivalent, equivalent... are they really equivalent?
    or just logically equivalent? *)
Abort.

Print SetU.

End hott_3_5.

(* "Recall that for any two universes Ui and Ui+1, if A : Ui then also
    A : Ui+1. Thus, for any (A, s) : SetUi we also have (A, s) : SetUi+1,
    and similarly for PropUi , giving natural maps
       SetUi → SetUi+1,              (3.5.3)
       PropUi → PropUi+1.            (3.5.4)" *)

(* ok, but I don't know how to program the hierarchy of universes in Coq;
   and the following axiom cannot be written either *)

(* "Axiom 3.5.5 (Propositional resizing). The map PropUi ! PropUi+1 is
    an equivalence." *)

(* "3.6 The logic of mere propositions" *)

Section hott_3_6.

(* "Example 3.6.1. If A and B are mere propositions, so is A x B." *)

Definition ex_3_6_1 {A B} : isProp A → isProp B → isProp (A * B).
Proof.
intros HA HB x y.
destruct x as (xa, xb).
destruct y as (ya, yb).
apply cartesian.pair_eq; simpl.
split; [ apply HA | apply HB ].
Defined.

(* "Example 3.6.2. If A is any type and B : A → U is such that for all
    x : A, the type B(x) is a mere proposition, then Π(x:A) B(x) is a
    mere proposition." *)

Import Π_type.

Definition ex_3_6_2 {A B} :
  (Π (x : A), isProp (B x)) → isProp (Π (x : A), B x).
Proof.
intros HP f g.
apply funext; intros x; apply HP.
Defined.

Definition isPropImp {A B} : isProp B → isProp (A → B).
Proof.
intros; apply ex_3_6_2; intros x; apply H.
Defined.

Definition isPropNot {A} : isProp A → isProp (notT A).
Proof.
intros. apply isPropImp; intros x y; destruct x.
Defined.

End hott_3_6.

(* "3.7 Propositional truncation" *)

(* I implement the element of a propositional truncation using a
   function of type unit → A. This way, two such elements can be
   forced to be equal (axiom PT_eq below), but the discriminate
   tactic, not appliable to functions, cannot be used with the
   risk of creating a contradiction (H: |1| = |2| and using the
   tactic 'discriminate H'). Not 100% sure since nothing prevent
   to use 'ap PT_elim' before (see theorem 'contradiction' below).
 *)

Inductive prop_trunc A :=
| PT : ∀ f : unit → A, prop_trunc A.
Arguments PT [A] f.

Notation "∥ A ∥" := (prop_trunc A) (A at level 0, format "∥ A ∥").
Notation "| x |" := (PT (λ _, x)) (x at level 0, format "| x |") : type_scope.

Axiom PT_eq : ∀ A, isProp ∥A∥.
Arguments PT_eq [A] x y.

Definition PT_elim {A} (x : ∥A∥) : A := match x with PT f => f tt end.

(* do not use "ap PT_elim"! here is the reason *)
Definition contradiction : False.
Proof.
pose proof PT_eq |1| |2| as H.
apply (ap PT_elim) in H.
discriminate H.
(* no  more subgoals, but aborting it even so *)
Abort.

(* "If B is a mere proposition and we have f : A → B, then there is an
    induced g : ∥A∥ → B such that g(|a|) ≡ f(a) for all a : A." *)

(* the hypothesis for B to be a mere proposition seems not useful... *)
Definition prop_trunc_rec_princ {A B} : (*isProp B →*)
  ∀ f : A → B, ∃ g : ∥A∥ → B, ∀ a : A, g |a| = f a.
Proof.
intros (*H*) f.
exists (λ z, f (PT_elim z)).
reflexivity.
Defined.

Definition prop_trunc_rec_fun {A B} (f : A → B) := f ◦ PT_elim.

Definition prop_trunc_rec_princ2 {A B} (f : A → B) a :
  prop_trunc_rec_fun f |a| = f a.
Proof.
reflexivity.
Defined.

Print prop_trunc_rec_princ2.

(* doing the exercise 3.14 in advance, just to see if my definition of
   propositional truncation works *)

Definition ex_3_14 : LEM → ∀ A, isProp A → (notT (notT A) ≃ ∥A∥).
Proof.
intros HLEM A HPA.
apply (existT _ (λ p, | (pr₁ LEM_LDN HLEM A HPA p) |)), qinv_isequiv.
apply (existT _ (λ p q, q (PT_elim p))).
unfold "◦", "~~", id; simpl.
split; [ intros x; destruct (HLEM A HPA); apply PT_eq | ].
intros f; apply Π_type.funext; intros x; destruct (f x).
Defined.

(* "3.8 The axiom of choice" *)

Axiom AC : ∀ X (A : X → U) (P : Π (x : X), (A x → U)),
  isSet X
  → (Π (x : X), isSet (A x))
  → (Π (x : X), Π (a : A x), isProp (P x a))
  → (Π (x : X), ∥ (Σ (a : A x), P x a) ∥)
  → ∥ (Σ (g : Π (x : X), A x), Π (x : X), P x (g x)) ∥.

_5htp.
