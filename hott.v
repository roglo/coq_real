Require Import Utf8 Arith.
Require List.
Import List.ListNotations.
Open Scope list_scope.

Definition isequiv {A B : Type} (f : A → B) :=
  {g : B → A & (∀ a, g (f a) = a) & (∀ b, f (g b) = b)}.

Definition equivalence (A B : Type) := { f : A → B & isequiv f}.
Notation "A ≃ B" := (equivalence A B) (at level 70).

Axiom univalence : ∀ A B, (A ≃ B) ≃ (A = B).

Notation "a ^ b" := (Nat.pow a b).

Fixpoint nat_of_list_nat l :=
  match l with
  | [] => 0
  | a :: l => 2 ^ a * (2 * nat_of_list_nat l + 1)
  end.

Fixpoint list_nat_of_nat_aux iter n :=
  match iter with
  | 0 => []
  | S i =>
      match n with
      | 0 => []
      | _ =>
          match (n mod 2, list_nat_of_nat_aux i (n / 2)) with
          | (0, []) => [0]
          | (0, a :: l) => S a :: l
          | (_, l) => 0 :: l
          end
      end
  end.

Definition list_nat_of_nat n := list_nat_of_nat_aux n n.

Theorem glop : (nat : Type) = (list nat : Type).
Proof.
specialize (univalence nat (list nat)) as (f, Hf).
destruct Hf as (g, Hgf, Hfg).
apply f.
exists list_nat_of_nat.
exists nat_of_list_nat.
-intros a.
 unfold list_nat_of_nat.

Theorem pouet : ∀ n i,
  n ≤ i
  → nat_of_list_nat (list_nat_of_nat_aux i n) = n.
Proof.
intros * Hni.
revert n Hni.
induction i; intros; [now apply Nat.le_0_r in Hni | ].
destruct n; [ easy | ].

...
