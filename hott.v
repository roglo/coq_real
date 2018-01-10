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

Theorem pouet : ∀ n i,
  n ≤ i
  → nat_of_list_nat (list_nat_of_nat_aux i n) = n.
Proof.
intros * Hni.
revert n Hni.
induction i; intros; [now apply Nat.le_0_r in Hni | ].
destruct n; [ easy | ].
Opaque Nat.modulo Nat.div.
simpl.
apply Nat.succ_le_mono in Hni.
...

specialize (IHi _ Hni) as IH.
remember (S n mod 2) as m eqn:Hm.
symmetry in Hm.
destruct m.
-remember (list_nat_of_nat_aux i (S n / 2)) as l eqn:Hl.
 symmetry in Hl.
 destruct l as [| a].
 +destruct n; [ easy | exfalso ].
  destruct i; [ easy | ].
  simpl in IH, Hl.
  apply Nat.mod_divides in Hm; [ | easy ].
  destruct Hm as (c, Hc); rewrite Nat.mul_comm in Hc.
  rewrite Hc in Hl.
  rewrite Nat.div_mul in Hl; [ | easy ].
  destruct c; [ easy | ].
  destruct (S c mod 2); [ | easy ].
  now destruct (list_nat_of_nat_aux i (S c / 2)).
 +simpl.
  do 2 rewrite Nat.add_0_r.
  destruct i.
  *apply Nat.le_0_r in Hni; subst n.
Transparent Nat.modulo.
   easy.
Opaque Nat.modulo.
  *simpl in Hl.
   apply Nat.mod_divides in Hm; [ | easy ].
   destruct Hm as (c, Hc); rewrite Nat.mul_comm in Hc.
   rewrite Hc in Hl.
   rewrite Nat.div_mul in Hl; [ | easy ].
   destruct c; [ easy | ].
   remember (S c mod 2) as x.
   symmetry in Heqx.
   destruct x.
   remember (list_nat_of_nat_aux i (S c / 2)) as y.
   symmetry in Heqy.
   destruct y.
  --injection Hl; clear Hl; intros; subst a l.
    simpl.
    destruct n; [ easy | ].
...

Theorem glop : (nat : Type) = (list nat : Type).
Proof.
specialize (univalence nat (list nat)) as (f, Hf).
destruct Hf as (g, Hgf, Hfg).
apply f.
exists list_nat_of_nat.
exists nat_of_list_nat.
-intros a.
 unfold list_nat_of_nat.
...
