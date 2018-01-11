(* proof that nat=list nat using univalence axiom *)

Require Import Utf8 Arith Psatz.
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
      if Nat.even n then
        match Nat.div2 n with
        | 0 => []
        | S m =>
            match list_nat_of_nat_aux i (S m) with
            | [] => [0]
            | a :: l => S a :: l
            end
        end
      else 0 :: list_nat_of_nat_aux i (Nat.div2 n)
  end.

Definition list_nat_of_nat n := list_nat_of_nat_aux n n.

Compute (List.fold_right
  (λ n l, (n, list_nat_of_nat n) :: l))
  [] (List.seq 0 31).

Compute (List.fold_right
  (λ n l, (n, nat_of_list_nat (list_nat_of_nat n)) :: l))
  [] (List.seq 0 31).

...

Fixpoint list_nat_of_nat_aux iter n :=
  match iter with
  | 0 => []
  | S i =>
      match n with
      | 0 => []
      | _ =>
          if Nat.even n then
            match list_nat_of_nat_aux i (Nat.div2 n) with
            | [] => [0]
            | a :: l => S a :: l
            end
          else 0 :: list_nat_of_nat_aux i (Nat.div2 n)
      end
  end.

Definition list_nat_of_nat n := list_nat_of_nat_aux n n.

Compute (List.fold_right
  (λ n l, (n, list_nat_of_nat n) :: l))
  [] (List.seq 0 31).

Theorem list_nat_of_nat_aux_enough_iter : ∀ n i j,
  n ≤ i → n ≤ j →
  list_nat_of_nat_aux i n = list_nat_of_nat_aux j n.
Proof.
intros * Hi Hj.
revert n j Hi Hj.
induction i; intros.
-apply Nat.le_0_r in Hi; subst n; simpl.
 now destruct j.
-destruct n; [ now destruct j | ].
 destruct j; [ easy | ].
 remember (S n) as ss; simpl; subst ss.
 apply Nat.succ_le_mono in Hi.
 apply Nat.succ_le_mono in Hj.
 assert (Hsi : Nat.div2 (S n) ≤ i). {
   eapply Nat.le_trans; [ | apply Hi ].
   apply Nat.le_div2.
 }
 assert (Hsj : Nat.div2 (S n) ≤ j). {
   eapply Nat.le_trans; [ | apply Hj ].
   apply Nat.le_div2.
 }
 now rewrite (IHi _ _ Hsi Hsj).
Qed.

Theorem Odd_list_nat_of_nat_aux : ∀ n i,
  Nat.Odd n
  → list_nat_of_nat_aux (S i) n =
      0 :: list_nat_of_nat_aux i (Nat.div2 n).
Proof.
intros * Hn.
destruct n; [ now apply Nat.odd_spec in Hn | ].
remember (S n) as x; simpl; subst x.
remember (Nat.even (S n)) as b eqn:Hb.
symmetry in Hb.
destruct b; [ | easy ].
apply Nat.even_spec in Hb.
now apply Nat.Even_Odd_False in Hb.
Qed.

Theorem Odd_list_nat_of_nat : ∀ n,
  Nat.Odd n
  → list_nat_of_nat n = 0 :: list_nat_of_nat (Nat.div2 n).
Proof.
intros * Hn.
unfold list_nat_of_nat.
rewrite list_nat_of_nat_aux_enough_iter with (j := S n); [ | easy | lia ].
rewrite Odd_list_nat_of_nat_aux; [ f_equal | easy ].
apply list_nat_of_nat_aux_enough_iter; [ | easy ].
apply Nat.div2_decr; lia.
Qed.

Theorem tigidi : ∀ i l,
  nat_of_list_nat l ≤ i
  → list_nat_of_nat_aux i (nat_of_list_nat l) = l.
Proof.
intros * Hli.
revert l Hli.
induction i; intros.
-apply Nat.le_0_r in Hli; rewrite Hli; simpl.
 destruct l as [| a]; [ easy | exfalso ].
 simpl in Hli.
 apply Nat.eq_mul_0 in Hli.
 specialize (Nat.pow_nonzero 2 a (Nat.neq_succ_0 1)) as H.
 destruct Hli; [ easy | lia ].
-simpl.
 remember (nat_of_list_nat l) as m eqn:Hm.
 symmetry in Hm.
 destruct m.
 +clear - Hm.
  destruct l as [| a]; [ easy | exfalso ].
  simpl in Hm.
  apply Nat.eq_mul_0 in Hm.
  specialize (Nat.pow_nonzero 2 a (Nat.neq_succ_0 1)) as H.
  destruct Hm; [ easy | lia ].
 +apply Nat.succ_le_mono in Hli.

...

Theorem tagada : ∀ l,
  list_nat_of_nat (nat_of_list_nat l) = l.
Proof.
intros.
unfold list_nat_of_nat.
...

induction l as [| a]; [ easy | simpl ].
rewrite Nat.add_0_r.
rewrite Nat.add_1_r; simpl.
destruct a.
-rewrite Nat.pow_0_r, Nat.mul_1_l.
 unfold list_nat_of

simpl.
...

Theorem pouet : ∀ n i,
  n ≤ i
  → nat_of_list_nat (list_nat_of_nat_aux i n) = n.
Proof.
intros * Hni.
revert n Hni.
induction i; intros; [now apply Nat.le_0_r in Hni | ].
simpl.
destruct n; [ easy | ].
remember (Nat.even (S n)) as b eqn:Hb.
symmetry in Hb.
destruct b.
Search (Nat.div2 (S _)).
apply Nat.succ_le_mono in Hni.
Focus 2.
specialize (Nat.le_div2 n) as H.
assert (H1 : Nat.div2 (S n) ≤ i) by lia.
specialize (IHi _ H1) as H2.
remember (Nat.div2 (S n)) as x; simpl; subst x.
rewrite H2.
do 2 rewrite Nat.add_0_r.
rewrite Nat.add_1_r.
f_equal.
Search (2 * Nat.div2 _).
simpl.
destruct n; [ easy | ].
simpl.
f_equal.
...

apply Nat.even_spec in Hb.
assert (S n / 2 ≤ i).
Search (Nat.Even _ ∨ _).
Search Nat.div2.
...

Nat.even_add_mul_even: ∀ n m p : nat, Nat.Even m → Nat.even (n + m * p) = Nat.even n
Focus 2.
specialize (IHi _ H) as IH.
simpl.
rewrite IH.
do 2 rewrite Nat.add_0_r.
rewrite Nat.add_1_r.
f_equal.
replace (S n / 2 + S n / 2) with (S n / 2 * 2).
...



remember (Nat.odd n) as b eqn:Hb.
symmetry in Hb.
destruct b.
-destruct n; [ easy | ].
 rewrite Nat.odd_succ in Hb.
Search (S _ mod _).

-apply Nat.odd_spec in Hb.
 destruct n; [ easy | ].
 apply Nat.odd_spec in Hb.
Search (Nat.odd (S _)).
simpl in Hb.

Search (Nat.Odd (S _)).
 apply Nat.Odd_succ in Hb.

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
