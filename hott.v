(* Proof that nat=list nat, using univalence axiom *)

Require Import Utf8 Arith Psatz.
Require List.
Import List.ListNotations.
Open Scope list_scope.

Fixpoint pow_2_of_nat_aux iter n :=
  match iter with
  | 0 => 0
  | S i =>
      match n with
      | 0 => 0
      | S m => if Nat.even n then 1 + pow_2_of_nat_aux i (Nat.div2 n) else 0
      end
  end.

Definition pow_2_of_nat n := pow_2_of_nat_aux n n.

Fixpoint odd_part_of_nat_aux iter n :=
  match iter with
  | 0 => 0
  | S i =>
      match n with
      | 0 => 0
      | S m =>
          if Nat.even n then odd_part_of_nat_aux i (Nat.div2 n)
          else Nat.div2 n
      end
  end.

Definition odd_part_of_nat n := odd_part_of_nat_aux n n.

Fixpoint nat_of_list_nat l :=
  match l with
  | [] => 0
  | a :: l => 2 ^ a * (2 * nat_of_list_nat l + 1)
  end.

Fixpoint list_nat_of_nat_aux iter n :=
  match iter with
  | 0 => []
  | S i =>
      if zerop n then []
      else pow_2_of_nat n :: list_nat_of_nat_aux i (odd_part_of_nat n)
  end.

Definition list_nat_of_nat n := list_nat_of_nat_aux n n.

(*
Compute (List.fold_right
  (λ n l, (n, list_nat_of_nat n) :: l))
  [] (List.seq 0 31).

Compute (List.fold_right
  (λ n l, (n, nat_of_list_nat (list_nat_of_nat n)) :: l))
  [] (List.seq 0 31).
*)

Theorem odd_part_of_nat_aux_lt : ∀ n i,
  0 < n
  → n ≤ i
  → odd_part_of_nat_aux i n < n.
Proof.
intros * Hn Hni.
destruct n; [ easy | clear Hn ].
revert n Hni.
induction i; intros.
-now apply Nat.le_0_r in Hni; subst; simpl.
-destruct n; [ simpl; lia | ].
 apply Nat.succ_le_mono in Hni.
 remember (S n) as sn; simpl; subst sn.
 remember (Nat.even n) as b eqn:Hb.
 symmetry in Hb.
 destruct b.
 +eapply Nat.lt_le_trans; [ apply IHi | ].
  *eapply Nat.le_trans; [ | apply Hni ].
   apply -> Nat.succ_le_mono.
   apply Nat.div2_decr; lia.
  *apply -> Nat.succ_le_mono.
   apply Nat.div2_decr; lia.
 +apply -> Nat.succ_lt_mono.
  destruct n; [ easy | ].
  apply Nat.lt_le_trans with (m := S n); [ | lia ].
  apply Nat.lt_div2; lia.
Qed.

Theorem odd_part_of_nat_le : ∀ n,
  odd_part_of_nat (S n) ≤ n.
Proof.
intros.
unfold odd_part_of_nat.
specialize (odd_part_of_nat_aux_lt _ (S n) (Nat.lt_0_succ n) (le_refl _)).
lia.
Qed.

Theorem eq_nat_of_list_nat_0 : ∀ l,
  nat_of_list_nat l = 0 ↔ l = [].
Proof.
intros.
split; intros H.
-destruct l as [| a]; [ easy | ].
 simpl in H.
 assert (2 ^ a ≠ 0) by now apply Nat.pow_nonzero.
 destruct (2 ^ a); [ easy | ].
 simpl in H; lia.
-now destruct l.
Qed.

Theorem nat_of_list_nat_cons : ∀ a l,
  nat_of_list_nat (a :: l) = 2 ^ a * (2 * nat_of_list_nat l + 1).
Proof. easy. Qed.

Theorem pow2_mul_odd_aux : ∀ n a b i j,
  n ≠ 0
  → n ≤ i
  → n ≤ j
  → a = pow_2_of_nat_aux i n
  → b = odd_part_of_nat_aux j n
  → n = 2 ^ a * (2 * b + 1).
Proof.
intros * Hn Hni Hnj Ha Hb.
revert i j a b Hni Hnj Ha Hb.
induction n as (n, IHn) using lt_wf_rec; intros.
destruct n; [ easy | clear Hn ].
destruct i; [ easy | ].
destruct j; [ easy | ].
remember (S n) as s; simpl in Ha, Hb; subst s.
remember (Nat.even (S n)) as e eqn:He.
symmetry in He.
destruct e.
-destruct n; [ easy | ].
 destruct a; [ easy | ].
 apply Nat.succ_inj in Ha.
 specialize (Nat.lt_div2 (S (S n)) (Nat.lt_0_succ (S n))) as Hldn.
 assert (Hzdn : Nat.div2 (S (S n)) ≠ 0) by easy.
 assert (Hdi : Nat.div2 (S (S n)) ≤ i). {
   destruct i; [ lia | simpl ].
   do 2 apply Nat.succ_le_mono in Hni.
   apply -> Nat.succ_le_mono.
   destruct n; [ easy | ].
   eapply Nat.le_trans; [ apply Nat.le_div2 | lia ].
 }
 assert (Hdj : Nat.div2 (S (S n)) ≤ j). {
   destruct j; [ lia | simpl ].
   do 2 apply Nat.succ_le_mono in Hnj.
   apply -> Nat.succ_le_mono.
   destruct n; [ easy | ].
   eapply Nat.le_trans; [ apply Nat.le_div2 | lia ].
 }
 specialize (IHn (Nat.div2 (S (S n))) Hldn Hzdn i j a b Hdi Hdj Ha Hb).
 rewrite Nat.pow_succ_r; [ | lia ].
 rewrite <- Nat.mul_assoc.
 rewrite <- IHn.
 specialize (Nat.div2_odd (S (S n))) as H.
 replace (Nat.odd (S (S n))) with false in H.
 +unfold Nat.b2n in H; lia.
+rewrite <- Nat.negb_odd in He.
 now apply Bool.negb_true_iff in He.
-specialize (Nat.div2_odd (S n)) as H.
 rewrite <- Hb in H.
 replace (Nat.odd (S n)) with true in H.
 +now subst a; rewrite Nat.pow_0_r, Nat.mul_1_l.
 +rewrite <- Nat.negb_odd in He.
  now apply Bool.negb_false_iff in He.
Qed.

Theorem pow2_mul_odd : ∀ n a b,
  n ≠ 0
  → a = pow_2_of_nat n
  → b = odd_part_of_nat n
  → n = 2 ^ a * (2 * b + 1).
Proof.
intros * Hn Ha Hb.
now eapply pow2_mul_odd_aux.
Qed.

Theorem pow_2_of_nat_aux_mul_odd : ∀ a b n i,
  n = 2 ^ a * (2 * b + 1)
  → n ≤ i
  → pow_2_of_nat_aux i n = a.
Proof.
intros * Hn Hni.
symmetry in Hn.
revert a b n Hn Hni.
induction i; intros.
-apply Nat.le_0_r in Hni.
 move Hni at top; subst n.
 apply Nat.eq_mul_0 in Hn.
 destruct Hn as [Hn| Hn]; [ | lia ].
 apply Nat.pow_nonzero in Hn; [ easy | lia ].
-simpl.
 destruct n.
 +apply Nat.eq_mul_0 in Hn.
  destruct Hn as [Hn| Hn]; [ | lia ].
  now apply Nat.pow_nonzero in Hn.
 +remember (Nat.even (S n)) as e eqn:He.
  symmetry in He.
  destruct e.
  *destruct a.
  --rewrite Nat.pow_0_r, Nat.mul_1_l in Hn.
    rewrite <- Hn in He.
    rewrite Nat.add_comm in He.
    now rewrite Nat.even_add_mul_2 in He.
  --f_equal.
    rewrite Nat.pow_succ_r in Hn; [ | lia ].
    rewrite <- Nat.mul_assoc in Hn.
    rewrite <- Hn.
    rewrite Nat.div2_double.
    eapply IHi; [ easy | lia ].
  *destruct a; [ easy | ].
   rewrite Nat.pow_succ_r in Hn; [ | lia ].
   rewrite <- Nat.mul_assoc in Hn.
   rewrite <- Hn in He.
   now rewrite Nat.even_mul in He.
Qed.

Theorem pow_2_of_nat_mul_odd : ∀ a b,
  pow_2_of_nat (2 ^ a * (2 * b + 1)) = a.
Proof.
intros.
now eapply pow_2_of_nat_aux_mul_odd.
Qed.

Theorem odd_part_of_nat_aux_mul_odd : ∀ a b n i,
  n = 2 ^ a * (2 * b + 1)
  → n ≤ i
  → odd_part_of_nat_aux i n = b.
Proof.
intros * Hn Hni.
symmetry in Hn.
revert a b n Hn Hni.
induction i; intros.
-apply Nat.le_0_r in Hni.
 move Hni at top; subst n.
 apply Nat.eq_mul_0 in Hn.
 destruct Hn as [Hn| Hn]; [ | lia ].
 apply Nat.pow_nonzero in Hn; [ easy | lia ].
-simpl.
 destruct n.
 +apply Nat.eq_mul_0 in Hn.
  destruct Hn as [Hn| Hn]; [ | lia ].
  now apply Nat.pow_nonzero in Hn.
 +remember (Nat.even (S n)) as e eqn:He.
  symmetry in He.
  destruct e.
  *destruct a.
  --rewrite Nat.pow_0_r, Nat.mul_1_l in Hn.
    rewrite <- Hn in He.
    rewrite Nat.add_comm in He.
    now rewrite Nat.even_add_mul_2 in He.
  --rewrite Nat.pow_succ_r in Hn; [ | lia ].
    rewrite <- Nat.mul_assoc in Hn.
    rewrite <- Hn.
    rewrite Nat.div2_double.
    eapply IHi; [ easy | lia ].
  *destruct a.
  --rewrite Nat.pow_0_r, Nat.mul_1_l in Hn.
    rewrite <- Hn, Nat.add_1_r.
    now rewrite Nat.div2_succ_double.
  --rewrite Nat.pow_succ_r in Hn; [ | lia ].
    rewrite <- Nat.mul_assoc in Hn.
    rewrite <- Hn in He.
    now rewrite Nat.even_mul in He.
Qed.

Theorem odd_part_of_nat_mul_odd : ∀ a b,
  odd_part_of_nat (2 ^ a * (2 * b + 1)) = b.
Proof.
intros.
now eapply odd_part_of_nat_aux_mul_odd.
Qed.

Theorem list_nat_of_nat_aux_mul_pow2 : ∀ a b i,
  2 ^ a * (2 * b + 1) ≤ i
  → list_nat_of_nat_aux i (2 ^ a * (2 * b + 1)) =
    a :: list_nat_of_nat_aux i b.
Proof.
intros * Hab.
revert a b Hab.
induction i; intros.
-apply Nat.le_0_r in Hab.
 apply Nat.eq_mul_0 in Hab.
 destruct Hab as [Hab| ]; [ | lia ].
 now apply Nat.pow_nonzero in Hab.
-remember (2 ^ a * (2 * b + 1)) as n eqn:Hn; simpl.
 rewrite Hn.
 rewrite pow_2_of_nat_mul_odd.
 rewrite odd_part_of_nat_mul_odd.
 rewrite <- Hn.
 destruct (zerop n) as [Hzn| Hzn].
 +move Hzn at top; subst n.
  symmetry in Hn.
  apply Nat.eq_mul_0 in Hn.
  destruct Hn as [Hn| ]; [ | lia ].
  now apply Nat.pow_nonzero in Hn.
 +f_equal.
  destruct b; [ now destruct i | simpl ].
  rewrite <- IHi.
  *rewrite <- pow2_mul_odd with (n := S b); try easy; lia.
  *rewrite <- pow2_mul_odd with (n := S b); try easy.
   destruct n; [ easy | ].
   apply Nat.succ_le_mono in Hab.
   assert (H : 2 ^ a ≠ 0) by now apply Nat.pow_nonzero.
   destruct (2 ^ a); [ easy | simpl in Hn; lia ].
Qed.

Theorem list_nat_of_nat_aux_to_nat_inv : ∀ i l,
  nat_of_list_nat l ≤ i
  → list_nat_of_nat_aux i (nat_of_list_nat l) = l.
Proof.
intros * Hli.
remember (nat_of_list_nat l) as n eqn:Hn.
symmetry in Hn.
revert i l Hn Hli.
induction n as (n, IHn) using lt_wf_rec; intros.
destruct n.
-apply eq_nat_of_list_nat_0 in Hn; subst l.
 now destruct i.
-remember (pow_2_of_nat (S n)) as a eqn:Ha.
 remember (odd_part_of_nat (S n)) as b eqn:Hb.
 move b before a.
 specialize (pow2_mul_odd _ a b (Nat.neq_succ_0 n) Ha Hb) as Hsn.
 rewrite Hsn.
 rewrite list_nat_of_nat_aux_mul_pow2; [ | lia ].
 destruct l as [| a1]; [ easy | ].
 rewrite nat_of_list_nat_cons in Hn.
 rewrite <- Hn in Ha.
 rewrite pow_2_of_nat_mul_odd in Ha; subst a1.
 f_equal.
 rewrite <- Hn in Hb.
 rewrite odd_part_of_nat_mul_odd in Hb.
 symmetry in Hb.
 assert (Hbn : b < S n). {
   rewrite Hsn.
   assert (2 ^ a ≠ 0) by now apply Nat.pow_nonzero.
   destruct (2 ^ a); [ easy | simpl; lia ].
 }
 apply IHn; [ easy | easy | ].
 apply Nat.le_trans with (m := S n); [ lia | easy ].
Qed.

Theorem nat_of_list_nat_to_list_nat_aux_inv : ∀ n i,
  n ≤ i
  → nat_of_list_nat (list_nat_of_nat_aux i n) = n.
Proof.
intros * Hn.
remember (pow_2_of_nat n) as a eqn:Ha.
remember (odd_part_of_nat n) as b eqn:Hb.
move b before a.
revert a b n Ha Hb Hn.
induction i; intros; simpl; [ lia | ].
destruct (zerop n) as [Hzn| Hzn]; [ now subst n | ].
rewrite nat_of_list_nat_cons.
symmetry.
apply pow2_mul_odd; [ lia | easy | ].
rewrite <- Hb.
eapply IHi; [ easy | easy | ].
rewrite Hb.
destruct n; [ easy | ].
apply Nat.succ_le_mono in Hn.
apply Nat.le_trans with (m := n); [ apply odd_part_of_nat_le | easy ].
Qed.

   (* --- *)

Theorem list_nat_of_nat_to_nat_inv : ∀ l,
  list_nat_of_nat (nat_of_list_nat l) = l.
Proof.
intros.
now apply list_nat_of_nat_aux_to_nat_inv.
Qed.

Theorem nat_of_list_nat_to_list_nat_inv : ∀ n,
  nat_of_list_nat (list_nat_of_nat n) = n.
Proof.
intros.
now apply nat_of_list_nat_to_list_nat_aux_inv.
Qed.

   (* --- *)

Definition isequiv {A B : Type} (f : A → B) :=
  {g : B → A & (∀ a, g (f a) = a) & (∀ b, f (g b) = b)}.

Definition equivalence (A B : Type) := { f : A → B & isequiv f}.
Notation "A ≃ B" := (equivalence A B) (at level 70).

Theorem nat_equiv_list_nat : nat ≃ list nat.
Proof.
exists list_nat_of_nat.
exists nat_of_list_nat.
-apply nat_of_list_nat_to_list_nat_inv.
-apply list_nat_of_nat_to_nat_inv.
Qed.

   (* --- *)

Axiom univalence : ∀ A B, (A ≃ B) ≃ (A = B).

Theorem nat_eq_list_nat : (nat : Type) = (list nat : Type).
Proof.
specialize (univalence nat (list nat)) as H.
apply H.
apply nat_equiv_list_nat.
Qed.

Check nat_eq_list_nat.

   (* --- *)

(* for sport: proof that univalence implies extentionality *)

Definition isContr A := ∃ a : A, ∀ x : A, a = x.

Definition weak_funext A (P : A → Type) :=
  (∀ x, isContr (P x)) → isContr (∀ x, P x).

Definition hott_4_9_4 A (P : A → Type) : weak_funext A P.
...

Theorem glop : ∀ A (P : A → Type),
  (∀ x, ∃ a : P x, ∀ y, a = y)
  → ∀ x y, P x = P y.
Proof.
intros * HP x z.
specialize (HP x) as H.
destruct H as (ax, Hx).
specialize (HP z) as H.
destruct H as (az, Hz).
move az before ax.


...

Theorem weak_funext : ∀ A (P : A → Type),
  (∀ x, ∃ a : P x, ∀ y, a = y)
  → ∃ a : ∀ x, P x, ∀ y, a = y.
Proof.
intros * HP.

...

Theorem funext : ∀ A B (f g : A → B),
  (∀ x, f x = g x) → f = g.
Proof.
intros * Hfg.
...
