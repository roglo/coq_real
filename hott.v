(* Proof that nat=list nat, using univalence axiom *)

Require Import Utf8 Arith Psatz.
Require List.
Import List.ListNotations.
Open Scope list_scope.

Definition isequiv {A B : Type} (f : A → B) :=
  {g : B → A & (∀ a, g (f a) = a) & (∀ b, f (g b) = b)}.

Definition equivalence (A B : Type) := { f : A → B & isequiv f}.
Notation "A ≃ B" := (equivalence A B) (at level 70).

Axiom univalence : ∀ A B, (A ≃ B) ≃ (A = B).

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
      else if Nat.even n then
        match list_nat_of_nat_aux i (Nat.div2 n) with
        | [] => [0]
        | a :: l => S a :: l
        end
      else 0 :: list_nat_of_nat_aux i (Nat.div2 n)
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

Theorem eq_list_nat_of_nat_aux_nil : ∀ iter n,
  list_nat_of_nat_aux iter n = []
  ↔ iter = 0 ∨ n = 0.
Proof.
intros.
split.
-intros Hl.
 destruct iter; [ now left | right; simpl in Hl ].
 destruct n; [ easy | exfalso; simpl in Hl ].
 destruct n; [ easy | ].
 destruct (Nat.even n); [ | easy ].
 now destruct (list_nat_of_nat_aux iter (S (Nat.div2 n))).
-intros [Hi| Hn]; [ now subst iter | ].
 subst n; now destruct iter.
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
 symmetry in Hn.
 destruct n.
 +apply Nat.eq_mul_0 in Hn.
  destruct Hn as [Hn |]; [ | lia ].
  now apply Nat.pow_nonzero in Hn.
 +destruct (zerop (S n)) as [| H]; [ easy | clear H ].
  remember (Nat.even (S n)) as e eqn:He.
  symmetry in He.
  destruct e.
  *destruct b.
  --remember (S n) as sn; simpl; subst sn.
    simpl in Hn; rewrite Nat.mul_1_r in Hn.
    rewrite <- Hn.
    destruct a; [ now destruct i | ].
    rewrite Nat.pow_succ_r; [ | lia ].
    rewrite Nat.div2_double.
    assert (Hi : 2 ^ a * (2 * 0 + 1) ≤ i). {
      simpl in Hn; simpl; lia.
    }
    specialize (IHi a 0 Hi) as IH.
    rewrite Nat.mul_0_r, Nat.mul_1_r in IH.
    rewrite IH.
    now destruct i.
  --destruct (zerop (S b)) as [| H]; [ easy | clear H ].
    destruct a.
   ++rewrite Nat.pow_0_r, Nat.mul_1_l in Hn.
     rewrite <- Hn in He.
     rewrite Nat.add_comm in He.
     now rewrite Nat.even_add_mul_2 in He.
   ++rewrite Nat.pow_succ_r in Hn; [ | lia ].
     rewrite <- Nat.mul_assoc in Hn.
     rewrite <- Hn.
     rewrite Nat.div2_double.
     rewrite IHi; [ | lia ].
     f_equal.
     remember (Nat.even (S b)) as sb eqn:Hsb.
     symmetry in Hsb.
     destruct sb.
    **destruct i; [ lia | ].
      remember (S i) as si eqn:Hsi.
      rewrite Hsi at 1.
      remember (S b) as sb; simpl; subst sb si.
      rewrite Hsb.
      enough (Nat.div2 (S b) ≤ i).
    ---rewrite list_nat_of_nat_aux_enough_iter with (j := S i); try easy; lia.
    ---apply Nat.div2_decr.
       apply Nat.succ_le_mono.
       eapply Nat.le_trans; [ | apply Hab ].
       rewrite <- Hn; simpl.
       assert (2 ^ a ≠ 0) by now apply Nat.pow_nonzero.
       destruct (2 ^ a); [ easy | simpl; lia ].
    **rewrite <- IHi.
    ---rewrite Nat.pow_0_r, Nat.mul_1_l.
       f_equal.
       specialize (Nat.div2_odd (S b)) as H.
       rewrite H; f_equal; f_equal.
     +++f_equal; apply Nat.div2_odd.
     +++rewrite <- Nat.negb_odd in Hsb.
        apply Bool.negb_false_iff in Hsb.
        now rewrite Hsb.
    ---rewrite Nat.pow_0_r, Nat.mul_1_l.
       apply Nat.le_trans with (m := 2 * b + 1).
       apply Nat.add_le_mono_r.
       apply Nat.mul_le_mono_l.
       apply Nat.le_div2.
       assert (2 ^ a ≠ 0) by now apply Nat.pow_nonzero.
       destruct (2 ^ a); [ easy | simpl in Hn; lia ].
  *destruct a.
  --f_equal.
    rewrite Nat.pow_0_r, Nat.mul_1_l, Nat.add_1_r in Hn.
    rewrite <- Hn.
    rewrite Nat.div2_succ_double.
    destruct b; [ now destruct i | ].
    destruct (zerop (S b)) as [| H]; [ easy | clear H ].
    remember (Nat.even (S b)) as sb eqn:Hsb.
    symmetry in Hsb.
    destruct sb.
   ++destruct i; [ lia | ].
     remember (S i) as si eqn:Hsi.
     rewrite Hsi at 1.
     remember (S b) as x; simpl; subst x.
     destruct (zerop (S b)) as [| H]; [ easy | clear H ].
     rewrite Hsb.
     assert (Nat.div2 (S b) ≤ i) by (apply Nat.div2_decr; lia).
     rewrite list_nat_of_nat_aux_enough_iter with (j := si); try easy; lia.
   ++rewrite <- IHi.
    **rewrite Nat.pow_0_r, Nat.mul_1_l.
      f_equal.
      specialize (Nat.div2_odd (S b)) as H.
      rewrite H; f_equal; f_equal.
    ---f_equal; apply Nat.div2_odd.
    ---rewrite <- Nat.negb_odd in Hsb.
       apply Bool.negb_false_iff in Hsb.
       now rewrite Hsb.
    **rewrite Nat.pow_0_r, Nat.mul_1_l.
      apply Nat.le_trans with (m := 2 * b + 1); [ | lia ].
      apply Nat.add_le_mono_r.
      apply Nat.mul_le_mono_l.
      apply Nat.le_div2.
  --rewrite <- Hn in He.
    rewrite Nat.pow_succ_r in He; [ | lia ].
    rewrite <- Nat.mul_assoc in He.
    now rewrite Nat.even_mul in He.
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

Theorem list_nat_of_nat_to_nat_inv : ∀ l,
  list_nat_of_nat (nat_of_list_nat l) = l.
Proof.
intros.
now apply list_nat_of_nat_aux_to_nat_inv.
Qed.

Theorem nat_of_list_nat_to_list_nat_aux_inv : ∀ n i,
  n ≤ i
  → nat_of_list_nat (list_nat_of_nat_aux i n) = n.
Proof.
intros * Hn.
remember (list_nat_of_nat_aux i n) as l eqn:Hl.
symmetry in Hl.
revert i l Hn Hl.
induction n as (n, IHn) using lt_wf_rec; intros.
destruct n; [ now destruct i; simpl in Hl; subst l | ].
destruct i; [ easy | ].
remember (S n) as sn; simpl in Hl; subst sn.
destruct (zerop (S n)) as [| H]; [ easy | clear H ].
remember (Nat.even (S n)) as e eqn:He.
symmetry in He.
remember (list_nat_of_nat_aux i (Nat.div2 (S n))) as l1 eqn:Hl1.
symmetry in Hl1.
assert (Hsn : Nat.div2 (S n) < S n) by (apply Nat.lt_div2; lia).
assert (Hsni : Nat.div2 (S n) ≤ i) by lia.
destruct e.
-destruct l1 as [| a1].
 +subst l; simpl.
  apply eq_list_nat_of_nat_aux_nil in Hl1.
  destruct Hl1; [ subst i; lia | now destruct n ].
 +subst l.
  rewrite nat_of_list_nat_cons.
  specialize (IHn (Nat.div2 (S n)) Hsn i (a1 :: l1) Hsni Hl1) as IH.
  rewrite nat_of_list_nat_cons in IH.
  rewrite Nat.pow_succ_r; [ | lia ].
  rewrite <- Nat.mul_assoc, IH.
  specialize (Nat.div2_odd (S n)) as H.
  rewrite <- Nat.negb_odd in He.
  apply Bool.negb_true_iff in He.
  rewrite He in H.
  unfold Nat.b2n in H; lia.
-subst l.
 rewrite nat_of_list_nat_cons.
 rewrite Nat.pow_0_r, Nat.mul_1_l.
 specialize (IHn (Nat.div2 (S n)) Hsn i l1 Hsni Hl1) as IH.
 rewrite IH.
 specialize (Nat.div2_odd (S n)) as H.
 rewrite <- Nat.negb_odd in He.
 apply Bool.negb_false_iff in He.
 rewrite He in H.
 unfold Nat.b2n in H; lia.
Qed.

Theorem nat_of_list_nat_to_list_nat_inv : ∀ n,
  nat_of_list_nat (list_nat_of_nat n) = n.
Proof.
intros.
now apply nat_of_list_nat_to_list_nat_aux_inv.
Qed.

Theorem nat_eq_list_nat : (nat : Type) = (list nat : Type).
Proof.
specialize (univalence nat (list nat)) as (f, Hf).
destruct Hf as (g, Hgf, Hfg).
apply f.
exists list_nat_of_nat.
exists nat_of_list_nat; intros.
-apply nat_of_list_nat_to_list_nat_inv.
-apply list_nat_of_nat_to_nat_inv.
Qed.

Check nat_eq_list_nat.

