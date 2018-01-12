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

(*
Fixpoint npower_0_aux iter n :=
  match iter with
  | 0 => (0, 0)
  | S i =>
      if zerop n then (0, 0)
      else if Nat.even n then
        let '(npow, rest) := npower_0_aux i (Nat.div2 n) in
        (S npow, rest)
      else
        (0, Nat.div2 n)
  end.

Definition npower_0 n := npower_0_aux n n.
*)

Fixpoint list_nat_of_nat_aux iter n :=
  match iter with
  | 0 => []
  | S i =>
      if zerop n then []
      else if Nat.even n then
(*
        let '(npow, rest) := npower_0 n in
        npow :: list_nat_of_nat_aux i rest
*)
        match list_nat_of_nat_aux i (Nat.div2 n) with
        | [] => [0]
        | a :: l => S a :: l
        end
(**)
      else 0 :: list_nat_of_nat_aux i (Nat.div2 n)
  end.

Definition list_nat_of_nat n := list_nat_of_nat_aux n n.

Compute (List.fold_right
  (λ n l, (n, list_nat_of_nat n) :: l))
  [] (List.seq 0 31).

Compute (List.fold_right
  (λ n l, (n, nat_of_list_nat (list_nat_of_nat n)) :: l))
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

Print list_nat_of_nat_aux.
Print nat_of_list_nat.

Theorem nat_of_list_nat_iff : ∀ l n,
  nat_of_list_nat l = n
  ↔ match n with
     | 0 => l = []
     | S m =>
         ∃ a1 l1,
         l = a1 :: l1 ∧
         n = 2 ^ a1 * (2 * nat_of_list_nat l1 + 1)
     end.
Proof.
intros.
split.
-intros Hln.
 destruct n; [ now apply eq_nat_of_list_nat_0 | ].
 destruct l as [| a1]; [ easy | ].
 now exists a1, l.
-intros Hn.
 destruct n.
 +now apply eq_nat_of_list_nat_0; destruct l.
 +destruct Hn as (a1 & l1 & Hn & Hl).
  now subst l.
Qed.

Theorem nat_of_list_nat_cons : ∀ a l,
  nat_of_list_nat (a :: l) = 2 ^ a * (2 * nat_of_list_nat l + 1).
Proof. easy. Qed.


Theorem list_nat_of_nat_aux_mul2 : ∀ n i j,
  2 * n ≤ i → n ≤ j →
  list_nat_of_nat_aux i (2 * n) =
    match list_nat_of_nat_aux j n with
    | [] => []
    | a :: l => S a :: l
    end.
Proof.
intros * Hni Hnj.
revert j Hnj.
induction i; intros.
-destruct n; [ now destruct j | easy ].
-remember (2 * n) as m eqn:Hm; symmetry in Hm.
 simpl.
 destruct (zerop m) as [Hzm| Hzm].
 +destruct j; [ easy | ].
  subst m.
  apply Nat.eq_mul_0 in Hzm.
  destruct Hzm; [ easy | now subst n ].
 +rewrite <- Hm at 1.
  rewrite Nat.even_mul; simpl.
  rewrite <- Hm.
  rewrite Nat.div2_double.
  rewrite list_nat_of_nat_aux_enough_iter with (j := j); [ | lia | easy ].
  remember (list_nat_of_nat_aux j n) as l eqn:Hl.
  symmetry in Hl.
  destruct l; [ | easy ].
  apply eq_list_nat_of_nat_aux_nil in Hl; lia.
Qed.

Theorem list_nat_of_nat_mul2 : ∀ n,
  list_nat_of_nat (2 * n) =
    match list_nat_of_nat n with
    | [] => []
    | a :: l => S a :: l
    end.
Proof.
intros.
now apply list_nat_of_nat_aux_mul2.
Qed.

Theorem list_nat_of_nat_aux_pow2 : ∀ n i,
  2 ^ n ≤ i →
  list_nat_of_nat_aux i (2 ^ n) = [n].
Proof.
intros * Hni.
revert i Hni.
induction n; intros.
-destruct i; [ easy | now destruct i ].
-rewrite Nat.pow_succ_r; [ | lia ].
 erewrite list_nat_of_nat_aux_mul2; [ | easy | reflexivity ].
 now rewrite IHn.
Qed.

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
 +symmetry.
  apply Bool.not_true_iff_false.
  intros Ho.
  apply Nat.even_spec in He.
  apply Nat.odd_spec in Ho.
  now apply Nat.Even_Odd_False in He.
-specialize (Nat.div2_odd (S n)) as H.
 rewrite <- Hb in H.
 replace (Nat.odd (S n)) with true in H.
 +now subst a; rewrite Nat.pow_0_r, Nat.mul_1_l.
 +symmetry.
  Check Nat.Even_or_Odd.
  specialize (Nat.Even_or_Odd (S n)) as Heo.
  destruct Heo as [Heo| Heo].
  *apply Nat.even_spec in Heo.
   now rewrite He in Heo.
  *now apply Nat.odd_spec.
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

Theorem list_nat_of_nat_pow2 : ∀ n,
  list_nat_of_nat (2 ^ n) = [n].
Proof.
intros.
now apply list_nat_of_nat_aux_pow2.
Qed.

Theorem tigidi : ∀ i l,
  nat_of_list_nat l ≤ i
  → list_nat_of_nat_aux i (nat_of_list_nat l) = l.
Proof.
intros * Hli.
remember (nat_of_list_nat l) as n eqn:Hn.
symmetry in Hn.
revert i l Hn Hli.
induction n as (n, IHn) using lt_wf_rec.
intros * Hln Hni.
destruct n.
-apply eq_nat_of_list_nat_0 in Hln; subst l.
 now destruct i.
-idtac.
 Check pow2_mul_odd.
...

-destruct i; [ easy | ].
 remember (S n) as sn; simpl; subst sn.
 destruct (zerop (S n)) as [| H]; [ easy | clear H ].

...

intros * Hli.
remember (nat_of_list_nat l) as n eqn:Hn.
symmetry in Hn.
remember (Nat.log2 n) as ln eqn:Hln.
symmetry in Hln.
revert i l n Hn Hli Hln.
induction ln; intros.
-apply Nat.log2_null in Hln.
 destruct n.
 +apply eq_nat_of_list_nat_0 in Hn; subst l.
  now destruct i.
 +destruct i; [ easy | ].
  replace n with 0 in Hn |-* by lia.
  destruct l as [| a]; [ easy | ].
  rewrite nat_of_list_nat_cons in Hn; simpl.
  remember (2 ^ a) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ easy | ].
  destruct b; [ | simpl in Hn; lia ].
  destruct a; [ | simpl in Hb; lia ].
  rewrite Nat.mul_1_l in Hn.
  assert (H : nat_of_list_nat l = 0) by lia.
  apply eq_nat_of_list_nat_0 in H; subst l.
  now destruct i.
-enough (H : Nat.log2 (Nat.div2 n) = ln).
 +destruct l as [| a].
  *simpl in Hn; subst n.
   now destruct i.
  *rewrite nat_of_list_nat_cons in Hn.
   destruct i.
  --apply Nat.le_0_r in Hli.
    now rewrite Hli in Hln.
  --simpl.
    destruct (zerop n) as [Hz| Hz].
   ++now rewrite Hz in Hln.
   ++remember (Nat.even n) as b eqn:Hb.
     symmetry in Hb.
     destruct b.
    **idtac.
      destruct a.
    ---rewrite Nat.pow_0_r, Nat.mul_1_l in Hn.
       rewrite <- Hn in Hb.
       rewrite Nat.
...

    **destruct l as [| a1 ].
    ---simpl in Hn; rewrite Nat.mul_1_r in Hn.
       subst n.
       rewrite Nat.log2_pow2 in Hln; [ | lia ].
       subst a.
       rewrite Nat.pow_succ_r; [ | lia ].
       rewrite Nat.div2_double.
       destruct ln.
     +++simpl in Hli; simpl.
        destruct i; [ lia | now destruct i ].
     +++destruct i.
      ***simpl in Hli.
         assert (2 ^ ln ≠ 0) by now apply Nat.pow_nonzero.
         lia.
      ***remember (2 ^ S ln) as s eqn:Hs; simpl; subst s.
         destruct (zerop (2 ^ S ln)) as [Hzz| Hzz].
      ----now apply Nat.pow_nonzero in Hzz.
      ----clear H Hz Hb Hzz.
          rewrite Nat.pow_succ_r; [ | lia ].
          rewrite Nat.div2_double.
          rewrite Nat.even_mul; simpl.
          rewrite list_nat_of_nat_aux_pow2; [ easy | ].
          simpl in Hli; lia.
    ---destruct a.
     +++exfalso.
        rewrite nat_of_list_nat_cons in Hn.
        rewrite Nat.pow_0_r, Nat.mul_1_l in Hn.
        rewrite <- Hn in Hb.
        rewrite Nat.add_comm in Hb.
        now rewrite Nat.even_add_mul_2 in Hb.
     +++rewrite IHln with (l := a :: a1 :: l); [ easy | | | easy ].
      ***rewrite nat_of_list_nat_cons.
         rewrite <- Hn.
         rewrite Nat.pow_succ_r; [ | lia ].
         rewrite <- Nat.mul_assoc.
         now rewrite Nat.div2_double.
      ***now apply Nat.div2_decr in Hli.
    **destruct a.
    ---f_equal.
       rewrite Nat.pow_0_r, Nat.mul_1_l in Hn.
       apply IHln.

...

intros * Hli.
remember (nat_of_list_nat l) as n eqn:Hn.
symmetry in Hn.
revert l n Hn Hli.
induction i; intros.
apply Nat.le_0_r in Hli; subst n.
-apply eq_nat_of_list_nat_0 in Hli.
 now subst l.
-destruct n.
 +now apply eq_nat_of_list_nat_0 in Hn; subst l.
 +remember (S n) as sn; simpl; subst sn.
  remember (Nat.even (S n)) as b1 eqn:Hb1.
  remember (Nat.div2 (S n)) as b2 eqn:Hb2.
  symmetry in Hb1, Hb2; simpl.
  destruct b1.
  *remember (list_nat_of_nat_aux i b2) as l1 eqn:Hl1.
   symmetry in Hl1.
   destruct l1 as [| a1].
  --apply eq_list_nat_of_nat_aux_nil in Hl1.
    destruct Hl1 as [Hl1| Hl1].
   ++subst i.
     apply Nat.succ_le_mono in Hli.
     now apply Nat.le_0_r in Hli; subst n.
   ++now subst b2; destruct n.
  --erewrite IHi with (l := S a1 :: l1) in Hl1.
   ++injection Hl1; clear Hl1; intros; lia.
   ++simpl.
admit.
++idtac.
admit.  
*idtac.
erewrite IHi.
(* ça marche peut-être mais j'y crois pas *)
...

intros * Hli.
remember (nat_of_list_nat l) as n eqn:Hn.
symmetry in Hn.
revert i l Hn Hli.
induction n; intros.
-apply eq_nat_of_list_nat_0 in Hn.
 now subst l; destruct i.
-destruct i; [ easy | ].
 remember (S n) as sn; simpl; subst sn.
 remember (Nat.even (S n)) as b1 eqn:Hb1.
 remember (Nat.div2 (S n)) as b2 eqn:Hb2.
 symmetry in Hb1, Hb2; simpl.
...

intros * Hli.
remember (nat_of_list_nat l) as n eqn:Hn.
symmetry in Hn.
destruct l as [| a1]; [ now subst n; destruct i | ].
destruct i.
-exfalso; apply Nat.le_0_r in Hli; subst n.
 now apply eq_nat_of_list_nat_0 in Hli.
-rewrite nat_of_list_nat_cons in Hn; simpl.
 destruct n.
 +exfalso.
  specialize (Nat.pow_nonzero 2 a1 (Nat.neq_succ_0 1)) as H.
  destruct (2 ^ a1); [ easy | simpl in Hn; lia ].
 +remember (Nat.even (S n)) as b1 eqn:Hb1.
  remember (Nat.div2 (S n)) as b2 eqn:Hb2.
  symmetry in Hb1, Hb2; simpl.
  destruct b1.
  *remember (list_nat_of_nat_aux i b2) as l1 eqn:Hl1.
   symmetry in Hl1.
   destruct l1 as [| a2].
   apply eq_list_nat_of_nat_aux_nil in Hl1.
   destruct Hl1 as [Hl1| Hl1].
  --now replace n with 0 in Hb1 by lia.
  --subst b2.
    destruct n.
   ++remember (nat_of_list_nat l) as m eqn:Hm.
     symmetry in Hm.
     specialize (Nat.pow_nonzero 2 a1 (Nat.neq_succ_0 1)) as H.
     destruct a1; [ easy | ].
     destruct (2 ^ a1); [ easy | simpl in Hn; lia ].
   ++idtac.


...

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
 destruct (zerop (nat_of_list_nat l)) as [Hn| Hn].
 +clear - Hn.
  destruct l as [| a]; [ easy | exfalso ].
  simpl in Hn.
  apply Nat.eq_mul_0 in Hn.
  specialize (Nat.pow_nonzero 2 a (Nat.neq_succ_0 1)) as H.
  destruct Hn; [ easy | lia ].
 +remember (nat_of_list_nat l) as m eqn:Hm.
  symmetry in Hm.
  destruct m; [ easy | clear Hn ].
  apply Nat.succ_le_mono in Hli.
  rewrite Nat.even_succ.
  remember (Nat.odd m) as no eqn:Hno.
  symmetry in Hno.
  destruct no.
  *remember (list_nat_of_nat_aux i (Nat.div2 (S m))) as l1 eqn:Hl1.
   symmetry in Hl1.
   destruct l1 as [| a].
  --apply eq_list_nat_of_nat_aux_nil in Hl1.
    destruct Hl1 as [Hi| Hdm]; [ | now destruct m ].
    now subst i; apply Nat.le_0_r in Hli; subst m.
  --simpl in Hl1.
    destruct m; [ easy | ].
    destruct i; [ easy | ].
    simpl in Hl1.
    remember (Nat.div2 m) as n eqn:Hn.
    symmetry in Hn.
    destruct n.
   ++injection Hl1; clear Hl1; intros; subst a l1.
     destruct m; [ | now destruct m ].
     destruct l as [| a]; [ easy | ].
     simpl in Hm.
     destruct a.
    **rewrite Nat.pow_0_r, Nat.mul_1_l in Hm; lia.
    **simpl in Hm.
      destruct a.
    ---f_equal.
       rewrite Nat.pow_0_r, Nat.add_0_r, Nat.add_0_r in Hm.
       simpl in Hm.
       assert (nat_of_list_nat l = 0) by lia.
       apply eq_nat_of_list_nat_0 in H.
       subst l.
       now destruct i.
    ---simpl in Hm; lia.
   ++remember (Nat.even n) as b eqn:Hb.
     symmetry in Hb.
     destruct b.
    **destruct i; simpl in Hl1.
    ---apply Nat.succ_le_mono in Hli.
       now apply Nat.le_0_r in Hli; subst m.
    ---remember (Nat.div2 n) as p eqn:Hp.
       symmetry in Hp.
       destruct p.
     +++destruct n.
      ***destruct m; [ easy | ].
         destruct m; [ easy | ].
         simpl in Hn.
         apply Nat.succ_inj in Hn.
         destruct m.
      ----clear Hno Hn Hb Hp.
          injection Hl1; clear Hl1; intros; subst a l1.
          apply nat_of_list_nat_iff in Hm.
          destruct Hm as (a1 & l1 & Hn & Hl).
          subst l.
          destruct a1.
       ++++rewrite Nat.pow_0_r, Nat.mul_1_l in Hl; lia.
       ++++destruct a1.
        ****rewrite Nat.pow_1_r in Hl; lia.
        ****destruct a1.
        -----f_equal.
             replace 4 with (4 * 1) in Hl by easy.
             replace (2 ^ 2) with 4 in Hl by easy.
             apply Nat.mul_cancel_l in Hl; [ | easy ].
             replace 1 with (0 + 1) in Hl at 1 by easy.
             apply Nat.add_cancel_r in Hl.
             symmetry in Hl.
             apply Nat.eq_mul_0 in Hl.
             destruct Hl as [| Hl]; [ easy | ].
             apply eq_nat_of_list_nat_0 in Hl; subst l1.
             now destruct i.
        -----simpl in Hl; lia.
      ----idtac.
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
