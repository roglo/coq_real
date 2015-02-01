(* Oracle giving the index of a true of an boolean sequence
   or None if the sequence has only falses *)

Require Import Utf8 Arith NPeano Misc.

(* find any true of a boolean sequence (oracle) *)

Parameter find_true : (nat → bool) → option nat.
Axiom find_true_iff : ∀ u odi, odi = find_true u ↔
  match odi with
  | Some i => u i = true
  | None => (∀ j, u j = false)
  end.

(* find the first true of a boolean sequence *)

Fixpoint first_true_loop (u : nat → bool) m i :=
  if u i then i
  else
    match m with
    | 0 => 0
    | S m1 => first_true_loop u m1 (S i)
    end.

Definition first_true u :=
  match find_true u with
  | Some i => Some (first_true_loop u i 0)
  | None => None
  end.

Theorem false_before_first_true : ∀ u m i j,
  i ≤ j
  → j < first_true_loop u m i
  → u j = false.
Proof.
intros u m i j Hij Hj.
revert i j Hij Hj.
induction m; intros.
 simpl in Hj.
 destruct (u i).
  apply Nat.nle_gt in Hj; contradiction.

  exfalso; revert Hj; apply Nat.nlt_0_r.

 simpl in Hj.
 remember (u i) as ui eqn:Hui .
 symmetry in Hui.
 destruct ui; [ apply Nat.nle_gt in Hj; contradiction | idtac ].
 destruct (eq_nat_dec i j) as [H1| H1].
  subst i; assumption.

  eapply IHm; [ idtac | eassumption ].
  apply Nat_le_neq_lt; assumption.
Qed.

Theorem true_at_first_true : ∀ u m i,
  u (i + m) = true
  → u (first_true_loop u m i) = true.
Proof.
intros u m i Hm.
revert i Hm.
induction m; intros; simpl.
 rewrite Nat.add_0_r in Hm; rewrite Hm; assumption.

 remember (u i) as ui eqn:Hui .
 symmetry in Hui.
 destruct ui; [ assumption | idtac ].
 rewrite Nat.add_succ_r in Hm.
 apply IHm; assumption.
Qed.

Theorem first_true_iff : ∀ u odi, odi = first_true u ↔
  match odi with
  | Some i => (∀ j, j < i → u j = false) ∧ u i = true
  | None => (∀ j, u j = false)
  end.
Proof.
intros u odi.
split; intros Hi.
 unfold first_true in Hi; simpl in Hi.
 remember (find_true u) as s1 eqn:Hs1 .
 apply find_true_iff in Hs1; simpl in Hs1.
 destruct odi as [i| ].
  destruct s1 as [k| ]; [ idtac | discriminate Hi ].
  injection Hi; clear Hi; intros; subst i.
  split; [ idtac | apply true_at_first_true; assumption ].
  intros j Hj.
  eapply false_before_first_true; [ idtac | eassumption ].
  apply Nat.le_0_l.

  intros j.
  destruct s1 as [k| ]; [ discriminate Hi | apply Hs1 ].

 unfold first_true.
 remember (find_true u) as s1 eqn:Hs1 .
 apply find_true_iff in Hs1; simpl in Hs1.
 destruct s1 as [k| ].
  destruct odi as [i| ].
   destruct Hi as (Hn, Ht).
   f_equal.
   remember (first_true_loop u k 0) as j eqn:Hj .
   destruct (lt_eq_lt_dec i j) as [[H1| H1]| H1].
    subst j.
    apply false_before_first_true in H1; [ idtac | apply Nat.le_0_l ].
    rewrite Ht in H1; discriminate H1.

    assumption.

    apply Hn in H1; subst j.
    rewrite true_at_first_true in H1; [ discriminate H1 | assumption ].

   rewrite Hi in Hs1; discriminate Hs1.

  destruct odi as [i| ]; [ idtac | reflexivity ].
  destruct Hi as (Hn, Ht).
  rewrite Hs1 in Ht; discriminate Ht.
Qed.
