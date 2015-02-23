(* Oracle giving the index of a non-zero value in an integer sequence
   or None if the sequence is identically nul *)

Require Import Utf8.

(* find any non-zero value of an integer sequence (oracle) *)

Parameter find_nonzero : (nat → nat) → option nat.
Axiom find_nonzero_iff : ∀ u odi, odi = find_nonzero u ↔
  match odi with
  | Some i => u i ≠ 0
  | None => (∀ j, u j = 0)
  end.

(* find the first nonzero of an integer sequence *)

Require Import Arith NPeano Misc.

Fixpoint first_nonzero_loop (u : nat → nat) m i :=
  if zerop (u i) then
    match m with
    | 0 => 0
    | S m1 => first_nonzero_loop u m1 (S i)
    end
  else i.

Definition first_nonzero u :=
  match find_nonzero u with
  | Some i => Some (first_nonzero_loop u i 0)
  | None => None
  end.

Theorem zero_before_first_nonzero : ∀ u m i j,
  i ≤ j
  → j < first_nonzero_loop u m i
  → u j = 0.
Proof.
intros u m i j Hij Hj.
revert i j Hij Hj.
induction m; intros; simpl in Hj.
 destruct (zerop (u i)) as [Hui| Hui].
  exfalso; revert Hj; apply Nat.nlt_0_r.

  apply Nat.nle_gt in Hj; contradiction.

 destruct (zerop (u i)) as [Hui| Hui].
  destruct (eq_nat_dec i j) as [H1| H1].
   subst i; assumption.

   eapply IHm; [ idtac | eassumption ].
   apply Nat_le_neq_lt; assumption.

  apply Nat.nle_gt in Hj; contradiction.
Qed.

Theorem nonzero_at_first_nonzero : ∀ u m i,
  u (i + m) ≠ 0
  → u (first_nonzero_loop u m i) ≠ 0.
Proof.
intros u m i H.
intros Hm; apply H; clear H.
revert i Hm.
induction m; intros; simpl in Hm.
 rewrite Nat.add_0_r.
 destruct (zerop (u i)); assumption.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 destruct (zerop (u i)) as [H1| H1]; [ apply IHm; assumption | idtac ].
 rewrite Hm in H1.
 exfalso; revert H1; apply Nat.nlt_0_r.
Qed.

Theorem first_nonzero_iff : ∀ u odi, odi = first_nonzero u ↔
  match odi with
  | Some i => (∀ j, j < i → u j = 0) ∧ u i ≠ 0
  | None => (∀ j, u j = 0)
  end.
Proof.
intros u odi.
split; intros Hi.
 unfold first_nonzero in Hi; simpl in Hi.
 remember (find_nonzero u) as s1 eqn:Hs1 .
 apply find_nonzero_iff in Hs1; simpl in Hs1.
 destruct odi as [i| ].
  destruct s1 as [k| ]; [ idtac | discriminate Hi ].
  injection Hi; clear Hi; intros; subst i.
  split; [ idtac | apply nonzero_at_first_nonzero; assumption ].
  intros j Hj.
  eapply zero_before_first_nonzero; [ idtac | eassumption ].
  apply Nat.le_0_l.

  intros j.
  destruct s1 as [k| ]; [ discriminate Hi | apply Hs1 ].

 unfold first_nonzero.
 remember (find_nonzero u) as s1 eqn:Hs1 .
 apply find_nonzero_iff in Hs1; simpl in Hs1.
 destruct s1 as [k| ].
  destruct odi as [i| ].
   destruct Hi as (Hn, Ht).
   f_equal.
   remember (first_nonzero_loop u k 0) as j eqn:Hj .
   destruct (lt_eq_lt_dec i j) as [[H1| H1]| H1].
    subst j.
    apply zero_before_first_nonzero in H1; [ idtac | apply Nat.le_0_l ].
    contradiction.

    assumption.

    apply Hn in H1; subst j.
    apply nonzero_at_first_nonzero in H1; [ contradiction | assumption ].

   exfalso; apply Hs1, Hi.

  destruct odi as [i| ]; [ idtac | reflexivity ].
  destruct Hi as (Hn, Ht).
  exfalso; apply Ht, Hs1.
Qed.
