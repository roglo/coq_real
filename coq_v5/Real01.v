Require Import Utf8 QArith NPeano.
Require Import Oracle Digit.

Open Scope nat_scope.

(* I = interval [0..1] of ℝ *)
Record I := mki { rm : nat → digit }.

Definition I_zero := {| rm i := 0%D |}.
Definition I_one := {| rm i := 1%D |}.

Notation "s .[ i ]" := (rm s i) (at level 15, i at level 200).

Delimit Scope I_scope with I.
Notation "0" := I_zero : I_scope.
Notation "1" := I_one : I_scope.

Definition I_eq_ext x y := ∀ i, x.[i] = y.[i].
Arguments I_eq_ext x%I y%I.

(* actually, I think that I_eq_ext is equivalent to I_eqs in Real01Cmp.v
   something should be done to unify these definitions *)

Theorem I_eq_ext_refl : reflexive _ I_eq_ext.
Proof. intros x i; reflexivity. Qed.

Theorem I_eq_ext_sym : symmetric _ I_eq_ext.
Proof.
intros x y Hxy i.
rewrite Hxy; reflexivity.
Qed.

Theorem I_eq_ext_trans : transitive _ I_eq_ext.
Proof.
intros x y z Hxy Hyz i.
rewrite Hxy, Hyz; reflexivity.
Qed.

Add Parametric Relation : _ I_eq_ext
 reflexivity proved by I_eq_ext_refl
 symmetry proved by I_eq_ext_sym
 transitivity proved by I_eq_ext_trans
 as I_eq_ext_rel.

Definition test_not_1 u i j := if eq_nat_dec (u (i + j)) 1 then 0 else 1.
Definition fst_not_1 u i := first_nonzero (test_not_1 u i).

Theorem fst_not_1_iff : ∀ u i odi, odi = fst_not_1 u i ↔
  match odi with
  | Some di => (∀ dj, dj < di → u (i + dj) = 1) ∧ u (i + di) ≠ 1
  | None => ∀ dj, u (i + dj) = 1
  end.
Proof.
intros u i odi.
split; intros Hi.
 subst odi.
 unfold fst_not_1; simpl.
 remember (first_nonzero (test_not_1 u i)) as s1 eqn:Hs1 .
 apply first_nonzero_iff in Hs1; simpl in Hs1.
 unfold test_not_1 in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Ht1).
  destruct (eq_nat_dec (u (i + di1)) 1) as [H1| H1].
   exfalso; apply Ht1; reflexivity.

   split; [ idtac | assumption ].
   intros dj Hdj.
   remember Hdj as H; clear HeqH.
   apply Hn1 in H.
   destruct (eq_nat_dec (u (i + dj)) 1); [ assumption | discriminate H ].

  intros dj.
  pose proof (Hs1 dj) as H.
  destruct (eq_nat_dec (u (i + dj)) 1); [ assumption | discriminate H ].

 unfold fst_not_1; simpl.
 apply first_nonzero_iff.
 destruct odi as [di| ].
  destruct Hi as (Hn1, Ht1).
  unfold test_not_1; simpl.
  destruct (eq_nat_dec (u (i + di)) 1) as [H1| H1]; [ contradiction | idtac ].
  split; [ idtac | intros H; discriminate H ].
  intros j Hj.
  destruct (eq_nat_dec (u (i + j)) 1) as [H2| H2]; [reflexivity | idtac ].
  exfalso; apply H2, Hn1; assumption.

  unfold test_not_1; intros j.
  destruct (eq_nat_dec (u (i + j)) 1) as [H1| H1]; [reflexivity | idtac ].
  exfalso; apply H1, Hi.
Qed.
