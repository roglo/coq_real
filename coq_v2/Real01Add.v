Require Import Utf8 QArith NPeano.
Require Import Real01.

Open Scope nat_scope.

Definition b2n (b : bool) := if b then 1 else 0.

Definition I_add_wn_i x y i := b2n (x.[i]) + b2n (y.[i]).
Arguments I_add_wn_i x%I y%I i%nat.

Definition I_add_wn x y := {| inat := I_add_wn_i x y |}.
Arguments I_add_wn x%I y%I.

Definition carry x i :=
  match fst_not_1 x i with
  | Some di => inat x (i + di)
  | None => 1
  end.

Definition Iwn2I x i := Nat.eqb (inat x i) 0 ⊕ Nat.eqb (carry x (S i)) 0.

Definition I_add x y := {| idig := Iwn2I (I_add_wn x y) |}.

Definition I_zero := {| idig i := false |}.

Notation "0" := I_zero : I_scope.
Notation "x + y" := (I_add x y) (at level 50, left associativity) : I_scope.

Definition I_eq x y := ∀ i, (x + 0)%I.[i] = (y + 0)%I.[i].

Notation "x = y" := (I_eq x y) : I_scope.
Notation "x ≠ y" := (¬ I_eq x y) : I_scope.


(* commutativity *)

Theorem I_add_wn_i_comm : ∀ x y i, I_add_wn_i x y i = I_add_wn_i y x i.
Proof. intros; apply Nat.add_comm. Qed.

Theorem fst_not_1_add_comm : ∀ x y i,
  fst_not_1 (I_add_wn x y) i = fst_not_1 (I_add_wn y x) i.
Proof.
intros x y i.
apply fst_not_1_iff; simpl.
remember (fst_not_1 (I_add_wn x y) i) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Ht1).
 split; [ idtac | rewrite I_add_wn_i_comm; assumption ].
 intros dj Hdj.
 apply Hn1 in Hdj.
 rewrite I_add_wn_i_comm; assumption.

 intros dj.
 rewrite I_add_wn_i_comm.
 apply Hs1.
Qed.

Theorem carry_add_comm : ∀ x y i,
  carry (I_add_wn x y) i = carry (I_add_wn y x) i.
Proof.
intros x y i.
unfold carry; simpl.
rewrite fst_not_1_add_comm.
bbb.

Theorem I_add_wn_i_comm_l : ∀ x y z i,
  I_add_wn_i (x + y) z i = I_add_wn_i (y + x) z i.
Proof.
intros x y z i.
unfold I_add_wn_i; simpl; f_equal; f_equal.
unfold Iwn2I; simpl.
unfold I_add_wn_i; simpl; f_equal; f_equal; [ apply Nat.add_comm | idtac ].
bbb.

Theorem I_add_comm : ∀ x y, (x + y = y + x)%I.
Proof.
intros x y.
unfold I_eq; simpl; intros i.
unfold Iwn2I; simpl.
bbb.
