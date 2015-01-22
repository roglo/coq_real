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

Definition I_eq_wn x y := ∀ i, inat x i = inat y i.
Definition I_eqs x y := ∀ i, x.[i] = y.[i].
Definition I_eq x y := ∀ i, (x + 0)%I.[i] = (y + 0)%I.[i].
Arguments I_eq_wn x%I y%I.
Arguments I_eqs x%I y%I.
Arguments I_eq x%I y%I.

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
remember (fst_not_1 (I_add_wn y x) i) as s1 eqn:Hs1 .
destruct s1 as [di1| ]; [ idtac | reflexivity ].
rewrite I_add_wn_i_comm; reflexivity.
Qed.

Theorem I_add_wn_i_comm_l : ∀ x y z i,
  I_add_wn_i (x + y) z i = I_add_wn_i (y + x) z i.
Proof.
intros x y z i.
unfold I_add_wn_i; simpl; f_equal; f_equal.
unfold Iwn2I; simpl.
unfold I_add_wn_i; simpl; f_equal; f_equal; [ apply Nat.add_comm | idtac ].
apply carry_add_comm.
Qed.

Theorem fst_not_1_add_comm_l : ∀ x y z i,
  fst_not_1 (I_add_wn (x + y) z) i = fst_not_1 (I_add_wn (y + x) z) i.
Proof.
intros x y z i.
apply fst_not_1_iff; simpl.
remember (fst_not_1 (I_add_wn (x + y) z) i) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Ht1).
 split; [ idtac | rewrite I_add_wn_i_comm_l; assumption ].
 intros dj Hdj.
 apply Hn1 in Hdj.
 rewrite I_add_wn_i_comm_l; assumption.

 intros dj.
 rewrite I_add_wn_i_comm_l.
 apply Hs1.
Qed.

Theorem carry_add_comm_l : ∀ x y z i,
   carry (I_add_wn (x + y) z) i = carry (I_add_wn (y + x) z) i.
Proof.
intros x y z i.
unfold carry; simpl.
rewrite fst_not_1_add_comm_l.
remember (fst_not_1 (I_add_wn (y + x) z) i) as s1 eqn:Hs1 .
destruct s1 as [di1| ]; [ idtac | reflexivity ].
apply I_add_wn_i_comm_l.
Qed.

Theorem fst_not_1_add_wm_eqs_compat : ∀ x y z i,
  I_eqs x y
  → fst_not_1 (I_add_wn x z) i = fst_not_1 (I_add_wn y z) i.
Proof.
intros x y z i Hxy.
unfold I_eqs in Hxy.
apply fst_not_1_iff; simpl.
remember (fst_not_1 (I_add_wn x z) i) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Ht1).
 split.
  intros dj Hdj.
  unfold I_add_wn_i; simpl.
  rewrite <- Hxy.
  apply Hn1; assumption.

  unfold I_add_wn_i.
  rewrite <- Hxy; assumption.

 intros dj.
 unfold I_add_wn_i.
 rewrite <- Hxy; apply Hs1.
Qed.

Theorem I_eqs_eq : ∀ x y, I_eqs x y → (x = y)%I.
Proof.
intros x y Hxy.
unfold I_eqs in Hxy; simpl in Hxy.
unfold I_eq; simpl; intros i.
unfold Iwn2I; simpl.
f_equal; f_equal.
 unfold I_add_wn_i.
 rewrite Hxy; reflexivity.

 unfold carry; simpl.
 erewrite fst_not_1_add_wm_eqs_compat; [ idtac | eassumption ].
 remember (fst_not_1 (I_add_wn y 0) (S i)) as s1 eqn:Hs1 .
 apply fst_not_1_iff in Hs1; simpl in Hs1.
 destruct s1 as [di1| ]; [ idtac | reflexivity ].
 destruct Hs1 as (Hn1, Ht1).
 unfold I_add_wn_i; simpl.
 rewrite Hxy; reflexivity.
Qed.

Theorem I_eqs_add_comm : ∀ x y, I_eqs (x + y) (y + x).
Proof.
intros x y.
unfold I_eqs; simpl; intros i.
unfold Iwn2I; simpl.
f_equal; f_equal; [ apply I_add_wn_i_comm | apply carry_add_comm ].
Qed.

Theorem I_add_comm : ∀ x y, (x + y = y + x)%I.
Proof.
intros x y.
apply I_eqs_eq, I_eqs_add_comm.
Qed.

Close Scope nat_scope.
