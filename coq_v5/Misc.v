Require Import Utf8 Arith NPeano.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y … l ]" := (cons x .. (cons y l) ..).
Notation "[ x ]" := (cons x nil).
Notation "x ∈ l" := (List.In x l) (at level 70).
Notation "x ∉ l" := (not (List.In x l)) (at level 70).

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y < z" := (x <= y ∧ y < z)%nat (at level 70, y at next level).

Theorem Nat_le_neq_lt : ∀ a b, a ≤ b → a ≠ b → a < b.
Proof.
intros a b Hab Hnab.
apply le_lt_eq_dec in Hab.
destruct Hab as [Hle| Heq]; [ assumption | idtac ].
exfalso; apply Hnab; assumption.
Qed.

Theorem Nat_sub_add_r : ∀ a b c,
  a < b
  → c = b - S a
  → b = a + S c.
Proof.
intros a b c Hab Hc; subst c.
rewrite <- Nat.sub_succ_l; [ simpl | assumption ].
rewrite Nat.add_sub_assoc; [ idtac | apply Nat.lt_le_incl; assumption ].
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Theorem Nat_sub_succ_1 : ∀ n, (S n - 1 = n).
Proof. intros n; simpl; rewrite Nat.sub_0_r; reflexivity. Qed.

Theorem Nat_sub_sub_distr :  ∀ a b c,
  c ≤ b
  → a - (b - c) = a + c - b.
Proof.
intros n m p Hpm.
rewrite Nat.add_comm.
revert n m Hpm.
induction p; intros.
 rewrite Nat.sub_0_r, Nat.add_0_l; reflexivity.

 destruct m as [| m].
  exfalso; revert Hpm; apply Nat.nle_succ_0.

  rewrite Nat.sub_succ; simpl.
  apply Nat.succ_le_mono in Hpm.
  apply IHp; assumption.
Qed.

Theorem Nat_sub_shuffle0 : ∀ a b c, a - b - c = a - c - b.
Proof.
intros a b c.
rewrite <- Nat.sub_add_distr, Nat.add_comm.
rewrite Nat.sub_add_distr; reflexivity.
Qed.

Theorem Nat_le_sub_add_r : ∀ a b c,
  a ≤ b
  → c = b - a
  → b = a + c.
Proof.
intros a b c Hab Hc; subst c.
rewrite Nat.add_sub_assoc; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

Theorem Nat_lt_add_sub_lt_r : ∀ a b c d,
  a < b + c
  → d < c
  → a - b < c.
Proof.
intros a b c d Ha Hdc.
revert b c Ha Hdc.
induction a; intros.
 simpl.
 eapply le_lt_trans; [ apply Nat.le_0_l | eassumption ].

 destruct b; [ rewrite Nat.sub_0_r; assumption | simpl ].
 simpl in Ha.
 apply Nat.succ_lt_mono in Ha.
 apply IHa; assumption.
Qed.

Theorem Nat_lt_add_sub_lt_l : ∀ a b c,
  a < b + c
  → b < S a
  → a - b < c.
Proof.
intros a b c Ha Hb.
revert b c Ha Hb.
induction a; intros.
 apply Nat.lt_1_r in Hb; subst b; assumption.

 destruct b; [ rewrite Nat.sub_0_r; assumption | simpl ].
 simpl in Ha.
 apply Nat.succ_lt_mono in Ha.
 apply Nat.succ_lt_mono in Hb.
 apply IHa; assumption.
Qed.

Theorem all_lt_all : ∀ P : nat → Prop,
  (∀ n, (∀ m, (m < n)%nat → P m) → P n)
  → ∀ n, P n.
Proof.
intros P Hm n.
apply Hm.
induction n; intros m Hmn.
 apply Nat.nle_gt in Hmn.
 exfalso; apply Hmn, Nat.le_0_l.

 destruct (eq_nat_dec m n) as [H1| H1].
  subst m; apply Hm; assumption.

  apply IHn.
  apply Nat_le_neq_lt; [ idtac | assumption ].
  apply Nat.succ_le_mono; assumption.
Qed.

Theorem Nat_add_mod_2 : ∀ a b, (a + b) mod 2 = 0 ↔ a mod 2 = b mod 2.
Proof.
intros a b.
split; intros Hab.
 rewrite Nat.add_mod in Hab; [ idtac | intros H; discriminate H ].
 remember (a mod 2) as aa eqn:Ha .
 remember (b mod 2) as bb eqn:Hb .
 symmetry in Ha, Hb.
 destruct aa, bb; try reflexivity.
  rewrite Nat.add_0_l, <- Hb in Hab.
  rewrite Nat.mod_mod in Hab; [ idtac | intros H; discriminate H ].
  rewrite Hb in Hab; discriminate Hab.

  rewrite Nat.add_0_r, <- Ha in Hab.
  rewrite Nat.mod_mod in Hab; [ idtac | intros H; discriminate H ].
  rewrite Ha in Hab; discriminate Hab.

  destruct aa.
   destruct bb; [ reflexivity | idtac ].
   assert (2 ≠ 0) as H by (intros H; discriminate H).
   apply Nat.mod_upper_bound with (a := b) in H.
   rewrite Hb in H.
   apply Nat.nlt_ge in H.
   exfalso; apply H.
   do 2 apply lt_n_S.
   apply Nat.lt_0_succ.

   assert (2 ≠ 0) as H by (intros H; discriminate H).
   apply Nat.mod_upper_bound with (a := a) in H.
   rewrite Ha in H.
   apply Nat.nlt_ge in H.
   exfalso; apply H.
   do 2 apply lt_n_S.
   apply Nat.lt_0_succ.

 rewrite Nat.add_mod; [ idtac | intros H; discriminate H ].
 rewrite Hab; clear a Hab.
 remember (b mod 2) as a; clear b Heqa.
 induction a; [ reflexivity | idtac ].
 rewrite <- Nat.add_1_r.
 rewrite Nat.add_shuffle0.
 do 2 rewrite <- Nat.add_assoc.
 rewrite Nat.add_assoc.
 rewrite Nat.add_mod; [ idtac | intros H; discriminate H ].
 rewrite IHa; reflexivity.
Qed.

Theorem divmod_div : ∀ a b, fst (divmod a b 0 b) = (a / S b)%nat.
Proof. intros a b; reflexivity. Qed.

Theorem divmod_mod : ∀ a b, b - snd (divmod a b 0 b) = (a mod S b)%nat.
Proof. intros a b; reflexivity. Qed.

Theorem fold_sub_succ_l : ∀ a b,
  (match a with 0 => S b | S c => b - c end = S b - a)%nat.
Proof. reflexivity. Qed.
