From Stdlib Require Import Utf8 Arith.
From Stdlib Require List.
Import List.ListNotations.
Open Scope list_scope.

Notation "x < y <= z" := (x < y ∧ y <= z) (at level 70, y at next level).
Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y < z" := (x <= y ∧ y < z)%nat (at level 70, y at next level).

Theorem Nat_le_neq_lt : ∀ a b, a ≤ b → a ≠ b → a < b.
Proof.
intros a b Hab Hnab.
apply le_lt_eq_dec in Hab.
now destruct Hab.
Qed.

Theorem Nat_eq_add_2 : ∀ a b, a + b = 2
  → a = 2 ∧ b = 0 ∨ a = 1 ∧ b = 1 ∨ a = 0 ∧ b = 2.
Proof.
intros * Hab.
destruct a; [ now right; right | ].
destruct a. {
  right; left.
  split; [ easy | ].
  change 2 with (1 + 1) in Hab.
  now apply Nat.add_cancel_l in Hab.
}
destruct a; [ | easy ].
left.
split; [ easy | ].
change 2 with (2 + 0) in Hab at 2.
now apply Nat.add_cancel_l in Hab.
Qed.

(*
Definition Nat_le_neq_lt₁ : ∀ a b, a ≤ b → a ≠ b → a < b :=
  λ (a b : nat) (Hab : a ≤ b) (Hnab : a ≠ b),
  match le_lt_eq_dec a b Hab with
  | left Hle => Hle
  | right Heq => match Hnab Heq with end
  end.
*)

Theorem list_Forall_inv : ∀ A (P : A → Prop) a l,
  List.Forall P (a :: l) → P a ∧ List.Forall P l.
Proof.
intros A P a l H.
now inversion H.
Qed.

(*
Definition list_Forall_inv₁ : ∀ A (P : A → Prop) a l,
  List.Forall P (a :: l) → P a ∧ List.Forall P l
:=
  λ _ P a l H,
  match H in (List.Forall _ l') return (l' = a :: l → P a ∧ List.Forall P l) with
  | List.Forall_nil _ => λ H1, match H1 with eq_refl => I end
  | List.Forall_cons _ px pl => λ H1, match H1 with eq_refl => conj px pl end
  end eq_refl.
*)

(*
Inductive myForall (A : Type) (P : A → Type) : list A → Type :=
    myForall_nil : myForall _ P []
  | myForall_cons : ∀ (x : A) (l : list A), P x → myForall _ P l → myForall _ P (x :: l).

Definition list_Forall_inv₁ : ∀ A (P : A → Type) a l,
  myForall _ P (a :: l) → P a * myForall _ P l
:=
  λ _ P a l H,
  match H with
  | myForall_cons _ _ _ _ px pl => (px, pl)
  end.
*)

Theorem last_cons_id : ∀ A (a : A) al,
  List.last al a ≠ a
  → List.last (a :: al) a ≠ a.
Proof.
intros * Hal.
now destruct al.
Qed.

(*
Definition last_cons_id₁ : ∀ A (a : A) al,
  List.last al a ≠ a
  → List.last (a :: al) a ≠ a
:=
  λ A (a : A) (al : list A),
  match al as l return (List.last l a ≠ a → List.last (a :: l) a ≠ a) with
  | [] => id
  | _ :: _ => id
  end.
*)

Theorem last_cons_cons : ∀ A (a b : A) al d,
  List.last (a :: b :: al) d = List.last (b :: al) d.
Proof. easy. Qed.

(*
Definition last_cons_cons₁ : ∀ A (a b : A) al d,
  List.last (a :: b :: al) d = List.last (b :: al) d
:=
  λ _ _ _ _ _, eq_refl.
*)

Theorem last_cons_ne : ∀ A (a d : A) al,
  a ≠ d
  → List.last al d ≠ d
  → List.last (a :: al) d ≠ d.
Proof.
intros * Had Hal.
revert a Had.
induction al as [| a1]; intros; [ easy | ].
rewrite last_cons_cons.
simpl in Hal.
destruct al as [| a2]; [ easy | ].
now rewrite last_cons_cons.
Qed.

Theorem List_cons_comm_app : ∀ A (x : A) l l', l ++ x :: l' = l ++ [x] ++ l'.
Proof. easy. Qed.

Theorem Nat_mod_add_same_l : ∀ a b, a ≠ 0 → (a + b) mod a = b mod a.
Proof.
intros * Ha.
rewrite <- Nat.Div0.add_mod_idemp_l.
now rewrite Nat.Div0.mod_same.
Qed.

Theorem Nat_mod_add_same_r : ∀ a b, b ≠ 0 → (a + b) mod b = a mod b.
Proof.
intros * Ha.
rewrite <- Nat.Div0.add_mod_idemp_r.
now rewrite Nat.Div0.mod_same, Nat.add_0_r.
Qed.

Theorem Nat_div_add_same_l : ∀ a b, a ≠ 0 → (a + b) / a = 1 + b / a.
Proof.
intros * Ha.
replace a with (1 * a) at 1 by apply Nat.mul_1_l.
rewrite Nat.add_comm.
rewrite Nat.div_add; [ apply Nat.add_comm | easy ].
Qed.

Theorem Nat_div_add_same_r : ∀ a b, b ≠ 0 → (a + b) / b = a / b + 1.
Proof.
intros * Ha.
replace b with (1 * b) at 1 by apply Nat.mul_1_l.
now rewrite Nat.div_add.
Qed.

Theorem Nat_le_add_l : ∀ a b, b ≤ a + b.
Proof.
intros.
replace b with (0 + b) at 1 by easy.
apply Nat.add_le_mono_r.
apply Nat.le_0_l.
Qed.

Theorem Nat_add_sub_diag : ∀ a b c, b = c → a + b - c = a.
Proof.
intros * Hbc; subst b.
apply Nat.add_sub.
Qed.

Theorem Nat_mul_le_pos_l : ∀ a b, 1 ≤ a → b ≤ a * b.
Proof.
intros * Ha.
replace b with (1 * b) at 1 by apply Nat.mul_1_l.
apply Nat.mul_le_mono_nonneg_r; [ apply Nat.le_0_l | easy ].
Qed.

Theorem Nat_mul_le_pos_r : ∀ a b, 1 ≤ b → a ≤ a * b.
Proof.
intros * Ha.
replace a with (a * 1) at 1 by apply Nat.mul_1_r.
apply Nat.mul_le_mono_nonneg_l; [ apply Nat.le_0_l | easy ].
Qed.

Theorem Nat_sqr_sub_1 : ∀ a, a ^ 2 - 1 = (a + 1) * (a - 1).
Proof.
intros; simpl.
rewrite Nat.mul_sub_distr_l.
do 2 rewrite Nat.mul_1_r.
rewrite Nat.mul_add_distr_r.
rewrite Nat.mul_1_l.
rewrite Nat.sub_add_distr.
now rewrite Nat.add_sub.
Qed.

Theorem Nat_sqr_sub_1_mod : ∀ a, (a ^ 2 - 1) mod a = a - 1.
Proof.
intros.
destruct (zerop a) as [Ha| Ha]; [ now subst a | ].
assert (Haz : a ≠ 0) by (now intros H; subst a).
rewrite Nat_sqr_sub_1.
rewrite <- Nat.Div0.mul_mod_idemp_l.
replace (a + 1) with (1 + 1 * a) by now rewrite Nat.mul_1_l, Nat.add_comm.
rewrite Nat.Div0.mod_add.
destruct a; [ easy | ].
rewrite Nat.sub_succ, Nat.sub_0_r.
destruct a; [ easy | ].
rewrite Nat.mod_1_l.
-rewrite Nat.mul_1_l.
 rewrite Nat.mod_small; [ easy | apply Nat.lt_succ_diag_r ].
-apply -> Nat.succ_lt_mono.
 apply Nat.lt_0_succ.
Qed.

Theorem Nat_sqr_sub_1_div : ∀ a, (a ^ 2 - 1) / a = a - 1.
Proof.
intros.
destruct (zerop a) as [Ha| Ha]; [ now subst a | ].
assert (Haz : a ≠ 0) by (now intros H; subst a).
specialize (Nat.div_mod (a ^ 2 - 1) a Haz) as H.
apply Nat.mul_cancel_r with (p := a); [ easy | ].
apply Nat.add_cancel_r with (p := (a ^ 2 - 1) mod a).
rewrite Nat.mul_comm in H.
rewrite <- H; simpl; rewrite Nat.mul_1_r.
rewrite <- Nat.pow_2_r.
rewrite Nat_sqr_sub_1_mod; simpl.
rewrite Nat.mul_1_r.
rewrite <- Nat.pow_2_r.
rewrite Nat_sqr_sub_1.
now rewrite Nat.mul_comm, Nat.mul_add_distr_l, Nat.mul_1_r.
Qed.

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

Theorem Nat_sub_sub_assoc : ∀ a b c,
  c ≤ b ≤ a + c
  → a - (b - c) = a + c - b.
Proof.
intros * (Hcb, Hba).
revert a c Hcb Hba.
induction b; intros.
-apply Nat.le_0_r in Hcb; subst c.
 now rewrite Nat.add_0_r.
-destruct c; [ now rewrite Nat.add_0_r | ].
 apply Nat.succ_le_mono in Hcb.
 rewrite Nat.add_succ_r in Hba.
 apply Nat.succ_le_mono in Hba.
 specialize (IHb a c Hcb Hba) as H1.
 rewrite Nat.sub_succ, H1.
 rewrite Nat.add_succ_r.
 now rewrite Nat.sub_succ.
Qed.

Theorem Nat_sub_sub_distr : ∀ a b c, c ≤ b ≤ a → a - (b - c) = a - b + c.
Proof.
intros.
rewrite <- Nat.add_sub_swap; [ | easy ].
apply Nat_sub_sub_assoc.
split; [ easy | ].
apply (Nat.le_trans _ a); [ easy | ].
apply Nat.le_add_r.
Qed.

Theorem Nat_mod_less_small : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a mod b = a - n * b.
Proof.
intros * Hab.
assert (Hb : b ≠ 0). {
  now intros Hb; rewrite Hb, (Nat.mul_comm (n + 1)) in Hab.
}
replace a with (a - n * b + n * b) at 1 by now apply Nat.sub_add.
rewrite Nat.Div0.mod_add.
apply Nat.mod_small.
apply Nat.add_lt_mono_r with (p := n * b).
rewrite Nat.add_comm in Hab; cbn in Hab.
now rewrite Nat.sub_add.
Qed.

Theorem Nat_div_less_small : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a / b = n.
Proof.
intros * Hab.
assert (Hb : b ≠ 0). {
  now intros Hb; rewrite Hb, (Nat.mul_comm (n + 1)) in Hab.
}
replace a with (a - n * b + n * b) at 1 by now apply Nat.sub_add.
rewrite Nat.div_add; [ | easy ].
replace n with (0 + n) at 3 by easy; f_equal.
apply Nat.div_small.
apply Nat.add_lt_mono_r with (p := n * b).
rewrite Nat.add_comm in Hab; cbn in Hab.
now rewrite Nat.sub_add.
Qed.

Theorem Nat_div_add_div : ∀ a b c,
  b mod c < c - a
  → (a + b) / c = b / c.
Proof.
intros * Hb.
destruct c; [ easy | ].
specialize (Nat.div_mod b (S c) (Nat.neq_succ_0 c)) as H1.
rewrite H1.
rewrite Nat.add_comm, Nat.mul_comm, <- Nat.add_assoc.
rewrite Nat.div_add_l; [ | easy ].
rewrite Nat.div_add_l; [ | easy ].
f_equal.
rewrite Nat.div_small.
rewrite Nat.div_small; [ easy | ].
-now apply Nat.mod_upper_bound.
-now apply Nat.lt_add_lt_sub_r.
Qed.

Theorem Nat_gcd_le_l : ∀ a b, a ≠ 0 → Nat.gcd a b ≤ a.
Proof.
intros * Ha.
specialize (Nat.gcd_divide_l a b) as (c, Hc).
rewrite <- Nat.mul_1_l at 1.
rewrite Hc at 2.
apply Nat.mul_le_mono_pos_r.
-apply Nat.neq_0_lt_0.
 intros H.
 now apply Nat.gcd_eq_0_l in H.
-destruct c; [ easy | ].
 apply -> Nat.succ_le_mono.
 apply Nat.le_0_l.
Qed.

Theorem Nat_gcd_le_r : ∀ a b, b ≠ 0 → Nat.gcd a b ≤ b.
Proof.
intros * Hb.
rewrite Nat.gcd_comm.
now apply Nat_gcd_le_l.
Qed.

Theorem Nat_gcd_add_diag_l : ∀ n m, Nat.gcd (m + n) n = Nat.gcd m n.
Proof.
intros.
rewrite Nat.gcd_comm.
rewrite Nat.gcd_add_diag_r.
apply Nat.gcd_comm.
Qed.

Theorem Nat_gcd_sub_diag_l : ∀ n m, n ≤ m → Nat.gcd (m - n) n = Nat.gcd m n.
Proof.
intros * Hnm.
replace m with (m - n + n) at 2; [ | now apply Nat.sub_add ].
symmetry; apply Nat_gcd_add_diag_l.
Qed.

Theorem Nat_eq_mul_diag : ∀ p n, p = n * p → p = 0 ∨ n = 1.
Proof.
intros * H.
destruct n; [ now left | ].
destruct p; [ now left | right ].
destruct n; [ easy | exfalso ].
cbn in H.
apply Nat.succ_inj in H.
symmetry in H.
specialize (Nat.eq_le_incl _ _ H) as H1.
apply Nat.le_add_le_sub_l in H1.
now rewrite Nat.sub_diag in H1.
Qed.

Theorem Nat_sub_lt_mono_l : ∀ n m p : nat, n < m ≤ p → p - m < p - n.
Proof.
intros * (Hnm, Hmp).
revert n m Hnm Hmp.
induction p; intros; [ now apply Nat.le_0_r in Hmp; subst m | ].
destruct (eq_nat_dec m (S p)) as [Hm| Hm].
-subst m; rewrite Nat.sub_diag.
 now apply Nat.lt_add_lt_sub_l; rewrite Nat.add_0_r.
-rewrite Nat.sub_succ_l; cycle 1. {
   apply Nat.nlt_ge; intros H; apply Hm.
   now apply Nat.le_antisymm.
 }
 rewrite Nat.sub_succ_l; cycle 1. {
   apply (Nat.le_trans _ m); [ now apply Nat.lt_le_incl | ].
   apply Nat.nlt_ge; intros H; apply Hm.
   now apply Nat.le_antisymm.
 }
 apply -> Nat.succ_lt_mono.
 apply IHp; [ easy | ].
 apply Nat.nlt_ge; intros H; apply Hm.
 now apply Nat.le_antisymm.
Qed.

Theorem Nat_div_interv : ∀ n a b,
  n * b ≤ a < (n + 1) * b
  → a / b = n.
Proof.
intros * Hn.
revert a b Hn.
induction n; intros.
-rewrite Nat.mul_0_l, Nat.mul_1_l in Hn.
 now apply Nat.div_small.
-specialize (IHn (a - b) b) as H1.
 assert (H : n * b ≤ a - b < (n + 1) * b). {
   destruct Hn as (H2, H3).
   assert (Hba : b ≤ a). {
     eapply Nat.le_trans; [ | apply H2 ].
     apply Nat.le_add_r.
   }
   split.
   -apply (Nat.add_le_mono_r _ _ b).
    replace (n * b + b) with (S n * b) by apply Nat.add_comm.
    rewrite Nat.sub_add; [ apply H2 | easy ].
   -apply (Nat.add_lt_mono_r _ _ b).
    rewrite Nat.sub_add; [ | easy ].
    rewrite Nat.add_1_r in H3; cbn in H3.
    rewrite Nat.add_1_r; cbn.
    now rewrite Nat.add_assoc, Nat.add_shuffle0 in H3.
 }
 specialize (H1 H); clear H.
 assert (H : b ≤ a). {
   apply (Nat.mul_le_mono_pos_l _ _ (S n)); [ apply Nat.lt_0_succ | ].
   eapply Nat.le_trans; [ apply Hn | apply Nat.le_add_r ].
 }
 destruct b.
 +now do 2 rewrite Nat.mul_0_r in Hn.
 +replace a with (S b + (a - S b)); cycle 1. {
    rewrite Nat.add_sub_assoc; [ | easy ].
    now rewrite Nat.add_comm, Nat.add_sub.
  }
  rewrite Nat_div_add_same_l; [ | easy ].
  rewrite Nat.add_1_l.
  now f_equal.
Qed.

Theorem Nat_sqr_sub : ∀ a b, b ≤ a → (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b.
Proof.
intros * Hba.
cbn.
do 3 rewrite Nat.mul_1_r.
rewrite Nat.add_0_r.
rewrite Nat.mul_sub_distr_l.
do 2 rewrite Nat.mul_sub_distr_r.
rewrite Nat.mul_add_distr_r.
rewrite Nat_sub_sub_swap.
rewrite Nat_sub_sub_assoc; cycle 1. {
  split; [ now apply Nat.mul_le_mono_r | ].
  apply (Nat.le_trans _ (a * a)).
  -now apply Nat.mul_le_mono_l.
  -apply Nat.le_add_r.
}
rewrite Nat.sub_add_distr.
now replace (b * a) with (a * b) by apply Nat.mul_comm.
Qed.

Theorem Nat_sqr_sub_sqr : ∀ a b, a ^ 2 - b ^ 2 = (a + b) * (a - b).
Proof.
intros.
rewrite Nat.mul_sub_distr_l.
do 2 rewrite Nat.mul_add_distr_r.
rewrite Nat.sub_add_distr.
replace (a * a) with (a ^ 2) by now cbn; rewrite Nat.mul_1_r.
rewrite Nat.mul_comm, Nat.add_sub.
now f_equal; cbn; rewrite Nat.mul_1_r.
Qed.

Theorem Nat_pow_ge_1 : ∀ a b, 0 < a → 1 ≤ a ^ b.
Proof.
intros * Ha.
induction b; [ easy | cbn ].
replace 1 with (1 * 1) by easy.
apply Nat.mul_le_mono_nonneg; [ | easy | apply Nat.le_0_1 | easy ].
apply Nat.le_0_1.
Qed.

Theorem Nat_pow_neq_0 : ∀ a b, a ≠ 0 → a ^ b ≠ 0.
Proof.
intros * Ha.
destruct a; [ easy | ].
now apply Nat.pow_nonzero.
Qed.

Theorem Nat_div_small_iff: ∀ a b : nat, b ≠ 0 → a < b ↔ a / b = 0.
Proof.
intros * Hb.
split; [ apply Nat.div_small | ].
intros Hab.
destruct b; [ easy | clear Hb ].
unfold "/" in Hab.
specialize (Nat.divmod_spec a b 0 b (Nat.le_refl _)) as H1.
remember (Nat.divmod a b 0 b) as d eqn:Hd.
symmetry in Hd.
destruct d as (d, m); cbn in Hab.
subst d.
rewrite Nat.mul_0_r, Nat.sub_diag in H1.
do 2 rewrite Nat.add_0_r in H1.
rewrite Nat.add_0_l in H1.
rewrite (proj1 H1).
apply -> Nat.succ_le_mono.
apply Nat.le_sub_l.
Qed.

Theorem Nat_mul_sub_div_le : ∀ a b c,
  c ≤ a * b
  → (a * b - c) / b ≤ a.
Proof.
intros * Hc.
destruct (zerop b) as [Hb| Hb]. {
  subst b; cbn; apply Nat.le_0_l.
}
apply Nat.neq_0_lt_0 in Hb.
remember (a * b - c) as d eqn:Hd.
assert (H1 : a = (c + d) / b). {
  rewrite Hd.
  rewrite Nat.add_sub_assoc; [ | easy ].
  rewrite Nat.add_comm, Nat.add_sub.
  now rewrite Nat.div_mul.
}
rewrite H1.
apply Nat.Div0.div_le_mono.
apply Nat_le_add_l.
Qed.

Definition bool_of_sumbool {A B : Prop} (P : sumbool A B) :=
  match P with
  | left _ _ => true
  | right _ _ => false
  end.
Definition sumbool_or {A B C D : Prop} (P : sumbool A B) (Q : sumbool C D) :=
  orb (bool_of_sumbool P) (bool_of_sumbool Q).

Notation "a ∨∨ b" := (sumbool_or a b) (at level 85, right associativity).
