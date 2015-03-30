(* digits *)

Require Import Utf8 QArith NPeano.

Open Scope nat_scope.

Delimit Scope digit_scope with D.

Record radix_type := { radix_value : nat; radix_ge_2 : radix_value ≥ 2 }.
Parameter rad : radix_type.
Definition radix := radix_value rad.

Record digit := { dig : nat }.
Definition digit_0 := {| dig := 0 |}.
Definition digit_rm1 := {| dig := pred radix |}.
Definition digit_eq x y := dig x mod radix = dig y mod radix.
Arguments dig d%D.
Arguments digit_eq x%D y%D.

Notation "0" := digit_0 : digit_scope.
Notation "9" := digit_rm1 : digit_scope.
Notation "x = y" := (digit_eq x y) : digit_scope.
Notation "x ≠ y" := (¬digit_eq x y) : digit_scope.

Definition digit_add x y := {| dig := dig x + dig y |}.
Definition oppd x := {| dig := pred radix - dig x mod radix |}.

Notation "x + y" := (digit_add x y) : digit_scope.

Module Digit.

Theorem radix_neq_0 : radix ≠ 0.
Proof.
intros Hr.
unfold radix in Hr.
pose proof radix_ge_2 rad as H.
rewrite Hr in H.
apply Nat.nlt_ge in H.
apply H, Nat.lt_0_succ.
Qed.

Theorem eq_refl : reflexive digit digit_eq.
Proof. intros d; reflexivity. Qed.

Theorem eq_sym : symmetric digit digit_eq.
Proof. intros x y Hxy; symmetry; assumption. Qed.

Theorem eq_trans : transitive digit digit_eq.
Proof. intros x y z Hxy Hyz; etransitivity; eassumption. Qed.

Add Parametric Relation : digit digit_eq
 reflexivity proved by eq_refl
 symmetry proved by eq_sym
 transitivity proved by eq_trans
 as eq_rel.

Theorem eq_dec : ∀ x y, {(x = y)%D} + {(x ≠ y)%D}.
Proof. intros x y; apply Nat.eq_dec. Qed.
Arguments eq_dec x%D y%D.

Ltac fsimpl_in H :=
  remember minus as fminus;
  remember div as fdiv;
  remember modulo as fmod;
  simpl in H; subst fminus fdiv fmod.

Ltac fsimpl :=
  remember minus as fminus;
  remember div as fdiv;
  remember modulo as fmod;
  simpl; subst fminus fdiv fmod.

Add Parametric Morphism : digit_add
  with signature digit_eq ==> digit_eq ==> digit_eq
  as add_compat.
Proof.
intros x y Hxy z t Hzt.
unfold digit_eq in Hxy, Hzt.
unfold digit_eq, digit_add; fsimpl.
rewrite Nat.add_mod; [ rewrite Hxy, Hzt | apply radix_neq_0 ].
rewrite <- Nat.add_mod; [ reflexivity | apply radix_neq_0 ].
Qed.

Add Parametric Morphism : oppd
  with signature digit_eq ==> digit_eq
  as opp_compat.
Proof.
intros x y Hxy.
unfold digit_eq in Hxy; unfold digit_eq, oppd.
rewrite Hxy; reflexivity.
Qed.

Theorem add_comm : ∀ d e, (d + e = e + d)%D.
Proof.
intros d e.
unfold digit_eq, digit_add, oppd; fsimpl.
rewrite Nat.add_comm; reflexivity.
Qed.

Theorem add_0_r : ∀ d, (d + 0 = d)%D.
Proof.
intros d.
unfold digit_eq, digit_add; fsimpl.
rewrite Nat.add_0_r; reflexivity.
Qed.

Theorem add_0_l : ∀ d, (0 + d = d)%D.
Proof.
intros d.
rewrite add_comm.
apply add_0_r.
Qed.

(*
Theorem add_1_r : ∀ d, (d + 1 = oppd d)%D.
Proof.
intros d.
unfold digit_eq, digit_add, oppd; fsimpl.
destruct (eq_nat_dec (dig d) 0) as [H1| H1]; simpl.
 right; split; intros H; discriminate H.

 left; split; reflexivity.
Qed.

Theorem add_1_l : ∀ d, (1 + d = oppd d)%D.
Proof.
intros d.
rewrite add_comm.
apply add_1_r.
Qed.
*)

Theorem Nat_mod_succ_diag_r_eq_0 : ∀ a, a mod S a = 0 → a = 0.
Proof.
intros a Ha.
apply Nat.mod_divides in Ha; [ idtac | intros H; discriminate H ].
destruct Ha as (c, Hc).
rewrite Nat.mul_comm in Hc.
destruct c; [ assumption | simpl in Hc ].
exfalso; revert Hc; rewrite Nat.add_comm.
apply Nat.succ_add_discr.
Qed.

Theorem neq_0_9 : (0 ≠ 9)%D.
Proof.
unfold digit_eq; simpl.
unfold radix; simpl; intros Hr.
pose proof radix_ge_2 rad as H.
remember (radix_value rad) as r; clear Heqr.
apply Nat.nlt_ge in H; apply H; clear H.
destruct r; [ apply Nat.lt_0_succ | apply lt_n_S, Nat.lt_1_r ].
fsimpl_in Hr; symmetry in Hr.
rewrite Nat.mod_0_l in Hr; [ idtac | intros H; discriminate H ].
apply Nat_mod_succ_diag_r_eq_0; assumption.
Qed.

Theorem neq_9_0 : (9 ≠ 0)%D.
Proof. intros H; symmetry in H; revert H; apply neq_0_9. Qed.

(*
Theorem not_0_iff_1 : ∀ d, (d ≠ 0)%D ↔ (d = 1)%D.
Proof.
intros d;
split; intros Hd.
 unfold digit_eq in Hd; unfold digit_eq.
 destruct (dig d); simpl.
  exfalso; apply Hd; left; split; reflexivity.

  right; split; intros H; discriminate H.

 intros H.
 rewrite Hd in H.
 revert H; apply neq_1_0.
Qed.

Theorem not_1_iff_0 : ∀ d, (d ≠ 1)%D ↔ (d = 0)%D.
Proof.
intros d;
split; intros Hd.
 unfold digit_eq in Hd; unfold digit_eq.
 destruct (dig d); simpl.
  left; split; reflexivity.

  exfalso; apply Hd; right; split; intros H; discriminate H.

 intros H.
 rewrite Hd in H.
 revert H; apply neq_0_1.
Qed.
*)

Theorem Nat_mod_succ : ∀ a, a mod S a = a.
Proof.
intros a.
rewrite Nat.mod_small; [ reflexivity | idtac ].
apply Nat.lt_succ_diag_r.
Qed.

Theorem Nat_pred_mod : ∀ a, pred a mod a = pred a.
Proof.
intros a.
destruct a; [ reflexivity | apply Nat_mod_succ ].
Qed.

Theorem Nat_pred_le_mod : ∀ a b, a ≠ 0 → pred a ≤ b mod a → b mod a = pred a.
Proof.
intros a b Ha H.
remember H as HH; clear HeqHH.
apply Nat.le_antisymm in H; [ assumption | idtac ].
apply Nat.mod_upper_bound with (a := b) in Ha.
apply Nat.lt_le_pred; assumption.
Qed.

Theorem opp_0_iff : ∀ d, (oppd d = 0)%D ↔ (d = 9)%D.
Proof.
intros d.
split; intros H1.
 unfold digit_eq in H1; fsimpl_in H1.
 unfold digit_eq; simpl.
 rewrite Nat.mod_0_l in H1; [ idtac | apply radix_neq_0 ].
 symmetry.
 rewrite Nat.mod_small; [ symmetry | apply Nat.lt_pred_l, radix_neq_0 ].
 apply Nat.mod_divides in H1; [ idtac | apply radix_neq_0 ].
 destruct H1 as (c, Hc); rewrite Nat.mul_comm in Hc.
 destruct c; simpl in Hc.
  apply Nat.sub_0_le in Hc.
  apply Nat_pred_le_mod in Hc; [ assumption | apply radix_neq_0 ].

  apply Nat.add_sub_eq_nz in Hc.
   rewrite Nat.add_comm in Hc.
   destruct radix; [ reflexivity | simpl in Hc ].
   rewrite <- Nat.add_1_r in Hc.
   do 2 rewrite <- Nat.add_assoc in Hc.
   apply Nat.add_sub_eq_l in Hc.
   rewrite Nat.sub_diag, Nat.add_assoc, Nat.add_1_r in Hc.
   discriminate Hc.

   intros H.
   apply Nat.eq_add_0 in H.
   destruct H as (H, _).
   revert H; apply radix_neq_0.

 unfold digit_eq in H1; fsimpl_in H1.
 unfold digit_eq; simpl.
 symmetry in H1.
 rewrite Nat.mod_small in H1; [ idtac | apply Nat.lt_pred_l, radix_neq_0 ].
 rewrite H1, Nat.sub_diag; reflexivity.
Qed.

Theorem opp_involutive : ∀ d, (oppd (oppd d) = d)%D.
Proof.
intros d.
unfold digit_eq, oppd; simpl.
rewrite Nat.mod_small.
 rewrite Nat.mod_small.
  apply Nat.add_sub_eq_r.
  rewrite Nat.add_sub_assoc.
   rewrite Nat.add_comm, Nat.add_sub; reflexivity.

   destruct radix; [ reflexivity | idtac ].
   apply le_S_n.
   apply Nat.mod_upper_bound.
   intros H; discriminate H.

  apply Nat.le_lt_trans with (m := pred radix).
   apply Nat.le_sub_le_add_r.
   apply Nat.le_sub_le_add_l.
   rewrite Nat.sub_diag.
   apply Nat.le_0_l.

   pose proof (radix_ge_2 rad) as H.
   unfold radix.
   destruct (radix_value rad); [ idtac | apply Nat.lt_succ_diag_r ].
   exfalso; apply Nat.nlt_ge in H; apply H, Nat.lt_0_succ.

 apply Nat.le_lt_trans with (m := pred radix).
  apply Nat.le_sub_le_add_r.
  apply Nat.le_sub_le_add_l.
  rewrite Nat.sub_diag.
  apply Nat.le_0_l.

  pose proof (radix_ge_2 rad) as H.
  unfold radix.
  destruct (radix_value rad); [ idtac | apply Nat.lt_succ_diag_r ].
  exfalso; apply Nat.nlt_ge in H; apply H, Nat.lt_0_succ.
Qed.

Theorem opp_1_iff : ∀ d, (oppd d = 9)%D ↔ (d = 0)%D.
Proof.
intros d.
split; intros H1.
 apply opp_compat in H1.
 rewrite opp_involutive in H1.
bbb.
unfold digit_eq, oppd; simpl.
split; intros H1.
Inspect 1.
SearchAbout oppd.
apply opp_compat.
bbb.

split; intros [(H1, H2)| (H1, H2)].
 discriminate H2.

 destruct (eq_nat_dec (dig d) 0) as [H3| H3].
  left; split; [ assumption | reflexivity ].

  exfalso; apply H1; reflexivity.

 destruct (eq_nat_dec (dig d) 0) as [H3| H3]; [ idtac | contradiction ].
 right; split; intros H; discriminate H.

 exfalso; apply H2; reflexivity.
Qed.
*)

Theorem neq_sym : ∀ d e, (d ≠ e)%D → (e ≠ d)%D.
Proof.
intros d e Hde.
intros H; apply Hde.
symmetry; assumption.
Qed.

Theorem add_assoc : ∀ d e f, (d + (e + f) = (d + e) + f)%D.
Proof.
intros d e f.
unfold digit_eq.
unfold digit_add, oppd; fsimpl.
rewrite Nat.add_assoc; reflexivity.
Qed.

Theorem add_shuffle0 : ∀ d e f, (d + e + f = d + f + e)%D.
Proof.
intros d e f.
do 2 rewrite <- add_assoc.
apply add_compat; [ reflexivity | idtac ].
apply add_comm.
Qed.

Theorem opp_0 : (oppd 0 = 9)%D.
Proof.
apply opp_1_iff; reflexivity.
Qed.

Theorem opp_1 : (oppd 1 = 0)%D.
Proof.
apply opp_0_iff; reflexivity.
Qed.

(*
Theorem add_nilpotent : ∀ d, (d + d = 0)%D.
Proof.
intros d.
unfold digit_eq, digit_add, oppd; simpl.
destruct (eq_nat_dec (dig d) 0) as [H1 | H1]; simpl.
 left; split; [ assumption | reflexivity ].

 left; split; reflexivity.
Qed.

Theorem eq_add_1 : ∀ d e, (d ≠ e)%D → (d + e = 1)%D.
Proof.
intros d e Hde.
unfold digit_eq, digit_add, oppd; simpl.
destruct (eq_nat_dec (dig d) 0) as [H1 | H1].
 right; split; [ idtac | intros H; discriminate H].
 intros H; apply Hde; unfold digit_eq.
 left; split; assumption.

 destruct (eq_nat_dec (dig e) 0) as [H2 | H2]; simpl.
  right; split; intros H; discriminate H.

  exfalso; apply Hde; unfold digit_eq.
  right; split; assumption.
Qed.
*)

Theorem opp_add_diag_l : ∀ d, (oppd d + d = radix - 1)%D.
Proof.
intros d.
bbb.
unfold digit_eq, digit_add, oppd; simpl.
destruct (eq_nat_dec (dig d) 0) as [H1| H1]; simpl.
 right; split; intros H; discriminate H.

 right; split; [ assumption | intros H; discriminate H ].
Qed.

Theorem opp_add_diag_r : ∀ d, (d + oppd d = 1)%D.
Proof.
intros d.
rewrite add_comm.
apply opp_add_diag_l.
Qed.

Theorem no_fixpoint_opp : ∀ d, (oppd d ≠ d)%D.
Proof.
intros d.
unfold digit_eq, oppd; simpl; intros H.
destruct H as [(Hx, Hy)| (Hx, Hy)].
 rewrite Hy in Hx; discriminate Hx.

 destruct (eq_nat_dec (dig d) 0) as [H1| H1]; [ contradiction | idtac ].
 apply Hx; reflexivity.
Qed.

Theorem neq_eq_opp : ∀ d e, (d ≠ e)%D ↔ (d = oppd e)%D.
Proof.
intros d e.
split; intros Hde.
 unfold digit_eq, digit_add, oppd; simpl.
 destruct (eq_nat_dec (dig e) 0) as [H1 | H1]; simpl.
  right; split; [ idtac | intros H; discriminate H ].
  intros H; apply Hde.
  unfold digit_eq, digit_add, oppd; simpl.
  left; split; assumption.

  left; split; [ idtac | reflexivity ].
  destruct (eq_nat_dec (dig d) 0) as [H2| H2]; [ assumption | idtac ].
  exfalso; apply Hde.
  unfold digit_eq, digit_add, oppd; simpl.
  right; split; assumption.

 intros H; rewrite Hde in H.
 exfalso; revert H; apply no_fixpoint_opp.
Qed.

Theorem opp_sym : ∀ d d', (d' = oppd d)%D → (d = oppd d')%D.
Proof.
intros d d' Hd'.
rewrite Hd'; unfold digit_eq, oppd; simpl.
destruct (eq_nat_dec (dig d) 0) as [H1 | H1]; simpl.
 left; split; [ assumption | reflexivity ].

 right; split; [ assumption | intros H; discriminate H ].
Qed.

Theorem opp_eq : ∀ d e, (oppd d = oppd e)%D → (d = e)%D.
Proof.
intros d e Hde.
unfold digit_eq, oppd in Hde; unfold digit_eq.
destruct (eq_nat_dec (dig d) 0) as [H1 | H1]; simpl in Hde; simpl.
 destruct (eq_nat_dec (dig e) 0) as [H2 | H2]; simpl in Hde; simpl.
  left; split; assumption.

  destruct Hde as [(Hd, He)|(Hd, He)]; [ discriminate Hd | idtac ].
  exfalso; apply He; reflexivity.

 destruct (eq_nat_dec (dig e) 0) as [H2 | H2]; simpl in Hde; simpl.
  destruct Hde as [(Hd, He)|(Hd, He)]; [ discriminate He | idtac ].
  exfalso; apply Hd; reflexivity.

  right; split; assumption.
Qed.

Theorem opp_add_r : ∀ d e, (oppd (d + e) = d + oppd e)%D.
Proof.
intros d e.
unfold digit_eq, digit_add, oppd; simpl.
destruct (eq_nat_dec (dig d) 0) as [H1 | H1]; simpl.
 destruct (eq_nat_dec (dig e) 0) as [H2 | H2]; simpl.
  right; split; intros H; discriminate H.

  left; split; reflexivity.

 destruct (eq_nat_dec (dig e) 0) as [H2 | H2]; simpl.
  left; split; reflexivity.

  right; split; intros H; discriminate H.
Qed.

Theorem opp_add_l : ∀ d e, (oppd (d + e) = oppd d + e)%D.
Proof.
intros d e.
rewrite add_comm; symmetry.
rewrite add_comm; symmetry.
apply opp_add_r.
Qed.

Theorem add_cancel_l : ∀ d e f, (d + e = d + f)%D → (e = f)%D.
Proof.
intros d e f Hd.
unfold digit_eq, digit_add, oppd in Hd; unfold digit_eq.
destruct (eq_nat_dec (dig d) 0) as [H1 | H1]; [ assumption | simpl ].
destruct (eq_nat_dec (dig e) 0) as [H2 | H2].
 destruct (eq_nat_dec (dig f) 0) as [H3 | H3]; simpl in Hd.
  left; split; assumption.

  destruct Hd as [(H4, H5)|(H4, H5)]; [ discriminate H4 | idtac ].
  exfalso; apply H5; reflexivity.

 destruct (eq_nat_dec (dig f) 0) as [H3 | H3]; simpl in Hd.
  destruct Hd as [(H4, H5)|(H4, H5)]; [ discriminate H5 | idtac ].
  exfalso; apply H4; reflexivity.

  right; split; assumption.
Qed.

Theorem add_cancel_r : ∀ d e f, (d + f = e + f)%D → (d = e)%D.
Proof.
intros d e f Hd.
rewrite add_comm in Hd; symmetry in Hd.
rewrite add_comm in Hd; symmetry in Hd.
apply add_cancel_l in Hd; assumption.
Qed.

Theorem move_l_r_1 : ∀ d e f, (d + e = f)%D → (e = d + f)%D.
Proof.
intros d e f Hd.
unfold digit_eq, digit_add, oppd in Hd.
unfold digit_eq, digit_add, oppd.
destruct (eq_nat_dec (dig d) 0) as [H1 | H1]; [ assumption | idtac ].
 destruct (eq_nat_dec (dig e) 0) as [H2 | H2]; simpl in Hd.
  destruct (eq_nat_dec (dig f) 0) as [H3 | H3]; simpl.
   destruct Hd as [(He, Hf)|(He, Hf)]; [ discriminate He | contradiction ].

   left; split; [ assumption | reflexivity ].

  destruct (eq_nat_dec (dig f) 0) as [H3 | H3]; simpl.
   right; split; [ assumption | intros H; discriminate H ].

   destruct Hd as [(He, Hf)|(He, Hf)]; [ contradiction | idtac ].
   exfalso; apply He; reflexivity.
Qed.

Theorem move_l_r_2 : ∀ d e f, (d + e = f)%D → (d = f + e)%D.
Proof.
intros d e f Hd.
unfold digit_eq, digit_add, oppd in Hd.
unfold digit_eq, digit_add, oppd.
destruct (eq_nat_dec (dig d) 0) as [H1| H1].
 destruct (eq_nat_dec (dig e) 0) as [H2| H2]; simpl in Hd.
  destruct (eq_nat_dec (dig f) 0) as [H3| H3]; simpl.
   left; split; assumption.

   destruct Hd as [(He, Hf)| (He, Hf)]; contradiction.

  destruct (eq_nat_dec (dig f) 0) as [H3| H3]; simpl.
   destruct Hd as [(He, Hf)| (He, Hf)]; contradiction.

   left; split; [ assumption | reflexivity ].

 destruct (eq_nat_dec (dig e) 0) as [H2| H2]; simpl in Hd.
  destruct (eq_nat_dec (dig f) 0) as [H3| H3]; simpl.
   destruct Hd as [(He, Hf)| (He, Hf)]; [ discriminate He | contradiction ].

   right; split; [ assumption | intros H; discriminate H ].

  destruct (eq_nat_dec (dig f) 0) as [H3| H3]; simpl.
   right; split; assumption.

   destruct Hd as [(He, Hf)| (He, Hf)]; [ contradiction | idtac ].
   exfalso; apply He; reflexivity.
Qed.

Theorem eq_add_0 : ∀ d e, (d + e = 0)%D → (d = e)%D.
Proof.
intros d e Hde.
unfold digit_eq, digit_add, oppd in Hde.
unfold digit_eq.
destruct (eq_nat_dec (dig d) 0) as [H1 | H1]; simpl in Hde.
 destruct Hde as [(He, Hd)|(He, Hd)].
  left; split; assumption.

  exfalso; apply Hd; reflexivity.

 destruct (eq_nat_dec (dig e) 0) as [H2 | H2]; simpl in Hde.
  destruct Hde as [(He, Hd)|(He, Hd)]; [ discriminate He | idtac ].
  exfalso; apply Hd; reflexivity.

  right; split; assumption.
Qed.

Theorem dec : ∀ x, {(x = 1)%D} + {(x = 0)%D}.
Proof.
intros x.
unfold digit_eq; simpl.
destruct (eq_nat_dec (dig x) 0) as [H1 | H1].
 right; left; split; [ assumption | reflexivity ].

 left; right; split; [ assumption | intros H; discriminate H ].
Qed.
Arguments dec x%D.

End Digit.

Theorem eq_digit_eq : ∀ d e, d = e → (d = e)%D.
Proof. intros d e H; subst d; reflexivity. Qed.

Ltac discr_digit x :=
  exfalso; revert x; try apply Digit.neq_1_0; apply Digit.neq_0_1.

Definition d2n d := dig d mod radix.
Definition n2d n := match n with 0 => 0%D | S n1 => 1%D end.
Arguments d2n d%D.
Arguments n2d n%nat.

Theorem d2n_0 : d2n 0 = 0.
Proof.
unfold d2n.
destruct (Digit.dec 0) as [H1| H1]; [ discr_digit H1 | reflexivity ].
Qed.

Theorem d2n_1 : d2n 1 = 1.
Proof.
unfold d2n.
destruct (Digit.dec 1) as [H1| H1]; [ reflexivity | discr_digit H1 ].
Qed.

Theorem eq_d2n_0 : ∀ b, d2n b = 0 ↔ (b = 0)%D.
Proof.
intros b.
split; intros Hb.
 unfold d2n in Hb.
 unfold digit_eq.
 left; split; [ idtac | reflexivity ].
bbb.
 destruct (Digit.dec b); [ discriminate Hb | assumption ].

 unfold d2n.
 destruct (Digit.dec b) as [H1| H1]; [ idtac | reflexivity ].
 rewrite Hb in H1; discr_digit H1.
Qed.

Theorem eq_d2n_1 : ∀ b, d2n b = 1 ↔ (b = 1)%D.
Proof.
intros b.
split; intros Hb.
 unfold d2n in Hb.
 destruct (Digit.dec b); [ assumption | discriminate Hb ].

 unfold d2n.
 destruct (Digit.dec b) as [H1| H1]; [ reflexivity | idtac ].
 rewrite Hb in H1; discr_digit H1.
Qed.

Theorem le_d2n_1 : ∀ b, d2n b ≤ 1.
Proof.
intros b.
unfold d2n.
destruct (Digit.dec b); [ reflexivity | apply Nat.le_0_l ].
Qed.

Theorem n2d_0_iff : ∀ n, (n2d n = 0)%D ↔ n = 0.
Proof.
intros n; split; intros Hn; [ idtac | subst n; reflexivity ].
unfold n2d in Hn.
destruct n; [ reflexivity | discr_digit Hn ].
Qed.

Theorem n2d_eq : ∀ a b, a = b → (n2d a = n2d b)%D.
Proof. intros; subst; reflexivity. Qed.

Theorem digit_d2n_eq_iff : ∀ d e, (d = e)%D ↔ d2n d = d2n e.
Proof.
intros d e.
split; intros Hde.
 unfold d2n.
 destruct (Digit.dec d) as [H1| H1].
  destruct (Digit.dec e) as [H2| H2]; [ reflexivity | exfalso ].
  rewrite H1, H2 in Hde; discr_digit Hde.

  destruct (Digit.dec e) as [H2| H2]; [ exfalso | reflexivity ].
  rewrite H1, H2 in Hde; discr_digit Hde.

 unfold d2n in Hde.
 destruct (Digit.dec d) as [H1| H1].
  destruct (Digit.dec e) as [H2| H2]; [ clear Hde | discriminate Hde ].
  rewrite H1, H2; reflexivity.

  destruct (Digit.dec e) as [H2| H2]; [ discriminate Hde | clear Hde ].
  rewrite H1, H2; reflexivity.
Qed.
