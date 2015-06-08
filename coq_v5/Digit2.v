(* digits *)

Require Import Utf8 QArith NPeano.
Require Import Misc.

(*
Axiom proof_irrelevance : ∀ (P : Prop) (a b : P), a = b.
*)

Open Scope nat_scope.

Delimit Scope digit_scope with D.

Inductive radix_type := Rad : ∀ r, r ≥ 2 → radix_type.
Parameter rad : radix_type.
Definition radix := match rad with Rad r _ => r end.

Theorem radix_neq_0 : radix ≠ 0.
Proof.
intros Hr.
unfold radix in Hr.
destruct rad as (r, H).
subst r; apply Nat.nlt_ge in H.
apply H, Nat.lt_0_succ.
Qed.

Theorem pred_radix_neq_0 : pred radix ≠ 0.
Proof.
intros Hr.
unfold radix in Hr.
destruct rad as (r, H).
apply Nat.eq_pred_0 in Hr.
apply Nat.nle_gt in H; apply H.
destruct Hr; subst r; [ apply Nat.le_0_1 | reflexivity ].
Qed.

Theorem radix_gt_0 : 0 < radix.
Proof. apply neq_0_lt, Nat.neq_sym, radix_neq_0. Qed.

Theorem radix_gt_1 : 1 < radix.
Proof.
unfold radix; destruct rad.
eapply lt_le_trans; [ apply Nat.lt_1_2 | assumption ].
Qed.

Theorem radix_gt_8 : pred (pred radix) < radix.
Proof.
unfold radix; destruct rad as (r, Hr).
destruct r.
 exfalso; apply Nat.nlt_ge in Hr; apply Hr, Nat.lt_0_succ.

 apply lt_S_n; simpl.
 rewrite Nat.succ_pred.
  apply Nat.lt_lt_succ_r, Nat.lt_succ_r; reflexivity.

  intros H; subst r; apply Nat.nle_gt in Hr.
  apply Hr; reflexivity.
Qed.

Theorem radix_gt_9 : pred radix < radix.
Proof.
unfold radix; destruct rad as (r, Hr).
destruct r; [ idtac | apply Nat.lt_succ_r; reflexivity ].
exfalso; apply Nat.nlt_ge in Hr; apply Hr, Nat.lt_0_succ.
Qed.

Inductive digit := dig : ∀ k, k < radix → digit.
Definition digit_0 := (dig 0 radix_gt_0).
Definition digit_1 := (dig 1 radix_gt_1).
Definition digit_8 := (dig (pred (pred radix)) radix_gt_8).
Definition digit_9 := (dig (pred radix) radix_gt_9).

Notation "0" := digit_0 : digit_scope.
Notation "1" := digit_1 : digit_scope.
Notation "8" := digit_8 : digit_scope.
Notation "9" := digit_9 : digit_scope.

Definition digit_add x y :=
  match (x, y) with
  | (dig a _, dig b _) =>
      dig ((a + b) mod radix) (Nat.mod_upper_bound (a + b) radix radix_neq_0)
  end.

Theorem pred_radix_sub_lt : ∀ a, pred radix - a < radix.
Proof.
intros a.
eapply Nat.le_lt_trans; [ apply Nat.le_sub_l | apply radix_gt_9 ].
Qed.

Definition oppd x :=
  match x with
  | dig a Ha => dig (pred radix - a) (pred_radix_sub_lt a)
  end.

Notation "x + y" := (digit_add x y) : digit_scope.

(*
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
*)

Module Digit.

(*
Theorem pred_radix_lt_radix : pred radix < radix.
Proof.
pose proof (radix_ge_2 rad) as H.
unfold radix.
destruct (radix_value rad); [ idtac | apply Nat.lt_succ_diag_r ].
exfalso; apply Nat.nlt_ge in H; apply H, Nat.lt_0_succ.
Qed.

Theorem radix_neq_0 : radix ≠ 0.
Proof.
intros Hr.
unfold radix in Hr.
pose proof radix_ge_2 rad as H.
rewrite Hr in H.
apply Nat.nlt_ge in H.
apply H, Nat.lt_0_succ.
Qed.
*)

Theorem radix_neq_1 : radix ≠ 1.
Proof.
intros Hr.
unfold radix in Hr.
destruct rad as (r, H).
subst r; apply Nat.nlt_ge in H.
apply H, Nat.lt_1_2.
Qed.

(*
Theorem radix_gt_0 : 0 < radix.
Proof. apply neq_0_lt, Nat.neq_sym, radix_neq_0. Qed.

Theorem radix_gt_1 : 1 < radix.
Proof.
eapply lt_le_trans; [ apply Nat.lt_1_2 | idtac ].
apply radix_ge_2.
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
 as eq_equivalence.
*)

Theorem bbb : ∀ a : nat, a = a.
Proof.
intros a.
reflexivity.
Qed.

Print bbb.

Theorem glop : 0 = 1 → False.
Proof.
intros H.
change (match 1 with 0 => True | S _ => False end).
rewrite <- H.
constructor.
Qed.

Theorem aaa : ∀ p, p ≠ eq_refl tt → False.
Proof.
intros p H.
apply H.
destruct H.

change (match eq_refl nat with eq_refl => False end).
bbb.

change (match eq_refl 0 with eq_refl => False end).
change (match 1 with 0 => True | S _ => False end).
bbb.

Theorem aaa : ∀ p, p = eq_refl 0.
Proof.
intros p.

destruct (eq_nat_dec 0 1) as [H1| H1].
change (match 1 with 0 => True | S _ => p = eq_refl end).
rewrite <- H1; reflexivity.
bbb.

Theorem aaa : ∀ p, p = eq_refl tt.
Proof.
intros p.
change (match 0 with 0 => p = eq_refl | S _ => True end).

bbb.

(* parait que ça peut se démontrer...
   ça m'éviterait de devoir faire proof irrelevance *)
Theorem aaa : ∀ (a : nat) p, p = eq_refl a.
Proof.
intros a p.
Unset Printing Notations. Show.
change (match p with eq_refl => eq_refl end) in p.
bbb.

Theorem nat_le_uniq_proof : ∀ a p, p = le_n a.
Proof.
intros a p.
Abort.

Theorem nat_le_uniq_proof : ∀ a b (p q : a ≤ b), p = q.
Proof.
intros a b p q.
bbb.

Theorem eq_dig_eq : ∀ a b pa pb, a = b → dig a pa = dig b pb.
Proof.
intros a b pa pb Hab.
subst a; f_equal.
unfold lt in pa, pb.
bbb.

revert pa pb.
destruct (eq_nat_dec (S b) radix) as [H1| H1].
Focus 2.
 destruct pa as [|n]; [ exfalso; apply H1; reflexivity | idtac ].
 intros pb.

unfold lt in pa, pb.

apply proof_irrelevance.
Qed.

Theorem eq_dec : ∀ x y : digit, {x = y} + {x ≠ y}.
Proof.
intros x y.
destruct x as (a, Ha).
destruct y as (b, Hb).
destruct (eq_nat_dec a b) as [H1| H1].
 left; apply eq_dig_eq; assumption.

 right; intros H; apply H1; clear H1.
 injection H; intros; assumption.
Qed.
Arguments eq_dec x%D y%D.

Theorem add_compat : ∀ x y z t,
  x = y
  → z = t
  → (x + z)%D = (y + t)%D.
Proof.
intros x y z t Hxy Hzt.
subst x z; reflexivity.
Qed.

(*
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
*)

Theorem add_comm : ∀ d e, (d + e = e + d)%D.
Proof.
intros d e.
destruct d as (d, Hd).
destruct e as (e, He).
unfold digit_add; simpl.
rewrite Nat.add_comm; reflexivity.
Qed.

Theorem add_0_r : ∀ d, (d + 0 = d)%D.
Proof.
intros d.
unfold digit_add.
destruct d as (d, Hd); simpl.
rewrite Nat.add_0_r.
apply eq_dig_eq.
apply Nat.mod_small; assumption.
Qed.

Theorem add_0_l : ∀ d, (0 + d = d)%D.
Proof.
intros d.
rewrite add_comm.
apply add_0_r.
Qed.

Theorem neq_0_9 : (0 ≠ 9)%D.
Proof.
unfold digit_0, digit_9.
intros Heq; injection Heq; intros H.
symmetry in H; revert H; apply pred_radix_neq_0.
Qed.

Theorem neq_9_0 : (9 ≠ 0)%D.
Proof. intros H; symmetry in H; revert H; apply neq_0_9. Qed.

Theorem neq_0_1 : (0 ≠ 1)%D.
Proof. intros Heq; discriminate Heq. Qed.

Theorem opp_0_iff : ∀ d, (oppd d = 0)%D ↔ (d = 9)%D.
Proof.
intros d.
split; intros H1.
 destruct d as (d, Hd); simpl in H1.
 unfold digit_9; simpl.
 apply eq_dig_eq.
 injection H1; intros H.
 apply Nat.sub_0_le in H.
 apply Nat.le_antisymm; [ idtac | assumption ].
 apply Nat.succ_le_mono.
 rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].

 subst d; simpl.
 unfold digit_0; simpl.
 apply eq_dig_eq, Nat.sub_diag.
Qed.

Theorem opp_involutive : ∀ d, (oppd (oppd d) = d)%D.
Proof.
intros d.
unfold oppd.
destruct d as (d, Hd).
apply eq_dig_eq.
rewrite Nat_sub_sub_distr.
 rewrite Nat.add_comm; apply Nat.add_sub.

 apply Nat.succ_le_mono.
 rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].
Qed.

Theorem opp_1_iff : ∀ d, (oppd d = 9)%D ↔ (d = 0)%D.
Proof.
intros d.
split; intros H1.
 unfold digit_0.
 destruct d as (d, Hd).
 apply eq_dig_eq.
 unfold oppd, digit_9 in H1.
 injection H1; intros H.
 symmetry in H.
 apply Nat_le_sub_add_r in H.
  rewrite Nat.add_comm in H.
  apply plus_minus in H.
  rewrite Nat.sub_diag in H; assumption.

  apply Nat.succ_le_mono.
  rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].

 subst d; simpl.
 apply eq_dig_eq, Nat.sub_0_r.
Qed.

(*
Theorem neq_sym : ∀ d e, (d ≠ e)%D → (e ≠ d)%D.
Proof.
intros d e Hde.
intros H; apply Hde.
symmetry; assumption.
Qed.
*)

Theorem add_assoc : ∀ d e f, (d + (e + f) = (d + e) + f)%D.
Proof.
intros d e f.
unfold digit_add, oppd.
destruct d as (d, Hd).
destruct e as (e, He).
destruct f as (f, Hf).
apply eq_dig_eq.
rewrite Nat.add_mod_idemp_l; [ idtac | apply radix_neq_0 ].
rewrite Nat.add_mod_idemp_r; [ idtac | apply radix_neq_0 ].
rewrite Nat.add_assoc; reflexivity.
Qed.

Theorem add_shuffle0 : ∀ d e f, (d + e + f = d + f + e)%D.
Proof.
intros d e f.
unfold digit_add.
destruct d as (d, Hd).
destruct e as (e, He).
destruct f as (f, Hf).
apply eq_dig_eq.
rewrite Nat.add_mod_idemp_l; [ idtac | apply radix_neq_0 ].
rewrite Nat.add_mod_idemp_l; [ idtac | apply radix_neq_0 ].
rewrite Nat.add_shuffle0; reflexivity.
Qed.

Theorem opp_0 : (oppd 0 = 9)%D.
Proof.
apply opp_1_iff; reflexivity.
Qed.

Theorem opp_9 : (oppd 9 = 0)%D.
Proof.
apply opp_0_iff; reflexivity.
Qed.

Theorem opp_add_diag_l : ∀ d, (oppd d + d = 9)%D.
Proof.
intros d.
unfold digit_add, oppd, digit_9.
destruct d as (d, Hd).
apply eq_dig_eq.
rewrite Nat.sub_add; [ apply Nat_pred_mod | idtac ].
apply Nat.succ_le_mono.
rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].
Qed.

Theorem opp_add_diag_r : ∀ d, (d + oppd d = 9)%D.
Proof.
intros d.
rewrite add_comm.
apply opp_add_diag_l.
Qed.

Theorem opp_sym : ∀ d d', (d' = oppd d)%D → (d = oppd d')%D.
Proof.
intros d d' Hd'.
symmetry; rewrite <- opp_involutive.
subst d'; reflexivity.
Qed.

Theorem opp_eq : ∀ d e, (oppd d = oppd e)%D → (d = e)%D.
Proof.
intros d e Hde.
rewrite <- opp_involutive, <- Hde.
symmetry; apply opp_involutive.
Qed.

Theorem opp_add : ∀ d e, (oppd (d + e) = oppd d + oppd e + 1)%D.
Proof.
intros d e.
unfold oppd, digit_add, digit_1; simpl.
destruct d as (d, Hd).
destruct e as (e, He).
apply eq_dig_eq.
rewrite Nat.add_mod_idemp_l; [ idtac | apply radix_neq_0 ].
destruct (lt_dec (d + e) radix) as [H1| H1].
 rewrite Nat.mod_small; [ idtac | assumption ].
 rewrite Nat.add_sub_assoc.
  rewrite Nat.add_sub_swap.
   rewrite <- Nat.sub_add_distr.
   rewrite <- Nat.add_assoc, Nat.add_1_r.
   rewrite Nat.succ_pred; [ idtac | apply radix_neq_0 ].
   rewrite Nat_mod_add_once; [ idtac | apply radix_neq_0 ].
   rewrite Nat.mod_small; [ reflexivity | idtac ].
   unfold lt.
   rewrite <- Nat.sub_succ_l.
    rewrite Nat.succ_pred; [ idtac | apply radix_neq_0 ].
    apply Nat.le_sub_le_add_r.
    rewrite Nat.add_comm.
    apply Nat.le_sub_le_add_r.
    rewrite Nat.sub_diag.
    apply Nat.le_0_l.

    apply Nat.succ_le_mono.
    rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].

   apply Nat.le_add_le_sub_l, Nat.succ_le_mono.
   rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].

  apply Nat.succ_le_mono.
  rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].

 apply Nat.nlt_ge in H1.
 rewrite Nat.add_sub_assoc.
  rewrite <- Nat.add_sub_swap.
   rewrite <- Nat.add_assoc, Nat.add_1_r.
   rewrite <- Nat.add_sub_swap.
    rewrite Nat.succ_pred; [ idtac | apply radix_neq_0 ].
    rewrite <- Nat.sub_add_distr.
    remember (d + e - radix) as x eqn:Hx .
    generalize Hx; intros H.
    apply Nat_le_sub_add_r in H; [ idtac | assumption ].
    rewrite H, Nat.sub_add_distr, Nat.add_sub, Nat.add_comm.
    rewrite Nat_mod_add_once; [ idtac | apply radix_neq_0 ].
    rewrite Nat.mod_small.
     rewrite Nat.mod_small; [ reflexivity | idtac ].
     eapply Nat.le_lt_trans; [ idtac | apply radix_gt_9 ].
     apply Nat.le_sub_le_add_r, Nat.le_sub_le_add_l.
     rewrite Nat.sub_diag; apply Nat.le_0_l.

     rewrite Hx.
     eapply Nat_lt_add_sub_lt_l.
      apply Nat.add_lt_mono; assumption.

      apply le_n_S; assumption.

    apply Nat.succ_le_mono.
    rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].

   rewrite <- Nat.add_sub_swap.
    apply Nat.le_add_le_sub_r.
    apply Nat.add_le_mono.
     apply Nat.succ_le_mono.
     rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].

     apply Nat.succ_le_mono.
     rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].

    apply Nat.succ_le_mono.
    rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].

  apply Nat.succ_le_mono.
  rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].
Qed.

Theorem add_cancel_lt_lt : ∀ d e f,
  d < radix
  → e < radix
  → f < radix
  → d + e = (d + f) mod radix
  → d + e < radix
  → d + f < radix.
Proof.
intros d e f Hdr Her Hfr H1 H2.
apply Nat.nle_gt; intros H3.
assert (f = e + radix) as H.
 remember (d + f - radix) as x eqn:Hx .
 generalize Hx; intros H.
 apply Nat_le_sub_add_r in H; [ idtac | assumption ].
 apply Nat.add_cancel_l with (p := d).
 rewrite Nat.add_assoc, H1, H, Nat.add_comm.
 apply Nat.add_cancel_r; symmetry.
 rewrite Nat.add_mod; [ idtac | apply radix_neq_0 ].
 rewrite Nat.mod_same; [ rewrite Nat.add_0_r | apply radix_neq_0 ].
 rewrite Nat.mod_mod; [ idtac | apply radix_neq_0 ].
 apply Nat.mod_small; rewrite Hx.
 eapply Nat_lt_add_sub_lt_r; [ idtac | apply radix_gt_0 ].
 apply Nat.add_lt_mono; assumption.

 rewrite H in Hfr.
 apply Nat.lt_add_lt_sub_r in Hfr.
 rewrite Nat.sub_diag in Hfr.
 revert Hfr; apply Nat.nlt_0_r.
Qed.

Theorem add_cancel_l : ∀ d e f, (d + e = d + f)%D → (e = f)%D.
Proof.
intros d e f Hdef.
unfold digit_add, oppd in Hdef.
destruct d as (d, Hd).
destruct e as (e, He).
destruct f as (f, Hf).
injection Hdef; intros H.
apply eq_dig_eq.
destruct (lt_dec (d + e) radix) as [H1| H1].
 rewrite Nat.mod_small in H; [ idtac | assumption ].
 destruct (lt_dec (d + f) radix) as [H2| H2].
  rewrite Nat.mod_small in H; [ idtac | assumption ].
  apply Nat.add_cancel_l in H; assumption.

  exfalso; apply H2.
  eapply add_cancel_lt_lt with (e := e); eassumption.

 destruct (lt_dec (d + f) radix) as [H2| H2].
  symmetry in H.
  rewrite Nat.mod_small in H; [ idtac | assumption ].
  exfalso; apply H1.
  eapply add_cancel_lt_lt with (e := f); eassumption.

  apply Nat.nlt_ge in H1.
  apply Nat.nlt_ge in H2.
  remember (d + e - radix) as x eqn:Hx.
  remember (d + f - radix) as y eqn:Hy.
  rename H into H3.
  generalize Hx; intros H.
  apply Nat_le_sub_add_r in H; [ idtac | assumption ].
  rewrite H in H3; clear H.
  generalize Hy; intros H.
  apply Nat_le_sub_add_r in H; [ idtac | assumption ].
  rewrite H in H3; clear H.
  rewrite Nat.add_mod in H3; symmetry in H3; [ idtac | apply radix_neq_0 ].
  rewrite Nat.add_mod in H3; symmetry in H3; [ idtac | apply radix_neq_0 ].
  rewrite Nat.mod_same in H3; [ simpl in H3 | apply radix_neq_0 ].
  rewrite Nat.mod_mod in H3; [ idtac | apply radix_neq_0 ].
  rewrite Nat.mod_mod in H3; [ idtac | apply radix_neq_0 ].
  rewrite Nat.mod_small in H3.
   rewrite Nat.mod_small in H3.
    subst y; rewrite Hy in Hx.
    apply Nat_le_sub_add_r in Hx; [ idtac | assumption ].
    rewrite Nat.add_sub_assoc in Hx; [ idtac | assumption ].
    symmetry in Hx.
    rewrite Nat.add_comm, Nat.add_sub in Hx.
    symmetry in Hx.
    apply Nat.add_cancel_l in Hx.
    assumption.

    rewrite Hy.
    eapply Nat_lt_add_sub_lt_r; [ idtac | apply radix_gt_0 ].
    apply Nat.add_lt_mono; assumption.

   rewrite Hx.
   eapply Nat_lt_add_sub_lt_r; [ idtac | apply radix_gt_0 ].
   apply Nat.add_lt_mono; assumption.
Qed.

Theorem add_cancel_r : ∀ d e f, (d + f = e + f)%D → (d = e)%D.
Proof.
intros d e f Hd.
rewrite add_comm in Hd; symmetry in Hd.
rewrite add_comm in Hd; symmetry in Hd.
apply add_cancel_l in Hd; assumption.
Qed.

Theorem add_1_9 : (1 + 9 = 0)%D.
Proof.
unfold digit_1, digit_9, digit_0, digit_add; simpl.
apply eq_dig_eq.
rewrite Nat.succ_pred; [ idtac | apply radix_neq_0 ].
rewrite Nat.mod_same; [ reflexivity | apply radix_neq_0 ].
Qed.

End Digit.

(*
Theorem eq_digit_eq : ∀ d e, d = e → (d = e)%D.
Proof. intros d e H; subst d; reflexivity. Qed.
*)

(*
Ltac discr_digit H :=
  exfalso; revert x; try apply Digit.neq_1_0; apply Digit.neq_0_1.
*)

(*
Definition d2n d := dig d mod radix.
Definition n2d n := {| dig := n |}.
*)
Definition d2n d :=
  match d with
  | dig a _ => a
  end.
Definition n2d n :=
  dig (n mod radix) (Nat.mod_upper_bound n radix radix_neq_0).
Arguments d2n d%D.
Arguments n2d n%nat.

Theorem d2n_0 : d2n 0 = 0.
Proof. reflexivity. Qed.

Theorem d2n_1 : d2n 1 = 1.
Proof. reflexivity. Qed.

Theorem d2n_9 : d2n 9 = pred radix.
Proof. reflexivity. Qed.

Theorem eq_d2n_0 : ∀ b, d2n b = 0 ↔ (b = 0)%D.
Proof.
intros b.
split; intros Hb.
 unfold d2n in Hb.
 destruct b as (b, H); subst b.
 apply Digit.eq_dig_eq; reflexivity.

 destruct b as (b, H).
 rewrite Hb; reflexivity.
Qed.

Theorem eq_d2n_1 : ∀ b, d2n b = 1 ↔ (b = 1)%D.
Proof.
intros b.
split; intros Hb.
 unfold d2n in Hb.
 destruct b as (b, H); subst b.
 apply Digit.eq_dig_eq; reflexivity.

 destruct b as (b, H).
 rewrite Hb; reflexivity.
Qed.

Theorem le_d2n_9 : ∀ b, d2n b ≤ pred radix.
Proof.
intros b.
unfold d2n.
destruct b as (b, Hb).
apply le_S_n.
rewrite Nat.succ_pred; [ assumption | apply radix_neq_0 ].
Qed.

Theorem n2d_eq : ∀ a b, a = b → (n2d a = n2d b)%D.
Proof. intros; subst; reflexivity. Qed.

Theorem digit_d2n_eq_iff : ∀ d e, (d = e)%D ↔ d2n d = d2n e.
Proof.
intros d e.
split; intros; [ subst; reflexivity | idtac ].
destruct d as (d, Hd).
destruct e as (e, He).
apply Digit.eq_dig_eq; assumption.
Qed.

Theorem d2n_lt_radix : ∀ d, d2n d < radix.
Proof.
intros d.
destruct d; assumption.
Qed.

Theorem d2n_n2d : ∀ n, d2n (n2d n) = n mod radix.
Proof. intros n; reflexivity. Qed.

Theorem n2d_d2n : ∀ d, (n2d (d2n d) = d)%D.
Proof.
intros d.
unfold n2d, d2n; simpl.
destruct d as (d, Hd).
apply Digit.eq_dig_eq, Nat.mod_small; assumption.
Qed.

Theorem d2n_mod_radix : ∀ d, d2n d mod radix = d2n d.
Proof.
intros d; unfold d2n.
destruct d as (d, Hd).
apply Nat.mod_small; assumption.
Qed.

Theorem sqr_radix_neq_0 : radix * radix ≠ 0.
Proof.
intros H.
apply Nat.eq_mul_0 in H.
destruct H; revert H; apply radix_neq_0.
Qed.

Theorem sqr_radix_gt_0 : radix * radix > 0.
Proof. apply neq_0_lt, Nat.neq_sym, sqr_radix_neq_0. Qed.
