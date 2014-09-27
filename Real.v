Require Import Utf8 QArith NPeano.

Set Implicit Arguments.

Open Scope nat_scope.

(* reals modulo 1 *)
Record real_mod_1 := { rm : nat → bool }.

Delimit Scope rm_scope with rm.
Arguments rm r%rm i%nat.
Notation "s .[ i ]" := (rm s i) (at level 1).

Axiom fst_same : real_mod_1 → real_mod_1 → nat → option nat.

Axiom fst_same_iff : ∀ a b i odi,
  fst_same a b i = odi ↔
  match odi with
  | Some di =>
      (∀ dj, dj < di → rm a (i + dj) ≠ rm b (i + dj))
      ∧ rm a (i + di) = rm b (i + di)
  | None =>
      ∀ dj, rm a (i + dj) ≠ rm b (i + dj)
  end.

Arguments fst_same a%rm b%rm i%nat.

Definition rm_eq a b := ∀ i, rm a i = rm b i.

Notation "a = b" := (rm_eq a b) : rm_scope.
Notation "a ≠ b" := (¬ rm_eq a b) : rm_scope.

Definition rm_add_i a b i :=
  match fst_same a b i with
  | Some di =>
      (* a[i+di]=b[i+di] *)
      if zerop di then
        (* a[i]=b[i] *)
        match fst_same a b (S i) with
        | Some dj =>
            (* a[i+dj]=b[i+dj] *)
            xorb (rm a i) (rm a (S i + dj))
        | None =>
            false
        end
      else negb (rm a (i + di))
  | None =>
      true
  end.

Definition rm_add a b := {| rm := rm_add_i a b |}.

Notation "a + b" := (rm_add a b) : rm_scope.

Theorem fst_same_comm : ∀ a b i, fst_same a b i = fst_same b a i.
Proof.
intros a b i.
apply fst_same_iff.
remember (fst_same b a i) as sba eqn:Hsba .
symmetry in Hsba.
apply fst_same_iff in Hsba.
destruct sba as [di| ].
 destruct Hsba as (Hns, Hs).
 split; [ idtac | symmetry; assumption ].
 intros dj Hdjn.
 intros H; symmetry in H; revert H.
 apply Hns; assumption.

 intros dj H.
 symmetry in H; revert H.
 apply Hsba.
Qed.

Theorem rm_add_comm : ∀ a b, (a + b = b + a)%rm.
Proof.
intros a b.
unfold rm_eq; intros i; simpl.
unfold rm_add_i.
rewrite fst_same_comm.
remember (fst_same b a i) as sba eqn:Hsba .
symmetry in Hsba.
apply fst_same_iff in Hsba.
destruct sba as [di| ]; auto.
destruct Hsba as (Hns, Hs).
destruct (zerop di) as [H₁| H₁]; [ idtac | rewrite Hs; reflexivity ].
rewrite fst_same_comm.
remember (fst_same b a (S i)) as sbas eqn:Hsbas .
symmetry in Hsbas.
apply fst_same_iff in Hsbas.
destruct sbas as [dis| ]; auto.
destruct Hsbas as (Hnss, Hss).
subst di; rewrite Nat.add_0_r in Hs.
rewrite Hs; f_equal; symmetry; assumption.
Qed.

Theorem eq_fst_same : ∀ a b i,
  a .[ i] = b .[ i] → fst_same a b i = Some 0.
Proof.
intros a b i Hab.
apply fst_same_iff; simpl.
rewrite Nat.add_0_r; split; auto.
intros dj Hdj.
exfalso; revert Hdj; apply Nat.nlt_0_r.
Qed.

(*
Theorem fst_same_assoc : ∀ a b c i,
  fst_same a (b + c)%rm i = fst_same (a + b)%rm c i.
Proof.
intros a b c i.
apply fst_same_iff.
remember (fst_same (a + b) c i) as sab eqn:Hsab .
symmetry in Hsab.
apply fst_same_iff in Hsab.
destruct sab as [di| ].
 destruct Hsab as (Hne, Heq).
 split.
  intros dj Hdji.
bbb.
  destruct (bool_dec a .[ i + di] b .[ i + di]) as [H₁| H₁].
   remember a .[ i + di] as aidi eqn:H₂ .
   symmetry in H₁, H₂.
   destruct aidi.
    remember (i + di - 1) as i₁.
    assert (c .[ i₁] = xorb a .[ i₁] b .[ i₁]).
     destruct di; [ exfalso; revert Hdji; apply Nat.nlt_0_r | idtac ].
     rewrite Nat.add_succ_r in Heqi₁.
     rewrite Nat.sub_succ, Nat.sub_0_r in Heqi₁.
     subst i₁.
bbb.

intros a b c i.
apply fst_same_iff.
remember (fst_same (a + b) c i) as sab eqn:Hsab .
symmetry in Hsab.
apply fst_same_iff in Hsab.
destruct sab as [di| ].
 destruct Hsab as (Hne, Heq).
 split.
  intros dj Hdji.
  destruct (bool_dec a .[ i + di] b .[ i + di]) as [H₁| H₁].
   Focus 1.
   unfold rm_add, rm_add_i in Heq; simpl in Heq.
bbb.

intros a b c i.
apply fst_same_iff.
remember (fst_same (a + b) c i) as sab eqn:Hsab .
symmetry in Hsab.
apply fst_same_iff in Hsab.
destruct sab as [di| ].
 destruct Hsab as (Hne, Heq).
 split.
  intros dj Hdji.
  destruct (bool_dec a .[ i + di] b .[ i + di]) as [H₁| H₁].
   Focus 1.
bbb.

  remember Hdji as H; clear HeqH.
  apply Hne in H.
  unfold rm_add in Heq; simpl in Heq.
  unfold rm_add_i in Heq; simpl in Heq.
  remember (fst_same a b (i + di)) as aidi eqn:Haidi .
  symmetry in Haidi.
  apply fst_same_iff in Haidi.
  destruct aidi as [aidi| ].
   destruct Haidi as (Haidine, Haidieq).
   destruct (zerop aidi) as [H₁| H₁].
    subst aidi.
    clear Haidine.
    rewrite Nat.add_0_r in Haidieq.
    remember b .[ i + di] as bidi eqn:Hbidi .
    symmetry in Hbidi.
    destruct bidi.
     Focus 1.
bbb.
*)

Theorem rm_add_assoc : ∀ a b c, (a + (b + c) = (a + b) + c)%rm.
Proof.
intros a b c.
unfold rm_eq; intros i; simpl.
unfold rm_add_i.
remember (fst_same a (b + c) i) as sa eqn:Hsa .
symmetry in Hsa.
remember (fst_same (a + b) c i) as sc eqn:Hsc .
symmetry in Hsc.
apply fst_same_iff in Hsa.
apply fst_same_iff in Hsc.
destruct sa as [dia| ].
 destruct (zerop dia) as [H₁| H₁].
  subst dia.
  destruct Hsa as (_, Hsa).
  rewrite Nat.add_0_r in Hsa.
  destruct sc as [dic| ].
   destruct (zerop dic) as [H₁| H₁].
    subst dic.
    destruct Hsc as (_, Hsc).
    rewrite Nat.add_0_r in Hsc.
    remember (fst_same a (b + c) (S i)) as sas eqn:Hsas .
    symmetry in Hsas.
    remember (fst_same (a + b) c (S i)) as scs eqn:Hscs .
    symmetry in Hscs.
    apply fst_same_iff in Hsas.
    apply fst_same_iff in Hscs.
    destruct sas as [dias| ].
     destruct scs as [dics| ].
      destruct Hsas as (Hsan, Hsas).
      destruct Hscs as (Hscn, Hscs).
bbb.

Close Scope nat_scope.
