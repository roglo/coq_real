(* Implementation of rationals using only nat *)

Require Import Utf8 Arith Morphisms.
Require Import PQ.
Set Nested Proofs Allowed.

Delimit Scope MQ_scope with MQ.

Inductive MQ :=
  | MQ0 : MQ
  | MQpos : PQ → MQ
  | MQneg : PQ → MQ.
Arguments MQpos p%PQ.
Arguments MQneg p%PQ.

Notation "0" := (MQ0) : MQ_scope.
Notation "1" := (MQpos 1) : MQ_scope.

(* equality *)

Definition MQeq x y :=
  match x with
  | MQ0 => match y with MQ0 => True | _ => False end
  | MQpos px => match y with MQpos py => PQeq px py | _ => False end
  | MQneg px => match y with MQneg py => PQeq px py | _ => False end
  end.

Notation "x == y" := (MQeq x y) (at level 70) : MQ_scope.

Theorem MQeq_refl : ∀ x : MQ, (x == x)%MQ.
Proof. now intros; destruct x. Qed.

Theorem MQeq_symm : ∀ x y : MQ, (x == y)%MQ → (y == x)%MQ.
Proof.
unfold "=="%MQ.
intros * Hxy.
destruct x as [| px| px]; [ easy | now destruct y | now destruct y ].
Qed.

Theorem MQeq_trans : ∀ x y z : MQ, (x == y)%MQ → (y == z)%MQ → (x == z)%MQ.
Proof.
unfold "=="%MQ.
intros * Hxy Hyz.
destruct x, y, z; try easy; now transitivity p0.
Qed.

Add Parametric Relation : _ MQeq
 reflexivity proved by MQeq_refl
 symmetry proved by MQeq_symm
 transitivity proved by MQeq_trans
 as MQeq_equiv_rel.

(* allows to use rewrite inside a MQpos
   e.g.
      H : x = y
      ====================
      ... (MQpos x) ...
   rewrite H.
 *)
Instance MQpos_morph : Proper (PQeq ==> MQeq) MQpos.
Proof. easy. Qed.

(* allows to use rewrite inside a MQneg
   e.g.
      H : x = y
      ====================
      ... (MQneg x) ...
   rewrite H.
 *)
Instance MQneg_morph : Proper (PQeq ==> MQeq) MQneg.
Proof. easy. Qed.

(* comparison *)

Definition MQcompare x y :=
  match x with
  | MQ0 => match y with MQ0 => Eq | MQpos _ => Lt | MQneg _ => Gt end
  | MQpos px => match y with MQpos py => PQcompare px py | _ => Gt end
  | MQneg px => match y with MQneg py => PQcompare py px | _ => Lt end
  end.

Definition MQlt x y :=
  match x with
  | MQ0 => match y with MQpos _ => True | _ => False end
  | MQpos px => match y with MQpos py => PQlt px py | _ => False end
  | MQneg px => match y with MQneg py => PQlt py px | _ => True end
  end.
Arguments MQlt x%MQ y%MQ.

Definition MQle x y :=
  match x with
  | MQ0 => match y with MQ0 | MQpos _ => True | _ => False end
  | MQpos px => match y with MQpos py => PQle px py | _ => False end
  | MQneg px => match y with MQneg py => PQle py px | _ => True end
  end.
Arguments MQle x%MQ y%MQ.

Definition MQgt x y := MQlt y x.
Definition MQge x y := MQle y x.

Notation "x < y" := (MQlt x y) : MQ_scope.
Notation "x ≤ y" := (MQle x y) : MQ_scope.
Notation "x > y" := (MQgt x y) : MQ_scope.
Notation "x ≥ y" := (MQge x y) : MQ_scope.

Instance MQlt_morph : Proper (MQeq ==> MQeq ==> iff) MQlt.
Proof.
unfold "<"%MQ, "=="%MQ.
intros x1 x2 Hx y1 y2 Hy.
destruct x1, y1, x2, y2; try easy; now rewrite Hx, Hy.
Qed.

(* addition, opposite, subtraction *)

Definition MQopp x :=
  match x with
  | MQ0 => MQ0
  | MQpos px => MQneg px
  | MQneg px => MQpos px
  end.

Definition MQadd_PQ_l px y :=
  match y with
  | MQ0 => MQpos px
  | MQpos py => MQpos (px + py)
  | MQneg py =>
      match PQcompare px py with
      | Eq => MQ0
      | Lt => MQneg (py - px)
      | Gt => MQpos (px - py)
      end
  end.

Definition MQadd x y :=
  match x with
  | MQ0 => y
  | MQpos px => MQadd_PQ_l px y
  | MQneg px => MQopp (MQadd_PQ_l px (MQopp y))
  end.

Definition MQabs x :=
  match x with
  | MQneg px => MQpos px
  | _ => x
  end.

Notation "- x" := (MQopp x) : MQ_scope.
Notation "x + y" := (MQadd x y) : MQ_scope.
Notation "x - y" := (MQadd x (MQopp y)) : MQ_scope.

Open Scope MQ_scope.

Instance MQabs_morph : Proper (MQeq ==> MQeq) MQabs.
Proof.
intros x y Hxy.
unfold MQabs, "=="%MQ; simpl.
unfold "==" in Hxy.
now destruct x, y.
Qed.

(* allows to use rewrite inside a if_PQlt_le_dec
   when P and Q are of type MQ, through PQlt_le_if, e.g.
      H : (x = y)%PQ
      ====================
      ... if_PQlt_le_dec x z then P else Q ...
   > rewrite H.
      ====================
      ... if_PQlt_le_dec y z then P else Q ...
 *)
Instance PQeq_PQlt_le_MQ_morph {P Q} :
  Proper (PQeq ==> PQeq ==> MQeq) (λ x y, if_PQlt_le_dec x y then P else Q).
Proof.
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
do 2 rewrite <- PQlt_le_if.
destruct (PQlt_le_dec x1 y1) as [H1| H1]; rewrite Hx, Hy in H1.
-destruct (PQlt_le_dec x2 y2) as [| H2]; [ easy | ].
 now apply PQnlt_ge in H2.
-destruct (PQlt_le_dec x2 y2) as [H2| ]; [ | easy ].
 now apply PQnlt_ge in H2.
Qed.

(* Leibnitz equality applies *)
Theorem MQadd_comm : ∀ x y, x + y = y + x.
Proof.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py]; try easy; simpl.
-f_equal; apply PQadd_comm.
-now rewrite PQcompare_comm; destruct (PQcompare py px).
-now rewrite PQcompare_comm; destruct (PQcompare py px).
-f_equal; apply PQadd_comm.
Qed.

(* allows to use rewrite inside an addition
   e.g.
      H : x == y
      ====================
      ... (x + z) ...
   rewrite H.
 *)
Instance MQadd_morph : Proper (MQeq ==> MQeq ==> MQeq) MQadd.
Proof.
intros x1 x2 Hx y1 y2 Hy.
move Hx before Hy.
assert (H : ∀ px1 px2 py1 py2,
  MQpos px1 == MQpos px2
  → MQneg py1 == MQneg py2
  → MQpos px1 + MQneg py1 == MQpos px2 + MQneg py2). {
  clear; intros * Hx Hy.
  unfold "=="%MQ in Hx, Hy |-*.
  unfold "+"%MQ; simpl.
  remember (PQcompare px1 py1) as c1 eqn:Hc1; symmetry in Hc1.
  remember (PQcompare px2 py2) as c2 eqn:Hc2; symmetry in Hc2.
  rewrite Hx, Hy, Hc2 in Hc1; subst c2.
  destruct c1; [ easy | | ].
  -apply PQcompare_lt_iff in Hc2.
   rewrite <- Hx, <- Hy in Hc2.
   now apply PQsub_morph.
  -apply PQcompare_gt_iff in Hc2.
   rewrite <- Hx, <- Hy in Hc2.
   now apply PQsub_morph.
}
destruct
  x1 as [| px1| px1], y1 as [| py1| py1],
  x2 as [| px2| px2], y2 as [| py2| py2]; try easy.
-unfold "=="%MQ in Hx, Hy |-*; unfold "+"%MQ; simpl.
 now rewrite Hx, Hy.
-now apply H.
-do 2 (rewrite MQadd_comm; symmetry).
 now apply H.
-unfold "=="%MQ in Hx, Hy |-*; unfold "+"%MQ; simpl.
 now rewrite Hx, Hy.
Qed.

(* Leibnitz equality applies *)
Theorem MQabs_0 : MQabs 0 = 0.
Proof. easy. Qed.

(* Leibnitz equality applies *)
Theorem MQabs_opp : ∀ x, MQabs (- x) = MQabs x.
Proof. now intros x; destruct x. Qed.

Theorem MQadd_swap_lemma1 : ∀ px py pz,
  match PQcompare (px + py) pz with
  | Eq => 0
  | Lt => MQneg (pz - (px + py))
  | Gt => MQpos (px + py - pz)
  end ==
  match PQcompare px pz with
  | Eq => MQpos py
  | Lt =>
      match PQcompare (pz - px) py with
      | Eq => 0
      | Lt => MQpos (py - (pz - px))
      | Gt => MQneg (pz - px - py)
      end
  | Gt => MQpos (px - pz + py)
  end.
Proof.
intros.
remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
remember (PQcompare px pz) as c2 eqn:Hc2; symmetry in Hc2.
move c2 before c1.
destruct c1, c2; repeat PQcompare_iff.
+now rewrite Hc2, PQadd_comm in Hc1; apply PQadd_no_neutral in Hc1.
+remember (PQcompare (pz - px) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; PQcompare_iff; [ easy | | ].
 *apply (PQadd_lt_mono_r _ _ px) in Hc3.
  rewrite PQsub_add in Hc3; [ | easy ].
  rewrite PQadd_comm, Hc1 in Hc3.
  now apply PQlt_irrefl in Hc3.
 *apply (PQadd_lt_mono_r _ _ px) in Hc3.
  rewrite PQsub_add in Hc3; [ | easy ].
  rewrite PQadd_comm, Hc1 in Hc3.
  now apply PQlt_irrefl in Hc3.
+rewrite <- Hc1 in Hc2.
 exfalso; apply PQnle_gt in Hc2; apply Hc2.
 apply PQlt_le_incl, PQlt_add_r.
+rewrite Hc2 in Hc1.
 exfalso; apply PQnle_gt in Hc1; apply Hc1.
 apply PQlt_le_incl, PQlt_add_r.
+remember (PQcompare (pz - px) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; PQcompare_iff; simpl.
 *rewrite PQadd_comm, <- Hc3 in Hc1.
  rewrite PQsub_add in Hc1; [ | easy ].
  now apply PQlt_irrefl in Hc1.
 *apply (PQadd_lt_mono_r _ _ px) in Hc3.
  rewrite PQsub_add in Hc3; [ | easy ].
  rewrite PQadd_comm in Hc3.
  exfalso; apply PQnle_gt in Hc3; apply Hc3.
  now apply PQlt_le_incl.
 *now f_equal; rewrite PQsub_add_distr.
+apply PQnle_gt in Hc2.
 exfalso; apply Hc2; apply PQlt_le_incl.
 apply (PQlt_trans _ (px + py)); [ | easy ].
 apply PQlt_add_r.
+rewrite (PQsub_morph pz pz (px + py) (py + pz)); [ | easy | easy | ].
 *now rewrite PQadd_sub.
 *now rewrite Hc2, PQadd_comm.
+simpl.
 remember (PQcompare (pz - px) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; PQcompare_iff; simpl.
 *rewrite PQadd_comm, <- Hc3 in Hc1.
  rewrite PQsub_add in Hc1; [ | easy ].
  now apply PQlt_irrefl in Hc1.
 *rewrite PQadd_comm; symmetry.
  now f_equal; rewrite PQsub_sub_distr.
 *apply (PQadd_lt_mono_r _ _ px) in Hc3.
  rewrite PQsub_add in Hc3; [ | easy ].
  rewrite PQadd_comm in Hc3.
  exfalso; apply PQnle_gt in Hc3; apply Hc3.
  now apply PQlt_le_incl.
+rewrite PQadd_comm.
 rewrite <- PQadd_sub_assoc; [ | easy ].
 now rewrite PQadd_comm.
Qed.

Theorem MQadd_swap_lemma2 : ∀ px py pz,
  match PQcompare px py with
  | Eq => MQneg pz
  | Lt => MQneg (py - px + pz)
  | Gt =>
      match PQcompare (px - py) pz with
      | Eq => 0
      | Lt => MQneg (pz - (px - py))
      | Gt => MQpos (px - py - pz)
      end
  end ==
  match PQcompare px pz with
  | Eq => MQneg py
  | Lt => MQneg (pz - px + py)
  | Gt =>
      match PQcompare (px - pz) py with
      | Eq => 0
      | Lt => MQneg (py - (px - pz))
      | Gt => MQpos (px - pz - py)
      end
  end.
Proof.
intros.
remember (PQcompare px py) as c1 eqn:Hc1; symmetry in Hc1.
remember (PQcompare px pz) as c2 eqn:Hc2; symmetry in Hc2.
destruct c1, c2; repeat PQcompare_iff; simpl.
-now rewrite <- Hc1, Hc2.
-rewrite (PQsub_morph _ py _ pz); [ | easy | easy | easy ].
 rewrite PQsub_add; [ easy | now rewrite <- Hc1 ].
-remember (PQcompare (px - pz) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; PQcompare_iff.
 +exfalso; rewrite <- Hc1 in Hc3.
  now apply PQsub_no_neutral in Hc3.
 +rewrite PQsub_sub_distr; [ | easy | easy ].
  rewrite PQadd_comm.
  rewrite (PQsub_morph px py (pz + py) (pz + py)); [ | | easy | easy ].
  *now rewrite PQadd_sub.
  *rewrite Hc1; apply PQlt_add_l.
 +apply PQnle_gt in Hc3.
  exfalso; apply Hc3; rewrite <- Hc1.
  now apply PQlt_le_incl, PQsub_lt.
-rewrite (PQsub_morph _ pz _ py); [ | easy | easy | easy ].
 rewrite PQsub_add; [ easy | now rewrite <- Hc2 ].
-rewrite PQadd_comm.
 rewrite PQadd_sub_assoc; [ | easy ].
 now rewrite PQadd_sub_swap.
-remember (PQcompare (px - pz) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; PQcompare_iff.
 +exfalso; rewrite <- Hc3 in Hc1.
  apply PQnle_gt in Hc1; apply Hc1.
  now apply PQlt_le_incl, PQsub_lt.
 +rewrite PQsub_sub_distr; [ | easy | easy ].
  now rewrite PQadd_sub_swap.
 +exfalso; apply PQnle_gt in Hc3; apply Hc3.
  apply PQlt_le_incl.
  apply (PQlt_trans _ px); [ now apply PQsub_lt | easy ].
-remember (PQcompare (px - py) pz) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; PQcompare_iff.
 +exfalso; rewrite <- Hc2 in Hc3.
  now apply PQsub_no_neutral in Hc3.
 +symmetry in Hc2.
  rewrite (PQsub_morph _ (px - py) _ px); [ | easy | easy | easy ].
  rewrite PQsub_sub_distr; [ | easy | now apply PQsub_lt ].
  now rewrite PQadd_comm, PQadd_sub.
 +exfalso; apply PQnle_gt in Hc3; apply Hc3.
  rewrite <- Hc2.
  now apply PQlt_le_incl, PQsub_lt.
-remember (PQcompare (px - py) pz) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; PQcompare_iff.
 *exfalso; rewrite <- Hc3 in Hc2.
  apply PQnle_gt in Hc2; apply Hc2.
  now apply PQlt_le_incl, PQsub_lt.
 *rewrite PQsub_sub_distr; [ | easy | easy ].
  now rewrite PQadd_sub_swap.
 *exfalso; apply PQnle_gt in Hc3; apply Hc3.
  apply PQlt_le_incl.
  apply (PQlt_trans _ px); [ now apply PQsub_lt | easy ].
-remember (PQcompare (px - py) pz) as c3 eqn:Hc3; symmetry in Hc3.
 remember (PQcompare (px - pz) py) as c4 eqn:Hc4; symmetry in Hc4.
 destruct c3, c4; repeat PQcompare_iff; simpl.
 *easy.
 *exfalso; apply PQnle_gt in Hc4; apply Hc4.
  symmetry in Hc3.
  rewrite (PQsub_morph _ (px - py) _ px); [ | easy | easy | easy ].
  rewrite PQsub_sub_distr; [ | easy | now apply PQsub_lt ].
  rewrite PQadd_comm, PQadd_sub; apply PQle_refl.
 *exfalso; apply PQnle_gt in Hc4; apply Hc4.
  symmetry in Hc3.
  rewrite (PQsub_morph _ (px - py) _ px); [ | easy | easy | easy ].
  rewrite PQsub_sub_distr; [ | easy | now apply PQsub_lt ].
  rewrite PQadd_comm, PQadd_sub; apply PQle_refl.
 *exfalso; symmetry in Hc4.
  rewrite (PQsub_morph _ (px - pz) _ px) in Hc3; [ | easy | easy | easy ].
  rewrite PQsub_sub_distr in Hc3; [ | easy | now apply PQsub_lt ].
  rewrite PQadd_comm, PQadd_sub in Hc3.
  now apply PQlt_irrefl in Hc3.
 *rewrite PQsub_sub_distr; [ | easy | easy ].
  rewrite PQsub_sub_distr; [ | easy | easy ].
  now rewrite PQadd_comm.
 *exfalso; apply PQnle_gt in Hc4; apply Hc4; clear Hc4.
  apply (PQadd_le_mono_r _ _ pz).
  rewrite PQsub_add; [ | easy ].
  apply PQnlt_ge; intros Hc4.
  apply PQnle_gt in Hc3; apply Hc3; clear Hc3.
  apply (PQadd_le_mono_r _ _ py).
  rewrite PQsub_add; [ | easy ].
  now apply PQlt_le_incl; rewrite PQadd_comm.
 *exfalso; symmetry in Hc4.
  rewrite (PQsub_morph _ (px - pz) _ px) in Hc3; [ | easy | easy | easy ].
  rewrite PQsub_sub_distr in Hc3; [ | easy | now apply PQsub_lt ].
  rewrite PQadd_comm, PQadd_sub in Hc3.
  now apply PQlt_irrefl in Hc3.
 *exfalso; apply PQnle_gt in Hc4; apply Hc4; clear Hc4.
  apply (PQadd_le_mono_r _ _ pz).
  rewrite PQsub_add; [ | easy ].
  apply PQnlt_ge; intros Hc4.
  apply PQnle_gt in Hc3; apply Hc3; clear Hc3.
  apply (PQadd_le_mono_r _ _ py).
  rewrite PQsub_add; [ | easy ].
  now apply PQlt_le_incl; rewrite PQadd_comm.
 *now rewrite PQsub_sub_swap.
Qed.

Theorem MQpos_inj_wd : ∀ x y, (MQpos x == MQpos y)%MQ ↔ (x == y)%PQ.
Proof. now intros; destruct x, y. Qed.

Theorem MQopp_inj_wd : ∀ x y, (- x == - y)%MQ ↔ (x == y)%MQ.
Proof. now intros; destruct x, y. Qed.

(* Leibnitz equality applies *)
Theorem MQopp_involutive : ∀ x, - - x = x.
Proof. intros; now destruct x. Qed.

Theorem MQopp_match_comp : ∀ c eq lt gt,
  - match c with Eq => eq | Lt => lt | Gt => gt end =
  match c with Eq => - eq | Lt => - lt | Gt => - gt end.
Proof. intros; now destruct c. Qed.

Theorem MQmatch_opp_comp : ∀ c eq lt gt,
  match c with Eq => eq | Lt => lt | Gt => gt end =
  - match c with Eq => - eq | Lt => - lt | Gt => - gt end.
Search (- - _).
Proof. now intros; destruct c; rewrite MQopp_involutive. Qed.

Theorem MQmatch_match_comp : ∀ A c p q (f0 : A) fp fn,
  match
    match c with
    | Eq => 0
    | Lt => MQneg p
    | Gt => MQpos q
    end
  with
  | 0 => f0
  | MQpos px => fp px
  | MQneg px => fn px
  end =
  match c with
  | Eq => f0
  | Lt => fn p
  | Gt => fp q
  end.
Proof. intros; now destruct c. Qed.

Theorem MQadd_add_swap : ∀ x y z, x + y + z == x + z + y.
Proof.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl.
-now rewrite PQadd_comm.
-now rewrite PQcompare_comm; destruct (PQcompare pz py).
-now rewrite PQcompare_comm; destruct (PQcompare pz py).
-now rewrite PQadd_comm.
-now destruct (PQcompare px pz).
-now rewrite PQadd_add_swap.
-rewrite MQmatch_match_comp, MQopp_match_comp; simpl.
 apply MQadd_swap_lemma1.
-now destruct (PQcompare px py).
-rewrite MQmatch_match_comp, MQopp_match_comp; simpl.
 symmetry; apply MQadd_swap_lemma1.
-do 2 (rewrite MQmatch_match_comp; symmetry).
 apply MQadd_swap_lemma2.
-now destruct (PQcompare px pz).
-now destruct (PQcompare px py).
-do 2 rewrite MQopp_match_comp; simpl.
 setoid_rewrite PQcompare_comm.
 do 2 (rewrite MQmatch_match_comp; symmetry).
 do 2 rewrite MQopp_match_comp; simpl.
 setoid_rewrite PQcompare_comm.
 setoid_rewrite MQmatch_opp_comp; simpl.
 apply MQopp_inj_wd.
 do 2 rewrite MQopp_match_comp; simpl.
 apply MQadd_swap_lemma2.
-do 2 rewrite MQopp_match_comp; simpl.
 rewrite PQcompare_comm, MQmatch_match_comp.
 rewrite MQmatch_opp_comp, PQcompare_comm; symmetry.
 rewrite MQmatch_opp_comp; simpl.
 apply MQopp_inj_wd.
 rewrite MQopp_match_comp; simpl.
 apply MQadd_swap_lemma1.
-do 2 rewrite MQopp_match_comp; simpl.
 symmetry; rewrite PQcompare_comm.
 rewrite MQmatch_match_comp, MQmatch_opp_comp; symmetry.
 rewrite MQmatch_opp_comp; symmetry.
 apply MQopp_inj_wd; simpl.
 rewrite PQcompare_comm, MQopp_match_comp; simpl.
 symmetry.
 apply MQadd_swap_lemma1.
-now rewrite PQadd_add_swap.
Qed.

Theorem MQadd_assoc : ∀ x y z, (x + y) + z == x + (y + z).
Proof.
intros.
rewrite MQadd_comm.
remember (x + y) as t eqn:H.
assert (Ht : t == x + y) by now subst t.
rewrite MQadd_comm in Ht; rewrite Ht.
clear t H Ht.
setoid_rewrite MQadd_comm.
apply MQadd_add_swap.
Qed.

Theorem MQadd_cancel_r : ∀ x y z, (x + z == y + z)%MQ ↔ (x == y)%MQ.
Proof.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py]; simpl.
-easy.
-split; [ | easy ].
 unfold MQadd_PQ_l; intros H.
 destruct z as [| pz| pz]; [ easy | | ].
 +apply -> MQpos_inj_wd in H; symmetry in H.
  now apply PQadd_no_neutral in H.
 +remember (PQcompare py pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; PQcompare_iff; [ easy | | easy ].
  apply -> MQpos_inj_wd in H. (* why is it working? *)
  symmetry in H.
  now apply PQsub_no_neutral in H.
-split; [ | easy ].
 unfold MQadd_PQ_l; intros H.
 destruct z as [| pz| pz]; [ easy | | ].
 +simpl in H.
  remember (PQcompare py pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; PQcompare_iff; [ easy | simpl in H | easy ].
  symmetry in H.
  now apply PQsub_no_neutral in H.
 +simpl in H; symmetry in H.
  now apply PQadd_no_neutral in H.
-split; [ | easy ].
 unfold MQadd_PQ_l; intros H.
 destruct z as [| pz| pz]; [ easy | | ].
 +apply -> MQpos_inj_wd in H.
  now apply PQadd_no_neutral in H.
 +remember (PQcompare px pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; PQcompare_iff; [ easy | | easy ].
  apply -> MQpos_inj_wd in H. (* why is it working? *)
  now apply PQsub_no_neutral in H.
-idtac.
...

Theorem MQadd_opp_r : ∀ x, (x - x == 0)%MQ.
Proof.
intros.
unfold "-", "+", "=="; simpl.
rewrite Bool.eqb_negb2.
destruct (PQlt_le_dec (MQpos x) (MQpos x)) as [H1| H1]; simpl.
-now apply PQlt_irrefl in H1.
-destruct (Bool.eqb (MQsign x) true); [ apply PQsub_diag | ].
 rewrite Nat.add_0_r.
 destruct (zerop (PQsub_num (MQpos x) (MQpos x))) as [H2| H2]; [ easy | ].
 unfold PQsub_num in H2.
 now rewrite Nat.sub_diag in H2.
Qed.

Theorem MQadd_opp_l : ∀ x, (- x + x == 0)%MQ.
Proof. intros; rewrite MQadd_comm; apply MQadd_opp_r. Qed.

Theorem MQsub_opp_r : ∀ x y, (x - - y = x + y)%MQ.
Proof.
intros.
unfold "-"%MQ; simpl.
now rewrite Bool.negb_involutive.
Qed.

Theorem MQopp_sub_distr : ∀ x y, (- (x - y) == - x + y)%MQ.
Proof.
intros.
unfold "+"%MQ; simpl.
remember (MQsign x) as sx eqn:Hsx; symmetry in Hsx.
remember (MQsign y) as sy eqn:Hsy; symmetry in Hsy.
destruct sx, sy; simpl; [ | easy | easy | ].
-now destruct (PQlt_le_dec (MQpos x) (MQpos y)).
-now destruct (PQlt_le_dec (MQpos x) (MQpos y)).
Qed.

Theorem MQsub_add_distr : ∀ x y z, (x - (y + z) == x - y - z)%MQ.
Proof.
intros.
rewrite MQadd_assoc.
unfold "+"%MQ; simpl.
remember (MQsign x) as sx eqn:Hsx; symmetry in Hsx.
remember (MQsign y) as sy eqn:Hsy; symmetry in Hsy.
remember (MQsign z) as sz eqn:Hsz; symmetry in Hsz.
destruct sy, sz; simpl; [ easy | | | easy ].
-now destruct sx, (PQlt_le_dec (MQpos y) (MQpos z)).
-now destruct sx, (PQlt_le_dec (MQpos y) (MQpos z)).
Qed.

Theorem MQsub_sub_distr : ∀ x y z, (x - (y - z) == x + z - y)%MQ.
Proof.
intros.
rewrite MQsub_add_distr, MQsub_opp_r.
rewrite MQadd_shuffle0.

...
intros.
rewrite MQadd_assoc.
unfold "+"%MQ; simpl.
remember (MQsign x) as sx eqn:Hsx; symmetry in Hsx.
remember (MQsign y) as sy eqn:Hsy; symmetry in Hsy.
remember (MQsign z) as sz eqn:Hsz; symmetry in Hsz.
destruct sy, sz; simpl.
-destruct sx; simpl.
 +destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H1| H1]; simpl.
  *destruct (PQlt_le_dec (MQpos z) (MQpos y)) as [H2|]; [ simpl | easy ].
   apply PQnle_gt in H2.
   exfalso; apply H2; clear H2.
   now apply PQlt_le_incl.
  *idtac.

...

-now destruct sx, (PQlt_le_dec (MQpos y) (MQpos z)).
-now destruct sx, (PQlt_le_dec (MQpos y) (MQpos z)).
Qed.

rewrite MQsub_add_distr.
...

(* multiplication, inverse, division *)

Definition MQmul x y :=
  MQmake (Bool.eqb (MQsign x) (MQsign y)) (MQpos x * MQpos y).

Definition MQinv x :=
  MQmake (MQsign x) (PQinv (MQpos x)).

Notation "x * y" := (MQmul x y) : MQ_scope.
Notation "/ x" := (MQinv x) : MQ_scope.
Notation "x / y" := (MQmul x (MQinv y)) : MQ_scope.

...
(* remplacer ?P et ?Q par True et False, pour voir *)

Ltac MQmul_morph_tac :=
  match goal with
  | [ H : if (zerop (PQnum (MQpos ?x) + PQnum (MQpos ?y))) then ?P else ?Q
       |- _ ] =>
      destruct (zerop (PQnum (MQpos x) + PQnum (MQpos y)))
        as [H1| H1]; [ | easy ];
      apply Nat.eq_add_0 in H1;
      unfold "=="%PQ, "*"%PQ, nd; simpl; unfold PQmul_num;
      now rewrite (proj1 H1), (proj2 H1)
  | [ H : if (zerop (PQnum (MQpos ?x) + PQnum (MQpos ?y))) then ?P else ?Q
       |- _ ] =>
      destruct (zerop (PQnum (MQpos x) + PQnum (MQpos y)))
        as [H1| H1]; [ | easy ];
      apply Nat.eq_add_0 in H1;
      unfold PQmul_num;
      now rewrite (proj1 H1), (proj2 H1), Nat.mul_0_r, Nat.mul_0_r
  | [ Hx : (MQpos ?x1 == MQpos ?x2)%PQ, Hy : (MQpos ?y1 == MQpos ?y2)%PQ
       |- _ ] =>
      now rewrite Hx, Hy
  | _ => idtac
  end.

(* allows to use rewrite inside a multiplication
   e.g.
      H : x = y
      ====================
      ... (x * z) ...
   rewrite H.
 *)
Instance MQmul_morph : Proper (MQeq ==> MQeq ==> MQeq) MQmul.
Proof.
unfold "=="%MQ; simpl.
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
unfold "*"%MQ; simpl.
remember (MQsign x1) as sx1 eqn:Hsx1; symmetry in Hsx1.
remember (MQsign x2) as sx2 eqn:Hsx2; symmetry in Hsx2.
remember (MQsign y1) as sy1 eqn:Hsy1; symmetry in Hsy1.
remember (MQsign y2) as sy2 eqn:Hsy2; symmetry in Hsy2.
move sx2 before sx1; move sy1 before sx2; move sy2 before sy1.
move Hsy1 before Hsx2; move Hsy2 before Hsy1.
destruct sx1, sx2, sy1, sy2; simpl in Hx, Hy |-*; MQmul_morph_tac.
Qed.

Theorem MQmul_comm : ∀ x y, x * y == y * x.
Proof.
intros.
unfold MQmul.
now rewrite Bool_eqb_comm, PQmul_comm.
Qed.

Theorem MQmul_assoc : ∀ x y z, (x * y) * z == x * (y * z).
Proof.
intros.
unfold MQmul; simpl.
now rewrite Bool_eqb_assoc, PQmul_assoc.
Qed.

Theorem MQpos_mul : ∀ x y, (MQpos (x * y) == MQpos x * MQpos y)%PQ.
Proof. easy. Qed.

Theorem MQmul_add_distr_l : ∀ x y z, x * (y + z) == x * y + x * z.
Proof.
(* the 2nd case is almost the first one by swapping y and z *)
intros.
unfold "=="; simpl.
unfold "+", "*"; simpl.
remember (MQsign x) as sx eqn:Hsx; symmetry in Hsx.
remember (MQsign y) as sy eqn:Hsy; symmetry in Hsy.
remember (MQsign z) as sz eqn:Hsz; symmetry in Hsz.
destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2]; simpl.
-destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z)) as [H3| H3].
 +destruct sx, sy, sz; simpl;
    try apply PQmul_add_distr_l; apply PQmul_sub_distr_l.
 +destruct (PQeq_dec (MQpos x) 0) as [H4| H4].
  *unfold "=="%PQ, nd in H4; simpl in H4.
   unfold PQmul_num, PQsub_num, nd; simpl.
   unfold PQmul_num.
   apply Nat.eq_mul_0_l in H4; [ | easy ].
   unfold "*"%PQ, "+"%PQ; simpl.
   unfold PQmul_num; simpl.
   rewrite H4.
   destruct sx, sy, sz; simpl; try easy; try apply PQmul_add_distr_l.
  *apply PQmul_le_mono_pos_l in H3; [ | easy ].
   now apply PQnlt_ge in H2.
-destruct (PQlt_le_dec (MQpos x * MQpos y) (MQpos x * MQpos z)) as [H3| H3].
 +destruct (PQeq_dec (MQpos x) 0) as [H4| H4].
  *unfold "=="%PQ, nd in H4; simpl in H4.
   unfold PQmul_num, PQsub_num, nd; simpl.
   unfold PQmul_num.
   apply Nat.eq_mul_0_l in H4; [ | easy ].
   unfold "*"%PQ, "+"%PQ; simpl.
   unfold PQmul_num; simpl.
   rewrite H4.
   destruct sx, sy, sz; simpl; try easy; try apply PQmul_add_distr_l.
  *apply PQnle_gt in H3; exfalso; apply H3.
   now apply PQmul_le_mono_pos_l.
 +destruct sx, sy, sz; simpl;
    try apply PQmul_add_distr_l; apply PQmul_sub_distr_l.
Qed.
