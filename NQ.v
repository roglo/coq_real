(* Implementation of rationals using only nat *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Morphisms.
Require Import PQ.

Delimit Scope NQ_scope with NQ.

Inductive NQ :=
  | NQ0 : NQ
  | NQpos : PQ → NQ
  | NQneg : PQ → NQ.
Arguments NQpos p%PQ.
Arguments NQneg p%PQ.

Notation "0" := (NQ0) : NQ_scope.
Notation "1" := (NQpos 1) : NQ_scope.

Definition NQ_of_nat n :=
  match n with
  | 0 => NQ0
  | S _ => NQpos (PQ_of_nat n)
  end.

(* equality *)

Definition NQeq x y :=
  match x with
  | NQ0 => match y with NQ0 => True | _ => False end
  | NQpos px => match y with NQpos py => (px == py)%PQ | _ => False end
  | NQneg px => match y with NQneg py => (px == py)%PQ | _ => False end
  end.

Notation "x == y" := (NQeq x y) (at level 70) : NQ_scope.

Theorem NQeq_refl : ∀ x : NQ, (x == x)%NQ.
Proof. now intros; unfold "=="%NQ; destruct x. Qed.

Theorem NQeq_symm : ∀ x y : NQ, (x == y)%NQ → (y == x)%NQ.
Proof.
unfold "=="%NQ.
intros * Hxy.
destruct x as [| px| px]; [ easy | now destruct y | now destruct y ].
Qed.

Theorem NQeq_trans : ∀ x y z : NQ, (x == y)%NQ → (y == z)%NQ → (x == z)%NQ.
Proof.
unfold "=="%NQ.
intros * Hxy Hyz.
destruct x, y as [| py| py], z; try easy; now transitivity py.
Qed.

Add Parametric Relation : _ NQeq
 reflexivity proved by NQeq_refl
 symmetry proved by NQeq_symm
 transitivity proved by NQeq_trans
 as NQeq_equiv_rel.

(* allows to use rewrite inside a NQpos
   e.g.
      H : x = y
      ====================
      ... (NQpos x) ...
   rewrite H.
 *)
Instance NQpos_morph : Proper (PQeq ==> NQeq) NQpos.
Proof. easy. Qed.

(* allows to use rewrite inside a NQneg
   e.g.
      H : x = y
      ====================
      ... (NQneg x) ...
   rewrite H.
 *)
Instance NQneg_morph : Proper (PQeq ==> NQeq) NQneg.
Proof. easy. Qed.

(* comparison *)

Definition NQcompare x y :=
  match x with
  | NQ0 => match y with NQ0 => Eq | NQpos _ => Lt | NQneg _ => Gt end
  | NQpos px => match y with NQpos py => PQcompare px py | _ => Gt end
  | NQneg px => match y with NQneg py => PQcompare py px | _ => Lt end
  end.

Definition NQlt x y :=
  match x with
  | NQ0 => match y with NQpos _ => True | _ => False end
  | NQpos px => match y with NQpos py => PQlt px py | _ => False end
  | NQneg px => match y with NQneg py => PQlt py px | _ => True end
  end.
Arguments NQlt x%NQ y%NQ.

Definition NQle x y :=
  match x with
  | NQ0 => match y with NQ0 | NQpos _ => True | _ => False end
  | NQpos px => match y with NQpos py => PQle px py | _ => False end
  | NQneg px => match y with NQneg py => PQle py px | _ => True end
  end.
Arguments NQle x%NQ y%NQ.

Definition NQgt x y := NQlt y x.
Definition NQge x y := NQle y x.

Notation "x < y" := (NQlt x y) : NQ_scope.
Notation "x ≤ y" := (NQle x y) : NQ_scope.
Notation "x > y" := (NQgt x y) : NQ_scope.
Notation "x ≥ y" := (NQge x y) : NQ_scope.

Instance NQlt_morph : Proper (NQeq ==> NQeq ==> iff) NQlt.
Proof.
unfold "<"%NQ, "=="%NQ.
intros x1 x2 Hx y1 y2 Hy.
destruct x1, y1, x2, y2; try easy; now rewrite Hx, Hy.
Qed.

(* addition, opposite, subtraction *)

Definition NQopp x :=
  match x with
  | NQ0 => NQ0
  | NQpos px => NQneg px
  | NQneg px => NQpos px
  end.

Definition NQadd_pos_l px y :=
  match y with
  | NQ0 => NQpos px
  | NQpos py => NQpos (px + py)
  | NQneg py =>
      match PQcompare px py with
      | Eq => NQ0
      | Lt => NQneg (py - px)
      | Gt => NQpos (px - py)
      end
  end.

Definition NQadd x y :=
  match x with
  | NQ0 => y
  | NQpos px => NQadd_pos_l px y
  | NQneg px => NQopp (NQadd_pos_l px (NQopp y))
  end.

Definition NQabs x :=
  match x with
  | NQneg px => NQpos px
  | _ => x
  end.

Notation "- x" := (NQopp x) : NQ_scope.
Notation "x + y" := (NQadd x y) : NQ_scope.
Notation "x - y" := (NQadd x (NQopp y)) : NQ_scope.
Notation "‖ x ‖" := (NQabs x) (at level 60) : NQ_scope.

(* *)

Ltac PQcompare_iff :=
  match goal with
  | [ H : PQcompare _ _ = Eq |- _ ] => apply PQcompare_eq_iff in H
  | [ H : PQcompare _ _ = Lt |- _ ] => apply PQcompare_lt_iff in H
  | [ H : PQcompare _ _ = Gt |- _ ] => apply PQcompare_gt_iff in H
  end.

Theorem PQcompare_swap : ∀ {A} {a b c : A} px py,
  match PQcompare px py with
  | Eq => a
  | Lt => b
  | Gt => c
  end =
  match PQcompare py px with
  | Eq => a
  | Lt => c
  | Gt => b
  end.
Proof.
intros.
remember (PQcompare px py) as b1 eqn:Hb1; symmetry in Hb1.
remember (PQcompare py px) as b2 eqn:Hb2; symmetry in Hb2.
move b2 before b1.
destruct b1, b2; try easy; repeat PQcompare_iff.
-now rewrite Hb1 in Hb2; apply PQlt_irrefl in Hb2.
-now rewrite Hb1 in Hb2; apply PQlt_irrefl in Hb2.
-now rewrite Hb2 in Hb1; apply PQlt_irrefl in Hb1.
-now apply PQnle_gt in Hb2; exfalso; apply Hb2; apply PQlt_le_incl.
-now rewrite Hb2 in Hb1; apply PQlt_irrefl in Hb1.
-now apply PQnle_gt in Hb2; exfalso; apply Hb2; apply PQlt_le_incl.
Qed.

(* *)

Open Scope NQ_scope.

Instance NQabs_morph : Proper (NQeq ==> NQeq) NQabs.
Proof.
intros x y Hxy.
unfold NQabs, "=="%NQ; simpl.
unfold "==" in Hxy.
now destruct x, y.
Qed.

Definition if_PQlt_le {A} (P Q : A) x y := if PQlt_le_dec x y then P else Q.
Arguments if_PQlt_le _ _ _ x%PQ y%PQ.

Notation "'if_PQlt_le_dec' x y 'then' P 'else' Q" :=
  (if_PQlt_le P Q x y) (at level 200, x at level 9, y at level 9).

Theorem PQlt_le_if : ∀ {A} (P Q : A) x y,
  (if PQlt_le_dec x y then P else Q) = @if_PQlt_le A P Q x y.
Proof. easy. Qed.

(* allows to use rewrite inside a if_PQlt_le_dec ...
   through PQlt_le_if, e.g.
      H : (x = y)%PQ
      ====================
      ... if_PQlt_le_dec x z then P else Q ...
   > rewrite H.
      ====================
      ... if_PQlt_le_dec y z then P else Q ...
 *)
Instance PQeq_PQlt_le_morph {P Q} :
  Proper (PQeq ==> PQeq ==> iff) (λ x y, if PQlt_le_dec x y then P else Q).
Proof.
intros x1 x2 Hx y1 y2 Hy.
move y1 before x2; move y2 before y1.
destruct (PQlt_le_dec x1 y1) as [H1| H1]; rewrite Hx, Hy in H1.
-destruct (PQlt_le_dec x2 y2) as [| H2]; [ easy | ].
 now apply PQnlt_ge in H2.
-destruct (PQlt_le_dec x2 y2) as [H2| ]; [ | easy ].
 now apply PQnlt_ge in H2.
Qed.

(* allows to use rewrite inside a if_PQlt_le_dec
   when P and Q are of type NQ, through PQlt_le_if, e.g.
      H : (x = y)%PQ
      ====================
      ... if_PQlt_le_dec x z then P else Q ...
   > rewrite H.
      ====================
      ... if_PQlt_le_dec y z then P else Q ...
 *)
Instance PQeq_PQlt_le_NQ_morph {P Q} :
  Proper (PQeq ==> PQeq ==> NQeq) (λ x y, if_PQlt_le_dec x y then P else Q).
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

Theorem NQpos_inj_wd : ∀ x y, (NQpos x == NQpos y)%NQ ↔ (x == y)%PQ.
Proof. intros; easy. Qed.

Instance NQadd_pos_l_morph : Proper (PQeq ==> NQeq ==> NQeq) NQadd_pos_l.
Proof.
intros x1 x2 Hx y1 y2 Hy.
unfold NQadd_pos_l.
destruct y1 as [| py1| py1], y2 as [| py2| py2]; try easy.
-now apply -> NQpos_inj_wd in Hy; rewrite Hx, Hy.
-apply -> NQpos_inj_wd in Hy; rewrite Hx, Hy.
 remember (PQcompare x2 py2) as c1 eqn:Hc1; symmetry in Hc1.
 destruct c1; PQcompare_iff; [ easy | | ].
 +symmetry in Hx, Hy.
  now rewrite (PQsub_morph x2 x1 _ py1).
 +symmetry in Hx, Hy.
  now rewrite (PQsub_morph py2 py1 _ x1).
Qed.

Theorem NQadd_comm : ∀ x y, x + y = y + x.
Proof.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py]; try easy; simpl.
-f_equal; apply PQadd_comm.
-now rewrite PQcompare_swap; destruct (PQcompare py px).
-now rewrite PQcompare_swap; destruct (PQcompare py px).
-f_equal; apply PQadd_comm.
Qed.

(* allows to use rewrite inside an addition
   e.g.
      H : x == y
      ====================
      ... (x + z) ...
   rewrite H.
 *)
Instance NQadd_morph : Proper (NQeq ==> NQeq ==> NQeq) NQadd.
Proof.
intros x1 x2 Hx y1 y2 Hy.
move Hx before Hy.
assert (H : ∀ px1 px2 py1 py2,
  NQpos px1 == NQpos px2
  → NQneg py1 == NQneg py2
  → NQpos px1 + NQneg py1 == NQpos px2 + NQneg py2). {
  clear; intros * Hx Hy.
  unfold "=="%NQ in Hx, Hy |-*.
  unfold "+"%NQ; simpl.
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
-unfold "=="%NQ in Hx, Hy |-*; unfold "+"%NQ; simpl.
 now rewrite Hx, Hy.
-now apply H.
-do 2 (rewrite NQadd_comm; symmetry).
 now apply H.
-unfold "=="%NQ in Hx, Hy |-*; unfold "+"%NQ; simpl.
 now rewrite Hx, Hy.
Qed.

(* Leibnitz equality applies *)
Theorem NQabs_0 : NQabs 0 = 0.
Proof. easy. Qed.

(* Leibnitz equality applies *)
Theorem NQabs_opp : ∀ x, NQabs (- x) = NQabs x.
Proof. now intros x; destruct x. Qed.

Theorem NQadd_swap_lemma1 : ∀ px py pz,
  match PQcompare (px + py) pz with
  | Eq => 0
  | Lt => NQneg (pz - (px + py))%PQ
  | Gt => NQpos (px + py - pz)%PQ
  end ==
  match PQcompare px pz with
  | Eq => NQpos py
  | Lt =>
      match PQcompare (pz - px) py with
      | Eq => 0
      | Lt => NQpos (py - (pz - px))%PQ
      | Gt => NQneg (pz - px - py)%PQ
      end
  | Gt => NQpos (px - pz + py)%PQ
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

Theorem NQadd_swap_lemma2 : ∀ px py pz,
  match PQcompare px py with
  | Eq => NQneg pz
  | Lt => NQneg (py - px + pz)%PQ
  | Gt =>
      match PQcompare (px - py) pz with
      | Eq => 0
      | Lt => NQneg (pz - (px - py))%PQ
      | Gt => NQpos (px - py - pz)%PQ
      end
  end ==
  match PQcompare px pz with
  | Eq => NQneg py
  | Lt => NQneg (pz - px + py)%PQ
  | Gt =>
      match PQcompare (px - pz) py with
      | Eq => 0
      | Lt => NQneg (py - (px - pz))%PQ
      | Gt => NQpos (px - pz - py)%PQ
      end
  end.
Proof.
intros.
remember (PQcompare px py) as c1 eqn:Hc1; symmetry in Hc1.
remember (PQcompare px pz) as c2 eqn:Hc2; symmetry in Hc2.
destruct c1, c2; repeat PQcompare_iff.
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

Theorem NQopp_inj_wd : ∀ x y, (- x == - y)%NQ ↔ (x == y)%NQ.
Proof. now intros; destruct x, y. Qed.

(* Leibnitz equality applies *)
Theorem NQopp_involutive : ∀ x, - - x = x.
Proof. intros; now destruct x. Qed.

Theorem NQopp_match_comp : ∀ c eq lt gt,
  - match c with Eq => eq | Lt => lt | Gt => gt end =
  match c with Eq => - eq | Lt => - lt | Gt => - gt end.
Proof. intros; now destruct c. Qed.

Theorem NQmatch_opp_comp : ∀ c eq lt gt,
  match c with Eq => eq | Lt => lt | Gt => gt end =
  - match c with Eq => - eq | Lt => - lt | Gt => - gt end.
Proof. now intros; destruct c; rewrite NQopp_involutive. Qed.

Theorem NQmatch_match_comp : ∀ A c p q (f0 : A) fp fn,
  match
    match c with
    | Eq => 0
    | Lt => NQneg p
    | Gt => NQpos q
    end
  with
  | 0 => f0
  | NQpos px => fp px
  | NQneg px => fn px
  end =
  match c with
  | Eq => f0
  | Lt => fn p
  | Gt => fp q
  end.
Proof. intros; now destruct c. Qed.

Theorem NQadd_add_swap : ∀ x y z, x + y + z == x + z + y.
Proof.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl.
-now rewrite PQadd_comm.
-now rewrite PQcompare_swap; destruct (PQcompare pz py).
-now rewrite PQcompare_swap; destruct (PQcompare pz py).
-now rewrite PQadd_comm.
-now destruct (PQcompare px pz).
-now rewrite PQadd_add_swap.
-rewrite NQmatch_match_comp, NQopp_match_comp; simpl.
 apply NQadd_swap_lemma1.
-now destruct (PQcompare px py).
-rewrite NQmatch_match_comp, NQopp_match_comp; simpl.
 symmetry; apply NQadd_swap_lemma1.
-do 2 (rewrite NQmatch_match_comp; symmetry).
 apply NQadd_swap_lemma2.
-now destruct (PQcompare px pz).
-now destruct (PQcompare px py).
-do 2 rewrite NQopp_match_comp; simpl.
 setoid_rewrite PQcompare_swap.
 do 2 (rewrite NQmatch_match_comp; symmetry).
 do 2 rewrite NQopp_match_comp; simpl.
 setoid_rewrite PQcompare_swap.
 setoid_rewrite NQmatch_opp_comp; simpl.
 apply NQopp_inj_wd.
 do 2 rewrite NQopp_match_comp; simpl.
 apply NQadd_swap_lemma2.
-do 2 rewrite NQopp_match_comp; simpl.
 rewrite PQcompare_swap, NQmatch_match_comp.
 rewrite NQmatch_opp_comp, PQcompare_swap; symmetry.
 rewrite NQmatch_opp_comp; simpl.
 apply NQopp_inj_wd.
 rewrite NQopp_match_comp; simpl.
 apply NQadd_swap_lemma1.
-do 2 rewrite NQopp_match_comp; simpl.
 symmetry; rewrite PQcompare_swap.
 rewrite NQmatch_match_comp, NQmatch_opp_comp; symmetry.
 rewrite NQmatch_opp_comp; symmetry.
 apply NQopp_inj_wd; simpl.
 rewrite PQcompare_swap, NQopp_match_comp; simpl.
 symmetry.
 apply NQadd_swap_lemma1.
-now rewrite PQadd_add_swap.
Qed.

Theorem NQadd_assoc : ∀ x y z, (x + y) + z == x + (y + z).
Proof.
intros.
rewrite NQadd_comm.
remember (x + y) as t eqn:H.
assert (Ht : t == x + y) by now subst t.
rewrite NQadd_comm in Ht; rewrite Ht.
clear t H Ht.
setoid_rewrite NQadd_comm.
apply NQadd_add_swap.
Qed.

Theorem NQadd_cancel_r : ∀ x y z, (x + z == y + z)%NQ ↔ (x == y)%NQ.
Proof.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py]; simpl.
-easy.
-split; [ | easy ].
 unfold NQadd_pos_l; intros H.
 destruct z as [| pz| pz]; [ easy | | ].
 +apply -> NQpos_inj_wd in H; symmetry in H.
  now apply PQadd_no_neutral in H.
 +remember (PQcompare py pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; PQcompare_iff; [ easy | | easy ].
  apply -> NQpos_inj_wd in H. (* why is it working? *)
  symmetry in H.
  now apply PQsub_no_neutral in H.
-split; [ | easy ].
 unfold NQadd_pos_l; intros H.
 destruct z as [| pz| pz]; [ easy | | ].
 +simpl in H.
  remember (PQcompare py pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; PQcompare_iff; [ easy | simpl in H | easy ].
  symmetry in H.
  now apply PQsub_no_neutral in H.
 +simpl in H; symmetry in H.
  now apply PQadd_no_neutral in H.
-split; [ | easy ].
 unfold NQadd_pos_l; intros H.
 destruct z as [| pz| pz]; [ easy | | ].
 +apply -> NQpos_inj_wd in H.
  now apply PQadd_no_neutral in H.
 +remember (PQcompare px pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; PQcompare_iff; [ easy | | easy ].
  apply -> NQpos_inj_wd in H. (* why is it working? *)
  now apply PQsub_no_neutral in H.
-split; intros H; [ | now rewrite H ].
 unfold NQadd_pos_l in H.
 destruct z as [| pz| pz].
 +now apply -> NQpos_inj_wd in H.
 +apply -> NQpos_inj_wd in H.
  now apply PQadd_cancel_r in H.
 +remember (PQcompare px pz) as c1 eqn:Hc1; symmetry in Hc1.
  remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
  destruct c1, c2; do 2 PQcompare_iff; try easy.
  *transitivity pz; [ easy | now symmetry ].
  *apply -> NQpos_inj_wd in H.
   now apply PQsub_cancel_l in H.
  *apply -> NQpos_inj_wd in H.
   now apply PQsub_cancel_r in H.
-split; [ | easy ].
 unfold NQadd_pos_l; intros H.
 destruct z as [| pz| pz]; [ easy | | ].
 +simpl in H.
  remember (PQcompare py pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; PQcompare_iff; [ easy | simpl in H | easy ].
  apply (PQadd_cancel_r _ _ py) in H.
  rewrite PQsub_add in H; [ | easy ].
  rewrite PQadd_add_swap in H.
  now apply PQadd_no_neutral in H.
 +remember (PQcompare px pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; PQcompare_iff; [ easy | simpl in H | easy ].
  apply (PQadd_cancel_r _ _ px) in H.
  rewrite PQsub_add in H; [ | easy ].
  rewrite PQadd_add_swap in H; symmetry in H.
  now apply PQadd_no_neutral in H.
-split; [ | easy ].
 unfold NQadd_pos_l; intros H.
 destruct z as [| pz| pz]; [ easy | | ].
 +simpl in H.
  remember (PQcompare px pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; PQcompare_iff; [ easy | simpl in H | easy ].
  now apply PQsub_no_neutral in H.
 +simpl in H.
  now apply PQadd_no_neutral in H.
-split; [ | easy ].
 unfold NQadd_pos_l; intros H.
 destruct z as [| pz| pz]; [ easy | | ].
 +simpl in H.
  remember (PQcompare px pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; PQcompare_iff; [ easy | simpl in H | easy ].
  apply (PQadd_cancel_r _ _ px) in H.
  rewrite PQsub_add in H; [ | easy ].
  rewrite PQadd_add_swap in H; symmetry in H.
  now apply PQadd_no_neutral in H.
 +simpl in H.
  remember (PQcompare py pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; PQcompare_iff; [ easy | simpl in H | easy ].
  apply (PQadd_cancel_r _ _ py) in H.
  rewrite PQsub_add in H; [ | easy ].
  rewrite PQadd_add_swap in H.
  now apply PQadd_no_neutral in H.
-split; intros H.
 +unfold NQadd_pos_l in H.
  destruct z as [| pz| pz]; [ easy | | ]; simpl in H.
  *remember (PQcompare px pz) as c1 eqn:Hc1; symmetry in Hc1.
   remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
   destruct c1, c2; do 2 PQcompare_iff; try easy; simpl in H.
  --now transitivity pz.
  --now apply PQsub_cancel_l in H.
  --now apply PQsub_cancel_r in H.
  *now apply PQadd_cancel_r in H.
 +unfold NQadd_pos_l.
  destruct z as [| pz| pz]; [ easy | | ]; simpl.
  *rewrite H.
   remember (PQcompare py pz) as c1 eqn:Hc1; symmetry in Hc1.
   destruct c1; PQcompare_iff; [ easy | | ]; simpl.
  --apply PQsub_cancel_l; [ now rewrite H | easy | easy ].
  --apply PQsub_cancel_r; [ now rewrite H | easy | easy ].
  *now rewrite H.
Qed.

Theorem NQadd_cancel_l : ∀ x y z, (x + y == x + z)%NQ ↔ (y == z)%NQ.
Proof.
intros.
setoid_rewrite NQadd_comm.
apply NQadd_cancel_r.
Qed.

(* Leibnitz equality applies *)
Theorem NQadd_opp_r : ∀ x, (x - x = 0)%NQ.
Proof.
intros.
now destruct x as [| px| px]; [ easy | | ]; simpl; rewrite PQcompare_refl.
Qed.

(* Leibnitz equality applies *)
Theorem NQadd_opp_l : ∀ x, (- x + x = 0)%NQ.
Proof. intros; rewrite NQadd_comm; apply NQadd_opp_r. Qed.

(* Leibnitz equality applies *)
Theorem NQsub_opp_r : ∀ x y, (x - - y = x + y)%NQ.
Proof.
intros.
unfold "-"%NQ; simpl; now destruct y.
Qed.

(* Leibnitz equality applies *)
Theorem NQopp_sub_distr : ∀ x y, (- (x - y) = - x + y)%NQ.
Proof.
intros.
unfold "+"%NQ; simpl.
destruct x as [| px| px]; [ | easy | ].
-apply NQopp_involutive.
-unfold NQadd_pos_l; simpl.
 rewrite NQopp_involutive.
 now destruct y.
Qed.

(* Leibnitz equality applies *)
Theorem NQopp_add_distr : ∀ x y, (- (x + y) = - x - y)%NQ.
Proof.
intros.
destruct x as [| px| px]; [ easy | | ]; simpl.
-now rewrite NQopp_involutive.
-now rewrite NQopp_involutive.
Qed.

(* Leibnitz equality applies *)
Theorem NQadd_0_l : ∀ x, (0 + x)%NQ = x.
Proof. now intros x; destruct x. Qed.

(* Leibnitz equality applies *)
Theorem NQadd_0_r : ∀ x, (x + 0)%NQ = x.
Proof. now intros x; destruct x. Qed.

Theorem NQsub_sub_distr : ∀ x y z, (x - (y - z) == x - y + z)%NQ.
Proof.
intros.
rewrite NQadd_assoc.
apply NQadd_cancel_l.
now rewrite NQopp_sub_distr.
Qed.

(* multiplication, inverse, division *)

Definition NQmul_PQ_l px y :=
  match y with
  | NQ0 => NQ0
  | NQpos py => NQpos (px * py)
  | NQneg py => NQneg (px * py)
  end.

Definition NQmul x y :=
  match x with
  | NQ0 => NQ0
  | NQpos px => NQmul_PQ_l px y
  | NQneg px => NQmul_PQ_l px (NQopp y)
  end.

Definition NQinv x :=
  match x with
  | NQ0 => NQ0
  | NQpos px => NQpos (/ px)
  | NQneg px => NQneg (/ px)
  end.

Notation "x * y" := (NQmul x y) : NQ_scope.
Notation "/ x" := (NQinv x) : NQ_scope.
Notation "x / y" := (NQmul x (NQinv y)) : NQ_scope.

Instance NQmul_PQ_l_morph : Proper (PQeq ==> NQeq ==> NQeq) NQmul_PQ_l.
Proof.
intros x1 x2 Hx y1 y2 Hy.
unfold NQmul_PQ_l.
destruct y1 as [| py1| py1], y2 as [| py2| py2]; try easy.
-now apply -> NQpos_inj_wd in Hy; rewrite Hx, Hy.
-now apply -> NQpos_inj_wd in Hy; rewrite Hx, Hy.
Qed.

(* allows to use rewrite inside a multiplication
   e.g.
      H : x == y
      ====================
      ... (x * z) ...
   rewrite H.
 *)
Instance NQmul_morph : Proper (NQeq ==> NQeq ==> NQeq) NQmul.
Proof.
intros x1 x2 Hx y1 y2 Hy.
unfold "*".
destruct x1 as [| px1| px1], x2 as [| px2| px2]; simpl; try easy.
-now apply -> NQpos_inj_wd in Hx; rewrite Hx, Hy.
-apply -> NQpos_inj_wd in Hx.
 apply NQopp_inj_wd in Hy.
 now rewrite Hx, Hy.
Qed.

(* Leibnitz equality applies *)
Theorem NQmul_comm : ∀ x y, x * y = y * x.
Proof.
intros.
unfold NQmul.
now destruct x, y; simpl; try now rewrite PQmul_comm.
Qed.

(* Leibnitz equality applies *)
Theorem NQmul_assoc : ∀ x y z, (x * y) * z = x * (y * z).
Proof.
intros.
unfold "*"%NQ.
now destruct x, y, z; simpl; try now rewrite PQmul_assoc.
Qed.

Theorem NQpos_add : ∀ x y, (NQpos (x + y) = NQpos x + NQpos y)%NQ.
Proof. easy. Qed.

Theorem NQpos_mul : ∀ x y, (NQpos (x * y) = NQpos x * NQpos y)%NQ.
Proof. easy. Qed.

Theorem NQpos_mul_neg : ∀ x y, (NQpos (x * y) = NQneg x * NQneg y)%NQ.
Proof. easy. Qed.

Theorem NQneg_add : ∀ x y, (NQneg (x + y) = NQneg x + NQneg y)%NQ.
Proof. easy. Qed.

Theorem NQneg_mul_l : ∀ x y, (NQneg (x * y) = NQneg x * NQpos y)%NQ.
Proof. easy. Qed.

Theorem NQneg_mul_r : ∀ x y, (NQneg (x * y) = NQpos x * NQneg y)%NQ.
Proof. easy. Qed.

Ltac NQpos_tac :=
  match goal with
  | [ |- context[NQpos _ + NQpos _] ] => rewrite <- NQpos_add
  | [ |- context[NQpos _ * NQpos _] ] => rewrite <- NQpos_mul
  | [ |- context[NQneg _ * NQneg _] ] => rewrite <- NQpos_mul_neg
  | [ |- context[NQneg _ + NQneg _] ] => rewrite <- NQneg_add
  | [ |- context[NQneg _ * NQpos _] ] => rewrite <- NQneg_mul_l
  | [ |- context[NQpos _ * NQneg _] ] => rewrite <- NQneg_mul_r
  end.

Theorem NQmul_add_distr_l_lemma1 : ∀ px py pz,
  match PQcompare py pz with
  | Eq => 0
  | Lt => NQneg (px * (pz - py))
  | Gt => NQpos (px * (py - pz))
  end ==
  match PQcompare (px * py) (px * pz) with
  | Eq => 0
  | Lt => NQneg (px * pz - px * py)
  | Gt => NQpos (px * py - px * pz)
  end.
Proof.
intros.
remember (PQcompare py pz) as c1 eqn:Hc1; symmetry in Hc1.
remember (PQcompare (px * py) (px * pz)) as c2 eqn:Hc2; symmetry in Hc2.
destruct c1, c2; do 2 PQcompare_iff.
-easy.
-now rewrite Hc1 in Hc2; apply PQlt_irrefl in Hc2.
-now rewrite Hc1 in Hc2; apply PQlt_irrefl in Hc2.
-apply PQmul_cancel_l in Hc2; rewrite Hc2 in Hc1.
 now apply PQlt_irrefl in Hc1.
-now rewrite PQmul_sub_distr_l.
-exfalso; apply PQnle_gt in Hc2; apply Hc2.
 now apply PQmul_le_mono_l, PQlt_le_incl.
-apply PQmul_cancel_l in Hc2; rewrite Hc2 in Hc1.
 now apply PQlt_irrefl in Hc1.
-exfalso; apply PQnle_gt in Hc2; apply Hc2.
 now apply PQmul_le_mono_l, PQlt_le_incl.
-now rewrite PQmul_sub_distr_l.
Qed.

Theorem NQmul_add_distr_l : ∀ x y z, x * (y + z) == x * y + x * z.
Proof.
intros.
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy;
  repeat NQpos_tac; try now rewrite PQmul_add_distr_l.
-simpl; unfold NQmul_PQ_l.
 rewrite NQmatch_match_comp.
 apply NQmul_add_distr_l_lemma1.
-simpl; unfold NQmul_PQ_l.
 rewrite NQopp_match_comp; simpl.
 rewrite PQcompare_swap, NQmatch_match_comp.
 rewrite NQopp_match_comp; simpl.
 symmetry; rewrite PQcompare_swap; symmetry.
 apply NQmul_add_distr_l_lemma1.
-simpl; unfold NQmul_PQ_l.
 rewrite NQopp_match_comp; simpl.
 rewrite PQcompare_swap, NQmatch_match_comp.
 rewrite NQopp_match_comp; simpl.
 symmetry; rewrite PQcompare_swap; symmetry.
 apply NQmul_add_distr_l_lemma1.
-simpl; unfold NQmul_PQ_l.
 rewrite NQopp_involutive.
 rewrite NQmatch_match_comp.
 apply NQmul_add_distr_l_lemma1.
Qed.

Close Scope NQ.
