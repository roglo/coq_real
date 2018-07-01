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

Definition MQadd x y :=
  match x with
  | MQ0 => y
  | MQpos px =>
      match y with
      | MQ0 => x
      | MQpos py => MQpos (px + py)
      | MQneg py =>
          match PQcompare px py with
          | Eq => MQ0
          | Lt => MQneg (py - px)
          | Gt => MQpos (px - py)
          end
      end
  | MQneg px =>
      match y with
      | MQ0 => x
      | MQpos py =>
          match PQcompare px py with
          | Eq => MQ0
          | Lt => MQpos (py - px)
          | Gt => MQneg (px - py)
          end
      | MQneg py => MQneg (px + py)
      end
  end.

Definition MQopp x :=
  match x with
  | MQ0 => MQ0
  | MQpos px => MQneg px
  | MQneg px => MQpos px
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

Theorem MQadd_comm : ∀ x y, x + y == y + x.
Proof.
assert (H : ∀ px py, MQpos px + MQneg py == MQneg py + MQpos px). {
  intros.
  unfold "==", "+".
  remember (PQcompare px py) as c1 eqn:Hc1; symmetry in Hc1.
  remember (PQcompare py px) as c2 eqn:Hc2; symmetry in Hc2.
  move c2 before c1.
  destruct c1.
  -apply PQcompare_eq_iff in Hc1.
   rewrite Hc1 in Hc2.
   destruct c2; [ easy | | ].
   +now apply PQcompare_lt_iff, PQlt_irrefl in Hc2.
   +now apply PQcompare_gt_iff, PQlt_irrefl in Hc2.
  -apply PQcompare_lt_iff in Hc1.
   destruct c2; [ | | easy ].
   +apply PQcompare_eq_iff in Hc2; rewrite Hc2 in Hc1.
    now apply PQlt_irrefl in Hc1.
   +apply PQcompare_lt_iff in Hc2.
    apply PQnle_gt in Hc2.
    now apply Hc2, PQlt_le_incl.
  -apply PQcompare_gt_iff in Hc1.
   destruct c2; [ | easy | ].
   +apply PQcompare_eq_iff in Hc2; rewrite Hc2 in Hc1.
    now apply PQlt_irrefl in Hc1.
   +apply PQcompare_gt_iff in Hc2.
    apply PQnle_gt in Hc2.
    now apply Hc2, PQlt_le_incl.
}
now intros; destruct x, y; try apply PQadd_comm.
Qed.

(* allows to use rewrite inside an addition
   e.g.
      H : x = y
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

Theorem MQabs_0 : MQabs 0 == 0.
Proof. easy. Qed.

Theorem MQabs_opp : ∀ x, MQabs (- x) == MQabs x.
Proof. now intros x; destruct x. Qed.

Theorem MQadd_assoc : ∀ x y z, (x + y) + z == x + (y + z).
Proof.
intros.
unfold "=="%MQ.
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl.
-now destruct (PQcompare py pz).
-now destruct (PQcompare py pz).
-now destruct (PQcompare px pz).
-apply PQadd_assoc.
-remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
 remember (PQcompare py pz) as cyz eqn:Hcyz; symmetry in Hcyz.
 destruct c1.
 +apply PQcompare_eq_iff in Hc1.
  destruct cyz.
  *apply PQcompare_eq_iff in Hcyz; rewrite Hcyz in Hc1; clear Hcyz.
   now apply PQadd_no_neutral in Hc1.
  *apply PQcompare_lt_iff in Hcyz.
   remember (PQcompare px (pz - py)) as c2 eqn:Hc2; symmetry in Hc2.
   destruct c2; [ easy | | ].
  --apply PQcompare_lt_iff in Hc2.
    apply (PQsub_morph py py) in Hc1; [ | | easy ].
   ++rewrite <- Hc1, PQadd_sub in Hc2.
     now apply PQlt_irrefl in Hc2.
   ++apply PQlt_add_l.
  --apply PQcompare_gt_iff in Hc2; unfold ">"%PQ in Hc2.
    rewrite (PQsub_morph py py pz (px + py)) in Hc2; [ | easy | easy | easy ].
    rewrite PQadd_sub in Hc2.
    now apply PQlt_irrefl in Hc2.
  *apply PQcompare_gt_iff in Hcyz.
   rewrite <- Hc1 in Hcyz; apply PQnle_gt in Hcyz.
   apply Hcyz, PQlt_le_incl, PQlt_add_l.
 +apply PQcompare_lt_iff in Hc1.
  destruct cyz.
  *apply PQcompare_eq_iff in Hcyz.
   rewrite Hcyz in Hc1; apply PQnle_gt in Hc1.
   apply Hc1, PQlt_le_incl, PQlt_add_l.
  *apply PQcompare_lt_iff in Hcyz.
...
intros.
unfold "=="%MQ.
remember (Bool.eqb (MQsign (x + y + z)) (MQsign (x + (y + z)))) as b1 eqn:Hb1.
symmetry in Hb1.
destruct b1.
-apply -> Bool.eqb_true_iff in Hb1.
 unfold "+"%MQ.
 remember (Bool.eqb (MQsign x) (MQsign y)) as bxy eqn:Hbxy.
 remember (Bool.eqb (MQsign x) (MQsign z)) as bxz eqn:Hbxz.
 remember (Bool.eqb (MQsign y) (MQsign z)) as byz eqn:Hbyz.
 symmetry in Hbxy, Hbyz, Hbxz.
 move byz before bxy; move bxz before byz.
 destruct bxy; simpl.
 +apply -> Bool.eqb_true_iff in Hbxy.
  rewrite Hbxy, Hbyz.
  destruct byz.
  *rewrite Bool.eqb_reflx; simpl; apply PQadd_assoc.
  *destruct (PQlt_le_dec (MQpos x + MQpos y) (MQpos z)) as [H1| H1].
  --simpl.
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2].
   ++simpl; rewrite Hbyz.
     destruct (PQlt_le_dec (MQpos x) (MQpos z - MQpos y)) as [H3| H3].
    **simpl.
      rewrite PQadd_comm.
      apply PQsub_add_distr.
    **exfalso.
      apply PQnlt_ge in H3; apply H3; clear H3.
      now apply PQlt_add_lt_sub_r.
   ++exfalso.
     apply PQnle_gt in H1; apply H1.
     rewrite <- PQadd_0_l.
     apply PQadd_le_mono; [ apply PQle_0_l | easy ].
  --simpl.
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2].
   ++simpl; rewrite Hbyz.
     destruct (PQlt_le_dec (MQpos x) (MQpos z - MQpos y)) as [H3| H3].
    **exfalso.
      apply PQnle_gt in H3; apply H3.
      now apply PQle_sub_le_add_r.
    **simpl; symmetry.
      apply PQsub_sub_distr.
      split; [ now apply PQlt_le_incl | easy ].
   ++rewrite Bool.eqb_reflx; simpl; symmetry.
     now apply PQadd_sub_assoc.
 +destruct (PQlt_le_dec (MQpos x) (MQpos y)) as [H1| H1].
  *simpl; rewrite Hbyz.
   destruct byz.
  --simpl; rewrite Hbxy.
    destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H2| H2].
   ++simpl; setoid_rewrite PQadd_comm.
     now apply PQadd_sub_assoc, PQlt_le_incl.
   ++exfalso.
     apply PQnlt_ge in H2; apply H2; clear H2.
     eapply PQlt_le_trans; [ apply H1 | ].
     rewrite <- PQadd_0_r at 1.
     apply PQadd_le_mono; [ | apply PQle_0_l ].
     now unfold "≤"%PQ.
  --destruct (PQlt_le_dec (MQpos y - MQpos x) (MQpos z)) as [H2| H2].
   ++simpl.
     destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H3| H3].
    **simpl; rewrite Hbxz.
      destruct bxz.
    ---simpl.
       rewrite PQadd_sub_assoc; [ | now apply PQlt_le_incl ].
       rewrite PQadd_comm.
       apply PQsub_sub_distr.
       split; [ now apply PQlt_le_incl | ].
       eapply PQle_trans; [ apply PQlt_le_incl, H3 | ].
       rewrite <- PQadd_0_r at 1.
       apply PQadd_le_mono; [ | apply PQle_0_l ].
       now unfold "≤"%PQ.
    ---apply Bool.eqb_false_iff in Hbxy.
       apply Bool.eqb_false_iff in Hbyz.
       apply Bool.eqb_false_iff in Hbxz.
       now destruct (MQsign x), (MQsign y), (MQsign z).
    **simpl; rewrite Hbxy.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H4| H4].
    ---exfalso.
       apply PQnle_gt in H4; apply H4.
       apply PQle_sub_le_add_r.
       rewrite PQadd_comm.
       now apply PQle_sub_le_add_r, PQlt_le_incl.
    ---simpl.
       rewrite PQsub_sub_distr.
     +++rewrite PQsub_sub_distr; [ now rewrite PQadd_comm | ].
        split; [ easy | now apply PQle_sub_le_add_r ].
     +++split; [ now apply PQlt_le_incl | ].
        now apply PQle_sub_le_add_r, PQlt_le_incl.
   ++simpl.
     destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H3| H3].
    **simpl; rewrite Hbxz.
      destruct bxz.
    ---exfalso.
       apply PQnlt_ge in H2; apply H2; clear H2.
       eapply PQle_lt_trans; [ | apply H3 ].
       apply PQle_sub_le_add_r.
       rewrite <- PQadd_0_r at 1.
       apply PQadd_le_mono; [ | apply PQle_0_l ].
       now unfold "≤"%PQ.
    ---apply Bool.eqb_false_iff in Hbxy.
       apply Bool.eqb_false_iff in Hbyz.
       apply Bool.eqb_false_iff in Hbxz.
       now destruct (MQsign x), (MQsign y), (MQsign z).
    **simpl; rewrite Hbxy.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H4| H4].
    ---apply PQsub_sub_swap.
    ---simpl.
       transitivity 0%PQ; [ | symmetry ].
     +++rewrite PQsub_sub_swap.
        now apply PQsub_0_le.
     +++apply PQsub_0_le.
        apply PQle_add_le_sub_l.
        apply (PQadd_le_mono_r _ _ (MQpos x)) in H2.
        rewrite PQsub_add in H2; [ easy | ].
        now apply PQlt_le_incl.
  *simpl; rewrite Hbxz.
   destruct bxz.
  --simpl.
    destruct byz.
   ++exfalso.
     apply Bool.eqb_false_iff in Hbxy.
     apply -> Bool.eqb_true_iff in Hbyz.
     apply -> Bool.eqb_true_iff in Hbxz.
     now rewrite Hbyz, <- Hbxz in Hbxy.
   ++simpl.
     destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H2| H2].
    **simpl; rewrite Hbxz; simpl.
      rewrite PQadd_sub_assoc; [ | now apply PQlt_le_incl ].
      rewrite PQadd_comm.
      rewrite PQadd_sub_assoc; [ | easy ].
      now rewrite PQadd_comm.
    **simpl; rewrite Hbxy.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H3| H3].
    ---exfalso.
       apply PQnle_gt in H3; apply H3.
       apply (PQle_trans _ (MQpos y)); [ | easy ].
       apply PQle_sub_le_add_r.
       rewrite <- PQadd_0_r at 1.
       apply PQadd_le_mono; [ | apply PQle_0_l ].
       now unfold "≤"%PQ.
    ---simpl; symmetry.
       rewrite PQsub_sub_distr.
     +++now apply PQadd_sub_swap.
     +++split; [ easy | ].
        now apply PQle_sub_le_add_r.
  --destruct (PQlt_le_dec (MQpos x - MQpos y) (MQpos z)) as [H2| H2].
   **simpl.
     destruct byz.
   ---simpl; rewrite Hbxy.
      destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H3| H3].
    +++simpl.
       rewrite PQadd_comm.
       apply PQsub_sub_distr.
       split; [ easy | now rewrite PQadd_comm; apply PQlt_le_incl ].
    +++exfalso.
       apply PQle_add_le_sub_l in H3.
       now apply PQnlt_ge in H3.
   ---exfalso.
      apply Bool.eqb_false_iff in Hbxy.
      apply Bool.eqb_false_iff in Hbyz.
      apply Bool.eqb_false_iff in Hbxz.
      now destruct (MQsign x), (MQsign y), (MQsign z).
   **simpl.
     destruct byz.
   ---simpl; rewrite Hbxy.
      destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H3| H3].
    +++exfalso.
       apply PQnlt_ge in H2; apply H2; clear H2.
       apply (PQadd_lt_mono_r _ _ (MQpos y)).
       rewrite PQsub_add; [ | easy ].
       now rewrite PQadd_comm.
    +++simpl; symmetry.
       apply PQsub_add_distr.
   ---exfalso.
      apply Bool.eqb_false_iff in Hbxy.
      apply Bool.eqb_false_iff in Hbyz.
      apply Bool.eqb_false_iff in Hbxz.
      now destruct (MQsign x), (MQsign y), (MQsign z).
-destruct (zerop (PQnum (MQpos (x + y + z)) + PQnum (MQpos (x + (y + z)))))
    as [H1| H1]; [ easy | ].
 apply Bool.eqb_false_iff in Hb1.
 unfold "+"%MQ in Hb1, H1.
 remember (Bool.eqb (MQsign x) (MQsign y)) as bxy eqn:Hbxy.
 remember (Bool.eqb (MQsign x) (MQsign z)) as bxz eqn:Hbxz.
 remember (Bool.eqb (MQsign y) (MQsign z)) as byz eqn:Hbyz.
 symmetry in Hbxy, Hbxz, Hbyz.
 move bxz before bxy; move byz before bxz.
 move Hbxz before Hbxy; move Hbyz before Hbxz.
 destruct bxy.
 +simpl in Hb1, H1.
  apply -> Bool.eqb_true_iff in Hbxy.
  rewrite <- Hbxy, Hbxz in Hbyz; subst byz.
  rewrite <- Hbxy, Hbxz in Hb1, H1.
  destruct bxz.
  *simpl in Hb1, H1.
   rewrite Bool.eqb_reflx in Hb1, H1.
   now simpl in Hb1, H1.
  *destruct (PQlt_le_dec (MQpos x + MQpos y) (MQpos z)) as [H2| H2].
  --simpl in Hb1, H1.
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H3| H3].
   ++simpl in Hb1, H1.
     rewrite Hbxz in Hb1, H1.
     destruct (PQlt_le_dec (MQpos x) (MQpos z - MQpos y)) as [H4| H4].
    **now simpl in Hb1.
    **simpl in Hb1, H1.
      apply PQle_sub_le_add_r in H4.
      now apply PQnlt_ge in H4; apply H4.
   ++apply PQnlt_ge in H3; apply H3.
     eapply PQle_lt_trans; [ | apply H2 ].
     apply PQle_sub_le_add_r.
     rewrite PQsub_diag.
     apply PQle_0_l.
  --simpl in Hb1, H1.
    destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H3| H3].
   ++simpl in Hb1, H1.
     rewrite Hbxz in Hb1, H1.
     destruct (PQlt_le_dec (MQpos x) (MQpos z - MQpos y)) as [H4| H4].
    **simpl in Hb1, H1.
      apply PQlt_add_lt_sub_r in H4.
      now apply PQnlt_ge in H2.
    **easy.
   ++now rewrite Bool.eqb_reflx in Hb1.
 +destruct (PQlt_le_dec (MQpos x) (MQpos y)) as [H2| H2].
  *simpl in Hb1, H1.
   rewrite Hbyz in Hb1, H1.
   destruct byz.
  --simpl in Hb1, H1.
    rewrite Hbxy in Hb1, H1.
    destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H3| H3].
   ++easy.
   ++apply PQnlt_ge in H3; apply H3.
     eapply PQlt_le_trans; [ apply H2 | ].
     rewrite PQadd_comm.
     apply PQle_sub_le_add_r.
     rewrite PQsub_diag.
     apply PQle_0_l.
  --destruct (PQlt_le_dec (MQpos y - MQpos x) (MQpos z)) as [H3| H3].
   ++simpl in Hb1, H1.
     destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H4| H4].
    **simpl in Hb1, H1.
      rewrite Hbxz in Hb1, H1.
      destruct bxz.
    ---simpl in Hb1, H1.
       apply -> Bool.eqb_true_iff in Hbxz.
       now symmetry in Hbxz.
    ---apply Bool.eqb_false_iff in Hbxy.
       apply Bool.eqb_false_iff in Hbxz.
       apply Bool.eqb_false_iff in Hbyz.
       now destruct (MQsign x), (MQsign y), (MQsign z).
    **simpl in Hb1, H1.
      rewrite Hbxy in Hb1, H1.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H5| H5].
    ---apply PQnle_gt in H5; apply H5.
       apply PQle_sub_le_add_r.
       rewrite PQadd_comm.
       now apply PQle_sub_le_add_r, PQlt_le_incl.
    ---simpl in Hb1, H1.
       destruct bxz.
     +++apply -> Bool.eqb_true_iff in Hbxz.
        now symmetry in Hbxz.
     +++apply Bool.eqb_false_iff in Hbxy.
        apply Bool.eqb_false_iff in Hbxz.
        apply Bool.eqb_false_iff in Hbyz.
        now destruct (MQsign x), (MQsign y), (MQsign z).
   ++simpl in Hb1, H1.
     destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H4| H4]; simpl in Hb1, H1.
    **clear Hb1 H1.
      apply PQnlt_ge in H3; apply H3.
      eapply PQle_lt_trans; [ | apply H4 ].
      apply PQle_sub_le_add_r.
      rewrite <- PQadd_0_r at 1.
      apply PQadd_le_mono; [ | apply PQle_0_l ].
      now unfold "≤"%PQ.
    **rewrite Hbxy in Hb1, H1.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H5| H5].
    ---easy.
    ---simpl in Hb1, H1.
       apply PQle_sub_le_add_r in H5.
       rewrite PQadd_comm in H5.
       apply PQle_sub_le_add_r in H5.
       specialize (PQle_antisymm _ _ H3 H5) as H6.
       unfold "=="%PQ in H6.
       unfold PQsub_num in H1.
       rewrite H6, Nat.sub_diag, Nat.add_0_l in H1.
       apply (PQadd_le_mono_r _ _ (MQpos x)) in H3.
       apply (PQadd_le_mono_r _ _ (MQpos x)) in H5.
       rewrite PQsub_add in H3; [ | now apply PQlt_le_incl ].
       rewrite PQsub_add in H5; [ | now apply PQlt_le_incl ].
       rewrite PQadd_comm in H3, H5.
       apply PQle_add_le_sub_r in H3.
       apply PQle_sub_le_add_r in H5.
       specialize (PQle_antisymm _ _ H3 H5) as H7.
       unfold "=="%PQ in H7.
       now rewrite H7, Nat.sub_diag in H1.
  *simpl in Hb1, H1.
   rewrite Hbxz in Hb1, H1.
   destruct bxz; simpl in Hb1, H1.
  --destruct byz; simpl in Hb1, H1.
   ++apply Bool.eqb_false_iff in Hbxy.
     apply -> Bool.eqb_true_iff in Hbxz.
     apply -> Bool.eqb_true_iff in Hbyz.
     now rewrite Hbxz, Hbyz in Hbxy.
   ++destruct (PQlt_le_dec (MQpos y) (MQpos z)) as [H3| H3]; simpl in Hb1, H1.
    **now rewrite Hbxz in Hb1.
    **rewrite Hbxy in Hb1, H1; simpl in Hb1, H1.
      destruct (PQlt_le_dec (MQpos x) (MQpos y - MQpos z)) as [H4| H4].
    ---clear Hb1 H1.
       apply PQnlt_ge in H2; apply H2.
       eapply PQlt_le_trans; [ apply H4 | ].
       apply PQle_sub_le_add_r.
       rewrite PQadd_comm.
       apply PQle_sub_le_add_r.
       rewrite PQsub_diag.
       apply PQle_0_l.
    ---easy.
  --destruct byz; simpl in Hb1, H1.
   ++rewrite Hbxy in Hb1, H1.
     destruct (PQlt_le_dec (MQpos x - MQpos y) (MQpos z)) as [H3| H3].
    **simpl in Hb1, H1.
      destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H4| H4].
    ---simpl in Hb1, H1.
       apply -> Bool.eqb_true_iff in Hbyz.
       now rewrite Hbyz in Hb1.
    ---simpl in Hb1, H1.
       apply PQnle_gt in H3; apply H3.
       now apply PQle_add_le_sub_l.
    **simpl in Hb1, H1.
      destruct (PQlt_le_dec (MQpos x) (MQpos y + MQpos z)) as [H4| H4].
    ---simpl in Hb1, H1.
       apply PQnlt_ge in H3; apply H3.
       apply (PQadd_lt_mono_r _ _ (MQpos y)).
       rewrite PQsub_add; [ | easy ].
       now rewrite PQadd_comm.
    ---easy.
   ++clear Hb1 H1.
     apply Bool.eqb_false_iff in Hbxy.
     apply Bool.eqb_false_iff in Hbxz.
     apply Bool.eqb_false_iff in Hbyz.
     now destruct (MQsign x), (MQsign y), (MQsign z).
Qed.

Theorem MQadd_cancel_r : ∀ x y z, (x + z == y + z)%MQ ↔ (x == y)%MQ.
Proof.
intros.
split.
Focus 2.
intros H.
Set Printing All.
 rewrite H.
...

Theorem MQadd_shuffle0 : ∀ x y z, (x + y + z == x + z + y)%MQ.
Proof.
intros.
do 2 rewrite MQadd_assoc.
setoid_rewrite MQadd_comm.
Search MQadd_cancel_r.
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
