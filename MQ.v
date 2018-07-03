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

Theorem MQadd_add_swap : ∀ x y z, x + y + z = x + z + y.
Proof.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl.
-f_equal; apply PQadd_comm.
-now rewrite PQcompare_comm; destruct (PQcompare pz py).
-now rewrite PQcompare_comm; destruct (PQcompare pz py).
-f_equal; apply PQadd_comm.
-now destruct (PQcompare px pz).
-f_equal; apply PQadd_add_swap.
-remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
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
  *now f_equal; apply PQsub_add_distr.
 +apply PQnle_gt in Hc2.
  exfalso; apply Hc2; apply PQlt_le_incl.
  apply (PQlt_trans _ (px + py)); [ | easy ].
  apply PQlt_add_r.
 +f_equal.
(* est-ce que c'est bon, ça ? Si c'est pas bon, alors le théorème est
   faux et il faut que je l'applique avec "==", pas avec "=" *)
...

(*
Ltac MQadd_assoc_morph_tac :=
  match goal with
  | [ px : PQ, py : PQ, pz : PQ |- _ : (_ + _ + _ == _ + (_ + _))%PQ ] =>
    apply PQadd_assoc
  | [ px : PQ, py : PQ, pz : PQ |- _ ] =>
    simpl;
    remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1;
    remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2;
    remember (PQcompare px (pz - py)) as c3 eqn:Hc3; symmetry in Hc3;
    move c2 before c1; move c3 before c2;
    destruct c1, c2; repeat PQcompare_iff;
    simpl;
    try (rewrite Hc3; destruct c3; (try easy; repeat PQcompare_iff))
  | _ => idtac
  end.
*)

(*
Ltac MQadd_assoc_morph_tac2 :=
  match goal with
  | [ px : PQ, py : PQ, pz : PQ |- _ : (_ + _ + _ == _ + (_ + _))%PQ ] =>
    apply PQadd_assoc
  | [ px : PQ, py : PQ, pz : PQ |- _ ] =>
    simpl;
    remember (PQcompare pz (py + px) pz) as c1 eqn:Hc1; symmetry in Hc1;
    remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2;
    remember (PQcompare px (pz - py)) as c3 eqn:Hc3; symmetry in Hc3;
    move c2 before c1; move c3 before c2;
    destruct c1, c2; repeat PQcompare_iff;
    simpl;
    try (rewrite Hc3; destruct c3; (try easy; repeat PQcompare_iff))
  | _ => idtac
  end.
*)

Theorem MQmatch_match : ∀ A u v (f00 : A) f0p f0n fp0 fpp fpn fn0 fnp fnn,
  match u with
  | 0 =>
      match v with 0 => f00 | MQpos pv => f0p pv | MQneg pv => f0n pv end
  | MQpos pu =>
      match v with
      | 0 => fp0 pu | MQpos pv => fpp pu pv | MQneg pv => fpn pu pv
      end
  | MQneg nu =>
      match v with
      | 0 => fn0 nu | MQpos pv => fnp nu pv | MQneg pv => fnn nu pv
      end
  end =
  match v with
  | 0 =>
      match u with 0 => f00 | MQpos pu => fp0 pu | MQneg pu => fn0 pu end
  | MQpos pv =>
      match u with
      | 0 => f0p pv | MQpos pu => fpp pu pv | MQneg pu => fnp pu pv
      end
  | MQneg nv =>
      match u with
      | 0 => f0n nv | MQpos pu => fpn pu nv | MQneg pu => fnn pu nv
      end
  end.
Proof.
intros.
now destruct u, v.
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
unfold "=="%MQ.
rewrite MQmatch_match.
...
intros.
rewrite MQadd_comm.
remember (x + y) as t eqn:H.
assert (Ht : t == x + y) by now subst t.
rewrite MQadd_comm in Ht; rewrite Ht.
clear t H Ht.
unfold "=="%MQ.
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy;
  try apply PQadd_comm.
-now simpl; rewrite PQcompare_comm; destruct (PQcompare py pz).
-now simpl; rewrite PQcompare_comm; destruct (PQcompare py pz).
-now simpl; rewrite PQcompare_comm; destruct (PQcompare px pz).
-simpl; rewrite <- PQadd_assoc, PQadd_comm; apply PQadd_cancel_l, PQadd_comm.
-simpl.
 remember (PQcompare pz (py + px)) as c1 eqn:Hc1; symmetry in Hc1.
 remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
 remember (PQcompare px (pz - py)) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c1, c2; repeat PQcompare_iff; simpl; try rewrite Hc3.
 +rewrite Hc2, PQadd_comm in Hc1; symmetry in Hc1; revert Hc1.
  apply PQadd_no_neutral.
 +destruct c3; [ easy | | ]; PQcompare_iff.
  *rewrite PQadd_comm in Hc1.
   rewrite (PQsub_morph py py pz (px + py)) in Hc3; [ | easy | easy | easy ].
   rewrite PQadd_sub in Hc3.
   now apply PQlt_irrefl in Hc3.
  *rewrite PQadd_comm in Hc1.
   rewrite (PQsub_morph py py pz (px + py)) in Hc3; [ | easy | easy | easy ].
   rewrite PQadd_sub in Hc3.
   now apply PQlt_irrefl in Hc3.
 +rewrite Hc1 in Hc2.
  apply PQnle_gt in Hc2; apply Hc2; clear Hc2.
  apply PQlt_le_incl, PQlt_add_r.
 +rewrite (PQsub_morph pz pz (py + px) (px + pz)); [ | easy | easy | ].
  *apply PQadd_sub.
  *now rewrite Hc2, PQadd_comm.
 +destruct c3; PQcompare_iff.
  *rewrite PQadd_comm, Hc3 in Hc1.
   rewrite PQsub_add in Hc1; [ | easy ].
   now apply PQlt_irrefl in Hc1.
  *apply PQnle_gt in Hc3; apply Hc3; clear Hc3.
   apply (PQadd_le_mono_r _ _ py).
   rewrite PQsub_add; [ | easy ].
   now rewrite PQadd_comm; apply PQlt_le_incl.
  *rewrite PQsub_sub_distr; [ | easy | easy ].
   apply PQsub_morph; [ easy | easy | apply PQadd_comm ].
 +rewrite PQadd_sub_assoc; [ | easy ].
  apply PQsub_morph; [ easy | easy | apply PQadd_comm ].
 +rewrite Hc2 in Hc1.
  apply PQnle_gt in Hc1; apply Hc1; clear Hc1.
  apply PQlt_le_incl; apply PQlt_add_r.
 +destruct c3; PQcompare_iff.
  *rewrite PQadd_comm, Hc3 in Hc1.
   rewrite PQsub_add in Hc1; [ | easy ].
   now apply PQlt_irrefl in Hc1.
  *now apply PQsub_add_distr.
  *apply PQnle_gt in Hc3; apply Hc3; clear Hc3.
   apply (PQadd_le_mono_r _ _ py).
   rewrite PQsub_add; [ | easy ].
   rewrite PQadd_comm.
   now apply PQlt_le_incl.
 +apply PQnle_gt in Hc1; apply Hc1; clear Hc1.
  apply PQlt_le_incl, (PQlt_trans _ py); [ easy | ].
  apply PQlt_add_r.
-now simpl; rewrite PQcompare_comm; destruct (PQcompare px py).
-simpl.
 remember (PQcompare py px) as c1 eqn:Hc1; symmetry in Hc1.
 remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
 destruct c1, c2; simpl; repeat PQcompare_iff.
 +now symmetry in Hc2; transitivity py.
 +now rewrite <- Hc1, PQadd_comm, PQsub_add.
 +symmetry in Hc1.
  rewrite (PQcompare_morph px py Hc1 (py - pz) (py - pz)); [ | easy ].
  remember (PQcompare py (py - pz)) as c3 eqn:Hc3; symmetry in Hc3.
  destruct c3; simpl; PQcompare_iff.
  *now symmetry in Hc3; apply PQsub_no_neutral in Hc3.
  *idtac.
...
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy;
  MQadd_assoc_morph_tac.
-now simpl; destruct (PQcompare py pz).
-now simpl; destruct (PQcompare py pz).
-now simpl; destruct (PQcompare px pz).
(**)
-rewrite Hc2 in Hc1.
 now apply PQadd_no_neutral in Hc1.
-apply (PQsub_morph py py) in Hc1; [ | apply PQlt_add_l | easy ].
 rewrite <- Hc1, PQadd_sub in Hc3.
 now apply PQlt_irrefl in Hc3.
-apply (PQsub_morph py py) in Hc1; [ | apply PQlt_add_l | easy ].
 rewrite <- Hc1, PQadd_sub in Hc3.
 now apply PQlt_irrefl in Hc3.
-rewrite <- Hc1 in Hc2; apply PQnle_gt in Hc2.
 apply Hc2, PQlt_le_incl, PQlt_add_l.
-rewrite <- Hc2 in Hc1; apply PQnle_gt in Hc1.
 apply Hc1, PQlt_le_incl, PQlt_add_l.
-rewrite Hc3 in Hc1.
 rewrite PQsub_add in Hc1; [ | easy ].
 now apply PQlt_irrefl in Hc1.
-rewrite PQsub_add_distr; [ | easy ].
 now apply PQsub_sub_swap.
-apply PQnle_gt in Hc3; apply Hc3; clear Hc3.
 apply (PQadd_le_mono_r _ _ py).
 rewrite PQsub_add; [ | easy ].
 now apply PQlt_le_incl.
-apply PQnle_gt in Hc2; apply Hc2; clear Hc2.
 apply PQlt_le_incl.
 apply (PQlt_trans _ (px + py)); [ apply PQlt_add_l | easy ].
-rewrite <- Hc2 in Hc1.
 rewrite <- (PQsub_morph py pz); [ | apply Hc1 | easy | easy ].
 apply PQadd_sub.
-idtac.

...
-simpl; apply PQadd_assoc.
-remember (MQpos px + MQpos py + MQneg pz) as u eqn:Hu.
 remember (MQpos px + (MQpos py + MQneg pz)) as v eqn:Hv.
 symmetry in Hu, Hv; move v before u.
 destruct u as [| pu| pu], v as [| pv| pv]; try easy.
 +simpl in Hu, Hv.
  remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
  remember (PQcompare py pz) as cyz eqn:Hcyz; symmetry in Hcyz.
  destruct c1; [ | easy | easy ].
  apply PQcompare_eq_iff in Hc1.
  destruct cyz.
  *apply PQcompare_eq_iff in Hcyz; rewrite Hcyz in Hc1.
   now apply PQadd_no_neutral in Hc1.
  *apply PQcompare_lt_iff in Hcyz.
   remember (MQadd_PQ_l px (MQneg (pz - py))) as c eqn:Hc; symmetry in Hc.
   destruct c; [ easy | | easy ].
   simpl in Hc.
   remember (PQcompare px (pz - py)) as c2 eqn:Hc2; symmetry in Hc2.
   destruct c2; [ easy | easy | ].
   apply PQcompare_gt_iff in Hc2.
   apply (PQsub_morph py py) in Hc1; [ | apply PQlt_add_l | easy ].
   rewrite <- Hc1, PQadd_sub in Hc2.
   now apply PQlt_irrefl in Hc2.
...
  *apply PQcompare_gt_iff in Hcyz.
   rewrite <- Hc1 in Hcyz; apply PQnle_gt in Hcyz.
   apply Hcyz, PQlt_le_incl, PQlt_add_l.
 +simpl in Hu, Hv.
  remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; [ | easy | easy ].
  apply PQcompare_eq_iff in Hc1; clear Hu.
  remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
  destruct c2; [ easy | | easy ].
  apply PQcompare_lt_iff in Hc2; simpl in Hv.
  remember (PQcompare px (pz - py)) as c3 eqn:Hc3; symmetry in Hc3.
  destruct c3; [ easy | | easy ].
  apply PQcompare_lt_iff in Hc3.
  rewrite (PQsub_morph py py pz (px + py)) in Hc3; [ | easy | easy | easy ].
  rewrite PQadd_sub in Hc3.
  now apply PQlt_irrefl in Hc3.
 +simpl in Hu, Hv.
  remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; [ easy | easy | ].
  apply PQcompare_gt_iff in Hc1; clear Hu.
  remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
  destruct c2; [ easy | | easy ].
  apply PQcompare_lt_iff in Hc2; simpl in Hv.
  remember (PQcompare px (pz - py)) as c3 eqn:Hc3; symmetry in Hc3.
  destruct c3; [ | easy | easy ].
  apply PQcompare_eq_iff in Hc3; clear Hv.
  rewrite Hc3 in Hc1.
  apply PQnle_gt in Hc1; apply Hc1; clear Hc1.
  rewrite PQsub_add; [ apply PQle_refl | easy ].
 +simpl in Hu, Hv.
  remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; [ easy | easy | ].
  apply PQcompare_gt_iff in Hc1.
  injection Hu; clear Hu; intros; subst pu.
  remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
  destruct c2; simpl in Hv.
  *apply PQcompare_eq_iff in Hc2.
   injection Hv; clear Hv; intros Hv; subst pv.
   symmetry in Hc2.
   rewrite (PQsub_morph pz py (px + py) (px + py)); [ | easy | easy | easy ].
   apply PQadd_sub.
  *apply PQcompare_lt_iff in Hc2.
   remember (PQcompare px (pz - py)) as c3 eqn:Hc3; symmetry in Hc3.
   destruct c3; [ easy | easy | ].
   apply PQcompare_gt_iff in Hc3.
   injection Hv; clear Hv; intros; subst pv.
   now symmetry; apply PQsub_sub_distr.
  *apply PQcompare_gt_iff in Hc2.
   injection Hv; clear Hv; intros; subst pv.
   now symmetry; apply PQadd_sub_assoc.
 +simpl in Hu, Hv.
  remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; [ easy | easy | ].
  apply PQcompare_gt_iff in Hc1.
  injection Hu; clear Hu; intros; subst pu.
  remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
  destruct c2; simpl in Hv; [ easy | | easy ].
  apply PQcompare_lt_iff in Hc2.
  remember (PQcompare px (pz - py)) as c3 eqn:Hc3; symmetry in Hc3.
  destruct c3; [ easy | | easy ].
  apply PQcompare_lt_iff in Hc3.
  injection Hv; clear Hv; intros; subst pv.
  apply PQnle_gt in Hc1; apply Hc1; clear Hc1.
  apply (PQadd_lt_mono_r _ _ py) in Hc3.
  rewrite PQsub_add in Hc3; [ | easy ].
  now apply PQlt_le_incl.
 +simpl in Hu, Hv.
  remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; [ easy | | easy ].
  apply PQcompare_lt_iff in Hc1.
  injection Hu; clear Hu; intros; subst pu.
  remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
  destruct c2; simpl in Hv; [ easy | | easy ].
  apply PQcompare_lt_iff in Hc2.
  remember (PQcompare px (pz - py)) as c3 eqn:Hc3; symmetry in Hc3.
  destruct c3; [ | easy | easy ].
  apply PQcompare_eq_iff in Hc3; clear Hv.
  rewrite Hc3 in Hc1.
  rewrite PQsub_add in Hc1; [ | easy ].
  now apply PQlt_irrefl in Hc1.
 +simpl in Hu, Hv.
  remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; [ easy | | easy ].
  apply PQcompare_lt_iff in Hc1.
  injection Hu; clear Hu; intros; subst pu.
  remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
  destruct c2; simpl in Hv.
  *apply PQcompare_eq_iff in Hc2.
   injection Hv; clear Hv; intros; subst pv.
   rewrite Hc2 in Hc1.
   apply PQnle_gt in Hc1; apply Hc1.
   apply PQlt_le_incl, PQlt_add_l.
  *apply PQcompare_lt_iff in Hc2.
   remember (PQcompare px (pz - py)) as c3 eqn:Hc3; symmetry in Hc3.
   destruct c3; [ easy | easy | ].
   apply PQcompare_gt_iff in Hc3.
   injection Hv; clear Hv; intros; subst pv.
   apply PQnle_gt in Hc3; apply Hc3; clear Hc3.
   apply (PQadd_le_mono_r _ _ py).
   rewrite PQsub_add; [ | easy ].
   now apply PQlt_le_incl.
  *apply PQcompare_gt_iff in Hc2.
   injection Hv; clear Hv; intros; subst pv.
   apply PQnle_gt in Hc2; apply Hc2; clear Hc2.
   apply (PQadd_le_mono_l _ _ px).
   apply PQlt_le_incl.
   eapply PQlt_trans; [ apply Hc1 | apply PQlt_add_l ].
 +simpl in Hu, Hv.
  remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
  destruct c1; [ easy | | easy ].
  apply PQcompare_lt_iff in Hc1.
  injection Hu; clear Hu; intros; subst pu.
  remember (PQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
  destruct c2; simpl in Hv; [ easy | | easy ].
  apply PQcompare_lt_iff in Hc2.
  remember (PQcompare px (pz - py)) as c3 eqn:Hc3; symmetry in Hc3.
  destruct c3; [ easy | | easy ].
  apply PQcompare_lt_iff in Hc3.
  injection Hv; clear Hv; intros; subst pv.
Search (_ - _ - _)%PQ.
Search (_ - (_ + _))%PQ.
Require Import ZArith.
Search (_ - _ - _)%positive.
Search (_ - (_ + _))%positive.
Check Pos.sub_add_distr.
...
  apply PQsub_add_assoc.

  now symmetry; apply PQsub_sub_distr.
  *apply PQcompare_gt_iff in Hc2.
   injection Hv; clear Hv; intros; subst pv.
   now symmetry; apply PQadd_sub_assoc.
...
 simpl.
 remember (PQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
 remember (PQcompare py pz) as cyz eqn:Hcyz; symmetry in Hcyz.
 destruct c1.
 +apply PQcompare_eq_iff in Hc1.
  destruct cyz.
  *apply PQcompare_eq_iff in Hcyz; rewrite Hcyz in Hc1.
   now apply PQadd_no_neutral in Hc1.
  *apply PQcompare_lt_iff in Hcyz.
   remember (MQadd_PQ_l px (MQneg (pz - py))) as c eqn:Hc; symmetry in Hc.
simpl in Hc.
   destruct c; [ easy | | ].
  --simpl in Hc.
    remember (PQcompare px (pz - py)) as c2 eqn:Hc2; symmetry in Hc2.
    destruct c2; [ easy | easy | ].
    apply PQcompare_gt_iff in Hc2.
    apply (PQsub_morph py py) in Hc1; [ | apply PQlt_add_l | easy ].
    rewrite <- Hc1, PQadd_sub in Hc2.
    now apply PQlt_irrefl in Hc2.
  --simpl in Hc.
    remember (PQcompare px (pz - py)) as c2 eqn:Hc2; symmetry in Hc2.
    destruct c2; [ easy | | easy ].
    apply PQcompare_lt_iff in Hc2.
    rewrite (PQsub_morph py py pz (px + py)) in Hc2; [ | easy | easy | easy ].
    rewrite PQadd_sub in Hc2.
    now apply PQlt_irrefl in Hc2.
  *apply PQcompare_gt_iff in Hcyz; simpl.
   rewrite <- Hc1 in Hcyz; apply PQnle_gt in Hcyz.
   apply Hcyz, PQlt_le_incl, PQlt_add_l.
 +apply PQcompare_lt_iff in Hc1.
  destruct cyz.
  *apply PQcompare_eq_iff in Hcyz; simpl.
   rewrite Hcyz in Hc1; apply PQnle_gt in Hc1.
   apply Hc1, PQlt_le_incl, PQlt_add_l.
  *apply PQcompare_lt_iff in Hcyz.

...
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

Theorem MQadd_add_swap : ∀ x y z, (x + y + z == x + z + y)%MQ.
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
