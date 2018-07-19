(* rationals where num and den are always common primes *)

Require Import Utf8 Arith Morphisms.
Require Import PQ Nat_ggcd.
Set Nested Proofs Allowed.

Delimit Scope GQ_scope with GQ.

Record GQ :=
  GQmake
    { PQ_of_GQ : PQ;
      GQprop : Nat.gcd (PQnum1 PQ_of_GQ + 1) (PQden1 PQ_of_GQ + 1) = 1 }.
Arguments GQmake PQ_of_GQ%PQ.

Definition GQ_of_PQ x := GQmake (PQred x) (PQred_gcd x).

Arguments PQ_of_GQ x%GQ : rename.
Arguments GQ_of_PQ x%PQ.

Definition GQ_of_nat n := GQmake (PQ_of_nat n) (Nat.gcd_1_r (n - 1 + 1)).
Definition GQ_of_pair n d := GQ_of_PQ (PQ_of_pair n d).

Notation "1" := (GQmake 1 (Nat.gcd_1_r (0 + 1))) : GQ_scope.

Definition GQadd x y := GQ_of_PQ (PQ_of_GQ x + PQ_of_GQ y).
Definition GQsub x y := GQ_of_PQ (PQ_of_GQ x - PQ_of_GQ y).
Definition GQmul x y := GQ_of_PQ (PQ_of_GQ x * PQ_of_GQ y).

Notation "x + y" := (GQadd x y) : GQ_scope.
Notation "x - y" := (GQsub x y) : GQ_scope.
Notation "x * y" := (GQmul x y) : GQ_scope.

Theorem GQeq_eq : ∀ x y, x = y ↔ (PQ_of_GQ x = PQ_of_GQ y)%PQ.
Proof.
intros.
split; [ now intros; subst x | ].
intros H.
destruct x as (x, xp).
destruct y as (y, yp).
simpl in H; subst x; f_equal.
apply UIP_nat.
Qed.

Instance GQ_of_PQ_morph : Proper (PQeq ==> eq) GQ_of_PQ.
Proof.
intros (xn, xd) (yn, yd) Hxy.
unfold "=="%PQ, nd in Hxy.
simpl in Hxy.
unfold GQ_of_PQ.
apply GQeq_eq; simpl.
unfold PQred; simpl.
remember (Nat.gcd (xn + 1) (xd + 1)) as gx eqn:Hgx.
remember (Nat.gcd (yn + 1) (yd + 1)) as gy eqn:Hgy.
move gy before gx.
specialize (ggcd_split _ _ _ Hgx) as Hx.
specialize (ggcd_split _ _ _ Hgy) as Hy.
rewrite Hx, Hy; simpl.
specialize (ggcd_correct_divisors (xn + 1) (xd + 1)) as H1.
specialize (ggcd_correct_divisors (yn + 1) (yd + 1)) as H3.
rewrite Hx in H1; rewrite Hy in H3.
destruct H1 as (H1, H2).
destruct H3 as (H3, H4).
assert (Hgxz : gx ≠ 0) by now intros H; rewrite H, Nat.add_1_r in H1.
assert (Hgyz : gy ≠ 0) by now intros H; rewrite H, Nat.add_1_r in H3.
f_equal; f_equal.
-rewrite <- (Nat.mul_cancel_l _ _ gx), <- H1; [ | easy ].
 rewrite <- (Nat.mul_cancel_l _ _ gy); [ | easy ].
 rewrite Nat.mul_assoc, Nat.mul_shuffle0, <- H3.
 rewrite Hgy, Nat.mul_comm, <- Nat.gcd_mul_mono_l.
 rewrite Hgx, <- Nat.gcd_mul_mono_l, Hxy, Nat.mul_comm.
 easy.
-rewrite <- (Nat.mul_cancel_l _ _ gx), <- H2; [ | easy ].
 rewrite <- (Nat.mul_cancel_l _ _ gy); [ | easy ].
 rewrite Nat.mul_assoc, Nat.mul_shuffle0, <- H4.
 rewrite Hgy, Nat.mul_comm, <- Nat.gcd_mul_mono_l.
 rewrite Nat.mul_comm, <- Hxy, Nat.gcd_mul_mono_r, <- Hgx.
 apply Nat.mul_comm.
Qed.

Theorem GQ_of_PQred : ∀ x, GQ_of_PQ (PQred x) = GQ_of_PQ x.
Proof.
intros.
unfold GQ_of_PQ.
apply GQeq_eq; simpl.
now rewrite PQred_idemp.
Qed.

Theorem PQred_of_GQ : ∀ x, PQred (PQ_of_GQ x) = PQ_of_GQ x.
Proof.
intros (xp, Hxp); simpl.
unfold PQred.
symmetry in Hxp.
apply ggcd_split in Hxp.
rewrite Hxp.
do 2 rewrite Nat.div_1_r.
do 2 rewrite Nat.add_sub.
now destruct xp.
Qed.

Theorem GQ_of_PQ_additive : ∀ x y,
  GQ_of_PQ (x + y) = (GQ_of_PQ x + GQ_of_PQ y)%GQ.
Proof.
intros.
apply GQeq_eq.
unfold GQ_of_PQ.
remember GQadd as f; simpl; subst f.
unfold "+"%GQ.
remember PQadd as f; simpl; subst f.
now rewrite PQred_add.
Qed.

Theorem GQ_of_PQ_multiplicative : ∀ x y,
  GQ_of_PQ (x * y) = (GQ_of_PQ x * GQ_of_PQ y)%GQ.
Proof.
intros.
apply GQeq_eq.
unfold GQ_of_PQ.
remember GQmul as f; simpl; subst f.
unfold "*"%GQ.
remember PQmul as f; simpl; subst f.
now rewrite PQred_mul.
Qed.

Theorem GQ_o_PQ : ∀ x, GQ_of_PQ (PQ_of_GQ x) = x.
Proof.
intros.
apply GQeq_eq.
unfold GQ_of_PQ; simpl.
rewrite PQred_of_GQ.
now destruct (PQ_of_GQ x).
Qed.

Ltac tac_to_PQ :=
  unfold "+"%GQ, "*"%GQ;
  repeat
  match goal with
  | [ x : GQ |- _ ] =>
      match goal with
      [ |- context[PQ_of_GQ x] ] =>
        let y := fresh "u" in
        let Hy := fresh "Hu" in
        remember (PQ_of_GQ x) as y eqn:Hy
      end
  | _ => idtac
  end;
  repeat rewrite GQ_of_PQ_additive;
  repeat rewrite GQ_of_PQ_multiplicative;
  repeat rewrite GQ_o_PQ;
  repeat rewrite <- GQ_of_PQ_additive;
  repeat rewrite <- GQ_of_PQ_multiplicative;
  repeat rewrite <- GQ_of_PQ_additive.

Theorem GQadd_comm : ∀ x y, (x + y = y + x)%GQ.
Proof.
intros.
tac_to_PQ.
now rewrite PQadd_comm.
Qed.

Theorem GQadd_assoc : ∀ x y z, ((x + y) + z = x + (y + z))%GQ.
Proof.
intros.
tac_to_PQ.
now rewrite PQadd_assoc.
Qed.

Theorem GQmul_comm : ∀ x y, (x * y = y * x)%GQ.
Proof.
intros.
tac_to_PQ.
now rewrite PQmul_comm.
Qed.

Theorem GQmul_assoc : ∀ x y z, ((x * y) * z = x * (y * z))%GQ.
Proof.
intros.
tac_to_PQ.
now rewrite PQmul_assoc.
Qed.

Theorem GQmul_add_distr_l : ∀ x y z, (x * (y + z) = x * y + x * z)%GQ.
Proof.
intros.
tac_to_PQ.
now rewrite PQmul_add_distr_l.
Qed.

Theorem GQmul_mul_swap : ∀ x y z, (x * y * z = x * z * y)%GQ.
Proof.
intros.
tac_to_PQ.
now rewrite PQmul_mul_swap.
Qed.

Definition GQcompare x y := PQcompare (PQ_of_GQ x) (PQ_of_GQ y).
Arguments GQcompare x%GQ y%GQ.

Theorem glop : ∀ x y,
  (PQ_of_GQ x == PQ_of_GQ y)%PQ
  → PQ_of_GQ x = PQ_of_GQ y.
Proof.
(*
intros * H.
rewrite <- PQred_of_GQ in H; symmetry in H.
rewrite <- PQred_of_GQ in H; symmetry in H.
rewrite <- PQred_of_GQ; symmetry.
rewrite <- PQred_of_GQ; symmetry.
remember (PQ_of_GQ x) as x'.
remember (PQ_of_GQ y) as y'.
move y' before x'.
destruct x' as (xn, xd).
destruct y' as (yn, yd); simpl in *.
unfold "=="%PQ, nd in H; simpl in H.
unfold PQred in H |-*.
simpl in H; simpl.
remember (ggcd (xn + 1) (xd + 1)) as gx eqn:Hgx.
remember (ggcd (yn + 1) (yd + 1)) as gy eqn:Hgy.
move gy before gx.
destruct gx as (gx, (aax, bbx)).
destruct gy as (gy, (aay, bby)).
simpl in H.
...
*)
(*
intros * H.
Search PQ_of_GQ.
rewrite <- PQred_of_GQ; symmetry.
rewrite <- PQred_of_GQ; symmetry.
unfold PQred.
...
*)
intros * H.
destruct x as (x, Hx).
destruct y as (y, Hy).
move y before x.
simpl in H; simpl.
destruct x as (xn, xd).
destruct y as (yn, yd).
simpl in *.
unfold "=="%PQ, nd in H.
simpl in H.
Search (Nat.gcd _ _ = 1).
...

assert (PQred (PQ_of_GQ x) = PQred (PQ_of_GQ y)). {
Check GQ_of_PQred.
Search GQ_of_PQ.
...

Theorem GQcompare_eq_iff : ∀ x y, GQcompare x y = Eq ↔ x = y.
Proof.
intros.
split; intros H.
-unfold GQcompare in H.
 apply PQcompare_eq_iff in H.
 apply GQeq_eq.
...
 destruct x as (x, Hx).
 destruct y as (y, Hy).
 move y before x.
 simpl in H; simpl.
 destruct x as (xn, xd).
 destruct y as (yn, yd).
 simpl in *.
 unfold "=="%PQ, nd in H.
 simpl in H.
Search (Nat.gcd _ _ = 1).
...

 f_equal.
 +apply (Nat.add_cancel_r _ _ 1).
  apply (Nat.mul_cancel_r _ _ (yd + 1)); [ flia | ].
  rewrite H.

...
Search PQ_of_GQ.
Search (_ == _)%PQ.
...
Proof. intros; apply Nat.compare_eq_iff. Qed.

Theorem GQcompare_lt_iff : ∀ x y, GQcompare x y = Lt ↔ (x < y)%GQ.
Proof. intros; apply Nat.compare_lt_iff. Qed.

Theorem GQcompare_gt_iff : ∀ x y, GQcompare x y = Gt ↔ (x > y)%GQ.
Proof. intros; apply Nat.compare_gt_iff. Qed.

Ltac GQcompare_iff :=
  match goal with
  | [ H : GQcompare _ _ = Eq |- _ ] => apply GQcompare_eq_iff in H
  | [ H : GQcompare _ _ = Lt |- _ ] => apply GQcompare_lt_iff in H
  | [ H : GQcompare _ _ = Gt |- _ ] => apply GQcompare_gt_iff in H
  end.

Theorem GQcompare_swap : ∀ {A} {a b c : A} px py,
  match GQcompare px py with
  | Eq => a
  | Lt => b
  | Gt => c
  end =
  match GQcompare py px with
  | Eq => a
  | Lt => c
  | Gt => b
  end.
Proof.
intros.
remember (GQcompare px py) as b1 eqn:Hb1; symmetry in Hb1.
remember (GQcompare py px) as b2 eqn:Hb2; symmetry in Hb2.
move b2 before b1.
destruct b1, b2; try easy; repeat GQcompare_iff.
-now rewrite Hb1 in Hb2; apply PQlt_irrefl in Hb2.
-now rewrite Hb1 in Hb2; apply PQlt_irrefl in Hb2.
-now rewrite Hb2 in Hb1; apply PQlt_irrefl in Hb1.
-now apply PQnle_gt in Hb2; exfalso; apply Hb2; apply PQlt_le_incl.
-now rewrite Hb2 in Hb1; apply PQlt_irrefl in Hb1.
-now apply PQnle_gt in Hb2; exfalso; apply Hb2; apply PQlt_le_incl.
Qed.

(* *)

Delimit Scope NQ_scope with NQ.

Inductive NQ :=
  | NQ0 : NQ
  | NQpos : GQ → NQ
  | NQneg : GQ → NQ.
Arguments NQpos p%GQ.
Arguments NQneg p%GQ.

Notation "0" := (NQ0) : NQ_scope.
Notation "1" := (NQpos 1) : NQ_scope.

Definition NQ_of_nat n :=
  match n with
  | 0 => NQ0
  | S _ => NQpos (GQ_of_nat n)
  end.

Definition NQ_of_pair n d := NQpos (GQ_of_pair n d).

Definition NQadd_pos_l px y :=
  match y with
  | NQ0 => NQpos px
  | NQpos py => NQpos (px + py)
  | NQneg py =>
      match GQcompare px py with
      | Eq => NQ0
      | Lt => NQneg (py - px)
      | Gt => NQpos (px - py)
      end
  end.

Definition NQadd_neg_l px y :=
  match y with
  | NQ0 => NQneg px
  | NQpos py =>
      match GQcompare px py with
      | Eq => NQ0
      | Lt => NQpos (py - px)
      | Gt => NQneg (px - py)
      end
  | NQneg py => NQneg (px + py)
  end.

Definition NQadd x y :=
  match x with
  | NQ0 => y
  | NQpos px => NQadd_pos_l px y
  | NQneg px => NQadd_neg_l px y
  end.

Definition NQopp x :=
  match x with
  | NQ0 => NQ0
  | NQpos px => NQneg px
  | NQneg px => NQpos px
  end.

Notation "- x" := (NQopp x) : NQ_scope.
Notation "x + y" := (NQadd x y) : NQ_scope.
Notation "x - y" := (NQadd x (NQopp y)) : NQ_scope.

Definition NQmul_pos_l px y :=
  match y with
  | NQ0 => NQ0
  | NQpos py => NQpos (px * py)
  | NQneg py => NQneg (px * py)
  end.

Definition NQmul_neg_l px y :=
  match y with
  | NQ0 => NQ0
  | NQpos py => NQneg (px * py)
  | NQneg py => NQpos (px * py)
  end.

Definition NQmul x y :=
  match x with
  | NQ0 => NQ0
  | NQpos px => NQmul_pos_l px y
  | NQneg px => NQmul_neg_l px y
  end.

Theorem NQadd_comm : ∀ x y, (x + y = y + x)%NQ.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py]; try easy; simpl.
-f_equal; apply GQadd_comm.
-now rewrite GQcompare_swap; destruct (GQcompare py px).
-now rewrite PQcompare_swap; destruct (PQcompare py px).
-f_equal; apply PQadd_comm.
Qed.
