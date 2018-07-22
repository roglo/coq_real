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
Arguments GQadd x%GQ y%GQ.
Arguments GQsub x%GQ y%GQ.
Arguments GQmul x%GQ y%GQ.

Notation "x + y" := (GQadd x y) : GQ_scope.
Notation "x - y" := (GQsub x y) : GQ_scope.
Notation "x * y" := (GQmul x y) : GQ_scope.

Definition GQlt x y := PQlt (PQ_of_GQ x) (PQ_of_GQ y).
Definition GQle x y := PQle (PQ_of_GQ x) (PQ_of_GQ y).
Definition GQgt x y := GQlt y x.
Definition GQge x y := GQle y x.

Notation "x < y" := (GQlt x y) : GQ_scope.
Notation "x ≤ y" := (GQle x y) : GQ_scope.
Notation "x > y" := (GQgt x y) : GQ_scope.
Notation "x ≥ y" := (GQge x y) : GQ_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%GQ (at level 70, y at next level) :
  GQ_scope.

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

Theorem GQle_refl : ∀ x, (x ≤ x)%GQ.
Proof. intros; apply PQle_refl. Qed.

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

Theorem GQ_of_PQ_subtractive : ∀ x y,
  (y < x)%PQ → GQ_of_PQ (x - y) = (GQ_of_PQ x - GQ_of_PQ y)%GQ.
Proof.
intros * Hyx.
apply GQeq_eq.
unfold GQ_of_PQ.
remember GQsub as f; simpl; subst f.
unfold "-"%GQ.
remember GQsub as f; simpl; subst f.
now apply PQred_sub.
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

Theorem PQ_o_GQ : ∀ x, (PQ_of_GQ (GQ_of_PQ x) == x)%PQ.
Proof.
intros.
unfold "=="%PQ, nd; simpl.
unfold PQred.
remember (ggcd (PQnum1 x + 1) (PQden1 x + 1)) as g eqn:Hg.
erewrite ggcd_split in Hg; [ | easy ].
subst g; simpl.
specialize (Nat.gcd_divide_l (PQnum1 x + 1) (PQden1 x + 1)) as (c1, Hc1).
specialize (Nat.gcd_divide_r (PQnum1 x + 1) (PQden1 x + 1)) as (c2, Hc2).
move c2 before c1.
rewrite Hc1 at 1.
assert (Hg : Nat.gcd (PQnum1 x + 1) (PQden1 x + 1) ≠ 0). {
  intros H; rewrite H in Hc1; flia Hc1.
}
rewrite Nat.div_mul; [ | easy ].
symmetry; rewrite Nat.mul_comm.
rewrite Hc2 at 1.
rewrite Nat.div_mul; [ | easy ].
symmetry; rewrite Nat.mul_comm.
rewrite Nat.sub_add.
-rewrite Nat.sub_add.
 +rewrite Hc1.
  rewrite Hc2 at 1.
  now rewrite Nat.mul_assoc, Nat.mul_shuffle0.
 +destruct c2; [ flia Hc2 | flia ].
-destruct c1; [ flia Hc1 | flia ].
Qed.

Theorem PQ_of_GQ_additive : ∀ x y,
  (PQ_of_GQ (x + y) == PQ_of_GQ x + PQ_of_GQ y)%PQ.
Proof.
intros.
remember (PQ_of_GQ x) as x'.
remember (PQ_of_GQ y) as y'.
move y' before x'.
specialize (GQ_o_PQ x) as H; rewrite <- H, <- Heqx'; clear H.
specialize (GQ_o_PQ y) as H; rewrite <- H, <- Heqy'; clear H.
clear x y Heqx' Heqy'; rename x' into x; rename y' into y.
rewrite <- GQ_of_PQ_additive.
apply PQ_o_GQ.
Qed.

Theorem PQ_of_GQ_subtractive : ∀ x y,
  (y < x)%GQ → (PQ_of_GQ (x - y) == PQ_of_GQ x - PQ_of_GQ y)%PQ.
Proof.
intros * Hyx.
remember (PQ_of_GQ x) as x'.
remember (PQ_of_GQ y) as y'.
move y' before x'.
specialize (GQ_o_PQ x) as H; rewrite <- H, <- Heqx'; clear H.
specialize (GQ_o_PQ y) as H; rewrite <- H, <- Heqy'; clear H.
rewrite <- GQ_of_PQ_subtractive; [ apply PQ_o_GQ | ].
now subst x' y'.
Qed.

Ltac tac_to_PQ :=
  unfold "+"%GQ, "-"%GQ, "*"%GQ;
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

Theorem GQadd_add_swap : ∀ x y z, (x + y + z = x + z + y)%GQ.
Proof.
intros.
tac_to_PQ.
now rewrite PQadd_add_swap.
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

Theorem GQadd_lt_mono_r : ∀ x y z, (x < y)%GQ ↔ (x + z < y + z)%GQ.
Proof.
intros.
unfold "+"%GQ, "<"%GQ.
do 2 rewrite GQ_of_PQ_additive.
do 2 rewrite PQ_of_GQ_additive.
do 3 rewrite PQ_o_GQ.
apply PQadd_lt_mono_r.
Qed.

Theorem GQsub_add : ∀ x y, (y < x)%GQ → (x - y + y)%GQ = x.
Proof.
intros * Hyx.
unfold "+"%GQ, "-"%GQ, "<"%GQ.
rewrite GQ_of_PQ_additive.
remember (PQ_of_GQ x) as x'.
remember (PQ_of_GQ y) as y'.
move y' before x'.
assert (Hyx' : (y' < x')%PQ) by now subst.
rewrite GQ_of_PQ_subtractive; [ | easy ].
rewrite GQ_o_PQ.
rewrite <- GQ_of_PQ_subtractive; [ | easy ].
rewrite <- GQ_of_PQ_additive.
rewrite PQsub_add; [ | easy ].
subst x'; apply GQ_o_PQ.
Qed.

Theorem GQlt_irrefl : ∀ x, ¬ (x < x)%GQ.
Proof. intros; apply PQlt_irrefl. Qed.

Theorem GQnle_gt : ∀ x y, ¬ (x ≤ y)%GQ ↔ (y < x)%GQ.
Proof. intros; apply PQnle_gt. Qed.

Theorem GQlt_le_incl : ∀ x y, (x < y)%GQ → (x ≤ y)%GQ.
Proof. intros x y; apply PQlt_le_incl. Qed.

Theorem GQlt_trans : ∀ x y z, (x < y)%GQ → (y < z)%GQ → (x < z)%GQ.
Proof. intros x y z; apply PQlt_trans. Qed.

Theorem GQsub_lt : ∀ x y, (y < x)%GQ → (x - y < x)%GQ.
Proof.
intros x y z.
unfold "-"%GQ, "<"%GQ.
rewrite GQ_of_PQ_subtractive; [ | easy ].
do 2 rewrite GQ_o_PQ.
rewrite PQ_of_GQ_subtractive; [ | easy ].
now apply PQsub_lt.
Qed.

Theorem GQadd_sub : ∀ x y, (x + y - y)%GQ = x.
Proof.
intros.
unfold "+"%GQ, "-"%GQ.
remember (PQ_of_GQ x) as x'.
remember (PQ_of_GQ y) as y'.
assert (Hyx : (y' < x' + y')%PQ) by apply PQlt_add_l.
rewrite GQ_of_PQ_additive.
rewrite GQ_of_PQ_subtractive.
-rewrite GQ_o_PQ.
 rewrite <- GQ_of_PQ_additive.
 rewrite <- GQ_of_PQ_subtractive; [ | easy ].
 rewrite PQadd_sub.
 now rewrite Heqx', GQ_o_PQ.
-rewrite PQ_of_GQ_additive.
 now do 2 rewrite PQ_o_GQ.
Qed.

Theorem GQlt_add_r : ∀ x y, (x < x + y)%GQ.
Proof.
intros x y.
unfold "<"%GQ, "+"%GQ.
remember (PQ_of_GQ x) as x'.
remember (PQ_of_GQ y) as y'.
rewrite PQ_o_GQ.
apply PQlt_add_r.
Qed.

Theorem GQsub_add_distr : ∀ x y z,
  (y + z < x)%GQ → (x - (y + z))%GQ = (x - y - z)%GQ.
Proof.
intros * Hyzx.
revert Hyzx.
unfold "+"%GQ, "-"%GQ, "<"%GQ; intros.
remember (PQ_of_GQ x) as x' eqn:Hx'.
remember (PQ_of_GQ y) as y' eqn:Hy'.
remember (PQ_of_GQ z) as z' eqn:Hz'.
rewrite PQ_o_GQ in Hyzx.
rewrite GQ_of_PQ_additive.
assert (Hyx : (y' < x')%PQ). {
  eapply PQlt_trans; [ | apply Hyzx ].
  apply PQlt_add_r.
}
assert (Hzxy : (z' < x' - y')%PQ). {
  apply (PQadd_lt_mono_r _ _ y').
  rewrite PQsub_add; [ | easy ].
  now rewrite PQadd_comm.
}
rewrite GQ_of_PQ_subtractive.
-rewrite GQ_of_PQ_subtractive; [ | now rewrite PQ_o_GQ ].
 rewrite GQ_of_PQ_subtractive; [ | easy ].
 do 2 rewrite GQ_o_PQ.
 rewrite <- GQ_of_PQ_subtractive; [ | easy ].
 rewrite <- GQ_of_PQ_subtractive; [ | easy ].
 rewrite <- GQ_of_PQ_additive.
 rewrite <- GQ_of_PQ_subtractive; [ | easy ].
 now rewrite PQsub_add_distr.
-rewrite PQ_of_GQ_additive.
 now do 2 rewrite PQ_o_GQ.
Qed.

Theorem GQsub_sub_distr : ∀ x y z,
  (z < y)%GQ → (y - z < x)%GQ → (x - (y - z))%GQ = (x + z - y)%GQ.
Proof.
intros * Hzy Hyzx.
revert Hzy Hyzx.
unfold "+"%GQ, "-"%GQ, "<"%GQ; intros.
remember (PQ_of_GQ x) as x' eqn:Hx'.
remember (PQ_of_GQ y) as y' eqn:Hy'.
remember (PQ_of_GQ z) as z' eqn:Hz'.
move x' after y'; move z' before y'.
move Hx' after Hy'.
rewrite PQ_o_GQ in Hyzx.
rewrite GQ_of_PQ_additive.
assert (Hyxz : (y' < x' + z')%PQ). {
  apply (PQadd_lt_mono_r _ _ z') in Hyzx.
  now rewrite PQsub_add in Hyzx.
}
rewrite GQ_of_PQ_subtractive; [ | now rewrite PQ_o_GQ ].
rewrite GQ_of_PQ_subtractive; [ | easy ].
rewrite GQ_of_PQ_subtractive.
-do 2 rewrite GQ_o_PQ.
 rewrite <- GQ_of_PQ_subtractive; [ | easy ].
 rewrite <- GQ_of_PQ_subtractive; [ | easy ].
 rewrite <- GQ_of_PQ_additive.
 rewrite <- GQ_of_PQ_subtractive; [ | easy ].
 now rewrite PQsub_sub_distr.
-rewrite PQ_of_GQ_additive.
 now do 2 rewrite PQ_o_GQ.
Qed.

Theorem GQadd_sub_assoc : ∀ x y z,
  (z < y)%GQ → (x + (y - z))%GQ = (x + y - z)%GQ.
Proof.
intros * Hzy.
revert Hzy.
unfold "+"%GQ, "-"%GQ, "<"%GQ; intros.
remember (PQ_of_GQ x) as x' eqn:Hx'.
remember (PQ_of_GQ y) as y' eqn:Hy'.
remember (PQ_of_GQ z) as z' eqn:Hz'.
revert Hzy; tac_to_PQ; intros.
move x' after y'; move z' before y'.
move Hx' after Hy'.
rewrite PQadd_sub_assoc; [ | easy ].
assert (Hzxy : (z' < x' + y')%PQ). {
  eapply PQlt_trans; [ apply Hzy | ].
  apply PQlt_add_l.
}
symmetry.
rewrite GQ_of_PQ_subtractive; [ | now rewrite PQ_o_GQ ].
rewrite PQ_o_GQ.
now rewrite <- GQ_of_PQ_subtractive.
Qed.

Theorem GQadd_sub_swap : ∀ x y z,
  (z < x)%GQ → (x + y - z)%GQ = (x - z + y)%GQ.
Proof.
intros * Hzx.
rewrite GQadd_comm, <- GQadd_sub_assoc; [ | easy ].
now rewrite GQadd_comm.
Qed.

Theorem PQ_of_GQ_eq : ∀ x y,
  (PQ_of_GQ x == PQ_of_GQ y)%PQ
  → PQ_of_GQ x = PQ_of_GQ y.
Proof.
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
apply (Nat.mul_cancel_r _ _ (yd + 1)) in Hx; [ | flia ].
rewrite Nat.mul_1_l in Hx.
Search (Nat.gcd (_ * _)).
rewrite <- Nat.gcd_mul_mono_r in Hx.
rewrite H, Nat.mul_comm in Hx.
rewrite Nat.gcd_mul_mono_l, Hy, Nat.mul_1_r in Hx.
rewrite Hx in H.
apply Nat.mul_cancel_r in H; [ | flia ].
apply Nat.add_cancel_r in Hx.
apply Nat.add_cancel_r in H.
now rewrite Hx, H.
Qed.

Theorem GQ_of_PQ_eq : ∀ x y, GQ_of_PQ x = GQ_of_PQ y → (x == y)%PQ.
Proof.
intros (xn, xd) (yn, yd) H.
unfold GQ_of_PQ in H; simpl in H.
injection H; clear H; intros H.
unfold PQred in H; simpl in H.
remember (ggcd (xn + 1) (xd + 1)) as g1 eqn:Hg1.
remember (ggcd (yn + 1) (yd + 1)) as g2 eqn:Hg2.
move g2 before g1.
destruct g1 as (g1, (aa1, bb1)).
destruct g2 as (g2, (aa2, bb2)).
erewrite ggcd_split in Hg1; [ | easy ].
erewrite ggcd_split in Hg2; [ | easy ].
injection Hg1; clear Hg1; intros; subst g1 aa1 bb1.
injection Hg2; clear Hg2; intros; subst g2 aa2 bb2.
injection H; clear H; intros H1 H2.
apply (Nat.add_cancel_r _ _ 1) in H1.
apply (Nat.add_cancel_r _ _ 1) in H2.
remember (Nat.gcd (xn + 1) (xd + 1)) as gx eqn:Hgx.
remember (Nat.gcd (yn + 1) (yd + 1)) as gy eqn:Hgy.
move gy before gx.
assert (Hgxz : gx ≠ 0). {
  intros H; rewrite Hgx in H; apply Nat.gcd_eq_0_r in H.
  now rewrite Nat.add_1_r in H.
}
assert (Hgyz : gy ≠ 0). {
  intros H; rewrite Hgy in H; apply Nat.gcd_eq_0_r in H.
  now rewrite Nat.add_1_r in H.
}
assert (Hxngx : 1 ≤ (xn + 1) / gx). {
  specialize (Nat.gcd_divide_l (xn + 1) (xd + 1)) as (c1, Hc1).
  rewrite <- Hgx in Hc1; rewrite Hc1.
  rewrite Nat.div_mul; [ | easy ].
  destruct c1; [ now rewrite Nat.add_1_r in Hc1 | flia ].
}
assert (Hxdgx : 1 ≤ (xd + 1) / gx). {
  specialize (Nat.gcd_divide_r (xn + 1) (xd + 1)) as (c1, Hc1).
  rewrite <- Hgx in Hc1; rewrite Hc1.
  rewrite Nat.div_mul; [ | easy ].
  destruct c1; [ now rewrite Nat.add_1_r in Hc1 | flia ].
}
assert (Hxngy : 1 ≤ (yn + 1) / gy). {
  specialize (Nat.gcd_divide_l (yn + 1) (yd + 1)) as (c1, Hc1).
  rewrite <- Hgy in Hc1; rewrite Hc1.
  rewrite Nat.div_mul; [ | easy ].
  destruct c1; [ now rewrite Nat.add_1_r in Hc1 | flia ].
}
assert (Hxdgy : 1 ≤ (yd + 1) / gy). {
  specialize (Nat.gcd_divide_r (yn + 1) (yd + 1)) as (c1, Hc1).
  rewrite <- Hgy in Hc1; rewrite Hc1.
  rewrite Nat.div_mul; [ | easy ].
  destruct c1; [ now rewrite Nat.add_1_r in Hc1 | flia ].
}
rewrite Nat.sub_add in H1; [ | easy ].
rewrite Nat.sub_add in H1; [ | easy ].
rewrite Nat.sub_add in H2; [ | easy ].
rewrite Nat.sub_add in H2; [ | easy ].
unfold "=="%PQ, nd; simpl.
apply (Nat.mul_cancel_l _ _ (xn + 1)) in H1; [ | flia ].
rewrite Hgx, <- Nat.gcd_div_swap, <- Hgx in H1.
rewrite H2 in H1.
symmetry in H1; rewrite Nat.mul_comm in H1; symmetry in H1.
specialize (Nat.gcd_divide_l (yn + 1) (yd + 1)) as (c1, Hc1).
specialize (Nat.gcd_divide_r (yn + 1) (yd + 1)) as (c2, Hc2).
rewrite <- Hgy in Hc1, Hc2.
rewrite Hc1, Nat.div_mul in H1; [ | easy ].
rewrite Hc2, Nat.div_mul in H1; [ | easy ].
rewrite Hc1, Hc2.
rewrite Nat.mul_shuffle0, Nat.mul_assoc.
apply Nat.mul_cancel_r; [ easy | ].
rewrite H1; apply Nat.mul_comm.
Qed.

Definition GQcompare x y := PQcompare (PQ_of_GQ x) (PQ_of_GQ y).
Arguments GQcompare x%GQ y%GQ.

Theorem GQcompare_eq_iff : ∀ x y, GQcompare x y = Eq ↔ x = y.
Proof.
intros.
unfold GQcompare.
split; intros H.
-apply PQcompare_eq_iff in H.
 now apply GQeq_eq, PQ_of_GQ_eq.
-rewrite H.
 now apply PQcompare_eq_iff.
Qed.

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

Theorem GQadd_no_neutral : ∀ x y, (y + x)%GQ ≠ x.
Proof.
intros x y Hxy.
unfold "+"%GQ in Hxy; simpl in Hxy.
rewrite <- GQ_o_PQ in Hxy.
remember (PQ_of_GQ x) as x'.
remember (PQ_of_GQ y) as y'.
move y' before x'.
apply GQ_of_PQ_eq in Hxy.
now apply PQadd_no_neutral in Hxy.
Qed.

Theorem GQsub_no_neutral : ∀ x y, (y < x)%GQ → (x - y ≠ x)%GQ.
Proof.
intros *.
unfold "-"%GQ, "<"%GQ; intros Hyx Hxy.
rewrite GQ_of_PQ_subtractive in Hxy; [ | easy ].
rewrite <- GQ_o_PQ in Hxy.
remember (PQ_of_GQ x) as x'.
remember (PQ_of_GQ y) as y'.
move y' before x'.
apply GQ_of_PQ_eq in Hxy.
rewrite (PQsub_morph _ y' _ x') in Hxy.
-now apply PQsub_no_neutral in Hxy.
-now do 2 rewrite PQ_o_GQ.
-apply PQ_o_GQ.
-apply PQ_o_GQ.
Qed.

Theorem NQmatch_match_comp : ∀ A c p q (f0 : A) fp fn,
  match
    match c with
    | Eq => 0%NQ
    | Lt => NQneg p
    | Gt => NQpos q
    end
  with
  | 0%NQ => f0
  | NQpos px => fp px
  | NQneg px => fn px
  end =
  match c with
  | Eq => f0
  | Lt => fn p
  | Gt => fp q
  end.
Proof. intros; now destruct c. Qed.

Theorem NQopp_match_comp : ∀ c eq lt gt,
  (- match c with Eq => eq | Lt => lt | Gt => gt end =
   match c with Eq => - eq | Lt => - lt | Gt => - gt end)%NQ.
Proof. intros; now destruct c. Qed.

Theorem NQadd_comm : ∀ x y, (x + y = y + x)%NQ.
Proof.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py]; try easy; simpl.
-f_equal; apply GQadd_comm.
-now rewrite GQcompare_swap; destruct (GQcompare py px).
-now rewrite GQcompare_swap; destruct (GQcompare py px).
-f_equal; apply GQadd_comm.
Qed.

Theorem NQadd_swap_lemma1 : ∀ px py pz,
  match GQcompare (px + py) pz with
  | Eq => 0%NQ
  | Lt => NQneg (pz - (px + py))
  | Gt => NQpos (px + py - pz)
  end =
  match GQcompare px pz with
  | Eq => NQpos py
  | Lt =>
      match GQcompare (pz - px) py with
      | Eq => 0%NQ
      | Lt => NQpos (py - (pz - px))
      | Gt => NQneg (pz - px - py)
      end
  | Gt => NQpos (px - pz + py)
  end.
Proof.
intros.
remember (GQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
remember (GQcompare px pz) as c2 eqn:Hc2; symmetry in Hc2.
move c2 before c1.
destruct c1, c2; repeat GQcompare_iff.
+now rewrite Hc2, GQadd_comm in Hc1; apply GQadd_no_neutral in Hc1.
+remember (GQcompare (pz - px) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff; [ easy | | ].
 *apply (GQadd_lt_mono_r (pz - px)%GQ _ px) in Hc3.
  rewrite GQsub_add in Hc3; [ | easy ].
  rewrite GQadd_comm, Hc1 in Hc3.
  now apply GQlt_irrefl in Hc3.
 *apply (GQadd_lt_mono_r _ _ px) in Hc3.
  rewrite GQsub_add in Hc3; [ | easy ].
  rewrite GQadd_comm, Hc1 in Hc3.
  now apply GQlt_irrefl in Hc3.
+rewrite <- Hc1 in Hc2.
 exfalso; apply GQnle_gt in Hc2; apply Hc2.
 apply GQlt_le_incl, GQlt_add_r.
+rewrite Hc2 in Hc1.
 exfalso; apply GQnle_gt in Hc1; apply Hc1.
 apply GQlt_le_incl, GQlt_add_r.
+remember (GQcompare (pz - px) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff; simpl.
 *rewrite GQadd_comm, <- Hc3 in Hc1.
  rewrite GQsub_add in Hc1; [ | easy ].
  now apply GQlt_irrefl in Hc1.
 *apply (GQadd_lt_mono_r (pz - px)%GQ _ px) in Hc3.
  rewrite GQsub_add in Hc3; [ | easy ].
  rewrite GQadd_comm in Hc3.
  exfalso; apply GQnle_gt in Hc3; apply Hc3.
  now apply GQlt_le_incl.
 *now f_equal; rewrite GQsub_add_distr.
+apply GQnle_gt in Hc2.
 exfalso; apply Hc2; apply GQlt_le_incl.
 apply (GQlt_trans _ (px + py)%GQ); [ | easy ].
 apply GQlt_add_r.
+now subst px; rewrite GQadd_comm, GQadd_sub.
+remember (GQcompare (pz - px) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff; simpl.
 *rewrite GQadd_comm, <- Hc3 in Hc1.
  rewrite GQsub_add in Hc1; [ | easy ].
  now apply GQlt_irrefl in Hc1.
 *rewrite GQadd_comm; symmetry.
  now f_equal; rewrite GQsub_sub_distr.
 *apply (GQadd_lt_mono_r _ _ px) in Hc3.
  rewrite GQsub_add in Hc3; [ | easy ].
  rewrite GQadd_comm in Hc3.
  exfalso; apply GQnle_gt in Hc3; apply Hc3.
  now apply GQlt_le_incl.
+rewrite GQadd_comm.
 rewrite <- GQadd_sub_assoc; [ | easy ].
 now rewrite GQadd_comm.
Qed.

Theorem NQadd_swap_lemma2 : ∀ px py pz,
  match GQcompare px py with
  | Eq => NQneg pz
  | Lt => NQneg (py - px + pz)
  | Gt =>
      match GQcompare (px - py) pz with
      | Eq => 0%NQ
      | Lt => NQneg (pz - (px - py))
      | Gt => NQpos (px - py - pz)
      end
  end =
  match GQcompare px pz with
  | Eq => NQneg py
  | Lt => NQneg (pz - px + py)
  | Gt =>
      match GQcompare (px - pz) py with
      | Eq => 0%NQ
      | Lt => NQneg (py - (px - pz))
      | Gt => NQpos (px - pz - py)
      end
  end.
Proof.
intros.
remember (GQcompare px py) as c1 eqn:Hc1; symmetry in Hc1.
remember (GQcompare px pz) as c2 eqn:Hc2; symmetry in Hc2.
destruct c1, c2; repeat GQcompare_iff.
-now rewrite <- Hc1, Hc2.
-rewrite Hc1.
 rewrite GQsub_add; [ easy | now rewrite <- Hc1 ].
-remember (GQcompare (px - pz) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff.
 +exfalso; rewrite <- Hc1 in Hc3.
  now apply GQsub_no_neutral in Hc3.
 +rewrite GQsub_sub_distr; [ | easy | easy ].
  rewrite GQadd_comm.
  now rewrite Hc1, GQadd_sub.
 +apply GQnle_gt in Hc3.
  exfalso; apply Hc3; rewrite <- Hc1.
  now apply GQlt_le_incl, GQsub_lt.
-rewrite Hc2, GQsub_add; [ easy | now rewrite <- Hc2 ].
-rewrite GQadd_comm.
 rewrite GQadd_sub_assoc; [ | easy ].
 now rewrite GQadd_sub_swap.
-remember (GQcompare (px - pz) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff.
 +exfalso; rewrite <- Hc3 in Hc1.
  apply GQnle_gt in Hc1; apply Hc1.
  now apply GQlt_le_incl, GQsub_lt.
 +rewrite GQsub_sub_distr; [ | easy | easy ].
  now rewrite GQadd_sub_swap.
 +exfalso; apply GQnle_gt in Hc3; apply Hc3.
  apply GQlt_le_incl.
  apply (GQlt_trans _ px); [ now apply GQsub_lt | easy ].
-remember (GQcompare (px - py) pz) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff.
 +exfalso; rewrite <- Hc2 in Hc3.
  now apply GQsub_no_neutral in Hc3.
 +symmetry in Hc2.
  rewrite Hc2, GQsub_sub_distr; [ | easy | now apply GQsub_lt ].
  now rewrite GQadd_comm, GQadd_sub.
 +exfalso; apply GQnle_gt in Hc3; apply Hc3.
  rewrite <- Hc2.
  now apply GQlt_le_incl, GQsub_lt.
-remember (GQcompare (px - py) pz) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff.
 *exfalso; rewrite <- Hc3 in Hc2.
  apply GQnle_gt in Hc2; apply Hc2.
  now apply GQlt_le_incl, GQsub_lt.
 *rewrite GQsub_sub_distr; [ | easy | easy ].
  now rewrite GQadd_sub_swap.
 *exfalso; apply GQnle_gt in Hc3; apply Hc3.
  apply GQlt_le_incl.
  apply (GQlt_trans _ px); [ now apply GQsub_lt | easy ].
-remember (GQcompare (px - py) pz) as c3 eqn:Hc3; symmetry in Hc3.
 remember (GQcompare (px - pz) py) as c4 eqn:Hc4; symmetry in Hc4.
 destruct c3, c4; repeat GQcompare_iff; simpl.
 *easy.
 *exfalso; apply GQnle_gt in Hc4; apply Hc4.
  symmetry in Hc3.
  rewrite Hc3, GQsub_sub_distr; [ | easy | now apply GQsub_lt ].
  rewrite GQadd_comm, GQadd_sub; apply GQle_refl.
 *exfalso; apply GQnle_gt in Hc4; apply Hc4.
  symmetry in Hc3.
  rewrite Hc3.
  rewrite GQsub_sub_distr; [ | easy | now apply GQsub_lt ].
  rewrite GQadd_comm, GQadd_sub; apply GQle_refl.
 *exfalso; symmetry in Hc4.
  rewrite Hc4 in Hc3.
  rewrite GQsub_sub_distr in Hc3; [ | easy | now apply GQsub_lt ].
  rewrite GQadd_comm, GQadd_sub in Hc3.
  now apply GQlt_irrefl in Hc3.
 *rewrite GQsub_sub_distr; [ | easy | easy ].
  rewrite GQsub_sub_distr; [ | easy | easy ].
  now rewrite GQadd_comm.
 *exfalso; apply GQnle_gt in Hc4; apply Hc4; clear Hc4.
...
  apply (GQadd_le_mono_r _ _ pz).
  rewrite GQsub_add; [ | easy ].
  apply GQnlt_ge; intros Hc4.
  apply GQnle_gt in Hc3; apply Hc3; clear Hc3.
  apply (GQadd_le_mono_r _ _ py).
  rewrite GQsub_add; [ | easy ].
  now apply GQlt_le_incl; rewrite GQadd_comm.
 *exfalso; symmetry in Hc4.
  rewrite (GQsub_morph _ (px - pz) _ px) in Hc3; [ | easy | easy | easy ].
  rewrite GQsub_sub_distr in Hc3; [ | easy | now apply GQsub_lt ].
  rewrite GQadd_comm, GQadd_sub in Hc3.
  now apply GQlt_irrefl in Hc3.
 *exfalso; apply GQnle_gt in Hc4; apply Hc4; clear Hc4.
  apply (GQadd_le_mono_r _ _ pz).
  rewrite GQsub_add; [ | easy ].
  apply GQnlt_ge; intros Hc4.
  apply GQnle_gt in Hc3; apply Hc3; clear Hc3.
  apply (GQadd_le_mono_r _ _ py).
  rewrite GQsub_add; [ | easy ].
  now apply GQlt_le_incl; rewrite GQadd_comm.
 *now rewrite GQsub_sub_swap.
Qed.
...

Theorem NQadd_add_swap : ∀ x y z, (x + y + z = x + z + y)%NQ.
Proof.
intros.
unfold "+"%NQ.
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl.
-now rewrite GQadd_comm.
-now rewrite GQcompare_swap; destruct (GQcompare pz py).
-now rewrite GQcompare_swap; destruct (GQcompare pz py).
-now rewrite GQadd_comm.
-now destruct (GQcompare px pz).
-now rewrite GQadd_add_swap.
-rewrite NQmatch_match_comp.
 apply NQadd_swap_lemma1.
-now destruct (GQcompare px py).
-rewrite NQmatch_match_comp.
 symmetry; apply NQadd_swap_lemma1.
-do 2 (rewrite NQmatch_match_comp; symmetry).
...
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
...

Theorem NQadd_assoc : ∀ x y z, ((x + y) + z = x + (y + z))%NQ.
Proof.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl.
-f_equal; apply GQadd_assoc.
-remember (GQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
 remember (GQcompare py pz) as c2 eqn:Hc2; symmetry in Hc2.
 move c2 before c1.
 destruct c1, c2; do 2  GQcompare_iff.
 +now subst py; apply GQadd_no_neutral in Hc1.
 +idtac.
...

-now rewrite GQcompare_swap; destruct (GQcompare py px).
-now rewrite GQcompare_swap; destruct (GQcompare py px).
-f_equal; apply GQadd_comm.
Qed.
