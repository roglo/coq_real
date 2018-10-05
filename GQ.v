(* Positive rationals where num and den are always common primes *)
(* allowing us to use Leibnitz' equality. *)

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
Notation "a // b" := (GQ_of_pair a b) (at level 32) : GQ_scope.

Definition GQadd x y := GQ_of_PQ (PQ_of_GQ x + PQ_of_GQ y).
Definition GQsub x y := GQ_of_PQ (PQ_of_GQ x - PQ_of_GQ y).
Definition GQmul x y := GQ_of_PQ (PQ_of_GQ x * PQ_of_GQ y).
Definition GQinv x := GQ_of_PQ (/ PQ_of_GQ x).
Arguments GQadd x%GQ y%GQ.
Arguments GQsub x%GQ y%GQ.
Arguments GQmul x%GQ y%GQ.
Arguments GQinv x%GQ.

Notation "x + y" := (GQadd x y) : GQ_scope.
Notation "x - y" := (GQsub x y) : GQ_scope.
Notation "x * y" := (GQmul x y) : GQ_scope.
Notation "x / y" := (GQmul x (GQinv y)) : GQ_scope.
Notation "/ x" := (GQinv x) : GQ_scope.

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

Theorem GQle_antisymm : ∀ x y, (x ≤ y)%GQ → (y ≤ x)%GQ → x = y.
Proof.
intros * Hxy Hyx.
apply Nat.le_antisymm in Hxy; [ | easy ].
unfold nd in Hxy.
destruct x as ((xn, xd), Hxp).
destruct y as ((yn, yd), Hyp).
move yd before xd; move yn before xd.
simpl in Hxp, Hyp, Hxy.
apply GQeq_eq; simpl.
clear Hyx.
assert (H : yd + 1 ≠ 0) by flia.
apply (proj2 (Nat.mul_cancel_r _ _ _ H)) in Hxp.
rewrite <- Nat.gcd_mul_mono_r, <- Hxy, Nat.mul_comm, Nat.mul_1_l in Hxp.
rewrite Nat.gcd_mul_mono_l, Hyp, Nat.mul_1_r in Hxp.
apply Nat.add_cancel_r in Hxp; subst xd.
apply Nat.mul_cancel_r in Hxy; [ | flia ].
apply Nat.add_cancel_r in Hxy.
now subst yn.
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

Theorem GQadd_assoc : ∀ x y z, (x + (y + z) = (x + y) + z)%GQ.
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

Theorem GQmul_assoc : ∀ x y z, (x * (y * z) = (x * y) * z)%GQ.
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

Theorem GQlt_le_dec : ∀ a b, {(a < b)%GQ} + {(b ≤ a)%GQ}.
Proof. intros; apply PQlt_le_dec. Qed.

Theorem GQle_lt_dec : ∀ a b, {(a ≤ b)%GQ} + {(b < a)%GQ}.
Proof. intros; apply PQle_lt_dec. Qed.

Theorem GQlt_irrefl : ∀ x, ¬ (x < x)%GQ.
Proof. intros; apply PQlt_irrefl. Qed.

Theorem GQnle_gt : ∀ x y, ¬ (x ≤ y)%GQ ↔ (y < x)%GQ.
Proof. intros; apply PQnle_gt. Qed.

Theorem GQnlt_ge : ∀ x y, ¬ (x < y)%GQ ↔ (y ≤ x)%GQ.
Proof. intros; apply PQnlt_ge. Qed.

Theorem GQlt_le_incl : ∀ x y, (x < y)%GQ → (x ≤ y)%GQ.
Proof. intros x y; apply PQlt_le_incl. Qed.

Theorem GQlt_trans : ∀ x y z, (x < y)%GQ → (y < z)%GQ → (x < z)%GQ.
Proof. intros x y z; apply PQlt_trans. Qed.

Theorem GQle_trans : ∀ x y z, (x ≤ y)%GQ → (y ≤ z)%GQ → (x ≤ z)%GQ.
Proof. intros x y z; apply PQle_trans. Qed.

Theorem GQlt_le_trans : ∀ x y z, (x < y)%GQ → (y ≤ z)%GQ → (x < z)%GQ.
Proof. intros x y z; apply PQlt_le_trans. Qed.

Theorem GQle_lt_trans : ∀ x y z, (x ≤ y)%GQ → (y < z)%GQ → (x < z)%GQ.
Proof. intros x y z; apply PQle_lt_trans. Qed.

Arguments GQle_trans x%GQ y%GQ z%GQ.
Arguments GQle_lt_trans x%GQ y%GQ z%GQ.

Theorem GQsub_lt : ∀ x y, (y < x)%GQ → (x - y < x)%GQ.
Proof.
intros x y z.
unfold "-"%GQ, "<"%GQ.
rewrite GQ_of_PQ_subtractive; [ | easy ].
do 2 rewrite GQ_o_PQ.
rewrite PQ_of_GQ_subtractive; [ | easy ].
now apply PQsub_lt.
Qed.

Theorem GQadd_le_mono_r : ∀ x y z, (x ≤ y)%GQ ↔ (x + z ≤ y + z)%GQ.
Proof.
intros *.
unfold "+"%GQ, "≤"%GQ.
do 2 rewrite GQ_of_PQ_additive.
do 3 rewrite GQ_o_PQ.
do 2 rewrite PQ_of_GQ_additive.
apply PQadd_le_mono_r.
Qed.

Theorem GQadd_le_mono_l : ∀ x y z, (x ≤ y)%GQ ↔ (z + x ≤ z + y)%GQ.
Proof.
intros *.
setoid_rewrite GQadd_comm.
apply GQadd_le_mono_r.
Qed.

Theorem GQadd_le_mono : ∀ x y z t,
   (x ≤ y)%GQ → (z ≤ t)%GQ → (x + z ≤ y + t)%GQ.
Proof.
intros * Hxy Hzt.
apply (GQle_trans _ (y + z)).
-now apply GQadd_le_mono_r.
-now apply GQadd_le_mono_l.
Qed.

Theorem GQsub_le_mono_r : ∀ x y z,
  (z < x)%GQ → (z < y)%GQ → (x ≤ y)%GQ ↔ (x - z ≤ y - z)%GQ.
Proof.
intros *.
unfold "-"%GQ, "≤"%GQ, "<"%GQ.
intros Hzx Hzy.
rewrite GQ_of_PQ_subtractive; [ | easy ].
rewrite GQ_of_PQ_subtractive; [ | easy ].
do 3 rewrite GQ_o_PQ.
rewrite PQ_of_GQ_subtractive; [ | easy ].
rewrite PQ_of_GQ_subtractive; [ | easy ].
now apply PQsub_le_mono_r.
Qed.

Theorem GQsub_le_mono_l : ∀ x y z,
  (x < z)%GQ → (y < z)%GQ → (y ≤ x)%GQ ↔ (z - x ≤ z - y)%GQ.
Proof.
intros *.
unfold "-"%GQ, "≤"%GQ, "<"%GQ.
intros Hzx Hzy.
rewrite GQ_of_PQ_subtractive; [ | easy ].
rewrite GQ_of_PQ_subtractive; [ | easy ].
do 3 rewrite GQ_o_PQ.
rewrite PQ_of_GQ_subtractive; [ | easy ].
rewrite PQ_of_GQ_subtractive; [ | easy ].
now apply PQsub_le_mono_l.
Qed.

Theorem GQsub_le_mono : ∀ x y z t,
  (y < x)%GQ → (t < z)%GQ → (x ≤ z)%GQ → (t ≤ y)%GQ → (x - y ≤ z - t)%GQ.
Proof.
intros * Hyx Htz Hxz Hty.
apply (GQle_trans _ (z - y)).
-apply GQsub_le_mono_r; [ easy | | easy ].
 eapply GQlt_le_trans; [ apply Hyx | apply Hxz ].
-apply GQsub_le_mono_l; [ | easy | easy ].
 eapply GQlt_le_trans; [ apply Hyx | apply Hxz ].
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

Theorem GQlt_add_l : ∀ x y, (y < x + y)%GQ.
Proof.
intros x y.
unfold "<"%GQ, "+"%GQ.
remember (PQ_of_GQ x) as x'.
remember (PQ_of_GQ y) as y'.
rewrite PQ_o_GQ.
apply PQlt_add_l.
Qed.

Theorem GQlt_add_r : ∀ x y, (x < x + y)%GQ.
Proof.
intros x y.
rewrite GQadd_comm.
apply GQlt_add_l.
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

Theorem GQsub_sub_swap : ∀ x y z,
  (y + z < x)%GQ → (x - y - z)%GQ = (x - z - y)%GQ.
Proof.
intros * Hyzx.
rewrite <- GQsub_add_distr; [ | easy ].
rewrite <- GQsub_add_distr; [ | now rewrite GQadd_comm ].
now rewrite GQadd_comm.
Qed.

Theorem GQle_add_l : ∀ x y, (x ≤ y + x)%GQ.
Proof.
intros.
unfold "≤"%GQ.
unfold "+"%GQ.
rewrite GQ_of_PQ_additive.
do 2 rewrite GQ_o_PQ.
rewrite PQ_of_GQ_additive.
apply PQle_add_l.
Qed.

Theorem GQle_add_r : ∀ x y, (x ≤ x + y)%GQ.
Proof.
intros.
rewrite GQadd_comm.
apply GQle_add_l.
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

Theorem GQadd_pair : ∀ a b c d,
  a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0
  → (a // b + c // d = (a * d + b * c) // (b * d))%GQ.
Proof.
intros * Ha Hb Hc Hd.
apply GQeq_eq; simpl.
rewrite <- PQred_add.
unfold PQ_of_pair.
unfold "+"%PQ, PQadd_num1, PQadd_den1, nd; simpl.
rewrite Nat.sub_add; [ | flia Ha ].
rewrite Nat.sub_add; [ | flia Hd ].
rewrite Nat.sub_add; [ | flia Hc ].
rewrite Nat.sub_add; [ | flia Hb ].
now replace (c * b) with (b * c) by apply Nat.mul_comm.
Qed.

Theorem GQsub_pair : ∀ a b c d,
  a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 → b * c < a * d
  → (a // b - c // d = (a * d - b * c) // (b * d))%GQ.
Proof.
intros * Ha Hb Hc Hd Hlt.
apply GQeq_eq; simpl.
rewrite <- PQred_sub; cycle 1. {
  unfold "<"%PQ, nd; simpl.
  do 4 (rewrite Nat.sub_add; [ | flia Ha Hb Hc Hd ]).
  now rewrite Nat.mul_comm.
}
unfold PQ_of_pair.
unfold "-"%PQ, PQsub_num1, PQadd_den1, nd; simpl.
do 4 (rewrite Nat.sub_add; [ | flia Ha Hb Hc Hd ]).
now replace (c * b) with (b * c) by apply Nat.mul_comm.
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

Theorem GQcompare_diag : ∀ x, GQcompare x x = Eq.
Proof.
intros.
now apply GQcompare_eq_iff.
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

Theorem GQcompare_mul_cancel_l : ∀ x y z,
  GQcompare (x * y) (x * z) = GQcompare y z.
Proof.
intros.
unfold GQcompare.
unfold "*"%GQ.
do 2 rewrite PQ_o_GQ.
apply PQcompare_mul_cancel_l.
Qed.

Theorem GQle_PQle : ∀ x y, (x ≤ y)%GQ ↔ (PQ_of_GQ x ≤ PQ_of_GQ y)%PQ.
Proof. easy. Qed.

Theorem GQeq_pair : ∀ x y z t,
  x ≠ 0 → y ≠ 0 → z ≠ 0 → t ≠ 0
  → GQ_of_pair x y = GQ_of_pair z t ↔ x * t = y * z.
Proof.
intros * Hx Hy Hz Ht.
unfold GQ_of_pair, GQ_of_PQ.
unfold PQ_of_pair, PQred; simpl.
rewrite GQeq_eq; simpl.
rewrite Nat.sub_add; [ | flia Hx ].
rewrite Nat.sub_add; [ | flia Hy ].
rewrite Nat.sub_add; [ | flia Hz ].
rewrite Nat.sub_add; [ | flia Ht ].
remember (ggcd x y) as g1 eqn:Hg1; symmetry in Hg1.
remember (ggcd z t) as g2 eqn:Hg2; symmetry in Hg2.
move g2 before g1.
destruct g1 as (g1, (aa1, bb1)).
specialize (ggcd_correct_divisors x y) as H5.
destruct g2 as (g2, (aa2, bb2)).
rewrite Hg1 in H5; destruct H5 as (H5, H6).
specialize (ggcd_correct_divisors z t) as H7.
rewrite Hg2 in H7; destruct H7 as (H7, H8).
rewrite H5, H6, H7, H8.
replace (g1 * aa1 * (g2 * bb2)) with ((g1 * g2) * (aa1 * bb2)) by flia.
replace (g1 * bb1 * (g2 * aa2)) with ((g1 * g2) * (aa2 * bb1)) by flia.
destruct aa1; [ now rewrite Nat.mul_0_r in H5 | ].
destruct aa2; [ now rewrite Nat.mul_0_r in H7 | ].
destruct bb1; [ now rewrite Nat.mul_0_r in H6 | ].
destruct bb2; [ now rewrite Nat.mul_0_r in H8 | ].
split; intros H.
-injection H; clear H; intros Hb Ha.
 do 2 rewrite Nat.sub_0_r in Hb, Ha.
 now subst aa1 bb1.
-(* y a peut-être plus simple, non ? chais pas *)
 apply Nat.mul_cancel_l in H; cycle 1. {
   destruct g1; [ easy | now destruct g2 ].
 }
 assert (Hg1z : g1 ≠ 0) by now destruct g1.
 assert (Hg2z : g2 ≠ 0) by now destruct g2.
 assert (H1 : Nat.gcd (S aa1) (S bb1) = 1). {
   assert (H1 : g1 = Nat.gcd x y) by now rewrite <- ggcd_gcd, Hg1.
   apply Nat.gcd_div_gcd in H1; [ | easy ].
   rewrite H5, Nat.mul_comm in H1.
   rewrite Nat.div_mul in H1; [ | easy ].
   rewrite H6, Nat.mul_comm in H1.
   rewrite Nat.div_mul in H1; [ | easy ].
   easy.
 }
 assert (H2 : Nat.gcd (S aa2) (S bb2) = 1). {
   assert (H2 : g2 = Nat.gcd z t) by now rewrite <- ggcd_gcd, Hg2.
   apply Nat.gcd_div_gcd in H2; [ | easy ].
   rewrite H7, Nat.mul_comm in H2.
   rewrite Nat.div_mul in H2; [ | easy ].
   rewrite H8, Nat.mul_comm in H2.
   rewrite Nat.div_mul in H2; [ | easy ].
   easy.
 }
 specialize (Nat.gauss (S aa1) (S bb1) (S aa2)) as H3.
 rewrite Nat.mul_comm, <- H in H3.
 specialize (H3 (Nat.divide_factor_l _ _) H1).
 specialize (Nat.gauss (S aa2) (S bb2) (S aa1)) as H4.
 rewrite Nat.mul_comm, H in H4.
 specialize (H4 (Nat.divide_factor_l _ _) H2).
 apply Nat.divide_antisym in H3; [ | easy ].
 rewrite H3 in H.
 apply Nat.mul_cancel_l in H; [ | easy ].
 now rewrite H, H3.
Qed.

Theorem GQlt_pair : ∀ x y z t,
  x ≠ 0 → y ≠ 0 → z ≠ 0 → t ≠ 0
  → (GQ_of_pair x y < GQ_of_pair z t)%GQ ↔ x * t < y * z.
Proof.
intros * Hx Hy Hz Ht.
unfold GQ_of_pair, GQ_of_PQ.
unfold PQ_of_pair, PQred.
unfold "<"%GQ; simpl.
rewrite Nat.sub_add; [ | flia Hx ].
rewrite Nat.sub_add; [ | flia Hy ].
rewrite Nat.sub_add; [ | flia Hz ].
rewrite Nat.sub_add; [ | flia Ht ].
remember (ggcd x y) as g1 eqn:Hg1; symmetry in Hg1.
remember (ggcd z t) as g2 eqn:Hg2; symmetry in Hg2.
move g2 before g1.
destruct g1 as (g1, (aa1, bb1)).
specialize (ggcd_correct_divisors x y) as H5.
destruct g2 as (g2, (aa2, bb2)).
rewrite Hg1 in H5; destruct H5 as (H5, H6).
specialize (ggcd_correct_divisors z t) as H7.
rewrite Hg2 in H7; destruct H7 as (H7, H8).
rewrite H5, H6, H7, H8.
unfold "<"%PQ, nd; simpl.
replace (g1 * aa1 * (g2 * bb2)) with ((g1 * g2) * (aa1 * bb2)) by flia.
replace (g1 * bb1 * (g2 * aa2)) with ((g1 * g2) * (aa2 * bb1)) by flia.
destruct aa1; [ now rewrite Nat.mul_0_r in H5 | ].
destruct aa2; [ now rewrite Nat.mul_0_r in H7 | ].
destruct bb1; [ now rewrite Nat.mul_0_r in H6 | ].
destruct bb2; [ now rewrite Nat.mul_0_r in H8 | ].
do 4 (rewrite Nat.sub_add; [ | flia ]).
apply Nat.mul_lt_mono_pos_l.
destruct g1; [ easy | ].
destruct g2; [ easy | ].
simpl; flia.
Qed.

(* perhaps do an Ltac for this theorem and the previous one *)
Theorem GQle_pair : ∀ x y z t,
  x ≠ 0 → y ≠ 0 → z ≠ 0 → t ≠ 0
  → (GQ_of_pair x y ≤ GQ_of_pair z t)%GQ ↔ x * t ≤ y * z.
Proof.
intros * Hx Hy Hz Ht.
unfold GQ_of_pair, GQ_of_PQ.
unfold PQ_of_pair, PQred.
unfold "≤"%GQ; simpl.
rewrite Nat.sub_add; [ | flia Hx ].
rewrite Nat.sub_add; [ | flia Hy ].
rewrite Nat.sub_add; [ | flia Hz ].
rewrite Nat.sub_add; [ | flia Ht ].
remember (ggcd x y) as g1 eqn:Hg1; symmetry in Hg1.
remember (ggcd z t) as g2 eqn:Hg2; symmetry in Hg2.
move g2 before g1.
destruct g1 as (g1, (aa1, bb1)).
specialize (ggcd_correct_divisors x y) as H5.
destruct g2 as (g2, (aa2, bb2)).
rewrite Hg1 in H5; destruct H5 as (H5, H6).
specialize (ggcd_correct_divisors z t) as H7.
rewrite Hg2 in H7; destruct H7 as (H7, H8).
rewrite H5, H6, H7, H8.
unfold "≤"%PQ, nd; simpl.
replace (g1 * aa1 * (g2 * bb2)) with ((g1 * g2) * (aa1 * bb2)) by flia.
replace (g1 * bb1 * (g2 * aa2)) with ((g1 * g2) * (aa2 * bb1)) by flia.
destruct aa1; [ now rewrite Nat.mul_0_r in H5 | ].
destruct aa2; [ now rewrite Nat.mul_0_r in H7 | ].
destruct bb1; [ now rewrite Nat.mul_0_r in H6 | ].
destruct bb2; [ now rewrite Nat.mul_0_r in H8 | ].
do 4 (rewrite Nat.sub_add; [ | flia ]).
apply Nat.mul_le_mono_pos_l.
destruct g1; [ easy | ].
destruct g2; [ easy | ].
simpl; flia.
Qed.

Theorem GQpair_diag : ∀ a, a ≠ 0 → GQ_of_pair a a = 1%GQ.
Proof.
intros * Ha.
apply GQeq_eq; simpl.
unfold PQred; simpl.
rewrite Nat.sub_add; [ | flia Ha ].
now rewrite ggcd_diag.
Qed.

Theorem GQmul_pair : ∀ x y z t,
  x ≠ 0 → y ≠ 0 → z ≠ 0 → t ≠ 0
  → ((x // y) * (z // t) = (x * z) // (y * t))%GQ.
Proof.
intros * Hx Hy Hz Ht; simpl.
unfold "*"%GQ, "//"%GQ; simpl.
apply GQeq_eq; simpl.
rewrite <- PQred_mul.
unfold PQ_of_pair.
unfold PQmul, PQmul_num1, PQmul_den1; simpl.
rewrite Nat.sub_add; [ | flia Hx ].
rewrite Nat.sub_add; [ | flia Hz ].
rewrite Nat.sub_add; [ | flia Hy ].
rewrite Nat.sub_add; [ | flia Ht ].
easy.
Qed.

Theorem GQmul_sub_distr_l : ∀ x y z, (z < y)%GQ → (x * (y - z) = x * y - x * z)%GQ.
Proof.
intros.
unfold "<"%GQ in H.
tac_to_PQ.
rename u into pz; rename Hu into Hpz.
rename u0 into py; rename Hu0 into Hpy.
rename u1 into px; rename Hu1 into Hpx.
rewrite (PQmul_sub_distr_l px _ _ H).
rewrite GQ_of_PQ_subtractive; [ | now apply PQmul_lt_cancel_l ].
do 2 rewrite GQ_of_PQ_multiplicative.
rewrite GQ_of_PQ_subtractive; [ now do 2 rewrite GQ_o_PQ | ].
unfold "*"%GQ.
do 5 rewrite PQ_o_GQ.
now apply PQmul_lt_cancel_l.
Qed.

Theorem GQmul_1_l : ∀ a, (1 * a)%GQ = a.
Proof.
intros.
apply GQeq_eq; simpl.
unfold PQred.
rewrite PQmul_1_l.
destruct a as (a, Ha); simpl.
rewrite (ggcd_split _ _ 1); [ | easy ].
do 2 rewrite Nat.div_1_r, Nat.add_1_r.
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
now destruct a.
Qed.

Theorem GQmul_1_r : ∀ a, (a * 1)%GQ = a.
Proof.
intros.
rewrite GQmul_comm.
apply GQmul_1_l.
Qed.

Definition GQfrac gq := GQ_of_PQ (PQfrac (PQ_of_GQ gq)).
Definition GQintg gq := PQintg (PQ_of_GQ gq).
