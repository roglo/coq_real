(* Positive rationals where num and den are always common primes *)
(* allowing us to use Leibnitz' equality. *)

Require Import Utf8 Arith Morphisms Init.Nat.
Require Import Misc PQ Nat_ggcd.
Import PQ_Notations.

Set Nested Proofs Allowed.

Declare Scope GQ_scope.
Delimit Scope GQ_scope with GQ.

Record GQ :=
  GQmake0
    { PQ_of_GQ : PQ;
      GQprop : Nat.gcd (PQnum1 PQ_of_GQ + 1) (PQden1 PQ_of_GQ + 1) = 1 }.
Arguments GQmake0 PQ_of_GQ%PQ.
Arguments PQ_of_GQ x%GQ : rename.

(* the use of transparentify below is to allow Numeral Notation of
   values of type Q (file NQ.v) work by always giving eq_refl as
   proof of gcd n d = 1; thanks to Theo Zimmermann, Hugo Herbelin
   and Jason Gross *)

Definition transparentify {A} (D : {A} + {¬A}) (H : A) : A :=
  match D with
  | left pf => pf
  | right npf => match npf H with end
  end.

Definition GQmake x p := GQmake0 x (transparentify (Nat.eq_dec _ _) p).
Arguments GQmake x%PQ.

Definition GQ_of_PQ x := GQmake (PQred x) (PQred_gcd x).
Arguments GQ_of_PQ x%PQ.

Definition GQ_of_pair n d := GQ_of_PQ (PQ_of_pair n d).

Definition GQadd x y := GQ_of_PQ (PQ_of_GQ x + PQ_of_GQ y).
Definition GQsub x y := GQ_of_PQ (PQ_of_GQ x - PQ_of_GQ y).
Definition GQmul x y := GQ_of_PQ (PQ_of_GQ x * PQ_of_GQ y).
Definition GQinv x := GQ_of_PQ (/ PQ_of_GQ x).
Arguments GQadd x%GQ y%GQ.
Arguments GQsub x%GQ y%GQ.
Arguments GQmul x%GQ y%GQ.
Arguments GQinv x%GQ.

Definition GQlt x y := PQlt (PQ_of_GQ x) (PQ_of_GQ y).
Definition GQle x y := PQle (PQ_of_GQ x) (PQ_of_GQ y).
Definition GQgt x y := GQlt y x.
Definition GQge x y := GQle y x.

(*
Notation "1" := (GQ_of_pair 1 1) : GQ_scope.
Notation "2" := (GQ_of_pair 2 1) : GQ_scope.
*)
Notation "a // b" := (GQ_of_pair a b) : GQ_scope.
Notation "x + y" := (GQadd x y) : GQ_scope.
Notation "x - y" := (GQsub x y) : GQ_scope.
Notation "x * y" := (GQmul x y) : GQ_scope.
Notation "x / y" := (GQmul x (GQinv y)) : GQ_scope.
Notation "/ x" := (GQinv x) : GQ_scope.
Notation "x < y" := (GQlt x y) : GQ_scope.
Notation "x ≤ y" := (GQle x y) : GQ_scope.
Notation "x > y" := (GQgt x y) : GQ_scope.
Notation "x ≥ y" := (GQge x y) : GQ_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%GQ (at level 70, y at next level) :
  GQ_scope.

Definition GQ_of_decimal_uint (n : Decimal.uint) : option GQ :=
  let a := Nat.of_uint n in
  if Nat.eq_dec a 0 then None
  else Some (GQ_of_pair a 1).

Definition GQ_of_decimal_int (n : Decimal.int) : option GQ :=
  match n with
  | Decimal.Pos ui => GQ_of_decimal_uint ui
  | Decimal.Neg ui => None
  end.

Definition GQ_to_decimal_uint (gq : GQ) : option Decimal.uint :=
  let (num, den) := PQ_of_GQ gq in
  match den with
  | 0 => Some (Nat.to_uint (num + 1))
  | _ => None
  end.

Definition GQ_to_decimal_int (gq : GQ) : option Decimal.int :=
  option_map Decimal.Pos (GQ_to_decimal_uint gq).

Numeral Notation GQ GQ_of_decimal_int GQ_to_decimal_int : GQ_scope.

(* Set Printing All. *)
(* Check 1%GQ. *)
(* GQmake0 (PQmake O O) (@eq_refl nat (S O)) *)
(* Check (1 // 1)%GQ. *)
(* GQ_of_pair (S O) (S O) *)

(*
Check 3%GQ.
Check (3 // 1)%GQ.
Compute 3%GQ.
Compute (3 // 1)%GQ.
*)
(*
Check 0%GQ.
Check (-4)%GQ.
*)
(*
Compute 1%GQ.
Check 1%GQ.
Check 2%GQ.
Check 3%GQ.
Check 4%GQ.
Check 5%GQ.
Check 6%GQ.
Check (22 // 7)%GQ.
Compute (22 // 7)%GQ.
*)

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
(*
symmetry in Hxp, Hyp.
*)
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
cbn.
unfold "+"%GQ.
now rewrite PQred_add.
Qed.

Theorem GQ_of_PQ_subtractive : ∀ x y,
  (y < x)%PQ → GQ_of_PQ (x - y) = (GQ_of_PQ x - GQ_of_PQ y)%GQ.
Proof.
intros * Hyx.
apply GQeq_eq.
unfold GQ_of_PQ.
unfold "-"%GQ.
now apply PQred_sub.
Qed.

Theorem GQ_of_PQ_multiplicative : ∀ x y,
  GQ_of_PQ (x * y) = (GQ_of_PQ x * GQ_of_PQ y)%GQ.
Proof.
intros.
apply GQeq_eq.
unfold GQ_of_PQ.
unfold "*"%GQ; cbn.
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

Theorem GQadd_lt_mono_l : ∀ x y z, (y < z)%GQ ↔ (x + y < x + z)%GQ.
Proof.
intros.
unfold "+"%GQ, "<"%GQ.
do 2 rewrite GQ_of_PQ_additive.
do 2 rewrite PQ_of_GQ_additive.
do 3 rewrite PQ_o_GQ.
apply PQadd_lt_mono_l.
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

Theorem GQeq_dec : ∀ x y : GQ, {x = y} + {x ≠ y}.
Proof.
intros.
destruct (GQle_lt_dec x y) as [H1| H1].
-destruct (GQle_lt_dec y x) as [H2| H2].
 +now left; apply GQle_antisymm.
 +right; intros H; subst x.
  now apply GQlt_irrefl in H2.
-destruct (GQle_lt_dec y x) as [H2| H2].
 +right; intros H; subst x.
  now apply GQlt_irrefl in H1.
 +now left; apply GQle_antisymm; apply GQlt_le_incl.
Qed.

Theorem GQlt_trans : ∀ x y z, (x < y)%GQ → (y < z)%GQ → (x < z)%GQ.
Proof. intros x y z; apply PQlt_trans. Qed.
Arguments GQlt_trans x%GQ y%GQ z%GQ t%GQ.

Theorem GQle_trans : ∀ x y z, (x ≤ y)%GQ → (y ≤ z)%GQ → (x ≤ z)%GQ.
Proof. intros x y z; apply PQle_trans. Qed.

Theorem GQlt_le_trans : ∀ x y z, (x < y)%GQ → (y ≤ z)%GQ → (x < z)%GQ.
Proof. intros x y z; apply PQlt_le_trans. Qed.

Theorem GQle_lt_trans : ∀ x y z, (x ≤ y)%GQ → (y < z)%GQ → (x < z)%GQ.
Proof. intros x y z; apply PQle_lt_trans. Qed.

Arguments GQle_trans x%GQ y%GQ z%GQ.
Arguments GQlt_le_trans x%GQ y%GQ z%GQ.
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

Theorem GQsub_le : ∀ x y, (y < x)%GQ → (x - y ≤ x)%GQ.
Proof.
intros * Hyx.
now apply GQlt_le_incl, GQsub_lt.
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

Theorem GQsub_lt_mono_l : ∀ x y z, (x < y)%GQ → (y < z)%GQ → (z - y < z - x)%GQ.
Proof.
intros * Hxy Hyz.
apply (GQadd_lt_mono_r _ _ y).
rewrite GQsub_add; [ | easy ].
rewrite GQadd_comm.
rewrite GQadd_sub_assoc; [ | now apply (GQlt_trans _ y) ].
apply (GQadd_lt_mono_l x).
remember (x + z)%GQ as a.
rewrite GQadd_comm; subst a.
rewrite GQsub_add; [ now apply GQadd_lt_mono_r | ].
apply (GQlt_trans _ y); [ easy | ].
apply GQlt_add_r.
Qed.

Theorem GQsub_lt_mono_r : ∀ x y z, (x < y)%GQ → (z < x)%GQ → (x - z < y - z)%GQ.
Proof.
intros * Hxy Hyz.
apply (GQadd_lt_mono_r _ _ z).
rewrite GQsub_add; [ | easy ].
rewrite GQsub_add; [ easy | ].
now apply (GQlt_trans _ x).
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
(*
symmetry in Hy.
*)
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

Theorem GQpair_diag : ∀ a, a ≠ 0 → (a // a = 1)%GQ.
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
unfold "*"%GQ; cbn.
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

Theorem GQpair_mul_l :
  ∀ a b c, a ≠ 0 → b ≠ 0 → c ≠ 0
  → ((a * b) // c)%GQ = (a // c * b // 1)%GQ.
Proof.
intros.
rewrite GQmul_pair; [ | easy | easy | easy | easy ].
now rewrite Nat.mul_1_r.
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

Theorem GQmul_le_mono : ∀ x y z t,
  (x ≤ y)%GQ → (z ≤ t)%GQ → (x * z ≤ y * t)%GQ.
Proof.
intros *.
unfold "≤"%GQ; cbn.
intros Hxy Hzt.
do 2 rewrite PQred_eq.
now apply PQmul_le_mono.
Qed.

Theorem GQmul_le_mono_l : ∀ x y z, (x ≤ y ↔ z * x ≤ z * y)%GQ.
Proof.
intros.
unfold "≤"%GQ; cbn.
do 2 rewrite PQred_eq.
apply PQmul_le_mono_l.
Qed.

Theorem GQmul_lt_mono_l : ∀ x y z, (x < y)%GQ ↔ (z * x < z * y)%GQ.
Proof.
intros.
unfold "<"%GQ; cbn.
do 2 rewrite PQred_eq.
split; intros H.
-now apply PQmul_lt_cancel_l.
-now apply PQmul_lt_cancel_l in H.
Qed.

Theorem GQmul_lt_mono_r : ∀ x y z, (x < y)%GQ ↔ (x * z < y * z)%GQ.
Proof.
setoid_rewrite GQmul_comm.
apply GQmul_lt_mono_l.
Qed.

Theorem GQmul_lt_mono : ∀ x y z t,
  (x < y)%GQ → (z < t)%GQ → (x * z < y * t)%GQ.
Proof.
intros * Hxy Hzt.
apply (GQlt_trans _ (x * t)).
-now apply GQmul_lt_mono_l.
-now apply GQmul_lt_mono_r.
Qed.

Definition GQnum x := PQnum1 (PQ_of_GQ x) + 1.
Definition GQden x := PQden1 (PQ_of_GQ x) + 1.
Arguments GQnum x%GQ.
Arguments GQden x%GQ.

(* co-fractional part = 1 - fractional part
   defined instead of fractional part because fractional part does not
   exist for integer values (would be 0 but 0 ∉ GQ) *)
Definition GQcfrac x := ((GQden x - GQnum x mod GQden x) // GQden x)%GQ.
(*
Definition GQintg x := PQintg (PQ_of_GQ x).
*)
Arguments GQcfrac x%GQ.

Theorem GQnum_neq_0 : ∀ x, GQnum x ≠ 0.
Proof.
intros x.
unfold GQnum.
now rewrite Nat.add_1_r.
Qed.

Theorem GQden_neq_0 : ∀ x, GQden x ≠ 0.
Proof.
intros x.
unfold GQden.
now rewrite Nat.add_1_r.
Qed.

Hint Resolve GQnum_neq_0 GQden_neq_0 : core.

Theorem GQnum_den : ∀ x, x = (GQnum x // GQden x)%GQ.
Proof.
intros x.
apply GQeq_eq.
unfold GQnum, GQden.
unfold GQ_of_PQ; cbn.
remember (PQ_of_GQ x) as px eqn:Hpx; symmetry in Hpx.
unfold PQred.
destruct px as (nx, dx).
remember ggcd as f; cbn; subst f.
remember (ggcd (nx + 1) (dx + 1)) as g eqn:Hg.
symmetry in Hg.
destruct g as (g, (aa, bb)).
specialize (ggcd_correct_divisors (nx + 1) (dx + 1)) as H.
rewrite Hg in H.
destruct H as (Hnx, Hdx).
specialize (PQred_gcd (PQ_of_GQ x)) as H.
rewrite PQred_of_GQ in H.
rewrite Hpx in H; cbn in H.
rewrite <- ggcd_gcd in H.
rewrite Hg in H; cbn in H; subst g.
rewrite Nat.mul_1_l in Hdx, Hnx.
subst aa bb.
do 2 rewrite Nat.add_sub.
rewrite Hg.
now do 2 rewrite Nat.add_sub.
Qed.

Theorem GQnum_mult_GQden : ∀ a b n,
  GQnum (a // b)%GQ = GQden (a // b)%GQ * n
  → a mod b = 0.
Proof.
intros * Hnd.
unfold GQnum, GQden in Hnd.
unfold GQ_of_PQ in Hnd; cbn in Hnd.
unfold PQred in Hnd.
remember ggcd as f; cbn in Hnd; subst f.
destruct b; [ easy | ].
destruct a; [ now rewrite Nat.mod_0_l | ].
rewrite Nat.sub_add in Hnd; [ | flia ].
rewrite Nat.sub_add in Hnd; [ | flia ].
remember (ggcd (S a) (S b)) as g eqn:Hg.
symmetry in Hg.
destruct g as (g, (aa, bb)).
cbn in Hnd.
specialize (ggcd_correct_divisors (S a) (S b)) as H1.
rewrite Hg in H1.
destruct H1 as (Ha, Hb).
destruct aa; [ now rewrite Nat.mul_comm in Ha | ].
destruct bb; [ now rewrite Nat.mul_comm in Hb | ].
rewrite Nat.sub_succ, Nat.sub_0_r, Nat.add_1_r in Hnd.
rewrite Nat.sub_succ, Nat.sub_0_r, Nat.add_1_r in Hnd.
rewrite Ha, Hb, Hnd.
replace (g * S bb) with (g * S bb * 1) by flia.
rewrite Nat.mul_assoc.
rewrite Nat.mul_mod_distr_l; [ | easy | ]; cycle 1. {
  intros H; apply Nat.eq_mul_0 in H.
  destruct H; [ now subst g | easy ].
}
now rewrite Nat.mod_1_r, Nat.mul_comm.
Qed.

Theorem GQnum_pair_0_r : ∀ a, a ≠ 0 → GQnum (a // 0)%GQ = a.
Proof.
intros * Ha.
unfold GQnum; cbn.
unfold PQred.
remember ggcd as f; cbn; subst f.
rewrite ggcd_1_r; cbn.
destruct a; [ easy | flia ].
Qed.

Theorem GQden_pair_0_r : ∀ a, GQden (a // 0)%GQ = 1.
Proof.
intros.
unfold GQden; cbn.
unfold PQred.
remember ggcd as f; cbn; subst f.
now rewrite ggcd_1_r; cbn.
Qed.

Theorem GQnum_pair_1_r : ∀ a, a ≠ 0 → GQnum (a // 1)%GQ = a.
Proof.
intros * Ha.
unfold GQnum; cbn.
unfold PQred.
remember ggcd as f; cbn; subst f.
rewrite ggcd_1_r; cbn.
destruct a; [ easy | flia ].
Qed.

Theorem GQden_pair_1_r : ∀ a, GQden (a // 1)%GQ = 1.
Proof.
intros.
unfold GQden; cbn.
unfold PQred.
remember ggcd as f; cbn; subst f.
now rewrite ggcd_1_r; cbn.
Qed.

Theorem GQnum_pair : ∀ a b,
  GQnum (a // b) =
    if zerop a then 1 else if zerop b then a else a / Nat.gcd a b.
Proof.
intros.
unfold GQnum; cbn.
unfold PQred.
remember ggcd as f; cbn; subst f.
destruct a.
-remember ggcd as f; cbn; subst f.
 now rewrite ggcd_1_l; cbn.
-rewrite Nat.sub_add; [ | flia ].
 destruct b.
 +remember ggcd as f; cbn; subst f.
  rewrite ggcd_1_r.
  now rewrite Nat.sub_succ, Nat.sub_0_r, Nat.add_1_r.
 +rewrite Nat.sub_add; [ | flia ].
  remember (ggcd (S a) (S b)) as g eqn:Hg.
  destruct g as (g, (aa, bb)).
  remember S as f; cbn; subst f.
  rewrite <- ggcd_gcd, <- Hg; cbn.
  specialize (ggcd_correct_divisors (S a) (S b)) as H.
  rewrite <- Hg in H.
  destruct H as (H1, H2).
  rewrite H1.
  rewrite Nat.mul_comm, Nat.div_mul; [ | now destruct g ].
  destruct aa; [ now rewrite Nat.mul_0_r in H1 | flia ].
Qed.

Theorem GQden_pair : ∀ a b,
  GQden (a // b) = if zerop a ∨∨ zerop b then Nat.max 1 b else b / Nat.gcd a b.
Proof.
intros.
unfold GQden; cbn.
unfold PQred.
remember ggcd as f; cbn; subst f.
destruct a.
-remember ggcd as f; cbn; subst f.
 rewrite ggcd_1_l; cbn.
 destruct b; [ easy | flia ].
-rewrite Nat.sub_add; [ | flia ].
 destruct b.
 +remember ggcd as f; cbn; subst f.
  now rewrite ggcd_1_r.
 +rewrite Nat.sub_add; [ | flia ].
  remember (ggcd (S a) (S b)) as g eqn:Hg.
  destruct g as (g, (aa, bb)).
  remember S as f; cbn; subst f.
  rewrite <- ggcd_gcd, <- Hg; cbn.
  specialize (ggcd_correct_divisors (S a) (S b)) as H.
  rewrite <- Hg in H.
  destruct H as (H1, H2).
  rewrite H2.
  rewrite Nat.mul_comm, Nat.div_mul; [ | now destruct g ].
  destruct bb; [ now rewrite Nat.mul_0_r in H2 | flia ].
Qed.

Theorem GQpair_add_l : ∀ a b c,
  a ≠ 0 → b ≠ 0 → c ≠ 0 → ((a + b) // c = a // c + b // c)%GQ.
Proof.
intros * Ha Hb Hc.
apply GQeq_eq.
rewrite GQadd_pair; [ | easy | easy | easy | easy ].
rewrite Nat.mul_comm, <- Nat.mul_add_distr_l.
rewrite <- GQmul_pair; [ | easy | easy | flia Ha | easy ].
rewrite GQpair_diag; [ | easy ].
now rewrite GQmul_1_l.
Qed.

Theorem GQpair_sub_l : ∀ a b c,
  b < a → b ≠ 0 → c ≠ 0 → ((a - b) // c = a // c - b // c)%GQ.
Proof.
intros * Hba Hb Hc.
apply GQeq_eq.
rewrite GQsub_pair; [ | flia Hba | easy | easy | easy | ]; cycle 1. {
  rewrite Nat.mul_comm.
  apply Nat.mul_lt_mono_pos_r; [ flia Hc | easy ].
}
rewrite Nat.mul_comm, <- Nat.mul_sub_distr_l.
rewrite <- GQmul_pair; [ | easy | easy | flia Hba | easy ].
rewrite GQpair_diag; [ | easy ].
now rewrite GQmul_1_l.
Qed.

Theorem GQadd_cancel_l : ∀ x y z, (x + y)%GQ = (x + z)%GQ ↔ y = z.
Proof.
intros.
split; intros Hyz; [ | now subst y ].
destruct x as (x, Hx), y as (y, Hy), z as (z, Hz).
move y before x; move z before y.
apply GQeq_eq; cbn.
apply GQeq_eq in Hyz.
cbn in Hyz.
apply PQeq_red; [ now apply gcd_1_PQred | now apply gcd_1_PQred | ].
apply (PQadd_cancel_l _ _ x).
rewrite <- PQred_eq; symmetry.
rewrite <- PQred_eq; symmetry.
now rewrite Hyz.
Qed.

Theorem GQadd_cancel_r : ∀ x y z, (x + z)%GQ = (y + z)%GQ ↔ x = y.
Proof.
intros.
setoid_rewrite GQadd_comm.
apply GQadd_cancel_l.
Qed.

Theorem GQmul_cancel_l : ∀ x y z, (x * y)%GQ = (x * z)%GQ ↔ y = z.
Proof.
intros.
split; intros Hyz; [ | now subst y ].
destruct x as (x, Hx), y as (y, Hy), z as (z, Hz).
move y before x; move z before y.
apply GQeq_eq; cbn.
apply GQeq_eq in Hyz.
cbn in Hyz.
apply PQeq_red; [ now apply gcd_1_PQred | now apply gcd_1_PQred | ].
apply (PQmul_cancel_l _ _ x).
rewrite <- PQred_eq; symmetry.
rewrite <- PQred_eq; symmetry.
now rewrite Hyz.
Qed.

Theorem GQmul_cancel_r : ∀ x y z, (x * z)%GQ = (y * z)%GQ ↔ x = y.
Proof.
intros.
setoid_rewrite GQmul_comm.
apply GQmul_cancel_l.
Qed.

Theorem GQmul_inv_r : ∀ x, (x * / x = 1)%GQ.
Proof.
intros.
apply GQeq_eq; cbn.
destruct x as (px, Hpx); cbn.
rewrite <- PQred_mul_r.
unfold "*"%PQ, "/"%PQ.
unfold PQmul_num1, PQmul_den1; cbn.
rewrite Nat.mul_comm.
apply PQred_diag.
now do 2 rewrite Nat.add_1_r.
Qed.

Theorem GQmul_inv_l : ∀ x, (/ x * x = 1)%GQ.
Proof.
intros; rewrite GQmul_comm.
apply GQmul_inv_r.
Qed.

Theorem GQpair_lt_nat_l : ∀ a b c, a ≠ 0 → b ≠ 0 → c ≠ 0 →
  (a // 1 < b // c)%GQ → a * c < b.
Proof.
intros * Ha Hb Hc Habc.
unfold "<"%GQ in Habc; cbn in Habc.
apply PQred_lt in Habc.
unfold "<"%PQ, nd in Habc; cbn in Habc.
rewrite Nat.mul_1_r in Habc.
destruct a; [ easy | ].
destruct b; [ easy | ].
destruct c; [ easy | ].
do 3 rewrite Nat.sub_succ, Nat.sub_0_r in Habc.
now do 3 rewrite Nat.add_1_r in Habc.
Qed.

Theorem GQpair_lt_nat_r : ∀ a b c, a ≠ 0 → b ≠ 0 → c ≠ 0 →
  (a // b < c // 1)%GQ → a < b * c.
Proof.
intros * Ha Hb Hc Habc.
unfold "<"%GQ in Habc; cbn in Habc.
apply PQred_lt in Habc.
unfold "<"%PQ, nd in Habc; cbn in Habc.
rewrite Nat.mul_1_r, Nat.mul_comm in Habc.
destruct a; [ easy | ].
destruct b; [ easy | ].
destruct c; [ easy | ].
do 3 rewrite Nat.sub_succ, Nat.sub_0_r in Habc.
now do 3 rewrite Nat.add_1_r in Habc.
Qed.

(*
Theorem glop : ∀ a b, a ≠ 0 → b ≠ 0 →
  (a // b < 1)%GQ → a < b.
Proof.
intros * Ha Hb Hab.
apply (GQpair_lt_nat_r _ _ 1) in Hab.
*)

Theorem GQpair_le_nat_l : ∀ a b c, a ≠ 0 → b ≠ 0 → c ≠ 0 →
  (a // 1 ≤ b // c)%GQ → a * c ≤ b.
Proof.
intros * Ha Hb Hc Habc.
unfold "<"%GQ in Habc; cbn in Habc.
apply PQred_le in Habc.
unfold "≤"%PQ, nd in Habc; cbn in Habc.
rewrite Nat.mul_1_r in Habc.
destruct a; [ easy | ].
destruct b; [ easy | ].
destruct c; [ easy | ].
do 3 rewrite Nat.sub_succ, Nat.sub_0_r in Habc.
now do 3 rewrite Nat.add_1_r in Habc.
Qed.

Theorem GQpair_le_nat_r : ∀ a b c, a ≠ 0 → b ≠ 0 → c ≠ 0 →
  (a // b ≤ c // 1)%GQ → a ≤ b * c.
Proof.
intros * Ha Hb Hc Habc.
unfold "≤"%GQ in Habc; cbn in Habc.
apply PQred_le in Habc.
unfold "≤"%PQ, nd in Habc; cbn in Habc.
rewrite Nat.mul_1_r, Nat.mul_comm in Habc.
destruct a; [ easy | ].
destruct b; [ easy | ].
destruct c; [ easy | ].
do 3 rewrite Nat.sub_succ, Nat.sub_0_r in Habc.
now do 3 rewrite Nat.add_1_r in Habc.
Qed.

Theorem GQle_decidable : ∀ x y, Decidable.decidable (x ≤ y)%GQ.
Proof.
intros.
unfold Decidable.decidable.
unfold "≤"%GQ.
destruct x as (x & Hx).
destruct y as (y & Hy).
move y before x; cbn.
apply PQle_decidable.
Qed.
