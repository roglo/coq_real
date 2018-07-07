(* rationals where num and den always common primes *)

Require Import Utf8 Arith.
Set Nested Proofs Allowed.

Delimit Scope GQ_scope with GQ.

Record GQ :=
  GQmake
    { GQnum1 : nat; GQden1 : nat;
      GQprop : Nat.gcd (S GQnum1) (S GQden1) = 1 }.

Definition GQ_of_nat n := GQmake (n - 1) 0 (Nat.gcd_1_r (S (n - 1))).

Definition GQadd_num x y :=
  S (GQnum1 x) * S (GQden1 y) + S (GQnum1 y) * S (GQden1 x).
Definition GQadd_den x y :=
  S (GQden1 x) * S (GQden1 y).

Theorem GQadd_prop : ∀ x y
  (n := GQadd_num x y) (d := GQadd_den x y) (g := Nat.gcd n d),
  Nat.gcd (S (n / g - 1)) (S (d / g - 1)) = 1.
Proof.
intros.
rewrite <- Nat.sub_succ_l.
-rewrite <- Nat.sub_succ_l.
 +do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
  rewrite Nat.gcd_div_gcd; [ easy | | easy ].
  subst g; intros H.
  now apply Nat.gcd_eq_0 in H.
 +specialize (Nat.gcd_divide_r n d) as H.
  fold g in H.
  unfold Nat.divide in H.
  destruct H as (c & Hc).
  rewrite Hc, Nat.div_mul.
  *destruct c; [ easy | apply Nat.lt_0_succ ].
  *now intros H; rewrite Nat.mul_comm, H in Hc.
-specialize (Nat.gcd_divide_l n d) as H.
 fold g in H.
 unfold Nat.divide in H.
 destruct H as (c & Hc).
 rewrite Hc, Nat.div_mul.
 *destruct c; [ easy | apply Nat.lt_0_succ ].
 *now intros H; rewrite Nat.mul_comm, H in Hc.
Qed.

Definition GQadd x y :=
  let n := GQadd_num x y in
  let d := GQadd_den x y in
  let g := Nat.gcd n d in
  GQmake (Nat.div n g - 1) (Nat.div d g - 1) (GQadd_prop x y).

Notation "x + y" := (GQadd x y) : GQ_scope.

Compute (GQadd (GQ_of_nat 7) (GQ_of_nat 13)).

Definition GQmul_num x y :=
  S (GQnum1 x) * S (GQnum1 y).

Theorem GQmul_prop : ∀ x y
  (n := GQmul_num x y) (d := GQadd_den x y) (g := Nat.gcd n d),
  Nat.gcd (S (n / g - 1)) (S (d / g - 1)) = 1.
Proof.
(* tactique à faire, ou lemmes communs avec GQadd_prop *)
intros.
rewrite <- Nat.sub_succ_l.
-rewrite <- Nat.sub_succ_l.
 +do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
  rewrite Nat.gcd_div_gcd; [ easy | | easy ].
  subst g; intros H.
  now apply Nat.gcd_eq_0 in H.
 +specialize (Nat.gcd_divide_r n d) as H.
  fold g in H.
  unfold Nat.divide in H.
  destruct H as (c & Hc).
  rewrite Hc, Nat.div_mul.
  *destruct c; [ easy | apply Nat.lt_0_succ ].
  *now intros H; rewrite Nat.mul_comm, H in Hc.
-specialize (Nat.gcd_divide_l n d) as H.
 fold g in H.
 unfold Nat.divide in H.
 destruct H as (c & Hc).
 rewrite Hc, Nat.div_mul.
 *destruct c; [ easy | apply Nat.lt_0_succ ].
 *now intros H; rewrite Nat.mul_comm, H in Hc.
Qed.

Definition GQmul x y :=
  let n := GQmul_num x y in
  let d := GQadd_den x y in
  let g := Nat.gcd n d in
  GQmake (Nat.div n g - 1) (Nat.div d g - 1) (GQmul_prop x y).

Compute (GQmul (GQ_of_nat 7) (GQ_of_nat 3)).

Theorem GQinv_prop : ∀ x, Nat.gcd (S (GQden1 x)) (S (GQnum1 x)) = 1.
Proof.
intros.
specialize (GQprop x) as H.
now rewrite Nat.gcd_comm in H.
Qed.

Definition GQinv x := GQmake (GQden1 x) (GQnum1 x) (GQinv_prop x).

Notation "x * y" := (GQmul x y) : GQ_scope.
Notation "x / y" := (GQmul x (GQinv y)) : GQ_scope.
Notation "/ x" := (GQinv x) : GQ_scope.

Definition GQN a b := (GQ_of_nat a / GQ_of_nat b)%GQ.

(*
Notation "x +/+ y" := (GQmake x y _) (at level 40, only parsing) : GQ_scope.
*)

Compute GQN 7 3.
Compute GQN 16 24.
Compute GQN 2 4.
Compute GQN 3 6.
Compute GQN 4 8.

Axiom GQeq : ∀ x y, x = y ↔ GQnum1 x = GQnum1 y ∧ GQden1 x = GQden1 y.

Theorem GQnum1_make : ∀ n d p, GQnum1 (GQmake n d p) = n.
Proof. easy. Qed.

Theorem GQden1_make : ∀ n d p, GQden1 (GQmake n d p) = d.
Proof. easy. Qed.

Theorem GQ_add_comm : ∀ x y, (x + y = y + x)%GQ.
Proof.
intros.
apply GQeq; unfold "+"%GQ.
do 2 rewrite GQnum1_make, GQden1_make.
split; f_equal.
-f_equal; [ apply Nat.add_comm | ].
 f_equal; [ apply Nat.add_comm | apply Nat.mul_comm ].
-f_equal; [ apply Nat.mul_comm | ].
 f_equal; [ apply Nat.add_comm | apply Nat.mul_comm ].
Qed.

Definition pouet xn xd yn yd := S xn * S yd + S yn * S xd.
Theorem GQadd_num_pouet : ∀ x y,
  GQadd_num x y = pouet (GQnum1 x) (GQden1 x) (GQnum1 y) (GQden1 y).
Proof. easy. Qed.

Definition glop xd yd := S xd * S yd.
Theorem GQadd_den_glop : ∀ x y, GQadd_den x y = glop (GQden1 x) (GQden1 y).
Proof. easy. Qed.

Theorem GQ_add_assoc : ∀ x y z, ((x + y) + z = x + (y + z))%GQ.
Proof.
intros.
apply GQeq; unfold "+"%GQ.
do 2 rewrite GQnum1_make, GQden1_make.
split; f_equal.
-idtac.
 rewrite GQadd_num_pouet, GQnum1_make, GQden1_make.
...
