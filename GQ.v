(* rationals where num and den always common primes *)

Require Import Utf8 Arith PQ.
Set Nested Proofs Allowed.

Delimit Scope GQ_scope with GQ.

Record GQ :=
  GQmake
    { GQnum1 : nat; GQden1 : nat;
      GQprop : Nat.gcd (S GQnum1) (S GQden1) = 1 }.

Definition GQ_of_nat n := GQmake (n - 1) 0 (Nat.gcd_1_r (S (n - 1))).

Definition div_gcd_l x y := Nat.div x (Nat.gcd x y).
Theorem fold_div_gcd_l x y : Nat.div x (Nat.gcd x y) = div_gcd_l x y.
Proof. easy. Qed.

Definition div_gcd_r x y := Nat.div y (Nat.gcd x y).
Theorem fold_div_gcd_r x y : Nat.div y (Nat.gcd x y) = div_gcd_r x y.
Proof. easy. Qed.

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
  GQmake (div_gcd_l n d - 1) (div_gcd_r n d - 1) (GQadd_prop x y).

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
  GQmake (div_gcd_l n d - 1) (div_gcd_r n d - 1) (GQmul_prop x y).

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

Theorem GQnum1_make : ∀ n d p, GQnum1 (GQmake n d p) = n.
Proof. easy. Qed.

Theorem GQden1_make : ∀ n d p, GQden1 (GQmake n d p) = d.
Proof. easy. Qed.

Theorem GQadd_num_make : ∀ xn xd xp yn yd yp,
  GQadd_num (GQmake xn xd xp) (GQmake yn yd yp) = S xn * S yd + S yn * S xd.
Proof. easy. Qed.

Theorem GQadd_den_make : ∀ xn xd xp yn yd yp,
  GQadd_den (GQmake xn xd xp) (GQmake yn yd yp) = S xd * S yd.
Proof. easy. Qed.

Theorem GQadd_num_make_l : ∀ xn xd xp y,
  GQadd_num (GQmake xn xd xp) y = S xn * S (GQden1 y) + S (GQnum1 y) * S xd.
Proof. easy. Qed.

Theorem GQadd_den_make_l : ∀ n d p y,
  GQadd_den (GQmake n d p) y = S d * S (GQden1 y).
Proof. easy. Qed.

Axiom GQeq : ∀ x y, x = y ↔ GQnum1 x = GQnum1 y ∧ GQden1 x = GQden1 y.

Theorem GQadd_comm : ∀ x y, (x + y = y + x)%GQ.
Proof.
intros.
apply GQeq; unfold "+"%GQ.
do 2 rewrite GQnum1_make, GQden1_make.
split; f_equal.
-f_equal; [ apply Nat.add_comm | apply Nat.mul_comm ].
-f_equal; [ apply Nat.add_comm | apply Nat.mul_comm ].
Qed.

Theorem eq_div_gcd_l_1_iff : ∀ a b,
  a ≠ 0 → div_gcd_l a b = 1 ↔ Nat.divide a b.
Proof.
intros * Ha.
split; intros H.
-exists (b / a).
 unfold div_gcd_l in H.
 specialize (Nat.gcd_divide_l a b) as H1.
 destruct H1 as (c, Hc).
 rewrite Hc in H at 1.
 rewrite Nat.div_mul in H.
 +subst c.
  rewrite Nat.mul_1_l in Hc.
  rewrite Hc at 1;
  rewrite Nat.mul_comm, <- Nat.gcd_div_swap, <- Hc.
  rewrite Nat.div_same; [ | easy ].
  now rewrite Nat.mul_1_l.
 +now intros H1; rewrite H1, Nat.mul_0_r in Hc.
-destruct H as (c, Hc); subst b.
 unfold div_gcd_l.
 rewrite Nat.mul_comm, Nat.gcd_mul_diag_l; [ | apply Nat.le_0_l ].
 now apply Nat.div_same.
Qed.

Theorem eq_div_gcd_l_same_iff : ∀ a b,
  a ≠ 0 → div_gcd_l a b = a ↔ Nat.gcd a b = 1.
Proof.
intros * Ha.
unfold div_gcd_l.
split; intros H.
-specialize (Nat.gcd_divide_l a b) as H1.
 destruct H1 as (c, Hc).
 rewrite Hc in H at 1.
 rewrite Nat.div_mul in H.
 +subst c; symmetry in Hc.
  rewrite <- Nat.mul_1_r in Hc.
  now apply Nat.mul_cancel_l in Hc.
 +now intros H1; rewrite H1, Nat.mul_0_r in Hc.
-now rewrite H, Nat.div_1_r.
Qed.

Theorem div_gcd_l_r : ∀ a b, div_gcd_l a b = div_gcd_r b a.
Proof.
intros.
unfold div_gcd_l, div_gcd_r.
now rewrite Nat.gcd_comm.
Qed.

Theorem eq_div_gcd_r_same_iff : ∀ a b,
  b ≠ 0 → div_gcd_r a b = b ↔ Nat.gcd a b = 1.
Proof.
intros * Ha.
split; intros H.
-rewrite Nat.gcd_comm.
 apply eq_div_gcd_l_same_iff; [ easy | ].
 rewrite <- H at 2.
 apply div_gcd_l_r.
-unfold div_gcd_r; rewrite H.
 apply Nat.div_1_r.
Qed.

Definition GQ_of_PQ x := GQN (S (PQnum1 x)) (S (PQden1 x)).
Definition PQ_of_GQ x := PQmake (GQnum1 x) (GQden1 x).

Theorem GQ_o_PQ : ∀ x, GQ_of_PQ (PQ_of_GQ x) = x.
Proof.
intros (xn, xd, xp).
apply GQeq.
unfold GQ_of_PQ, PQ_of_GQ; simpl.
unfold GQmul_num, GQadd_den, GQ_of_nat; simpl.
do 2 rewrite Nat.sub_0_r.
rewrite Nat.add_0_r, Nat.mul_1_r.
split.
-apply eq_div_gcd_l_same_iff in xp; [ | easy ].
 now rewrite xp, Nat.sub_succ, Nat.sub_0_r.
-apply eq_div_gcd_r_same_iff in xp; [ | easy ].
 now rewrite xp, Nat.sub_succ, Nat.sub_0_r.
Qed.

Theorem GQadd_add_swap : ∀ x y z, (x + y + z = x + z + y)%GQ.
Proof.
intros.
apply GQeq; unfold "+"%GQ.
do 2 rewrite GQnum1_make, GQden1_make.
split; f_equal.
-do 2 rewrite GQadd_num_make_l.
 do 2 rewrite GQadd_den_make_l.
 remember S as f.
 remember Nat.gcd as g.
 destruct x as (xn, xd, xp).
 destruct y as (yn, yd, yp).
 destruct z as (zn, zd, zp).
 simpl; subst f g.
 do 2 rewrite GQadd_num_make.
 do 2 rewrite GQadd_den_make.
 move xp at bottom; move yp at bottom; move zp at bottom.
 setoid_rewrite <- Nat.sub_succ_l.
 +do 4 rewrite Nat.sub_succ, Nat.sub_0_r.
  remember (S xn * S yd + S yn * S xd) as a1.
  remember (S xd * S yd) as b1.
  remember (S xn * S zd + S zn * S xd) as a2.
  remember (S xd * S zd) as b2.
  move b2 before a1; move a2 before a1; move b1 before a1.
  do 2 rewrite <- div_gcd_l_r.
Print div_gcd_l.
Search div_gcd_l.
Search ((_ + _) / Nat.gcd _ _).
Inspect 2.
Check Nat.gauss.
...
(1/2+1/2)+1/3 = 4/4+1/3 = 1/1+1/3 = 4/3 = 4/3
1/2+(1/2+1/3) = 1/2+5/6 = 1/2+5/6 = 16/12 = 4/3

Search (Nat.gcd _ _ = 1).

...
Search (_ / Nat.gcd _ _).
...

Theorem GQadd_assoc : ∀ x y z, ((x + y) + z = x + (y + z))%GQ.
Proof.
intros.
rewrite GQadd_comm.
remember (x + y)%GQ as t eqn:Ht.
rewrite GQadd_comm in Ht; subst t.
setoid_rewrite GQadd_comm.
apply GQadd_add_swap.
Qed.

Definition div_gcd x y := Nat.div x (Nat.gcd x y).

(* y a-t-il une fonction qui fait Nat.div x (Nat.gcd x y) ?
   car c'est toujours divisible ! *)
