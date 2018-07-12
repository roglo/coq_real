(* rationals where num and den always common primes *)

Require Import Utf8 Arith.
Require Import PQ Nat_ggcd.
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

(*
Compute (GQadd (GQ_of_nat 7) (GQ_of_nat 13)).
*)

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

Theorem div_gcd_l_r : ∀ a b, div_gcd_l a b = div_gcd_r b a.
Proof.
intros.
unfold div_gcd_l, div_gcd_r.
now rewrite Nat.gcd_comm.
Qed.

(*
Theorem ggcd_div_gcd_l : ∀ a b,
  b ≠ 0 → fst (snd (ggcd a b)) = div_gcd_l a b.
Proof.
intros * Hb.
specialize (ggcd_correct_divisors a b Hb) as H.
remember (ggcd a b) as g eqn:Hg.
destruct g as (g, (aa, bb)).
destruct H as (H1, H2); simpl.
unfold div_gcd_l.
subst a b.
specialize (ggcd_gcd (g * aa) (g * bb)) as H1.
rewrite <- Hg in H1; simpl in H1.
rewrite <- H1.
rewrite Nat.mul_comm, Nat.div_mul; [ easy | ].
now intros H; subst g.
Qed.

Theorem ggcd_div_gcd_r : ∀ a b,
  b ≠ 0 → snd (snd (ggcd a b)) = div_gcd_r a b.
Proof.
intros * Hb.
specialize (ggcd_correct_divisors a b Hb) as H.
remember (ggcd a b) as g eqn:Hg.
destruct g as (g, (aa, bb)).
destruct H as (H1, H2); simpl.
unfold div_gcd_r.
subst a b.
specialize (ggcd_gcd (g * aa) (g * bb)) as H1.
rewrite <- Hg in H1; simpl in H1.
rewrite <- H1.
rewrite Nat.mul_comm, Nat.div_mul; [ easy | ].
now intros H; subst g.
Qed.
*)

Theorem div_gcd_l_succ_l_pos : ∀ n d, 0 < div_gcd_l (S n) d.
Proof.
intros.
unfold div_gcd_l.
specialize (Nat.gcd_divide_l (S n) d) as (c, Hc).
rewrite Hc at 1.
rewrite Nat.div_mul.
-destruct c; [ easy | apply Nat.lt_0_succ ].
-intros H; rewrite H in Hc.
 now rewrite Nat.mul_0_r in Hc.
Qed.

(*
Definition GQN a b := (GQ_of_nat a / GQ_of_nat b)%GQ.
*)

Theorem GQN_prop : ∀ a b,
  Nat.gcd (S (div_gcd_l a b - 1)) (S (div_gcd_r a b - 1)) = 1.
Proof.
intros.
destruct a; [ now destruct b | ].
destruct b.
-remember Nat.gcd as f.
 unfold div_gcd_l, div_gcd_r; simpl.
 rewrite Nat.sub_diag.
 rewrite Nat.div_0_l; [ | easy ].
 remember Nat.div as g; simpl; subst g.
 rewrite Nat.div_same; [ now subst f | easy ].
-rewrite <- Nat.sub_succ_l; [ | apply div_gcd_l_succ_l_pos ].
 rewrite <- div_gcd_l_r.
 rewrite <- Nat.sub_succ_l; [ | apply div_gcd_l_succ_l_pos ].
 do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
 remember Nat.gcd as f.
 unfold div_gcd_l at 2.
 rewrite Nat.gcd_comm.
 subst f.
 apply Nat.gcd_div_gcd; [ | easy ].
 specialize (ggcd_correct_divisors (S a) (S b)) as H.
 remember (ggcd (S a) (S b)) as g eqn:Hg; symmetry in Hg.
 destruct g as (g, (aa, bb)).
 destruct H as (Ha, Hb).
 specialize (ggcd_gcd (S a) (S b)) as H1.
 rewrite Hg in H1.
 assert (Hgz : g ≠ 0) by now intros H; rewrite H in Ha.
 apply Nat.gcd_div_gcd in H1; simpl in H1; [ | easy ].
 rewrite Ha, Hb in H1.
 rewrite Nat.mul_comm, Nat.div_mul in H1; [ | easy ].
 rewrite Nat.mul_comm, Nat.div_mul in H1; [ | easy ].
 rewrite Ha, Hb.
 rewrite Nat.gcd_mul_mono_l.
 intros H.
 apply Nat.eq_mul_0 in H.
 destruct H; [ easy | ].
 now rewrite H1 in H.
Qed.
Definition GQN a b := GQmake (div_gcd_l a b - 1) (div_gcd_r a b - 1) (GQN_prop a b).

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
Arguments GQ_of_PQ x%PQ.
Arguments PQ_of_GQ x%GQ.

Theorem GQ_o_PQ : ∀ x, GQ_of_PQ (PQ_of_GQ x) = x.
Proof.
intros (xn, xd, xp).
apply GQeq; simpl.
split.
-apply eq_div_gcd_l_same_iff in xp; [ | easy ].
 now rewrite xp, Nat.sub_succ, Nat.sub_0_r.
-apply eq_div_gcd_r_same_iff in xp; [ | easy ].
 now rewrite xp, Nat.sub_succ, Nat.sub_0_r.
Qed.

Theorem GQadd_PQadd : ∀ x y, (x + y)%GQ = GQ_of_PQ (PQ_of_GQ x + PQ_of_GQ y).
Proof.
intros.
apply GQeq; simpl.
PQtac1.
rewrite <- Nat.sub_succ_l; [ | simpl; flia ].
rewrite Nat.sub_succ, Nat.sub_0_r.
now rewrite <- Nat.sub_succ_l; [ easy | simpl; flia ].
Qed.

Theorem GQnum1_of_nat : ∀ m, GQnum1 (GQ_of_nat m) = m - 1.
Proof. easy. Qed.

Theorem GQden1_of_nat : ∀ m, GQden1 (GQ_of_nat m) = 0.
Proof. easy. Qed.

Theorem GQnum1_GQN : ∀ n d,
  GQnum1 (GQN (S n) (S d)) = div_gcd_l (S n) (S d) - 1.
Proof. easy. Qed.

Theorem GQden1_GQN : ∀ n d,
  GQden1 (GQN (S n) (S d)) = div_gcd_r (S n) (S d) - 1.
Proof. easy. Qed.

Theorem GQ_of_PQ_red_prop : ∀ x, Nat.gcd (S (PQnum1 (PQred x) - 1)) (S (PQden1 (PQred x) - 1)) = 1.
Proof.
...

Theorem GQ_of_PQ_red : ∀ x, GQ_of_PQ x = GQmake (PQnum1 (PQred x) - 1) (PQden1 (PQred x) - 1) (glop x).
Proof.
Admitted.
*)

(**)
Theorem GQ_of_PQ_additive : ∀ x y,
  GQ_of_PQ (x + y) = (GQ_of_PQ x + GQ_of_PQ y)%GQ.
Proof.
intros.
...

intros.
apply GQeq; simpl.
unfold GQadd_num, GQmul_num, GQadd_den.
do 2 rewrite <- div_gcd_l_r.
unfold PQadd_num1, PQadd_den1, nd.
do 4 rewrite Nat.add_1_r.
do 2 (rewrite <- Nat.sub_succ_l; [ | simpl; flia ]).
do 2 rewrite Nat.sub_succ, Nat.sub_0_r.
unfold GQ_of_PQ.
do 2 rewrite GQnum1_GQN.
do 2 rewrite GQden1_GQN.
do 2 rewrite <- div_gcd_l_r.
do 4 (rewrite <- Nat.sub_succ_l; [ | apply div_gcd_l_succ_l_pos ]).
do 4 rewrite Nat.sub_succ, Nat.sub_0_r.
split; f_equal.
-remember (div_gcd_l (S (PQnum1 x)) (S (PQden1 x))) as a1 eqn:Ha1.
 remember (div_gcd_l (S (PQden1 x)) (S (PQnum1 x))) as a2 eqn:Ha2.
 remember (div_gcd_l (S (PQnum1 y)) (S (PQden1 y))) as b1 eqn:Hb1.
 remember (div_gcd_l (S (PQden1 y)) (S (PQnum1 y))) as b2 eqn:Hb2.
 move b2 before a1; move b1 before a1; move a2 before a1.
 destruct x as (xn, xd).
 destruct y as (yn, yd).
 remember S as f; simpl in *; subst f.
 rewrite <- ggcd_div_gcd_l; [ | simpl; flia ].
 rewrite <- ggcd_div_gcd_l.
 +remember (S xn * S yd + S yn * S xd) as u1 eqn:Hu1.
  remember (S xd * S yd) as v1 eqn:Hv1.
  move v1 before u1.
  specialize (ggcd_correct_divisors u1 v1) as H1.
  assert (H : v1 ≠ 0) by now intros H; subst v1.
  specialize (H1 H); clear H.
  remember (ggcd u1 v1) as g1 eqn:Hg1; symmetry in Hg1.
  destruct g1 as (g1, (aa1, bb1)); simpl.
  destruct H1 as (H1, H2).
  remember (a1 * b2 + b1 * a2) as u2 eqn:Hu2.
  remember (a2 * b2) as v2 eqn:Hv2.
  move v2 before v1; move u2 before v1.
  specialize (ggcd_correct_divisors u2 v2) as H3.
  assert (H : v2 ≠ 0). {
    intros H; move H at top; subst v2.
    symmetry in Hv2.
    apply Nat.eq_mul_0 in Hv2.
    destruct Hv2 as [Hv2| Hv2].
    -move Hv2 at top; subst a2.
     specialize (div_gcd_l_succ_l_pos xd (S xn)) as H.
     now rewrite <- Ha2 in H.
    -move Hv2 at top; subst b2.
     specialize (div_gcd_l_succ_l_pos yd (S yn)) as H.
     now rewrite <- Hb2 in H.
  }
  specialize (H3 H); clear H.
  remember (ggcd u2 v2) as g2 eqn:Hg2; symmetry in Hg2.
  destruct g2 as (g2, (aa2, bb2)); simpl.
  destruct H3 as (H3, H4).
  move g2 before g1; move bb2 before bb1; move aa2 before bb1.
  move Hg1 at bottom; move Hg2 at bottom.
  move H2 before H3; move H1 before H2.
  move Hu1 before Hu2; move Hv1 before Hu2.
...
Require Import ZArith.
Search Z.ggcd.
...
Print Qred.
Print Z.ggcd.
About Z.ggcd.
Print Pos.ggcd.
Close Scope Q_scope.
...
(*
 unfold div_gcd_l at 2.
 specialize (Nat.gcd_divide_l (a1 * b2 + b1 * a2) (a2 * b2)) as (c, Hc).
 rewrite Hc at 1.
 rewrite Nat.div_mul.
...
*)

Theorem GQadd_add_swap : ∀ x y z, (x + y + z = x + z + y)%GQ.
Proof.
(*
intros.
apply GQeq; unfold "+"%GQ.
do 2 rewrite GQnum1_make, GQden1_make.
do 2 rewrite GQadd_num_make_l.
do 2 rewrite GQadd_den_make_l.
...
*)
(**)
intros.
do 4 rewrite GQadd_PQadd.
remember (PQ_of_GQ x) as x' eqn:Hx'.
remember (PQ_of_GQ y) as y' eqn:Hy'.
remember (PQ_of_GQ z) as z' eqn:Hz'.
move z' before x'; move y' before x'.
do 4 rewrite GQ_of_PQ_additive.
do 2 rewrite GQ_o_PQ.
do 4 rewrite <- GQ_of_PQ_additive.
now rewrite PQadd_add_swap.
...
(**)
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
Search (Nat.gcd _ _ = 1).
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
