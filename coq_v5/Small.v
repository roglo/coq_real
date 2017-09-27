Require Import Utf8 NPeano.

Notation "a ^ b" := (Nat.pow a b).

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
do 2 rewrite <- Nat.sub_add_distr.
f_equal.
apply Nat.add_comm.
Qed.

Theorem small : ∀ r, r ≥ 2 →
  ∀ i n, n ≥ r * (i + 2) → n * (r - 1) + r < r ^ (n - (i + 1)).
Proof.
intros r Hr * Hnr.
induction n.
 exfalso.
 apply Nat.le_0_r in Hnr.
 apply Nat.eq_mul_0 in Hnr.
 destruct Hnr; [ subst r; easy | ].
 now apply Nat.eq_add_0 in H.

 destruct (Nat.eq_dec (S n) (r * (i + 2))) as [Hn| Hn].
  rewrite Hn.
  remember (r * (i + 2) - (i + 1)) as a eqn:Ha.
  replace r with (r * 1) at 3 by apply Nat.mul_1_r.
  rewrite <- Nat.mul_assoc.
  rewrite <- Nat.mul_add_distr_l.
  replace ((i + 2) * (r - 1) + 1) with a.

Focus 2.
   subst a.
   rewrite Nat.mul_sub_distr_l.
   rewrite Nat.mul_1_r.
   rewrite Nat.mul_add_distr_l.
   rewrite Nat.mul_add_distr_r.
   rewrite <- Nat.add_sub_swap.
bbb.
