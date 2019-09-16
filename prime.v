(* playing with prime numbers, as a break *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz List.
Import List.ListNotations.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).

Fixpoint prime_test n d :=
  match d with
  | 0 | 1 => true
  | S d' =>
      match n mod d with
      | 0 => false
      | _ => prime_test n d'
      end
  end.

Definition is_prime n :=
  match n with
  | 0 | 1 => false
  | S n' => prime_test n n'
  end.

Theorem fold_mod_succ : ∀ n d, d - snd (Nat.divmod n d 0 d) = n mod (S d).
Proof. easy. Qed.

Theorem not_prime_div : ∀ n d, 2 ≤ n → d < n →
  prime_test n d = false
  → ∃ m, is_prime m = true ∧ Nat.divide m n.
Proof.
intros * Hn Hd Hp.
revert n Hn Hd Hp.
induction d; intros; [ easy | ].
cbn in Hp.
rewrite fold_mod_succ in Hp.
destruct d; [ easy | ].
remember (n mod (S (S d))) as m eqn:Hm.
symmetry in Hm.
destruct m. {
  clear Hp.
  apply Nat.mod_divide in Hm; [ | easy ].
  remember (is_prime (S (S d))) as b eqn:Hb.
  symmetry in Hb.
  destruct b; [ now exists (S (S d)) | ].
  unfold is_prime in Hb.
  apply IHd in Hb; [ | flia | flia ].
  destruct Hb as (m & Hpm & Hmd).
  exists m.
  split; [ easy | ].
  now apply (Nat.divide_trans _ (S (S d))).
}
apply IHd in Hp; [ | easy | flia Hd ].
destruct Hp as (p & Hp & Hpn).
now exists p.
Qed.

Theorem prime_divisor : ∀ n, 2 ≤ n →
  ∃ d, is_prime d = true ∧ Nat.divide d n.
Proof.
intros * Hn.
destruct n; [ flia Hn | ].
destruct n; [ flia Hn | ].
clear Hn.
remember (is_prime (S (S n))) as b eqn:Hb.
symmetry in Hb.
destruct b; [ now exists (S (S n)) | ].
apply (not_prime_div _ (S n)); [ flia | flia | easy ].
Qed.

Theorem Nat_fact_succ : ∀ n, fact (S n) = S n * fact n.
Proof. easy. Qed.

Theorem Nat_divide_fact_fact : ∀ n d, Nat.divide (fact (n - d)) (fact n).
Proof.
intros *.
revert n.
induction d; intros; [ rewrite Nat.sub_0_r; apply Nat.divide_refl | ].
destruct n; [ apply Nat.divide_refl | ].
rewrite Nat.sub_succ.
apply (Nat.divide_trans _ (fact n)); [ apply IHd | ].
rewrite Nat_fact_succ.
now exists (S n).
Qed.

Theorem Nat_le_divides_fact : ∀ n d, d ≤ n → Nat.divide (fact d) (fact n).
Proof.
intros * Hdn.
replace d with (n - (n - d)) by flia Hdn.
apply Nat_divide_fact_fact.
Qed.

Theorem Nat_fact_divides_small : ∀ n d,
  1 ≤ d ≤ n
  → fact n = fact n / d * d.
Proof.
intros * (Hd, Hdn).
specialize (Nat_le_divides_fact n d Hdn) as H1.
destruct H1 as (c, Hc).
rewrite Hc at 2.
destruct d; [ easy | ].
rewrite Nat_fact_succ.
rewrite (Nat.mul_comm (S d)).
rewrite Nat.mul_assoc.
rewrite Nat.div_mul; [ | easy ].
rewrite Hc, Nat_fact_succ.
now rewrite Nat.mul_assoc, Nat.mul_shuffle0.
Qed.

Theorem infinite_primes : ∀ n, ∃ m, m > n ∧ is_prime m = true.
Proof.
intros.
specialize (prime_divisor (fact n + 1)) as H1.
assert (H : 2 ≤ fact n + 1). {
  clear.
  induction n; [ easy | ].
  rewrite Nat_fact_succ.
  apply (Nat.le_trans _ (fact n + 1)); [ easy | ].
  apply Nat.add_le_mono_r.
  cbn; flia.
}
specialize (H1 H); clear H.
destruct H1 as (d & Hd & Hdn).
exists d.
split; [ | easy ].
destruct (lt_dec n d) as [Hnd| Hnd]; [ easy | ].
apply Nat.nlt_ge in Hnd; exfalso.
assert (Ht : Nat.divide d (fact n)). {
  exists (fact n / d).
  apply Nat_fact_divides_small.
  split; [ | easy ].
  destruct d; [ easy | flia ].
}
destruct Hdn as (z, Hz).
destruct Ht as (t, Ht).
rewrite Ht in Hz.
apply Nat.add_sub_eq_l in Hz.
rewrite <- Nat.mul_sub_distr_r in Hz.
apply Nat.eq_mul_1 in Hz.
now destruct Hz as (Hz, H); subst d.
Qed.

(* ζ(s) = Σ (n ∈ ℕ) 1/n^s = Π (p ∈ primes) 1/(1-1/p^s) *)

Class field :=
  { f_type : Set;
    f_zero : f_type;
    f_one : f_type;
    f_add : f_type → f_type → f_type;
    f_mul : f_type → f_type → f_type;
    f_opp : f_type → f_type;
    f_inv : f_type → f_type;
    f_pow : nat → f_type → f_type;
    f_add_comm : ∀ x y, f_add x y = f_add y x;
    f_add_assoc : ∀ x y z, f_add x (f_add y z) = f_add (f_add x y) z;
    f_add_0_r : ∀ x, f_add x f_zero = x;
    f_add_opp_diag_l : ∀ x, f_add (f_opp x) x = f_zero;
    f_mul_comm : ∀ x y, f_mul x y = f_mul y x;
    f_mul_assoc : ∀ x y z, f_mul x (f_mul y z) = f_mul (f_mul x y) z;
    f_mul_1_l : ∀ x, f_mul f_one x = x;
    f_mul_inv_diag_l : ∀ x, x ≠ f_zero → f_mul (f_inv x) x = f_one;
    f_mul_add_distr_l : ∀ x y z,
      f_mul x (f_add y z) = f_add (f_mul x y) (f_mul x z);
    f_pow_mul_l : ∀ a b x, f_pow (a * b) x = f_mul (f_pow a x) (f_pow b x);
    f_pow_nonzero : ∀ n x, n ≠ 0 → f_pow n x ≠ f_zero }.

Declare Scope field_scope.
Delimit Scope field_scope with F.

Definition f_sub {F : field} x y := f_add x (f_opp y).
Definition f_div {F : field} x y := f_mul x (f_inv y).

Notation "- x" := (f_opp x) : field_scope.
Notation "x + y" := (f_add x y) : field_scope.
Notation "x - y" := (f_sub x y) : field_scope.
Notation "x * y" := (f_mul x y) : field_scope.
Notation "x / y" := (f_div x y) : field_scope.
Notation "n ^ x" := (f_pow n x) : field_scope.

Theorem f_add_0_l {F : field} : ∀ x, (f_zero + x)%F = x.
Proof.
intros.
rewrite f_add_comm.
apply f_add_0_r.
Qed.

Theorem f_add_opp_diag_r {F : field} : ∀ x, f_add x (f_opp x) = f_zero.
Proof.
intros.
rewrite f_add_comm.
apply f_add_opp_diag_l.
Qed.

Theorem f_add_sub {F : field} : ∀ x y, (x + y - y)%F = x.
Proof.
intros.
unfold f_sub.
rewrite <- f_add_assoc.
rewrite f_add_opp_diag_r.
now rewrite f_add_0_r.
Qed.

Theorem f_add_move_r {F : field} : ∀ x y z, (x + y)%F = z ↔ x = (z - y)%F.
Proof.
intros.
split.
-intros H.
 rewrite <- H.
 now rewrite f_add_sub.
-intros H.
 rewrite H.
 unfold f_sub.
 rewrite <- f_add_assoc.
 rewrite f_add_opp_diag_l.
 now rewrite f_add_0_r.
Qed.

Theorem f_add_move_0_r {F : field} : ∀ x y, (x + y)%F = f_zero ↔ x = (- y)%F.
Proof.
intros.
split.
-intros H.
 apply f_add_move_r in H.
 unfold f_sub in H.
 now rewrite f_add_0_l in H.
-intros H.
 apply f_add_move_r.
 unfold f_sub.
 now rewrite f_add_0_l.
Qed.

Theorem f_mul_add_distr_r {F : field} : ∀ x y z,
  ((x + y) * z)%F = (x * z + y * z)%F.
Proof.
intros.
rewrite f_mul_comm, f_mul_add_distr_l.
now do 2 rewrite (f_mul_comm z).
Qed.

Theorem f_mul_0_l {F : field} : ∀ x, (f_zero * x)%F = f_zero.
Proof.
intros.
assert (H : (f_zero * x + x = x)%F). {
  transitivity ((f_zero * x + f_one * x)%F).
  -now rewrite f_mul_1_l.
  -rewrite <- f_mul_add_distr_r.
   now rewrite f_add_0_l, f_mul_1_l.
}
apply f_add_move_r in H.
unfold f_sub in H.
now rewrite f_add_opp_diag_r in H.
Qed.

Theorem f_mul_0_r {F : field} : ∀ x, (x * f_zero)%F = f_zero.
Proof.
intros.
rewrite f_mul_comm.
apply f_mul_0_l.
Qed.

Theorem f_mul_opp_l {F : field} : ∀ x y, (- x * y = - (x * y))%F.
Proof.
intros.
apply f_add_move_0_r.
rewrite <- f_mul_add_distr_r.
rewrite f_add_opp_diag_l.
apply f_mul_0_l.
Qed.

Theorem f_mul_opp_r {F : field} : ∀ x y, (x * - y = - (x * y))%F.
Proof.
intros.
now rewrite f_mul_comm, f_mul_opp_l, f_mul_comm.
Qed.

Theorem f_opp_add_distr {F : field} : ∀ x y, (- (x + y))%F = (- x + - y)%F.
Proof.
intros.
symmetry.
apply f_add_move_0_r.
rewrite (f_add_comm x).
rewrite f_add_assoc.
rewrite <- (f_add_assoc _ (- y)%F).
Search (- _ + _)%F.
rewrite f_add_opp_diag_l.
rewrite f_add_0_r.
apply f_add_opp_diag_l.
Qed.

Theorem f_add_add_swap {F : field} : ∀ x y z, (x + y + z = x + z + y)%F.
Proof.
intros.
do 2 rewrite <- f_add_assoc.
f_equal.
apply f_add_comm.
Qed.

Theorem f_opp_involutive {F : field} : ∀ x, (- - x)%F = x.
Proof.
intros.
symmetry.
apply f_add_move_0_r.
apply f_add_opp_diag_r.
Qed.

Theorem f_mul_inv_diag_r {F : field} : ∀ x,
  x ≠ f_zero → f_mul x (f_inv x) = f_one.
Proof.
intros * Hx.
rewrite f_mul_comm.
now apply f_mul_inv_diag_l.
Qed.

Theorem f_mul_1_r {F : field} : ∀ x, (x * f_one)%F = x.
Proof.
intros.
rewrite f_mul_comm.
apply f_mul_1_l.
Qed.

Theorem f_mul_eq_0_l {F : field} : ∀ x y,
  (x * y)%F = f_zero → y ≠ f_zero → x = f_zero.
Proof.
intros * Hxy Hx.
assert (H1 : (x * y * f_inv y = f_zero * f_inv y)%F) by now f_equal.
rewrite <- f_mul_assoc in H1.
rewrite f_mul_inv_diag_r in H1; [ | easy ].
rewrite f_mul_1_r in H1.
now rewrite f_mul_0_l in H1.
Qed.

Theorem f_mul_eq_0_r {F : field} : ∀ x y,
  (x * y)%F = f_zero → x ≠ f_zero → y = f_zero.
Proof.
intros * Hxy Hx.
rewrite f_mul_comm in Hxy.
now apply f_mul_eq_0_l in Hxy.
Qed.

Theorem f_mul_cancel_l {F : field} : ∀ x y z,
  z ≠ f_zero → (z * x = z * y)%F ↔ x = y.
Proof.
intros * Hz.
split; [ | now intros; subst x ].
intros H.
replace (z * y)%F with (- - (z * y))%F in H by apply f_opp_involutive.
apply f_add_move_0_r in H.
rewrite <- f_mul_opp_r in H.
rewrite <- f_mul_add_distr_l in H.
apply f_mul_eq_0_r in H; [ | easy ].
apply f_add_move_0_r in H.
now rewrite f_opp_involutive in H.
Qed.

Theorem f_inv_mul_inv {F : field} : ∀ x y,
  x ≠ f_zero → y ≠ f_zero →
  (f_inv x * f_inv y = f_inv (x * y))%F.
Proof.
intros * Hx Hy.
apply (f_mul_cancel_l _ _ (x * y)%F). {
  intros H.
  apply Hy.
  now apply f_mul_eq_0_r in H.
}
rewrite f_mul_assoc.
rewrite (f_mul_comm x).
rewrite <- (f_mul_assoc y).
rewrite f_mul_inv_diag_r; [ | easy ].
rewrite f_mul_1_r.
rewrite f_mul_inv_diag_r; [ | easy ].
rewrite f_mul_inv_diag_r; [ easy | ].
intros H.
apply Hy.
now apply f_mul_eq_0_l in H.
Qed.

(* https://en.wikipedia.org/wiki/Proof_of_the_Euler_product_formula_for_the_Riemann_zeta_function *)

(* representation of zeta function as series in x where x=1/e^s; we have
     Σ 1/n^s = Σ x^ln(n)
 *)

(* {| ls := u |} represents Σ (n=0,∞) u(n)/(n+1)^s = Σ (n=0,∞) u(n)x^ln(n+1) =
   Σ (n=0,∞) u(n)(x⊗(n+1)) where a⊗b=a^ln(b)=b^ln(a)=e^(ln(a)ln(b)) *)

Class ln_series {F : field} :=
  { ls : nat → f_type }.

Class ln_polyn {F : field} :=
  { lp : list f_type }.

Arguments ls {_}.
Arguments lp {_}.

Definition ls_eq {F : field} s1 s2 := ∀ n, ls s1 n = ls s2 n.

Definition zeta {F : field} := {| ls _ := f_one |}.

Definition zeta_but_mul_of {F : field} d :=
  {| ls n :=
       match S n mod d with
       | 0 => f_zero
       | _ => f_one
       end |}.

Fixpoint log_prod {F : field} u v n i :=
  match i with
  | 0 => f_zero
  | S i' =>
      (match S n mod i with
       | 0 => u i' * v (S n / i - 1)%nat
       | _ => f_zero
       end + log_prod u v n i')%F
  end.

Definition ls_mul {F : field} s1 s2 :=
  {| ls n := log_prod (ls s1) (ls s2) n (S n) |}.

Definition ls_of_pol {F : field} p :=
  {| ls n := List.nth n (lp p) f_zero |}.

Definition ls_pol_mul_l {F : field} p s :=
  ls_mul (ls_of_pol p) s.

(* 1+1/3^s+1/5^s+1/7^s+... = (1-1/2^s)ζ(s) *)
(* 1+1/3^s+1/5^s+1/7^s+... = zeta_but_mul_of 2
   (1-1/2^s) = {| lp := [f_one; (- f_one)%F] |}
   ζ(s) = zeta *)

Theorem Nat_succ_mod : ∀ n, 2 ≤ n → S n mod n = 1.
Proof.
intros * Hn.
replace (S n) with (1 + 1 * n) by flia.
rewrite Nat.mod_add; [ | flia Hn ].
specialize (Nat.div_mod 1 n) as H1.
assert (H : n ≠ 0) by flia Hn.
specialize (H1 H); clear H.
rewrite Nat.div_small in H1; [ | flia Hn ].
now rewrite Nat.mul_0_r in H1.
Qed.

Theorem log_prod_succ {F : field} : ∀ u v n i,
  log_prod u v n (S i) =
    (match S n mod S i with
     | 0 => u i * v (S n / S i - 1)%nat
     | S _ => f_zero
     end + log_prod u v n i)%F.
Proof. easy. Qed.

Theorem step_1 {F : field} :
  ls_eq (zeta_but_mul_of 2)
    (ls_pol_mul_l {| lp := [f_one; (- f_one)%F] |} zeta).
Proof.
intros n.
unfold ls_pol_mul_l.
remember (ls_of_pol {| lp := [f_one; (- f_one)%F] |}) as p eqn:Hp.
remember zeta as ζ eqn:Hζ.
Opaque Nat.modulo. Opaque Nat.div. cbn.
Transparent Nat.modulo.
subst ζ.
rewrite Nat.div_same; [ | easy ].
rewrite Nat.sub_diag.
replace (ls zeta 0) with f_one by easy.
rewrite f_mul_1_r.
rewrite Nat.mod_same; [ | easy ].
remember (S n mod 2) as b eqn:Hb; symmetry in Hb.
symmetry.
destruct b. {
  apply Nat.mod_divide in Hb; [ | easy ].
  destruct Hb as (m, Hm).
  destruct n; [ flia Hm | ].
  destruct m; [ easy | ].
  cbn in Hm.
  do 2 apply Nat.succ_inj in Hm.
  subst n.
  induction m. {
    subst p; cbn.
    rewrite f_mul_1_r, f_add_0_r.
    apply f_add_opp_diag_l.
  }
  replace (ls p (S (S m * 2))) with f_zero by now subst p.
  rewrite f_add_0_l.
  destruct m. {
    subst p; cbn.
    do 2 rewrite f_mul_1_r.
    rewrite f_add_0_l, f_add_0_r.
    apply f_add_opp_diag_l.
  }
  replace (ls p (S (S m * 2))) with f_zero in IHm by now rewrite Hp.
  rewrite f_add_0_l in IHm.
  replace (S (S m * 2)) with (2 * m + 3) in IHm by flia.
(**)
  replace (S (S (S m) * 2)) with (2 * m + 5) by flia.
...
  rewrite log_prod_succ.
  replace (S (S (S m) * 2)) with (2 * m + 5) by flia.
  rewrite Nat_succ_mod; [ | flia ].
  rewrite f_add_0_l.
  replace (S (S m) * 2) with (S (2 * m + 3)) by flia.
  rewrite log_prod_succ.
  replace (S (2 * m + 5)) with (2 * m + 6) by flia.
  replace (S (2 * m + 3)) with (2 * m + 4) by flia.
  replace ((2 * m + 6) mod (2 * m + 4)) with 2. 2: {
    clear; symmetry.
...
  }
  rewrite f_add_0_l.
...

Theorem zeta_Euler_product_eq : ∀ s, expr_eq (zeta s) (zeta' s).
Proof.
...
