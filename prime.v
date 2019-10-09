(* playing with prime numbers, as a break *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz List.
Import List.ListNotations.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level).

Theorem Nat_sub_succ_1 : ∀ n, S n - 1 = n.
Proof. now intros; rewrite Nat.sub_succ, Nat.sub_0_r. Qed.

Theorem Nat_sub_succ_diag_l : ∀ n, S n - n = 1.
Proof.
intros; induction n; [ easy | now rewrite Nat.sub_succ ].
Qed.

Theorem fold_mod_succ : ∀ n d, d - snd (Nat.divmod n d 0 d) = n mod (S d).
Proof. easy. Qed.

(* *)

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

Theorem fold_f_sub {F : field} : ∀ x y, (x + - y = x - y)%F.
Proof. easy. Qed.

Theorem f_add_0_l {F : field} : ∀ x, (f_zero + x)%F = x.
Proof.
intros.
rewrite f_add_comm.
apply f_add_0_r.
Qed.

Theorem f_opp_0 {F : field} : (- f_zero)%F = f_zero.
Proof.
rewrite <- (f_add_0_r (- f_zero)%F).
apply f_add_opp_diag_l.
Qed.

Theorem f_add_opp_diag_r {F : field} : ∀ x, f_add x (f_opp x) = f_zero.
Proof.
intros.
rewrite f_add_comm.
apply f_add_opp_diag_l.
Qed.

Theorem f_sub_diag {F : field} : ∀ x, (x - x = f_zero)%F.
Proof. apply f_add_opp_diag_r. Qed.

Theorem f_sub_0_l {F : field} : ∀ x, (f_zero - x = -x)%F.
Proof. intros; unfold f_sub; apply f_add_0_l. Qed.

Theorem f_sub_0_r {F : field} : ∀ x, (x - f_zero = x)%F.
Proof. intros; unfold f_sub; rewrite f_opp_0; apply f_add_0_r. Qed.

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

Theorem f_mul_sub_distr_l {F : field} : ∀ x y z,
  (x * (y - z))%F = (x * y - x * z)%F.
Proof.
intros.
unfold f_sub; rewrite f_mul_add_distr_l.
now rewrite f_mul_opp_r.
Qed.

Theorem f_mul_sub_distr_r {F : field} : ∀ x y z,
  ((x - y) * z)%F = (x * z - y * z)%F.
Proof.
intros.
rewrite f_mul_comm, f_mul_sub_distr_l.
now do 2 rewrite (f_mul_comm z).
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

Theorem f_sub_add_distr {F : field} : ∀ x y z,
  (x - (y + z) = x - y - z)%F.
Proof.
intros.
unfold f_sub.
rewrite f_opp_add_distr.
apply f_add_assoc.
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

(* Euler product formula *)

(* https://en.wikipedia.org/wiki/Proof_of_the_Euler_product_formula_for_the_Riemann_zeta_function *)

(* representation of ζ function as series in x where x=1/e^s; we have
     Σ 1/n^s = Σ x^ln(n)
 *)

(* {| ls := u |} represents Σ (n=1,∞) u(n)/n^s = Σ (n=1,∞) u(n)x^ln(n) =
   Σ (n=1,∞) u(n)(x⊗n) where a⊗b=a^ln(b)=b^ln(a)=e^(ln(a)ln(b)) *)

Class ln_series {F : field} :=
  { ls : nat → f_type }.

Class ln_polyn {F : field} :=
  { lp : list f_type }.

Declare Scope ls_scope.
Delimit Scope ls_scope with LS.

Declare Scope lp_scope.
Delimit Scope lp_scope with LP.

Arguments ls {_} _%LS _%nat.
Arguments lp {_}.

Definition ls_eq {F : field} s1 s2 := ∀ n, ls s1 (n + 1) = ls s2 (n + 1).
Arguments ls_eq _ s1%LS s2%LS.

Definition List_combine_all {A} (l1 l2 : list A) (d : A) :=
  let '(l'1, l'2) :=
    match List.length l1 ?= List.length l2 with
    | Eq => (l1, l2)
    | Lt => (l1 ++ List.repeat d (List.length l2 - List.length l1), l2)
    | Gt => (l1, l2 ++ List.repeat d (List.length l1 - List.length l2))
    end
  in
  List.combine l'1 l'2.

Definition lp_add {F : field} p q :=
  {| lp :=
       List.map (prod_curry f_add) (List_combine_all (lp p) (lp q) f_zero) |}.
Definition lp_opp {F : field} p := {| lp := List.map f_opp (lp p) |}.
Definition lp_sub {F : field} p q := lp_add p (lp_opp q).

Notation "- x" := (lp_opp x) : lp_scope.
Notation "x + y" := (lp_add x y) : lp_scope.
Notation "x - y" := (lp_sub x y) : lp_scope.

Definition ζ {F : field} := {| ls _ := f_one |}.

Definition series_but_mul_of {F : field} s n :=
  {| ls i :=
       match i mod n with
       | 0 => f_zero
       | _ => ls s i
       end |}.

Definition ζ_but_mul_of {F : field} n :=
  {| ls i :=
       match i mod n with
       | 0 => f_zero
       | _ => f_one
       end |}.

Definition ε {F: field} i n :=
  match i mod n with
  | 0 => f_one
  | _ => f_zero
  end.

Definition log_prod_term {F : field} u v n i :=
  (u i * v (n / i)%nat * ε n i)%F.

Fixpoint log_prod_list {F : field} cnt u v n i :=
  match cnt with
  | 0 => []
  | S cnt' => log_prod_term u v n i :: log_prod_list cnt' u v n (i + 1)
  end.

Definition log_prod {F : field} u v n :=
  List.fold_right f_add f_zero (log_prod_list n u v n 1).

(* Σ (i = 1, ∞) s1_i x^ln(i) + Σ (i = 1, ∞) s2_i x^ln(i) *)
Definition ls_add {F : field} s1 s2 :=
  {| ls n := (ls s1 n + ls s2 n)%F |}.

(* Σ (i = 1, ∞) s1_i x^ln(i) * Σ (i = 1, ∞) s2_i x^ln(i) *)
Definition ls_mul {F : field} s1 s2 :=
  {| ls := log_prod (ls s1) (ls s2) |}.

Definition ls_of_pol {F : field} p :=
  {| ls n :=
       match n with
       | 0 => f_zero
       | S n' => List.nth n' (lp p) f_zero end |}.

(* Σ (i = 1, k), p_(i-1) x^ln(i) * Σ (i = 1, ∞) s_(i-1) x^ln(i) *)
Definition ls_pol_mul_l {F : field} p s :=
  ls_mul (ls_of_pol p) s.

Definition ls_opp {F : field} s := {| ls n := (- ls s n)%F |}.
Definition ls_sub {F : field} s1 s2 := ls_add s1 (ls_opp s2).

Arguments ls_of_pol _ p%LP.
Arguments ls_pol_mul_l _ p%LP s%LS.

(* 1+1/3^s+1/5^s+1/7^s+... = (1-1/2^s)ζ(s) *)
(* 1+1/3^s+1/5^s+1/7^s+... = ζ_but_mul_of 2
   (1-1/2^s) = {| lp := [f_one; (- f_one)%F] |} *)

Notation "x = y" := (ls_eq x y) : ls_scope.
Notation "x + y" := (ls_add x y) : ls_scope.
Notation "x * y" := (ls_mul x y) : ls_scope.
Notation "x - y" := (ls_sub x y) : ls_scope.
Notation "- x" := (ls_opp x) : ls_scope.
Notation "p .* s" := (ls_pol_mul_l p s) (at level 40) : ls_scope.

Theorem fold_ls_sub {F : field} : ∀ x y, (x + - y = x - y)%LS.
Proof. easy. Qed.

Theorem ls_of_opp {F : field} : ∀ x n, ls (- x) n = (- ls x n)%F.
Proof. easy. Qed.

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

...

Theorem log_prod_list_length {F : field} : ∀ u v n i,
  length (log_prod_list u v n i) = i.
Proof.
intros.
revert n.
induction i; intros; [ easy | now cbn; rewrite IHi ].
Qed.

Theorem log_prod_list_succ {F : field} : ∀ u v n i,
  log_prod_list u v n (S i) =
    log_prod_term u v n (n - i) :: log_prod_list u v n i.
Proof. easy. Qed.

Theorem log_prod_succ {F : field} : ∀ u v n i,
  log_prod u v n (S i) =
    (log_prod_term u v n (n - i) + log_prod u v n i)%F.
Proof. easy. Qed.

Theorem log_prod_0_l {F : field} : ∀ u v n i,
  (∀ n, u n = f_zero) → log_prod u v n i = f_zero.
Proof.
intros * Hu.
revert n.
induction i; intros; [ easy | ].
rewrite log_prod_succ.
cbn - [ Nat.div Nat.modulo ].
rewrite IHi, f_add_0_r.
unfold log_prod_term, ε.
remember (n mod (n - i)) as r eqn:Hr; symmetry in Hr.
destruct r; [ | now rewrite f_mul_0_r ].
now rewrite Hu, f_mul_0_l, f_mul_1_r.
Qed.

Theorem ls_mul_0_l {F : field} : ∀ s1 s2,
  (∀ n, ls s1 n = f_zero) → ls_eq (ls_mul s1 s2) {| ls _ := f_zero |}.
Proof.
intros * Hs1 i.
cbn - [ "/" "mod" ].
unfold log_prod_term, ε.
now apply log_prod_0_l.
Qed.

Theorem ls_ls_add {F : field} : ∀ s1 s2 i,
  ls (ls_add s1 s2) i = (ls s1 i + ls s2 i)%F.
Proof. easy. Qed.

Theorem ζ_is_one {F : field} : ∀ n, ls ζ n = f_one.
Proof.
intros; now unfold ζ.
Qed.

Definition pol_pow {F : field} n :=
  {| lp := List.repeat f_zero (n - 1) ++ [f_one] |}.

Theorem ls_of_pol_add {F : field} : ∀ x y,
  (ls_of_pol (x + y) = ls_of_pol x + ls_of_pol y)%LS.
Proof.
intros * i.
unfold ls_of_pol, "+"%LS; cbn.
rewrite Nat.add_1_r.
remember (lp x) as lx eqn:Hlx.
remember (lp y) as ly eqn:Hly.
clear x y Hlx Hly.
unfold List_combine_all.
remember (length lx ?= length ly) as c eqn:Hc; symmetry in Hc.
destruct c.
-apply Nat.compare_eq in Hc.
 revert i ly Hc.
 induction lx as [| x lx]; intros. {
   destruct ly as [| y ly]; [ cbn | easy ].
   now destruct i; rewrite f_add_0_r.
 }
 destruct ly as [| y ly]; [ easy | cbn ].
 destruct i; [ easy | ].
 cbn in Hc; apply Nat.succ_inj in Hc; clear x y.
 now apply IHlx.
-apply Nat.compare_lt_iff in Hc.
 revert i ly Hc.
 induction lx as [| x lx]; intros. {
   cbn in Hc |-*; rewrite Nat.sub_0_r.
   replace (match i with 0 | _ => f_zero end) with f_zero by now destruct i.
   rewrite f_add_0_l.
   clear Hc; revert i.
   induction ly as [| y ly]; intros; [ easy | cbn ].
   destruct i; [ now rewrite f_add_0_l | ].
   apply IHly.
 }
 destruct ly as [| y ly]; [ cbn in Hc; flia Hc | cbn ].
 destruct i; [ easy | ].
 cbn in Hc.
 apply Nat.succ_lt_mono in Hc.
 now apply IHlx.
-apply Nat.compare_gt_iff in Hc.
 revert i lx Hc.
 induction ly as [| y ly]; intros. {
   cbn in Hc |-*; rewrite Nat.sub_0_r.
   replace (match i with 0 | _ => f_zero end) with f_zero by now destruct i.
   rewrite f_add_0_r.
   clear Hc; revert i.
   induction lx as [| x lx]; intros; [ easy | cbn ].
   destruct i; [ now rewrite f_add_0_r | ].
   apply IHlx.
 }
 destruct lx as [| x lx]; [ cbn in Hc; flia Hc | cbn ].
 destruct i; [ easy | ].
 cbn in Hc.
 apply Nat.succ_lt_mono in Hc.
 now apply IHly.
Qed.

Theorem log_prod_pol_add {F : field} : ∀ x y s n i,
  i ≤ n
  → log_prod (ls (ls_of_pol (x + y))) (ls s) n i =
       (log_prod (ls (ls_of_pol y)) (ls s) n i +
        log_prod (ls (ls_of_pol x)) (ls s) n i)%F.
Proof.
intros * Hin.
revert n Hin.
induction i; intros; [ now cbn; rewrite f_add_0_l | ].
rewrite log_prod_succ.
unfold log_prod_term.
specialize (ls_of_pol_add x y (n - i - 1)) as H1.
rewrite Nat.sub_add in H1; [ | flia Hin ].
rewrite H1, ls_ls_add.
rewrite IHi; [ | flia Hin ].
do 2 rewrite log_prod_succ.
do 2 rewrite f_add_assoc; f_equal.
rewrite (f_add_comm (_ + _)%F), f_add_assoc; f_equal.
unfold log_prod_term.
now do 2 rewrite f_mul_add_distr_r.
Qed.

Theorem ls_mul_pol_add_distr_r {F : field} : ∀ x y s,
  ((x + y) .* s = x .* s + y .* s)%LS.
Proof.
intros * i.
rewrite Nat.add_1_r.
cbn - [ "/" "mod" ls_of_pol "-" ].
rewrite Nat_sub_succ_diag_l.
unfold log_prod_term.
replace (ε (S i) 1) with f_one by easy.
do 3 rewrite f_mul_1_r.
rewrite Nat.div_1_r.
specialize (ls_of_pol_add x y 0) as H1.
rewrite Nat.add_0_l in H1; rewrite H1; clear H1.
rewrite ls_ls_add, f_mul_add_distr_r.
do 2 rewrite <- f_add_assoc; f_equal.
rewrite (f_add_comm (fold_right _ _ _)).
rewrite <- f_add_assoc; f_equal.
apply log_prod_pol_add; flia.
Qed.

Theorem log_prod_pol_1_l_trunc {F : field} : ∀ s n i,
  i < n
  → log_prod (ls (ls_of_pol (pol_pow 1))) (ls s) n i = f_zero.
Proof.
intros * Hin.
revert n Hin.
induction i; intros; [ easy | ].
rewrite log_prod_succ.
unfold ls_of_pol at 1.
unfold log_prod_term.
cbn - [ "/" ls_of_pol ].
remember (n - i) as m eqn:Hm.
destruct m; [ flia Hin Hm | ].
destruct m; [ flia Hin Hm | ].
replace (match _ with 0 | _ => f_zero end) with f_zero by now destruct m.
do 2 rewrite f_mul_0_l.
rewrite f_add_0_l.
apply IHi; flia Hin.
Qed.

(*
Theorem log_prod_pol_pow {F : field} : ∀ s n i k,
  0 < k
  → i + k < n + 2
  → log_prod (ls (ls_of_pol (pol_pow k))) (ls s) n i = f_zero.
Proof.
intros * Hk Hin.
revert n Hin.
induction i; intros; [ easy | ].
rewrite log_prod_succ.
unfold log_prod_term.
rewrite IHi; [ | flia Hin ].
rewrite f_add_0_r.
cbn - [ "/" "mod" ].
replace (nth _ _ _) with f_zero. 2: {
  assert (Hkn : k - 1 < n - i) by flia Hk Hin.
  clear - Hkn.
  remember (k - 1) as t.
  remember (n - i) as u.
  clear k n Heqt Hequ.
  revert t Hkn.
  induction u; intros. {
    destruct t; [ easy | now destruct t ].
  }
  destruct t; [ now destruct u | ].
  apply IHu; flia Hkn.
}
rewrite <- f_mul_assoc.
apply f_mul_0_l.
Qed.
*)

Theorem ls_mul_pol_1_l {F : field} : ∀ s,
  (pol_pow 1 .* s = s)%LS.
Proof.
intros * i.
cbn - [ "/" "mod" ls_of_pol ].
rewrite Nat.add_1_r.
rewrite log_prod_succ.
unfold log_prod_term.
rewrite Nat_sub_succ_diag_l, Nat.div_1_r.
unfold ls_of_pol at 1.
cbn - [ ls_of_pol "/" ].
rewrite f_mul_1_l, f_mul_1_r, <- f_add_0_r; f_equal.
apply log_prod_pol_1_l_trunc; flia.
Qed.

Theorem ls_of_pol_opp {F : field} : ∀ p,
  (ls_of_pol (- p) = - ls_of_pol p)%LS.
Proof.
intros * i; cbn.
rewrite Nat.add_1_r.
revert i.
induction (lp p) as [| c cl]; intros. {
  now cbn; destruct i; rewrite f_opp_0.
}
cbn.
destruct i; [ easy | ].
apply IHcl.
Qed.

Theorem log_prod_pol_opp_l {F : field} : ∀ p s n i,
  log_prod (ls (ls_of_pol (- p))) (ls s) n i =
  (- log_prod (ls (ls_of_pol p)) (ls s) n i)%F.
Proof.
intros.
induction i; [ now cbn; rewrite f_opp_0 | ].
do 2 rewrite log_prod_succ.
unfold log_prod_term.
rewrite IHi, f_opp_add_distr; f_equal.
rewrite <- f_mul_opp_l; f_equal.
rewrite <- f_mul_opp_l; f_equal.
destruct (Nat.eq_dec n i) as [Hni| Hni]. {
  subst n; rewrite Nat.sub_diag; cbn.
  symmetry; apply f_opp_0.
}
destruct (lt_dec n i) as [Hnlti| Hngei]. {
  replace (n - i) with 0 by flia Hnlti.
  symmetry; apply f_opp_0.
}
remember (n - i) as m eqn:Hm; symmetry in Hm.
destruct m; [ flia Hni Hngei Hm | ].
specialize (ls_of_pol_opp p m) as H1.
now rewrite Nat.add_1_r in H1.
Qed.

(*
Theorem log_prod_term_0 {F : field} : ∀ u v n,
  log_prod_term u v n 0 = (u 0 * v n)%F.
Proof.
intros.
unfold log_prod_term, ε.
cbn - [ "/" ].
...
now rewrite Nat.div_1_r, Nat_sub_succ_1, f_mul_1_r.
Qed.
*)

Theorem ls_mul_pol_opp_l {F : field} : ∀ p s,
  (- p .* s = - (p .* s))%LS.
Proof.
intros * i.
cbn - [ "/" "mod" ls_of_pol ].
apply log_prod_pol_opp_l.
Qed.

(*
Theorem pol_pow_1_mul_l {F : field} : ∀ s n i,
  i ≤ n
  → log_prod (ls (ls_of_pol (pol_pow 1))) (ls s) n i = f_zero.
Proof.
intros * Hin.
Search log_prod.
Check log_prod_pol_1_l_trunc.
revert n Hin.
induction i; intros; [ easy | ].
rewrite log_prod_succ.
unfold log_prod_term.
replace (ls (ls_of_pol (pol_pow 1)) (n - i)) with f_zero. 2: {
  cbn.
  remember (n - i) as m eqn:Hm.
  destruct m; [ | now destruct m ].
  flia Hin Hm.
}
rewrite f_mul_0_l, f_mul_0_l, f_add_0_l.
apply IHi; flia Hin.
Qed.
*)

(*
Theorem log_prod_pow_ge_2 {F : field} : ∀ s i k,
  0 < i
  → log_prod (ls (ls_of_pol (pol_pow (k + 2)))) (ls s) (i + k) i =
      (ls s ((i + k) / (k + 1)) * ε (i + k) (k + 1))%F.
Proof.
intros * Hi.
destruct i; [ flia Hi | clear Hi ].
rewrite log_prod_succ.
replace (S i + k - i) with (k + 1) by flia.
unfold log_prod_term.
replace (ls _ (k + 1)) with f_one. 2: {
  setoid_rewrite Nat.add_comm; cbn.
...
  induction k; [ easy | apply IHk ].
}
rewrite <- f_mul_assoc, f_mul_1_l.
replace (S (S i + k)) with (S i + k + 1) by flia.
replace (S (k + 1)) with (k + 2) by flia.
rewrite <- f_add_0_r; f_equal.
apply log_prod_pol_pow; flia.
...

intros * Hi.
destruct i. {
  cbn; unfold ε.
  rewrite Nat.mod_small; [ | flia ].
  now rewrite f_mul_0_r.
}
rewrite log_prod_succ.
replace (S i + k - i) with (k + 1) by flia.
unfold log_prod_term.
replace (ls _ (k + 1)) with f_one. 2: {
  setoid_rewrite Nat.add_comm; cbn.
  induction k; [ easy | apply IHk ].
}
rewrite <- f_mul_assoc, f_mul_1_l.
replace (S (S i + k)) with (S i + k + 1) by flia.
replace (S (k + 1)) with (k + 2) by flia.
rewrite <- f_add_0_r; f_equal.
apply log_prod_pol_pow; flia.
Qed.
*)

(*
Theorem pol_pow_mul {F : field} : ∀ s n i,
  ls (pol_pow (S n) .* s) i = (ls s (i / n) * ε i n)%F.
Proof.
intros.
revert n.
induction i; intros. {
  destruct n. {
    unfold ".*", "*"%LS.
    cbn - [ "/" "mod" ls_of_pol ].
    unfold log_prod_term.
    replace (1 / 1 - 1) with 0 by easy.
    unfold ε; replace (1 mod 1) with 0 by easy.
    rewrite f_add_0_r, f_mul_1_r, f_mul_1_r.
    now cbn; rewrite f_mul_1_l.
  }
  unfold ".*", "*"%LS.
  cbn - [ "/" "mod" ls_of_pol ].
  unfold log_prod_term; cbn.
  unfold ε.
  rewrite Nat.mod_1_l; [ | flia ].
  do 2 rewrite f_mul_0_l.
  now rewrite f_mul_0_r, f_add_0_l.
}
...
intros.
unfold ".*", "*"%LS.
cbn - [ "/" "mod" ls_of_pol ].
rewrite Nat.sub_diag.
unfold log_prod_term.
rewrite Nat.div_1_r, Nat_sub_succ_1.
destruct n. {
  rewrite Nat.div_1_r, Nat_sub_succ_1.
  replace (ls _ 0) with f_one by easy.
  rewrite f_mul_1_l, <- f_add_0_r; f_equal.
  now apply pol_pow_1_mul_l.
}
replace (ls _ 0) with f_zero by easy.
rewrite <- f_mul_assoc, f_mul_0_l, f_add_0_l.
destruct n; intros. {
  specialize (log_prod_pow_ge_2 s i 0) as H1.
  rewrite Nat.add_0_r in H1.
  replace (i + 1) with (S i) in H1 by flia.
  now do 2 replace (i + 1) with (S i) in H1 by flia.
}
destruct n. {
  destruct i; [ now cbn; rewrite f_mul_0_r | ].
  rewrite log_prod_succ.
  unfold log_prod_term.
  rewrite Nat_sub_succ_diag_l.
  replace (ls _ 1) with f_zero by easy.
  rewrite <- f_mul_assoc, f_mul_0_l, f_add_0_l.
  specialize (log_prod_pow_ge_2 s i 1) as H1.
  replace (i + 1 + 1) with (S (S i)) in H1 by flia.
  now do 2 replace (i + 1) with (S i) in H1 by flia.
}
destruct n. {
  destruct i; [ now cbn; rewrite f_mul_0_r | ].
  rewrite log_prod_succ.
  unfold log_prod_term.
  rewrite Nat_sub_succ_diag_l.
  replace (ls _ 1) with f_zero by easy.
  rewrite <- f_mul_assoc, f_mul_0_l, f_add_0_l.
  destruct i; [ now cbn; rewrite f_mul_0_r | ].
  rewrite log_prod_succ.
  replace (S (S i) - i) with 2 by flia.
  unfold log_prod_term.
  replace (ls _ 2) with f_zero by easy.
  rewrite <- f_mul_assoc, f_mul_0_l.
  rewrite f_add_0_l.
  specialize (log_prod_pow_ge_2 s i 2) as H1.
  replace (i + 2 + 1) with (S (S (S i))) in H1 by flia.
  now do 2 replace (i + 2) with (S (S i)) in H1 by flia.
}
destruct n. {
  destruct i; [ now cbn; rewrite f_mul_0_r | ].
  rewrite log_prod_succ.
  unfold log_prod_term.
  rewrite Nat_sub_succ_diag_l.
  replace (ls _ 1) with f_zero by easy.
  rewrite <- f_mul_assoc, f_mul_0_l, f_add_0_l.
  destruct i; [ now cbn; rewrite f_mul_0_r | ].
  rewrite log_prod_succ.
  replace (S (S i) - i) with 2 by flia.
  unfold log_prod_term.
  replace (ls _ 2) with f_zero by easy.
  rewrite <- f_mul_assoc, f_mul_0_l.
  rewrite f_add_0_l.
  destruct i; [ now cbn; rewrite f_mul_0_r | ].
  rewrite log_prod_succ.
  replace (S (S (S i)) - i) with 3 by flia.
  unfold log_prod_term.
  replace (ls _ 3) with f_zero by easy.
  rewrite <- f_mul_assoc, f_mul_0_l.
  rewrite f_add_0_l.
  specialize (log_prod_pow_ge_2 s i 3) as H1.
  replace (i + 3 + 1) with (S (S (S (S i)))) in H1 by flia.
  now do 2 replace (i + 3) with (S (S (S i))) in H1 by flia.
}
...
*)

(*
Theorem pol_pow_mul {F : field} : ∀ s i n,
  n ≠ 0
  → ls (pol_pow n .* s) i =
       match S i mod n with
       | 0 => ls s (S i / n - 1)
       | _ => f_zero
       end.
Proof.
intros * Hn.
remember (S i mod n) as m eqn:Hm; symmetry in Hm.
Print ε.
destruct m. {
  unfold ".*", "*"%LS.
  cbn - [ log_prod ls_of_pol pol_pow "/" ].
  rewrite log_prod_succ, Nat.sub_diag.
  unfold log_prod_term.
  rewrite Nat.div_1_r, Nat_sub_succ_1.
...
  rewrite Nat.mod_1_r, Nat.div_1_r, Nat_sub_succ_1.
(**)
destruct i. {
  destruct n; [ flia Hn | ].
  destruct n. {
    now cbn; rewrite f_mul_1_l, <- f_add_0_r.
  }
  rewrite Nat.mod_1_l in Hm; [ easy | flia ].
}
rewrite log_prod_succ, f_add_assoc.
rewrite Nat_sub_succ_diag_l.
unfold log_prod_term.
replace (S (S i)) with (i + 1 * 2) by flia.
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.div_add; [ | easy ].
rewrite Nat.add_sub.
rewrite Nat.mul_1_l.
remember (i mod 2) as m2 eqn:Hm2; symmetry in Hm2.
move m2 before n.
destruct m2. {
  destruct i. {
    clear Hm2.
    destruct n; [ flia Hn | clear Hn ].
    destruct n. {
      now cbn; rewrite f_mul_1_l, f_mul_0_l, f_add_0_r, f_add_0_r.
    }
    destruct n. {
      now cbn; rewrite f_mul_1_l, f_mul_0_l, f_add_0_l, f_add_0_r.
    }
    rewrite Nat.mod_small in Hm; [ easy | flia ].
  }
  rewrite log_prod_succ, f_add_assoc.
  unfold log_prod_term.
  replace (S (S (S i) - i)) with 3 by flia.
  replace (S (S i) - i) with 2 by flia.
  replace (S (S (S i))) with (i + 1 * 3) by flia.
  rewrite Nat.mod_add; [ | easy ].
  rewrite Nat.div_add; [ | easy ].
  rewrite Nat.add_sub.
  remember (i mod 3) as m3 eqn:Hm3; symmetry in Hm3.
  move m3 before n.
  replace (S (S i)) with (i + 2) by flia.
  replace (S i + 2) with (i + 3) by flia.
  destruct m3. {
    destruct i; [ easy | ].
    rewrite log_prod_succ, f_add_assoc.
    replace (S (S i)) with (i + 1 * 2) in Hm2 |-* by flia.
    rewrite Nat.mod_add in Hm2; [ | easy ].
    rewrite Nat.div_add; [ | easy ].
    replace (S i + 2 - i) with 3 by flia.
    replace (S i + 2) with (i + 3) by flia.
    replace (S i + 3) with (i + 4) by flia.
    replace (S i) with (i + 1) by flia.
    ring_simplify in Hm; rewrite Nat.add_comm in Hm.
    ring_simplify in Hm3; rewrite Nat.add_comm in Hm3.
    unfold log_prod_term.
    replace (S (i + 3)) with (i + 1 * 4) by flia.
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.add_sub.
    remember (i mod 4) as m4 eqn:Hm4; symmetry in Hm4.
    move m4 before n.
    destruct m4. {
      destruct i; [ easy | ].
      rewrite log_prod_succ, f_add_assoc.
      replace (S i + 3 - i) with 4 by flia.
      replace (S i + 3) with (i + 4) by flia.
      unfold log_prod_term.
      replace (S (i + 4)) with (i + 1 * 5) by flia.
      rewrite Nat.mod_add; [ | easy ].
      rewrite Nat.div_add; [ | easy ].
      rewrite Nat.add_sub.
      remember (i mod 5) as m5 eqn:Hm5; symmetry in Hm5.
      move m5 before n.
      replace (S i + 1) with (i + 2) by flia.
      replace (S i) with (i + 1) by flia.
      replace ((i + 1) / 2 + 1) with ((i + 3) / 2). 2: {
        replace (i + 3) with (i + 1 + 1 * 2) by flia.
        now rewrite Nat.div_add; [ | easy ].
      }
      destruct m5. {
Set Printing Width 70.
...
  destruct n; [ flia Hn | clear Hn ].
  destruct n. {
    replace (ls _ 0) with f_one by easy.
    rewrite Nat.div_1_r, Nat_sub_succ_1.
    rewrite f_mul_1_l, <- f_add_0_r; f_equal.
    clear Hm.
    now apply pol_pow_1_mul_l.
  }
  replace (ls _ 0) with f_zero by easy.
  rewrite f_mul_0_l, f_add_0_l.
(**)
  apply Nat.mod_divides in Hm; [ | easy ].
  destruct Hm as (m, Hm).
  rewrite <- Nat.add_1_r in Hm.
  replace (S i) with (m * S (S n)) by flia Hm.
  rewrite Nat.div_mul; [ | easy ].
  revert i m Hm.
  induction n; intros. {
    destruct i; [ flia Hm | ].
    rewrite log_prod_succ, Nat_sub_succ_diag_l.
    unfold log_prod_term.
    replace (S (S i)) with (m * 2) by flia Hm.
    rewrite Nat.mod_mul; [ | easy ].
    rewrite Nat.div_mul; [ | easy ].
    replace (ls _ 1) with f_one by easy.
    rewrite f_mul_1_l, <- f_add_0_r; f_equal.
    apply log_prod_pol_pow; flia.
  }
  replace (S (S (S n)) * m) with (S (S n) * m + m) in Hm by flia.
  remember (S (S n) * m) as j eqn:Hj.
  destruct j. {
    destruct m; [ flia Hm | cbn in Hj; flia Hj ].
  }
  rewrite <- Nat.add_1_r in Hj.
  specialize (IHn _ _ Hj) as H1.
  replace i with (j + m) by flia Hm.
  clear i Hm.
  replace (S (S (S n))) with (S (S n) + 1) by flia.
  replace (j + m) with ((S (S n) + 1) * m - 1) by flia Hj.
  replace j with (S (S n) * m - 1) in H1 by flia Hj.
  replace (S (S n) + 1) with (n + 3) by flia.
  replace (S (S n)) with (n + 2) in IHn, Hj, H1 by flia.
  replace ((n + 3) * m - 1) with ((n + 2) * m - 1 + m) by flia Hj.
  remember ((n + 2) * m - 1) as i eqn:Hi.
  rewrite log_prod_succ_r' in H1.
  rewrite log_prod_succ_r'.
  replace (ls (ls_of_pol (pol_pow (n + 2))) 0) with f_zero in H1 by
      now rewrite Nat.add_comm.
  replace (ls (ls_of_pol (pol_pow (n + 3))) 0) with f_zero by
      now rewrite Nat.add_comm.
  rewrite f_mul_0_l, f_sub_0_r in H1 |-*.
Print ls_mul.
...
Theorem glop {F : field} : ∀ n i s,
  log_prod (ls (ls_of_pol (pol_pow (n + 1)))) (ls s) ((n + 1) * i - 1) ((n + 1) * i - 1) =
  log_prod (ls (ls_of_pol (pol_pow n))) (ls s) (n * i - 1) (n * i - 1).
Proof.
intros.
destruct i. {
  now do 2 rewrite Nat.mul_0_r.
}
destruct i. {
  cbn.
  do 2 rewrite Nat.mul_1_r.
  rewrite Nat.add_sub.
  destruct n; [ easy | ].
  rewrite Nat_sub_succ_1.
  remember (repeat _ (S n) ++ _) as x eqn:Hx.
  cbn in Hx; subst x.
  rewrite log_prod_succ.
  rewrite Nat_sub_succ_diag_l.
  unfold log_prod_term.


  remember (S n) as sn eqn:Hsn.
  rewrite Hsn at 3.
  cbn - [ repeat log_prod ].
...
intros.
revert n.
induction i; intros. {
  now do 2 rewrite Nat.mul_0_r.
}
...
intros.
revert i.
induction n; intros. {
  cbn - [ ls_of_pol pol_pow ].
  apply log_prod_pol_1_l; [ flia | easy ].
}
specialize (IHn (i + 1)) as H1.
...
rewrite <- glop in H1.
easy.
...
Theorem glop {F : field} : ∀ n s i j,
  log_prod (ls (ls_of_pol (pol_pow (n + 1)))) (ls s) (i + k) (i + k) =
  log_prod (ls (ls_of_pol (pol_pow n))) (ls s) i i.
Proof.
...
  destruct n. {
    destruct i. {
      rewrite Nat.mod_1_l in Hm; [ easy | flia ].
    }
    rewrite log_prod_succ, Nat_sub_succ_diag_l.
    unfold log_prod_term.
    rewrite Hm.
    replace (ls _ 1) with f_one by easy.
    rewrite f_mul_1_l, <- f_add_0_r; f_equal.
    apply log_prod_pol_pow; flia.
  }
  destruct n. {
    destruct i; [ easy | ].
    rewrite log_prod_succ, Nat_sub_succ_diag_l.
    unfold log_prod_term.
    replace (ls _ 1) with f_zero by easy.
    rewrite f_mul_0_l.
    replace (match _ with 0 | _ => f_zero end) with f_zero
      by now destruct (S (S i) mod 2).
    rewrite f_add_0_l.
    destruct i; [ easy | ].
    rewrite log_prod_succ.
    unfold log_prod_term.
    replace (S (S i) - i) with 2 by flia.
    rewrite Hm.
    replace (ls _ 2) with f_one by easy.
    rewrite f_mul_1_l, <- f_add_0_r; f_equal.
    apply log_prod_pol_pow; flia.
  }
...
*)

(*
Theorem pol_pow_mul {F : field} : ∀ s i n k,
  2 ≤ k
  → ls (pol_pow (n + k) .* s) ((i + 1) * (n + k) - 1) = ls s i.
Proof.
intros * Hk.
destruct k; [ flia Hk | ].
destruct k; [ flia Hk | ].
clear Hk.
revert i k.
induction n; intros. {
  rewrite Nat.add_0_l.
...
  unfold ".*", "*"%LS.
  cbn - [ log_prod ls_of_pol pol_pow ].
  rewrite log_prod_succ.
  unfold log_prod_term.
  rewrite Nat.sub_diag, Nat.mod_1_r, Nat.div_1_r.
  replace ((i + 1) * S (S k) - 1) with (S (2 * i + k * (i + 1))) by flia.
  rewrite Nat_sub_succ_1.
  rewrite log_prod_succ, Nat_sub_succ_diag_l.
  unfold log_prod_term.
  replace (ls (ls_of_pol (pol_pow (S (S k)))) 0) with f_zero by easy.
  rewrite f_mul_0_l, f_add_0_l.
  replace (S (S (2 * i + k * (i + 1)))) with (k * (i + 1) + (i + 1) * 2) by flia.
  rewrite Nat.mod_add; [ | easy ].
  rewrite Nat.div_add; [ | easy ].
  rewrite Nat.add_assoc, Nat.add_sub.
  remember (k * (i + 1) mod 2) as m eqn:Hm; symmetry in Hm.
  destruct m. {
    apply Nat.mod_divides in Hm; [ | easy ].
    destruct Hm as (m, Hm).
    rewrite Hm, Nat.mul_comm, Nat.div_mul; [ | easy ].
    destruct k. {
      replace (ls (ls_of_pol (pol_pow 2)) 1) with f_one by easy.
      rewrite f_mul_1_l.
      cbn in Hm.
      replace m with 0 by flia Hm.
      rewrite Nat.mul_0_l, Nat.add_0_l, Nat.add_0_r.
      rewrite <- f_add_0_r; f_equal.
      rewrite log_prod_pol_pow; [ easy | flia | flia ].
    }
    replace (ls (ls_of_pol (pol_pow (S (S (S k))))) 1) with f_zero by easy.
    rewrite f_mul_0_l, f_add_0_l.
    replace (2 * i + m * 2) with (S (k * S i + 3 * i)) by flia Hm.
    remember (k * S i + 3 * i) as x.
    rewrite log_prod_succ.
    replace (S (S x) - x) with 2 by flia.
    unfold log_prod_term; subst x.
    replace (S (S (S (k * S i + 3 * i)))) with (k * (i + 1) + (i + 1) * 3)
      by flia.
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.add_assoc, Nat.add_sub.
    destruct k. {
      do 2 rewrite Nat.mul_0_l.
      do 2 rewrite Nat.add_0_l.
      rewrite Nat.mod_0_l; [ | easy ].
      replace (ls (ls_of_pol (pol_pow 3)) 2) with f_one by easy.
      rewrite f_mul_1_l.
      rewrite <- f_add_0_r; f_equal.
      rewrite log_prod_pol_pow; [ easy | flia | flia ].
    }
    replace (ls (ls_of_pol (pol_pow (S (S (S (S k)))))) 2) with f_zero
      by easy.
    rewrite f_mul_0_l.
    replace (match _ with 0 | _ => f_zero end) with f_zero. 2: {
      now destruct ((S k * (i + 1)) mod 3).
    }
    rewrite f_add_0_l.
    replace (S (S (S (S k)))) with (k + 4) by flia.
    replace (S k * S i + 3 * i) with (S (S k * i + k + 3 * i)) by flia.
    remember (S k * i + k + 3 * i) as x.
    rewrite log_prod_succ.
    replace (S (S (S x)) - x) with 3 by flia.
    unfold log_prod_term.
    replace (S (S (S (S x)))) with (k * (i + 1) + (i + 1) * 4) by flia Heqx.
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.add_assoc, Nat.add_sub.
    destruct k. {
      cbn - [ ls_of_pol ].
      replace (ls (ls_of_pol (pol_pow 4)) 3) with f_one by easy.
      rewrite f_mul_1_l.
      rewrite <- f_add_0_r; f_equal.
      rewrite log_prod_pol_pow; [ easy | flia | flia ].
    }
    replace (ls (ls_of_pol (pol_pow (S k + 4))) 3) with f_zero. 2: {
      now rewrite Nat.add_comm; cbn.
    }
    rewrite f_mul_0_l.
    replace (match _ with 0 | _ => f_zero end) with f_zero. 2: {
      now destruct ((S k * (i + 1)) mod 4).
    }
    rewrite f_add_0_l.
    rewrite Heqx at 2.
    replace (S (S k) * i + S k + 3 * i) with (S (S (S k) * i + k + 3 * i))
      by flia.
    rewrite log_prod_succ.
    replace (S (S (S x)) - (S (S k) * i + k + 3 * i)) with 4 by flia Heqx.
    replace (S k + 4) with (k + 5) by flia.
    unfold log_prod_term.
    ring_simplify in Heqx.
    replace (S (S (S (S x)))) with (k * (i + 1) + (i + 1) * 5) by flia Heqx.
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.add_assoc, Nat.add_sub.
    destruct k. {
      replace (ls (ls_of_pol (pol_pow (0 + 5))) 4) with f_one. 2: {
        now rewrite Nat.add_comm; cbn.
      }
      rewrite f_mul_1_l, Nat.mul_0_l.
      rewrite Nat.mod_0_l; [ | easy ].
      rewrite Nat.div_0_l; [ | easy ].
      do 2 rewrite Nat.add_0_l.
      rewrite Nat.add_0_r.
      rewrite <- f_add_0_r; f_equal.
      replace (2 * i + 3 * i) with (5 * i) by flia.
      ring_simplify in Heqx.
...
*)

(*
... fait chier, marche pas, faut re-réfléchir
Theorem nth_log_prod_list2 {F : field} : ∀ m n i k u l,
  l = log_prod_list (ls (ls_of_pol (pol_pow 1 - pol_pow n))) u
        (n * (m + 1)) k
  → k < n * (m + 1)
  → 0 < i < n * (m + 1) - 1
  → nth i l f_zero = f_zero.
Proof.
intros * Hl Hknm (Hi, Hin).
destruct i; [ flia Hi | clear Hi ].
revert m n i l Hl Hknm Hin.
induction k; intros; [ now rewrite Hl; destruct i | ].
rewrite log_prod_list_succ in Hl.
destruct l as [| a l]; [ easy | ].
remember ls_of_pol as f; remember (S n) as sn.
injection Hl; clear Hl; intros Hl Ha; subst f sn; cbn.
destruct i. 2: {
  destruct (Nat.eq_dec (n * m) k) as [H1| H1]. 2: {
    specialize (IHk m n i l Hl) as H2.
    assert (H : k < n * (m + 1)) by flia Hknm.
    specialize (H2 H); clear H.
    assert (H : S i < n * (m + 1) - 1) by flia Hin.
    now specialize (H2 H); clear H.
  }
  rewrite Hl.
  rewrite Nat.mul_add_distr_l, Nat.mul_1_r, H1.
  destruct k; [ easy | ].
  rewrite log_prod_list_succ.
  cbn - [ ls_of_pol ].
  clear.
  remember (S (k + n)) as j eqn:Hj.
  assert (Hnj : n + k < j) by flia Hj.
  clear Hj.
  revert n i j Hnj.
  induction k; intros; [ now cbn; destruct i | ].
  rewrite log_prod_list_succ.
  destruct i. {
    cbn - [ ls_of_pol ].
    unfold log_prod_term.
    replace (ls _ (j - k)) with f_zero. 2: {
      symmetry.
      unfold lp_sub.
      replace (j - k) with (j - k - 1 + 1) by flia Hnj.
      rewrite ls_of_pol_add, ls_ls_add, ls_of_pol_opp, ls_of_opp.
      replace (j - k - 1 + 1) with (j - k) by flia Hnj.
      destruct n; [ cbn; apply f_add_opp_diag_r | ].
      cbn.
      remember (j - k) as jk eqn:Hjk; symmetry in Hjk.
      destruct jk; [ apply f_add_opp_diag_r | ].
      destruct jk; [ flia Hnj Hjk | cbn ].
      replace (match _ with 0 | _ => f_zero end) with f_zero. 2: {
        now destruct jk.
      }
      rewrite f_add_0_l, Nat.sub_0_r.
      clear - Hnj Hjk.
      revert j k jk Hnj Hjk.
      induction n; intros; [ cbn; destruct jk; apply f_opp_0 | cbn ].
      destruct jk; [ flia Hnj Hjk | cbn ].
      replace (S (S n) + S k) with (S n + S (S k)) in Hnj by flia.
      eapply IHn; [ apply Hnj | cbn ].
      flia Hnj Hjk.
    }
    rewrite <- f_mul_assoc.
    apply f_mul_0_l.
  }
  cbn - [ ls_of_pol ].
  apply IHk.
  flia Hnj.
}
rewrite Hl.
destruct k; [ easy | ].
rewrite log_prod_list_succ.
cbn - [ ls_of_pol ].
unfold log_prod_term.
replace (ls _ (n * (m + 1) - k)) with f_zero. 2: {
  remember (n * (m + 1) - k) as p eqn:Hp; symmetry in Hp.
  destruct p; [ easy | cbn ].
  destruct n; [ flia Hp | ].
  rewrite Nat_sub_succ_1.
  destruct n. {
    cbn.
    rewrite f_add_opp_diag_r.
    destruct p; [ easy | now destruct p ].
  }
  cbn.
  destruct p; [ flia Hknm Hp | ].
  destruct n. {
    destruct p; [ | now destruct p ].
    flia Hknm Hp.
  }
  cbn.
  rewrite f_add_opp_diag_r.
  destruct p; [ easy | ].
  destruct (lt_dec (n + 4) p) as [Hnp| Hnp]. {
    clear - Hnp.
    revert p Hnp.
    induction n; intros. {
      destruct p; [ flia Hnp | now destruct p ].
    }
    destruct p; [ symmetry; apply f_add_opp_diag_r | cbn ].
    apply IHn; flia Hnp.
  }
  rewrite List.nth_overflow; [ easy | ].
  rewrite List.map_length.
  rewrite List.combine_length.
  rewrite List.repeat_length.
  rewrite List.map_length.
  rewrite List.app_length; cbn.
  rewrite List.repeat_length.
  rewrite Nat.min_idempotent.
  apply Nat.nlt_ge in Hnp.
ring_simplify in Hp.
rewrite Nat.mul_add_distr_l, Nat.mul_1_r in Hp.
rewrite Nat.mul_add_distr_r in Hp.
(* fichtre bougre diantre *)
...
now do 2 rewrite f_mul_0_l.
Qed.
*)

Theorem nth_log_prod_list {F : field} : ∀ n i k u l,
  l = log_prod_list (ls (ls_of_pol (pol_pow 1 - pol_pow n))) u n k
  → k < n
  → k = length l
  → i < k - 1
  → nth i l f_zero = f_zero.
Proof.
intros * Hl Hkn Hn Hik.
revert n i l Hl Hn Hkn Hik.
induction k; intros; [ now rewrite Hl; destruct i | ].
rewrite log_prod_list_succ in Hl.
destruct l as [| a l]; [ easy | ].
cbn in Hn; apply Nat.succ_inj in Hn.
remember ls_of_pol as f; remember (S n) as sn.
injection Hl; clear Hl; intros Hl Ha; subst f sn.
cbn in Hn; cbn.
destruct i. 2: {
  specialize (IHk _ i _ Hl Hn) as H1.
  assert (H : k < n) by flia Hkn.
  specialize (H1 H); clear H.
  assert (H : i < k - 1) by flia Hik.
  now specialize (H1 H); clear H.
}
rewrite Ha.
unfold log_prod_term.
replace (ls _ (n - k)) with f_zero. 2: {
  remember (n - k) as m eqn:Hm; symmetry in Hm.
  destruct m; [ easy | ].
  cbn.
  destruct n; [ flia Hkn | ].
  rewrite Nat_sub_succ_1.
  destruct n. {
    cbn.
    rewrite f_add_opp_diag_r.
    destruct m; [ easy | now destruct m ].
  }
  cbn.
  destruct m; [ flia Hm Hkn | ].
  destruct n; [ flia Hkn Hik | cbn ].
  rewrite f_add_opp_diag_r.
  destruct m; [ easy | ].
  assert (Hmn : m < n) by flia Hik Hm.
  clear - Hmn.
  revert m Hmn.
  induction n; intros; [ flia Hmn | ].
  destruct m; [ symmetry; apply f_add_opp_diag_r | cbn ].
  apply IHn; flia Hmn.
}
now do 2 rewrite f_mul_0_l.
Qed.

Theorem nth_log_prod_list_last {F : field} : ∀ k l n s,
  l = log_prod_list (ls (ls_of_pol (pol_pow 1 - pol_pow (n + k + 3)))) (ls s) (n + k + 3) (n + 1)
  → nth n l f_zero = (- ls s 1)%F.
Proof.
intros * Hl.
replace (n + 1) with (S n) in Hl by flia.
revert n k Hl.
induction l as [| a l]; intros; [ easy | cbn ].
rewrite log_prod_list_succ in Hl.
remember ls_of_pol as f; remember (S n) as sn; remember Nat.sub as m.
injection Hl; clear Hl; intros Hl Ha; subst f sn m.
destruct n. {
  rewrite Ha; cbn.
  rewrite Nat.sub_0_r.
  replace (k + 3 - 1) with (k + 2) by flia.
  unfold log_prod_term.
  replace (k + 3) with (S (k + 2)) by flia.
  replace (k + 2) with (S (S k)) by flia; cbn - [ "/" ].
  unfold ε.
  rewrite Nat.div_same; [ | easy ].
  rewrite Nat.mod_same; [ | easy ].
  rewrite f_mul_1_r.
  clear.
  induction k; [ now cbn; rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l | ].
  cbn; apply IHk.
}
apply (IHl _ (k + 1)).
now replace (n + (k + 1) + 3) with (S n + k + 3) by flia.
Qed.

Theorem mul_pol_1_sub_pow_ser_at_pow {F : field} : ∀ n s,
  1 < n
  → (∀ i : nat, 0 < i → ls s i = ls s (n * i))
  → ls ((pol_pow 1 - pol_pow n) .* s) n = f_zero.
Proof.
intros * Hn Hs.
unfold ".*", "*"%LS.
cbn - [ ls_of_pol ].
unfold log_prod.
(* log_prod_list ... =
       [1*s_n*ε; 0*s_{n-1}*ε; 0*s_{n-2}*ε; ... 0*s_2*ε; (-1)*s_1)*ε] *)
remember
  (log_prod_list (ls (ls_of_pol (pol_pow 1 - pol_pow n))) (ls s) n n)
  as l eqn:Hl.
assert (Hfirst : List.nth 0 l f_zero = ls s n). {
  subst l.
  destruct n; [ flia Hn | ].
  rewrite log_prod_list_succ.
  unfold nth.
  rewrite Nat_sub_succ_diag_l.
  unfold log_prod_term.
  rewrite Nat.div_1_r.
  replace (ε _ _) with f_one by easy.
  rewrite f_mul_1_r.
  destruct n; [ flia Hn | ].
  replace (ls _ 1) with f_one. 2: {
    now destruct n; cbn; rewrite f_opp_0, f_add_0_r.
  }
  apply f_mul_1_l.
}
assert (Hnl : n = length l). {
  subst l.
  symmetry; apply log_prod_list_length.
}
assert (Hbetw : ∀ i, 0 < i < n - 1 → List.nth i l f_zero = f_zero). {
  intros i (Hi, Hin).
  move i before n.
  destruct i; [ flia Hi | clear Hi ].
  destruct l as [| a l]; [ easy | cbn ].
  destruct n; [ easy | ].
  rewrite log_prod_list_succ in Hl.
  remember ls_of_pol as f; remember (S n) as sn.
  injection Hl; clear Hl; intros Hl Ha; subst f sn.
  cbn in Hnl.
  apply Nat.succ_inj in Hnl.
  rewrite Nat_sub_succ_1 in Hin.
  destruct n; [ flia Hin | clear Hn ].
  apply Nat.succ_lt_mono in Hin.
  eapply nth_log_prod_list; [ apply Hl | flia | easy | flia Hin ].
}
assert (Hlast : List.nth (n - 1) l f_zero = (- ls s 1)%F). {
  clear Hfirst Hs.
  destruct n; [ flia Hn | ].
  rewrite Nat_sub_succ_1.
  destruct n; [ flia Hn | ].
  clear Hn.
  destruct l as [| a l]; [ easy | cbn ].
  rewrite log_prod_list_succ in Hl.
  rewrite Nat_sub_succ_diag_l in Hl.
  remember ls_of_pol as f; remember (S n) as sn.
  injection Hl; clear Hl; intros Hl Ha; subst f sn.
  cbn in Hnl; apply Nat.succ_inj in Hnl.
  rewrite log_prod_list_succ in Hl.
  clear a Ha Hbetw.
  destruct l as [| a l]; [ easy | cbn ].
  remember ls_of_pol as f; remember (S n) as sn; remember Nat.sub as m.
  injection Hl; clear Hl; intros Hl Ha; subst f sn m.
  cbn in Hnl; apply Nat.succ_inj in Hnl.
  destruct n. {
    rewrite Ha; cbn.
    unfold log_prod_term.
    rewrite f_add_0_l, Nat.div_same; [ | easy ].
    unfold ε; cbn.
    now rewrite f_mul_1_r, f_mul_opp_l, f_mul_1_l.
  }
  apply (nth_log_prod_list_last 0).
  replace (n + 0 + 3) with (S (S (S n))) by flia.
  now replace (n + 1) with (S n) by flia.
}
destruct l as [| a l]; [ easy | ].
cbn in Hfirst, Hnl; cbn.
rewrite Hnl, Nat_sub_succ_1 in Hlast.
rewrite Hfirst.
remember (length l) as len eqn:Hlen; symmetry in Hlen.
destruct len; [ flia Hnl Hn | ].
specialize (@app_removelast_last _ l f_zero) as H1.
assert (H : l ≠ []). {
  now intros H; rewrite H in Hlen.
}
specialize (H1 H); clear H.
cbn in Hlast.
rewrite H1, List.fold_right_app; cbn.
rewrite f_add_0_r.
replace (last l f_zero) with (nth len l f_zero). 2: {
  clear - Hlen.
  revert l Hlen.
  induction len; intros. {
    destruct l as [| a1 l]; [ easy | ].
    cbn in Hlen; cbn.
    now destruct l.
  }
  destruct l as [| a1 l]; [ easy | ].
  cbn in Hlen.
  apply Nat.succ_inj in Hlen.
  specialize (IHlen _ Hlen) as H1.
  cbn; rewrite H1.
  now destruct l.
}
rewrite Hlast.
rewrite (Hs 1); [ | flia ].
rewrite Nat.mul_1_r.
destruct (Nat.eq_dec n 2) as [Hn2| Hn2]. {
  move Hn2 at top; subst n.
  clear Hn; do 2 apply Nat.succ_inj in Hnl; subst len.
  destruct l as [| a1 l]; [ easy | ].
  destruct l as [| a2 l]; [ | easy ].
  cbn; apply f_add_opp_diag_r.
}
assert (H : 2 < n) by flia Hn Hn2.
clear Hn; rename H into Hn.
rewrite <- Hlen in Hnl.
rewrite Hnl in Hn.
apply Nat.succ_lt_mono in Hn.
rewrite Hnl in Hbetw.
rewrite Nat_sub_succ_1 in Hbetw.
clear - Hn Hbetw.
revert a Hbetw.
induction l as [| a1 l]; intros. {
  cbn; apply f_add_opp_diag_r.
}
cbn.
destruct l as [ | a2 l]. {
  cbn; apply f_add_opp_diag_r.
}
cbn - [ removelast ].
replace a1 with f_zero. 2: {
  specialize (Hbetw 1) as H2.
  cbn in H2; rewrite H2; [ easy | flia ].
}
rewrite f_add_0_l.
destruct l as [| a3 l]. {
  cbn; apply f_add_opp_diag_r.
}
assert (H : 1 < length (a2 :: a3 :: l)) by (cbn; flia).
specialize (IHl H); clear H.
apply (IHl a1).
intros i Hi.
specialize (Hbetw (i + 1)) as H1.
assert (H : 0 < i + 1 ∧ i + 1 < length (a1 :: a2 :: a3 :: l)). {
  split; [ flia | cbn in Hi; cbn; flia Hi ].
}
specialize (H1 H); clear H.
replace (i + 1) with (S i) in H1 by flia.
remember (a1 :: a2 :: a3 :: l) as l'.
now cbn in H1.
Qed.

(* perhaps the previous theorem is no more required if this one works *)
Theorem mul_pol_1_sub_pow_ser_at_nth_pow {F : field} : ∀ n m s,
  1 < n
  → (∀ i : nat, 0 < i → ls s i = ls s (n * i))
  → ls ((pol_pow 1 - pol_pow n) .* s) (n * (m + 1)) = f_zero.
Proof.
intros * Hn Hs.
unfold ".*", "*"%LS.
cbn - [ ls_of_pol ].
unfold log_prod.
(* log_prod_list ... =
       [1*s[n*(m+1)]*ε; 0*s[n*(m+1)-1]*ε; ... ; 0*s[n*m+1]*ε;
        0*s[n*m]*ε; 0*s[n*m-1]*ε; ... ; 0*s[(n-1)*m+1]*ε;
        (-1)*s[m+1]*ε; 0*s[m]*e; 0*s[m-1]*ε; ... ; 0*s[1]*ε] *)
remember
  (log_prod_list (ls (ls_of_pol (pol_pow 1 - pol_pow n))) (ls s) (n * (m + 1))
     (n * (m + 1))) as l eqn:Hl.
assert (Hfirst : List.nth 0 l f_zero = ls s (n * (m + 1))). {
  subst l.
  destruct n; [ flia Hn | ].
  replace (S n * (m + 1)) with (S (n * (m + 1) + m)) by flia.
  rewrite log_prod_list_succ.
  unfold nth.
  rewrite Nat_sub_succ_diag_l.
  unfold log_prod_term.
  rewrite Nat.div_1_r.
  replace (ε _ _) with f_one by easy.
  rewrite f_mul_1_r.
  destruct n; [ flia Hn | ].
  replace (ls _ 1) with f_one. 2: {
    now destruct n; cbn; rewrite f_opp_0, f_add_0_r.
  }
  apply f_mul_1_l.
}
assert (Hnl : n * (m + 1) = length l). {
  subst l.
  symmetry; apply log_prod_list_length.
}
Print log_prod_list.
...
assert (Hbetw : ∀ i, 1 < i < n - 1 → List.nth i l f_zero = f_zero). {
  intros i (Hi, Hin).
  move i before n.
  destruct i; [ flia Hi | ].
  destruct l as [| a l]; [ easy | cbn ].
  destruct n; [ easy | ].
  replace (S n * (m + 1)) with (S (n * (m + 1) + m)) in Hl by flia.
  rewrite log_prod_list_succ in Hl.
  remember ls_of_pol as f; remember (S n) as sn.
  injection Hl; clear Hl; intros Hl Ha; subst f sn.
  rewrite Nat_sub_succ_1 in Hin.
  cbn in Hnl.
  replace (m + 1 + n * (m + 1)) with (S (n * (m + 1) + m)) in Hnl by flia.
  apply Nat.succ_inj in Hnl.
  destruct n; [ flia Hin | clear Hn ].
  apply Nat.succ_lt_mono in Hin.
  replace (S n * (m + 1) + m) with ((n + 2) * (m + 1) - 1) in Hl, Hnl by flia.
  remember ((n + 2) * (m + 1)) as m' eqn:Hm'.
  replace (S (m' - 1)) with m' in Hl by (ring_simplify in Hm'; flia Hm').
  replace (S (S n)) with (n + 2) in Hl by flia.
  subst m'.
  apply Nat.succ_lt_mono in Hi.
remember (n + 2) as n'.
Print log_prod_list.
Print log_prod_term.
...
(* en fait, ça va pas : nth_log_prod_list2 s'applique pour i entre
   0 et n(m+1)-1 (et non pas entre 1 et n-1) et seulement pour
   k<nm-2 et non pas k<n(m+1)-1 *)
(* donc, c'est nth_log_prod_list2 qui, pourtant est prouvé, qui ne
   va pas *)
  eapply nth_log_prod_list2; [ apply Hl | | ].
  2: {
    split; [ flia Hi | ].
    rewrite Nat.mul_add_distr_l, Nat.mul_1_r, Nat.add_assoc.
    flia Hin.
  }
...
}
assert (Hbetw2 : ∀ i, n < i < n * (m + 1) - 1 → List.nth i l f_zero = f_zero). {
...

Theorem step_1 {F : field} : ∀ s n,
  (∀ i, 0 < i → ls s i = ls s (n * i))
  → 1 < n
  → (series_but_mul_of s n = (pol_pow 1 - pol_pow n) .* s)%LS.
Proof.
intros * Hs Hn i.
remember ((i + 1) mod n) as m eqn:Hm; symmetry in Hm.
destruct m. {
  replace (ls _ (i + 1)) with f_zero by now cbn; rewrite Hm.
  symmetry.
  apply Nat.mod_divides in Hm; [ | flia Hn ].
  destruct Hm as (m, Hm).
  destruct m; [ flia Hm | ].
  rewrite Hm.
  clear i Hm.
  replace (S m) with (m + 1) by flia.
  revert m.
  induction m; intros. {
    rewrite Nat.mul_1_r.
    now apply mul_pol_1_sub_pow_ser_at_pow.
  }
  replace (S m + 1) with (m + 2) by flia.
...

Theorem step_1 {F : field} :
  (ζ_but_mul_of 2 = (pol_pow 1 - pol_pow 2) .* ζ)%LS.
Proof.
intros i.
unfold pol_pow.
cbn - [ ζ_but_mul_of ζ ".*" ].
unfold lp_sub, lp_opp, "+"%LP.
cbn - [ ζ_but_mul_of ζ ".*" ].
rewrite f_add_0_l, f_opp_0, f_add_0_r.
cbn - [ "mod" ls_pol_mul_l ].
remember (S i mod 2) as p eqn:Hp; symmetry in Hp.
symmetry.
destruct p. {
  apply Nat.mod_divides in Hp; [ | easy ].
  destruct Hp as (m & Hm).
  destruct m; [ flia Hm | ].
  assert (Hn : i = 2 * m + 1) by flia Hm; clear Hm.
  unfold ls_pol_mul_l.
  cbn - [ "/" "mod" ls_of_pol ζ ].
  rewrite Nat.sub_diag, Nat.div_1_r, Nat.sub_succ, Nat.sub_0_r.
  destruct (lt_dec i 0) as [H| H]; [ easy | clear H ].
  destruct (Nat.eq_dec i 0) as [H| H]; [ flia Hn H | clear H ].
  unfold ls_of_pol at 1 2.
  cbn - [ ls_of_pol log_prod ζ ].
  destruct i; [ flia Hn | ].
  destruct i. {
    cbn; rewrite f_mul_1_r.
    now rewrite f_mul_1_r, f_add_opp_diag_r, f_add_0_l.
  }
  replace (match _ with 0 | _ => f_zero end) with f_zero by now destruct i.
  rewrite f_mul_0_l, f_add_0_r, f_mul_1_l.
  rewrite ζ_is_one.
  assert (Hnn : 3 ≤ S (S i)). {
    destruct i. {
      destruct m; [ easy | ].
      destruct m; [ easy | flia Hn ].
    }
    flia.
  }
  rewrite log_prod_pol_ζ; [ apply f_add_opp_diag_r | easy | ].
  rewrite Hn, Nat.add_comm, Nat.mul_comm.
  now rewrite Nat.mod_add.
}
destruct p. 2: {
  specialize (Nat.mod_upper_bound (S i) 2 (Nat.neq_succ_0 _)) as H1.
  flia Hp H1.
}
unfold ls_pol_mul_l.
cbn - [ "/" "mod" ls_of_pol ζ ].
rewrite Nat.sub_diag, Nat.div_1_r, Nat.sub_succ, Nat.sub_0_r.
destruct (lt_dec i 0) as [H| H]; [ easy | clear H ].
rewrite Nat.mod_1_r.
do 2 rewrite ζ_is_one.
do 2 rewrite f_mul_1_r.
unfold ls_of_pol at 1 2.
cbn - [ ls_of_pol log_prod ζ ].
destruct (Nat.eq_dec i 0) as [Hn| Hn]. {
  subst i; cbn; apply f_add_0_r.
}
assert (H : i mod 2 = 0). {
  specialize (Nat.div_mod (S i) 2 (Nat.neq_succ_0 _)) as H1.
  rewrite Hp in H1.
  replace i with (0 + (S i / 2) * 2) by flia H1.
  now rewrite Nat.mod_add.
}
clear Hp; rename H into Hp.
apply Nat.mod_divides in Hp; [ | easy ].
destruct Hp as (p, Hp).
remember (ls_of_pol _) as q eqn:Hq.
replace (ls q i) with f_zero. 2: {
  destruct i; [ easy | ].
  destruct i; [ flia Hp | ].
  subst q; cbn; now destruct i.
}
rewrite f_add_0_r.
rewrite Hq, log_prod_pol_ζ'; [ apply f_add_0_r | | easy ].
replace i with (0 + p * 2) by flia Hp.
now rewrite Nat.mod_add.
Qed.

Theorem ζ_Euler_product_eq : False.
Proof.
Inspect 1.
...
