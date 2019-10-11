(* playing with prime numbers, as a break *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz.
Import List List.ListNotations.

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
  match n mod i with
  | 0 => f_one
  | _ => f_zero
  end.

Definition log_prod_term {F : field} u v i n :=
  (u i * v (n / i)%nat * ε i n)%F.

Fixpoint log_prod_list {F : field} cnt u v i n :=
  match cnt with
  | 0 => []
  | S cnt' => log_prod_term u v i n :: log_prod_list cnt' u v (i + 1) n
  end.

Definition log_prod {F : field} u v n :=
  List.fold_right f_add f_zero (log_prod_list n u v 1 n).

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

Theorem log_prod_list_length {F : field} : ∀ cnt u v i n,
  length (log_prod_list cnt u v i n) = cnt.
Proof.
intros.
revert i.
induction cnt; intros; [ easy | now cbn; rewrite IHcnt ].
Qed.

Theorem log_prod_list_succ {F : field} : ∀ cnt u v i n,
  log_prod_list (S cnt) u v i n =
    log_prod_term u v i n :: log_prod_list cnt u v (i + 1) n.
Proof. easy. Qed.

Theorem fold_log_prod_list_0_l {F : field} : ∀ cnt u v i n,
  (∀ n, u n = f_zero)
  → List.fold_right f_add f_zero (log_prod_list cnt u v i n) = f_zero.
Proof.
intros * Hu.
revert i.
induction cnt; intros; [ easy | cbn ].
unfold log_prod_term.
rewrite Hu, IHcnt.
rewrite <- f_mul_assoc, f_mul_0_l.
apply f_add_0_r.
Qed.

Theorem log_prod_0_l {F : field} : ∀ u v,
  (∀ n, u n = f_zero) → ∀ i, log_prod u v i = f_zero.
Proof.
intros * Hu i.
destruct i; intros; [ easy | ].
cbn; unfold log_prod_term.
rewrite Hu, f_mul_0_l, f_mul_0_l, f_add_0_l.
now apply fold_log_prod_list_0_l.
Qed.

Theorem ls_mul_0_l {F : field} : ∀ s1 s2,
  (∀ n, ls s1 n = f_zero) → ls_eq (ls_mul s1 s2) {| ls _ := f_zero |}.
Proof.
intros * Hs1 i.
cbn - [ "/" "mod" ].
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

Theorem fold_log_prod_list_add {F : field} : ∀ cnt x y u n i,
  fold_right f_add f_zero (log_prod_list cnt (ls (ls_of_pol (x + y))) u i n) =
  (fold_right f_add f_zero (log_prod_list cnt (ls (ls_of_pol x)) u i n) +
   fold_right f_add f_zero (log_prod_list cnt (ls (ls_of_pol y)) u i n))%F.
Proof.
intros.
revert i.
induction cnt; intros; [ cbn; symmetry; apply f_add_0_l | ].
cbn - [ ls_of_pol ].
rewrite IHcnt.
do 2 rewrite f_add_assoc; f_equal.
rewrite f_add_add_swap; f_equal.
unfold log_prod_term.
destruct i. {
  cbn.
  do 2 rewrite f_mul_0_l.
  symmetry; apply f_add_0_l.
}
rewrite <- Nat.add_1_r.
rewrite ls_of_pol_add.
rewrite ls_ls_add.
now do 2 rewrite f_mul_add_distr_r.
Qed.

Theorem log_prod_pol_add {F : field} : ∀ x y u n,
  log_prod (ls (ls_of_pol (x + y))) u n =
     (log_prod (ls (ls_of_pol x)) u n +
      log_prod (ls (ls_of_pol y)) u n)%F.
Proof.
intros.
unfold log_prod.
apply fold_log_prod_list_add.
Qed.

Theorem ls_mul_pol_add_distr_r {F : field} : ∀ x y s,
  ((x + y) .* s = x .* s + y .* s)%LS.
Proof.
intros * i.
rewrite Nat.add_1_r.
cbn - [ "/" "mod" ls_of_pol "-" log_prod ].
apply log_prod_pol_add.
Qed.

Theorem fold_log_prod_list_1_l {F : field} : ∀ cnt u i n,
  2 ≤ i
  → fold_right f_add f_zero
       (log_prod_list cnt (ls (ls_of_pol (pol_pow 1))) u i n) = f_zero.
Proof.
intros * Hi.
revert i Hi.
induction cnt; intros; [ easy | ].
cbn - [ ls_of_pol ].
unfold log_prod_term.
replace (ls _ i) with f_zero. 2: {
  destruct i; [ easy | ].
  destruct i; [ flia Hi | now destruct i ].
}
rewrite <- f_mul_assoc, f_mul_0_l, f_add_0_l.
apply IHcnt; flia Hi.
Qed.

Theorem ls_mul_pol_1_l {F : field} : ∀ s,
  (pol_pow 1 .* s = s)%LS.
Proof.
intros * n.
cbn - [ "/" "mod" ls_of_pol ].
rewrite Nat.add_1_r.
cbn - [ ls_of_pol ].
unfold log_prod_term.
rewrite Nat.div_1_r.
unfold ls_of_pol at 1.
cbn - [ ls_of_pol ].
rewrite f_mul_1_l, f_mul_1_r.
rewrite <- f_add_0_r; f_equal.
now apply fold_log_prod_list_1_l.
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

Theorem fold_log_prod_list_opp_l {F : field} : ∀ cnt u i n p,
  fold_right f_add f_zero (log_prod_list cnt (ls (ls_of_pol (- p))) u i n) =
  (- fold_right f_add f_zero (log_prod_list cnt (ls (ls_of_pol p)) u i n))%F.
Proof.
intros.
revert i.
induction cnt; intros; [ cbn; symmetry; apply f_opp_0 | ].
cbn - [ ls_of_pol ].
rewrite IHcnt.
rewrite f_opp_add_distr; f_equal.
unfold log_prod_term.
destruct i. {
  cbn.
  rewrite <- f_mul_assoc, f_mul_0_l.
  symmetry; apply f_opp_0.
}
rewrite <- Nat.add_1_r.
rewrite ls_of_pol_opp.
rewrite ls_of_opp.
now do 2 rewrite f_mul_opp_l.
Qed.

Theorem ls_mul_pol_opp_l {F : field} : ∀ p s,
  (- p .* s = - (p .* s))%LS.
Proof.
intros * i.
cbn - [ "/" "mod" ls_of_pol ].
unfold log_prod.
apply fold_log_prod_list_opp_l.
Qed.

Theorem firstn_log_prod_list {F : field} : ∀ m cnt u v i n,
  firstn m (log_prod_list cnt u v i n) =
  log_prod_list (min m cnt) u v i n.
Proof.
intros.
revert i m n.
induction cnt; intros; [ now rewrite Nat.min_0_r, List.firstn_nil | ].
cbn - [ "-" ].
destruct m; [ easy | ].
rewrite List.firstn_cons.
rewrite <- Nat.succ_min_distr; cbn.
f_equal; apply IHcnt.
Qed.

Theorem skipn_log_prod_list {F : field} : ∀ m cnt u v i n,
  skipn m (log_prod_list cnt u v i n) =
  log_prod_list (cnt - m) u v (i + m) n.
Proof.
intros.
revert i m n.
induction cnt; intros; [ apply List.skipn_nil | ].
cbn - [ "-" ].
destruct m; [ now rewrite Nat.add_0_r | ].
rewrite Nat.sub_succ, List.skipn_cons.
replace (i + S m) with (i + 1 + m) by flia.
apply IHcnt.
Qed.

(* a version using firstn_log_prod_list could be better, perhaps *)
Theorem in_firstn_log_prod_list {F : field} : ∀ x n c m k u,
  In x
    (firstn (n - k)
       (log_prod_list c (ls (ls_of_pol (pol_pow 1 - pol_pow (n + 2))))
          u (2 + k) ((n + 2) * (m + 1))))
  → x = f_zero.
Proof.
intros * Hx.
revert k Hx.
induction c; intros; [ now destruct (n - k) | ].
cbn - [ ls_of_pol ] in Hx.
remember (n - k) as p eqn:Hp; symmetry in Hp.
destruct p; [ easy | ].
cbn - [ ls_of_pol ] in Hx.
destruct Hx as [Hx| Hx]. {
  subst x.
  unfold log_prod_term.
  replace (ls _ (S (S k))) with f_zero. 2: {
    symmetry; cbn.
    replace (n + 2 - 1) with (S n) by flia.
    cbn.
    clear - Hp.
    destruct n; [ flia Hp | ].
    revert k p Hp.
    induction n; intros. {
      cbn.
      rewrite f_add_opp_diag_r.
      destruct k; [ easy | flia Hp ].
    }
    destruct k; [ apply f_add_opp_diag_r | ].
    assert (H : S n - k = S p) by flia Hp.
    now specialize (IHn _ _ H).
  }
  now rewrite <- f_mul_assoc, f_mul_0_l.
}
replace p with (n - S k) in Hx by flia Hp.
replace (S (S (k + 1))) with (2 + S k) in Hx by flia.
now specialize (IHc (S k) Hx) as H1.
Qed.

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
  cbn - [ ls_of_pol ].
  unfold log_prod.
  remember
    (log_prod_list (n * S m) (ls (ls_of_pol (pol_pow 1 - pol_pow n))) (ls s)
        1 (n * S m))
    as l eqn:Hl.
Compute (List.hd 0 [1;2;3;4;5;6;7]).
Compute (let n := 5 in List.firstn (n - 2) (List.tl [1;2;3;4;5;6;7])).
Compute (let n := 5 in List.hd 0 (List.skipn (n - 1) [1;2;3;4;5;6;7])).
Compute (let n := 5 in List.skipn n [1;2;3;4;5;6;7]).
  assert (H11 : List.hd f_zero l = ls s (S m)). {
    destruct l as [| a l]. {
      destruct n; [ flia Hn | easy ].
    }
    remember (n * S m) as cnt eqn:Hcnt; symmetry in Hcnt.
    rewrite <- Hcnt in Hl at 2.
    destruct cnt; [ easy | ].
    cbn - [ ls_of_pol ] in Hl.
    remember ls_of_pol as f.
    injection Hl; clear Hl; intros Hl Hx; subst f; cbn.
    subst a.
    unfold log_prod_term.
    rewrite Nat.div_1_r.
    replace (ls _ 1) with f_one. 2: {
      symmetry; cbn.
      destruct n; [ easy | ].
      destruct n; [ flia Hn | cbn ].
      destruct n; cbn; rewrite f_opp_0; apply f_add_0_r.
    }
    rewrite f_mul_1_l.
    unfold ε.
    rewrite Nat.mod_1_r, f_mul_1_r.
    rewrite <- Hs; [ easy | flia ].
  }
  assert
    (Hz1 : ∀ x,
     List.In x (List.firstn (n - 2) (List.tl l)) → x = f_zero). {
    intros x Hx.
    remember (n * S m) as cnt eqn:Hcnt; symmetry in Hcnt.
    destruct n; [ flia Hn | ].
    destruct n; [ flia Hn | clear Hn ].
    replace (S (S n) - 2) with n in Hx by flia.
    assert (H : cnt = S ((n + 2) * m + n + 1)) by flia Hcnt.
    clear Hcnt; subst cnt.
    rewrite Hl in Hx.
    cbn - [ ls_of_pol ] in Hx.
    clear - Hx.
    remember ((n + 2) * m + n + 1) as c eqn:Hc.
    replace (S (S n)) with (n + 2) in Hx by flia.
    apply (in_firstn_log_prod_list _ n c m 0 (ls s)).
    rewrite Nat.sub_0_r, Nat.add_0_r.
    now replace (S c) with ((n + 2) * (m + 1)) in Hx by flia Hc.
  }
  assert (Hn1 : List.hd f_zero (List.skipn (n - 1) l) = (- ls s (S m))%F). {
    destruct n; [ flia Hn | ].
    rewrite Nat_sub_succ_1.
    destruct n; [ flia Hn | cbn ].
    destruct l as [| a l]; [ easy | ].
    remember ((n + 2) * m + n + 1) as p eqn:Hp.
    replace (S (S n) * S m) with (S p) in Hl by flia Hp.
    cbn - [ ls_of_pol ] in Hl.
    remember ls_of_pol as f.
    injection Hl; clear Hl; intros Hl Ha; subst f.
    rewrite Hl, skipn_log_prod_list.
    replace (p - n) with (S ((n + 2) * m)) by flia Hp.
    cbn - [ ls_of_pol ].
    unfold log_prod_term.
    replace (ls _ (S (S n))) with (- f_one)%F. 2: {
      symmetry; clear; cbn.
      destruct n; [ now cbn; rewrite f_add_0_l | ].
      induction n; [ now cbn; rewrite f_add_0_l | ].
      apply IHn.
    }
    unfold ε.
    remember (ls s (S p / S (S n))) as x.
    replace (S p) with (0 + (m + 1) * S (S n)) by flia Hp.
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.mod_0_l; [ | easy ].
    rewrite f_mul_opp_l, f_mul_1_l, f_mul_1_r.
    f_equal; subst x.
    replace (S p) with (0 + (m + 1) * S (S n)) by flia Hp.
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.div_0_l; [ | easy ].
    now rewrite Nat.add_0_l, Nat.add_1_r.
  }
  assert (Hz2 : ∀ x, List.In x (List.skipn n l) → x = f_zero). {
    intros * Hx.
    remember (n * S m) as cnt eqn:Hcnt; symmetry in Hcnt.
    destruct n; [ flia Hn | ].
    destruct n; [ flia Hn | clear Hn ].
    assert (H : cnt = S (S ((n + 2) * m + n))) by flia Hcnt.
    clear Hcnt; subst cnt.
    rewrite Hl in Hx.
    cbn - [ ls_of_pol ] in Hx.
    clear - Hx.
    remember ((n + 2) * m + n) as c eqn:Hc.
    replace (S (S n)) with (n + 2) in Hx by flia.
    rewrite skipn_log_prod_list in Hx.
    replace (c - n) with ((n + 2) * m) in Hx by flia Hc.
    replace (S (S c)) with ((n + 2) * m + n + 2) in Hx by flia Hc.
    clear c Hc.
    remember ((n + 2) * m) as c eqn:Hc.
...
    clear Hc.
    induction c; [ easy | ].
    cbn - [ ls_of_pol ] in Hx.
...
    apply (in_firstn_log_prod_list _ n 2 c m 0 (ls s)); [ flia | ].
    rewrite Nat.sub_0_r, Nat.add_0_r.
    replace (S (S c)) with ((n + 2) * (m + 1)) in Hx by flia Hc.
  }
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
