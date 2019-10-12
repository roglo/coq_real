(* playing with prime numbers, as a break *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz Setoid.
Import List List.ListNotations.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level).

Theorem Nat_sub_succ_1 : ∀ n, S n - 1 = n.
Proof. now intros; rewrite Nat.sub_succ, Nat.sub_0_r. Qed.

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
    f_add_comm : ∀ x y, f_add x y = f_add y x;
    f_add_assoc : ∀ x y z, f_add x (f_add y z) = f_add (f_add x y) z;
    f_add_0_l : ∀ x, f_add f_zero x = x;
    f_add_opp_diag_l : ∀ x, f_add (f_opp x) x = f_zero;
    f_mul_comm : ∀ x y, f_mul x y = f_mul y x;
    f_mul_assoc : ∀ x y z, f_mul x (f_mul y z) = f_mul (f_mul x y) z;
    f_mul_1_l : ∀ x, f_mul f_one x = x;
    f_mul_inv_diag_l : ∀ x, x ≠ f_zero → f_mul (f_inv x) x = f_one;
    f_mul_add_distr_l : ∀ x y z,
      f_mul x (f_add y z) = f_add (f_mul x y) (f_mul x z) }.

Declare Scope field_scope.
Delimit Scope field_scope with F.

Definition f_sub {F : field} x y := f_add x (f_opp y).

Notation "- x" := (f_opp x) : field_scope.
Notation "x + y" := (f_add x y) : field_scope.
Notation "x - y" := (f_sub x y) : field_scope.
Notation "x * y" := (f_mul x y) : field_scope.

Theorem f_add_0_r {F : field} : ∀ x, (x + f_zero)%F = x.
Proof.
intros.
rewrite f_add_comm.
apply f_add_0_l.
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

Theorem f_mul_1_r {F : field} : ∀ x, (x * f_one)%F = x.
Proof.
intros.
rewrite f_mul_comm.
apply f_mul_1_l.
Qed.

(* Euler product formula *)

(* https://en.wikipedia.org/wiki/Proof_of_the_Euler_product_formula_for_the_Riemann_zeta_function *)

(*
Riemann zeta function is
   ζ(s) = 1 + 1/2^s + 1/3^s + 1/4^s + 1/5^s + ...

Euler product formula is the fact that
                    1
   ζ(s) = -----------------------------------------------
          (1-1/2^s) (1-1/3^s) (1-1/5^s) ... (1-1/p^s) ...

where the product in the denominateur applies on all prime numbers
and only them.

The proof is the following.

We first prove that
   (1-1/2^s) ζ(s) = 1 + 1/3^s + 1/5^s + 1/7^s + ...

i.e. all terms but the multiples of 2
i.e. all odd numbers

(this is easy to verify on a paper)

Then we continue by proving
   (1-1/3^s) (1-1/2^s) ζ(s) =
       1 + 1/5^s + 1/7^s + 1/11^s + ... + 1/23^s + 1/25^s + ...

i.e. all terms but the multiples of 2 and 3

Then we do it for the number (5) in the second term (1/5^s) of the series.

This number in the second term is always the next prime number, like in the
Sieve of Eratosthenes.

Up to prime number p, we have, using commutativity
  (1-1/2^s) (1-1/3^s) ... (1-1/p^s) ζ(s) = 1 + 1/q^s + ...

where q is the prime number after p and the rest holds terms whose
number is greater than q and not divisible by the primes between
2 and p.

When p tends towards infinity, the term to the right is just 1
and we get Euler's formula.

    ---

Implementation.

ζ(s) and all the expressions above are actually of the form
    a₁ + a₂/2^s + a₃/3^s + a₄/4^s + ...

We can represent them as the sequence
    (a_n) = (a₁, a₂, a₃, ...)

For example, ζ is (1, 1, 1, 1, ...)
and (1-1/3^s) is (1, 0, -1, 0, 0, 0, ...)

We call them "series with logarithm powers" because they can be
written
    a₁ + a₂ x^ln(2) + a₃ x^ln(3) + a₄ x^ln(4) + a₅ x^ln(5) + ...

with x = e^(-s). Easy to verify.

Note that we do not consider the parameter s or x. The fact that
they are supposed to be complex number is irrelevant in this proof.
We just consider they belong to a field (type "field" defined
above).
*)

(* Definition of the type of such a series *)

Class ln_series {F : field} :=
  { ls : nat → f_type }.

(* Definition of the type of a polynomial (a finite series) *) 

Class ln_polyn {F : field} :=
  { lp : list f_type }.

(* Syntactic scopes, allowing to use operations on series and
   polynomials with usual mathematical forms. For example we can
   write e.g.
        (s1 * s2 + s3)%LS
   instead of the less readable
        ls_add (ls_mul s1 s2) s3
*)

Declare Scope ls_scope.
Delimit Scope ls_scope with LS.

Declare Scope lp_scope.
Delimit Scope lp_scope with LP.

Arguments ls {_} _%LS _%nat.
Arguments lp {_}.

(* Equality between series; since these series start with 1, the
   comparison is only on natural indices different from 0 *)

Definition ls_eq {F : field} s1 s2 := ∀ n, n ≠ 0 → ls s1 n = ls s2 n.
Arguments ls_eq _ s1%LS s2%LS.

Theorem ls_eq_refl {F : field} : reflexive _ ls_eq.
Proof. easy. Qed.

Theorem ls_eq_sym {F : field} : symmetric _ ls_eq.
Proof.
intros x y Hxy i Hi.
now symmetry; apply Hxy.
Qed.

Theorem ls_eq_trans {F : field} : transitive _ ls_eq.
Proof.
intros x y z Hxy Hyz i Hi.
now eapply eq_trans; [ apply Hxy | apply Hyz ].
Qed.

Add Parametric Relation {F : field} : (ln_series) ls_eq
 reflexivity proved by ls_eq_refl
 symmetry proved by ls_eq_sym
 transitivity proved by ls_eq_trans
 as ls_eq_rel.

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

Notation "x - y" := (lp_sub x y) : lp_scope.

Definition ζ {F : field} := {| ls _ := f_one |}.

Definition series_but_mul_of {F : field} n s :=
  {| ls i :=
       match i mod n with
       | 0 => f_zero
       | _ => ls s i
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

Arguments ls_of_pol _ p%LP.
Arguments ls_pol_mul_l _ p%LP s%LS.

Notation "x = y" := (ls_eq x y) : ls_scope.
Notation "p .* s" := (ls_pol_mul_l p s) (at level 41, right associativity) :
   ls_scope.

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

Definition pol_pow {F : field} n :=
  {| lp := List.repeat f_zero (n - 1) ++ [f_one] |}.

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

Theorem pol_1_sub_pow_coeff_1 {F : field} : ∀ n,
  1 < n
  → ls (ls_of_pol (pol_pow 1 - pol_pow n)) 1 = f_one.
Proof.
intros * Hn; cbn.
destruct n; [ flia Hn | ].
destruct n; [ flia Hn | ].
destruct n; cbn; rewrite f_opp_0; apply f_add_0_r.
Qed.

Theorem pol_1_sub_pow_coeff_minus_1 {F : field} : ∀ n,
  1 < n
  → ls (ls_of_pol (pol_pow 1 - pol_pow n)) n = (- f_one)%F.
Proof.
intros * Hn; cbn.
destruct n; [ flia Hn | ].
destruct n; [ flia Hn | clear Hn ].
destruct n; [ now cbn; rewrite f_add_0_l | ].
induction n; [ now cbn; rewrite f_add_0_l | ].
apply IHn.
Qed.

Theorem pol_1_sub_pow_coeff_0 {F : field} : ∀ n i,
  1 < n
  → 1 < i ∧ i ≠ n
  → ls (ls_of_pol (pol_pow 1 - pol_pow n)) i = f_zero.
Proof.
intros * Hn (Hi, Hin); cbn.
destruct n; [ flia Hn | ].
destruct n; [ flia Hn | clear Hn ].
destruct i; [ easy | ].
destruct i; [ flia Hi | clear Hi ].
destruct n. {
  destruct i; [ easy | now destruct i ].
}
replace (S n + 2 - 1) with (2 + n) by flia; cbn.
rewrite f_add_opp_diag_r.
destruct i; [ easy | ].
assert (Hi : i ≠ n) by flia Hin.
clear Hin.
revert i Hi.
induction n; intros. {
  cbn.
  destruct i; [ easy | ].
  destruct i; [ easy | now destruct i].
}
destruct i; [ cbn; apply f_add_opp_diag_r | ].
cbn.
apply IHn; flia Hi.
Qed.

Theorem step_1_lemma_1 {F : field} : ∀ x n c m k u,
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
  rewrite pol_1_sub_pow_coeff_0; [ | flia | flia Hp ].
  now rewrite <- f_mul_assoc, f_mul_0_l.
}
replace p with (n - S k) in Hx by flia Hp.
replace (S (S (k + 1))) with (2 + S k) in Hx by flia.
now specialize (IHc (S k) Hx) as H1.
Qed.

Theorem step_1_lemma_2 {F : field} : ∀ m k x c n u,
  In x
    (log_prod_list c (ls (ls_of_pol (pol_pow 1 - pol_pow (n + 2)))) u
       (3 + n + m) k)
  → x = f_zero.
Proof.
intros * Hx.
revert k m Hx.
induction c; intros; [ easy | ].
cbn - [ ls_of_pol ] in Hx.
destruct Hx as [Hx| Hx]. {
  subst x.
  unfold log_prod_term.
  rewrite pol_1_sub_pow_coeff_0; [ | flia | flia ].
  now rewrite <- f_mul_assoc, f_mul_0_l.
}
apply (IHc k (S m)).
now replace (3 + n + S m) with (S (S (S (n + m + 1)))) by flia.
Qed.

Theorem step_1 {F : field} : ∀ s n,
  (∀ i, 0 < i → ls s i = ls s (n * i))
  → 1 < n
  → ((pol_pow 1 - pol_pow n) .* s = series_but_mul_of n s)%LS.
Proof.
intros * Hs Hn i Hi.
destruct i; [ flia Hi | clear Hi; rewrite <- (Nat.add_1_r i) ].
symmetry.
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
    rewrite pol_1_sub_pow_coeff_1; [ | easy ].
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
    apply (step_1_lemma_1 _ n c m 0 (ls s)).
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
    rewrite pol_1_sub_pow_coeff_minus_1; [ | flia ].
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
    eapply (step_1_lemma_2 0).
    rewrite Nat.add_0_r.
    apply Hx.
  }
  replace l with
     (List.hd f_zero l :: List.firstn (n - 2) (tl l) ++
      List.hd f_zero (skipn (n - 1) l) :: skipn n l). 2: {
    rewrite List.app_comm_cons.
    symmetry.
    rewrite <- (firstn_skipn (n - 1) l) at 1.
    f_equal. {
      rewrite <- List.firstn_cons.
      destruct l as [| a l]. {
        destruct n; [ flia Hn | easy ].
      }
      cbn.
      replace (n - 1) with (S (n - 2)) by flia Hn.
      apply List.firstn_cons.
    }
    assert (Hlen : n ≤ List.length l). {
      rewrite Hl.
      rewrite log_prod_list_length.
      rewrite Nat.mul_comm; cbn; flia.
    }
    destruct n; [ flia Hn | ].
    rewrite Nat_sub_succ_1.
    clear - Hlen.
    revert n Hlen.
    induction l as [| a l]; intros; [ easy | ].
    destruct n; [ easy | ].
    rewrite List.skipn_cons.
    remember (S n) as sn; cbn; subst sn.
    cbn in Hlen.
    apply IHl; flia Hlen.
  }
  cbn; rewrite List.fold_right_app; cbn.
  rewrite H11, Hn1.
  replace (List.fold_right _ _ (skipn n _)) with f_zero. 2: {
    symmetry.
    remember (skipn n l) as l'.
    clear - Hz2; rename l' into l.
    induction l as [| a l]; [ easy | ].
    cbn in Hz2 |- *.
    rewrite (Hz2 a); [ | now left ].
    rewrite f_add_0_l.
    apply IHl; intros x Hx.
    now apply Hz2; right.
  }
  rewrite f_add_0_r.
  replace (fold_right f_add _ _) with (- ls s (S m))%F. 2: {
    symmetry.
    remember (- ls s (S m))%F as x.
    remember (firstn _ (tl l)) as l'.
    clear - Hz1.
    rename l' into l.
    induction l as [| a l]; [ easy | cbn ].
    rewrite (Hz1 a); [ | now left ].
    rewrite f_add_0_l.
    apply IHl; intros y Hy.
    apply Hz1; cbn.
    now right.
  }
  apply f_add_opp_diag_r.
}
cbn - [ ls_of_pol ].
rewrite Hm; symmetry; unfold log_prod.
replace (i + 1) with (S i) by flia.
rewrite log_prod_list_succ.
cbn - [ ls_of_pol ].
unfold log_prod_term.
rewrite pol_1_sub_pow_coeff_1; [ | easy ].
unfold ε.
rewrite Nat.mod_1_r, f_mul_1_l, f_mul_1_r.
rewrite Nat.div_1_r, <- f_add_0_r; f_equal.
assert
  (H : ∀ c k,
   fold_right f_add f_zero
     (log_prod_list c
        (ls (ls_of_pol (pol_pow 1 - pol_pow n))) (ls s) (k + 2) (S i)) =
     f_zero). {
  intros *.
  revert k.
  induction c; intros; [ easy | ].
  cbn - [ ls_of_pol ].
  replace (log_prod_term _ _ _ _) with f_zero. 2: {
    symmetry; unfold log_prod_term.
    unfold ε.
    remember (S i mod (k + 2)) as p eqn:Hp; symmetry in Hp.
    destruct p. {
      rewrite pol_1_sub_pow_coeff_0; [ | easy | ]. 2: {
        split; [ flia | ].
        intros H; rewrite H, <- Nat.add_1_r in Hp.
        now rewrite Hp in Hm.
      }
      now rewrite <- f_mul_assoc, f_mul_0_l.
    }
    apply f_mul_0_r.
  }
  rewrite f_add_0_l.
  replace (k + 2 + 1) with (k + 1 + 2) by flia.
  apply IHc.
}
replace 2 with (0 + 2) by flia.
apply H.
Qed.

Require Import Morphisms.

Instance series_but_mul_of_morph {F : field} :
  Proper (eq ==> ls_eq ==> ls_eq) series_but_mul_of.
Proof.
intros x y Hxy s1 s2 Hss i Hi.
destruct i; [ flia Hi | clear Hi; rewrite <- (Nat.add_1_r i) ].
subst x; cbn.
destruct ((i + 1) mod y) as [H| H]; [ easy | ].
apply Hss; flia.
Qed.

Theorem step_1_ζ {F : field} :
  ((pol_pow 1 - pol_pow 2) .* ζ = series_but_mul_of 2 ζ)%LS.
Proof.
apply step_1; [ easy | flia ].
Qed.

Theorem step_42_ζ {F : field} : ∀ n,
  1 < n
  → ((pol_pow 1 - pol_pow n) .* ζ = series_but_mul_of n ζ)%LS.
Proof.
intros * Hn.
now apply step_1.
Qed.

Theorem step_2 {F : field} : ∀ s a b,
  (∀ i, 0 < i → ls s i = ls s (a * i))
  → (∀ i, 0 < i → ls s i = ls s (b * i))
  → 1 < a
  → 1 < b
  → Nat.gcd a b = 1
  → ((pol_pow 1 - pol_pow b) .* (pol_pow 1 - pol_pow a) .* s =
      series_but_mul_of b (series_but_mul_of a s))%LS.
Proof.
intros * Ha Hb H1a H1b Gab.
rewrite step_1; [ now rewrite step_1 | | easy ].
intros i Hi.
rewrite step_1; [ | easy | easy | flia Hi ].
(*
destruct i; [ flia Hi | clear Hi; rewrite <- (Nat.add_1_r i) ].
replace b with (b - 1 + 1) by flia H1b.
replace ((b - 1 + 1) * (i + 1)) with (i + (b - 1) * S i + 1) by flia H1b.
*)
rewrite step_1; [ | easy | easy | ]. 2: {
  intros Hbi.
  apply Nat.eq_mul_0 in Hbi.
  flia H1b Hi Hbi.
}
remember (series_but_mul_of a s) as sa eqn:Hsa.
(*
replace (i + (b - 1) * S i + 1) with ((b - 1 + 1) * (i + 1)) by flia.
rewrite Nat.sub_add by flia H1b.
*)
assert (Hsai : ∀ i : nat, 0 < i → ls sa i = ls sa (b * i)). {
  subst sa.
  clear - H1a Hb Gab.
  intros i Hi.
  unfold series_but_mul_of; cbn.
  rewrite <- Nat.mul_mod_idemp_r; [ | flia H1a ].
  rewrite Nat.mul_comm.
  remember (i mod a) as n eqn:Hn; symmetry in Hn.
  destruct n. {
    cbn; rewrite Nat.mod_0_l; [ easy | flia H1a ].
  }
  rewrite <- Hb; [ | easy ].
  remember ((S n * b) mod a) as m eqn:Hm; symmetry in Hm.
  destruct m; [ | easy ].
  exfalso.
  apply Nat.mod_divides in Hm; [ | flia H1a ].
  destruct Hm as (m, Hm).
  move m before n.
  specialize (Nat.gauss a b (S n)) as H1.
  rewrite Nat.mul_comm, Hm in H1.
  specialize (Nat.divide_factor_l a m) as H.
  specialize (H1 H Gab); clear H.
  rewrite <- Hn in H1.
  unfold Nat.divide in H1.
  destruct H1 as (z, Hz).
  destruct z; [ now rewrite Hn in Hz | ].
  specialize (Nat.mod_upper_bound i a) as H1.
  assert (H : a ≠ 0) by flia H1a.
  specialize (H1 H); clear H.
  rewrite Hz in H1.
  apply Nat.nle_gt in H1.
  apply H1; cbn; flia.
}
now apply Hsai.
Qed.

(*
Here, we try to prove that
   (1 - 1/2^s) (1 - 1/3^s) (1 - 1/5^s) ... (1 - 1/p^s) ζ(s)
is equal to
   ζ(s) without terms whose rank is divisible by 2, 3, 5, ... or p
i.e.
   1 + 1/q^s + ... where q is the next prime after p

But actually, our theorem is a little more general:

1/ we do not do it for 2, 3, 5 ... p but for any list of natural numbers
   (n1, n2, n3, ... nm) such that gcd(ni,nj) = 1 for i≠j

2/ It is not the η function but any series r with logarithm powers such that
       ∀ i, r_{i} = r_{n*i}
   for any n in (n1, n2, n3 ... nm)
*)

Notation "r ~{ i }" := (ls r i) (at level 1, format "r ~{ i }").
Notation "x '∈' l" := (List.In x l) (at level 60).

Theorem step_3 {F : field} : ∀ (r : ln_series) (l : list nat),
  (∀ a, a ∈ l → ∀ i, 0 < i → r~{i} = r~{a*i})
  → (∀ a, List.In a l → 2 ≤ a)
  → (∀ a b, List.In a l → List.In b l → a ≠ b → Nat.gcd a b = 1)
  → List.fold_right (λ a c, ((pol_pow 1 - pol_pow a) .* c)%LS) r l =
     List.fold_right series_but_mul_of r l.
Proof.
intros * Ha Hge2 Hgcd.
...

Theorem ζ_Euler_product_eq : False.
Proof.
Inspect 1.
...
