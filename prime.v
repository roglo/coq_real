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
    f_add_0_r : ∀ x, f_add x f_zero = x;
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

Theorem ls_eq_refl {F : field} : reflexive _ ls_eq.
Proof. easy. Qed.

Theorem ls_eq_sym {F : field} : symmetric _ ls_eq.
Proof. easy. Qed.

Theorem ls_eq_trans {F : field} : transitive _ ls_eq.
Proof.
intros x y z Hxy Hyz i.
eapply eq_trans; [ apply Hxy | apply Hyz ].
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

Definition series_but_mul_of {F : field} s n :=
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
Notation "p .* s" := (ls_pol_mul_l p s) (at level 40) : ls_scope.

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

Theorem step_1_ζ {F : field} :
  ((pol_pow 1 - pol_pow 2) .* ζ = series_but_mul_of ζ 2)%LS.
Proof.
symmetry.
apply step_1; [ easy | flia ].
Qed.

Theorem ζ_Euler_product_eq : False.
Proof.
Inspect 1.
...
