(* playing with prime numbers, as a break *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz Setoid Morphisms.
Import List List.ListNotations.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x < y ≤ z" := (x < y ∧ y <= z)%nat (at level 70, y at next level).
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat (at level 70, y at next level).

Theorem Nat_sub_succ_1 : ∀ n, S n - 1 = n.
Proof. now intros; rewrite Nat.sub_succ, Nat.sub_0_r. Qed.

Theorem fold_mod_succ : ∀ n d, d - snd (Nat.divmod n d 0 d) = n mod (S d).
Proof. easy. Qed.

Theorem List_fold_right_cons {A B} : ∀ (f : B → A → A) (a : A) x l,
  List.fold_right f a (x :: l) = f x (List.fold_right f a l).
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

Definition ls_one {F : field} :=
  {| ls n := match n with 1 => f_one | _ => f_zero end |}.

Definition List_combine_all {A} (l1 l2 : list A) (d : A) :=
  let '(l'1, l'2) :=
    match List.length l1 ?= List.length l2 with
    | Eq => (l1, l2)
    | Lt => (l1 ++ List.repeat d (List.length l2 - List.length l1), l2)
    | Gt => (l1, l2 ++ List.repeat d (List.length l1 - List.length l2))
    end
  in
  List.combine l'1 l'2.

Notation "r ~{ i }" := (ls r i) (at level 1, format "r ~{ i }").
Notation "x '∈' l" := (List.In x l) (at level 60).

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

Definition divisors_from d n :=
  List.filter (λ a, n mod a =? 0) (List.seq d n).

Definition divisors_of := divisors_from 1.

Definition log_prod_add {F : field} u v n i c :=
  (c + u i * v (n / i))%F.

Definition log_prod {F : field} u v n :=
  List.fold_right (log_prod_add u v n) f_zero (divisors_of n).

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
Notation "x * y" := (ls_mul x y) : ls_scope.
Notation "p .* s" := (ls_pol_mul_l p s) (at level 41, right associativity) :
   ls_scope.

(* allows to rewrite
      Hn : n = n'
      Hs : s = s'
   in expression
      series_but_mul_of n s *)
Instance series_but_mul_of_morph {F : field} :
  Proper (eq ==> ls_eq ==> ls_eq) series_but_mul_of.
Proof.
intros x y Hxy s1 s2 Hss i Hi.
destruct i; [ flia Hi | clear Hi; rewrite <- (Nat.add_1_r i) ].
subst x; cbn.
destruct ((i + 1) mod y) as [H| H]; [ easy | ].
apply Hss; flia.
Qed.

(*
(* allows to rewrite
      H1 : s1 = s3
      H2 : s2 = s4
   in expression
      (s1 * s2)%F *)
Instance ls_mul_morph {F : field} :
  Proper (ls_eq ==> ls_eq ==> ls_eq) ls_mul.
Proof.
intros r1 r2 Hrr r'1 r'2 Hrr' i Hi; cbn.
unfold log_prod.
remember (log_prod_list i 1 i) as l eqn:Hl.
assert (Ha : ∀ a, a ∈ l → a ≠ 0 ∧ i / a ≠ 0). {
  intros a Ha.
  subst l.
  destruct i; [ easy | cbn in Ha ].
  destruct Ha as [Ha| Ha]. {
    subst a.
    now rewrite Nat.div_1_r.
  }
  destruct i; [ easy | cbn - [ "mod" ] in Ha ].
  replace (S (S i)) with (i + 1 * 2) in Ha at 1 by flia.
  rewrite Nat.mod_add in Ha; [ | easy ].
  remember (i mod 2) as m eqn:Hm; symmetry in Hm.
  destruct m. {
    destruct Ha as [Ha| Ha]. {
      subst a.
      split; [ easy | intros H ].
      apply Nat.div_small_iff in H; [ | easy ].
      flia H.
    }
    destruct i; [ easy | ].
    cbn - [ "mod" ] in Ha.
    replace (S (S (S i))) with (i + 1 * 3) in Ha at 1 by flia.
    rewrite Nat.mod_add in Ha; [ | easy ].
    remember (i mod 3) as m3 eqn:Hm3; symmetry in Hm3.
    destruct m3. {
      destruct Ha as [Ha| Ha]. {
        subst a.
        split; [ easy | intros H ].
        apply Nat.div_small_iff in H; [ | easy ].
        flia H.
      }
      destruct i; [ easy | ].
...
  assert
    (H : ∀ cnt k j, cnt ≤ S j → k ≠ 0 →
     ∀ a, a ∈ log_prod_list cnt k (k + i) → a ≠ 0). {
    clear a i Ha Hi Hl.
    intros * Hcnt Hk a Ha.
    destruct k; [ easy | clear Hk ].
    revert i k Hcnt Ha.
    induction cnt; intros; [ easy | ].
    cbn - [ "mod" ] in Ha.
    remember (S (k + i) mod S k) as m eqn:Hm; symmetry in Hm.
    destruct m. {
      destruct Ha as [Ha| Ha]; [ now subst a | ].
      apply (IHcnt (i - 1) (k + 1)); [ flia Hcnt | ].
      replace (S (k + 1) + (i - 1)) with (S (k + i)) by flia Hcnt.
    }
    apply (IHcnt (k + 1) (n - 1)); [ flia Hcnt | ].
    now replace (S (k + 1) + (n - 1)) with (S (k + n)) by flia Hcnt.
  }
  destruct i; [ easy | clear Hi ].
  split. {
    apply (H (S i) 1 i).
...
    apply (H i 1 i); [ easy | ].
    now rewrite Hl in Ha.
  }
...
unfold log_prod_add.
assert (H : ∀ cnt k i, cnt ≤ S i → k ≠ 0 →
  log_prod_list cnt (ls r1) (ls r'1) k (k + i) =
  log_prod_list cnt (ls r2) (ls r'2) k (k + i)). {
  clear i.
  intros * Hcnt Hk.
  destruct k; [ easy | clear Hk ].
  revert i k Hcnt.
  induction cnt; intros; [ easy | cbn ].
  unfold log_prod_term.
  f_equal. {
    rewrite Hrr; [ | easy ].
    rewrite Hrr'; [ easy | ].
    intros H.
    apply Nat.div_small_iff in H; [ | easy ].
    flia H.
  }
  destruct i. 2: {
    replace (S (k + S i)) with (S (k + 1 + i)) by flia.
    apply IHcnt.
    flia Hcnt.
  }
  destruct cnt; [ easy | flia Hcnt ].
}
now apply H.
Qed.
*)

(*
(* allows to rewrite
      Hp : p1 = p2
      Hs : s1 = s2
   in expression
      (p1 .* s2)%F *)
Instance ls_pol_mul_morph {F : field} :
  Proper (eq ==> ls_eq ==> ls_eq) ls_pol_mul_l.
Proof.
intros p1 p2 Hpp r1 r2 Hrr i Hi.
subst p1.
now apply ls_mul_morph.
Qed.
*)

Theorem fold_log_prod_1_l_from_2nd {F : field} : ∀ r i l,
  (∀ j, j ∈ l → 2 ≤ j)
  → fold_right (log_prod_add (ls ls_one) (ls r) (S i)) f_zero l = f_zero.
Proof.
intros * Hin.
revert i.
induction l as [| a l]; intros; [ easy | ].
cbn - [ ls_one ].
rewrite IHl. 2: {
  intros j Hj.
  now apply Hin; right.
}
unfold log_prod_add.
replace ls_one~{a} with f_zero. 2: {
  cbn.
  destruct a; [ easy | ].
  destruct a; [ exfalso | now destruct a ].
  specialize (Hin 1 (or_introl eq_refl)); flia Hin.
}
now rewrite f_add_0_l, f_mul_0_l.
Qed.

Theorem ls_mul_1_l {F : field} : ∀ r, (ls_one * r = r)%LS.
Proof.
intros * i Hi.
destruct i; [ easy | clear Hi ].
cbn - [ ls_one ].
unfold log_prod_add at 1.
replace ls_one~{1} with f_one by easy.
rewrite f_mul_1_l, Nat.div_1_r.
rewrite <- f_add_0_l; f_equal.
apply fold_log_prod_1_l_from_2nd.
intros j Hj.
apply List.filter_In in Hj.
destruct Hj as (Hj, _).
now apply List.in_seq in Hj.
Qed.

(* playing with numbers represented multiplicativelly *)

(* mmm... ne garantit pas l'unicité d'un nombre ;
   par exemple, 6 a deux représentations
      (Times 2 eq_refl (Times 3 eq_refl One)
      (Times 3 eq_refl (Times 2 eq_refl One) ;
   on pourrait faire un type dépendant mais c'est la
   merde parce que deux nombres ne seraient pas du
   même type ; il va donc nous falloir une comparaison,
   une équivalence entre deux représentations ;
   par chance, on a une valeur canonique (premiers
   dans l'ordre croissant) *)
Inductive number :=
  | One : number
  | Times : ∀ p : nat, is_prime p = true → number → number.

Check (Times 2 eq_refl One).
Check (Times 3 eq_refl (Times 7 eq_refl One)).
Check (Times 5 eq_refl (Times 5 eq_refl One)).

Fixpoint nat_of_number n :=
  match n with
  | One => 1
  | Times p _ n' => p * nat_of_number n'
  end.

Compute (nat_of_number (Times 2 eq_refl One)).
Compute (nat_of_number (Times 3 eq_refl (Times 7 eq_refl One))).
Compute (nat_of_number (Times 5 eq_refl (Times 5 eq_refl One))).

Fixpoint fd_loop cnt n d :=
  match cnt with
  | 0 => 2
  | S cnt' =>
      if is_prime d then
        match n mod d with
        | 0 => d
        | _ => fd_loop cnt' n (d + 1)
        end
      else fd_loop cnt' n (d + 1)
  end.

Definition first_divisor_of_number n := fd_loop n n 2.

Compute (first_divisor_of_number 343).

Theorem fd_loop_is_prime :
  ∀ cnt n d, 2 ≤ d → is_prime (fd_loop cnt n d) = true.
Proof.
intros * Hd.
revert d Hd.
induction cnt; intros; [ easy | cbn ].
remember (is_prime d) as p eqn:Hp; symmetry in Hp.
destruct p. {
  remember (n mod d) as nd eqn:Hnd; symmetry in Hnd.
  destruct nd; [ easy | apply IHcnt ].
  transitivity d; [ easy | apply Nat.le_add_r ].
}
apply IHcnt.
transitivity d; [ easy | apply Nat.le_add_r ].
Qed.

Theorem first_divisor_is_prime :
  ∀ n, is_prime (first_divisor_of_number n) = true.
Proof.
intros.
now apply fd_loop_is_prime.
Qed.

Fixpoint non_loop cnt n :=
  match cnt with
  | 0 => One
  | S cnt' =>
      match n with
      | 0 | 1 => One
      | S (S n') =>
          let d := first_divisor_of_number n in
          let p := first_divisor_is_prime n in
          Times d p (non_loop cnt' (n / d))
      end
  end.

Definition number_of_nat n := non_loop n n.

Compute (number_of_nat 21).
Compute (number_of_nat 2).
Compute (number_of_nat 24).
Compute (number_of_nat 1001).

(* end play *)

(*
Theorem divisors_loop_rev_map : ∀ k n,
  k ≤ n
  → divisors_loop k (n - k + 1) n =
       List.rev
         (List.map (Nat.div n) (divisors_loop k (n - k + 1) n)).
Proof.
intros * Hkn.
revert n Hkn.
induction k; intros; [ easy | cbn ].
replace (n - S k + 1) with (n - k) by flia Hkn.
remember (n mod (n - k)) as m eqn:Hm; symmetry in Hm.
destruct m. {
  cbn.
  rewrite <- IHk; [ | flia Hkn ].
...
}
apply IHk.
...
*)

Theorem first_divisor : ∀ n, n ≠ 0 → List.hd 0 (divisors_of n) = 1.
Proof.
intros.
now destruct n.
Qed.

Theorem last_divisor : ∀ n, n ≠ 0 → List.last (divisors_of n) 0 = n.
Proof.
intros n Hn.
unfold divisors_of, divisors_from.
...

Theorem last_divisor : ∀ n, n ≠ 0 → List.hd 0 (List.rev (divisors_of n)) = n.
Proof.
intros * Hn.
Search last.
...
intros * Hn.
unfold divisors_of, divisors_from.
destruct n; [ easy | clear Hn ].
destruct n; [ easy | ].
cbn - [ "mod" ].
rewrite Nat.mod_1_r.
cbn - [ "mod" ].
...
intros * Hn.
destruct n; [ easy | clear Hn ].
induction n; [ easy | ].
cbn in IHn; cbn - [ "mod" ].
rewrite Nat.mod_1_r.
cbn - [ "mod" ].
...

Theorem tagada : ∀ n l,
  l = divisors_of n
  → List.hd 0 l = n / List.hd 0 (List.rev l).
Proof.
intros * Hl.
subst l.
destruct n; [ easy | ].
destruct n; [ easy | ].
cbn.
...

Theorem pouet : ∀ n,
  divisors_of n = List.rev (List.map (λ i, n / i) (divisors_of n)).
Proof.
intros.
remember (length (divisors_of n)) as len eqn:Hlen.
symmetry in Hlen.
revert n Hlen.
induction len; intros. {
  destruct n; [ easy | now destruct n ].
}
...

Compute (divisors_loop 24 1 24).
Compute (divisors_loop 22 2 24).
Compute (divisors_loop 11 2 24).
Compute (divisors_loop 9 3 24).
Compute (divisors_loop 6 3 24).
Compute (divisors_loop 4 4 24).
Compute (divisors_loop 3 4 24).
Compute (divisors_loop 1 5 24).
Compute (divisors_loop 60 1 60).
Compute (divisors_loop 58 2 60).
Compute (divisors_loop 29 2 60).
Compute (divisors_loop 29 3 60).

...
intros.
unfold divisors_of.
remember (divisors_of n) as l eqn:Hl.
revert n Hl.
induction l as [| a l]; intros. {
  destruct n; [ easy | now destruct n ].
}
destruct n; [ easy | ].
destruct n; [ easy | ].
cbn - [ "mod" ] in Hl.
rewrite Nat.mod_1_r in Hl.
replace (S (S n)) with (n + 1 * 2) in Hl at 1 by flia.
rewrite Nat.mod_add in Hl; [ | easy ].
remember Nat.modulo as f.
injection Hl; clear Hl; intros Hl Ha; subst f.
clear a Ha.
...
unfold divisors_of.
Print divisors_loop.
...
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
destruct n; [ easy | ].
...

Theorem glip {F : field} : ∀ u v n l,
  fold_right (log_prod_add u v n) f_zero l =
  fold_right (log_prod_add u v n) f_zero (List.rev l).
Proof.
intros.
revert n.
induction l as [| a l]; intros; [ easy | ].
cbn; rewrite IHl.
unfold log_prod_add at 1.
rewrite List.fold_right_app.
cbn.
...

Theorem glop {F : field} : ∀ u v n,
  fold_right (log_prod_add u v n) f_zero (divisors_of n) =
  fold_right (log_prod_add v u n) f_zero (List.rev (divisors_of n)).
Proof.
intros.
destruct n; [ easy | ].
Print log_prod_add.
...
destruct n. {
  cbn.
  unfold log_prod_add.
  now rewrite f_mul_comm.
}
destruct n. {
  cbn.
  unfold log_prod_add.
  now rewrite (f_mul_comm (v 1)), (f_mul_comm (v 2)).
}
destruct n. {
  cbn.
  unfold log_prod_add.
  now rewrite (f_mul_comm (v 1)), (f_mul_comm (v 3)).
}
destruct n. {
  cbn.
  unfold log_prod_add.
  now rewrite (f_mul_comm (v 1)), (f_mul_comm (v 2)), (f_mul_comm (v 4)).
}
destruct n. {
  cbn.
  unfold log_prod_add.
  now rewrite (f_mul_comm (v 1)), (f_mul_comm (v 5)).
}
destruct n. {
  cbn.
  unfold log_prod_add.
  rewrite (f_mul_comm (v 1)), (f_mul_comm (v 2)).
  rewrite (f_mul_comm (v 3)), (f_mul_comm (v 6)).
  easy.
}
...

Theorem fold_log_prod_comm {F : field} : ∀ u v i,
  fold_right (log_prod_add u v i) f_zero (divisors_of i) =
  fold_right (log_prod_add v u i) f_zero (divisors_of i).
Proof.
intros.
Search (fold_right _ _ (rev _)).
...
rewrite glop.
now rewrite glip.
...
destruct i; [ easy | cbn ].
unfold log_prod_add; cbn - [ "/" ].
rewrite Nat.div_1_r.
destruct i. {
  cbn; rewrite f_add_0_l, f_add_0_l.
  apply f_mul_comm.
}
destruct i. {
  cbn; do 2 rewrite f_add_0_l.
  rewrite (f_mul_comm (v 1)), (f_mul_comm (v 2)).
  apply f_add_comm.
}
destruct i. {
  cbn; do 2 rewrite f_add_0_l.
  rewrite (f_mul_comm (v 1)), (f_mul_comm (v 3)).
  apply f_add_comm.
}
destruct i. {
  cbn; do 2 rewrite f_add_0_l.
  rewrite (f_mul_comm (v 1)), (f_mul_comm (v 2)), (f_mul_comm (v 4)).
  rewrite f_add_comm, <- f_add_assoc; f_equal.
  apply f_add_comm.
}
destruct i. {
  cbn; do 2 rewrite f_add_0_l.
  rewrite (f_mul_comm (v 1)), (f_mul_comm (v 5)).
  apply f_add_comm.
}
destruct i. {
  cbn; do 2 rewrite f_add_0_l.
  rewrite (f_mul_comm (v 1)), (f_mul_comm (v 2)).
  rewrite (f_mul_comm (v 3)), (f_mul_comm (v 6)).
  rewrite f_add_comm.
  do 3 rewrite <- f_add_assoc; f_equal.
  rewrite f_add_comm, f_add_assoc; f_equal.
  apply f_add_comm.
}
...

Theorem log_prod_comm {F : field} : ∀ u v i,
  log_prod u v i = log_prod v u i.
Proof.
intros.
unfold log_prod.
...
apply fold_log_prod_comm.
...
intros.
apply fold_log_prod_list_comm.
unfold log_prod.
destruct i; [ easy | ].
...
rewrite log_prod_list_rev.
Search (fold_left _ (rev _) _).
Search (rev (fold_right _ _ _)).
...

Theorem log_prod_prod_swap {F : field} : ∀ u v w i,
  i ≠ 0
  → log_prod (log_prod u v) w i = log_prod (log_prod u w) v i.
Proof.
intros * Hi.
unfold log_prod.
...

Theorem log_prod_assoc {F : field} : ∀ u v w i,
  i ≠ 0
  → log_prod u (log_prod v w) i = log_prod (log_prod u v) w i.
Proof.
intros * Hi.
...
rewrite log_prod_comm.
rewrite log_prod_prod_swap; [ | easy ].
...

Theorem ls_mul_assoc {F : field} : ∀ x y z,
  (x * (y * z) = x * y * z)%LS.
Proof.
intros * i Hi.
cbn.
...

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
  2 ≤ n
  → ls (ls_of_pol (pol_pow 1 - pol_pow n)) 1 = f_one.
Proof.
intros * Hn; cbn.
destruct n; [ flia Hn | ].
destruct n; [ flia Hn | ].
destruct n; cbn; rewrite f_opp_0; apply f_add_0_r.
Qed.

Theorem pol_1_sub_pow_coeff_minus_1 {F : field} : ∀ n,
  2 ≤ n
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
  2 ≤ n
  → 2 ≤ i ∧ i ≠ n
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

Theorem pol_1_sub_pow_times_series_lemma_1 {F : field} : ∀ x n c m k u,
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

Theorem pol_1_sub_pow_times_series_lemma_2 {F : field} : ∀ m k x c n u,
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

(*
Here, we prove that
   (1 - 1/2^s) ζ(s)
is equal to
   ζ(s) without terms whose rank is divisible by 2
   (only odd ones are remaining)

But actually, our theorem is more general.
We prove, for any n and r, that
   (1 - 1/n^s) r(s)

where r is a series having the following property
   ∀ i, r(s)_{i} = r(s)_{n*i}

(the i-th coefficient of the series is equal to its (n*i)-th coefficient)

which is true for ζ since all its coefficients are 1.

The resulting series (1-1/n^s) ζ(s) has this property for all m
such as gcd(n,m)=1, allowing us at the next theorems to restart
with that series and another prime number. We can then iterate
for all prime numbers.

Note that we can then apply that whatever order of prime numbers
and even not prime numbers if we want, providing their gcd two by
two is 1.
*)

Theorem pol_1_sub_pow_times_series {F : field} : ∀ s n,
  2 ≤ n
  → (∀ i, i ≠ 0 → ls s i = ls s (n * i))
  → ((pol_pow 1 - pol_pow n) .* s = series_but_mul_of n s)%LS.
Proof.
intros * Hn Hs i Hi.
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
    apply (pol_1_sub_pow_times_series_lemma_1 _ n c m 0 (ls s)).
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
    eapply (pol_1_sub_pow_times_series_lemma_2 0).
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

Corollary pol_1_sub_pow_times_series_ζ {F : field} : ∀ n,
  2 ≤ n
  → ((pol_pow 1 - pol_pow n) .* ζ = series_but_mul_of n ζ)%LS.
Proof.
intros * Hn.
now apply pol_1_sub_pow_times_series.
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
   (n1, n2, n3, ... nm) such that gcd(ni,nj) = 1 for i≠j, what is true
   for a list of prime numbers.

2/ It is not the ζ function but any series r with logarithm powers such that
       ∀ i, r_{i} = r_{n*i}
   for any n in (n1, n2, n3 ... nm)
   what is true for ζ function since ∀ i ζ_{i}=1.
*)

Notation "'Π' ( a ∈ l ) , e" := (List.fold_right (λ a c, (e .* c)%LS) ls_one l)
  (at level 36, a at level 0, l at level 60, e at level 36) : ls_scope.

Theorem list_of_pow_1_sub_pol_times_series {F : field} : ∀ l r,
  (∀ a, List.In a l → 2 ≤ a)
  → (∀ a, a ∈ l → ∀ i, i ≠ 0 → r~{i} = r~{a*i})
  → (∀ na nb, na ≠ nb → Nat.gcd (List.nth na l 1) (List.nth nb l 1) = 1)
  → (Π (a ∈ l), (pol_pow 1 - pol_pow a) * r =
     fold_right series_but_mul_of r l)%LS.
Proof.
intros * Hge2 Hai Hgcd.
induction l as [| a1 l]. {
  intros i Hi.
  cbn - [ ".*" ls_mul ls_one ].
  now apply ls_mul_1_l.
}
cbn.
remember (Π (a ∈ l), (pol_pow 1 - pol_pow a))%LS as p eqn:Hp.
unfold ".*".
...
rewrite <- ls_mul_assoc.
rewrite IHl.
...

Theorem list_of_pow_1_sub_pol_times_series {F : field} : ∀ l r,
  (∀ a, List.In a l → 2 ≤ a)
  → (∀ a, a ∈ l → ∀ i, i ≠ 0 → r~{i} = r~{a*i})
  → (∀ na nb, na ≠ nb → Nat.gcd (List.nth na l 1) (List.nth nb l 1) = 1)
  → (List.fold_right (λ a c, ((pol_pow 1 - pol_pow a) .* c)) r l =
      List.fold_right series_but_mul_of r l)%LS.
Proof.
intros * Hge2 Hai Hgcd.
induction l as [| a1 l]; [ easy | cbn ].
rewrite IHl; cycle 1. {
  now intros; apply Hge2; right.
} {
  now intros a Ha'; apply Hai; right.
} {
  intros na nb Hnn.
  apply (Hgcd (S na) (S nb)); flia Hnn.
}
clear IHl.
apply pol_1_sub_pow_times_series; [ now apply Hge2; left | ].
intros i Hi.
destruct i; [ flia Hi | clear Hi ].
revert i.
induction l as [| a2 l]; intros. {
  apply Hai; [ now left | easy ].
}
cbn.
remember (S i mod a2) as m2 eqn:Hm2; symmetry in Hm2.
assert (Ha2 : a2 ≠ 0). {
  enough (H : 2 ≤ a2) by flia H.
  now apply Hge2; right; left.
}
rewrite <- Nat.mul_mod_idemp_r; [ | easy ].
rewrite Hm2.
destruct m2; [ now rewrite Nat.mul_0_r, Nat.mod_0_l | ].
remember ((a1 * S m2) mod a2) as m1 eqn:Hm1; symmetry in Hm1.
destruct m1. {
  apply Nat.mod_divide in Hm1; [ | easy ].
  apply Nat.gauss in Hm1; [ | now apply (Hgcd 1 0) ].
  destruct Hm1 as (m1, Hm1).
  destruct m1; [ easy | ].
  destruct a2; [ easy | ].
  rewrite <- Hm2 in Hm1.
  specialize (Nat.mod_upper_bound (S i) (S a2) Ha2) as H1.
  rewrite Hm1 in H1.
  cbn in H1; flia H1.
}
apply IHl. {
  intros a Ha; apply Hge2.
  destruct Ha as [Ha| Ha]; [ now left | now right; right ].
}  {
  intros a Ha j Hj.
  apply Hai; [ | easy ].
  destruct Ha as [Ha| Ha]; [ now left | now right; right ].
} {
  intros na nb Hnn.
  destruct na, nb; [ easy | | | ]. {
    now apply (Hgcd 0 (S (S nb))).
  } {
    now apply (Hgcd (S (S na)) 0).
  } {
    apply (Hgcd (S (S na)) (S (S nb))); flia Hnn.
  }
}
Qed.

(* just the case of multiplication with two polynomials  *)
Corollary two_pow_1_sub_pol_times_series {F : field} : ∀ s a b,
  2 ≤ a
  → 2 ≤ b
  → (∀ i, i ≠ 0 → ls s i = ls s (a * i))
  → (∀ i, i ≠ 0 → ls s i = ls s (b * i))
  → Nat.gcd a b = 1
  → ((pol_pow 1 - pol_pow b) .* (pol_pow 1 - pol_pow a) .* s =
      series_but_mul_of b (series_but_mul_of a s))%LS.
Proof.
intros * H2a H2b Ha Hb Gab.
apply (list_of_pow_1_sub_pol_times_series [b; a] s). {
  intros x [Hxa| [Hxb | ]]; [ now subst x | now subst x | easy ].
} {
  intros x [Hxa| [Hxb | ]]; [ now subst x | now subst x | easy ].
} {
  intros na nb Hab.
  destruct na. {
    destruct nb; [ easy | ].
    destruct nb; [ now rewrite Nat.gcd_comm | ].
    destruct nb; apply Nat.gcd_1_r.
  }
  destruct na. {
    destruct nb; [ easy | ].
    destruct nb; [ easy | ].
    destruct nb; apply Nat.gcd_1_r.
  }
  now destruct na.
}
Qed.

Theorem ζ_Euler_product_eq : ...
