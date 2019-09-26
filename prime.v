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

(* Euler product formula *)

(* https://en.wikipedia.org/wiki/Proof_of_the_Euler_product_formula_for_the_Riemann_zeta_function *)

(* representation of ζ function as series in x where x=1/e^s; we have
     Σ 1/n^s = Σ x^ln(n)
 *)

(* {| ls := u |} represents Σ (n=0,∞) u(n)/(n+1)^s = Σ (n=0,∞) u(n)x^ln(n+1) =
   Σ (n=0,∞) u(n)(x⊗(n+1)) where a⊗b=a^ln(b)=b^ln(a)=e^(ln(a)ln(b)) *)

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

Definition ls_eq {F : field} s1 s2 := ∀ n, ls s1 n = ls s2 n.
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

Definition series_but_mul_of {F : field} s d :=
  {| ls n :=
       match S n mod d with
       | 0 => f_zero
       | _ => ls s n
       end |}.

Definition ζ_but_mul_of {F : field} d :=
  {| ls n :=
       match S n mod d with
       | 0 => f_zero
       | _ => f_one
       end |}.

Definition log_prod_term {F : field} u v n i :=
  match S n mod S i with
  | 0 => (u i * v (S n / S i - 1)%nat)%F
  | _ => f_zero
  end.

Fixpoint log_prod {F : field} u v n i :=
  match i with
  | 0 => f_zero
  | S i' => (log_prod_term u v n (n - i') + log_prod u v n i')%F
  end.

(* Σ (i = 1, ∞) s1_(i-1) x^ln(i) + Σ (i = 1, ∞) s2_(i-1) x^ln(i) *)
Definition ls_add {F : field} s1 s2 :=
  {| ls n := (ls s1 n + ls s2 n)%F |}.

(* Σ (i = 1, ∞) s1_(i-1) x^ln(i) * Σ (i = 1, ∞) s2_(i-1) x^ln(i) *)
Definition ls_mul {F : field} s1 s2 :=
  {| ls n := log_prod (ls s1) (ls s2) n (S n) |}.

Definition ls_of_pol {F : field} p :=
  {| ls n := List.nth n (lp p) f_zero |}.

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
    (log_prod_term u v n (n - i) + log_prod u v n i)%F.
Proof. easy. Qed.

(* c*x^ln(n+1) * Σ (i = 1, ∞) s_(i-1) x^ln(i) =
   Σ (i = 1, ∞) c*s_(i-1) x^ln((n+1)*i) *)
Definition ls_mul_elem {F : field} c n s :=
  {| ls i :=
       match S i mod S n with
       | 0 => (c * ls s (S i / S n - 1))%F
       | _ => f_zero
       end |}.

(* multiplication of the first k elements of a series
   (i.e. a polynomial formed by its first k elements)
   to a series
    Σ (i = 1, k) s1_(i-1) x^ln(i) * Σ (i = 1, ∞) s2_(i-1) x^ln(i) *)
Fixpoint ls_mul_l_upto {F : field} k s1 s2 :=
  match k with
  | 0 => {| ls _ := f_zero |}
  | S k' => ls_add (ls_mul_l_upto k' s1 s2) (ls_mul_elem (ls s1 k') k' s2)
  end.

Theorem log_prod_0_l {F : field} : ∀ u v n i,
  (∀ n, u n = f_zero) → log_prod u v n i = f_zero.
Proof.
intros * Hu.
revert n.
induction i; intros; [ easy | ].
rewrite log_prod_succ.
cbn - [ Nat.div Nat.modulo ].
rewrite IHi, f_add_0_r.
unfold log_prod_term.
remember (S n mod S (n - i)) as r eqn:Hr; symmetry in Hr.
destruct r; [ | easy ].
now rewrite Hu, f_mul_0_l.
Qed.

Theorem ls_mul_0_l {F : field} : ∀ s1 s2,
  (∀ n, ls s1 n = f_zero) → ls_eq (ls_mul s1 s2) {| ls _ := f_zero |}.
Proof.
intros * Hs1 i.
cbn - [ "/" "mod" ].
unfold log_prod_term.
rewrite Nat.sub_diag, Nat.div_1_r, Nat.sub_succ, Nat.sub_0_r.
rewrite Nat.mod_1_r.
rewrite Hs1, f_mul_0_l, f_add_0_l.
now apply log_prod_0_l.
Qed.

Theorem ls_mul_l_upto_succ {F : field} : ∀ k s1 s2,
  ls_mul_l_upto (S k) s1 s2 =
    ls_add (ls_mul_l_upto k s1 s2) (ls_mul_elem (ls s1 k) k s2).
Proof. easy. Qed.

Theorem ls_mul_l_upto_of_0 {F : field} : ∀ k s1 s2,
  ls (ls_mul_l_upto k s1 s2) 0 =
    match k with
    | 0 => f_zero
    | S k => (ls s1 0 * ls s2 0)%F
    end.
Proof.
intros.
destruct k; [ easy | ].
induction k; [ cbn; now rewrite f_add_0_l | ].
remember (S k) as x; cbn; subst x.
unfold snd.
replace (S k - k) with 1 by flia.
now rewrite f_add_0_r.
Qed.

Theorem ls_mul_l_upto_of_succ {F : field} : ∀ k s1 s2 i,
  ls (ls_mul_l_upto k s1 s2) (S i) =
  match k with
  | 0 => f_zero
  | S k' =>
      (ls (ls_mul_l_upto k' s1 s2) (S i) +
       match S (S i) mod k with
       | 0 => ls s1 k' * ls s2 (S (S i) / k - 1)
       | S _ => f_zero
       end)%F
  end.
Proof. intros; now destruct k. Qed.

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
  log_prod (ls (ls_of_pol (x + y))) (ls s) n i =
  (log_prod (ls (ls_of_pol y)) (ls s) n i +
   log_prod (ls (ls_of_pol x)) (ls s) n i)%F.
Proof.
intros.
revert n.
induction i; intros; [ now cbn; rewrite f_add_0_r | ].
do 3 rewrite log_prod_succ.
cbn - [ "/" "mod" ls_of_pol ].
unfold log_prod_term.
remember (S n mod S (n - i)) as m eqn:Hm; symmetry in Hm.
destruct m. {
  apply Nat.mod_divides in Hm; [ | easy ].
  destruct Hm as (m, Hm).
  rewrite Hm, Nat.mul_comm, Nat.div_mul; [ | easy ].
  rewrite IHi, ls_of_pol_add.
  cbn - [ ls_of_pol ].
  rewrite f_mul_add_distr_r.
  do 2 rewrite <- f_add_assoc.
  rewrite f_add_comm.
  do 2 rewrite <- f_add_assoc; f_equal; f_equal.
  apply f_add_comm.
}
do 3 rewrite f_add_0_l.
apply IHi.
Qed.

Theorem ls_mul_pol_add_distr_r {F : field} : ∀ x y s,
  ((x + y) .* s = x .* s + y .* s)%LS.
Proof.
intros * i.
cbn - [ "/" "mod" ls_of_pol ].
unfold log_prod_term.
rewrite Nat.sub_diag, Nat.div_1_r, Nat.mod_1_r.
rewrite Nat_sub_succ_1.
rewrite ls_of_pol_add.
cbn - [ ls_of_pol ].
rewrite f_mul_add_distr_r.
do 2 rewrite <- f_add_assoc; f_equal.
symmetry.
rewrite f_add_comm, <- f_add_assoc; f_equal.
symmetry.
apply log_prod_pol_add.
Qed.

Theorem log_prod_pol_1_l {F : field} : ∀ s k n i,
  k < 2
  → i ≤ n
  → log_prod (ls (ls_of_pol (pol_pow k))) (ls s) n i = f_zero.
Proof.
intros * Hk Hin.
revert n Hin.
induction i; intros; [ easy | ].
rewrite log_prod_succ.
unfold ls_of_pol at 1.
unfold log_prod_term.
remember (S n mod S (n - i)) as m eqn:Hm.
cbn - [ "/" ls_of_pol ].
replace (k - 1) with 0 by flia Hk.
cbn - [ "/" ls_of_pol ].
replace (n - i) with (S (n - S i)) by flia Hin.
replace (match n - S i with 0 | _ => f_zero end) with f_zero. 2: {
  now destruct (n - S i).
}
rewrite f_mul_0_l.
replace (match m with 0 | _ => f_zero end) with f_zero by now destruct m.
rewrite f_add_0_l.
apply IHi; flia Hin.
Qed.

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
remember (S n mod S (n - i)) as m eqn:Hm; symmetry in Hm.
rewrite IHi; [ | flia Hin ].
rewrite f_add_0_r.
destruct m; [ | easy ].
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
apply f_mul_0_l.
Qed.

Theorem ls_mul_pol_1_l {F : field} : ∀ s,
  (pol_pow 1 .* s = s)%LS.
Proof.
intros * i.
cbn - [ "/" "mod" ls_of_pol ].
unfold log_prod_term.
rewrite Nat.sub_diag, Nat.div_1_r, Nat.mod_1_r, Nat_sub_succ_1.
unfold ls_of_pol at 1.
cbn - [ ls_of_pol ].
rewrite f_mul_1_l, <- f_add_0_r; f_equal.
apply log_prod_pol_1_l; [ flia | easy ].
Qed.

Theorem ls_of_pol_opp {F : field} : ∀ p,
  (ls_of_pol (- p) = - ls_of_pol p)%LS.
Proof.
intros * i; cbn.
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
rewrite ls_of_pol_opp.
cbn - [ "/" "mod" ls_of_pol ].
destruct (S n mod S (n - i)) as [Hn| Hn]. {
  now rewrite f_opp_add_distr, f_mul_opp_l, IHi.
}
do 2 rewrite f_add_0_l.
apply IHi.
Qed.

Theorem log_prod_term_0 {F : field} : ∀ u v n,
  log_prod_term u v n 0 = (u 0 * v n)%F.
Proof.
intros.
cbn - [ "/" ].
now rewrite Nat.div_1_r, Nat_sub_succ_1.
Qed.

Theorem ls_mul_pol_opp_l {F : field} : ∀ p s,
  (- p .* s = - (p .* s))%LS.
Proof.
intros * i.
cbn - [ "/" "mod" ls_of_pol ].
unfold log_prod_term.
rewrite Nat.sub_diag, Nat.mod_1_r.
rewrite ls_of_pol_opp.
cbn - [ "/" "mod" ls_of_pol ].
rewrite log_prod_pol_opp_l.
rewrite f_opp_add_distr.
now rewrite f_mul_opp_l.
Qed.

Theorem pol_pow_1_mul_l {F : field} : ∀ s n i,
  i ≤ n
  → log_prod (ls (ls_of_pol (pol_pow 1))) (ls s) n i = f_zero.
Proof.
intros * Hin.
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
rewrite f_mul_0_l.
replace (match _ with 0 | _ => _ end) with f_zero by
  now destruct (S n mod S (n - i)).
rewrite f_add_0_l.
apply IHi; flia Hin.
Qed.

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
destruct m. {
  unfold ".*", "*"%LS.
  cbn - [ log_prod ls_of_pol pol_pow "/" ].
  rewrite log_prod_succ, Nat.sub_diag.
  unfold log_prod_term.
  rewrite Nat.mod_1_r, Nat.div_1_r, Nat_sub_succ_1.
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
...

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

Theorem step_1 {F : field} : ∀ s n,
  (∀ i, ls s i = ls s (n * S i - 1))
  → (series_but_mul_of s n = (pol_pow 1 - pol_pow n) .* s)%LS.
Proof.
intros * Hs i.
unfold lp_sub.
rewrite ls_mul_pol_add_distr_r, ls_ls_add.
rewrite ls_mul_pol_1_l.
rewrite ls_mul_pol_opp_l.
cbn - [ series_but_mul_of log_prod ls_of_pol ".*" ].
rewrite fold_f_sub.
unfold series_but_mul_of.
cbn - [ pol_pow ".*" ].
symmetry.
remember (S i mod n) as m eqn:Hm; symmetry in Hm.
destruct m. {
  destruct (lt_dec n 2) as [Hn| Hn]. {
    unfold ".*", "*"%LS.
    cbn - [ "/" "mod" ls_of_pol pol_pow ].
    unfold log_prod_term.
    rewrite Nat.sub_diag, Nat.mod_1_r, Nat.div_1_r, Nat_sub_succ_1.
    unfold ls_of_pol at 1, pol_pow at 1.
    cbn - [ "/" "mod" ls_of_pol pol_pow ].
    unfold f_sub.
    rewrite f_opp_add_distr, f_add_assoc.
    replace (n - 1) with 0 by flia Hn.
    rewrite log_prod_pol_1_l; [ cbn | easy | easy ].
    now rewrite f_mul_1_l, f_add_opp_diag_r, f_add_opp_diag_r.
  }
  apply Nat.nlt_ge in Hn.
  enough (H : ls (pol_pow n .* s) i = ls s i). {
    rewrite H; apply f_sub_diag.
  }
(**)
  destruct n; [ flia Hn | ].
  destruct n; [ flia Hn | clear Hn ].
  apply Nat.mod_divides in Hm; [ | easy ].
  destruct Hm as (m, Hm).
  assert (H : i + 1 = m * (n + 2)) by flia Hm.
  clear Hm; rename H into Hm.
  replace (S (S n)) with (n + 2) in Hs |-* by flia.
  specialize (Hs (m - 1)) as H1.
  replace (S (m - 1)) with m in H1. 2: {
    destruct m; [ flia Hm | flia ].
  }
  rewrite Nat.mul_comm, <- Hm in H1.
  rewrite Nat.add_sub in H1.
  rewrite <- H1; clear H1.
  destruct i; [ destruct m; cbn in Hm; flia Hm | ].
  replace (S i) with (m * (n + 2) - 1) by flia Hm.
  destruct m; [ flia Hm | ].
  rewrite Nat_sub_succ_1.
  clear i Hm Hs.
  replace (S m) with (m + 1) by flia.
  rename m into i.
  destruct n. {
    unfold ".*", "*"%LS.
    cbn - [ log_prod ls_of_pol pol_pow ].
    rewrite log_prod_succ.
    unfold log_prod_term.
    rewrite Nat.sub_diag, Nat.mod_1_r, Nat.div_1_r.
    replace ((i + 1) * 2 - 1) with (S (2 * i)) by flia.
    rewrite log_prod_succ, Nat_sub_succ_diag_l.
    rewrite log_prod_pol_pow; [ | flia | flia ].
    rewrite f_add_0_r.
    cbn - [ "/" "mod" "+" "*" ].
    unfold log_prod_term.
    rewrite f_mul_0_l, f_add_0_l, f_mul_1_l.
    replace (S (S (2 * i))) with ((i + 1) * 2) by flia.
    rewrite Nat.mod_mul; [ | easy ].
    rewrite Nat.div_mul; [ | easy ].
    now rewrite Nat.add_sub.
  }
  replace (S n + 2) with (n + 3) by flia.
  destruct n. {
    unfold ".*", "*"%LS.
    cbn - [ log_prod ls_of_pol pol_pow ].
    rewrite log_prod_succ.
    unfold log_prod_term.
    rewrite Nat.sub_diag, Nat.mod_1_r, Nat.div_1_r.
    replace ((i + 1) * 3 - 1) with (S (3 * i + 1)) by flia.
    rewrite Nat_sub_succ_1, log_prod_succ, Nat_sub_succ_diag_l.
    unfold log_prod_term.
    replace (ls (ls_of_pol (pol_pow 3)) 0) with f_zero by easy.
    replace (ls (ls_of_pol (pol_pow 3)) 1) with f_zero by easy.
    do 2 rewrite f_mul_0_l; rewrite f_add_0_l.
    replace (match _ with 0 | _ => f_zero end) with f_zero. 2: {
      now destruct (S (S (3 * i + 1)) mod 2).
    }
    rewrite f_add_0_l.
    replace (3 * i + 1) with (S (3 * i)) by flia.
    rewrite log_prod_succ.
    unfold log_prod_term.
    rewrite log_prod_pol_pow; [ | flia | flia ].
    rewrite f_add_0_r.
    replace (S (S (S (3 * i)) - 3 * i)) with 3 by flia.
    replace (S (S (S (3 * i)))) with ((i + 1) * 3) by flia.
    rewrite Nat.mod_mul; [ | easy ].
    rewrite Nat.div_mul; [ | easy ].
    rewrite Nat.add_sub.
    replace (S (S (3 * i)) - 3 * i) with 2 by flia.
    replace (ls (ls_of_pol (pol_pow 3)) 2) with f_one by easy.
    now rewrite f_mul_1_l.
  }
  replace (S n + 3) with (n + 4) by flia.
  destruct n. {
    unfold ".*", "*"%LS.
    cbn - [ log_prod ls_of_pol pol_pow ].
    rewrite log_prod_succ.
    unfold log_prod_term.
    rewrite Nat.sub_diag, Nat.mod_1_r, Nat.div_1_r.
    replace ((i + 1) * 4 - 1) with (S (4 * i + 2)) by flia.
    rewrite Nat_sub_succ_1, log_prod_succ, Nat_sub_succ_diag_l.
    unfold log_prod_term.
    replace (ls (ls_of_pol (pol_pow 4)) 0) with f_zero by easy.
    replace (ls (ls_of_pol (pol_pow 4)) 1) with f_zero by easy.
    do 2 rewrite f_mul_0_l; rewrite f_add_0_l.
    replace (match _ with 0 | _ => f_zero end) with f_zero. 2: {
      now destruct (S (S (4 * i + 2)) mod 2).
    }
    rewrite f_add_0_l.
    replace (4 * i + 2) with (S (4 * i + 1)) by flia.
    rewrite log_prod_succ.
    unfold log_prod_term.
    remember (4 * i + 1) as x.
    replace (S (S x) - x) with 2 by flia.
    replace (S (S (S x))) with (i + 1 + (i + 1) * 3) by flia Heqx.
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.add_assoc, Nat.add_sub.
    replace (S (S x)) with (4 * i + 3) by flia Heqx.
    subst x.
    replace (ls (ls_of_pol (pol_pow 4)) 2) with f_zero by easy.
    rewrite f_mul_0_l.
    replace (match _ with 0 | _ => f_zero end) with f_zero. 2: {
      now destruct ((i + 1) mod 3).
    }
    rewrite f_add_0_l.
    rewrite Nat.add_1_r.
    rewrite log_prod_succ.
    rewrite Nat.add_sub_swap; [ | easy ].
    rewrite Nat.sub_diag, Nat.add_0_l.
    unfold log_prod_term.
    replace (S (4 * i + 3)) with (0 + (i + 1) * 4) by flia.
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.add_assoc, Nat.add_sub.
    rewrite Nat.mod_0_l; [ | easy ].
    rewrite Nat.div_0_l; [ | easy ].
    rewrite Nat.add_0_l.
    replace (ls _ 3) with f_one by easy.
    rewrite f_mul_1_l.
    rewrite <- f_add_0_r; f_equal.
    apply log_prod_pol_pow; flia.
  }
  replace (S n + 4) with (n + 5) by flia.
  destruct n. {
    unfold ".*", "*"%LS.
    cbn - [ log_prod ls_of_pol pol_pow ].
    rewrite log_prod_succ.
    unfold log_prod_term.
    rewrite Nat.sub_diag, Nat.mod_1_r, Nat.div_1_r.
    replace ((i + 1) * 5 - 1) with (S (5 * i + 3)) by flia.
    rewrite Nat_sub_succ_1, log_prod_succ, Nat_sub_succ_diag_l.
    unfold log_prod_term.
    replace (ls (ls_of_pol (pol_pow 5)) 0) with f_zero by easy.
    replace (ls (ls_of_pol (pol_pow 5)) 1) with f_zero by easy.
    do 2 rewrite f_mul_0_l; rewrite f_add_0_l.
    replace (match _ with 0 | _ => f_zero end) with f_zero. 2: {
      now destruct (S (S (5 * i + 3)) mod 2).
    }
    rewrite f_add_0_l.
    replace (5 * i + 3) with (S (5 * i + 2)) by flia.
    rewrite log_prod_succ.
    unfold log_prod_term.
    remember (5 * i + 2) as x.
    replace (S (S x) - x) with 2 by flia.
    replace (S (S (S x))) with (2 * i + 2 + (i + 1) * 3) by flia Heqx.
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.add_assoc, Nat.add_sub.
    replace (S (S x)) with (5 * i + 4) by flia Heqx.
    subst x.
    replace (ls (ls_of_pol (pol_pow 5)) 2) with f_zero by easy.
    rewrite f_mul_0_l.
    replace (match _ with 0 | _ => f_zero end) with f_zero. 2: {
      now destruct ((2 * i + 2) mod 3).
    }
    rewrite f_add_0_l.
    replace (5 * i + 2) with (S (5 * i + 1)) by flia.
    rewrite log_prod_succ.
    rewrite Nat.sub_add_distr.
    rewrite Nat.add_sub_swap; [ | easy ].
    rewrite Nat.sub_diag, Nat.add_0_l.
    replace (4 - 1) with 3 by easy.
    unfold log_prod_term.
    replace (S (5 * i + 4)) with ((i + 1) + (i + 1) * 4) by flia.
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.add_assoc, Nat.add_sub.
    replace (ls (ls_of_pol (pol_pow 5)) 3) with f_zero by easy.
    rewrite f_mul_0_l.
    replace (match _ with 0 | _ => f_zero end) with f_zero. 2: {
      now destruct (_ mod _).
    }
    rewrite f_add_0_l.
    replace (5 * i + 1) with (S (5 * i)) by flia.
    rewrite log_prod_succ.
    rewrite Nat.add_sub_swap; [ | easy ].
    rewrite Nat.sub_diag, Nat.add_0_l.
    unfold log_prod_term.
    replace (S (5 * i + 4)) with ((i + 1) * 5) by flia.
    rewrite Nat.mod_mul; [ | easy ].
    rewrite Nat.div_mul; [ | easy ].
    rewrite Nat.add_sub.
    replace (ls (ls_of_pol (pol_pow 5)) 4) with f_one by easy.
    rewrite f_mul_1_l.
    rewrite <- f_add_0_r; f_equal.
    apply log_prod_pol_pow; flia.
  }
  replace (S n + 5) with (n + 6) by flia.
...
intros * Hs i.
unfold ".*".
remember (ls_of_pol (pol_pow 1 - pol_pow n)%LP) as p eqn:Hp.
destruct (lt_dec n 2) as [Hn| Hn]. {
  cbn - [ "/" "mod" ].
  rewrite Nat.sub_diag, Nat.div_1_r, Nat_sub_succ_1, Nat.mod_1_r.
  cbn; symmetry; cbn in Hs.
  rewrite (Hs i).
  unfold pol_pow in Hp; cbn in Hp.
  replace (n - 1) with 0 in Hp by flia Hn.
  unfold lp_sub, lp_add, lp_opp in Hp; cbn in Hp.
  rewrite f_add_opp_diag_r in Hp.
  remember (log_prod (ls p)) as x.
  rewrite Hp; cbn - [ "/" "mod" ]; subst x.
  do 2 rewrite f_mul_0_l.
  rewrite f_add_0_l.
  destruct (Nat.eq_dec i 0) as [Hi| Hi]. {
    rewrite f_add_0_l; subst i; cbn.
    destruct n; [ easy | ].
    destruct n; [ easy | ].
    rewrite Nat.mod_1_l; [ flia Hn | flia ].
  }
  destruct i; [ flia Hi | ].
  replace (match i with 0 | _ => f_zero end) with f_zero by now destruct i.
  rewrite f_mul_0_l, f_add_0_l.
  destruct n. {
    cbn - [ log_prod ].
    apply log_prod_0_l; intros m; subst p; cbn.
    destruct m; [ easy | now destruct m ].
  }
  destruct n. {
    rewrite Nat.mod_1_r.
    apply log_prod_0_l; intros m; subst p; cbn.
    destruct m; [ easy | now destruct m ].
  }
  flia Hn.
}
apply Nat.nlt_ge in Hn; symmetry.
cbn - [ log_prod ].
remember (S i mod n) as m eqn:Hm; symmetry in Hm.
destruct m. {
  rewrite log_prod_succ.
  rewrite Nat.sub_diag.
  cbn - [ "/" "mod" ].
  rewrite Nat.mod_1_r, Nat.div_1_r, Nat_sub_succ_1.
  destruct (Nat.eq_dec i 0) as [Hi| Hi]. {
    destruct n; [ flia Hn | ].
    destruct n; [ flia Hn | ].
    rewrite Nat.mod_small in Hm; [ easy | subst i; flia ].
  }
(*
  ============================
  (ls p 0 * ls s i + ls p i * ls s 0 + log_prod (ls p) (ls s) i i)%F = f_zero
*)
  destruct i; [ easy | clear Hi ].
  rewrite log_prod_succ.
  rewrite Nat_sub_succ_diag_l.
  cbn - [ "/" "mod" ].
  replace (S (S i)) with (i + 1 * 2) by flia.
  rewrite Nat.div_add; [ | easy ].
  rewrite Nat.mod_add; [ | easy ].
  rewrite Nat.add_sub.
  destruct (lt_dec (i / 2) 1) as [Hi| Hi]. {
    rewrite f_add_0_r.
    destruct n; [ flia Hn | ].
    destruct n; [ flia Hn | ].
    destruct i. {
      destruct n. {
        rewrite (Hs 0); cbn.
        rewrite Hp; cbn.
        rewrite f_opp_0, f_add_0_r, f_mul_1_l, f_add_0_l.
        now rewrite f_mul_opp_l, f_mul_1_l, f_add_opp_diag_r.
      }
      rewrite Nat.mod_small in Hm; [ easy | flia ].
    }
    destruct i. {
      destruct n; [ easy | ].
      rewrite Hp; cbn.
      rewrite f_opp_0, f_add_0_r, f_mul_1_l.
      destruct n. {
        rewrite (Hs 0); cbn.
        now rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l, f_add_opp_diag_r.
      }
      rewrite Nat.mod_small in Hm; [ easy | flia ].
    }
    replace (S (S i)) with (i + 1 * 2) in Hi by flia.
    rewrite Nat.div_add in Hi; [ flia Hi | easy ].
  }
  assert (H : 2 ≤ i). {
    destruct i; [ cbn in Hi; flia Hi | ].
    destruct i; [ cbn in Hi; flia Hi | flia ].
  }
  clear Hi; rename H into Hi; move Hi before Hn.
  remember (i mod 2) as q eqn:Hq; symmetry in Hq.
  destruct q. {
    apply Nat.mod_divides in Hq; [ | easy ].
    destruct Hq as (q, Hq).
    rewrite Hq, Nat.mul_comm, Nat.div_mul; [ | easy ].
    rewrite Nat.mul_comm, <- Hq.
    destruct (Nat.eq_dec q 1) as [Hq1| Hq1]. {
      subst q; cbn in Hq; subst i; clear Hi.
      cbn; rewrite f_add_0_r.
      subst p; cbn.
      destruct n; [ flia Hn | ].
      destruct n; [ flia Hn | clear Hn; cbn ].
      destruct n. {
        rewrite (Hs 1); cbn.
        cbn; rewrite f_opp_0, f_add_0_r, f_mul_1_l.
        rewrite f_mul_0_l, f_add_0_r, f_add_0_l.
        rewrite f_mul_opp_l, f_mul_1_l.
        apply f_add_opp_diag_r.
      }
      cbn; rewrite f_opp_0, f_add_0_r, f_mul_1_l.
      destruct n; [ easy | ].
      destruct n. {
        rewrite (Hs 0); cbn.
        rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l.
        rewrite f_add_0_l, f_mul_0_l, f_add_0_r.
        apply f_add_opp_diag_r.
      }
      rewrite Nat.mod_small in Hm; [ easy | flia ].
    }
(*
  ============================
  (ls p 0 * ls s (S i) + ls p (S i) * ls s 0 +
   (ls p 1 * ls s q + ls p q * ls s 1 + log_prod (ls p) (ls s) (S i) i))%F =
  f_zero
*)
    destruct i; [ flia Hi | ].
    rewrite log_prod_succ.
    replace (S (S i) - i) with 2 by flia.
    cbn - [ "/" "mod" ].
    replace (S (S (S i))) with (i + 1 * 3) by flia.
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.add_sub.
    destruct (lt_dec (i / 3) 2) as [Hi3| Hi3]. {
      rewrite f_add_0_r.
      destruct i; [ flia Hi | clear Hi ].
      destruct i; [ flia Hq Hq1 | ].
      destruct i; [ flia Hq | ].
      destruct q; [ flia Hq | ].
      destruct q; [ flia Hq | clear Hq1 ].
      destruct i. {
        assert (H : q = 0) by flia Hq.
        subst q p; cbn; clear Hq Hi3.
        destruct n; [ flia Hn | ].
        destruct n; [ flia Hn | clear Hn ].
        destruct n. {
          rewrite (Hs 2); cbn.
          rewrite f_opp_0, f_add_0_r, f_mul_1_l.
          rewrite f_mul_0_l, f_add_0_r.
          rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l.
          rewrite f_mul_0_l, f_add_0_r.
          apply f_add_opp_diag_r.
        }
        destruct n. {
          rewrite (Hs 1); cbn.
          rewrite f_opp_0, f_add_0_r, f_mul_1_l.
          rewrite f_mul_0_l, f_add_0_r.
          rewrite f_add_0_l, f_mul_0_l, f_add_0_l.
          rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l.
          apply f_add_opp_diag_r.
        }
        destruct n; [ easy | ].
        destruct n; [ easy | ].
        destruct n. {
          rewrite (Hs 0); cbn.
          rewrite f_opp_0, f_add_0_r, f_mul_1_l.
          rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l.
          rewrite f_add_0_l, f_mul_0_l, f_add_0_l.
          rewrite f_mul_0_l, f_add_0_r.
          apply f_add_opp_diag_r.
        }
        rewrite Nat.mod_small in Hm; [ easy | flia ].
      }
      destruct i; [ flia Hq | ].
      destruct i. {
        assert (H : q = 1) by flia Hq.
        subst q; clear Hq Hi3.
        destruct n; [ flia Hn | ].
        destruct n; [ flia Hn | clear Hn ].
        destruct n. {
          subst p; cbn.
          rewrite f_opp_0, f_add_0_r, f_mul_1_l.
          rewrite f_mul_0_l, f_add_0_r.
          rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l.
          rewrite f_mul_0_l, f_add_0_r.
          rewrite (Hs 3); cbn.
          apply f_add_opp_diag_r.
        }
        destruct n; [ easy | ].
        destruct n. {
          subst p; cbn.
          rewrite f_opp_0, f_add_0_r, f_mul_1_l.
          rewrite f_mul_0_l, f_add_0_r.
          rewrite f_add_0_l, f_mul_0_l, f_add_0_l.
          rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l.
          rewrite (Hs 1); cbn.
          apply f_add_opp_diag_r.
        }
        destruct n; [ easy | ].
        destruct n; [ easy | ].
        destruct n; [ easy | ].
        destruct n. {
          subst p; cbn.
          rewrite f_opp_0, f_add_0_r, f_mul_1_l.
          rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l.
          rewrite f_add_0_l, f_mul_0_l, f_add_0_l.
          rewrite f_mul_0_l, f_add_0_r.
          rewrite (Hs 0); cbn.
          apply f_add_opp_diag_r.
        }
        rewrite Nat.mod_small in Hm; [ easy | flia ].
      }
      ring_simplify in Hi3.
      replace (6 + i) with (i + 2 * 3) in Hi3 by flia.
      rewrite Nat.div_add in Hi3; [ flia Hi3 | easy ].
    }
    apply Nat.nlt_ge in Hi3.
    assert (H : 6 ≤ i). {
      destruct i; [ flia Hi | ].
      destruct i; [ cbn in Hi3; flia Hi3 | ].
      destruct i; [ cbn in Hi3; flia Hi3 | ].
      destruct i; [ cbn in Hi3; flia Hi3 | ].
      destruct i; [ cbn in Hi3; flia Hi3 | ].
      destruct i; [ cbn in Hi3; flia Hi3 | flia ].
    }
    move H before Hi; clear Hi; rename H into Hi; clear Hi3.
    remember (i mod 3) as r eqn:Hr; symmetry in Hr.
    destruct r. {
      apply Nat.mod_divides in Hr; [ | easy ].
      destruct Hr as (r, Hr).
      rewrite Hr, Nat.mul_comm, Nat.div_mul; [ | easy ].
      rewrite Nat.mul_comm, <- Hr.
      destruct (Nat.eq_dec r 2) as [Hr2| Hr2]. {
        subst r; cbn in Hr; subst i; flia Hq.
      }
(*
  ============================
  (ls p 0 * ls s (S (S i)) + ls p (S (S i)) * ls s 0 +
   (ls p 1 * ls s q + ls p q * ls s 1 +
    (ls p 2 * ls s r + ls p r * ls s 2 + log_prod (ls p) (ls s) (S (S i)) i)))%F =
  f_zero
*)
(* is next step with 4 (next natural) or with 5 (next prime)?
   I guess it is 5 but not sure;
   anyway it is complicated *)
...
(*
  (ls p 0 * ls s (i + k) + ls p (i + k) * ls s 0 + ...
   log_prod (ls p) (ls s) (i + k) i)%F = f_zero

*)

(*
  ============================
  (ls p 0 * ls s i + ls p i * ls s 0 + log_prod (ls p) (ls s) i i)%F = f_zero
*)
(*
  ============================
  (ls p 0 * ls s (S i) + ls p (S i) * ls s 0 +
   (ls p 1 * ls s q + ls p q * ls s 1 + log_prod (ls p) (ls s) (S i) i))%F =
  f_zero
*)
(*
  ============================
  (ls p 0 * ls s (S (S i)) + ls p (S (S i)) * ls s 0 +
   (ls p 1 * ls s q + ls p q * ls s 1 +
    (ls p 2 * ls s r + ls p r * ls s 2 + log_prod (ls p) (ls s) (S (S i)) i)))%F =
  f_zero
*)
...
unfold ls_mul; symmetry.
cbn - [ log_prod ].
rewrite log_prod_succ.
rewrite Nat.sub_diag.
cbn - [ "/" "mod" ].
rewrite Nat.div_1_r, Nat.mod_1_r, Nat_sub_succ_1.
destruct (Nat.eq_dec i 0) as [Hi| Hi]. {
  subst i.
  rewrite Nat.mod_1_l; [ cbn | easy ].
  rewrite f_add_0_r.
  replace (ls p 0) with f_one. 2: {
    subst p; cbn.
    destruct n; [ easy | ].
    destruct n; [ flia Hn | cbn ].
    destruct n; now cbn; rewrite f_opp_0, f_add_0_r.
  }
  apply f_mul_1_l.
}
destruct i; [ easy | clear Hi ].
replace (ls p 0) with f_one. 2: {
  subst p; cbn.
  destruct n; [ flia Hn | ].
  destruct n; [ flia Hn | cbn ].
  now destruct n; cbn; rewrite f_opp_0, f_add_0_r.
}
rewrite f_mul_1_l.
remember (S (S i) mod n) as m eqn:Hm; symmetry in Hm.
destruct m. {
  rewrite log_prod_succ.
  rewrite Nat_sub_succ_diag_l.
  cbn - [ "/" "mod" ].
  replace (S (S i)) with (i + 1 * 2) by flia.
  rewrite Nat.div_add; [ | easy ].
  rewrite Nat.mod_add; [ | easy ].
  rewrite Nat.add_sub.
  destruct (lt_dec (i / 2) 1) as [Hi| Hi]. {
    rewrite f_add_0_r.
    destruct n; [ flia Hn | ].
    destruct n; [ flia Hn | ].
    destruct i. {
      destruct n. {
        rewrite (Hs 0); cbn.
        rewrite Hp; cbn.
        now rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l, f_add_opp_diag_r.
      }
      rewrite Nat.mod_small in Hm; [ easy | flia ].
    }
    destruct i. {
      destruct n; [ easy | ].
      rewrite Hp; cbn.
      destruct n. {
        rewrite (Hs 0); cbn.
        now rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l, f_add_opp_diag_r.
      }
      rewrite Nat.mod_small in Hm; [ easy | flia ].
    }
    replace (S (S i)) with (i + 1 * 2) in Hi by flia.
    rewrite Nat.div_add in Hi; [ flia Hi | easy ].
  }
  assert (H : 2 ≤ i). {
    destruct i; [ cbn in Hi; flia Hi | ].
    destruct i; [ cbn in Hi; flia Hi | flia ].
  }
  clear Hi; rename H into Hi; move Hi before Hn.
  remember (i mod 2) as q eqn:Hq; symmetry in Hq.
  destruct q. {
    apply Nat.mod_divides in Hq; [ | easy ].
    destruct Hq as (q, Hq).
    replace (i / 2) with (q * 2 / 2) by now rewrite Hq, Nat.mul_comm.
    rewrite Nat.div_mul; [ | easy ].
    destruct (Nat.eq_dec q 1) as [H| H]. {
      subst q; cbn in Hq; subst i; clear Hi.
      cbn; rewrite f_add_0_r.
      destruct n; [ flia Hn | ].
      destruct n; [ flia Hn | clear Hn ].
      destruct n. {
        subst p; cbn.
        rewrite (Hs 1); cbn.
        rewrite f_mul_0_l, f_add_0_r.
        rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l.
        apply f_add_opp_diag_r.
      }
      destruct n; [ easy | ].
      destruct n. {
        rewrite (Hs 0); cbn.
        subst p; cbn.
        rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l, f_add_opp_diag_r.
        now rewrite f_add_0_l, f_add_opp_diag_r, f_mul_0_l.
      }
      rewrite Nat.mod_small in Hm; [ easy | flia ].
    }
    replace (S (S i)) with (2 * q + 2) in Hm by flia Hq.
    assert (H1 : 4 ≤ i). {
      destruct q; [ flia Hq Hi | ].
      destruct q; [ easy | flia Hq ].
    }
    move H1 before Hi; clear Hi; rename H1 into Hi.
(*
  ============================
  (ls s (S i) + ls p (S i) * ls s 0 + (ls p 1 * ls s q + ls p q * ls s 1 + log_prod (ls p) (ls s) (S i) i))%F =
  f_zero
*)
...
    destruct i; [ flia Hi | ].
    rewrite log_prod_succ.
    replace (S (S i) - i) with 2 by flia.
    cbn - [ "/" "mod" log_prod ].
...
replace (ls p (S i)) with f_zero. 2: {
  subst p; cbn.
  destruct n; [ flia Hn | ].
  destruct n; [ flia Hn | ].
  cbn.
clear Hn.
  destruct n.
cbn.
destruct i; [ flia Hi | ].
now destruct i.
cbn.
rewrite List.map_app; cbn.
rewrite List.app_length; cbn.
rewrite Nat.add_1_r.
cbn.
rewrite f_add_opp_diag_r.
destruct i; [ easy | ].
...
intros * Hs i.
unfold ".*".
remember (ls_of_pol (pol_pow 1 - pol_pow n)%LP) as p eqn:Hp.
unfold ls_mul.
symmetry.
cbn - [ log_prod series_but_mul_of ].
cbn - [ log_prod ].
rewrite log_prod_succ.
rewrite Nat.sub_diag.
cbn - [ "/" "mod" ].
rewrite Nat.div_1_r, Nat.mod_1_r, Nat_sub_succ_1.
destruct (Nat.eq_dec i 0) as [Hi| Hi]. {
  subst i.
  destruct (lt_dec n 2) as [Hn| Hn]. {
    replace (ls p 0) with f_zero. 2: {
      subst p; cbn.
      destruct n; [ now cbn; rewrite f_add_opp_diag_r | ].
      destruct n; [ now cbn; rewrite f_add_opp_diag_r | ].
      flia Hn.
    }
    rewrite f_mul_0_l, f_add_0_l.
    cbn.
    destruct n; [ easy | ].
    destruct n; [ easy | ].
    flia Hn.
  }
  apply Nat.nlt_ge in Hn.
  rewrite Nat.mod_1_l; [ cbn | easy ].
  rewrite f_add_0_r.
  replace (ls p 0) with f_one. 2: {
    subst p; cbn.
    destruct n; [ easy | ].
    destruct n; [ flia Hn | cbn ].
    destruct n; now cbn; rewrite f_opp_0, f_add_0_r.
  }
  apply f_mul_1_l.
}
destruct i; [ easy | clear Hi ].
rewrite log_prod_succ.
rewrite Nat_sub_succ_diag_l.
cbn - [ "/" "mod" ].
remember (S (S i) mod n) as x.
replace (S (S i)) with (i + 1 * 2) by flia.
rewrite Nat.div_add; [ | easy ].
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.add_sub; subst x.
destruct (lt_dec i 2) as [Hi | Hi]. {
  destruct (lt_dec (i / 2) 1) as [H| H]; [ clear H | ]. 2: {
    destruct i; [ cbn in H; flia H | ].
    destruct i; [ cbn in H; flia H | flia Hi ].
  }
  rewrite f_add_0_r.
  remember (S (S i) mod n) as m eqn:Hm; symmetry in Hm.
  destruct m. {
    destruct n. {
      subst p; cbn.
      rewrite f_add_opp_diag_r, f_mul_0_l, f_add_0_l.
      now destruct i; rewrite f_mul_0_l.
    }
    apply Nat.mod_divides in Hm; [ | easy ].
    destruct Hm as (m, Hm).
    subst p; cbn.
    rewrite Nat.sub_0_r.
    destruct i. {
      destruct n. {
        now cbn; rewrite f_add_opp_diag_r, f_mul_0_l, f_add_0_l, f_mul_0_l.
      }
      cbn.
      destruct n. {
        cbn; rewrite f_opp_0, f_add_0_r, f_add_0_l.
        rewrite (Hs 0); cbn.
        now rewrite f_mul_opp_l, f_add_opp_diag_r.
      }
      destruct m; [ flia Hm | ].
      cbn in Hm; flia Hm.
    }
    destruct i; [ clear Hi | flia Hi ].
    destruct n. {
      cbn; rewrite f_add_opp_diag_r.
      do 2 rewrite f_mul_0_l.
      apply f_add_0_r.
    }
    destruct n; [ flia Hm | ].
    cbn; rewrite f_opp_0, f_add_0_r, f_mul_1_l.
    destruct m; [ flia Hm | ].
    destruct m; [ | cbn in Hm; flia Hm ].
    rewrite Nat.mul_1_r in Hm.
    do 3 apply Nat.succ_inj in Hm.
    subst n; cbn.
    rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l.
    rewrite (Hs 0); cbn.
    apply f_add_opp_diag_r.
  }
  destruct n; [ cbn in Hm; flia Hm | ].
  destruct n; [ cbn in Hm; flia Hm | ].
  replace (ls p 0) with f_one. 2: {
    now subst p; cbn; destruct n; cbn; rewrite f_opp_0, f_add_0_r.
  }
  rewrite f_mul_1_l.
  replace (ls p (S i)) with f_zero. 2: {
    destruct i. {
      destruct n; [ cbn in Hm; flia Hm | ].
      subst p; cbn.
      now rewrite f_opp_0, f_add_0_r.
    }
    destruct i; [ | flia Hi ].
    subst p; cbn.
    destruct n; [ easy | ].
    destruct n; [ cbn in Hm; flia Hm | ].
    now cbn; rewrite f_opp_0, f_add_0_r.
  }
  now rewrite f_mul_0_l, f_add_0_r.
}
apply Nat.nlt_ge in Hi.
destruct (lt_dec (i / 2) 1) as [H| H]; [ | clear H ]. {
  destruct i; [ flia Hi | ].
  destruct i; [ flia Hi | ].
  replace (S (S i)) with (i + 1 * 2) in H by flia.
  rewrite Nat.div_add in H; [ flia H | easy ].
}
destruct i; [ flia Hi | ].
destruct i; [ flia Hi | clear Hi ].
replace (S (S i)) with (i + 1 * 2) by flia.
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.div_add; [ | easy ].
replace (i + 1 * 2) with (S (S i)) by flia.
replace (S (S (S (S i)))) with (i + 4) by flia.
replace (S (S (S i))) with (i + 3) by flia.
replace (S (S i)) with (i + 2) by flia.
destruct (Nat.eq_dec (i / 2 + 1) 1) as [Hi| Hi]. {
  destruct i. {
    clear Hi; cbn; rewrite f_add_0_r.
    remember (4 mod n) as m eqn:Hm; symmetry in Hm.
    destruct m. {
      destruct n. {
        unfold pol_pow in Hp; cbn in Hp.
        unfold lp_sub, lp_add, lp_opp in Hp.
        cbn in Hp; rewrite f_add_opp_diag_r in Hp.
        subst p; cbn.
        do 3 rewrite f_mul_0_l.
        now do 2 rewrite f_add_0_l.
      }
      destruct n. {
        unfold pol_pow in Hp; cbn in Hp.
        unfold lp_sub, lp_add, lp_opp in Hp.
        cbn in Hp; rewrite f_add_opp_diag_r in Hp.
        subst p; cbn.
        do 3 rewrite f_mul_0_l.
        now do 2 rewrite f_add_0_l.
      }
      destruct n. {
        replace (ls p 3) with f_zero by now subst p.
        rewrite f_mul_0_l, f_add_0_r.
        rewrite (Hs 1); cbn.
        rewrite <- f_mul_add_distr_r.
        replace (ls p 0) with f_one. 2: {
          subst p; cbn.
          now rewrite f_opp_0, f_add_0_r.
        }
        replace (ls p 1) with (- f_one)%F. 2: {
          subst p; cbn.
          now rewrite f_add_0_l.
        }
        now rewrite f_add_opp_diag_r, f_mul_0_l.
      }
      destruct n; [ cbn in Hm; flia Hm | ].
      destruct n; [ clear Hm | ]. 2: {
        cbn in Hm.
        destruct n; [ easy | ].
        destruct n; [ easy | ].
        destruct n; [ easy | ].
        destruct n; [ easy | flia Hm ].
      }
      rewrite (Hs 0); cbn.
      rewrite <- f_mul_add_distr_r.
      replace (ls p 1) with f_zero. 2: {
        now subst p; cbn; rewrite f_add_opp_diag_r.
      }
      rewrite f_mul_0_l, f_add_0_r.
      replace (ls p 0) with f_one. 2: {
        subst p; cbn.
        now rewrite f_opp_0, f_add_0_r.
      }
      replace (ls p 3) with (- f_one)%F. 2: {
        subst p; cbn.
        now rewrite f_add_0_l.
      }
      now rewrite f_add_opp_diag_r, f_mul_0_l.
    }
    destruct n; [ cbn in Hm; flia Hm | ].
    destruct n; [ cbn in Hm; flia Hm | ].
    destruct n; [ cbn in Hm; flia Hm | ].
    replace (ls p 0) with f_one. 2: {
      subst p; cbn.
      now rewrite f_opp_0, f_add_0_r.
    }
    rewrite f_mul_1_l.
    replace (ls p 3) with f_zero. 2: {
      subst p; cbn.
      destruct n; [ easy | ].
      destruct n; [ cbn in Hm; flia Hm | ].
      now cbn; rewrite f_opp_0, f_add_0_r.
    }
    rewrite f_mul_0_l, f_add_0_r.
    replace (ls p 1) with f_zero. 2: {
      now subst p; cbn; rewrite f_opp_0, f_add_0_r.
    }
    now rewrite f_mul_0_l, f_add_0_r.
  }
  destruct i; [ clear Hi | ]. 2: {
    replace (S (S i)) with (i + 1 * 2) in Hi by flia.
    rewrite Nat.div_add in Hi; [ flia Hi | easy ].
  }
  cbn; do 2 rewrite f_add_0_r.
  remember (5 mod n) as m eqn:Hm; symmetry in Hm.
  destruct m. {
    destruct n. {
      unfold pol_pow in Hp; cbn in Hp.
      unfold lp_sub, lp_add, lp_opp in Hp.
      cbn in Hp; rewrite f_add_opp_diag_r in Hp.
      subst p; cbn.
      do 2 rewrite f_mul_0_l.
      now rewrite f_add_0_l.
    }
    destruct n. {
      unfold pol_pow in Hp; cbn in Hp.
      unfold lp_sub, lp_add, lp_opp in Hp.
      cbn in Hp; rewrite f_add_opp_diag_r in Hp.
      subst p; cbn.
      do 2 rewrite f_mul_0_l.
      now rewrite f_add_0_l.
    }
    destruct n; [ easy | ].
    destruct n; [ easy | ].
    destruct n; [ easy | ].
    destruct n; [ clear Hm | ]. 2: {
      cbn in Hm.
      destruct n; [ easy | ].
      destruct n; [ easy | ].
      destruct n; [ easy | ].
      destruct n; [ easy | ].
      destruct n; [ easy | flia Hm ].
    }
    rewrite (Hs 0); cbn.
    rewrite <- f_mul_add_distr_r.
    replace (ls p 0) with f_one. 2: {
      subst p; cbn.
      now rewrite f_opp_0, f_add_0_r.
    }
    replace (ls p 4) with (- f_one)%F. 2: {
      subst p; cbn.
      now rewrite f_add_0_l.
    }
    now rewrite f_add_opp_diag_r, f_mul_0_l.
  }
  subst p; cbn.
  destruct n; [ cbn in Hm; flia Hm | ].
  destruct n; [ cbn in Hm; flia Hm | ].
  destruct n. {
    now cbn; rewrite f_opp_0, f_add_0_r, f_mul_0_l, f_add_0_r, f_mul_1_l.
  }
  cbn; rewrite f_opp_0, f_add_0_r, f_mul_1_l.
  destruct n; [ now cbn; rewrite f_mul_0_l, f_add_0_r | ].
  destruct n; [ now cbn; rewrite f_mul_0_l, f_add_0_r | ].
  destruct n; [ easy | ].
  now cbn; rewrite f_add_opp_diag_r, f_mul_0_l, f_add_0_r.
}
assert (H : 2 ≤ i). {
  destruct i; [ cbn in Hi; flia Hi | ].
  destruct i; [ cbn in Hi; flia Hi | flia ].
}
clear Hi; rename H into Hi.
(**)
destruct n. {
  cbn - [ "/" "mod" ].
  unfold pol_pow in Hp; cbn in Hp.
  unfold lp_sub, lp_add, lp_opp in Hp; cbn in Hp.
  rewrite f_add_opp_diag_r in Hp.
  remember (log_prod (ls p)) as x.
  rewrite Hp; cbn - [ "/" "mod" ]; subst x.
  do 2 rewrite f_mul_0_l, f_add_0_l.
  replace
    (match i + 3 with
     | O => f_zero
     | S m => match m with O => f_zero | S _ => f_zero end
     end) with f_zero. 2: {
    destruct (i + 3) as [| n]; [ easy | ].
    now destruct n.
  }
  rewrite f_mul_0_l, f_add_0_l.
  replace
    (match i / 2 + 1 with
     | O => f_zero
     | S m => match m with O => f_zero | S _ => f_zero end
     end) with f_zero. 2: {
    destruct (i / 2 + 1) as [| n]; [ easy | ].
    now destruct n.
  }
  rewrite f_mul_0_l.
  replace (match i mod 2 with 0 | _ => f_zero end) with f_zero. 2: {
    now destruct (i mod 2).
  }
  rewrite f_add_0_l.
  cbn.
  apply log_prod_0_l.
  intros n; subst p; cbn.
  destruct n; [ easy | now destruct n].
}
...
remember (i mod 2) as m eqn:Hm; symmetry in Hm.
destruct m. {
  destruct n. {
    cbn - [ "/" "mod" ].
    unfold pol_pow in Hp; cbn in Hp.
    unfold lp_sub, lp_add, lp_opp in Hp; cbn in Hp.
    rewrite f_add_opp_diag_r in Hp.
    rewrite Hp at 1 2 3 4; cbn - [ "/" "mod" ].
    do 2 rewrite f_mul_0_l, f_add_0_l.
    replace
      (match i + 3 with
       | O => f_zero
       | S m => match m with O => f_zero | S _ => f_zero end
       end) with f_zero. 2: {
      destruct (i + 3) as [| n]; [ easy | ].
      now destruct n.
    }
    rewrite f_mul_0_l, f_add_0_l.
    replace
      (match i / 2 + 1 with
       | O => f_zero
       | S m => match m with O => f_zero | S _ => f_zero end
       end) with f_zero. 2: {
      destruct (i / 2 + 1) as [| n]; [ easy | ].
      now destruct n.
    }
    rewrite f_mul_0_l, f_add_0_l.
    apply log_prod_0_l.
    intros n; subst p; cbn.
    destruct n; [ easy | now destruct n ].
  }
  remember ((i + 4) mod S n) as q eqn:Hq; symmetry in Hq.
  destruct q. {
    apply Nat.mod_divides in Hq; [ | easy ].
    destruct Hq as (q, Hq).
    destruct q; [ flia Hq | ].
    destruct n. {
      unfold pol_pow in Hp; cbn in Hp.
      unfold lp_sub, lp_add, lp_opp in Hp; cbn in Hp.
      rewrite f_add_opp_diag_r in Hp.
      replace (ls p 0) with f_zero by now rewrite Hp.
      rewrite f_mul_0_l, f_add_0_l.
      replace (ls p (i + 3)) with f_zero by now rewrite Hp, Nat.add_comm.
      rewrite f_mul_0_l, f_add_0_l.
      replace (ls p 1) with f_zero by now rewrite Hp.
      rewrite f_mul_0_l, f_add_0_l.
      replace (ls p (i / 2 + 1)) with f_zero. 2: {
        rewrite Hp, Nat.add_comm; cbn - [ "/" ].
        now destruct (i / 2).
      }
      rewrite f_mul_0_l, f_add_0_l.
      apply log_prod_0_l; rewrite Hp; cbn.
      intros n; destruct n; [ easy | now destruct n ].
    }
    replace (ls p 0) with f_one. 2: {
      subst p; cbn.
      now destruct n; cbn; rewrite f_opp_0, f_add_0_r.
    }
    rewrite f_mul_1_l.
    replace (S (S n)) with (n + 2) in Hq, Hp by flia.
    replace (S q) with (q + 1) in Hq by flia.
    replace (i + 2) with (S (i + 1)) by flia.
    cbn - [ "/" "mod" ].
    replace (i + 3 - (i + 1)) with 2 by flia.
    replace (S (i + 3)) with (i + 1 + 1 * 3) by flia.
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.add_sub.
    destruct (lt_dec ((i + 1) / 3) 2) as [Hi3| Hi3]. {
      rewrite f_add_0_r.
      destruct i; [ flia Hi | ].
      destruct i; [ flia Hi | ].
      replace (S (S i) + 1) with (i + 1 * 3) in Hi3 by flia.
      rewrite Nat.div_add in Hi3; [ | easy ].
      clear Hi.
      destruct i. {
        rewrite Hp; cbn.
        replace (n + 2 - 1) with (S n) by flia; cbn.
        destruct n. {
          cbn; do 2 rewrite f_mul_0_l, f_add_0_r.
          rewrite f_add_0_l.
          rewrite (Hs 2); cbn.
          rewrite f_mul_opp_l, f_mul_1_l.
          apply f_add_opp_diag_r.
        }
        cbn; rewrite f_add_opp_diag_r, f_mul_0_l, f_add_0_l.
        destruct n. {
          cbn; rewrite f_mul_0_l, f_add_0_r, f_add_0_l.
          rewrite f_mul_opp_l, f_mul_1_l.
          rewrite (Hs 1); cbn.
          apply f_add_opp_diag_r.
        }
        cbn; rewrite f_add_opp_diag_r, f_mul_0_l, f_add_0_r.
        assert (H : n = 2). {
          replace (S (S n) + 2) with (n + 4) in Hq by flia.
          destruct n; [ flia Hq | ].
          destruct n; [ flia Hq | ].
          destruct n; [ easy | exfalso ].
          destruct q; [ flia Hq | ].
          cbn in Hq; rewrite Nat.mul_comm in Hq; cbn in Hq.
          flia Hq.
        }
        subst n; cbn.
        rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l.
        rewrite (Hs 0); cbn.
        apply f_add_opp_diag_r.
      }
      destruct i; [ easy | ].
      destruct i. {
        cbn; subst p; cbn.
        replace (n + 2 - 1) with (S n) by flia.
        destruct n. {
          cbn; rewrite f_mul_0_l, f_add_0_r, f_add_0_l.
          rewrite f_mul_0_l, f_add_0_r, f_mul_opp_l, f_mul_1_l.
          rewrite (Hs 3); cbn.
          apply f_add_opp_diag_r.
        }
        destruct n; [ flia Hq | ].
        cbn; rewrite f_add_opp_diag_r, f_mul_0_l, f_add_0_l.
        destruct n. {
          cbn.
          rewrite f_mul_0_l, f_add_0_r, f_add_0_l.
          rewrite f_mul_opp_l, f_mul_1_l.
          rewrite (Hs 1); cbn.
          apply f_add_opp_diag_r.
        }
        replace (S (S (S n)) + 2) with (n + 5) in Hq by flia.
        destruct n; [ flia Hq | ].
        destruct n; [ flia Hq | ].
        destruct n; [ flia Hq | ].
        destruct n. {
          cbn; rewrite f_add_0_l, f_mul_opp_l, f_mul_1_l.
          rewrite f_add_opp_diag_r, f_mul_0_l, f_add_0_r.
          rewrite (Hs 0); cbn.
          apply f_add_opp_diag_r.
        }
        ring_simplify in Hq; flia Hq.
      }
      ring_simplify in Hi3.
      replace (3 + i) with (i + 1 * 3) in Hi3 by flia.
      rewrite Nat.div_add in Hi3; [ flia Hi3 | easy ].
    }
    apply Nat.nlt_ge in Hi3.
    assert (Hi' : 5 ≤ i). {
      destruct i; [ cbn in Hi3; flia Hi3 | ].
      destruct i; [ cbn in Hi3; flia Hi3 | ].
      destruct i; [ cbn in Hi3; flia Hi3 | ].
      destruct i; [ cbn in Hi3; flia Hi3 | ].
      destruct i; [ cbn in Hi3; flia Hi3 | flia ].
    }
    clear Hi Hi3; rename Hi' into Hi.
    (* ouais, on s'enfonce, quoi *)
...
intros * Hs i.
unfold ".*".
remember (ls_of_pol (pol_pow 1 - pol_pow n)%LP) as p eqn:Hp.
unfold ls_mul.
cbn - [ log_prod series_but_mul_of ].
symmetry.
(*
  Hp : p = ls_of_pol (pol_pow 1 - pol_pow n)%LP
  ============================
  log_prod (ls p) (ls s) i (S i) = ls (but_mul_of s n) i
*)
cbn - [ log_prod ].
remember (S i mod n) as m eqn:Hm; symmetry in Hm.
destruct m. {
  destruct n. {
    apply log_prod_0_l; intros n.
    subst p; cbn.
    rewrite f_add_opp_diag_r.
    destruct n; [ easy | now destruct n ].
  }
  apply Nat.mod_divides in Hm; [ | easy ].
  destruct Hm as (m, Hm).
(*
  Hp : p = ls_of_pol (pol_pow 1 - pol_pow (S n))%LP
  m : nat
  Hm : S i = S n * m
  ============================
  log_prod (ls p) (ls s) i (S i) = f_zero
*)
  cbn - [ "/" "mod" ].
  rewrite Nat.sub_diag.
  rewrite Nat.div_1_r, Nat.mod_1_r, Nat_sub_succ_1.
  destruct (lt_dec i 0) as [H| H]; [ easy | clear H ].
  destruct (Nat.eq_dec i 0) as [Hi| Hi]. {
    subst i; cbn; rewrite f_add_0_r.
    destruct n; [ now subst p; cbn; rewrite f_add_opp_diag_r, f_mul_0_l | ].
    destruct n. {
      destruct m; [ easy | cbn in Hm; flia Hm ].
    }
    cbn in Hm.
    destruct m; cbn in Hm; flia Hm.
  }
  destruct n. {
    destruct m; [ flia Hm | ].
    subst p; cbn.
    rewrite f_add_opp_diag_r, f_mul_0_l, f_add_0_l.
    destruct i; [ easy | ].
    replace (match i with 0 | _ => f_zero end) with f_zero by now destruct i.
    rewrite f_mul_0_l, f_add_0_l.
    apply log_prod_0_l.
    intros n; destruct n; [ easy | now destruct n ].
  }
  replace (ls p 0) with f_one. 2: {
    subst p; cbn; symmetry.
    destruct n; now cbn; rewrite f_opp_0, f_add_0_r.
  }
  rewrite f_mul_1_l.
  destruct m; [ flia Hm | clear Hi ].
  destruct m. {
    rewrite Nat.mul_1_r in Hm.
    apply Nat.succ_inj in Hm.
    replace (ls p i) with (- f_one)%F. 2: {
      subst p i; cbn.
      destruct n; [ now cbn; rewrite f_add_0_l | cbn ].
      clear Hs.
      induction n; [ now cbn; rewrite f_add_0_l | easy ].
    }
    rewrite f_mul_opp_l, f_mul_1_l, fold_f_sub.
    rewrite (Hs 0), Nat.mul_1_r, Nat_sub_succ_1, <- Hm.
    unfold f_sub; rewrite f_add_opp_diag_r, f_add_0_l.
(*
  Hp : p = ls_of_pol (pol_pow 1 - pol_pow (S (S n)))%LP
  Hm : i = S n
  ============================
  (log_prod (ls p) (ls s) i i)%F = f_zero
*)
    rewrite Hm at 2.
    cbn - [ "/" "mod" ].
    rewrite Hm, Nat_sub_succ_diag_l.
    replace (S (S n)) with (n + 1 * 2) by flia.
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.add_sub.
    destruct (lt_dec (n / 2) 1) as [| Hn]; [ easy | ].
    assert (H : 2 ≤ n). {
      destruct n; [ cbn in Hn; flia Hn | ].
      destruct n; [ cbn in Hn; flia Hn | flia ].
    }
    clear Hn; rename H into Hn.
    replace (ls p 1) with f_zero. 2: {
      subst p; cbn.
      destruct n; [ cbn in Hn; flia Hn | ].
      now cbn; rewrite f_add_opp_diag_r.
    }
    do 2 rewrite f_mul_0_l.
    rewrite f_add_0_l.
    replace (ls p (n / 2)) with f_zero. 2: {
      subst p; cbn - [ "/" ].
      destruct n; [ cbn in Hn; flia Hn | ].
      cbn - [ "/" ].
      rewrite f_opp_0.
      do 2 rewrite f_add_0_r.
      remember (S n / 2) as r eqn:Hr; symmetry in Hr.
      destruct r. {
        destruct n; [ flia Hn | ].
        replace (S (S n)) with (n + 1 * 2) in Hr by flia.
        rewrite Nat.div_add in Hr; [ flia Hr | easy ].
      }
      clear - Hr.
      destruct r; [ easy | ].
      assert (Hrn : 2 * r < n). {
        specialize (Nat.div_mod (S n) 2 (Nat.neq_succ_0 _)) as H1.
        rewrite Hr in H1.
        flia H1.
      }
      clear Hr.
      revert r Hrn.
      induction n; intros; [ cbn in Hrn; flia Hrn | cbn ].
      rewrite f_add_opp_diag_r.
      destruct r; [ easy | ].
      apply IHn; flia Hrn.
    }
    rewrite f_mul_0_l.
    replace (if Nat.eq_dec _ 1 then f_zero else f_zero) with f_zero. 2: {
      now destruct (Nat.eq_dec _ 1).
    }
    replace (match n mod 2 with | 0 | _ => _ end) with f_zero by
        now destruct (n mod 2).
    rewrite f_add_0_l.
    clear i Hm.
(*
  Hp : p = ls_of_pol (pol_pow 1 - pol_pow (S (S n)))%LP
  Hn : 2 ≤ n
  ============================
  log_prod (ls p) (ls s) (S n) n = f_zero
*)
    destruct n; [ flia Hn | ].
    apply Nat.succ_le_mono in Hn.
    remember (S (S n)) as ssn eqn:Hssn.
    cbn - [ "/" "mod" ]; subst ssn.
    replace (S (S n) - n) with 2 by flia.
    replace (S (S (S n))) with (n + 1 * 3) by flia.
    rewrite Nat.div_add; [ | easy ].
    rewrite Nat.mod_add; [ | easy ].
    rewrite Nat.add_sub.
    replace (ls p 2) with f_zero. 2: {
      subst p; cbn.
      destruct n; [ cbn in Hn; flia Hn | ].
      now cbn; rewrite f_add_opp_diag_r.
    }
    do 2 rewrite f_mul_0_l.
    rewrite f_add_0_l.
    destruct (Nat.eq_dec (n / 3) 2) as [Hn3| Hn3]. 2: {
      destruct (lt_dec (n / 3) 2) as [Hn2| Hn2]; [ easy | ].
      apply Nat.nlt_ge in Hn2.
      replace (ls p (n / 3)) with f_zero. 2: {
        subst p; cbn - [ "/" ].
        destruct n; [ cbn in Hn; flia Hn | ].
        cbn - [ "/" ].
        rewrite f_opp_0.
        do 2 rewrite f_add_0_r.
        remember (S n / 3) as r eqn:Hr; symmetry in Hr.
        destruct r; [ flia Hn2 | ].
        destruct r; [ easy | ].
        clear - Hr.
        assert (Hrn : 3 * r < n). {
          specialize (Nat.div_mod (S n) 3 (Nat.neq_succ_0 _)) as H1.
          rewrite Hr in H1.
          flia H1.
        }
        destruct r; [ easy | ].
        clear Hr.
        revert r Hrn.
        induction n; intros; [ cbn in Hrn; flia Hrn | cbn ].
        rewrite f_add_opp_diag_r.
        destruct r; [ easy | ].
        apply IHn; flia Hrn.
      }
      rewrite f_mul_0_l.
      replace (match _ with 0 | _ => f_zero end) with f_zero by
          now destruct (n mod 3).
      rewrite f_add_0_l.
      assert (H : 9 ≤ n). {
        specialize (Nat.div_mod n 3 (Nat.neq_succ_0 _)) as H.
        flia Hn3 Hn2 H.
      }
      clear Hn Hn3 Hn2; rename H into Hn.
(*
  Hp : p = ls_of_pol (pol_pow 1 - pol_pow (S (S (S n))))%LP
  Hn : 9 ≤ n
  ============================
  log_prod (ls p) (ls s) (S (S n)) n = f_zero
*)
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
