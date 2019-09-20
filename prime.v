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

(* Euler product formula *)

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
      let j := S n - i in
      let q := S n / S j - 1 in
      if lt_dec q j then f_zero
      else
        (match S n mod S j with
         | 0 =>
             if Nat.eq_dec q j then u j * v j
             else u j * v q + u q * v j
         | _ => f_zero
         end + log_prod u v n i')%F
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
    let j := n - i in
    let q := S n / S j - 1 in
    if lt_dec q j then f_zero
    else
      (match S n mod S j with
       | 0 =>
           if Nat.eq_dec q (n - i) then u j * v j
           else u j * v q + u q * v j
       | S _ => f_zero
       end + log_prod u v n i)%F.
Proof. easy. Qed.

Theorem log_prod_comm {F : field} : ∀ s1 s2 n i,
  log_prod s1 s2 n i = log_prod s2 s1 n i.
Proof.
intros.
revert n.
induction i; intros; [ easy | ].
do 2 rewrite log_prod_succ.
cbn - [ Nat.div Nat.modulo ].
set (j := n - i).
set (q := S n / S j - 1).
destruct (lt_dec q j) as [Hqj| Hqj]; [ easy | ].
f_equal; [ | apply IHi ].
remember (S n mod S j) as m eqn:Hm; symmetry in Hm.
destruct m; [ | easy ].
destruct (Nat.eq_dec q j) as [| Hqje]; [ apply f_mul_comm | ].
rewrite f_add_comm; f_equal; apply f_mul_comm.
Qed.

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
destruct (lt_dec (S n / S (n - i) - 1) (n - i)) as [Hni| Hni]; [ easy | ].
apply Nat.nlt_ge in Hni.
remember (S n mod S (n - i)) as r eqn:Hr; symmetry in Hr.
destruct r; [ | easy ].
do 2 rewrite Hu.
do 2 rewrite f_mul_0_l.
rewrite f_add_0_l.
now destruct (Nat.eq_dec _ _).
Qed.

Theorem ls_mul_0_l {F : field} : ∀ s1 s2,
  (∀ n, ls s1 n = f_zero) → ls_eq (ls_mul s1 s2) {| ls _ := f_zero |}.
Proof.
intros * Hs1 i.
cbn - [ Nat.div Nat.modulo ].
rewrite Nat.sub_diag, Nat.div_1_r, Nat.sub_succ, Nat.sub_0_r.
rewrite Nat.mod_1_r.
destruct (lt_dec i 0) as [H| H]; [ flia H | clear H ].
replace (ls s1 0) with f_zero by now rewrite Hs1.
replace (ls s1 i) with f_zero by now rewrite Hs1.
do 2 rewrite f_mul_0_l.
rewrite f_add_0_l.
replace (if Nat.eq_dec _ _ then _ else _) with f_zero by
  now destruct (Nat.eq_dec i 0).
rewrite f_add_0_l.
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

(*
Theorem ls_mul_ls_mul_upto {F : field} : ∀ s1 s2 len i,
  i < len
  → ls (ls_mul s1 s2) i = ls (ls_mul_l_upto len s1 s2) i.
Proof.
intros * Hlen.
destruct i. {
  rewrite ls_mul_l_upto_of_0.
  cbn - [ "mod" "/" ].
  rewrite Nat.mod_1_r, Nat.div_1_r, Nat.sub_diag.
  rewrite f_add_0_r.
  destruct (Nat.eq_dec 0 0) as [H| H]; [ clear H | flia H ].
  destruct len; [ flia Hlen | easy ].
}
destruct i. {
  rewrite ls_mul_l_upto_of_succ.
  cbn; rewrite f_add_0_r.
  destruct len; [ flia Hlen | ].
  remember (2 mod S len) as b eqn:Hb; symmetry in Hb.
  destruct b. {
    apply Nat.mod_divides in Hb; [ | easy ].
    destruct Hb as (c, Hc).
    rewrite ls_mul_l_upto_of_succ.
    destruct len; [ flia Hlen | clear Hlen ].
...
  rewrite ls_mul_l_upto_of_succ.
  destruct len; [ flia Hlen | clear Hlen ].
  rewrite ls_mul_l_upto_of_succ.
...
rewrite ls_mul_l_upto_of_succ.
destruct len; [ flia Hlen | ].
apply Nat.succ_lt_mono in Hlen.
rewrite ls_mul_l_upto_of_succ.
destruct len; [ flia Hlen | ].
...
intros * Hlen.
revert i Hlen.
induction len; intros; [ flia Hlen | ].
destruct i. {
  clear Hlen.
  rewrite ls_mul_l_upto_of_0.
  cbn - [ "mod" "/" ].
  rewrite Nat.mod_1_r, Nat.div_1_r, Nat.sub_diag.
  now rewrite f_add_0_r.
}
apply Nat.succ_lt_mono in Hlen.
cbn - [ "mod" "/" log_prod ls_add ].
rewrite ls_ls_add.
specialize (IHlen _ Hlen).
rewrite ls_mul_l_upto_of_succ.
...
*)

(*
Theorem ls_pol_mul_l_eq_ls_mul_l_upto_of {F : field} :
  ∀ p s i,
  ls (ls_pol_mul_l p s) i =
  ls (ls_mul_l_upto (length (lp p)) (ls_of_pol p) s) i.
Proof.
intros.
Print ls_mul.
Print log_prod.
Print ls_mul_l_upto.
Print ls_mul_elem.
...
intros.
unfold ls_pol_mul_l.
unfold ls_of_pol.
remember (lp p) as cl eqn:Hcl.
clear p Hcl.
(**)
unfold ls_mul.
cbn - [ "/" "mod" log_prod ].
remember (List.length cl) as len eqn:Hlen; symmetry in Hlen.
revert s i cl Hlen.
induction len; intros. {
  apply length_zero_iff_nil in Hlen.
  subst cl; cbn - [ "/" "mod" ].
  rewrite Nat.sub_diag, Nat.div_1_r, Nat.sub_succ, Nat.sub_0_r.
  rewrite Nat.mod_1_r.
  do 2 rewrite f_mul_0_l.
  rewrite f_add_0_l.
  replace (match _ with 0 | _ => f_zero end) with f_zero by now destruct i.
  rewrite f_mul_0_l.
  replace (if Nat.eq_dec i 0 then f_zero else f_zero) with f_zero. 2: {
    now destruct (Nat.eq_dec _ _).
  }
  destruct (lt_dec i 0) as [H| H]; [ easy | clear H ].
  rewrite f_add_0_l.
  apply log_prod_0_l.
  now intros n; destruct n.
}
rewrite ls_mul_l_upto_succ.
rewrite ls_ls_add.
cbn - [ "/" "mod" log_prod ls_mul_elem ].
unfold ls_mul_elem.
cbn - [ "/" "mod" log_prod ls_mul_elem ].
...
induction cl as [| c cl]. {
  cbn - [ "mod" "/" ].
  rewrite Nat.sub_diag, Nat.div_1_r, Nat.sub_succ, Nat.sub_0_r.
  rewrite Nat.mod_1_r.
  do 2 rewrite f_mul_0_l.
  rewrite f_add_0_l.
  replace (match _ with 0 | _ => f_zero end) with f_zero by now destruct i.
  rewrite f_mul_0_l.
  replace (if Nat.eq_dec i 0 then f_zero else f_zero) with f_zero. 2: {
    now destruct (Nat.eq_dec _ _).
  }
  rewrite f_add_0_l.
  destruct (lt_dec i 0) as [H| H]; [ easy | clear H ].
  apply log_prod_0_l.
  now intros; destruct n.
}
cbn - [ "mod" "/" ls_add ].
rewrite Nat.sub_diag, Nat.div_1_r, Nat.sub_succ, Nat.sub_0_r.
rewrite Nat.mod_1_r.
destruct (lt_dec i 0) as [H| H]; [ flia H | clear H ].
destruct (Nat.eq_dec i 0) as [Hi | Hi]. {
  subst i.
  cbn - [ "mod" "/" ls_add ].
  rewrite f_add_0_r.
  cbn in IHcl.
  rewrite f_add_0_r in IHcl.
...
  destruct cl as [| c1 cl]. {
    now cbn; rewrite f_add_0_l.
  }
  cbn - [ "mod" "/" ls_add ].
  cbn.
...
 rewrite f_mul_0_l.
  rewrite f_add_0_l.
  replace (match _ with 0 | _ => f_zero end) with f_zero by now destruct i.
  rewrite f_mul_0_l.
  replace (if Nat.eq_dec i 0 then f_zero else f_zero) with f_zero. 2: {
    now destruct (Nat.eq_dec _ _).
  }
  rewrite f_add_0_l.
...
*)

(*
Theorem ls_pol_mul_l_eq_ls_mul_l_upto {F : field} :
  ∀ p s,
  ls_eq (ls_pol_mul_l p s)
    (ls_mul_l_upto (List.length (lp p)) (ls_of_pol p) s).
Proof.
intros * i.
...
destruct i. {
  cbn; rewrite f_add_0_r.
  unfold ls_of_pol.
  remember (lp p) as cl eqn:Hcl; symmetry in Hcl.
  clear p Hcl.
  destruct cl as [| c cl]; [ cbn; apply f_mul_0_l | ].
  unfold nth at 1.
  remember (length (c :: cl)) as x; cbn in Heqx; subst x.
  induction cl as [| c1 cl]. {
    now cbn; rewrite f_add_0_l; cbn.
  }
  remember (length (c1 :: cl)) as x; cbn in Heqx; subst x.
  rewrite IHcl; clear IHcl.
  remember (S (length cl)) as x; cbn; subst x.
  unfold snd.
  replace (S (length cl) - length cl) with 1 by flia.
  rewrite f_add_0_r.
  cbn - [ ls_add ].
  do 2 rewrite ls_ls_add.
  f_equal. 2: {
    destruct cl as [| c2 cl]; [ easy | ].
    cbn - [ "-" ].
    now replace (S _ - _) with 1 by flia.
  }
  destruct cl as [| c2 cl]; [ easy | ].
  cbn - [ ls_mul_l_upto ].
  now do 2 rewrite ls_mul_l_upto_0.
}
cbn - [ "/" "mod" "-" ].
rewrite Nat.sub_diag, Nat.div_1_r.
rewrite Nat.sub_succ, Nat.sub_0_r.
destruct (lt_dec (S i) 0) as [H| H]; [ flia H | clear H ].
rewrite Nat.mod_1_r.
destruct (Nat.eq_dec (S i) 0) as [H| H]; [ flia H | clear H ].
replace (S _ - _) with 1 by flia.
replace (S (S i) / 2 - 1) with (i / 2). 2: {
  replace (S (S i)) with (i + 1 * 2) by flia.
  rewrite Nat.div_add; [ | easy ].
  now rewrite Nat.add_sub.
}
symmetry.
destruct (lt_dec (i / 2) 1) as [Hi| Hi]. {
  rewrite f_add_0_r.
  destruct i. {
    cbn.
...
(*
Check ls_mul_l_upto_succ.
Search (ls_mul_l_upto (S _)).
Theorem glop {F : field} : ∀ k s1 s2 i,
  ls (ls_mul_l_upto (S k) s1 s2) i =
    (ls (ls_mul_l_upto k s1 s2) i +
     match S i mod S k with
     | 0 => ls s1 k * ls s2 (S i / S k - 1)
     | S _ => f_zero
     end)%F.
Proof. easy. Qed.
*)
remember (length (lp p)) as len eqn:Hlen; symmetry in Hlen.
clear Hi.
revert p Hlen.
induction len; intros. {
  apply length_zero_iff_nil in Hlen.
  rewrite Hlen; cbn.
  do 2 rewrite f_mul_0_l.
  apply f_add_0_l.
}
rewrite glop.
...

destruct len. {
  cbn.
  rewrite f_add_0_l.
  rewrite (@nth_overflow _ _ 1); [ | flia Hlen ].
  now rewrite f_mul_0_l, f_add_0_r.
}
destruct len. {
  rewrite Nat.mod_same; [ | easy ].
  rewrite Nat.div_same; [ | easy ].
  rewrite Nat.sub_diag.
  now cbn; rewrite f_add_0_l.
}
replace (2 mod (S (S (S len)))) with 2. 2: {
  now rewrite Nat.mod_small; [ | flia ].
}
rewrite f_add_0_r.
rewrite glop.
...

destruct k; cbn.
...
  }
  destruct i. 2: {
    replace (S (S i)) with (i + 1 * 2) in Hi by flia.
    rewrite Nat.div_add in Hi; [ flia Hi | easy ].
  }
  clear Hi.
...
Print ls_mul_l_upto.
*)

Theorem zeta_is_one {F : field} : ∀ n, ls zeta n = f_one.
Proof.
intros; now unfold zeta.
Qed.

(* seems to be true by testing it in ocaml *)
Theorem log_prod_pol_zeta' {F : field} : ∀ n m,
  2 ≤ n → n mod 2 = 0 → n ≤ m →
  (log_prod (ls (ls_of_pol {| lp := [f_one; - f_one] |})) (ls zeta) m n =
   f_zero)%F.
Proof.
intros * H3n Hn2 Hnm.
destruct n; [ flia H3n | ].
destruct n; [ flia H3n | clear H3n ].
replace (S (S n)) with (n + 1 * 2) in Hn2 by flia.
rewrite Nat.mod_add in Hn2; [ | easy ].
apply Nat.mod_divides in Hn2; [ | easy ].
destruct Hn2 as (c, Hc).
remember (ls_of_pol _) as p eqn:Hp.
replace (S (S n)) with (2 * S c) in Hnm by flia Hc.
revert m n Hc Hnm.
induction c; intros. {
  cbn in Hc; subst n.
  cbn - [ "/" "mod" ].
  rewrite Nat.sub_0_r, f_add_0_r.
  do 4 rewrite f_mul_1_r.
  rewrite Nat.div_same; [ | easy ].
  rewrite Nat.mod_same; [ | easy ].
  rewrite Nat.sub_diag.
  replace (S (m - 1)) with m by flia Hnm.
  replace (S m) with (1 + 1 * m) by flia.
  rewrite Nat.div_add; [ | flia Hnm ].
  rewrite Nat.mod_add; [ | flia Hnm ].
  rewrite Nat.add_sub.
  rewrite Nat.div_small; [ | easy ].
  rewrite Nat.mod_small; [ | easy ].
  replace (ls p m) with f_zero. 2: {
    subst p.
    destruct m; [ easy | ].
    destruct m; [ flia Hnm | ].
    now destruct m.
  }
  do 2 rewrite f_add_0_l.
  replace (ls p 0) with f_one by now subst p.
  destruct (lt_dec 0 (m - 1)) as [Hm| Hm]; [ easy | ].
  flia Hm Hnm.
}
destruct n; [ flia Hc | ].
destruct n; [ flia Hc | ].
assert (H : n = 2 * c) by flia Hc.
clear Hc; rename H into Hc.
assert (H1 : 2 * S c ≤ m). {
  eapply le_trans; [ | apply Hnm ].
  flia.
}
specialize (IHc _ _ Hc H1).
remember (S (S n)) as sn; cbn - [ "/" "mod" zeta ]; subst sn.
rewrite IHc, f_add_0_r.
do 4 rewrite zeta_is_one.
do 4 rewrite f_mul_1_r.
replace (m - S (S (S n))) with (m - n - 3) by flia.
replace (S (m - n - 3)) with (m - n - 2) by flia Hnm Hc.
destruct (lt_dec (S m / (m - n - 2) - 1) (m - n - 3)) as [| H2]; [ easy | ].
apply Nat.nlt_ge in H2.
replace (m - S (S n)) with (m - n - 2) by flia.
remember (S m mod (m - n - 2)) as q eqn:Hq; symmetry in Hq.
destruct q. {
  assert (H3 : m - n - 2 ≥ 2) by flia Hnm Hc.
  assert (H4 : m - n - 3 ≥ 1) by flia Hnm Hc.
  apply Nat.mod_divides in Hq; [ | flia H3 ].
  destruct Hq as (r, Hr).
  rewrite Hr, Nat.mul_comm, Nat.div_mul in H2; [ | flia H3 ].
  rewrite Hr, Nat.mul_comm, Nat.div_mul; [ | flia H3 ].
  destruct (Nat.eq_dec (r - 1) (m - n - 3)) as [H5| H5]. {
    destruct (lt_dec (r * (m - n - 2) / S (m - n - 2) - 1) (m - n - 2))
      as [H6| H6]. {
      rewrite f_add_0_r.
      remember (m - n - 3) as t eqn:Ht; symmetry in Ht.
      destruct t; [ flia H4 | clear H4 ].
      destruct t; [ | rewrite Hp; cbn; now destruct t ].
      exfalso.
      assert (H : r = 2) by flia H5; clear H5 H2.
      subst r.
      flia Ht Hr.
    }
    apply Nat.nlt_ge in H6.
    assert (H7 : r ≥ 2) by flia H4 H5.
    replace (ls p (m - n - 2)) with f_zero. 2: {
      subst p; cbn.
      destruct (m - n - 2) as [| x]; [ flia H3 | ].
      destruct x; [ flia H3 | ].
      now destruct x.
    }
    assert (H8 : r = m - n - 2) by lia.
    rewrite f_add_0_l.
    rewrite <- H5.
    rewrite <- H8 in *.
    remember ((r * r) mod S r) as t eqn:Ht.
    symmetry in Ht.
    destruct t. {
      apply Nat.mod_divides in Ht; [ | flia ].
      destruct Ht as (t, Ht).
      rewrite Ht, Nat.mul_comm, Nat.div_mul; [ | easy ].
      destruct t; [ flia Hr Ht | ].
      replace (S t - 1) with t by flia.
      destruct (Nat.eq_dec t r) as [H9| H9]; [ subst t; flia Ht | ].
      destruct t; [ flia Hr H8 Ht H9 | ].
      destruct r; [ flia H3 | ].
      destruct r; [ flia H3 | clear H3 H7 ].
      cbn in Ht.
      do 2 apply Nat.succ_inj in Ht.
      setoid_rewrite Nat.add_comm in Ht; cbn in Ht.
      do 2 apply Nat.succ_inj in Ht.
      rewrite Nat.mul_comm in Ht; cbn in Ht.
      destruct r; [ flia Ht | ].
      rewrite Hp at 1; cbn.
      replace (match r with 0 | _ => _ end) with f_zero by now destruct r.
      rewrite f_add_0_l.
      destruct t; [ | now rewrite Hp; cbn; destruct t ].
      exfalso; clear H9.
      ring_simplify in Ht.
      flia Ht.
    }
    rewrite f_add_0_r.
    destruct r; [ flia H3 | ].
    destruct r; [ flia H3 | clear H3 H7 ].
    destruct r; [ flia Hr H8 | ].
    subst p; cbn; now destruct r.
  }
  replace (ls p (m - n - 3)) with f_zero. 2: {
    subst p; cbn.
    remember (m - n - 3) as t eqn:Ht; symmetry in Ht.
    destruct t; [ flia H4 | ].
    destruct t; [ exfalso | now destruct t ].
    replace (m - n - 2) with 2 in Hr by flia Ht.
    flia Hc Ht Hr.
  }
  rewrite f_add_0_l.
  replace (ls p (r - 1)) with f_zero. 2: {
    destruct r; [ flia H2 H4 | ].
    destruct r; [ flia H2 H4 | ].
    destruct r; [ flia H2 H4 H5 | ].
    now rewrite Hp; cbn; destruct r.
  }
  rewrite f_add_0_l.
  remember (m - n - 2) as t eqn:Ht; symmetry in Ht.
  destruct (lt_dec (r * t / S t - 1) t) as [H6| H6]; [ easy | ].
  apply Nat.nlt_ge in H6.
  remember ((r * t) mod S t) as u eqn:Hu; symmetry in Hu.
  destruct u; [ | easy ].
  apply Nat.mod_divides in Hu; [ | easy ].
  destruct Hu as (u, Hu).
  rewrite Hu, Nat.mul_comm, Nat.div_mul; [ | easy ].
  destruct (Nat.eq_dec (u - 1) t) as [H7| H7]. {
    destruct t; [ flia H3 | ].
    destruct t; [ flia H3 | ].
    destruct t; [ flia Hu H7 | ].
    now rewrite Hp.
  }
  destruct t; [ flia H3 | ].
  destruct t; [ flia H3 | ].
  destruct t; [ flia Hc H2 Ht Hr | ].
  rewrite Hp at 1; cbn; rewrite f_add_0_l.
  clear H3.
  rewrite Hu, Nat.mul_comm in H6.
  rewrite Nat.div_mul in H6; [ | easy ].
  destruct u; [ flia H6 | ].
  destruct u; [ flia H6 | ].
  destruct u; [ flia H6 | ].
  now rewrite Hp; cbn; destruct u.
}
rewrite f_add_0_l.
remember (m - n - 2) as t eqn:Ht; symmetry in Ht.
destruct (lt_dec (S m / S t - 1) t) as [| H3]; [ easy | ].
apply Nat.nlt_ge in H3.
remember (S m mod S t) as u eqn:Hu; symmetry in Hu.
destruct u; [ | easy ].
apply Nat.mod_divides in Hu; [ | easy ].
destruct Hu as (u, Hu).
rewrite Hu, Nat.mul_comm, Nat.div_mul; [ | easy ].
rewrite Hu, Nat.mul_comm, Nat.div_mul in H3; [ | easy ].
destruct (Nat.eq_dec (u - 1) t) as [H4| H4]. {
  clear H3.
  destruct u; [ flia Hu | ].
  replace (S u - 1) with u in H4 by flia.
  subst u.
  assert (H3 : m = t + n + 2) by flia Ht Hnm Hc.
  rewrite H3 in Hu.
  cbn in Hu.
  apply Nat.succ_inj in Hu.
  assert (H4 : t * (t + 1) = n + 2) by flia Hu.
  rewrite Hc in H4.
  (* mouais, faut voir... *)
...
replace (ls p t) with f_zero. 2: {
  destruct t; [ flia Hnm Hc Ht | ].
  destruct t; [ flia Hnm Hc Ht | ].
  destruct t; [ exfalso | now rewrite Hp; cbn ].
  destruct q. 2: {
    specialize (Nat.mod_upper_bound (S m) 2 (Nat.neq_succ_0 _)) as H4.
    flia Hq H4.
  }
  assert (Hm : m = n + 4) by flia Hc Ht.
  clear Hnm H1 Ht H2 Hq.
  cbn - [ "/" "mod" zeta ] in IHc.
  do 4 rewrite zeta_is_one in IHc.
  do 4 rewrite f_mul_1_r in IHc.
  rewrite Hm in IHc.
  replace (n + 4 - S n) with 3 in IHc by flia.
  replace (n + 4 - n) with 4 in IHc by flia.
  replace (S (n + 4)) with (n + 1 + 1 * 4) in IHc by flia.
  rewrite Nat.div_add in IHc; [ | easy ].
  rewrite Nat.mod_add in IHc; [ | easy ].
  rewrite Nat.add_sub in IHc.
  replace (n + 1 + 1 * 4) with (n + 1 * 5) in IHc by flia.
  rewrite Nat.div_add in IHc; [ | easy ].
  rewrite Nat.mod_add in IHc; [ | easy ].
  rewrite Nat.add_sub in IHc.
  replace (ls p 3) with f_zero in IHc by now subst p.
  rewrite f_add_0_l in IHc.
  replace (ls p 4) with f_zero in IHc by now subst p.
  rewrite f_add_0_l in IHc.
  destruct (lt_dec ((n + 1) / 4) 3) as [H1| H1]. {
    clear IHc.
    rewrite Hm in Hu.
    ring_simplify in Hu.
    clear m Hm.
    subst n.
    destruct c; [ flia Hu | ].
    destruct c; [ flia Hu | ].
    destruct c. {
      remember (3 * u) as x; cbn in Hu; subst x.
      cbn in H1.
      (* merdalor *)
...

(* seems to be true by testing it in ocaml *)
Theorem log_prod_pol_zeta {F : field} : ∀ n,
  3 ≤ n → n mod 2 = 1 →
  (log_prod (ls (ls_of_pol {| lp := [f_one; - f_one] |})) (ls zeta) n n =
   - f_one)%F.
Proof.
intros * H3n Hn2.
destruct n; [ easy | ].
cbn - [ "/" "mod" "-" zeta ls_of_pol ].
replace (S (S n) - S n) with 1 by flia.
replace (S (S n)) with (n + 1 * 2) by flia.
rewrite Nat.div_add; [ | easy ].
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.add_sub.
(**)
replace (ls (ls_of_pol _) 1) with (- f_one)%F by easy.
rewrite f_mul_opp_l, f_mul_1_l.
replace (ls zeta 1) with f_one by easy.
rewrite f_mul_opp_l, f_mul_1_l, f_mul_1_r.
replace (ls zeta (n / 2)) with f_one by easy.
destruct (lt_dec (n / 2) 1) as [Hn| Hn]. {
  exfalso.
  destruct n; [ flia H3n | ].
  destruct n; [ flia H3n | ].
  replace (S (S n)) with (n + 1 * 2) in Hn by flia.
  rewrite Nat.div_add in Hn; [ flia Hn | easy ].
}
clear Hn.
remember (n mod 2) as m eqn:Hm; symmetry in Hm.
destruct m. 2: {
  destruct m. 2: {
    specialize (Nat.mod_upper_bound n 2 (Nat.neq_succ_0 _)) as H1.
    rewrite Hm in H1; flia H1.
  }
  specialize (Nat.div_mod n 2 (Nat.neq_succ_0 _)) as H1.
  rewrite H1, Hm in Hn2.
  replace (S (2 * (n / 2) + 1)) with (0 + (n / 2 + 1) * 2) in Hn2 by flia.
  now rewrite Nat.mod_add in Hn2.
}
clear Hn2.
apply Nat.mod_divides in Hm; [ | easy ].
destruct Hm as (m, Hm).
rewrite Hm, Nat.mul_comm, Nat.div_mul; [ | easy ].
destruct (Nat.eq_dec m 1) as [Hm1| Hm1]. {
  subst m; cbn in Hm; subst n; cbn.
  apply f_add_0_r.
}
destruct m; [ cbn in Hm; flia H3n Hm | ].
destruct m; [ easy | clear Hm1 ].
replace (ls (ls_of_pol _) (S (S m))) with f_zero. 2: {
  cbn; now destruct m.
}
rewrite f_add_0_r.
replace (S (S m) * 2) with n by flia Hm.
assert (H : n mod 2 = 0). {
  replace n with (0 + S (S m) * 2) by flia Hm.
  now rewrite Nat.mod_add.
}
rewrite log_prod_pol_zeta'; [ | flia H3n | easy | flia ].
apply f_add_0_r.
Qed.

Theorem step_1 {F : field} :
  ls_eq (zeta_but_mul_of 2)
    (ls_pol_mul_l {| lp := [f_one; (- f_one)%F] |} zeta).
Proof.
intros n.
cbn - [ "mod" ls_pol_mul_l ].
remember (S n mod 2) as p eqn:Hp; symmetry in Hp.
symmetry.
destruct p. {
  apply Nat.mod_divides in Hp; [ | easy ].
  destruct Hp as (m & Hm).
  destruct m; [ flia Hm | ].
  assert (Hn : n = 2 * m + 1) by flia Hm; clear Hm.
  unfold ls_pol_mul_l.
  cbn - [ "/" "mod" ls_of_pol zeta ].
  rewrite Nat.sub_diag, Nat.div_1_r, Nat.sub_succ, Nat.sub_0_r.
  destruct (lt_dec n 0) as [H| H]; [ easy | clear H ].
(*
  rewrite Nat.mod_1_r, f_mul_1_r, f_mul_1_r.
*)
  destruct (Nat.eq_dec n 0) as [H| H]; [ flia Hn H | clear H ].
  unfold ls_of_pol at 1 2.
  cbn - [ ls_of_pol log_prod zeta ].
  destruct n; [ flia Hn | ].
  destruct n. {
    cbn; rewrite f_mul_1_r.
    now rewrite f_mul_1_r, f_add_opp_diag_r, f_add_0_l.
  }
  replace (match _ with 0 | _ => f_zero end) with f_zero by now destruct n.
  rewrite f_mul_0_l, f_add_0_r, f_mul_1_l.
  replace (ls zeta (S (S n))) with f_one by easy.
  assert (Hnn : 3 ≤ S (S n)). {
    destruct n. {
      destruct m; [ easy | ].
      destruct m; [ easy | flia Hn ].
    }
    flia.
  }
  rewrite log_prod_pol_zeta; [ apply f_add_opp_diag_r | easy | ].
  rewrite Hn, Nat.add_comm, Nat.mul_comm.
  now rewrite Nat.mod_add.
}
destruct p. 2: {
  specialize (Nat.mod_upper_bound (S n) 2 (Nat.neq_succ_0 _)) as H1.
  flia Hp H1.
}
...

Theorem zeta_Euler_product_eq : ∀ s, expr_eq (zeta s) (zeta' s).
Proof.
...
