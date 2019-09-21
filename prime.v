(* playing with prime numbers, as a break *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz List.
Import List.ListNotations.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Notation "x ≤ y ≤ z" := (x <= y ∧ y <= z)%nat (at level 70, y at next level).

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

Arguments ls {_}.
Arguments lp {_}.

Definition ls_eq {F : field} s1 s2 := ∀ n, ls s1 n = ls s2 n.

Declare Scope ls_scope.
Delimit Scope ls_scope with LS.

Declare Scope lp_scope.
Delimit Scope lp_scope with LP.

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

Arguments ls_pol_mul_l _ p%LP s%LS.

(* 1+1/3^s+1/5^s+1/7^s+... = (1-1/2^s)ζ(s) *)
(* 1+1/3^s+1/5^s+1/7^s+... = ζ_but_mul_of 2
   (1-1/2^s) = {| lp := [f_one; (- f_one)%F] |} *)

Notation "x = y" := (ls_eq x y) : ls_scope.
Notation "p .* s" := (ls_pol_mul_l p s) (at level 40) : ls_scope.

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

Theorem ζ_is_one {F : field} : ∀ n, ls ζ n = f_one.
Proof.
intros; now unfold ζ.
Qed.

Theorem log_prod_pol_ζ' {F : field} : ∀ n m,
  n mod 2 = 0 → n ≤ m →
  (log_prod (ls (ls_of_pol {| lp := [f_one; - f_one] |})) (ls ζ) m n =
   f_zero)%F.
Proof.
intros * Hn2 Hnm.
apply Nat.mod_divides in Hn2; [ | easy ].
destruct Hn2 as (c, Hc).
remember (ls_of_pol _) as p eqn:Hp.
revert m n Hc Hnm.
induction c; intros; [ now subst n | ].
destruct n; [ flia Hc | ].
destruct n; [ flia Hc | ].
assert (H : n = 2 * c) by flia Hc.
clear Hc; rename H into Hc.
assert (H1 : n ≤ m) by flia Hnm.
specialize (IHc _ _ Hc H1).
clear H1.
cbn - [ "/" "mod" ζ ].
rewrite IHc, f_add_0_r.
do 4 rewrite ζ_is_one.
do 4 rewrite f_mul_1_r.
replace (S (m - S n)) with (m - n) by flia Hnm.
destruct (lt_dec (S m / (m - n) - 1) (m - S n)) as [| H1]; [ easy | ].
apply Nat.nlt_ge in H1.
remember (S m mod (m - n)) as q eqn:Hq; symmetry in Hq.
replace (ls p (m - n)) with f_zero. 2: {
  rewrite Hp; cbn.
  assert (H : m - n ≥ 2) by lia.
  destruct (m - n) as [| x]; [ flia H | ].
  destruct x; [ flia H | now destruct x ].
}
rewrite f_add_0_l.
destruct q. {
  apply Nat.mod_divides in Hq; [ | flia Hnm ].
  destruct Hq as (q, Hq).
  rewrite Hq, Nat.mul_comm, Nat.div_mul in H1; [ | flia Hnm ].
  rewrite Hq, Nat.mul_comm, Nat.div_mul; [ | flia Hnm ].
  destruct q; [ flia Hq | ].
  replace (S q - 1) with q in H1 |-* by flia.
  destruct (Nat.eq_dec q (m - S n)) as [H2| H2]. {
    clear H1.
    replace (m - n) with (S q) by flia H2 Hnm.
    rewrite <- H2.
    destruct (lt_dec (S q * S q / S (S q) - 1) (S q)) as [H1| H1]. {
      rewrite f_add_0_r.
      destruct q; [ flia Hq | ].
      destruct q; [ flia Hc Hq H2 | ].
      rewrite Hp; cbn; now destruct q.
    }
    apply Nat.nlt_ge in H1.
    replace (ls p q) with f_zero. 2: {
      destruct q; [ flia Hq | ].
      destruct q; [ flia Hc Hq H2 | ].
      rewrite Hp; cbn; now destruct q.
    }
    rewrite f_add_0_l.
    remember ((S q * S q) mod S (S q)) as r eqn:Hr; symmetry in Hr.
    destruct r; [ | easy ].
    apply Nat.mod_divides in Hr; [ | easy ].
    destruct Hr as (r, Hr).
    rewrite Hr, Nat.mul_comm, Nat.div_mul in H1; [ | easy ].
    rewrite Hr, Nat.mul_comm, Nat.div_mul; [ | easy ].
    destruct (Nat.eq_dec (r - 1) (S q)) as [| H3]; [ easy | ].
    destruct r; [ flia H1 | ].
    destruct r; [ flia H1 | ].
    destruct r; [ flia H1 H3 | ].
    rewrite Hp; cbn; now destruct r.
  }
  replace (ls p q) with f_zero. 2: {
    destruct q; [ flia Hq | ].
    destruct q; [ flia Hnm H1 H2 | ].
    rewrite Hp; cbn; now destruct q.
  }
  rewrite f_add_0_r.
  rewrite Nat.mul_comm in Hq; rewrite <- Hq.
  destruct (lt_dec (S m / S (m - n) - 1) (m - n)) as [H3| H3]. {
    rewrite f_add_0_r.
    remember (m - S n) as t eqn:Ht; symmetry in Ht.
    destruct t; [ flia Hnm Ht | ].
    destruct t; [ | rewrite Hp; cbn; now destruct t ].
    exfalso.
    replace (m - n) with 2 in Hq, H3 by flia Ht.
    replace (S m) with (S n + 2) in Hq by flia Ht.
    rewrite Hc in Hq.
    flia Hq.
  }
  apply Nat.nlt_ge in H3.
  remember (m - S n) as t eqn:Ht; symmetry in Ht.
  destruct t; [ flia Hnm Ht | ].
  destruct t. 2: {
    replace (ls p (S (S t))) with f_zero. 2: {
      rewrite Hp; cbn; now destruct t.
    }
    rewrite f_add_0_l.
    remember (S m mod S (m - n)) as u eqn:Hu; symmetry in Hu.
    destruct u; [ | easy ].
    apply Nat.mod_divides in Hu; [ | easy ].
    destruct Hu as (u, Hu).
    rewrite Hu, Nat.mul_comm, Nat.div_mul; [ | easy ].
    destruct (Nat.eq_dec (u - 1) (m - n)) as [| H4]; [ easy | ].
    rewrite Hu, Nat.mul_comm, Nat.div_mul in H3; [ | easy ].
    assert (H : u - 1 ≥ 3) by flia Hnm H3 H4.
    rewrite Hp; cbn.
    destruct (u - 1) as [| x]; [ flia H | ].
    destruct x; [ flia H | now destruct x ].
  }
  replace (m - n) with 2 in Hq by flia Ht.
  replace (S m) with (n + 3) in Hq by flia Ht.
  flia Hc Hq.
}
rewrite f_add_0_l.
destruct (lt_dec (S m / S (m - n) - 1) (m - n)) as [| H2]; [ easy | ].
apply Nat.nlt_ge in H2.
remember (S m mod S (m - n)) as t eqn:Ht; symmetry in Ht.
destruct t; [ | easy ].
apply Nat.mod_divides in Ht; [ | easy ].
destruct Ht as (t, Ht).
rewrite Ht, Nat.mul_comm, Nat.div_mul; [ | easy ].
rewrite Ht, Nat.mul_comm, Nat.div_mul in H2; [ | easy ].
destruct (Nat.eq_dec (t - 1) (m - n)) as [| H3]; [ easy | ].
assert (H : t ≥ 3) by lia.
rewrite Hp; cbn.
destruct t; [ easy | ].
replace (S t - 1) with t by flia.
destruct t; [ flia H | ].
destruct t; [ flia H | now destruct t ].
Qed.

Theorem log_prod_pol_ζ {F : field} : ∀ n,
  3 ≤ n → n mod 2 = 1 →
  (log_prod (ls (ls_of_pol {| lp := [f_one; - f_one] |})) (ls ζ) n n =
   - f_one)%F.
Proof.
intros * H3n Hn2.
destruct n; [ easy | ].
cbn - [ "/" "mod" "-" ζ ls_of_pol ].
replace (S (S n) - S n) with 1 by flia.
replace (S (S n)) with (n + 1 * 2) by flia.
rewrite Nat.div_add; [ | easy ].
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.add_sub.
(**)
replace (ls (ls_of_pol _) 1) with (- f_one)%F by easy.
rewrite f_mul_opp_l, f_mul_1_l.
replace (ls ζ 1) with f_one by easy.
rewrite f_mul_opp_l, f_mul_1_l, f_mul_1_r.
replace (ls ζ (n / 2)) with f_one by easy.
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
rewrite log_prod_pol_ζ'; [ apply f_add_0_r | easy | flia ].
Qed.

Definition pol_pow {F : field} n :=
  {| lp := List.repeat f_zero (n - 1) ++ [f_one] |}.

Theorem step_1 {F : field} : ∀ s n,
  (∀ i, ls s i = ls s (n * S i - 1))
  → (series_but_mul_of s n = (pol_pow 1 - pol_pow n) .* s)%LS.
Proof.
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
        remember (S n mod 2) as s eqn:Hs; symmetry in Hs.
        destruct s. {
          rewrite Nat.add_0_r in H1.
          assert (n = 2 * r + 3) by flia H1.
          rewrite H; flia.
        }
        destruct s. 2: {
          specialize (Nat.mod_upper_bound (S n) 2 (Nat.neq_succ_0 _)) as H2.
          rewrite Hs in H2; flia H2.
        }
        assert (n = 2 * r + 4) by flia H1.
        rewrite H; flia.
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
