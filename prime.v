(* playing with prime numbers, as a break *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz.

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

Require Import Reals.

Record C := { Re : R; Im : R }.
Declare Scope complex_scope.
Delimit Scope complex_scope with C.
Definition C_opp c := {| Re := - Re c; Im := - Im c |}.
Definition C_mul x y :=
  {| Re := Re x * Re y - Im x * Im y;
     Im := Re x * Im y + Im x * Re y |}.
(* 1/(a+ib)=(a-ib)/(a²+b²) *)
Definition C_inv x :=
  {| Re := Re x / (Re x * Re x + Im x * Im x);
     Im := - Im x / (Re x * Re x + Im x * Im x) |}.
Definition C_div x y := C_mul x (C_inv y).
(* e^(a+ib) = e^a (cos b + i sin b) *)
Definition C_exp c :=
  {| Re := exp (Re c) * cos (Im c);
     Im := exp (Re c) * sin (Im c) |}.
Definition C_of_R x := {| Re := x; Im := 0%R |}.
Definition C_pow_nat_l n c := C_exp (C_mul c (C_of_R (ln (INR n)))).
Notation "- x" := (C_opp x) : complex_scope.
Notation "x * y" := (C_mul x y) : complex_scope.
Notation "x / y" := (C_div x y) : complex_scope.
Definition C_of_decimal_uint (n : Decimal.uint) : C :=
  {| Re := INR (Nat.of_uint n); Im := 0%R |}.
Definition C_of_decimal_int (n : Decimal.int) : C :=
  match n with
  | Decimal.Pos ui => C_of_decimal_uint ui
  | Decimal.Neg ui => (- C_of_decimal_uint ui)%C
  end.
Definition Req_dec' x y :=
  if Rle_dec x y then if Rle_dec y x then true else false else false.
Definition C_to_decimal_uint (c : C) : option Decimal.uint :=
  if Req_dec' (Im c) 0%R then
    if Req_dec' (frac_part (Re c)) 0%R then
      if Rle_dec 0%R (Re c) then
        Some (Nat.to_uint (Z.to_nat (Int_part (Re c))))
      else None
  else None
  else None.
Definition C_to_decimal_int (c : C) : option Decimal.int :=
  match C_to_decimal_uint c with
  | Some u => Some (Decimal.Pos u)
  | None =>
      match C_to_decimal_uint (- c)%C with
      | Some u => Some (Decimal.Neg u)
      | None => None
      end
  end.
Numeral Notation C C_of_decimal_int C_to_decimal_int : complex_scope
  (abstract after 5001).

Record series A := { ser : nat → A }.
Record product A := { pro : nat → A }.

Definition zeta s := {| ser n := (1 / C_pow_nat_l n s)%C |}.
Print zeta.
