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

Theorem Nat_sub_succ_diag_l : ∀ n, S n - n = 1.
Proof.
intros; induction n; [ easy | now rewrite Nat.sub_succ ].
Qed.

Theorem Nat_sub_sub_swap : ∀ a b c, a - b - c = a - c - b.
Proof.
intros.
rewrite <- Nat.sub_add_distr.
rewrite Nat.add_comm.
now rewrite Nat.sub_add_distr.
Qed.

Theorem Nat_mod_0_mod_div : ∀ a b,
  0 < b ≤ a → a mod b = 0 → a mod (a / b) = 0.
Proof.
intros * Hba Ha.
assert (Hbz : b ≠ 0) by flia Hba.
assert (Habz : a / b ≠ 0). {
  intros H.
  apply Nat.div_small_iff in H; [ | flia Hba ].
  now apply Nat.nle_gt in H.
}
specialize (Nat.div_mod a (a / b) Habz) as H1.
specialize (Nat.div_mod a b Hbz) as H2.
rewrite Ha, Nat.add_0_r in H2.
rewrite H2 in H1 at 3.
rewrite Nat.div_mul in H1; [ | easy ].
rewrite Nat.mul_comm in H1.
flia H1 H2.
Qed.

Theorem Nat_mod_0_div_div : ∀ a b,
  0 < b ≤ a → a mod b = 0 → a / (a / b) = b.
Proof.
intros * Hba Ha.
assert (Hbz : b ≠ 0) by flia Hba.
assert (Habz : a / b ≠ 0). {
  intros H.
  apply Nat.div_small_iff in H; [ | easy ].
  now apply Nat.nle_gt in H.
}
specialize (Nat.div_mod a (a / b) Habz) as H1.
rewrite Nat_mod_0_mod_div in H1; [ | easy | easy ].
rewrite Nat.add_0_r in H1.
apply (Nat.mul_cancel_l _ _ (a / b)); [ easy | ].
rewrite <- H1; symmetry.
rewrite Nat.mul_comm.
apply Nat.mod_divide in Ha; [ | easy ].
rewrite <- Nat.divide_div_mul_exact; [ | easy | easy ].
now rewrite Nat.mul_comm, Nat.div_mul.
Qed.

Theorem Nat_sub_sub_assoc : ∀ a b c,
  c ≤ b ≤ a + c
  → a - (b - c) = a + c - b.
Proof.
intros * (Hcb, Hba).
revert a c Hcb Hba.
induction b; intros.
-apply Nat.le_0_r in Hcb; subst c.
 now rewrite Nat.add_0_r.
-destruct c; [ now rewrite Nat.add_0_r | ].
 apply Nat.succ_le_mono in Hcb.
 rewrite Nat.add_succ_r in Hba.
 apply Nat.succ_le_mono in Hba.
 specialize (IHb a c Hcb Hba) as H1.
 rewrite Nat.sub_succ, H1.
 rewrite Nat.add_succ_r.
 now rewrite Nat.sub_succ.
Qed.

Theorem Nat_sub_sub_distr : ∀ a b c, c ≤ b ≤ a → a - (b - c) = a - b + c.
Proof.
intros.
rewrite <- Nat.add_sub_swap; [ | easy ].
apply Nat_sub_sub_assoc.
split; [ easy | ].
apply (Nat.le_trans _ a); [ easy | ].
apply Nat.le_add_r.
Qed.

Theorem List_fold_right_cons {A B} : ∀ (f : B → A → A) (a : A) x l,
  List.fold_right f a (x :: l) = f x (List.fold_right f a l).
Proof. easy. Qed.

Theorem List_removelast_firstn {A} : ∀ l : list A,
  List.removelast l = List.firstn (List.length l - 1) l.
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
rewrite Nat.sub_0_r.
destruct l as [| b l]; [ easy | ].
rewrite IHl.
now cbn; rewrite Nat.sub_0_r.
Qed.

Theorem List_filter_map {A} : ∀ (f : A → bool) (g : A → A) l,
  List.filter f (List.map g l) = List.map g (List.filter (λ x, f (g x)) l).
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
remember (f (g a)) as b eqn:Hb; symmetry in Hb.
destruct b; [ cbn; f_equal; apply IHl | apply IHl ].
Qed.

Theorem List_filter_length_upper_bound {A} : ∀ (f : A → bool) l,
  List.length (List.filter f l) ≤ List.length l.
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
destruct (f a); [ now apply Nat.succ_le_mono in IHl | ].
transitivity (length l); [ easy | apply Nat.le_succ_diag_r ].
Qed.

Theorem Sorted_Sorted_seq : ∀ start len, Sorted.Sorted lt (seq start len).
Proof.
intros.
revert start.
induction len; intros; [ apply Sorted.Sorted_nil | ].
cbn; apply Sorted.Sorted_cons; [ apply IHlen | ].
clear IHlen.
induction len; [ apply Sorted.HdRel_nil | ].
cbn. apply Sorted.HdRel_cons.
apply Nat.lt_succ_diag_r.
Qed.

(* *)

Fixpoint prime_test cnt n d :=
  match cnt with
  | 0 => true
  | S c =>
      match n mod d with
      | 0 => false
      | S _ => prime_test c n (d + 1)
      end
  end.

Definition is_prime n :=
  match n with
  | 0 | 1 => false
  | S (S c) => prime_test c n 2
  end.

Theorem prime_test_false_exists_div_iff : ∀ n k,
  2 ≤ k
  → (∀ d, 2 ≤ d < k → n mod d ≠ 0)
  → prime_test (n - k) n k = false
  ↔ ∃ a b : nat, a < n ∧ b < n ∧ n = a * b.
Proof.
intros * Hk Hd.
split.
-intros Hp.
 remember (n - k) as cnt eqn:Hcnt; symmetry in Hcnt.
 revert n k Hk Hd Hcnt Hp.
 induction cnt; intros; [ easy | ].
 cbn in Hp.
 remember (n mod k) as m eqn:Hm; symmetry in Hm.
 destruct m. {
   destruct k; [ easy | ].
   apply Nat.mod_divides in Hm; [ | easy ].
   destruct Hm as (m, Hm).
   destruct m; [ now rewrite Hm, Nat.mul_0_r in Hcnt | ].
   destruct k; [ flia Hk | ].
   destruct m. {
     now rewrite Hm, Nat.mul_1_r, Nat.sub_diag in Hcnt.
   }
   exists (S (S k)), (S (S m)).
   rewrite Hm.
   replace (S (S k) * S (S m)) with (S (S k) + k * m + k + 2 * m + 2) by flia.
   split; [ flia | ].
   split; [ flia | easy ].
 }
 destruct n; [ flia Hcnt | ].
 apply (IHcnt (S n) (k + 1)); [ flia Hk | | flia Hcnt | easy ].
 intros d Hdk.
 destruct (Nat.eq_dec d k) as [Hdk1| Hdk1]. {
   now intros H; rewrite <- Hdk1, H in Hm.
 }
 apply Hd; flia Hdk Hdk1.
-intros (a & b & Han & Hbn & Hnab).
 remember (n - k) as cnt eqn:Hcnt; symmetry in Hcnt.
 revert n a b k Hk Hd Hcnt Han Hbn Hnab.
 induction cnt; intros. {
   specialize (Hd a) as H1.
   assert (H : 2 ≤ a < k). {
     split. {
       destruct a; [ flia Hnab Han | ].
       destruct a; [ flia Hnab Han Hbn | flia ].
     }
     flia Han Hcnt.
   }
   specialize (H1 H).
   exfalso; apply H1; rewrite Hnab, Nat.mul_comm.
   apply Nat.mod_mul; flia H.
 }
 cbn.
 remember (n mod k) as m eqn:Hm; symmetry in Hm.
 destruct m; [ easy | ].
 apply (IHcnt _ a b); [ flia Hk | | flia Hcnt | easy | easy | easy ].
 intros d (H2d, Hdk).
 destruct (Nat.eq_dec d k) as [Hdk1| Hdk1]. {
   now intros H; rewrite <- Hdk1, H in Hm.
 }
 apply Hd.
 flia H2d Hdk Hdk1.
Qed.

Theorem not_prime_decomp : ∀ n, 2 ≤ n →
  is_prime n = false
  → ∃ a b, a < n ∧ b < n ∧ n = a * b.
Proof.
intros n Hn Hp.
unfold is_prime in Hp.
destruct n; [ flia Hn | ].
destruct n; [ flia Hn | ].
replace n with (S (S n) - 2) in Hp at 1 by flia.
apply (prime_test_false_exists_div_iff _ 2); [ easy | | easy ].
intros * H; flia H.
Qed.

Theorem not_prime_exists_div : ∀ n, 2 ≤ n →
  is_prime n = false
  → ∃ a, 2 ≤ a < n ∧ Nat.divide a n.
Proof.
intros n Hn Hp.
specialize (not_prime_decomp n Hn Hp) as (a & b & Ha & Hb & Hab).
exists a.
split; [ | now rewrite Hab; apply Nat.divide_mul_l ].
split; [ | easy ].
destruct a; [ flia Hab Hb | ].
destruct a; [ flia Hab Hb | flia ].
Qed.

Theorem prime_divisor : ∀ n, 2 ≤ n →
  ∃ d, is_prime d = true ∧ Nat.divide d n.
Proof.
intros * Hn.
induction n as (n, IHn) using (well_founded_ind lt_wf).
remember (is_prime n) as b eqn:Hb; symmetry in Hb.
destruct b; [ now exists n | ].
specialize (not_prime_exists_div n Hn Hb) as (a & Han & Hd).
specialize (IHn a (proj2 Han) (proj1 Han)) as H1.
destruct H1 as (d & Hpd & Hda).
exists d.
split; [ easy | ].
now transitivity a.
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

Theorem f_add_add_swap {F : field} : ∀ x y z, (x + y + z = x + z + y)%F.
Proof.
intros.
do 2 rewrite <- f_add_assoc.
apply f_equal, f_add_comm.
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

Definition divisors_but_firstn_and_lastn d n :=
  List.filter (λ a, n mod a =? 0) (List.seq d (S n - d)).

Definition divisors := divisors_but_firstn_and_lastn 1.

Definition log_prod_term {F : field} u v n i :=
  (u i * v (n / i))%F.

Definition log_prod_list {F : field} u v n :=
  List.map (log_prod_term u v n) (divisors n).

Definition log_prod {F : field} u v n :=
  List.fold_left f_add (log_prod_list u v n) f_zero.

(*
Definition log_prod_add {F : field} u v n i c :=
  (c + u i * v (n / i))%F.

Definition log_prod {F : field} u v n :=
  List.fold_right (log_prod_add u v n) f_zero (divisors n).
*)

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

Theorem fold_left_map_log_prod_term {F : field} : ∀ u i x l,
  (∀ j, j ∈ l → 2 ≤ j)
  → fold_left f_add (map (log_prod_term (ls ls_one) u (S i)) l) x = x.
Proof.
intros * Hin.
revert i.
induction l as [| a l]; intros; [ easy | ].
cbn - [ ls_one ].
unfold log_prod_term at 2.
replace ls_one~{a} with f_zero. 2: {
  cbn.
  destruct a; [ easy | ].
  destruct a; [ exfalso | now destruct a ].
  specialize (Hin 1 (or_introl eq_refl)); flia Hin.
}
rewrite f_mul_0_l, f_add_0_r.
apply IHl.
intros j Hj.
now apply Hin; right.
Qed.

Theorem ls_mul_1_l {F : field} : ∀ r, (ls_one * r = r)%LS.
Proof.
intros * i Hi.
destruct i; [ easy | clear Hi ].
cbn - [ ls_one ].
unfold log_prod_term at 2.
replace ls_one~{1} with f_one by easy.
rewrite f_add_0_l, f_mul_1_l, Nat.div_1_r.
cbn - [ ls_one ].
apply fold_left_map_log_prod_term.
intros j Hj.
assert (H : ∀ s i f, 2 ≤ s → j ∈ filter f (seq s i) → 2 ≤ j). {
  clear; intros * Hs Hj.
  revert s j Hs Hj.
  induction i; intros; [ easy | ].
  cbn - [ "mod" ] in Hj.
  remember (f s) as m eqn:Hm; symmetry in Hm.
  destruct m. {
    cbn in Hj.
    destruct Hj as [Hj| Hj]; [ now subst s | ].
    apply (IHi (S s)); [ flia Hs | easy ].
  }
  apply (IHi (S s)); [ flia Hs | easy ].
}
eapply (H 2 i); [ easy | ].
apply Hj.
Qed.

Theorem divisor_iff : ∀ n,
  n ≠ 0 → ∀ d, d ∈ divisors n ↔ n mod d = 0 ∧ d ≠ 0.
Proof.
intros * Hn *.
unfold divisors, divisors_but_firstn_and_lastn.
split. {
  intros Hd.
  apply filter_In in Hd.
  destruct Hd as (Hd, Hnd).
  split; [ now apply Nat.eqb_eq | ].
  apply in_seq in Hd; flia Hd.
}
intros (Hnd, Hd).
apply filter_In.
split; [ | now apply Nat.eqb_eq ].
apply in_seq.
split; [ flia Hd | ].
apply Nat.mod_divides in Hnd; [ | easy ].
destruct Hnd as (c, Hc).
rewrite Nat.mul_comm in Hc; rewrite Hc.
destruct c; [ easy | ].
cbn; flia.
Qed.

Theorem List_last_seq : ∀ i n, n ≠ 0 → last (seq i n) 0 = i + n - 1.
Proof.
intros * Hn.
destruct n; [ easy | clear Hn ].
revert i; induction n; intros. {
  cbn; symmetry.
  apply Nat.add_sub.
}
remember (S n) as sn; cbn; subst sn.
remember (seq (S i) (S n)) as l eqn:Hl.
destruct l; [ easy | ].
rewrite Hl.
replace (i + S (S n)) with (S i + S n) by flia.
apply IHn.
Qed.

Theorem List_last_In {A} : ∀ (d : A) l, l ≠ [] → last l d ∈ l.
Proof.
intros * Hl.
destruct l as [| a l]; [ easy | clear Hl ].
revert a.
induction l as [| b l]; intros; [ now left | ].
remember (b :: l) as l'; cbn; subst l'.
right; apply IHl.
Qed.

Theorem List_last_app {A} : ∀ l (d a : A), List.last (l ++ [a]) d = a.
Proof.
intros.
induction l; [ easy | ].
cbn.
remember (l ++ [a]) as l' eqn:Hl'.
destruct l'; [ now destruct l | apply IHl ].
Qed.

Theorem eq_first_divisor_1 : ∀ n, n ≠ 0 → List.hd 0 (divisors n) = 1.
Proof.
intros.
now destruct n.
Qed.

Theorem eq_last_divisor : ∀ n, n ≠ 0 → List.last (divisors n) 0 = n.
Proof.
intros n Hn.
remember (divisors n) as l eqn:Hl.
symmetry in Hl.
unfold divisors, divisors_but_firstn_and_lastn in Hl.
rewrite Nat_sub_succ_1 in Hl.
specialize (List_last_seq 1 n Hn) as H1.
replace (1 + n - 1) with n in H1 by flia.
specialize (proj2 (filter_In (λ a, n mod a =? 0) n (seq 1 n))) as H2.
rewrite Hl in H2.
rewrite Nat.mod_same in H2; [ | easy ].
cbn in H2.
assert (H3 : n ∈ seq 1 n). {
  rewrite <- H1 at 1.
  apply List_last_In.
  now destruct n.
}
assert (H : n ∈ seq 1 n ∧ true = true) by easy.
specialize (H2 H); clear H.
assert (H : seq 1 n ≠ []); [ now intros H; rewrite H in H3 | ].
specialize (app_removelast_last 0 H) as H4; clear H.
rewrite H1 in H4.
assert (H : seq 1 n ≠ []); [ now intros H; rewrite H in H3 | ].
rewrite H4, filter_app in Hl; cbn in Hl.
rewrite Nat.mod_same in Hl; [ | easy ].
cbn in Hl; rewrite <- Hl.
apply List_last_app.
Qed.

Theorem first_last_divisor : ∀ n l,
  l = divisors n
  → List.hd 0 l = n / List.last l 0.
Proof.
intros * Hl.
subst l.
destruct n; [ easy | ].
rewrite eq_last_divisor; [ | easy ].
now rewrite Nat.div_same.
Qed.

Theorem List_filter_empty {A} : ∀ f (l : list A),
  filter f l = [] → ∀ a, a ∈ l → f a = false.
Proof.
intros * Hf a Ha.
revert a Ha.
induction l as [| b l]; intros; [ easy | ].
destruct Ha as [Ha| Ha]. {
  subst b; cbn in Hf.
  now destruct (f a).
}
apply IHl; [ | easy ].
cbn in Hf.
now destruct (f b).
Qed.

Theorem only_1_has_one_divisor : ∀ n, length (divisors n) = 1 → n = 1.
Proof.
intros * Hn.
remember (divisors n) as l eqn:Hl.
destruct l as [| a l]; [ easy | ].
destruct l as [| a2 l]; [ | easy ].
clear Hn; symmetry in Hl.
destruct n; [ easy | ].
destruct n; [ easy | exfalso ].
specialize (eq_first_divisor_1 (S (S n)) (Nat.neq_succ_0 _)) as H1.
rewrite Hl in H1; cbn in H1; subst a.
specialize (eq_last_divisor (S (S n)) (Nat.neq_succ_0 _)) as H1.
now rewrite Hl in H1.
Qed.

Theorem divisors_are_sorted : ∀ n, Sorted.Sorted lt (divisors n).
Proof.
intros.
unfold divisors, divisors_but_firstn_and_lastn.
rewrite Nat_sub_succ_1.
specialize (SetoidList.filter_sort eq_equivalence Nat.lt_strorder) as H2.
specialize (H2 Nat.lt_wd).
specialize (H2 (λ a, n mod a =? 0) (seq 1 n)).
now specialize (H2 (Sorted_Sorted_seq _ _)).
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

Definition smallest_divisor_after_1 n := List.hd 0 (List.tl (divisors n)).

Theorem smallest_divisor_is_prime :
  ∀ n, 2 ≤ n → is_prime (smallest_divisor_after_1 n) = true.
Proof.
intros * Hn.
unfold smallest_divisor_after_1.
remember (divisors n) as l eqn:Hl; symmetry in Hl.
destruct l as [| a l]. {
  destruct n; [ flia Hn | now destruct n ].
}
cbn.
assert (H : n ≠ 0) by flia Hn.
specialize (eq_first_divisor_1 n H) as H1; clear H.
rewrite Hl in H1; cbn in H1; subst a.
destruct l as [| a l]. {
  exfalso.
  specialize (only_1_has_one_divisor n) as H1.
  rewrite Hl in H1; cbn in H1.
  specialize (H1 eq_refl); subst n; flia Hn.
}
cbn.
apply Bool.not_false_is_true.
intros Ha.
specialize (divisors_are_sorted n) as Hls.
rewrite Hl in Hls.
specialize (not_prime_exists_div a) as H1.
assert (H : 2 ≤ a). {
  apply Sorted.Sorted_inv in Hls.
  destruct Hls as (_, Hls).
  now apply Sorted.HdRel_inv in Hls.
}
specialize (H1 H Ha) as (b & Hb & Hba); clear H.
assert (Hbn : b ∈ divisors n). {
  unfold divisors, divisors_but_firstn_and_lastn.
  rewrite Nat_sub_succ_1.
  apply List.filter_In.
  assert (Han : a ∈ divisors n) by now rewrite Hl; right; left.
  apply List.filter_In in Han.
  rewrite Nat_sub_succ_1 in Han.
  split. {
    apply List.in_seq.
    split; [ flia Hb | ].
    transitivity a; [ easy | ].
    destruct Han as (Han, _).
    now apply List.in_seq in Han.
  }
  destruct Han as (_, Han).
  apply Nat.eqb_eq in Han.
  apply Nat.eqb_eq.
  apply Nat.mod_divide in Han; [ | flia Hb ].
  apply Nat.mod_divide; [ flia Hb | ].
  now transitivity a.
}
rewrite Hl in Hbn.
cbn in Hbn.
destruct Hbn as [Hbn| Hbn]; [ flia Hbn Hb | ].
destruct Hbn as [Hbn| Hbn]; [ flia Hbn Hb | ].
apply Sorted.Sorted_inv in Hls.
destruct Hls as (Hls, _).
apply Sorted.Sorted_inv in Hls.
destruct Hls as (Hls, Hr).
clear - Hls Hr Hb Hbn.
induction l as [| c l]; [ easy | ].
cbn in Hbn.
destruct Hbn as [Hbn| Hbn]. {
  subst c.
  apply Sorted.HdRel_inv in Hr.
  flia Hr Hb.
}
apply IHl; [ | | easy ]. {
  now apply Sorted.Sorted_inv in Hls.
}
clear - Hls Hr.
destruct l as [| b l]; [ easy | ].
constructor.
specialize (@Sorted.HdRel_inv _ lt _ _ _ Hr) as H1.
transitivity c; [ easy | ].
apply Sorted.Sorted_inv in Hls.
destruct Hls as (_, Hls).
now apply Sorted.HdRel_inv in Hls.
Qed.

Fixpoint non_loop cnt n :=
  match cnt with
  | 0 => One
  | S cnt' =>
      match le_dec 2 n with
      | left P =>
          let d := smallest_divisor_after_1 n in
          let p := smallest_divisor_is_prime n P in
          Times d p (non_loop cnt' (n / d))
      | right _ => One
      end
  end.

Definition number_of_nat n := non_loop n n.

(*
Compute (number_of_nat 21).
Compute (number_of_nat 2).
Compute (number_of_nat 24).
Compute (number_of_nat 1001).
*)

(* end play *)

Theorem fold_log_prod_add_assoc {F : field} : ∀ a b l u v n,
  fold_left f_add (map (log_prod_term u v n) l) (a + b)%F =
  (fold_left f_add (map (log_prod_term u v n) l) a + b)%F.
Proof.
intros.
revert a b.
induction l as [| c l]; intros; [ easy | cbn ].
rewrite <- IHl; f_equal.
apply f_add_add_swap.
Qed.

(*
Theorem fold_log_prod_add_assoc {F : field} : ∀ a b l u v n,
  List.fold_right (log_prod_add u v n) (a + b)%F l =
  (List.fold_right (log_prod_add u v n) a l + b)%F.
Proof.
intros.
revert a b.
induction l as [| c l]; intros; [ easy | cbn ].
rewrite IHl.
unfold log_prod_add at 1 3.
do 2 rewrite <- f_add_assoc; f_equal.
apply f_add_comm.
Qed.

Theorem fold_log_prod_add_on_rev {F : field} : ∀ u v n l c,
  fold_right (log_prod_add u v n) c l =
  fold_right (log_prod_add u v n) c (List.rev l).
Proof.
intros.
revert c.
induction l as [| a l]; intros; [ easy | cbn ].
rewrite List.fold_right_app; cbn.
rewrite <- IHl.
unfold log_prod_add at 4; cbn.
unfold log_prod_add at 1.
symmetry; apply fold_log_prod_add_assoc.
Qed.
*)

Theorem fold_log_prod_add_on_rev {F : field} : ∀ u v n l,
  n ≠ 0
  → (∀ d, d ∈ l → n mod d = 0 ∧ d ≠ 0)
  → fold_left f_add (map (log_prod_term u v n) l) f_zero =
     fold_left f_add (map (log_prod_term v u n) (rev (map (λ i, n / i) l)))
       f_zero.
Proof.
intros * Hn Hd.
induction l as [| a l]; intros; [ easy | cbn ].
rewrite f_add_0_l.
rewrite List.map_app.
rewrite List.fold_left_app; cbn.
specialize (Hd a (or_introl eq_refl)) as H1.
destruct H1 as (H1, H2).
rewrite <- IHl.
-unfold log_prod_term at 2 4.
 rewrite Nat_mod_0_div_div; [ | | easy ]; cycle 1. {
   split; [ flia H2 | ].
   apply Nat.mod_divides in H1; [ | easy ].
   destruct H1 as (c, Hc).
   destruct c; [ now rewrite Nat.mul_comm in Hc | ].
   rewrite Hc, Nat.mul_comm; cbn; flia.
 }
 rewrite (f_mul_comm (v (n / a))).
 now rewrite <- fold_log_prod_add_assoc, f_add_0_l.
-intros d Hdl.
 now apply Hd; right.
Qed.

Theorem divisors_length_upper_bound : ∀ n, List.length (divisors n) ≤ n.
Proof.
intros.
unfold divisors, divisors_but_firstn_and_lastn.
rewrite Nat_sub_succ_1.
rewrite <- (List.seq_length n 1) at 2.
apply List_filter_length_upper_bound.
Qed.

Theorem divisor_inv : ∀ n d, d ∈ divisors n → n / d ∈ divisors n.
Proof.
intros * Hd.
apply List.filter_In in Hd.
apply List.filter_In.
destruct Hd as (Hd, Hm).
apply List.in_seq in Hd.
apply Nat.eqb_eq in Hm.
rewrite Nat_mod_0_mod_div; [ | flia Hd | easy ].
split; [ | easy ].
apply Nat.mod_divides in Hm; [ | flia Hd ].
destruct Hm as (m, Hm).
rewrite Hm at 1.
apply List.in_seq.
rewrite Nat.mul_comm, Nat.div_mul; [ | flia Hd ].
split.
+apply (Nat.mul_lt_mono_pos_l d); [ flia Hd | ].
 flia Hm Hd.
+rewrite Hm.
 destruct d; [ flia Hd | cbn; flia ].
Qed.

Theorem sorted_equiv_nat_lists : ∀ l l',
  Sorted.Sorted lt l
  → Sorted.Sorted lt l'
  → (∀ a, a ∈ l ↔ a ∈ l')
  → l = l'.
Proof.
intros * Hl Hl' Hll.
revert l' Hl' Hll.
induction l as [| a l]; intros. {
  destruct l' as [| a' l']; [ easy | ].
  now specialize (proj2 (Hll a') (or_introl eq_refl)) as H1.
}
destruct l' as [| a' l']. {
  now specialize (proj1 (Hll a) (or_introl eq_refl)) as H1.
}
assert (Hltt : Relations_1.Transitive lt). {
  intros x y z Hxy Hyz.
  now transitivity y.
}
assert (Haa : a = a'). {
  specialize (proj1 (Hll a) (or_introl eq_refl)) as H1.
  destruct H1 as [H1| H1]; [ easy | ].
  specialize (proj2 (Hll a') (or_introl eq_refl)) as H2.
  destruct H2 as [H2| H2]; [ easy | ].
  apply Sorted.Sorted_StronglySorted in Hl; [ | easy ].
  apply Sorted.Sorted_StronglySorted in Hl'; [ | easy ].
  inversion Hl; subst.
  inversion Hl'; subst.
  specialize (proj1 (Forall_forall (lt a) l) H4) as H7.
  specialize (proj1 (Forall_forall (lt a') l') H6) as H8.
  specialize (H7 _ H2).
  specialize (H8 _ H1).
  flia H7 H8.
}
subst a; f_equal.
apply IHl.
-now apply Sorted.Sorted_inv in Hl.
-now apply Sorted.Sorted_inv in Hl'.
-intros a; split; intros Ha.
 +specialize (proj1 (Hll _) (or_intror Ha)) as H1.
  destruct H1 as [H1| H1]; [ | easy ].
  subst a'.
  apply Sorted.Sorted_StronglySorted in Hl; [ | easy ].
  inversion Hl; subst.
  specialize (proj1 (Forall_forall (lt a) l) H2) as H3.
  specialize (H3 _ Ha); flia H3.
 +specialize (proj2 (Hll _) (or_intror Ha)) as H1.
  destruct H1 as [H1| H1]; [ | easy ].
  subst a'.
  apply Sorted.Sorted_StronglySorted in Hl'; [ | easy ].
  inversion Hl'; subst.
  specialize (proj1 (Forall_forall (lt a) l') H2) as H3.
  specialize (H3 _ Ha); flia H3.
Qed.

Theorem unicity_sorted_lists_with_prop : ∀ l l' P,
  Sorted.Sorted lt l
  → Sorted.Sorted lt l'
  → (∀ a, a ∈ l ↔ P a)
  → (∀ a, a ∈ l' ↔ P a)
  → l = l'.
Proof.
intros * Hl Hl' Hal Hal'.
assert (Hll : ∀ a, a ∈ l ↔ a ∈ l'). {
  intros; split; intros H.
  -now apply Hal', Hal.
  -now apply Hal, Hal'.
}
now apply sorted_equiv_nat_lists.
Qed.

Theorem sorted_gt_lt_rev : ∀ l, Sorted.Sorted gt l → Sorted.Sorted lt (rev l).
Proof.
intros l Hl.
induction l as [| a l]; [ constructor | cbn ].
apply (SetoidList.SortA_app eq_equivalence).
-now apply IHl; inversion Hl.
-now constructor.
-intros x y Hx Hy.
 apply SetoidList.InA_alt in Hy.
 destruct Hy as (z & Haz & Hza); subst z.
 destruct Hza; [ subst a | easy ].
 apply SetoidList.InA_rev in Hx.
 rewrite List.rev_involutive in Hx.
 apply SetoidList.InA_alt in Hx.
 destruct Hx as (z & Haz & Hza); subst z.
 apply Sorted.Sorted_inv in Hl.
 destruct Hl as (Hl, Hyl).
 clear IHl.
 induction Hyl; [ easy | ].
 destruct Hza as [Hx| Hx]; [ now subst x | ].
 transitivity b; [ clear H | easy ].
 assert (Hgtt : Relations_1.Transitive gt). {
   unfold gt.
   clear; intros x y z Hxy Hyz.
   now transitivity y.
 }
 apply Sorted.Sorted_StronglySorted in Hl; [ | easy ].
 inversion Hl; subst.
 specialize (proj1 (Forall_forall (gt b) l) H2) as H3.
 now apply H3.
Qed.

Theorem map_inv_divisors : ∀ n,
  divisors n = List.rev (List.map (λ i, n / i) (divisors n)).
Proof.
intros.
specialize (divisors_are_sorted n) as H1.
assert (H2 : Sorted.Sorted lt (rev (map (λ i : nat, n / i) (divisors n)))). {
  apply sorted_gt_lt_rev.
  destruct n; [ constructor | ].
  remember (divisors (S n)) as l eqn:Hl; symmetry in Hl.
  assert (H2 : ∀ d, d ∈ l → S n mod d = 0 ∧ d ≠ 0). {
    now intros d; subst l; apply divisor_iff.
  }
  clear Hl.
  induction l as [| a l]; [ constructor | ].
  cbn; constructor.
  -apply IHl; [ now inversion H1 | ].
   now intros d; intros Hd; apply H2; right.
  -clear IHl.
   revert a H1 H2.
   induction l as [| b l]; intros; [ constructor | ].
   cbn; constructor; unfold gt.
   apply Sorted.Sorted_inv in H1.
   destruct H1 as (_, H1).
   apply Sorted.HdRel_inv in H1.
   assert (Ha : a ≠ 0). {
     intros H; subst a.
     now specialize (H2 0 (or_introl eq_refl)) as H3.
   }
   assert (Hb : b ≠ 0). {
     intros H; subst b.
     now specialize (H2 0 (or_intror (or_introl eq_refl))) as H3.
   }
   specialize (Nat.div_mod (S n) a Ha) as H3.
   specialize (Nat.div_mod (S n) b Hb) as H4.
   specialize (H2 a (or_introl eq_refl)) as H.
   rewrite (proj1 H), Nat.add_0_r in H3; clear H.
   specialize (H2 b (or_intror (or_introl eq_refl))) as H.
   rewrite (proj1 H), Nat.add_0_r in H4; clear H.
   apply (Nat.mul_lt_mono_pos_l b); [ flia Hb | ].
   rewrite <- H4.
   apply (Nat.mul_lt_mono_pos_l a); [ flia Ha | ].
   rewrite (Nat.mul_comm _ (_ * _)), Nat.mul_shuffle0.
   rewrite <- Nat.mul_assoc, <- H3.
   apply Nat.mul_lt_mono_pos_r; [ flia | easy ].
}
apply sorted_equiv_nat_lists; [ easy | easy | ].
intros a.
split; intros Ha.
-apply List.in_rev; rewrite List.rev_involutive.
 destruct (zerop n) as [Hn| Hn]; [ now subst n | ].
 apply Nat.neq_0_lt_0 in Hn.
 specialize (proj1 (divisor_iff n Hn a) Ha) as (Hna, Haz).
 apply List.in_map_iff.
 exists (n / a).
 split; [ | now apply divisor_inv ].
 apply Nat_mod_0_div_div; [ | easy ].
 split; [ flia Haz | ].
 apply Nat.mod_divides in Hna; [ | easy ].
 destruct Hna as (c, Hc); subst n.
 destruct c; [ now rewrite Nat.mul_comm in Hn | ].
 rewrite Nat.mul_comm; cbn; flia.
-apply List.in_rev in Ha.
 destruct (zerop n) as [Hn| Hn]; [ now subst n | ].
 apply Nat.neq_0_lt_0 in Hn.
 apply divisor_iff; [ easy | ].
 apply List.in_map_iff in Ha.
 destruct Ha as (b & Hnb & Hb).
 subst a.
 apply divisor_iff; [ easy | ].
 now apply divisor_inv.
Qed.

Theorem divisors_symmetry : ∀ n k l,
  l = divisors n
  → k < List.length l
  → List.nth k l 0 * List.nth (List.length l - S k) l 0 = n.
Proof.
intros * Hl Hk.
specialize (map_inv_divisors n) as H1.
rewrite <- Hl in H1.
rewrite H1 at 3.
rewrite List.rev_nth; [ | rewrite List.map_length; flia Hk ].
rewrite List.map_length.
rewrite <- Nat.sub_succ_l; [ | easy ].
rewrite Nat.sub_succ.
rewrite Nat_sub_sub_distr; [ | flia Hk ].
rewrite Nat.sub_diag, Nat.add_0_l.
clear H1.
assert (Hn : n ≠ 0) by now intros H; subst n l.
assert (Hd : ∀ d, d ∈ l → n mod d = 0 ∧ d ≠ 0). {
  intros d Hd; apply divisor_iff; [ easy | now subst l ].
}
clear Hl.
revert l Hk Hd.
induction k; intros. {
  destruct l as [| a l]; [ easy | cbn ].
  specialize (Hd a (or_introl eq_refl)) as Ha.
  destruct Ha as (Hna, Haz).
  apply Nat.mod_divides in Hna; [ | easy ].
  destruct Hna as (c, Hc).
  rewrite Hc at 1.
  rewrite (Nat.mul_comm _ c).
  now rewrite Nat.div_mul.
}
destruct l as [| a l]; [ cbn in Hk; flia Hk | cbn ].
cbn in Hk; apply Nat.succ_lt_mono in Hk.
apply IHk; [ easy | ].
intros d Hdl.
now apply Hd; right.
Qed.

(*
Theorem fold_log_prod_add_first_last {F : field} : ∀ k n u v l,
  l = divisors n
  → fold_right (log_prod_add u v n) f_zero (firstn k l) =
     fold_right (log_prod_add v u n) f_zero (skipn (length l - k) l).
Proof.
intros * Hl.
...
intros * Hl.
symmetry in Hl.
destruct k. {
  cbn; rewrite Nat.sub_0_r.
  now rewrite List.skipn_all.
}
destruct l as [| a l]; [ easy | ].
assert (Hn : n ≠ 0) by now intros H; subst n.
specialize (eq_first_divisor_1 n Hn) as H1.
rewrite Hl in H1; cbn in H1; subst a.
cbn; unfold log_prod_add at 1.
rewrite Nat.div_1_r.
destruct (le_dec (length l) k) as [Hlk| Hlk]. {
  rewrite (proj2 (Nat.sub_0_le _ _)); [ | easy ].
  rewrite List.skipn_O.
  assert (H : 1 :: l ≠ []) by easy.
  specialize (app_removelast_last 0 H) as H1; clear H.
  rewrite List_removelast_firstn in H1.
  cbn - [ last ] in H1.
  rewrite Nat.sub_0_r in H1.
  rewrite <- Hl in H1.
  rewrite last_divisor in H1; [ | easy ].
  move H1 before Hl.
  rewrite <- Hl at 1; rewrite H1.
  rewrite List.fold_right_app; cbn.
  unfold log_prod_add at 3.
  rewrite f_add_0_l, (f_mul_comm (v n)).
  rewrite Nat.div_same; [ | easy ].
  remember (u 1 * v n)%F as x eqn:Hx.
  replace x with (f_zero + x)%F at 2 by now rewrite f_add_0_l.
  rewrite fold_log_prod_add_assoc; f_equal.
  rewrite List.firstn_all2; [ | easy ].
  clear k Hlk x Hx.
  destruct l as [| a l]; [ easy | ].
  assert (H : a :: l ≠ []) by easy.
  specialize (app_removelast_last 0 H) as H2; clear H.
  rewrite H2 in Hl.
  specialize (last_divisor _ Hn) as H3.
  rewrite Hl in H3.
  rewrite List.app_comm_cons in H3.
  rewrite List_last_app in H3.
  rewrite H3 in Hl, H2.
  rewrite H2 at 1.
  rewrite fold_right_app.
  cbn - [ removelast firstn ].
  unfold log_prod_add at 2.
  rewrite Hl.
  cbn - [ removelast ].
  unfold log_prod_add at 2.
  rewrite (f_mul_comm (v 1)).
  rewrite Nat.div_same; [ | easy ].
  rewrite Nat.div_1_r, f_add_0_l.
  rewrite <- H2.
  remember (u n * v 1)%F as x eqn:Hx.
  replace x with (f_zero + x)%F at 1 by now rewrite f_add_0_l.
  rewrite fold_log_prod_add_assoc; f_equal.
  clear x Hx.
  replace (firstn (length l) (a :: l)) with (removelast (a :: l)). 2: {
    clear; revert a; induction l as [| b l]; intros; [ easy | ].
    remember (b :: l) as l'; cbn; subst l'.
    now rewrite IHl.
  }
  remember (a :: l) as l'.
  clear a l Heql'; rename l' into l.
...
intros * Hl.
symmetry in Hl.
revert k n Hl.
induction l as [| a l]; intros; [ now destruct k | ].
cbn - [ "-" ].
assert (Hn : n ≠ 0) by now intros H; subst n.
specialize (eq_first_divisor_1 n Hn) as H1.
rewrite Hl in H1; cbn in H1; subst a.
assert (H : 1 :: l ≠ []) by easy.
specialize (app_removelast_last 0 H) as H1; clear H.
rewrite List_removelast_firstn in H1.
cbn - [ last ] in H1.
rewrite Nat.sub_0_r in H1.
rewrite <- Hl in H1.
rewrite last_divisor in H1; [ | easy ].
move H1 before Hl.
rewrite <- Hl at 1; rewrite H1.
rewrite List.firstn_app.
rewrite List.firstn_firstn.
rewrite List.firstn_length.
rewrite Hl at 2.
rewrite (Nat.min_l (length l)); [ | cbn; flia ].
rewrite fold_right_app.
destruct k. {
  rewrite Nat.sub_0_r, Nat.sub_0_l.
  now cbn; rewrite List.skipn_all.
}
rewrite Nat.sub_succ.
...
*)

Theorem fold_log_prod_comm {F : field} : ∀ u v i,
  fold_left f_add (log_prod_list u v i) f_zero =
  fold_left f_add (log_prod_list v u i) f_zero.
Proof.
intros u v n.
unfold log_prod_list.
rewrite map_inv_divisors at 2.
remember (divisors n) as l eqn:Hl; symmetry in Hl.
destruct (zerop n) as [Hn| Hn]; [ now subst n; cbn in Hl; subst l | ].
apply Nat.neq_0_lt_0 in Hn.
assert (Hd : ∀ d, d ∈ l → n mod d = 0 ∧ d ≠ 0). {
  intros d Hd; apply divisor_iff; [ easy | now subst l ].
}
now apply fold_log_prod_add_on_rev.
Qed.

(*
Theorem fold_log_prod_comm {F : field} : ∀ u v i,
  fold_right (log_prod_add u v i) f_zero (divisors i) =
  fold_right (log_prod_add v u i) f_zero (divisors i).
Proof.
intros u v n.
rewrite map_inv_divisors at 2.
symmetry; rewrite <- fold_log_prod_add_on_rev at 1; symmetry.
remember (divisors n) as l eqn:Hl; symmetry in Hl.
destruct (zerop n) as [Hn| Hn]; [ now subst n; cbn in Hl; subst l | ].
apply Nat.neq_0_lt_0 in Hn.
assert (Hd : ∀ d, d ∈ l → n mod d = 0 ∧ d ≠ 0). {
  intros d Hd; apply divisor_iff; [ easy | now subst l ].
}
clear Hl.
induction l as [| a l]; [ easy | cbn ].
rewrite <- IHl. 2: {
  intros d Hdl.
  now apply Hd; right.
}
unfold log_prod_add; f_equal.
rewrite f_mul_comm; f_equal; f_equal.
specialize (Hd a (or_introl eq_refl)) as (Hna, Ha).
symmetry; apply Nat_mod_0_div_div; [ | easy ].
split; [ flia Ha | ].
apply Nat.mod_divides in Hna; [ | easy ].
destruct Hna as (c, Hc); subst n.
destruct c; [ now rewrite Nat.mul_comm in Hn | ].
rewrite Nat.mul_comm; cbn; flia.
Qed.
*)

Theorem log_prod_comm {F : field} : ∀ u v i,
  log_prod u v i = log_prod v u i.
Proof.
intros.
unfold log_prod.
apply fold_log_prod_comm.
Qed.

Theorem divisors_1 : divisors 1 = [1].
Proof. easy. Qed.

Theorem log_prod_assoc {F : field} : ∀ u v w i,
  i ≠ 0
  → log_prod u (log_prod v w) i = log_prod (log_prod u v) w i.
Proof.
intros * Hi.
unfold log_prod at 1 3.
remember (divisors i) as l eqn:Hl; symmetry in Hl.
...
destruct l as [| a l]; [ easy | ].
specialize (eq_first_divisor_1 i Hi) as H1.
rewrite Hl in H1; cbn in H1; subst a; cbn.
unfold log_prod_add at 1 3.
rewrite Nat.div_1_r.
unfold log_prod at 2 4.
rewrite divisors_1.
cbn - [ divisors ].
unfold log_prod_add at 4.
rewrite f_add_0_l, Nat.div_1_r.
Print log_prod_add.
...

(* other solution, if log_prod_assoc above does not work *)
Theorem log_prod_prod_swap {F : field} : ∀ u v w i,
  i ≠ 0
  → log_prod (log_prod u v) w i = log_prod (log_prod u w) v i.
Proof.
intros * Hi.
unfold log_prod at 1 3.
remember (divisors i) as l eqn:Hl; symmetry in Hl.
destruct l as [| a l]; [ easy | cbn ].
unfold log_prod_add at 1 3.
...
unfold log_prod at 2 4.
...

Theorem log_prod_assoc {F : field} : ∀ u v w i,
  i ≠ 0
  → log_prod u (log_prod v w) i = log_prod (log_prod u v) w i.
Proof.
intros * Hi.
rewrite log_prod_comm.
rewrite log_prod_prod_swap; [ | easy ].
unfold log_prod at 1 3.
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
