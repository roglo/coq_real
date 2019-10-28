(* playing with prime numbers, as a break *)

Set Nested Proofs Allowed.
Require Import Utf8 Arith Psatz Setoid Morphisms.
Require Import Sorting.Permutation.
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

Theorem List_map_map_map {A B C D} : ∀ (f : A → B → C) (g : A → D → B) h l,
  map (λ d, map (f d) (map (g d) (h d))) l =
  map (λ d, map (λ x, (f d (g d x))) (h d)) l.
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
now rewrite List.map_map, IHl.
Qed.

Theorem List_flat_map_length {A B} : ∀ (l : list A) (f : _ → list B),
  length (flat_map f l) =
    List.fold_right Nat.add 0 (map (@length B) (map f l)).
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
now rewrite app_length, IHl.
Qed.

Theorem List_in_app_cons_in_cons_app {A} : ∀ l1 l2 a (b : A),
  List.In b (l1 ++ a :: l2) ↔ List.In b (a :: l1 ++ l2).
Proof.
intros t; split; intros Ht. {
  apply List.in_app_or in Ht.
  rewrite List.app_comm_cons.
  apply List.in_or_app.
  destruct Ht as [Ht| Ht]; [ now left; right | ].
  destruct Ht as [Ht| Ht]; [ now left; left | now right ].
}
apply List.in_or_app.
rewrite List.app_comm_cons in Ht.
apply List.in_app_or in Ht.
destruct Ht as [Ht| Ht]. {
  destruct Ht as [Ht| Ht]; [ now right; left | now left ].
}
now right; right.
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

Theorem Sorted_Sorted_lt_app_not_in_l : ∀ a l1 l2,
  Sorted.Sorted lt (l1 ++ a :: l2)
  → not (List.In a l1).
Proof.
intros * Hs Ha.
apply Sorted.Sorted_StronglySorted in Hs; [ | apply Nat.lt_strorder ].
induction l1 as [| b l]; [ easy | cbn ].
destruct Ha as [Ha| Ha]. {
  subst b.
  clear IHl.
  cbn in Hs.
  induction l as [| b l]; intros. {
    cbn in Hs.
    apply Sorted.StronglySorted_inv in Hs.
    destruct Hs as (_, Hr).
    apply Forall_inv in Hr; flia Hr.
  }
  apply IHl.
  apply Sorted.StronglySorted_inv in Hs.
  destruct Hs as (Hs, Hr).
  cbn in Hs, Hr.
  constructor. {
    now apply Sorted.StronglySorted_inv in Hs.
  }
  now apply Forall_inv_tail in Hr.
}
apply IHl; [ | easy ].
cbn in Hs.
now apply Sorted.StronglySorted_inv in Hs.
Qed.

Theorem Sorted_Sorted_lt_app_not_in_r : ∀ a l1 l2,
  Sorted.Sorted lt (l1 ++ a :: l2)
  → not (List.In a l2).
Proof.
intros * Hs Ha.
apply Sorted.Sorted_StronglySorted in Hs; [ | apply Nat.lt_strorder ].
induction l1 as [| b l]. {
  cbn in Hs.
  apply Sorted.StronglySorted_inv in Hs.
  destruct Hs as (Hs, Hr).
  specialize (proj1 (Forall_forall _ _) Hr) as H1.
  specialize (H1 _ Ha); flia H1.
}
cbn in Hs.
apply Sorted.StronglySorted_inv in Hs.
now apply IHl.
Qed.

Theorem NoDup_app_comm {A} : ∀ l l' : list A,
  NoDup (l ++ l') → NoDup (l' ++ l).
Proof.
intros * Hll.
revert l Hll.
induction l' as [| a l']; intros; [ now rewrite app_nil_r in Hll | ].
cbn; constructor. {
  intros Ha.
  apply NoDup_remove_2 in Hll; apply Hll.
  apply in_app_or in Ha.
  apply in_or_app.
  now destruct Ha; [ right | left ].
}
apply IHl'.
now apply NoDup_remove_1 in Hll.
Qed.

Theorem List_in_app_app_swap {A} : ∀ (a : A) l1 l2 l3,
  In a (l1 ++ l3 ++ l2)
  → In a (l1 ++ l2 ++ l3).
Proof.
intros * Hin.
revert l2 l3 Hin.
induction l1 as [| a2 l1]; intros. {
  cbn in Hin; cbn.
  apply in_app_or in Hin.
  apply in_or_app.
  now destruct Hin; [ right | left ].
}
cbn in Hin; cbn.
destruct Hin as [Hin| Hin]; [ now left | right ].
now apply IHl1.
Qed.

Theorem NoDup_app_app_swap {A} : ∀ l1 l2 l3 : list A,
  NoDup (l1 ++ l2 ++ l3) → NoDup (l1 ++ l3 ++ l2).
Proof.
intros * Hlll.
revert l2 l3 Hlll.
induction l1 as [| a1 l1]; intros; [ now cbn; apply NoDup_app_comm | ].
cbn; constructor. {
  intros Hin.
  cbn in Hlll.
  apply NoDup_cons_iff in Hlll.
  destruct Hlll as (Hin2, Hlll).
  apply Hin2; clear Hin2.
  now apply List_in_app_app_swap.
}
apply IHl1.
cbn in Hlll.
now apply NoDup_cons_iff in Hlll.
Qed.

Theorem NoDup_app_lr {A} : ∀ l1 l2 : list A,
  NoDup (l1 ++ l2) → NoDup l1 ∧ NoDup l2.
Proof.
intros * Hll.
split. {
  induction l2 as [| a2 l2]; intros; [ now rewrite app_nil_r in Hll | ].
  apply NoDup_remove_1 in Hll.
  now apply IHl2.
}
induction l2 as [| a2 l2]; [ constructor | ].
constructor. {
  intros H.
  apply NoDup_remove_2 in Hll; apply Hll.
  now apply in_or_app; right.
}
apply NoDup_remove_1 in Hll.
now apply IHl2.
Qed.

Theorem NoDup_concat_rev {A} : ∀ (ll : list (list A)),
  NoDup (concat (rev ll)) → NoDup (concat ll).
Proof.
intros * Hll.
destruct ll as [| l ll]; [ easy | ].
cbn; cbn in Hll.
rewrite concat_app in Hll; cbn in Hll.
rewrite app_nil_r in Hll.
apply NoDup_app_comm.
revert l Hll.
induction ll as [| l' ll]; intros; [ easy | ].
cbn in Hll; cbn.
rewrite concat_app in Hll; cbn in Hll.
rewrite app_nil_r, <- app_assoc in Hll.
rewrite <- app_assoc.
apply NoDup_app_app_swap.
rewrite app_assoc.
apply NoDup_app_comm.
now apply IHll.
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

Theorem prime_test_mod_ne_0 : ∀ n k,
  2 ≤ n
  → prime_test (n - k) n k = true
  → ∀ d, k ≤ d < n → n mod d ≠ 0.
Proof.
intros * Hn Hp d Hd.
remember (n - k) as cnt eqn:Hcnt; symmetry in Hcnt.
revert n k d Hn Hcnt Hp Hd.
induction cnt; intros; [ flia Hcnt Hd | ].
cbn in Hp.
remember (n mod k) as m eqn:Hm; symmetry in Hm.
destruct m; [ easy | ].
destruct n; [ flia Hcnt | ].
destruct (Nat.eq_dec k d) as [Hkd| Hkd]. {
  now intros H; rewrite Hkd, H in Hm.
}
apply (IHcnt (S n) (k + 1)); [ easy | flia Hcnt | easy | flia Hd Hkd ].
Qed.

Theorem prime_divisors : ∀ p,
  is_prime p = true → ∀ a, Nat.divide a p → a = 1 ∨ a = p.
Proof.
intros * Hp a * Hap.
unfold is_prime in Hp.
destruct (lt_dec p 2) as [Hp2| Hp2]. {
  destruct p; [ easy | ].
  destruct p; [ easy | flia Hp2 ].
}
apply Nat.nlt_ge in Hp2.
destruct (zerop a) as [Ha| Ha]. {
  subst a.
  apply Nat.divide_0_l in Hap; flia Hap Hp2.
}
apply Nat.neq_0_lt_0 in Ha.
apply Nat.mod_divide in Hap; [ | easy ].
apply Nat.mod_divides in Hap; [ | easy ].
destruct Hap as (k, Hk).
symmetry in Hk.
destruct p; [ easy | ].
destruct p; [ easy | ].
specialize (prime_test_mod_ne_0 (S (S p)) 2 Hp2) as H1.
replace (S (S p) - 2) with p in H1 by flia.
specialize (H1 Hp).
destruct k; [ now rewrite Nat.mul_0_r in Hk | ].
destruct k; [ now rewrite Nat.mul_1_r in Hk; right | left ].
destruct a; [ easy | ].
destruct a; [ easy | exfalso ].
specialize (H1 (S (S k))) as H2.
assert (H : 2 ≤ S (S k) < S (S p)). {
  split; [ flia Hp2 | rewrite <- Hk; cbn; flia ].
}
specialize (H2 H); clear H.
apply H2; rewrite <- Hk.
now rewrite Nat.mod_mul.
Qed.

Theorem eq_primes_gcd_1 : ∀ a b,
  is_prime a = true → is_prime b = true → a ≠ b
  → Nat.gcd a b = 1.
Proof.
intros p q Hp Hq Hpq.
specialize (prime_divisors _ Hp) as Hpp.
specialize (prime_divisors _ Hq) as Hqp.
specialize (Hpp (Nat.gcd p q) (Nat.gcd_divide_l _ _)) as H1.
specialize (Hqp (Nat.gcd p q) (Nat.gcd_divide_r _ _)) as H2.
destruct H1 as [H1| H1]; [ easy | ].
destruct H2 as [H2| H2]; [ easy | ].
now rewrite H1 in H2.
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
Notation "x '∉' l" := (¬ List.In x l) (at level 60).

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

Theorem in_divisors : ∀ n,
  n ≠ 0 → ∀ d, d ∈ divisors n → n mod d = 0 ∧ d ≠ 0.
Proof.
intros * Hn *.
unfold divisors, divisors_but_firstn_and_lastn.
intros Hd.
apply filter_In in Hd.
destruct Hd as (Hd, Hnd).
split; [ now apply Nat.eqb_eq | ].
apply in_seq in Hd; flia Hd.
Qed.

(* allows to rewrite H1, H2 with
      H1 : s1 = s3
      H2 : s2 = s4
   in expression
      (s1 * s2)%F
   changing it into
      (s3 * s4)%F *)
Instance ls_mul_morph {F : field} :
  Proper (ls_eq ==> ls_eq ==> ls_eq) ls_mul.
Proof.
intros s1 s2 Hs12 s'1 s'2 Hs'12 n Hn.
cbn - [ log_prod ].
unfold log_prod, log_prod_list; f_equal.
specialize (in_divisors n Hn) as Hd.
remember (divisors n) as l eqn:Hl; clear Hl.
induction l as [| a l]; [ easy | cbn ].
rewrite IHl; [ | now intros d Hdl; apply Hd; right ].
f_equal.
unfold log_prod_term.
specialize (Hd a (or_introl eq_refl)) as Ha.
destruct Ha as (Hna, Ha).
rewrite Hs12; [ | easy ].
rewrite Hs'12; [ easy | ].
apply Nat.mod_divides in Hna; [ | easy ].
destruct Hna as (c, Hc).
rewrite Hc, Nat.mul_comm, Nat.div_mul; [ | easy ].
now intros H; rewrite Hc, H, Nat.mul_0_r in Hn.
Qed.

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
destruct ((i + 1) mod y); [ easy | ].
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

Theorem in_divisors_iff : ∀ n,
  n ≠ 0 → ∀ d, d ∈ divisors n ↔ n mod d = 0 ∧ d ≠ 0.
Proof.
intros * Hn *.
unfold divisors, divisors_but_firstn_and_lastn.
split; [ now apply in_divisors | ].
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

Theorem fold_f_add_assoc {F : field} : ∀ a b l,
  fold_left f_add l (a + b)%F = (fold_left f_add l a + b)%F.
Proof.
intros.
revert a.
induction l as [| c l]; intros; [ easy | cbn ].
rewrite <- IHl; f_equal.
apply f_add_add_swap.
Qed.

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
 now rewrite <- fold_f_add_assoc, f_add_0_l.
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
  specialize (in_divisors (S n) (Nat.neq_succ_0 _)) as H2.
  remember (divisors (S n)) as l eqn:Hl; symmetry in Hl.
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
 specialize (in_divisors n Hn a Ha) as (Hna, Haz).
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
 apply in_divisors_iff; [ easy | ].
 apply List.in_map_iff in Ha.
 destruct Ha as (b & Hnb & Hb).
 subst a.
 apply in_divisors; [ easy | ].
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
specialize (in_divisors n Hn) as Hd; rewrite <- Hl in Hd.
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
specialize (in_divisors n Hn) as Hd; rewrite Hl in Hd.
now apply fold_log_prod_add_on_rev.
Qed.

Theorem log_prod_comm {F : field} : ∀ u v i,
  log_prod u v i = log_prod v u i.
Proof.
intros.
unfold log_prod.
apply fold_log_prod_comm.
Qed.

Theorem divisors_1 : divisors 1 = [1].
Proof. easy. Qed.

Theorem f_mul_fold_add_distr_l {F : field} : ∀ a b l,
  (a * fold_left f_add l b)%F =
  (fold_left f_add (map (f_mul a) l) (a * b)%F).
Proof.
intros.
revert a b.
induction l as [| c l]; intros; [ easy | cbn ].
rewrite <- f_mul_add_distr_l.
apply IHl.
Qed.

Theorem f_mul_fold_add_distr_r {F : field} : ∀ a b l,
  (fold_left f_add l a * b)%F =
  (fold_left f_add (map (f_mul b) l) (a * b)%F).
Proof.
intros.
revert a b.
induction l as [| c l]; intros; [ easy | cbn ].
rewrite (f_mul_comm b).
rewrite <- f_mul_add_distr_r.
apply IHl.
Qed.

Theorem map_f_mul_fold_add_distr_l {F : field} : ∀ (a : nat → f_type) b f l,
  map (λ i, (a i * fold_left f_add (f i) b)%F) l =
  map (λ i, fold_left f_add (map (f_mul (a i)) (f i)) (a i * b)%F) l.
Proof.
intros a b.
induction l as [| c l]; [ easy | cbn ].
rewrite f_mul_fold_add_distr_l; f_equal.
apply IHl.
Qed.

Theorem map_f_mul_fold_add_distr_r {F : field} : ∀ a (b : nat → f_type) f l,
  map (λ i, (fold_left f_add (f i) a * b i)%F) l =
  map (λ i, fold_left f_add (map (f_mul (b i)) (f i)) (a * b i)%F) l.
Proof.
intros a b.
induction l as [| c l]; [ easy | cbn ].
rewrite f_mul_fold_add_distr_r; f_equal.
apply IHl.
Qed.

Theorem fold_add_add {F : field} : ∀ a a' l l',
  (fold_left f_add l a + fold_left f_add l' a')%F =
  fold_left f_add (l ++ l') (a + a')%F.
Proof.
intros.
revert a.
induction l as [| b l]; intros; cbn. {
  rewrite f_add_comm, (f_add_comm _ a').
  symmetry; apply fold_f_add_assoc.
}
rewrite IHl.
now rewrite f_add_add_swap.
Qed.

Theorem fold_add_map_fold_add {F : field} : ∀ (f : nat → _) a b l,
  List.fold_left f_add (List.map (λ i, List.fold_left f_add (f i) (a i)) l)
    b =
  List.fold_left f_add (List.flat_map (λ i, a i :: f i) l)
    b.
Proof.
intros.
induction l as [| c l]; [ easy | cbn ].
rewrite fold_f_add_assoc.
rewrite fold_f_add_assoc.
rewrite IHl, f_add_comm.
rewrite fold_add_add.
rewrite (f_add_comm _ b).
now rewrite fold_f_add_assoc.
Qed.

Theorem map_mul_triplet {F : field} : ∀ u v w (f g h : nat → nat → nat) k l a,
  fold_left f_add
    (flat_map
       (λ d, map (λ d', (u (f d d') * v (g d d') * w (h d d')))%F (k d)) l)
    a =
  fold_left f_add
    (map (λ t, let '(i, j, k) := t in (u i * v j * w k)%F)
      (flat_map
         (λ d, map (λ d', (f d d', g d d', h d d')) (k d)) l))
    a.
Proof.
intros.
revert a.
induction l as [| b l]; intros; [ easy | cbn ].
rewrite map_app.
do 2 rewrite fold_left_app.
rewrite IHl; f_equal; clear.
remember (k b) as l eqn:Hl; clear Hl.
revert a b.
induction l as [| c l]; intros; [ easy | cbn ].
apply IHl.
Qed.

Theorem rev_concat_map {A B} : ∀ (f : A → list B) l,
  rev (concat (map f l)) = concat (map (@rev B) (map f (rev l))).
Proof.
intros.
induction l as [| a l]; [ easy | cbn ].
rewrite rev_app_distr.
rewrite IHl.
rewrite map_app; cbn.
rewrite map_app; cbn.
rewrite concat_app; cbn.
now rewrite app_nil_r.
Qed.

Definition xyz_zxy '((x, y, z) : (nat * nat * nat)) := (z, x, y).

Theorem mul_assoc_indices_eq : ∀ n,
  flat_map (λ d, map (λ d', (d, d', n / d / d')) (divisors (n / d))) (divisors n) =
  map xyz_zxy (flat_map (λ d, map (λ d', (d', d / d', n / d)) (divisors d)) (rev (divisors n))).
Proof.
intros.
destruct (zerop n) as [Hn| Hn]; [ now rewrite Hn | ].
apply Nat.neq_0_lt_0 in Hn.
do 2 rewrite flat_map_concat_map.
rewrite map_rev.
rewrite (map_inv_divisors n) at 2.
rewrite <- map_rev.
rewrite rev_involutive.
rewrite map_map.
rewrite concat_map.
rewrite map_map.
f_equal.
specialize (in_divisors n Hn) as Hin.
remember (divisors n) as l eqn:Hl; clear Hl.
induction l as [| a l]; [ easy | ].
cbn - [ divisors ].
rewrite IHl. 2: {
  intros * Hd.
  now apply Hin; right.
}
f_equal.
rewrite Nat_mod_0_div_div; cycle 1. {
  specialize (Hin a (or_introl eq_refl)) as (H1, H2).
  split; [ flia H2 | ].
  apply Nat.mod_divides in H1; [ | easy ].
  destruct H1 as (c, Hc); rewrite Hc.
  destruct c; [ now rewrite Hc, Nat.mul_comm in Hn | ].
  rewrite Nat.mul_comm; cbn; flia.
} {
  apply (Hin a (or_introl eq_refl)).
}
now rewrite map_map.
Qed.

Definition compare_trip '(i1, j1, k1) '(i2, j2, k2) :=
  match Nat.compare i1 i2 with
  | Eq =>
      match Nat.compare j1 j2 with
      | Eq => Nat.compare k1 k2
      | c => c
      end
  | c => c
  end.
Definition lt_triplet t1 t2 := compare_trip t1 t2 = Lt.

Theorem StrictOrder_lt_triplet : StrictOrder lt_triplet.
Proof.
constructor.
-intros ((i, j), k) H.
 unfold lt_triplet, compare_trip in H.
 now do 3 rewrite Nat.compare_refl in H.
-unfold lt_triplet, compare_trip.
 intros ((a1, a2), a3) ((b1, b2), b3) ((c1, c2), c3) Hab Hbc.
 remember (a1 ?= b1) as ab1 eqn:Hab1; symmetry in Hab1.
 remember (a1 ?= c1) as ac1 eqn:Hac1; symmetry in Hac1.
 remember (b1 ?= c1) as bc1 eqn:Hbc1; symmetry in Hbc1.
 remember (a2 ?= b2) as ab2 eqn:Hab2; symmetry in Hab2.
 remember (b2 ?= c2) as bc2 eqn:Hbc2; symmetry in Hbc2.
 remember (a2 ?= c2) as ac2 eqn:Hac2; symmetry in Hac2.
 move ac2 before ab1; move bc2 before ab1; move ab2 before ab1.
 move bc1 before ab1; move ac1 before ab1.
 destruct ab1; [ | | easy ].
 +apply Nat.compare_eq_iff in Hab1; subst b1.
  destruct ab2; [ | | easy ].
  *apply Nat.compare_eq_iff in Hab2; subst b2.
   apply Nat.compare_lt_iff in Hab.
   destruct bc1; [ | | easy ].
  --apply Nat.compare_eq_iff in Hbc1; subst c1.
    rewrite <- Hac1, Nat.compare_refl.
    destruct bc2; [ | | easy ].
   ++apply Nat.compare_eq_iff in Hbc2; subst c2.
     apply Nat.compare_lt_iff in Hbc.
     rewrite <- Hac2, Nat.compare_refl.
     apply Nat.compare_lt_iff.
     now transitivity b3.
   ++apply Nat.compare_lt_iff in Hbc2.
     destruct ac2; [ | easy | ].
    **apply Nat.compare_eq_iff in Hac2; subst c2.
      flia Hbc2.
    **apply Nat.compare_gt_iff in Hac2.
      flia Hbc2 Hac2.
  --apply Nat.compare_lt_iff in Hbc1.
    destruct ac1; [ | easy | ].
   **apply Nat.compare_eq_iff in Hac1; flia Hbc1 Hac1.
   **apply Nat.compare_gt_iff in Hac1; flia Hbc1 Hac1.
  *destruct bc1; [ | | easy ].
  --apply Nat.compare_eq_iff in Hbc1; subst c1.
    destruct bc2; [ | | easy ].
   ++apply Nat.compare_eq_iff in Hbc2; subst c2.
     rewrite <- Hac2, Hab2.
     destruct ac1; [ easy | easy | ].
     now rewrite Nat.compare_refl in Hac1.
   ++apply Nat.compare_lt_iff in Hab2.
     apply Nat.compare_lt_iff in Hbc2.
     destruct ac1; [ | easy | ].
    **destruct ac2; [ | easy | ].
    ---apply Nat.compare_eq_iff in Hac2; subst c2.
       flia Hab2 Hbc2.
    ---apply Nat.compare_gt_iff in Hac2.
       flia Hab2 Hbc2 Hac2.
    **now rewrite Nat.compare_refl in Hac1.
  --now rewrite <- Hac1, Hbc1.
 +destruct ac1; [ | easy | ].
  *apply Nat.compare_eq_iff in Hac1; subst c1.
   destruct ac2; [ | easy | ].
  --apply Nat.compare_eq_iff in Hac2; subst c2.
    destruct bc1; [ | | easy ].
   ++apply Nat.compare_eq_iff in Hbc1; subst b1.
     now rewrite Nat.compare_refl in Hab1.
   ++apply Nat.compare_lt_iff in Hab1.
     apply Nat.compare_lt_iff in Hbc1.
     flia Hab1 Hbc1.
  --destruct bc1; [ | | easy ].
   ++apply Nat.compare_eq_iff in Hbc1; subst b1.
     now rewrite Nat.compare_refl in Hab1.
   ++apply Nat.compare_lt_iff in Hab1.
     apply Nat.compare_lt_iff in Hbc1.
     flia Hab1 Hbc1.
  *destruct bc1; [ | | easy ].
  --apply Nat.compare_eq_iff in Hbc1; subst c1.
    now rewrite Hac1 in Hab1.
  --apply Nat.compare_lt_iff in Hab1.
    apply Nat.compare_lt_iff in Hbc1.
    apply Nat.compare_gt_iff in Hac1.
    flia Hab1 Hbc1 Hac1.
Qed.

Theorem Permutation_f_sum_add {F : field} {A} : ∀ (l1 l2 : list A) f a,
  Permutation l1 l2
  → fold_left f_add (map f l1) a =
     fold_left f_add (map f l2) a.
Proof.
intros * Hperm.
induction Hperm using Permutation_ind; [ easy | | | ]. {
  cbn; do 2 rewrite fold_f_add_assoc.
  now rewrite IHHperm.
} {
  now cbn; rewrite f_add_add_swap.
}
etransitivity; [ apply IHHperm1 | apply IHHperm2 ].
Qed.

Theorem fold_add_flat_prod_assoc {F : field} : ∀ n u v w,
  n ≠ 0
  → fold_left f_add
       (flat_map (λ d, map (f_mul (u d)) (log_prod_list v w (n / d)))
          (divisors n))
       f_zero =
     fold_left f_add
       (flat_map (λ d, map (f_mul (w (n / d))) (log_prod_list u v d))
          (divisors n))
       f_zero.
Proof.
intros * Hn.
do 2 rewrite flat_map_concat_map.
unfold log_prod_list.
do 2 rewrite List_map_map_map.
unfold log_prod_term.
assert (H : ∀ f l,
  map (λ d, map (λ d', (u d * (v d' * w (n / d / d')))%F) (f d)) l =
  map (λ d, map (λ d', (u d * v d' * w (n / d / d'))%F) (f d)) l). {
  intros.
  induction l as [| a l]; [ easy | cbn ].
  rewrite IHl; f_equal; clear.
  induction (f a) as [| b l]; [ easy | cbn ].
  rewrite IHl; f_equal.
  apply f_mul_assoc.
}
rewrite H; clear H.
assert (H : ∀ f l,
  map (λ d, map (λ d', (w (n / d) * (u d' * v (d / d')))%F) (f d)) l =
  map (λ d, map (λ d', (u d' * v (d / d') * w (n / d))%F) (f d)) l). {
  intros.
  induction l as [| a l]; [ easy | cbn ].
  rewrite IHl; f_equal; clear.
  induction (f a) as [| b l]; [ easy | cbn ].
  rewrite IHl; f_equal.
  apply f_mul_comm.
}
rewrite H; clear H.
do 2 rewrite <- flat_map_concat_map.
do 2 rewrite map_mul_triplet.
remember (
  flat_map (λ d, map (λ d', (d, d', n / d / d')) (divisors (n / d)))
    (divisors n))
  as l1 eqn:Hl1.
remember (
  flat_map (λ d, map (λ d', (d', d / d', n / d)) (divisors d))
    (divisors n))
  as l2 eqn:Hl2.
move l2 before l1.
assert (H1 : ∀ d1 d2 d3, d1 * d2 * d3 = n ↔ (d1, d2, d3) ∈ l1). {
  split; intros Huvw.
  -intros.
   assert (Hd1 : d1 ≠ 0) by now intros H; rewrite <- Huvw, H in Hn.
   assert (Hd2 : d2 ≠ 0). {
     now intros H; rewrite <- Huvw, H, Nat.mul_0_r in Hn.
   }
   assert (Hd3 : d3 ≠ 0). {
     now intros H; rewrite <- Huvw, H, Nat.mul_comm in Hn.
   }
   subst l1.
   apply in_flat_map.
   exists d1.
   split. {
     apply in_divisors_iff; [ easy | ].
     split; [ | easy ].
     rewrite <- Huvw.
     apply Nat.mod_divides; [ easy | ].
     exists (d2 * d3).
     symmetry; apply Nat.mul_assoc.
   }
   apply List.in_map_iff.
   exists d2.
   rewrite <- Huvw.
   rewrite <- Nat.mul_assoc, Nat.mul_comm.
   rewrite Nat.div_mul; [ | easy ].
   rewrite Nat.mul_comm.
   rewrite Nat.div_mul; [ | easy ].
   split; [ easy | ].
   apply in_divisors_iff; [ now apply Nat.neq_mul_0 | ].
   split; [ | easy ].
   apply Nat.mod_divides; [ easy | ].
   exists d3; apply Nat.mul_comm.
  -subst l1.
   apply List.in_flat_map in Huvw.
   destruct Huvw as (d & Hd & Hdi).
   apply List.in_map_iff in Hdi.
   destruct Hdi as (d' & Hd' & Hdd).
   apply in_divisors in Hd; [ | easy ].
   destruct Hd as (Hnd, Hd).
   injection Hd'; clear Hd'; intros Hw Hv Hu.
   subst d1 d2 d3.
   apply Nat.mod_divides in Hnd; [ | easy ].
   destruct Hnd as (d1, Hd1).
   rewrite Hd1, Nat.mul_comm, Nat.div_mul in Hdd; [ | easy ].
   rewrite Hd1, (Nat.mul_comm _ d1), Nat.div_mul; [ | easy ].
   assert (Hd1z : d1 ≠ 0) by now intros H; rewrite H in Hdd.
   apply in_divisors in Hdd; [ | easy ].
   destruct Hdd as (Hdd, Hd'z).
   apply Nat.mod_divides in Hdd; [ | easy ].
   destruct Hdd as (d'', Hdd).
   rewrite <- Nat.mul_assoc, Nat.mul_comm; f_equal.
   rewrite Hdd at 1.
   now rewrite (Nat.mul_comm _ d''), Nat.div_mul.
}
assert (H2 : ∀ d1 d2 d3, d1 * d2 * d3 = n ↔ (d1, d2, d3) ∈ l2). {
  intros.
  split; intros Hddd.
  -assert (Hd1 : d1 ≠ 0) by now intros H; rewrite <- Hddd, H in Hn.
   assert (Hd2 : d2 ≠ 0). {
     now intros H; rewrite <- Hddd, H, Nat.mul_0_r in Hn.
   }
   assert (Hd3 : d3 ≠ 0). {
     now intros H; rewrite <- Hddd, H, Nat.mul_comm in Hn.
   }
   subst l2.
   apply in_flat_map.
   exists (d1 * d2).
   split. {
     apply in_divisors_iff; [ easy | ].
     split; [ | now apply Nat.neq_mul_0 ].
     rewrite <- Hddd.
     apply Nat.mod_divides; [ now apply Nat.neq_mul_0 | ].
     now exists d3.
   }
   apply List.in_map_iff.
   exists d1.
   rewrite <- Hddd.
   rewrite Nat.mul_comm, Nat.div_mul; [ | easy ].
   rewrite Nat.mul_comm, Nat.div_mul; [ | now apply Nat.neq_mul_0 ].
   split; [ easy | ].
   apply in_divisors_iff; [ now apply Nat.neq_mul_0 | ].
   split; [ | easy ].
   apply Nat.mod_divides; [ easy | ].
   exists d2; apply Nat.mul_comm.
  -subst l2.
   apply List.in_flat_map in Hddd.
   destruct Hddd as (d & Hd & Hdi).
   apply List.in_map_iff in Hdi.
   destruct Hdi as (d' & Hd' & Hdd).
   apply in_divisors in Hd; [ | easy ].
   destruct Hd as (Hnd, Hd).
   injection Hd'; clear Hd'; intros Hd3 Hd2 Hd1.
   subst d1 d2 d3.
   apply Nat.mod_divides in Hnd; [ | easy ].
   destruct Hnd as (d1, Hd1).
   rewrite Hd1, (Nat.mul_comm d), Nat.div_mul; [ | easy ].
   rewrite Nat.mul_comm; f_equal.
   apply in_divisors in Hdd; [ | easy ].
   destruct Hdd as (Hdd, Hd').
   apply Nat.mod_divides in Hdd; [ | easy ].
   destruct Hdd as (d'', Hdd).
   rewrite Hdd at 1.
   now rewrite (Nat.mul_comm _ d''), Nat.div_mul.
}
assert (Hl1s : Sorted.Sorted lt_triplet l1). {
  clear - Hn Hl1.
  specialize (in_divisors n Hn) as Hin.
  specialize (divisors_are_sorted n) as Hs.
  remember (divisors n) as l eqn:Hl; clear Hl.
  subst l1.
  induction l as [| a l]; [ now cbn | ].
  cbn - [ divisors ].
  apply (SetoidList.SortA_app eq_equivalence).
  -specialize (Hin a (or_introl eq_refl)); clear IHl.
   destruct Hin as (Hna, Ha).
   apply Nat.mod_divides in Hna; [ | easy ].
   destruct Hna as (b, Hb).
   rewrite Hb, Nat.mul_comm, Nat.div_mul; [ | easy ].
   subst n.
   assert (Hb : b ≠ 0) by now intros H; rewrite H, Nat.mul_comm in Hn.
   clear Hn l Hs; rename b into n; rename Hb into Hn.
   specialize (in_divisors n Hn) as Hin.
   specialize (divisors_are_sorted n) as Hs.
   remember (divisors n) as l eqn:Hl; clear Hl.
   induction l as [| b l]; cbn; [ easy | ].
   constructor.
   +apply IHl; [ now intros d Hd; apply Hin; right | now inversion Hs ].
   +clear IHl.
    destruct l as [| c l]; cbn; [ easy | ].
    constructor.
    unfold lt_triplet, compare_trip.
    rewrite Nat.compare_refl.
    remember (b ?= c) as bb eqn:Hbb; symmetry in Hbb.
    destruct bb; [ | easy | ].
    *apply Nat.compare_eq in Hbb; subst b.
     inversion Hs; subst.
     inversion H2; flia H0.
    *apply Nat.compare_gt_iff in Hbb.
     inversion Hs; subst.
     inversion H2; flia H0 Hbb.
  -apply IHl; [ now intros d Hd; apply Hin; right | now inversion Hs ].
  -intros t1 t2 Hsl Hitt.
   assert (Hjk1 : ∃ j1 k1, t1 = (a, j1, k1)). {
     clear - Hsl.
     remember (divisors (n / a)) as l eqn:Hl; symmetry in Hl; clear Hl.
     induction l as [| b l]; [ now apply SetoidList.InA_nil in Hsl | ].
     cbn in Hsl.
     apply SetoidList.InA_cons in Hsl.
     destruct Hsl as [Hsl| Hsl]. {
       now rewrite Hsl; exists b, (n / a / b).
     }
     now apply IHl.
   }
   destruct Hjk1 as (j1 & k1 & Ht1); rewrite Ht1.
   assert (Hjk2 : ∃ i2 j2 k2, a < i2 ∧ t2 = (i2, j2, k2)). {
     clear - Hs Hitt.
     revert a Hs.
     induction l as [| b l]; intros. {
       now apply SetoidList.InA_nil in Hitt.
     }
     cbn - [ divisors ] in Hitt.
     apply SetoidList.InA_app in Hitt.
     destruct Hitt as [Hitt| Hitt]. {
       clear - Hitt Hs.
       assert (H2 : ∃ j2 k2, t2 = (b, j2, k2)). {
         clear - Hitt.
         induction (divisors (n / b)) as [| a l]. {
           now apply SetoidList.InA_nil in Hitt.
         }
         cbn in Hitt.
         apply SetoidList.InA_cons in Hitt.
         destruct Hitt as [Hitt| Hitt]. {
           now rewrite Hitt; exists a, (n / b / a).
         }
         now apply IHl.
       }
       destruct H2 as (j2 & k2 & H2).
       rewrite H2.
       exists b, j2, k2.
       split; [ | easy ].
       apply Sorted.Sorted_inv in Hs.
       destruct Hs as (Hs, Hr2).
       now apply Sorted.HdRel_inv in Hr2.
     }
     apply IHl; [ easy | ].
     apply Sorted.Sorted_inv in Hs.
     destruct Hs as (Hs, Hr).
     apply Sorted.Sorted_inv in Hs.
     destruct Hs as (Hs, Hr2).
     constructor; [ easy | ].
     apply Sorted.HdRel_inv in Hr.
     eapply (SetoidList.InfA_ltA Nat.lt_strorder); [ apply Hr | easy ].
   }
   destruct Hjk2 as (i2 & j2 & k2 & Hai2 & Ht2).
   rewrite Ht2.
   unfold lt_triplet; cbn.
   remember (a ?= i2) as ai eqn:Hai; symmetry in Hai.
   destruct ai; [ | easy | ].
   +apply Nat.compare_eq_iff in Hai; flia Hai Hai2.
   +apply Nat.compare_gt_iff in Hai; flia Hai Hai2.
}
assert (Hll : length l1 = length l2). {
  rewrite mul_assoc_indices_eq in Hl1.
  subst l1 l2.
  rewrite map_length.
  do 2 rewrite List_flat_map_length.
  do 2 rewrite map_rev.
  rewrite map_map.
  remember (map _ (divisors n)) as l eqn:Hl; clear.
  remember 0 as a; clear Heqa.
  revert a.
  induction l as [| b l]; intros; [ easy | cbn ].
  rewrite fold_right_app; cbn.
  rewrite IHl; clear.
  revert a b.
  induction l as [| c l]; intros; [ easy | cbn ].
  rewrite IHl; ring.
}
assert (H3 : ∀ t, t ∈ l1 ↔ t ∈ l2). {
  intros ((d1, d2), d3); split; intros Ht.
  -now apply H2, H1.
  -now apply H1, H2.
}
assert (Hnd1 : NoDup l1). {
  clear - Hl1s.
  induction l1 as [| a1 l1]; [ constructor | ].
  apply Sorted.Sorted_inv in Hl1s.
  destruct Hl1s as (Hs, Hr).
  constructor; [ | now apply IHl1 ].
  intros Ha.
  clear IHl1.
  revert a1 Hr Ha.
  induction l1 as [| a2 l1]; intros; [ easy | ].
  apply Sorted.HdRel_inv in Hr.
  destruct Ha as [Ha| Ha]. {
    subst a1; revert Hr.
    apply StrictOrder_lt_triplet.
  }
  apply Sorted.Sorted_inv in Hs.
  eapply IHl1; [ easy | | apply Ha ].
  eapply SetoidList.InfA_ltA; [ | apply Hr | easy ].
  apply StrictOrder_lt_triplet.
}
assert (Hnd2 : NoDup l2). {
  rewrite mul_assoc_indices_eq in Hl1.
  remember (λ d : nat, map (λ d' : nat, (d', d / d', n / d)) (divisors d))
    as f eqn:Hf.
  rewrite Hl1 in Hnd1.
  rewrite Hl2.
  apply NoDup_map_inv in Hnd1.
  rewrite flat_map_concat_map in Hnd1.
  rewrite map_rev in Hnd1.
  rewrite flat_map_concat_map.
  remember (map f (divisors n)) as l eqn:Hl.
  now apply NoDup_concat_rev.
}
assert (HP : Permutation l1 l2). {
  now apply NoDup_Permutation.
}
now apply Permutation_f_sum_add.
Qed.

Theorem log_prod_assoc {F : field} : ∀ u v w i,
  i ≠ 0
  → log_prod u (log_prod v w) i = log_prod (log_prod u v) w i.
Proof.
intros * Hi.
unfold log_prod at 1 3.
unfold log_prod_list, log_prod_term.
unfold log_prod.
rewrite map_f_mul_fold_add_distr_l.
rewrite fold_add_map_fold_add.
rewrite map_f_mul_fold_add_distr_r.
rewrite fold_add_map_fold_add.
assert
  (H : ∀ (u : nat → _) f l,
   flat_map (λ i, (u i * f_zero)%F :: f i) l =
   flat_map (λ i, f_zero :: f i) l). {
  clear; intros.
  induction l as [| a l]; [ easy | cbn ].
  now rewrite f_mul_0_r, IHl.
}
rewrite H; clear H.
assert
  (H : ∀ (u : nat → _) f l,
   flat_map (λ i, (f_zero * u i)%F :: f i) l =
   flat_map (λ i, f_zero :: f i) l). {
  clear; intros.
  induction l as [| a l]; [ easy | cbn ].
  now rewrite f_mul_0_l, IHl.
}
rewrite H; clear H.
assert
  (H : ∀ (f : nat → _) l l',
   fold_left f_add (flat_map (λ i, f_zero :: f i) l) l' =
   fold_left f_add (flat_map f l) l'). {
  clear; intros.
  revert l'.
  induction l as [| a l]; intros; [ easy | cbn ].
  rewrite f_add_0_r.
  do 2 rewrite fold_left_app.
  apply IHl.
}
do 2 rewrite H.
clear H.
now apply fold_add_flat_prod_assoc.
Qed.

Theorem ls_mul_assoc {F : field} : ∀ x y z,
  (x * (y * z) = x * y * z)%LS.
Proof.
intros * i Hi.
now cbn; apply log_prod_assoc.
Qed.

Theorem log_prod_list_length {F : field} : ∀ u v n,
  length (log_prod_list u v n) = length (divisors n).
Proof.
intros.
unfold log_prod_list.
apply map_length.
Qed.

Definition pol_pow {F : field} n :=
  {| lp := List.repeat f_zero (n - 1) ++ [f_one] |}.

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

Theorem pol_1_sub_pow_times_series {F : field} : ∀ s m,
  2 ≤ m
  → (∀ i, i ≠ 0 → ls s i = ls s (m * i))
  → ((pol_pow 1 - pol_pow m) .* s = series_but_mul_of m s)%LS.
Proof.
intros * Hm Hs n Hn.
cbn - [ ls_of_pol log_prod ].
remember (n mod m) as p eqn:Hp; symmetry in Hp.
unfold log_prod, log_prod_list.
remember (log_prod_term (ls (ls_of_pol (pol_pow 1 - pol_pow m))) (ls s) n)
  as t eqn:Ht.
assert (Ht1 : t 1 = s~{n}). {
  rewrite Ht; unfold log_prod_term.
  rewrite Nat.div_1_r.
  replace ((ls_of_pol _)~{1}) with f_one. 2: {
    symmetry; cbn.
    destruct m; [ flia Hm | cbn ].
    rewrite Nat.sub_0_r.
    destruct m; [ flia Hm | clear; cbn ].
    now destruct m; cbn; rewrite f_opp_0, f_add_0_r.
  }
  apply f_mul_1_l.
}
destruct p. {
  assert (Htn : t m = (- s~{n})%F). {
    assert (H : t m = (- s~{n/m})%F). {
      rewrite Ht; unfold log_prod_term.
      replace ((ls_of_pol _)~{m}) with (- f_one)%F. 2: {
        symmetry; cbn.
        destruct m; [ flia Hm | cbn ].
        rewrite Nat.sub_0_r.
        destruct m; [ flia Hm | clear; cbn ].
        induction m; [ cbn; apply f_add_0_l | cbn ].
        destruct m; cbn in IHm; cbn; [ easy | apply IHm ].
      }
      now rewrite f_mul_opp_l, f_mul_1_l.
    }
    apply Nat.mod_divides in Hp; [ | flia Hm ].
    destruct Hp as (p, Hp).
    rewrite Hp, Nat.mul_comm, Nat.div_mul in H; [ | flia Hm ].
    destruct (zerop p) as [Hpz| Hpz]; [ now rewrite Hpz, Nat.mul_0_r in Hp | ].
    apply Nat.neq_0_lt_0 in Hpz.
    rewrite Hs in H; [ | easy ].
    now rewrite <- Hp in H.
  }
  assert (Hto : ∀ d, d ≠ 1 → d ≠ m → t d = f_zero). {
    intros d Hd1 Hdm.
    rewrite Ht; unfold log_prod_term.
    replace ((ls_of_pol (pol_pow 1 - pol_pow m))~{d}) with f_zero. 2: {
      symmetry; cbn.
      destruct d; [ easy | cbn ].
      destruct m; intros. {
        cbn; rewrite f_add_opp_diag_r.
        destruct d; [ easy | now destruct d ].
      }
      rewrite Nat_sub_succ_1.
      destruct m; intros. {
        cbn; rewrite f_add_opp_diag_r.
        destruct d; [ easy | now destruct d ].
      }
      destruct m; intros. {
        cbn; rewrite f_opp_0, f_add_0_r, f_add_0_l.
        destruct d; [ easy | ].
        destruct d; [ easy | ].
        now destruct d.
      }
      cbn; rewrite f_opp_0, f_add_0_r, f_add_0_l.
      destruct d; [ easy | clear Hd1 ].
      destruct d; [ easy | ].
      assert (Hd : d ≠ m) by flia Hdm.
      clear - Hd.
      revert d Hd.
      induction m; intros; cbn. {
        destruct d; [ easy | now destruct d ].
      }
      rewrite f_opp_0, f_add_0_l.
      destruct d; [ easy | ].
      apply IHm; flia Hd.
    }
    apply f_mul_0_l.
  }
  assert (Hmd : m ∈ divisors n). {
    apply in_divisors_iff; [ easy | ].
    split; [ easy | flia Hm ].
  }
  specialize (In_nth _ _ 0 Hmd) as (k & Hkd & Hkn).
  specialize (nth_split _ 0 Hkd) as (l1 & l2 & Hll & Hl1).
  rewrite Hkn in Hll.
  rewrite Hll, map_app; cbn.
  specialize (eq_first_divisor_1 n Hn) as H1.
  remember (divisors n) as l.
  destruct l1 as [| a l1]. {
    cbn in Hl1; subst k.
    destruct l as [| a l]; [ easy | ].
    cbn in Hkn, H1.
    rewrite <- Hkn, H1 in Hm; flia Hm.
  }
  rewrite Hll in H1; cbn in H1; subst a.
  cbn; rewrite f_add_0_l, Ht1, Htn.
  rewrite fold_left_app; cbn.
  rewrite fold_f_add_assoc.
  assert (H1 : ∀ a, fold_left f_add (map t l1) a = a). {
    assert (Hdl : ∀ d, d ∈ l1 → t d = f_zero). {
      intros d Hd.
      specialize (divisors_are_sorted n) as Hds.
      rewrite <- Heql, Hll in Hds; cbn in Hds.
      apply Hto. {
        intros H; subst d.
        assert (H : 1 ∈ (l1 ++ m :: l2)). {
          now apply in_or_app; left.
        }
        replace (1 :: l1 ++ m :: l2) with ([] ++ 1 :: l1 ++ m :: l2)
          in Hds by easy.
        now apply Sorted_Sorted_lt_app_not_in_r in Hds.
      }
      intros H; subst d.
      assert (H : m ∈ (1 :: l1)) by now right.
      rewrite app_comm_cons in Hds.
      revert H.
      now apply Sorted_Sorted_lt_app_not_in_l in Hds.
    }
    intros a; clear - Hdl.
    revert a.
    induction l1 as [| b l]; intros; [ easy | ].
    cbn; rewrite Hdl; [ | now left ].
    rewrite f_add_0_r.
    apply IHl; intros c Hc.
    now apply Hdl; right.
  }
  rewrite H1.
  assert (H2 : ∀ a, fold_left f_add (map t l2) a = a). {
    assert (Hdl : ∀ d, d ∈ l2 → t d = f_zero). {
      intros d Hd.
      clear Hs.
      specialize (divisors_are_sorted n) as Hs.
      rewrite <- Heql, Hll in Hs; cbn in Hs.
      apply Hto. {
        intros H; subst d.
        apply Sorted.Sorted_StronglySorted in Hs; [ | apply Nat.lt_strorder ].
        apply Sorted.StronglySorted_inv in Hs.
        destruct Hs as (Hds, Hall).
        specialize (proj1 (Forall_forall _ _) Hall 1) as H2.
        assert (H : 1 ∈ (l1 ++ m :: l2)). {
          now apply in_or_app; right; right.
        }
        specialize (H2 H); flia H2.
      }
      intros H; subst d.
      apply Sorted.Sorted_inv in Hs.
      destruct Hs as (Hs, Hr).
      now apply Sorted_Sorted_lt_app_not_in_r in Hs.
    }
    intros a; clear - Hdl.
    revert a.
    induction l2 as [| b l]; intros; [ easy | ].
    cbn; rewrite Hdl; [ | now left ].
    rewrite f_add_0_r.
    apply IHl; intros c Hc.
    now apply Hdl; right.
  }
  rewrite H2.
  apply f_add_opp_diag_r.
}
assert (Hto : ∀ d, d ∈ divisors n → d ≠ 1 → t d = f_zero). {
  intros d Hd Hd1.
  rewrite Ht; unfold log_prod_term.
  replace ((ls_of_pol (pol_pow 1 - pol_pow m))~{d}) with f_zero. 2: {
    symmetry.
    clear - Hn Hp Hd Hd1.
    assert (Hdm : d ≠ m). {
      intros H; subst d.
      apply in_divisors in Hd; [ | easy ].
      now rewrite Hp in Hd.
    }
    clear - Hd1 Hdm; cbn.
    destruct d; [ easy | ].
    destruct m. {
      cbn.
      cbn; rewrite f_add_opp_diag_r.
      destruct d; [ easy | now destruct d ].
    }
    apply -> Nat.succ_inj_wd_neg in Hd1.
    apply -> Nat.succ_inj_wd_neg in Hdm.
    rewrite Nat_sub_succ_1.
    revert d Hd1 Hdm.
    induction m; intros. {
      cbn; rewrite f_add_opp_diag_r.
      destruct d; [ easy | now destruct d ].
    }
    cbn.
    destruct d; [ easy | clear Hd1 ].
    apply -> Nat.succ_inj_wd_neg in Hdm.
    destruct d. {
      destruct m; [ easy | ].
      now cbn; rewrite f_add_opp_diag_r.
    }
    specialize (IHm (S d) (Nat.neq_succ_0 _) Hdm) as H1.
    destruct m. {
      cbn.
      destruct d; [ easy | now destruct d ].
    }
    cbn in H1; cbn.
    destruct m. {
      cbn.
      destruct d; [ easy | ].
      destruct d; [ easy | now destruct d ].
    }
    cbn in H1.
    destruct d. {
      now cbn; rewrite f_add_opp_diag_r.
    }
    cbn; apply H1.
  }
  apply f_mul_0_l.
}
remember (divisors n) as l eqn:Hl; symmetry in Hl.
destruct l as [| a l]; [ now destruct n | ].
specialize (eq_first_divisor_1 n Hn) as H1.
rewrite Hl in H1; cbn in H1; subst a.
cbn; rewrite f_add_0_l, <- Ht1.
assert (H1 : ∀ a, fold_left f_add (map t l) a = a). {
  intros a.
  specialize (divisors_are_sorted n) as Hds.
  rewrite Hl in Hds; clear Hl.
  apply Sorted.Sorted_StronglySorted in Hds; [ | apply Nat.lt_strorder ].
  apply Sorted.StronglySorted_inv in Hds.
  destruct Hds as (Hds, Hall).
  revert a.
  induction l as [| b l]; intros; cbn; [ easy | ].
  rewrite f_add_comm, fold_f_add_assoc.
  rewrite IHl; cycle 1. {
    intros d Hd Hd1.
    apply Hto; [ | easy ].
    destruct Hd as [Hd| Hd]; [ now subst d | ].
    now right; right.
  } {
    now apply Sorted.StronglySorted_inv in Hds.
  } {
    now apply Forall_inv_tail in Hall.
  }
  rewrite Hto; cycle 1; [ now right; left | | ]. {
    intros H; subst b.
    apply Forall_inv in Hall; flia Hall.
  }
  apply f_add_0_l.
}
apply H1.
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
rewrite <- ls_mul_assoc.
rewrite IHl; cycle 1. {
  now intros a Ha; apply Hge2; right.
} {
  intros a Ha i Hi; apply Hai; [ now right | easy ].
} {
  intros na nb Hnn.
  apply (Hgcd (S na) (S nb)).
  now intros H; apply Hnn; apply Nat.succ_inj in H.
}
apply pol_1_sub_pow_times_series; [ now apply Hge2; left | ].
intros i Hi.
specialize (Hai a1 (or_introl eq_refl)) as Ha1i.
clear - Hi Ha1i Hgcd.
induction l as [| a l]; [ now apply Ha1i | cbn ].
remember (i mod a) as m eqn:Hm; symmetry in Hm.
destruct m. {
  destruct a; [ easy | ].
  apply Nat.mod_divides in Hm; [ | easy ].
  destruct Hm as (m, Hm).
  rewrite Hm, Nat.mul_comm, <- Nat.mul_assoc, Nat.mul_comm.
  now rewrite Nat.mod_mul.
}
remember ((a1 * i) mod a) as n eqn:Hn; symmetry in Hn.
destruct n. {
  destruct a; [ easy | ].
  apply Nat.mod_divide in Hn; [ | easy ].
  specialize (Nat.gauss (S a) a1 i Hn) as H1.
  enough (H : Nat.gcd (S a) a1 = 1). {
    specialize (H1 H); clear H.
    apply Nat.mod_divide in H1; [ | easy ].
    now rewrite Hm in H1.
  }
  specialize (Hgcd 0 1 (Nat.neq_0_succ _)) as H2.
  now cbn in H2; rewrite Nat.gcd_comm in H2.
}
apply IHl; intros na nb Hnab; cbn.
destruct na. {
  destruct nb; [ easy | ].
  now apply (Hgcd 0 (S (S nb))).
}
destruct nb; [ now apply (Hgcd (S (S na)) 0) | ].
apply (Hgcd (S (S na)) (S (S nb))).
now apply Nat.succ_inj_wd_neg.
Qed.

Corollary list_of_1_sub_pow_primes_times_ζ {F : field} : ∀ l,
  (∀ p, p ∈ l → is_prime p = true)
  → NoDup l
  → (Π (p ∈ l), (pol_pow 1 - pol_pow p) * ζ =
     fold_right series_but_mul_of ζ l)%LS.
Proof.
intros * Hp Hnd.
apply list_of_pow_1_sub_pol_times_series; [ | easy | ]. {
  intros p Hpl.
  specialize (Hp _ Hpl) as H1.
  destruct p; [ easy | ].
  destruct p; [ easy | ].
  do 2 apply -> Nat.succ_le_mono.
  apply Nat.le_0_l.
} {
  intros * Hnab.
  destruct (lt_dec na (length l)) as [Hna| Hna]. {
    specialize (Hp _ (nth_In l 1 Hna)) as H1.
    destruct (lt_dec nb (length l)) as [Hnb| Hnb]. {
      specialize (Hp _ (nth_In l 1 Hnb)) as H2.
      move H1 before H2.
      assert (Hne : nth na l 1 ≠ nth nb l 1). {
        intros He.
        apply Hnab.
        apply (proj1 (NoDup_nth l 1) Hnd na nb Hna Hnb He).
      }
      now apply eq_primes_gcd_1.
    }
    apply Nat.nlt_ge in Hnb.
    rewrite (nth_overflow _ _ Hnb).
    apply Nat.gcd_1_r.
  }
  apply Nat.nlt_ge in Hna.
  rewrite (nth_overflow _ _ Hna).
  apply Nat.gcd_1_r.
}
Qed.

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
