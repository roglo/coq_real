(* gcd a b with computation of a/gcd a b and b/gcd a b on the fly *)

Require Import Utf8 Arith Psatz.

Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Fixpoint ggcdn it a b :=
  match it with
  | 0 => (0, (0, 0))
  | S it' =>
      match a with
      | 0 => (b, (0, 1))
      | _ =>
          match Nat.compare a b with
          | Eq => (a, (1, 1))
          | Lt =>
              let '(g, (a', b')) := ggcdn it' (b - a) a in
              (g, (b', a' + b'))
          | Gt =>
              let '(g, (a', b')) := ggcdn it' b (a - b) in
              (g, (a' + b', a'))
          end
      end
  end.
Definition ggcd a b := ggcdn (a + b + 1) a b.

Theorem ggcdn_gcd : ∀ a b n, a + b + 1 ≤ n → fst (ggcdn n a b) = Nat.gcd a b.
Proof.
intros * Hab.
revert a b Hab.
induction n; intros.
-now apply Nat.le_0_r, Nat.eq_add_0 in Hab.
-simpl.
 destruct a; [ easy | ].
 simpl in Hab.
 apply Nat.succ_le_mono in Hab.
 remember (Nat.compare (S a) b) as c eqn:Hc; symmetry in Hc.
 destruct c.
 +apply Nat.compare_eq_iff in Hc; rewrite Hc.
  now rewrite Nat.gcd_diag.
 +apply Nat.compare_lt_iff in Hc.
  specialize (IHn (b - S a) (S a)) as H1.
  assert (H : b - S a + S a + 1 ≤ n) by flia Hab Hc.
  specialize (H1 H); clear H.
  remember (ggcdn n (b - S a) (S a)) as gab eqn:Hgab.
  symmetry in Hgab.
  destruct gab as (g, (a', b')).
  rewrite Nat.gcd_comm, Nat.gcd_sub_diag_r in H1; [ easy | flia Hc ].
 +apply Nat.compare_gt_iff in Hc.
  destruct b.
  *destruct n; [ now rewrite Nat.add_comm in Hab | simpl ].
   now rewrite Nat.sub_diag.
  *specialize (IHn (S b) (S a - S b)) as H1.
   assert (H : S b + (S a - S b) + 1 ≤ n) by flia Hab Hc.
   specialize (H1 H); clear H.
   remember (ggcdn n (S b) (S a - S b)) as gab eqn:Hgab.
   symmetry in Hgab.
   destruct gab as (g, (a', b')).
   rewrite Nat.gcd_sub_diag_r in H1; [ | flia Hc ].
   now rewrite Nat.gcd_comm in H1.
Qed.

Theorem ggcd_gcd : ∀ a b, fst (ggcd a b) = Nat.gcd a b.
Proof. now intros; apply ggcdn_gcd. Qed.

Theorem ggcdn_correct_divisors : ∀ a b n,
  b ≠ 0
  → a + b + 1 ≤ n
  → let '(g, (aa, bb)) := ggcdn n a b in
     a = g * aa ∧ b = g * bb.
Proof.
intros * Hb Hn.
remember (ggcdn n a b) as g eqn:Hg.
destruct g as (g, (aa, bb)).
revert a b g aa bb Hb Hn Hg.
induction n; intros; [ flia Hn | ].
simpl in Hg.
destruct a.
-injection Hg; clear Hg; intros; subst g aa bb; flia.
-remember (S a ?= b) as c1 eqn:Hc1; symmetry in Hc1.
 destruct c1.
 +apply Nat.compare_eq_iff in Hc1.
  subst b.
  injection Hg; clear Hg; intros; subst g aa bb; flia.
 +apply Nat.compare_lt_iff in Hc1.
  remember (ggcdn n (b - S a) (S a)) as g1 eqn:Hg1.
  destruct g1 as (g1, (aa1, bb1)).
  injection Hg; clear Hg; intros; subst g1 bb1 bb.
  specialize (IHn (b - S a) (S a) g aa1 aa (Nat.neq_succ_0 a)) as H1.
  assert (H : b - S a + S a + 1 ≤ n) by flia Hn Hc1.
  specialize (H1 H Hg1) as (H1, H2); clear H.
  split; [ easy | ].
  apply Nat.add_sub_eq_nz in H1; [ flia H1 H2 | ].
  intros H.
  apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ now subst g | subst aa1; flia Hc1 H1 ].
 +apply Nat.compare_gt_iff in Hc1.
  remember (ggcdn n b (S a - b)) as g1 eqn:Hg1.
  destruct g1 as (g1, (aa1, bb1)).
  injection Hg; clear Hg; intros; subst g1 aa1 aa.
  specialize (IHn b (S a - b) g bb bb1) as H1.
  assert (H : b + (S a - b) + 1 ≤ n) by flia Hb Hn Hc1.
  assert (H' : S a - b ≠ 0) by flia Hc1.
  specialize (H1 H' H Hg1) as (H1, H2); clear H H'.
  split; [ | easy ].
  apply Nat.add_sub_eq_nz in H2; [ flia H1 H2 | ].
  intros H.
  apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ now subst g | subst bb1; flia Hc1 H2 ].
Qed.

Theorem ggcd_correct_divisors : ∀ a b,
  b ≠ 0
  → let '(g, (aa, bb)) := ggcd a b in
     a = g * aa ∧ b = g * bb.
Proof. now intros; apply ggcdn_correct_divisors. Qed.
