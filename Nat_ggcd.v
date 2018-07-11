(* gcd a b with computation of a/gcd a b and b/gcd a b on the fly *)

Require Import Utf8 Arith Psatz.
Set Nested Proofs Allowed.

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

Theorem ggcd_fst_snd : ∀ a b, b ≠ 0 → fst (snd (ggcd a b)) = a / Nat.gcd a b.
Proof.
intros * Hb.
specialize (ggcd_correct_divisors a b Hb) as H.
remember (ggcd a b) as g eqn:Hg.
destruct g as (g, (aa, bb)).
destruct H as (H1, H2); simpl.
subst a b.
specialize (ggcd_gcd (g * aa) (g * bb)) as H1.
rewrite <- Hg in H1; simpl in H1.
rewrite <- H1.
rewrite Nat.mul_comm, Nat.div_mul; [ easy | ].
now intros H; subst g.
Qed.

Theorem ggcd_snd_snd : ∀ a b,
  b ≠ 0 → snd (snd (ggcd a b)) = b / Nat.gcd a b.
Proof.
intros * Hb.
specialize (ggcd_correct_divisors a b Hb) as H.
remember (ggcd a b) as g eqn:Hg.
destruct g as (g, (aa, bb)).
destruct H as (H1, H2); simpl.
subst a b.
specialize (ggcd_gcd (g * aa) (g * bb)) as H1.
rewrite <- Hg in H1; simpl in H1.
rewrite <- H1.
rewrite Nat.mul_comm, Nat.div_mul; [ easy | ].
now intros H; subst g.
Qed.

Theorem ggcd_swap : ∀ a b g aa bb,
  a ≠ 0 → b ≠ 0
  → ggcd a b = (g, (aa, bb))
  → ggcd b a = (g, (bb, aa)).
Proof.
intros * Ha Hb Hab.
specialize (ggcd_fst_snd a b Hb) as H1.
specialize (ggcd_snd_snd a b Hb) as H2.
specialize (ggcd_fst_snd b a Ha) as H3.
specialize (ggcd_snd_snd b a Ha) as H4.
rewrite Hab in H1; simpl in H1.
rewrite Hab in H2; simpl in H2.
rewrite Nat.gcd_comm, <- H2 in H3.
rewrite Nat.gcd_comm, <- H1 in H4.
remember (ggcd b a) as g1 eqn:Hg1.
destruct g1 as (g1, (aa1, bb1)).
simpl in H3, H4; subst aa1 bb1; f_equal.
specialize (ggcd_gcd a b) as H3.
specialize (ggcd_gcd b a) as H4.
rewrite Hab in H3; simpl in H3.
rewrite <- Hg1 in H4; simpl in H4.
now rewrite Nat.gcd_comm, <- H3 in H4.
Qed.

Theorem Nat_gcd_le : ∀ a b, Nat.gcd a b ≤ a.
Proof.
intros.
specialize (Nat.gcd_divide_l a b) as (c, Hc).
...

Theorem ggcd_succ_l_neq_0 : ∀ a b, fst (snd (ggcd (S a) b)) ≠ 0.
Proof.
intros.
destruct b.
-now unfold ggcd; rewrite Nat.add_0_r, Nat.add_1_r.
-rewrite ggcd_fst_snd; [ | easy ].
 intros H1.
 apply Nat.div_small_iff in H1.
 +idtac.
Search (Nat.gcd _ _ ≤ _).

...
 apply Nat.div_small_iff in H1.
 +rewrite <- Nat.mul_1_l in H1.
  apply Nat.nle_gt in H1; apply H1.
  specialize (Nat.gcd_divide_l (S a) (S b)) as H2.
  destruct H2 as (c, Hc).
  rewrite Hc at 2.
  apply Nat.mul_le_mono_pos_r.
  *idtac.
Search Nat.gcd.
...

Nat.gcd_divide_l: ∀ a b : nat, Nat.divide (Nat.gcd a b) a
Search (Nat.gcd _ _).
...
intros.
unfold ggcd.
remember (S a + b + 1) as n eqn:Hn.
assert (H : S a + b + 1 ≤ n) by flia Hn.
clear Hn; rename H into Hn.
revert a b Hn.
induction n; intros; [ easy | ].
remember (S a) as aa; simpl; subst aa.
remember (S a ?= b) as c1 eqn:Hc1; symmetry in Hc1.
destruct c1; [ easy | | ].
-apply Nat.compare_lt_iff in Hc1.
 remember (ggcdn n (b - S a) (S a)) as g eqn:Hg1.
 destruct g as (g1, (aa1, bb1)).
Inspect 4.
...
