(* gcd a b with computation of a/gcd a b and b/gcd a b on the fly *)

Require Import Utf8 Arith Psatz.
Require Import Misc.

Set Nested Proofs Allowed.

Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Fixpoint ggcdn it a b :=
  match it with
  | 0 => (0, (0, 0))
  | S it' =>
      match a with
      | 0 => (b, (0, b / b))
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
  a + b + 1 ≤ n
  → let '(g, (aa, bb)) := ggcdn n a b in
     a = g * aa ∧ b = g * bb.
Proof.
intros * Hn.
remember (ggcdn n a b) as g eqn:Hg.
destruct g as (g, (aa, bb)).
revert a b g aa bb (*Hb*) Hn Hg.
induction n; intros; [ flia Hn | ].
simpl in Hg.
destruct a.
-injection Hg; clear Hg; intros; subst g aa bb.
 destruct b; [ easy | ].
 rewrite Nat.div_same; [ flia | easy ].
-remember (S a ?= b) as c1 eqn:Hc1; symmetry in Hc1.
 destruct c1.
 +apply Nat.compare_eq_iff in Hc1.
  subst b.
  injection Hg; clear Hg; intros; subst g aa bb; flia.
 +apply Nat.compare_lt_iff in Hc1.
  remember (ggcdn n (b - S a) (S a)) as g1 eqn:Hg1.
  destruct g1 as (g1, (aa1, bb1)).
  injection Hg; clear Hg; intros; subst g1 bb1 bb.
  specialize (IHn (b - S a) (S a) g aa1 aa (*Nat.neq_succ_0 a*)) as H1.
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
  destruct b.
  *rewrite Nat.sub_0_r in Hg1.
   destruct n; [ flia Hn | ].
   remember (S a) as aa; simpl in Hg1; subst aa.
   rewrite Nat.div_same in Hg1; [ | easy ].
   injection Hg1; clear Hg1; intros; subst g bb bb1.
   now rewrite Nat.add_0_l, Nat.mul_1_r, Nat.mul_0_r.
  *specialize (IHn (S b) (S a - S b) g bb bb1) as H1.
   assert (H : S b + (S a - S b) + 1 ≤ n) by flia Hn Hc1.
   specialize (H1 H Hg1) as (H1, H2); clear H.
   split; [ | easy ].
   apply Nat.add_sub_eq_nz in H2; [ flia H1 H2 | ].
   intros H.
   apply Nat.eq_mul_0 in H.
   destruct H as [H| H]; [ now subst g | subst bb1; flia Hc1 H2 ].
Qed.

Theorem ggcd_correct_divisors : ∀ a b,
  let '(g, (aa, bb)) := ggcd a b in
  a = g * aa ∧ b = g * bb.
Proof. now intros; apply ggcdn_correct_divisors. Qed.

Theorem ggcd_fst_snd : ∀ a b, fst (snd (ggcd a b)) = a / Nat.gcd a b.
Proof.
intros.
specialize (ggcd_correct_divisors a b) as H.
remember (ggcd a b) as g eqn:Hg.
destruct g as (g, (aa, bb)).
destruct H as (H1, H2); simpl.
destruct g.
-simpl in H1, H2; subst a b; simpl.
 unfold ggcd in Hg; simpl in Hg.
 now injection Hg; intros; subst aa.
-subst a b.
 specialize (ggcd_gcd (S g * aa) (S g * bb)) as H1.
 rewrite <- Hg in H1.
 rewrite <- H1.
 rewrite Nat.mul_comm, Nat.div_mul; [ easy | ].
 now intros H; simpl in H.
Qed.

Theorem ggcd_snd_snd : ∀ a b, snd (snd (ggcd a b)) = b / Nat.gcd a b.
Proof.
intros.
specialize (ggcd_correct_divisors a b) as H.
remember (ggcd a b) as g eqn:Hg.
destruct g as (g, (aa, bb)).
destruct H as (H1, H2); simpl.
destruct g.
-simpl in H1, H2; subst a b; simpl.
 unfold ggcd in Hg; simpl in Hg.
 now injection Hg; intros; subst bb.
-subst a b.
 specialize (ggcd_gcd (S g * aa) (S g * bb)) as H1.
 rewrite <- Hg in H1.
 rewrite <- H1.
 rewrite Nat.mul_comm, Nat.div_mul; [ easy | ].
 now intros H; simpl in H.
Qed.

Theorem ggcd_swap : ∀ a b g aa bb,
  ggcd a b = (g, (aa, bb)) → ggcd b a = (g, (bb, aa)).
Proof.
intros * Hab.
specialize (ggcd_fst_snd a b) as H1.
specialize (ggcd_snd_snd a b) as H2.
specialize (ggcd_fst_snd b a) as H3.
specialize (ggcd_snd_snd b a) as H4.
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

Theorem ggcd_succ_l_neq_0 : ∀ a b, fst (snd (ggcd (S a) b)) ≠ 0.
Proof.
intros.
rewrite ggcd_fst_snd.
intros H1.
apply Nat.div_small_iff in H1.
+apply Nat.nle_gt in H1; apply H1.
 now apply Nat_gcd_le_l.
+intros H2.
 now apply Nat.gcd_eq_0_l in H2.
Qed.

Theorem ggcd_split : ∀ a b g,
  g = Nat.gcd a b → ggcd a b = (g, (a / g, b / g)).
Proof.
intros * Hg.
remember (ggcd a b) as g1 eqn:Hg1.
destruct g1 as (g1, (aa1, bb1)).
specialize (ggcd_gcd a b) as H1.
rewrite <- Hg1, <- Hg in H1; simpl in H1; subst g1.
specialize (ggcd_fst_snd a b) as H1.
rewrite <- Hg1, <- Hg in H1; simpl in H1; subst aa1.
specialize (ggcd_snd_snd a b) as H1.
rewrite <- Hg1, <- Hg in H1; simpl in H1; subst bb1.
easy.
Qed.

Theorem snd_ggcd_mul_mono_l : ∀ a b c,
  c ≠ 0
  → snd (ggcd (c * a) (c * b)) = snd (ggcd a b).
Proof.
intros * Hc.
remember (Nat.gcd (c * a) (c * b)) as g eqn:Hg.
rewrite (ggcd_split _ _ g); [ | easy ].
rewrite Nat.gcd_mul_mono_l in Hg.
remember (Nat.gcd a b) as g1 eqn:Hg1.
destruct g1.
-rewrite Nat.mul_0_r in Hg; subst g.
 symmetry in Hg1.
 apply Nat.gcd_eq_0 in Hg1.
 now destruct Hg1; subst a b.
-subst g.
 rewrite Nat.div_mul_cancel_l; [ | easy | easy ].
 rewrite Nat.div_mul_cancel_l; [ | easy | easy ].
 now rewrite (ggcd_split _ _ (S g1)).
Qed.

Theorem ggcd_mul_mono_l : ∀ a b c,
  c ≠ 0
  → ggcd (c * a) (c * b) = (c * Nat.gcd a b, snd (ggcd a b)).
Proof.
intros * Hc.
specialize (snd_ggcd_mul_mono_l a b c Hc) as H.
remember (ggcd (c * a) (c * b)) as g eqn:Hg.
destruct g as (g, (aa, bb)).
simpl in H; rewrite H; f_equal.
specialize (ggcd_gcd (c * a) (c * b)) as H1.
rewrite <- Hg in H1; simpl in H1.
now rewrite Nat.gcd_mul_mono_l in H1.
Qed.

Theorem ggcd_succ_l : ∀ a b g aa bb,
  ggcd (S a) b = (g, (aa, bb)) → g ≠ 0 ∧ aa ≠ 0.
Proof.
intros * Hg.
erewrite ggcd_split in Hg; [ | easy ].
remember S as f; simpl.
injection Hg; clear Hg; intros; subst g aa bb.
subst f.
split.
-now intros H; apply Nat.gcd_eq_0_l in H.
-intros H.
 apply Nat.div_small_iff in H.
 +apply Nat.nle_gt in H; apply H.
  now apply Nat_gcd_le_l.
 +now intros H1; apply Nat.gcd_eq_0_l in H1.
Qed.

Theorem ggcd_succ_r : ∀ a b g aa bb,
  ggcd a (S b) = (g, (aa, bb)) → g ≠ 0 ∧ bb ≠ 0.
Proof.
intros * Hg.
erewrite ggcd_split in Hg; [ | easy ].
remember S as f; simpl.
injection Hg; clear Hg; intros; subst g aa bb.
subst f.
split.
-now intros H; apply Nat.gcd_eq_0_r in H.
-intros H.
 apply Nat.div_small_iff in H.
 +apply Nat.nle_gt in H; apply H.
  now apply Nat_gcd_le_r.
 +now intros H1; apply Nat.gcd_eq_0_r in H1.
Qed.

Theorem ggcd_1_l : ∀ n, ggcd 1 n = (1, (1, n)).
Proof.
intros.
erewrite ggcd_split; [ | easy ].
rewrite Nat.gcd_1_l.
now do 2 rewrite Nat.div_1_r.
Qed.

Theorem ggcd_1_r : ∀ n, ggcd n 1 = (1, (n, 1)).
Proof.
intros.
erewrite ggcd_split; [ | easy ].
rewrite Nat.gcd_1_r.
now do 2 rewrite Nat.div_1_r.
Qed.

Theorem ggcd_diag : ∀ a, a ≠ 0 → ggcd a a = (a, (1, 1)).
Proof.
intros.
unfold ggcd.
rewrite Nat.add_1_r; simpl.
destruct a; [ easy | ].
now rewrite Nat.compare_refl.
Qed.
