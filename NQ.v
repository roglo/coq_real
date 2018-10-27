(* Positive rationals where num and den are always common primes *)
(* allowing us to use Leibnitz' equality. *)

Require Import Utf8 Arith Psatz.
Require Import Misc GQ.
Set Nested Proofs Allowed.

Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Declare Scope NQ_scope.
Delimit Scope NQ_scope with NQ.

Inductive NQ :=
  | NQ0 : NQ
  | NQpos : GQ → NQ
  | NQneg : GQ → NQ.
Arguments NQpos p%GQ.
Arguments NQneg p%GQ.

Definition NQ_of_nat n :=
  match n with
  | 0 => NQ0
  | S _ => NQpos (GQ_of_nat n)
  end.

Definition NQ_of_pair n d :=
  match n with
  | 0 => NQ0
  | _ => NQpos (GQ_of_pair n d)
  end.

Notation "a // b" := (NQ_of_pair a b) : NQ_scope.

Notation "0" := NQ0 : NQ_scope.
Notation "1" := (1 // 1)%NQ : NQ_scope.
Notation "2" := (2 // 1)%NQ : NQ_scope.

Definition NQnum x :=
  match x with
  | NQ0 => 0
  | NQpos a => GQnum a
  | NQneg a => GQnum a
  end.
Definition NQden x :=
  match x with
  | NQ0 => 1
  | NQpos a => GQden a
  | NQneg a => GQden a
  end.
Arguments NQnum x%NQ.
Arguments NQden x%NQ.

Definition NQcompare x y :=
  match x with
  | NQ0 => match y with NQ0 => Eq | NQpos _ => Lt | NQneg _ => Gt end
  | NQpos px => match y with NQpos py => GQcompare px py | _ => Gt end
  | NQneg px => match y with NQneg py => GQcompare py px | _ => Lt end
  end.

Definition NQlt x y :=
  match x with
  | NQ0 => match y with NQpos _ => True | _ => False end
  | NQpos px => match y with NQpos py => GQlt px py | _ => False end
  | NQneg px => match y with NQneg py => GQlt py px | _ => True end
  end.
Arguments NQlt x%NQ y%NQ.

Definition NQle x y :=
  match x with
  | NQ0 => match y with NQ0 | NQpos _ => True | _ => False end
  | NQpos px => match y with NQpos py => GQle px py | _ => False end
  | NQneg px => match y with NQneg py => GQle py px | _ => True end
  end.
Arguments NQle x%NQ y%NQ.

Definition NQgt x y := NQlt y x.
Definition NQge x y := NQle y x.

Notation "x < y" := (NQlt x y) : NQ_scope.
Notation "x ≤ y" := (NQle x y) : NQ_scope.
Notation "x > y" := (NQgt x y) : NQ_scope.
Notation "x ≥ y" := (NQge x y) : NQ_scope.

Theorem NQeq_dec : ∀ x y : NQ, {x = y} + {x ≠ y}.
Proof.
intros.
destruct x as [| px| px], y as [| py| py]; try now right.
-now left.
-destruct (GQeq_dec px py) as [H1| H1]; [ left | right ].
 +now f_equal.
 +now intros H; apply H1; injection H; intros.
-destruct (GQeq_dec px py) as [H1| H1]; [ left | right ].
 +now f_equal.
 +now intros H; apply H1; injection H; intros.
Qed.
Arguments NQeq_dec x%NQ y%NQ.

Theorem NQlt_le_dec : ∀ x y : NQ, {(x < y)%NQ} + {(y ≤ x)%NQ}.
Proof.
intros.
destruct x as [| px| px].
-destruct y as [| py| py]; [ now right | now left | now right ].
-destruct y as [| py| py]; [ now right | simpl | now right ].
 apply GQlt_le_dec.
-destruct y as [| py| py]; [ now left | now left | ].
 apply GQlt_le_dec.
Qed.
Arguments NQlt_le_dec x%NQ y%NQ.

Theorem NQle_lt_dec : ∀ x y : NQ, {(x ≤ y)%NQ} + {(y < x)%NQ}.
Proof.
destruct x as [| px| px].
-destruct y as [| py| py]; [ now left | now left | now right ].
-destruct y as [| py| py]; [ now right | simpl | now right ].
 apply GQle_lt_dec.
-destruct y as [| py| py]; [ now left | now left | ].
 apply GQle_lt_dec.
Qed.
Arguments NQle_lt_dec x%NQ y%NQ.

Theorem NQle_refl : ∀ x, (x ≤ x)%NQ.
Proof.
intros.
destruct x as [| px| px]; [ easy | apply GQle_refl | apply GQle_refl ].
Qed.

Theorem NQle_antisymm : ∀ x y, (x ≤ y)%NQ → (y ≤ x)%NQ → x = y.
Proof.
intros * Hxy Hyx.
unfold "≤"%NQ in Hxy, Hyx.
destruct x as [| px| px], y as [| py| py]; try easy; simpl.
-f_equal; now apply GQle_antisymm.
-f_equal; now apply GQle_antisymm.
Qed.

Definition NQadd_pos_l px y :=
  match y with
  | NQ0 => NQpos px
  | NQpos py => NQpos (px + py)
  | NQneg py =>
      match GQcompare px py with
      | Eq => NQ0
      | Lt => NQneg (py - px)
      | Gt => NQpos (px - py)
      end
  end.

Definition NQadd_neg_l px y :=
  match y with
  | NQ0 => NQneg px
  | NQpos py =>
      match GQcompare px py with
      | Eq => NQ0
      | Lt => NQpos (py - px)
      | Gt => NQneg (px - py)
      end
  | NQneg py => NQneg (px + py)
  end.

Definition NQadd x y :=
  match x with
  | NQ0 => y
  | NQpos px => NQadd_pos_l px y
  | NQneg px => NQadd_neg_l px y
  end.

Definition NQopp x :=
  match x with
  | NQ0 => NQ0
  | NQpos px => NQneg px
  | NQneg px => NQpos px
  end.

Definition NQsub x y := NQadd x (NQopp y).

Definition NQabs x :=
  match x with
  | NQneg px => NQpos px
  | _ => x
  end.

Notation "- x" := (NQopp x) : NQ_scope.
Notation "x + y" := (NQadd x y) : NQ_scope.
Notation "x - y" := (NQadd x (NQopp y)) : NQ_scope.
Notation "‖ x ‖" := (NQabs x) (at level 60) : NQ_scope.

Definition NQmul_pos_l px y :=
  match y with
  | NQ0 => NQ0
  | NQpos py => NQpos (px * py)
  | NQneg py => NQneg (px * py)
  end.

Definition NQmul_neg_l px y :=
  match y with
  | NQ0 => NQ0
  | NQpos py => NQneg (px * py)
  | NQneg py => NQpos (px * py)
  end.

Definition NQmul x y :=
  match x with
  | NQ0 => NQ0
  | NQpos px => NQmul_pos_l px y
  | NQneg px => NQmul_neg_l px y
  end.

Definition NQinv x :=
  match x with
  | NQ0 => NQ0
  | NQpos px => NQpos (/ px)
  | NQneg px => NQneg (/ px)
  end.

Notation "x * y" := (NQmul x y) : NQ_scope.
Notation "x / y" := (NQmul x (NQinv y)) : NQ_scope.
Notation "/ x" := (NQinv x) : NQ_scope.

Theorem NQmatch_match_comp : ∀ A c p q (f0 : A) fp fn,
  match
    match c with
    | Eq => 0%NQ
    | Lt => NQneg p
    | Gt => NQpos q
    end
  with
  | NQ0 => f0
  | NQpos px => fp px
  | NQneg px => fn px
  end =
  match c with
  | Eq => f0
  | Lt => fn p
  | Gt => fp q
  end.
Proof. intros; now destruct c. Qed.

Theorem NQopp_involutive : ∀ x, (- - x)%NQ = x.
Proof. intros; now destruct x. Qed.

Theorem NQopp_match_comp : ∀ c eq lt gt,
  (- match c with Eq => eq | Lt => lt | Gt => gt end =
   match c with Eq => - eq | Lt => - lt | Gt => - gt end)%NQ.
Proof. intros; now destruct c. Qed.

Theorem NQmatch_opp_comp : ∀ c eq lt gt,
  (match c with Eq => eq | Lt => lt | Gt => gt end =
   - match c with Eq => - eq | Lt => - lt | Gt => - gt end)%NQ.
Proof. now intros; destruct c; rewrite NQopp_involutive. Qed.

Theorem NQadd_comm : ∀ x y, (x + y = y + x)%NQ.
Proof.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py]; try easy; simpl.
-f_equal; apply GQadd_comm.
-now rewrite GQcompare_swap; destruct (GQcompare py px).
-now rewrite GQcompare_swap; destruct (GQcompare py px).
-f_equal; apply GQadd_comm.
Qed.

Theorem NQadd_0_l : ∀ x, (0 + x = x)%NQ.
Proof. easy. Qed.

Theorem NQadd_0_r : ∀ x, (x + 0 = x)%NQ.
Proof. intros; now rewrite NQadd_comm. Qed.

Theorem NQnle_gt : ∀ x y, ¬ (x ≤ y)%NQ ↔ (y < x)%NQ.
Proof.
intros.
destruct x as [| xp| xp], y as [| yp| yp]; try now simpl.
-apply GQnle_gt.
-apply GQnle_gt.
Qed.

Theorem NQnlt_ge : ∀ x y, ¬ (x < y)%NQ ↔ (y ≤ x)%NQ.
Proof.
intros.
destruct x as [| xp| xp], y as [| yp| yp]; try now simpl.
-apply GQnlt_ge.
-apply GQnlt_ge.
Qed.

Theorem NQlt_irrefl : ∀ x, ¬ (x < x)%NQ.
Proof.
intros * Hx.
destruct x as [| xp| xp]; [ easy | | ].
-now apply GQlt_irrefl in Hx.
-now apply GQlt_irrefl in Hx.
Qed.

Theorem NQadd_swap_lemma1 : ∀ px py pz,
  match GQcompare (px + py) pz with
  | Eq => 0%NQ
  | Lt => NQneg (pz - (px + py))
  | Gt => NQpos (px + py - pz)
  end =
  match GQcompare px pz with
  | Eq => NQpos py
  | Lt =>
      match GQcompare (pz - px) py with
      | Eq => 0%NQ
      | Lt => NQpos (py - (pz - px))
      | Gt => NQneg (pz - px - py)
      end
  | Gt => NQpos (px - pz + py)
  end.
Proof.
intros.
remember (GQcompare (px + py) pz) as c1 eqn:Hc1; symmetry in Hc1.
remember (GQcompare px pz) as c2 eqn:Hc2; symmetry in Hc2.
move c2 before c1.
destruct c1, c2; repeat GQcompare_iff.
+now rewrite Hc2, GQadd_comm in Hc1; apply GQadd_no_neutral in Hc1.
+remember (GQcompare (pz - px) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff; [ easy | | ].
 *apply (GQadd_lt_mono_r (pz - px)%GQ _ px) in Hc3.
  rewrite GQsub_add in Hc3; [ | easy ].
  rewrite GQadd_comm, Hc1 in Hc3.
  now apply GQlt_irrefl in Hc3.
 *apply (GQadd_lt_mono_r _ _ px) in Hc3.
  rewrite GQsub_add in Hc3; [ | easy ].
  rewrite GQadd_comm, Hc1 in Hc3.
  now apply GQlt_irrefl in Hc3.
+rewrite <- Hc1 in Hc2.
 exfalso; apply GQnle_gt in Hc2; apply Hc2.
 apply GQlt_le_incl, GQlt_add_r.
+rewrite Hc2 in Hc1.
 exfalso; apply GQnle_gt in Hc1; apply Hc1.
 apply GQlt_le_incl, GQlt_add_r.
+remember (GQcompare (pz - px) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff; simpl.
 *rewrite GQadd_comm, <- Hc3 in Hc1.
  rewrite GQsub_add in Hc1; [ | easy ].
  now apply GQlt_irrefl in Hc1.
 *apply (GQadd_lt_mono_r (pz - px)%GQ _ px) in Hc3.
  rewrite GQsub_add in Hc3; [ | easy ].
  rewrite GQadd_comm in Hc3.
  exfalso; apply GQnle_gt in Hc3; apply Hc3.
  now apply GQlt_le_incl.
 *now f_equal; rewrite GQsub_add_distr.
+apply GQnle_gt in Hc2.
 exfalso; apply Hc2; apply GQlt_le_incl.
 apply (GQlt_trans _ (px + py)%GQ); [ | easy ].
 apply GQlt_add_r.
+now subst px; rewrite GQadd_comm, GQadd_sub.
+remember (GQcompare (pz - px) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff; simpl.
 *rewrite GQadd_comm, <- Hc3 in Hc1.
  rewrite GQsub_add in Hc1; [ | easy ].
  now apply GQlt_irrefl in Hc1.
 *rewrite GQadd_comm; symmetry.
  now f_equal; rewrite GQsub_sub_distr.
 *apply (GQadd_lt_mono_r _ _ px) in Hc3.
  rewrite GQsub_add in Hc3; [ | easy ].
  rewrite GQadd_comm in Hc3.
  exfalso; apply GQnle_gt in Hc3; apply Hc3.
  now apply GQlt_le_incl.
+rewrite GQadd_comm.
 rewrite <- GQadd_sub_assoc; [ | easy ].
 now rewrite GQadd_comm.
Qed.

Theorem NQadd_swap_lemma2 : ∀ px py pz,
  match GQcompare px py with
  | Eq => NQneg pz
  | Lt => NQneg (py - px + pz)
  | Gt =>
      match GQcompare (px - py) pz with
      | Eq => 0%NQ
      | Lt => NQneg (pz - (px - py))
      | Gt => NQpos (px - py - pz)
      end
  end =
  match GQcompare px pz with
  | Eq => NQneg py
  | Lt => NQneg (pz - px + py)
  | Gt =>
      match GQcompare (px - pz) py with
      | Eq => 0%NQ
      | Lt => NQneg (py - (px - pz))
      | Gt => NQpos (px - pz - py)
      end
  end.
Proof.
intros.
remember (GQcompare px py) as c1 eqn:Hc1; symmetry in Hc1.
remember (GQcompare px pz) as c2 eqn:Hc2; symmetry in Hc2.
destruct c1, c2; repeat GQcompare_iff.
-now rewrite <- Hc1, Hc2.
-rewrite Hc1.
 rewrite GQsub_add; [ easy | now rewrite <- Hc1 ].
-remember (GQcompare (px - pz) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff.
 +exfalso; rewrite <- Hc1 in Hc3.
  now apply GQsub_no_neutral in Hc3.
 +rewrite GQsub_sub_distr; [ | easy | easy ].
  rewrite GQadd_comm.
  now rewrite Hc1, GQadd_sub.
 +apply GQnle_gt in Hc3.
  exfalso; apply Hc3; rewrite <- Hc1.
  now apply GQlt_le_incl, GQsub_lt.
-rewrite Hc2, GQsub_add; [ easy | now rewrite <- Hc2 ].
-rewrite GQadd_comm.
 rewrite GQadd_sub_assoc; [ | easy ].
 now rewrite GQadd_sub_swap.
-remember (GQcompare (px - pz) py) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff.
 +exfalso; rewrite <- Hc3 in Hc1.
  apply GQnle_gt in Hc1; apply Hc1.
  now apply GQlt_le_incl, GQsub_lt.
 +rewrite GQsub_sub_distr; [ | easy | easy ].
  now rewrite GQadd_sub_swap.
 +exfalso; apply GQnle_gt in Hc3; apply Hc3.
  apply GQlt_le_incl.
  apply (GQlt_trans _ px); [ now apply GQsub_lt | easy ].
-remember (GQcompare (px - py) pz) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff.
 +exfalso; rewrite <- Hc2 in Hc3.
  now apply GQsub_no_neutral in Hc3.
 +symmetry in Hc2.
  rewrite Hc2, GQsub_sub_distr; [ | easy | now apply GQsub_lt ].
  now rewrite GQadd_comm, GQadd_sub.
 +exfalso; apply GQnle_gt in Hc3; apply Hc3.
  rewrite <- Hc2.
  now apply GQlt_le_incl, GQsub_lt.
-remember (GQcompare (px - py) pz) as c3 eqn:Hc3; symmetry in Hc3.
 destruct c3; GQcompare_iff.
 *exfalso; rewrite <- Hc3 in Hc2.
  apply GQnle_gt in Hc2; apply Hc2.
  now apply GQlt_le_incl, GQsub_lt.
 *rewrite GQsub_sub_distr; [ | easy | easy ].
  now rewrite GQadd_sub_swap.
 *exfalso; apply GQnle_gt in Hc3; apply Hc3.
  apply GQlt_le_incl.
  apply (GQlt_trans _ px); [ now apply GQsub_lt | easy ].
-remember (GQcompare (px - py) pz) as c3 eqn:Hc3; symmetry in Hc3.
 remember (GQcompare (px - pz) py) as c4 eqn:Hc4; symmetry in Hc4.
 destruct c3, c4; repeat GQcompare_iff; simpl.
 *easy.
 *exfalso; apply GQnle_gt in Hc4; apply Hc4.
  symmetry in Hc3.
  rewrite Hc3, GQsub_sub_distr; [ | easy | now apply GQsub_lt ].
  rewrite GQadd_comm, GQadd_sub; apply GQle_refl.
 *exfalso; apply GQnle_gt in Hc4; apply Hc4.
  symmetry in Hc3.
  rewrite Hc3.
  rewrite GQsub_sub_distr; [ | easy | now apply GQsub_lt ].
  rewrite GQadd_comm, GQadd_sub; apply GQle_refl.
 *exfalso; symmetry in Hc4.
  rewrite Hc4 in Hc3.
  rewrite GQsub_sub_distr in Hc3; [ | easy | now apply GQsub_lt ].
  rewrite GQadd_comm, GQadd_sub in Hc3.
  now apply GQlt_irrefl in Hc3.
 *rewrite GQsub_sub_distr; [ | easy | easy ].
  rewrite GQsub_sub_distr; [ | easy | easy ].
  now rewrite GQadd_comm.
 *exfalso; apply GQnle_gt in Hc4; apply Hc4; clear Hc4.
  apply (GQadd_le_mono_r _ _ pz).
  rewrite GQsub_add; [ | easy ].
  apply GQnlt_ge; intros Hc4.
  apply GQnle_gt in Hc3; apply Hc3; clear Hc3.
  apply (GQadd_le_mono_r _ _ py).
  rewrite GQsub_add; [ | easy ].
  now apply GQlt_le_incl; rewrite GQadd_comm.
 *exfalso; symmetry in Hc4.
  rewrite Hc4 in Hc3.
  rewrite GQsub_sub_distr in Hc3; [ | easy | now apply GQsub_lt ].
  rewrite GQadd_comm, GQadd_sub in Hc3.
  now apply GQlt_irrefl in Hc3.
 *exfalso; apply GQnle_gt in Hc4; apply Hc4; clear Hc4.
  apply (GQadd_le_mono_r _ _ pz).
  rewrite GQsub_add; [ | easy ].
  apply GQnlt_ge; intros Hc4.
  apply GQnle_gt in Hc3; apply Hc3; clear Hc3.
  apply (GQadd_le_mono_r _ _ py).
  rewrite GQsub_add; [ | easy ].
  now apply GQlt_le_incl; rewrite GQadd_comm.
 *rewrite GQsub_sub_swap; [ easy | ].
  apply (GQadd_lt_mono_r _ _ pz) in Hc4.
  now rewrite GQsub_add in Hc4.
Qed.

Theorem NQadd_add_swap : ∀ x y z, (x + y + z = x + z + y)%NQ.
Proof.
intros.
unfold "+"%NQ.
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl.
-now rewrite GQadd_comm.
-now rewrite GQcompare_swap; destruct (GQcompare pz py).
-now rewrite GQcompare_swap; destruct (GQcompare pz py).
-now rewrite GQadd_comm.
-now destruct (GQcompare px pz).
-now rewrite GQadd_add_swap.
-rewrite NQmatch_match_comp.
 apply NQadd_swap_lemma1.
-now destruct (GQcompare px py).
-rewrite NQmatch_match_comp.
 symmetry; apply NQadd_swap_lemma1.
-do 2 (rewrite NQmatch_match_comp; symmetry).
 apply NQadd_swap_lemma2.
-now destruct (GQcompare px pz).
-now destruct (GQcompare px py).
-rewrite GQcompare_swap, NQmatch_match_comp; symmetry.
 rewrite GQcompare_swap, NQmatch_match_comp; symmetry.
 do 2 rewrite <- NQadd_swap_lemma1.
 now replace (pz + py)%GQ with (py + pz)%GQ by apply GQadd_comm.
-rewrite GQcompare_swap, NQmatch_match_comp; symmetry.
 rewrite NQmatch_opp_comp; simpl.
 rewrite NQadd_swap_lemma1.
 rewrite GQcompare_swap.
 rewrite NQmatch_opp_comp; simpl.
 rewrite NQopp_involutive.
 now rewrite NQopp_match_comp.
-rewrite NQmatch_opp_comp; simpl.
 rewrite NQadd_swap_lemma1; symmetry.
 rewrite GQcompare_swap, NQmatch_match_comp, GQcompare_swap.
 now do 2 rewrite NQopp_match_comp.
-now rewrite GQadd_add_swap.
Qed.

Theorem NQadd_assoc : ∀ x y z, (x + (y + z) = (x + y) + z)%NQ.
Proof.
intros.
symmetry.
rewrite NQadd_comm.
remember (x + y)%NQ as t eqn:Ht.
rewrite NQadd_comm in Ht; rewrite Ht.
setoid_rewrite NQadd_comm.
apply NQadd_add_swap.
Qed.

Theorem NQsub_diag : ∀ x, (x - x = 0)%NQ.
Proof.
intros.
destruct x as [| px| px]; [ easy | | ]; simpl.
-now rewrite GQcompare_diag.
-now rewrite GQcompare_diag.
Qed.

Theorem NQsub_add : ∀ a b, (a - b + b)%NQ = a.
Proof.
intros.
rewrite NQadd_add_swap, <- NQadd_assoc.
now rewrite NQsub_diag, NQadd_0_r.
Qed.

Theorem NQadd_sub : ∀ a b, (a + b - b)%NQ = a.
Proof.
intros.
rewrite <- NQadd_assoc.
now rewrite NQsub_diag, NQadd_0_r.
Qed.

Theorem NQlt_trans: ∀ x y z, (x < y)%NQ → (y < z)%NQ → (x < z)%NQ.
Proof.
intros * Hxy Hyz.
unfold "≤"%NQ in *.
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-eapply GQlt_trans; [ apply Hxy | apply Hyz ].
-eapply GQlt_trans; [ apply Hyz | apply Hxy ].
Qed.
Arguments NQlt_trans x%NQ y%NQ z%NQ.

Theorem NQle_trans: ∀ x y z, (x ≤ y)%NQ → (y ≤ z)%NQ → (x ≤ z)%NQ.
Proof.
intros * Hxy Hyz.
unfold "≤"%NQ in *.
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-eapply GQle_trans; [ apply Hxy | apply Hyz ].
-eapply GQle_trans; [ apply Hyz | apply Hxy ].
Qed.
Arguments NQle_trans x%NQ y%NQ z%NQ.

Theorem NQle_lt_trans: ∀ x y z, (x ≤ y)%NQ → (y < z)%NQ → (x < z)%NQ.
Proof.
intros * Hxy Hyz.
unfold "≤"%NQ, "<"%NQ in *.
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-eapply GQle_lt_trans; [ apply Hxy | apply Hyz ].
-eapply GQlt_le_trans; [ apply Hyz | apply Hxy ].
Qed.
Arguments NQle_lt_trans x%NQ y%NQ z%NQ.

Theorem NQlt_le_trans: ∀ x y z, (x < y)%NQ → (y ≤ z)%NQ → (x < z)%NQ.
Proof.
intros * Hxy Hyz.
unfold "≤"%NQ, "<"%NQ in *.
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-eapply GQlt_le_trans; [ apply Hxy | apply Hyz ].
-eapply GQle_lt_trans; [ apply Hyz | apply Hxy ].
Qed.
Arguments NQlt_le_trans x%NQ y%NQ z%NQ.

Theorem NQle_add_l : ∀ x y, (0 ≤ y)%NQ → (x ≤ y + x)%NQ.
Proof.
intros * Hy.
destruct y as [| py| py]; [ apply NQle_refl | | easy ].
simpl; unfold NQadd_pos_l.
destruct x as [| px| px]; [ easy | apply GQle_add_l | simpl ].
remember (GQcompare py px) as b eqn:Hb; symmetry in Hb.
destruct b; GQcompare_iff; [ easy | | easy ].
apply GQlt_le_incl.
now apply GQsub_lt.
Qed.

Theorem NQle_add_r : ∀ x y, (0 ≤ y)%NQ → (x ≤ x + y)%NQ.
Proof.
intros.
now rewrite NQadd_comm; apply NQle_add_l.
Qed.

Theorem NQadd_lt_mono_l : ∀ x y z, (y < z)%NQ ↔ (x + y < x + z)%NQ.
Proof.
intros *.
split; intros Hxy.
-destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
 +apply GQlt_add_r.
 +now apply GQadd_lt_mono_l.
 +cbn.
  remember (GQcompare xp yp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff; [ easy | easy | now apply GQsub_lt ].
 +cbn.
  remember (GQcompare xp yp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff; [ easy | easy | cbn ].
  apply (GQlt_trans _ xp); [ now apply GQsub_lt | apply GQlt_add_r ].
 +cbn in Hxy; cbn.
  remember (GQcompare xp yp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff.
  *subst xp.
   remember (GQcompare yp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff; [ | | easy ].
  --now subst yp; apply GQlt_irrefl in Hxy.
  --apply (GQlt_trans yp) in Hxy; [ | easy ].
    now apply GQlt_irrefl in Hxy.
  *remember (GQcompare xp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff; [ easy | cbn | easy ].
   now apply GQsub_lt_mono_r.
  *remember (GQcompare xp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff.
  --subst xp.
    apply (GQlt_trans yp) in Hxy; [ | easy ].
    now apply GQlt_irrefl in Hxy.
  --apply (GQlt_trans xp) in Hxy; [ | easy ].
    apply (GQlt_trans yp) in Hxy; [ | easy ].
    now apply GQlt_irrefl in Hxy.
  --now apply GQsub_lt_mono_l.
 +cbn.
  remember (GQcompare xp zp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff; [ easy | easy | now apply GQsub_lt ].
 +cbn in Hxy; cbn.
  remember (GQcompare xp yp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff.
  *subst xp.
   remember (GQcompare yp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff; [ | easy | ].
  --now subst yp; apply GQlt_irrefl in Hxy.
  --apply (GQlt_trans zp) in Hxy; [ | easy ].
    now apply GQlt_irrefl in Hxy.
  *remember (GQcompare xp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff.
  --subst xp.
    apply (GQlt_trans zp) in Hxy; [ | easy ].
    now apply GQlt_irrefl in Hxy.
  --now apply GQsub_lt_mono_r.
  --apply (GQlt_trans xp) in Hxy; [ | easy ].
    apply (GQlt_trans zp) in Hxy; [ | easy ].
    now apply GQlt_irrefl in Hxy.
  *remember (GQcompare xp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff; [ easy | easy | cbn ].
   now apply GQsub_lt_mono_l.
 +apply GQlt_add_r.
 +cbn.
  remember (GQcompare xp zp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff; [ easy | easy | cbn ].
  apply (GQlt_trans _ xp); [ now apply GQsub_lt | apply GQlt_add_r ].
 +now apply GQadd_lt_mono_l.
-destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
 +now apply GQlt_irrefl in Hxy.
 +cbn in Hxy.
  remember (GQcompare xp zp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff; [ easy | easy | exfalso ].
  apply GQnle_gt in Hxy; apply Hxy.
  now apply GQsub_le.
 +exfalso; apply GQnle_gt in Hxy; apply Hxy, GQle_add_r.
 +cbn in Hxy; cbn.
  now apply GQadd_lt_mono_l in Hxy.
 +cbn in Hxy; cbn.
  remember (GQcompare xp zp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff; [ easy | easy | ].
  apply (GQlt_trans xp) in Hxy; [ | apply GQlt_add_r ].
  now apply GQnle_gt in Hxy; apply Hxy, GQsub_le.
 +cbn in Hxy; cbn.
  remember (GQcompare xp yp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff.
  *subst xp.
   remember (GQcompare yp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff; [ | easy | easy ].
   now apply NQlt_irrefl in Hxy.
  *remember (GQcompare xp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff; [ now subst xp | | ].
  --cbn in Hxy.
    apply -> (GQadd_lt_mono_r (zp - xp)%GQ (yp - xp)%GQ xp) in Hxy.
    rewrite GQsub_add in Hxy; [ | easy ].
    rewrite GQsub_add in Hxy; [ | easy ].
    easy.
  --now apply (GQlt_trans _ xp).
  *cbn in Hxy.
   remember (GQcompare xp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff; [ easy | easy | cbn ].
   apply GQnle_gt; intros Hyz.
   apply GQnle_gt in Hxy; apply Hxy; clear Hxy.
   now apply GQsub_le_mono_l.
 +now apply NQlt_irrefl in Hxy.
 +cbn in Hxy; exfalso.
  apply GQnle_gt in Hxy; apply Hxy.
  apply GQle_add_r.
 +cbn in Hxy; exfalso.
  remember (GQcompare xp yp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff; [ easy | easy | cbn in Hxy ].
  apply GQnle_gt in Hxy; apply Hxy.
  now apply GQsub_le.
 +cbn in Hxy; cbn.
  remember (GQcompare xp yp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff.
  *subst xp.
   remember (GQcompare yp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff; [ | easy | easy ].
   now apply NQlt_irrefl in Hxy.
  *remember (GQcompare xp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff; [ now subst xp | | ].
  --cbn in Hxy.
    apply -> (GQadd_lt_mono_r (yp - xp)%GQ (zp - xp)%GQ xp) in Hxy.
    rewrite GQsub_add in Hxy; [ | easy ].
    rewrite GQsub_add in Hxy; [ | easy ].
    easy.
  --now apply (GQlt_trans _ xp).
  *cbn in Hxy.
   remember (GQcompare xp zp) as b2 eqn:Hb2; symmetry in Hb2.
   destruct b2; GQcompare_iff; [ now subst xp | | ].
  --now apply (GQlt_trans _ xp).
  --apply GQnle_gt in Hxy; apply GQnle_gt; intros H; apply Hxy.
    now apply GQsub_le_mono_l.
 +cbn in Hxy; cbn.
  remember (GQcompare xp yp) as b1 eqn:Hb1; symmetry in Hb1.
  destruct b1; GQcompare_iff; [ easy | easy | cbn in Hxy ].
  apply GQnle_gt in Hxy; apply Hxy.
  apply (GQle_trans _ xp); [ now apply GQsub_le | apply GQle_add_r ].
 +cbn in Hxy; cbn.
  apply GQnle_gt in Hxy; apply GQnle_gt; intros H; apply Hxy.
  now apply GQadd_le_mono_l.
Qed.
Arguments NQadd_lt_mono_l x%NQ y%NQ z%NQ.

Theorem NQadd_lt_mono_r : ∀ x y z, (x < y)%NQ ↔ (x + z < y + z)%NQ.
Proof.
intros *.
setoid_rewrite NQadd_comm.
apply NQadd_lt_mono_l.
Qed.
Arguments NQadd_lt_mono_r x%NQ y%NQ z%NQ.

Theorem NQlt_le_incl : ∀ x y, (x < y)%NQ → (x ≤ y)%NQ.
Proof.
intros * Hxy.
destruct x as [| xp| xp], y as [| yp| yp]; try easy.
-now apply GQlt_le_incl.
-now apply GQlt_le_incl.
Qed.

Theorem NQadd_le_mono : ∀ x y z t,
  (x ≤ y)%NQ → (z ≤ t)%NQ → (x + z ≤ y + t)%NQ.
Proof.
intros * Hxy Hzt.
destruct (NQeq_dec x y) as [H1| H1].
-subst x.
 destruct (NQeq_dec z t) as [H2| H2].
 +subst z; apply NQle_refl.
 +apply NQlt_le_incl, NQadd_lt_mono_l, NQnle_gt.
  now intros H; apply H2, NQle_antisymm.
-destruct (NQeq_dec z t) as [H2| H2].
 +subst z.
  apply NQlt_le_incl, NQadd_lt_mono_r, NQnle_gt.
  now intros H; apply H1, NQle_antisymm.
 +apply (NQle_trans _ (x + t)).
  *apply NQlt_le_incl, NQadd_lt_mono_l, NQnle_gt.
   now intros H; apply H2, NQle_antisymm.
  *apply NQlt_le_incl, NQadd_lt_mono_r, NQnle_gt.
   now intros H; apply H1, NQle_antisymm.
Qed.
Arguments NQadd_le_mono x%NQ y%NQ z%NQ t%NQ.

Theorem NQadd_le_mono_l : ∀ x y z, (x ≤ y)%NQ ↔ (z + x ≤ z + y)%NQ.
Proof.
intros.
split; intros Hxy.
-apply NQadd_le_mono; [ apply NQle_refl | easy ].
-apply (NQadd_le_mono _ _ (- z) (- z)) in Hxy; [ | apply NQle_refl ].
 replace (z + x)%NQ with (x + z)%NQ in Hxy by apply NQadd_comm.
 replace (z + y)%NQ with (y + z)%NQ in Hxy by apply NQadd_comm.
 now do 2 rewrite NQadd_sub in Hxy.
Qed.
Arguments NQadd_le_mono_l x%NQ y%NQ z%NQ.

Theorem NQadd_le_mono_r : ∀ x y z, (x ≤ y)%NQ ↔ (x + z ≤ y + z)%NQ.
Proof.
intros.
setoid_rewrite NQadd_comm.
apply NQadd_le_mono_l.
Qed.
Arguments NQadd_le_mono_r x%NQ y%NQ z%NQ.

Theorem NQadd_le_lt_mono : ∀ x y z t, (x ≤ y → z < t → x + z < y + t)%NQ.
Proof.
intros * Hxy Hzt.
destruct (NQeq_dec x y) as [H1| H1].
-subst x.
 destruct (NQeq_dec z t) as [H2| H2].
 +now subst z; apply NQlt_irrefl in Hzt.
 +now apply NQadd_lt_mono_l.
-destruct (NQeq_dec z t) as [H2| H2].
 +subst z.
  apply NQadd_lt_mono_r, NQnle_gt.
  now intros H; apply H1, NQle_antisymm.
 +apply (NQle_lt_trans _ (x + t)).
  *apply NQadd_le_mono; [ apply NQle_refl | ].
   now apply NQlt_le_incl.
  *apply NQadd_lt_mono_r, NQnle_gt.
   now intros H; apply H1, NQle_antisymm.
Qed.
Arguments NQadd_le_lt_mono x%NQ y%NQ z%NQ t%NQ.

Theorem NQadd_le_r : ∀ x y z, (x + z ≤ y + z ↔ x ≤ y)%NQ.
Proof.
intros.
split; intros H.
-apply (NQadd_le_mono _ _ (- z) (- z)) in H; [ | apply NQle_refl ].
 now do 2 rewrite NQadd_sub in H.
-apply NQadd_le_mono; [ easy | apply NQle_refl ].
Qed.
Arguments NQadd_le_r x%NQ y%NQ z%NQ.

Theorem NQopp_le_mono : ∀ x y, (x ≤ y)%NQ ↔ (- y ≤ - x)%NQ.
Proof. intros; now destruct x, y. Qed.

Theorem NQsub_le_mono : ∀ x y z t,
  (x ≤ y)%NQ → (z ≤ t)%NQ → (x - t ≤ y - z)%NQ.
Proof.
intros * Hxy Hzt.
destruct (NQeq_dec x y) as [H1| H1].
-subst x.
 destruct (NQeq_dec z t) as [H2| H2].
 +subst z; apply NQle_refl.
 +apply NQlt_le_incl, NQadd_lt_mono_l, NQnle_gt.
  intros H; apply H2.
  apply NQle_antisymm; [ easy | ].
  now apply NQopp_le_mono.
-destruct (NQeq_dec z t) as [H2| H2].
 +subst z.
  apply NQlt_le_incl, NQadd_lt_mono_r, NQnle_gt.
  now intros H; apply H1, NQle_antisymm.
 +apply (NQle_trans _ (y - t)).
  *apply NQlt_le_incl, NQadd_lt_mono_r, NQnle_gt.
   now intros H; apply H1, NQle_antisymm.
  *apply NQlt_le_incl, NQadd_lt_mono_l, NQnle_gt.
   intros H; apply H2, NQle_antisymm; [ easy | ].
   now apply NQopp_le_mono.
Qed.
Arguments NQsub_le_mono x%NQ y%NQ z%NQ t%NQ.

Theorem NQsub_lt : ∀ x y, (0 < x)%NQ → (y - x < y)%NQ.
Proof.
intros * Hxy.
apply (NQadd_lt_mono_r _ _ x).
rewrite NQsub_add.
replace y with (y + 0)%NQ at 1 by apply NQadd_0_r.
now apply NQadd_lt_mono_l.
Qed.

Theorem NQadd_cancel_l: ∀ x y z, (x + y = x + z)%NQ ↔ (y = z)%NQ.
Proof.
intros.
split; intros Hxy; [ | now subst y ].
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-rewrite NQadd_0_r in Hxy; cbn in Hxy.
 injection Hxy as H; symmetry in H; rewrite GQadd_comm in H.
 now apply GQadd_no_neutral in H.
-rewrite NQadd_0_r in Hxy; cbn in Hxy.
 remember (GQcompare xp zp) as b eqn:Hb; symmetry in Hb.
 destruct b; [ easy | easy | GQcompare_iff ].
 injection Hxy as H; symmetry in H.
 now apply GQsub_no_neutral in H.
-rewrite NQadd_0_r in Hxy; cbn in Hxy.
 injection Hxy as H; rewrite GQadd_comm in H.
 now apply GQadd_no_neutral in H.
-cbn in Hxy.
 remember GQadd as f; injection Hxy as H; subst f.
 now apply GQadd_cancel_l in H; subst.
-cbn in Hxy.
 remember (GQcompare xp zp) as b eqn:Hb; symmetry in Hb.
 destruct b; [ easy | easy | GQcompare_iff ].
 remember GQadd as f; injection Hxy as H; subst f.
 apply (GQadd_cancel_r _ _ zp) in H.
 rewrite GQsub_add in H; [ | easy ].
 rewrite <- GQadd_assoc, GQadd_comm in H.
 now apply GQadd_no_neutral in H.
-rewrite NQadd_0_r in Hxy; cbn in Hxy.
 remember (GQcompare xp yp) as b eqn:Hb; symmetry in Hb.
 destruct b; [ easy | easy | GQcompare_iff ].
 injection Hxy as H.
 now apply GQsub_no_neutral in H.
-cbn in Hxy.
 remember (GQcompare xp yp) as b eqn:Hb; symmetry in Hb.
 destruct b; [ easy | easy | GQcompare_iff ].
 remember GQadd as f; injection Hxy as H; subst f.
 apply (GQadd_cancel_r _ _ yp) in H.
 rewrite GQsub_add in H; [ | easy ].
 rewrite <- GQadd_assoc, GQadd_comm in H.
 symmetry in H.
 now apply GQadd_no_neutral in H.
-cbn in Hxy; f_equal.
 remember (GQcompare xp yp) as b1 eqn:Hb1; symmetry in Hb1.
 remember (GQcompare xp zp) as b2 eqn:Hb2; symmetry in Hb2.
 destruct b1; GQcompare_iff.
 +destruct b2; [ now GQcompare_iff; subst | easy | easy ].
 +destruct b2; [ easy | GQcompare_iff | easy ].
  remember GQsub as f; injection Hxy as H; subst f.
  apply (GQadd_cancel_r _ _ xp) in H.
  now do 2 rewrite GQsub_add in H.
 +destruct b2; [ easy | easy | GQcompare_iff ].
  remember GQsub as f; injection Hxy as H; subst f.
  apply (GQadd_cancel_r _ _ yp) in H.
  rewrite GQsub_add in H; [ | easy ].
  apply (GQadd_cancel_r _ _ zp) in H.
  rewrite GQadd_add_swap in H.
  rewrite GQsub_add in H; [ | easy ].
  now apply GQadd_cancel_l in H.
-rewrite NQadd_0_r in Hxy; cbn in Hxy.
 remember (GQcompare xp zp) as b eqn:Hb; symmetry in Hb.
 destruct b; [ easy | easy | GQcompare_iff ].
 injection Hxy as H; symmetry in H.
 now apply GQsub_no_neutral in H.
-rewrite NQadd_0_r in Hxy; cbn in Hxy.
 injection Hxy as H; symmetry in H.
 rewrite GQadd_comm in H.
 now apply GQadd_no_neutral in H.
-rewrite NQadd_0_r in Hxy; cbn in Hxy.
 remember (GQcompare xp yp) as b eqn:Hb; symmetry in Hb.
 destruct b; [ easy | easy | GQcompare_iff ].
 injection Hxy as H.
 now apply GQsub_no_neutral in H.
-(* same as above ⇒ lemma to do? *)
 cbn in Hxy; f_equal.
 remember (GQcompare xp yp) as b1 eqn:Hb1; symmetry in Hb1.
 remember (GQcompare xp zp) as b2 eqn:Hb2; symmetry in Hb2.
 destruct b1; GQcompare_iff.
 +destruct b2; [ now GQcompare_iff; subst | easy | easy ].
 +destruct b2; [ easy | GQcompare_iff | easy ].
  remember GQsub as f; injection Hxy as H; subst f.
  apply (GQadd_cancel_r _ _ xp) in H.
  now do 2 rewrite GQsub_add in H.
 +destruct b2; [ easy | easy | GQcompare_iff ].
  remember GQsub as f; injection Hxy as H; subst f.
  apply (GQadd_cancel_r _ _ yp) in H.
  rewrite GQsub_add in H; [ | easy ].
  apply (GQadd_cancel_r _ _ zp) in H.
  rewrite GQadd_add_swap in H.
  rewrite GQsub_add in H; [ | easy ].
  now apply GQadd_cancel_l in H.
-cbn in Hxy.
 remember (GQcompare xp yp) as b eqn:Hb; symmetry in Hb.
 destruct b; [ easy | easy | GQcompare_iff ].
 remember GQadd as f; injection Hxy as H; subst f.
 apply (GQadd_cancel_r _ _ yp) in H.
 rewrite GQsub_add in H; [ | easy ].
 rewrite <- GQadd_assoc, GQadd_comm in H.
 symmetry in H.
 now apply GQadd_no_neutral in H.
-(* déjà vu *)
 rewrite NQadd_0_r in Hxy; cbn in Hxy.
 injection Hxy as H; rewrite GQadd_comm in H.
 now apply GQadd_no_neutral in H.
-cbn in Hxy.
 remember (GQcompare xp zp) as b eqn:Hb; symmetry in Hb.
 destruct b; [ easy | easy | GQcompare_iff ].
 remember GQadd as f; injection Hxy as H; subst f.
 apply (GQadd_cancel_r _ _ zp) in H.
 rewrite GQsub_add in H; [ | easy ].
 rewrite <- GQadd_assoc, GQadd_comm in H.
 now apply GQadd_no_neutral in H.
-cbn in Hxy; f_equal.
 remember GQadd as f; injection Hxy as H; subst f.
 now apply GQadd_cancel_l in H.
Qed.

Theorem NQadd_cancel_r: ∀ x y z, (x + z = y + z)%NQ ↔ (x = y)%NQ.
Proof.
intros.
setoid_rewrite NQadd_comm.
apply NQadd_cancel_l.
Qed.

Theorem NQopp_add_distr : ∀ x y, (- (x + y))%NQ = (- x - y)%NQ.
Proof.
intros.
destruct x as [| xp| xp], y as [| yp| yp]; try easy.
-now cbn; destruct (GQcompare xp yp).
-now cbn; destruct (GQcompare xp yp).
Qed.

Theorem NQsub_add_distr : ∀ x y z, (x - (y + z))%NQ = (x - y - z)%NQ.
Proof.
intros.
rewrite <- NQadd_assoc.
apply NQadd_cancel_l.
apply NQopp_add_distr.
Qed.

Theorem NQmul_pair : ∀ x y z t,
  y ≠ 0 → t ≠ 0 → ((x // y) * (z // t) = (x * z) // (y * t))%NQ.
Proof.
intros * Hy Ht; simpl.
unfold "*"%GQ, "//"%NQ; simpl.
destruct x; [ easy | ].
destruct z; [ now rewrite Nat.mul_0_r | simpl ].
f_equal.
now apply GQmul_pair.
Qed.

Theorem NQmul_comm : ∀ x y, (x * y = y * x)%NQ.
Proof.
intros.
unfold "*".
destruct x as [| px| px], y as [| py| py]; try easy; simpl;
f_equal; apply GQmul_comm.
Qed.

Theorem NQmul_mul_swap : ∀ x y z, (x * y * z = x * z * y)%NQ.
Proof.
intros.
unfold "*"%NQ.
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl;
f_equal; apply GQmul_mul_swap.
Qed.

Theorem NQmul_assoc : ∀ x y z, (x * (y * z) = (x * y) * z)%NQ.
Proof.
intros.
symmetry.
rewrite NQmul_comm.
remember (x * y)%NQ as t eqn:Ht.
rewrite NQmul_comm in Ht; rewrite Ht.
setoid_rewrite NQmul_comm.
apply NQmul_mul_swap.
Qed.

Theorem NQmul_add_distr_l : ∀ x y z, (x * (y + z) = x * y + x * z)%NQ.
Proof.
intros.
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl.
-f_equal; apply GQmul_add_distr_l.
-rewrite GQcompare_mul_cancel_l.
 unfold NQmul_pos_l.
 remember (GQcompare py pz) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff; [ easy | | ].
 +now f_equal; apply GQmul_sub_distr_l.
 +now f_equal; apply GQmul_sub_distr_l.
-rewrite GQcompare_mul_cancel_l.
 unfold NQmul_pos_l.
 remember (GQcompare py pz) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff; [ easy | | ].
 +now f_equal; apply GQmul_sub_distr_l.
 +now f_equal; apply GQmul_sub_distr_l.
-f_equal; apply GQmul_add_distr_l.
-f_equal; apply GQmul_add_distr_l.
-rewrite GQcompare_mul_cancel_l.
 unfold NQmul_neg_l.
 remember (GQcompare py pz) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff; [ easy | | ].
 +now f_equal; apply GQmul_sub_distr_l.
 +now f_equal; apply GQmul_sub_distr_l.
-rewrite GQcompare_mul_cancel_l.
 unfold NQmul_neg_l.
 remember (GQcompare py pz) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff; [ easy | | ].
 +now f_equal; apply GQmul_sub_distr_l.
 +now f_equal; apply GQmul_sub_distr_l.
-f_equal; apply GQmul_add_distr_l.
Qed.

Theorem NQmul_add_distr_r : ∀ x y z, ((x + y) * z = x * z + y * z)%NQ.
Proof.
intros.
setoid_rewrite NQmul_comm.
apply NQmul_add_distr_l.
Qed.

Theorem NQmul_sub_distr_l : ∀ x y z, (x * (y - z) = x * y - x * z)%NQ.
Proof.
intros.
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl.
-rewrite GQcompare_mul_cancel_l.
 unfold NQmul_pos_l.
 remember (GQcompare py pz) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff; [ easy | | ].
 +now f_equal; apply GQmul_sub_distr_l.
 +now f_equal; apply GQmul_sub_distr_l.
-f_equal; apply GQmul_add_distr_l.
-f_equal; apply GQmul_add_distr_l.
-rewrite GQcompare_mul_cancel_l.
 unfold NQmul_pos_l.
 remember (GQcompare py pz) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff; [ easy | | ].
 +now f_equal; apply GQmul_sub_distr_l.
 +now f_equal; apply GQmul_sub_distr_l.
-rewrite GQcompare_mul_cancel_l.
 unfold NQmul_neg_l.
 remember (GQcompare py pz) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff; [ easy | | ].
 +now f_equal; apply GQmul_sub_distr_l.
 +now f_equal; apply GQmul_sub_distr_l.
-f_equal; apply GQmul_add_distr_l.
-f_equal; apply GQmul_add_distr_l.
-rewrite GQcompare_mul_cancel_l.
 unfold NQmul_neg_l.
 remember (GQcompare py pz) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff; [ easy | | ].
 +now f_equal; apply GQmul_sub_distr_l.
 +now f_equal; apply GQmul_sub_distr_l.
Qed.

Theorem NQmul_sub_distr_r : ∀ x y z, ((x - y) * z = x * z - y * z)%NQ.
Proof.
intros.
setoid_rewrite NQmul_comm.
apply NQmul_sub_distr_l.
Qed.

Theorem NQeq_mul_0 : ∀ x y, (x * y = 0 → x = 0 ∨ y = 0)%NQ.
Proof.
intros * Hxy.
destruct x as [| xp| xp]; [ now left | now right; destruct y | ].
destruct y as [| yp| yp]; [ now right | easy | easy ].
Qed.

Theorem NQmul_le_mono_nonneg_l : ∀ x y z, (0 ≤ x → y ≤ z → x * y ≤ x * z)%NQ.
Proof.
intros * Hx Hyz.
destruct x as [| xp| xp]; [ easy | | easy ].
destruct y as [| yp| yp]; [ now destruct z | | ].
-destruct z as [| zp| zp]; [ easy | | easy ].
 now apply GQmul_le_mono_l.
-destruct z as [| zp| zp]; [ easy | easy | ].
 now apply GQmul_le_mono_l.
Qed.

Theorem NQmul_le_mono_nonneg_r : ∀ x y z, (0 ≤ x → y ≤ z → y * x ≤ z * x)%NQ.
Proof.
setoid_rewrite NQmul_comm.
apply NQmul_le_mono_nonneg_l.
Qed.

Theorem NQmul_lt_mono_pos_l : ∀ x y z,
  (0 < x)%NQ → (y < z)%NQ ↔ (x * y < x * z)%NQ.
Proof.
intros * Hx.
destruct x as [| xp| xp]; [ easy | | easy ].
destruct y as [| yp| yp]; [ now destruct z | | ].
-destruct z as [| zp| zp]; [ easy | cbn | easy ].
 apply GQmul_lt_mono_l.
-destruct z as [| zp| zp]; [ easy | easy | cbn ].
 apply GQmul_lt_mono_l.
Qed.

Theorem NQmul_lt_mono_pos_r : ∀ x y z,
  (0 < x)%NQ → (y < z)%NQ ↔ (y * x < z * x)%NQ.
Proof.
setoid_rewrite NQmul_comm.
apply NQmul_lt_mono_pos_l.
Qed.

Theorem NQle_pair : ∀ x y z t,
  y ≠ 0 → t ≠ 0 → (x // y ≤ z // t)%NQ ↔ x * t ≤ y * z.
Proof.
intros * Hy Ht.
unfold "≤"%NQ.
remember (x // y)%NQ as a eqn:Ha; symmetry in Ha.
remember (z // t)%NQ as b eqn:Hb; symmetry in Hb.
move b before a.
destruct a as [| a| a]; [ | | now destruct x ].
-destruct x; [ | easy ].
 split; [ simpl; flia | intros H ].
 destruct b; [ easy | easy | now destruct z ].
-destruct b as [| b| b]; [ | | now destruct z ].
 +split; [ easy | intros H ].
  destruct z; [ | easy ].
  rewrite Nat.mul_0_r in H.
  apply Nat.le_0_r in H.
  apply Nat.eq_mul_0 in H.
  destruct H; [ now subst x | easy ].
 +destruct x; [ easy | simpl in Ha ].
  injection Ha; clear Ha; intros Ha.
  destruct z; [ easy | simpl in Hb ].
  injection Hb; clear Hb; intros Hb.
  subst a b.
  now apply GQle_pair.
Qed.

Theorem NQlt_pair : ∀ a b c d,
  b ≠ 0 → d ≠ 0 → (a // b < c // d)%NQ ↔ a * d < b * c.
Proof.
intros * Hb Hd.
unfold "<"%GQ, "//"%NQ; simpl.
destruct a.
-destruct c; [ now rewrite Nat.mul_0_r | simpl ].
 split; [ intros _ | easy ].
 destruct b; [ easy | simpl; flia ].
-destruct c; [ now rewrite Nat.mul_0_r | simpl ].
 now apply GQlt_pair.
Qed.

Theorem NQeq_pair : ∀ x y z t : nat,
   y ≠ 0 → t ≠ 0 → (x // y = z // t)%NQ ↔ x * t = y * z.
Proof.
intros * Hy Ht.
remember (x // y)%NQ as a eqn:Ha; symmetry in Ha.
remember (z // t)%NQ as b eqn:Hb; symmetry in Hb.
move b before a.
destruct a as [| a| a]; [ | | now destruct x ].
-destruct x; [ simpl | easy ].
 rewrite Nat.mul_comm.
 split; intros H.
 +rewrite <- H in Hb; now destruct z.
 +symmetry in H.
  apply Nat.eq_mul_0 in H.
  destruct H; [ | easy ].
  subst z; now rewrite <- Hb.
-destruct b as [| b| b]; [ | | now destruct z ].
 +split; [ easy | intros H ].
  destruct z; [ | easy ].
  rewrite Nat.mul_0_r in H.
  apply Nat.eq_mul_0 in H.
  destruct H; [ now subst x | easy ].
 +destruct x; [ easy | simpl in Ha ].
  injection Ha; clear Ha; intros Ha.
  destruct z; [ easy | simpl in Hb ].
  injection Hb; clear Hb; intros Hb.
  subst a b.
  split; intros H.
  *apply GQeq_pair; try easy.
   injection H; clear H; intros H.
   now apply GQeq_eq.
  *apply GQeq_pair in H; try easy.
   now rewrite H.
Qed.

Theorem NQpair_diag : ∀ a, a ≠ 0 → (a // a = 1)%NQ.
Proof.
intros.
unfold "//"%NQ.
destruct a; [ easy | ].
rewrite GQpair_diag; [ now rewrite GQpair_diag | easy ].
Qed.

Theorem NQmul_1_l : ∀ a, (1 * a)%NQ = a.
Proof.
intros.
unfold "*"%NQ; simpl.
rewrite GQpair_diag; [ | easy ].
unfold NQmul_pos_l.
destruct a; [ easy | | ]; now rewrite GQmul_1_l.
Qed.

Theorem NQmul_1_r : ∀ a, (a * 1)%NQ = a.
Proof.
intros.
rewrite NQmul_comm.
apply NQmul_1_l.
Qed.

Theorem NQmul_0_l : ∀ a, (0 * a)%NQ = 0%NQ.
Proof. easy. Qed.

Theorem NQmul_0_r : ∀ a, (a * 0)%NQ = 0%NQ.
Proof. intros; now rewrite NQmul_comm. Qed.

Theorem NQadd_pair : ∀ a b c d,
  b ≠ 0 → d ≠ 0 → (a // b + c // d = (a * d + b * c) // (b * d))%NQ.
Proof.
intros * Hb Hd.
unfold "+"%NQ.
remember (a // b)%NQ as ab eqn:Hab; symmetry in Hab.
destruct ab as [| pab| pab]; [ | | now destruct a ].
-unfold "//"%NQ in Hab.
 destruct a; [ simpl | easy ].
 rewrite <- NQmul_pair; [ | easy | easy ].
 rewrite NQpair_diag; [ | easy ].
 now rewrite NQmul_1_l.
-remember (c // d)%NQ as cd eqn:Hcd; symmetry in Hcd.
 move cd before pab.
 destruct cd as [| pcd| pcd]; [ | | now destruct c ].
 +unfold "//"%NQ in Hcd.
  destruct c; [ | easy ].
  rewrite Nat.mul_0_r, Nat.add_0_r; simpl.
  rewrite <- NQmul_pair; [ | easy | easy ].
  rewrite NQpair_diag; [ | easy ].
  now rewrite NQmul_1_r.
 +unfold NQadd_pos_l.
  unfold "//"%NQ.
  remember (a * d + b * c) as e eqn:He; symmetry in He.
  destruct e.
  *apply Nat.eq_add_0 in He.
   destruct He as (H1, H2).
   apply Nat.eq_mul_0 in H1.
   destruct H1; [ now subst a | easy ].
  *f_equal.
   destruct a; [ easy | ].
   destruct c; [ easy | ].
   simpl in Hab, Hcd.
   injection Hab; clear Hab; intros Hab.
   injection Hcd; clear Hcd; intros Hcd.
   subst pab pcd.
   rewrite <- He.
   now apply GQadd_pair.
Qed.

Theorem NQden_0 : ∀ a, (a // 0 = a // 1)%NQ.
Proof. easy. Qed.

Theorem NQsub_pair_pos : ∀ a b c d,
  b ≠ 0 → d ≠ 0 → b * c ≤ a * d
  → (a // b - c // d)%NQ = ((a * d - b * c) // (b * d))%NQ.
Proof.
intros * Hb Hd Hle.
destruct b; [ flia Hb | ].
destruct d; [ flia Hd | ].
unfold "-"%NQ.
destruct a. {
  destruct c; [ easy | cbn in Hle; flia Hle ].
}
remember (S a // S b)%NQ as ab eqn:Hab; symmetry in Hab.
destruct ab as [| pab| pab]; [ easy | | easy ].
injection Hab; clear Hab; intros Hab; subst pab.
-remember (S a // S b)%NQ as ab eqn:Hab; symmetry in Hab.
 destruct ab as [| pab| pab]; [ easy | | easy ].
 injection Hab; clear Hab; intros Hab; subst pab.
 destruct c.
 +rewrite Nat.mul_0_r, Nat.sub_0_r.
  rewrite <- NQmul_pair; [ | easy | easy ].
  rewrite NQpair_diag; [ | easy ].
  now rewrite NQmul_1_r.
 +remember (S a) as sa; remember (S b) as sb; simpl; subst sa sb.
  unfold "//"%NQ.
  remember (S a * S d - S b * S c) as x eqn:Hx; symmetry in Hx.
  destruct x.
  *assert (H : S a * S d = S b * S c) by flia Hle Hx.
   assert (Ha : S a ≠ 0) by easy.
   assert (Hc : S c ≠ 0) by easy.
   rewrite (proj2 (GQeq_pair _ _ _ _ Ha Hb Hc Hd)); [ | easy ].
   now rewrite (proj2 (GQcompare_eq_iff _ _)).
  *remember (GQcompare (S a // S b) (S c // S d)) as b1 eqn:Hb1.
   symmetry in Hb1.
   destruct b1; GQcompare_iff.
  --apply GQeq_pair in Hb1; [ | easy | easy | easy | easy ].
    now rewrite Hb1, Nat.sub_diag in Hx.
  --apply -> GQlt_pair in Hb1; [ | easy | easy | easy | easy ].
    setoid_rewrite Nat.mul_comm in Hb1.
    flia Hle Hb1.
  --f_equal.
    setoid_rewrite Nat.mul_comm in Hle.
    rewrite GQsub_pair; [ now rewrite Hx| easy | easy | easy | easy | ].
    setoid_rewrite Nat.mul_comm.
    flia Hle Hx.
Qed.

Theorem NQsub_pair_neg : ∀ a b c d,
  b ≠ 0 → d ≠ 0 → a * d < b * c
  → (a // b - c // d)%NQ = (- (b * c - a * d) // (b * d))%NQ.
Proof.
intros * Hb Hd Hlt.
destruct b; [ flia Hb | ].
destruct d; [ flia Hd | ].
unfold "-"%NQ.
destruct a.
-destruct c; [ now rewrite Nat.mul_0_r | ].
 remember (S b) as x; simpl; subst x.
 rewrite Nat.sub_0_r.
 remember (S b * S c) as bc eqn:Hbc; symmetry in Hbc.
 destruct bc; [ easy | rewrite <- Hbc ].
 rewrite <- NQmul_pair; [ | easy | easy ].
 rewrite NQpair_diag; [ | easy ].
 now rewrite NQmul_1_l.
-remember (S a // S b)%NQ as ab eqn:Hab; symmetry in Hab.
 destruct ab as [| pab| pab]; [ easy | | easy ].
 injection Hab; clear Hab; intros Hab; subst pab.
 destruct c; [ now rewrite Nat.mul_0_r in Hlt | ].
 remember (S a) as sa; remember (S b) as sb; simpl; subst sa sb.
 unfold "//"%NQ.
 remember (S b * S c - S a * S d) as x eqn:Hx; symmetry in Hx.
 destruct x; [ flia Hlt Hx | ].
 remember (GQcompare (S a // S b) (S c // S d)) as b1 eqn:Hb1.
 symmetry in Hb1.
 destruct b1; GQcompare_iff.
 *apply GQeq_pair in Hb1; [ flia Hlt Hb1 | easy | easy | easy | easy ].
 *f_equal.
  setoid_rewrite Nat.mul_comm in Hlt.
  rewrite GQsub_pair; try easy.
  rewrite <- Hx.
  f_equal; [ f_equal; apply Nat.mul_comm | apply Nat.mul_comm ].
 *apply -> GQlt_pair in Hb1; [ | easy | easy | easy | easy ].
  setoid_rewrite Nat.mul_comm in Hb1.
  flia Hlt Hb1.
Qed.

Theorem NQpair_add_l : ∀ a b c,
  ((a + b) // c)%NQ = (a // c + b // c)%NQ.
Proof.
intros.
destruct c. {
  do 3 rewrite NQden_0.
  rewrite NQadd_pair; [ | easy | easy ].
  now rewrite Nat.mul_1_l, Nat.mul_1_r.
}
rewrite NQadd_pair; [ | easy | easy ].
rewrite Nat.mul_comm, <- Nat.mul_add_distr_l.
rewrite <- NQmul_pair; [ | easy | easy ].
rewrite NQpair_diag; [ | easy ].
now rewrite NQmul_1_l.
Qed.

Theorem NQpair_sub_l : ∀ a b c,
  b ≤ a → ((a - b) // c)%NQ = (a // c - b // c)%NQ.
Proof.
intros * Hba.
destruct c. {
  do 3 rewrite NQden_0.
  rewrite NQsub_pair_pos; [ | easy | easy | ].
  -now rewrite Nat.mul_1_r, Nat.mul_1_l.
  -now rewrite Nat.mul_comm; apply Nat.mul_le_mono_r.
}
rewrite NQsub_pair_pos; [ | easy | easy | ]; cycle 1. {
  now rewrite Nat.mul_comm; apply Nat.mul_le_mono_r.
}
rewrite Nat.mul_comm, <- Nat.mul_sub_distr_l.
rewrite <- NQmul_pair; [ | easy | easy ].
rewrite NQpair_diag; [ | easy ].
now rewrite NQmul_1_l.
Qed.

Definition NQfrac x := ((NQnum x mod NQden x) // NQden x)%NQ.
Definition NQintg x := NQnum x / NQden x.

Arguments NQfrac x%NQ.
Arguments NQintg x%NQ.

Theorem NQfrac_pair : ∀ a b, NQfrac (a // b) = ((a mod b) // b)%NQ.
Proof.
intros.
destruct (zerop a) as [Ha| Ha].
-subst a; destruct b; [ easy | cbn; now rewrite Nat.sub_diag ].
-destruct a; [ easy | clear Ha ].
 unfold NQfrac; cbn.
 destruct b.
 +rewrite GQnum_pair_0_r; [ | easy ].
  now rewrite GQden_pair_0_r.
 +rewrite GQnum_pair.
  rewrite GQden_pair.
  remember Nat.gcd as f; remember Nat.modulo as g; cbn; subst f g.
  remember (Nat_ggcd.ggcd (S a) (S b)) as g eqn:Hg.
  destruct g as (g, (aa, bb)).
  rewrite <- Nat_ggcd.ggcd_gcd, <- Hg.
  remember S as f; cbn; subst f.
  specialize (Nat_ggcd.ggcd_correct_divisors (S a) (S b)) as H.
  rewrite <- Hg in H.
  destruct H as (Ha, Hb).
  rewrite Ha, Hb.
  setoid_rewrite Nat.mul_comm.
  assert (Hgz : g ≠ 0) by now intros H; subst g.
  rewrite Nat.div_mul; [ | easy ].
  rewrite Nat.div_mul; [ | easy ].
  assert (Hbb : bb ≠ 0) by now intros H; subst bb; rewrite Nat.mul_0_r in Hb.
  rewrite Nat.mul_mod_distr_r; [ | easy | easy ].
  rewrite <- NQmul_pair; [ | easy | easy ].
  rewrite NQpair_diag; [ | easy ].
  now rewrite NQmul_1_r.
Qed.

Theorem NQden_neq_0 : ∀ x, NQden x ≠ 0.
Proof.
intros x.
destruct x; [ easy | | ].
-unfold NQden, GQden.
 now rewrite Nat.add_1_r.
-unfold NQden, GQden.
 now rewrite Nat.add_1_r.
Qed.

Theorem NQnum_pair_1_r : ∀ a, NQnum (a // 1) = a.
Proof.
intros.
destruct a; [ easy | cbn ].
now apply GQnum_pair_1_r.
Qed.

Theorem NQden_pair_1_r : ∀ a, NQden (a // 1) = 1.
Proof.
intros.
destruct a; [ easy | cbn ].
now apply GQden_pair_1_r.
Qed.

Theorem NQnum_pair : ∀ a b, NQnum (a // b) = a / Nat.gcd a (max 1 b).
Proof.
intros.
destruct a; [ now destruct b | ].
destruct b. {
  rewrite NQden_0, Nat.gcd_1_r, NQnum_pair_1_r.
  symmetry; apply Nat.div_1_r.
}
unfold "//"%NQ.
rewrite Nat.max_r; [ | flia ].
unfold NQnum.
now rewrite GQnum_pair.
Qed.

Theorem NQden_pair : ∀ a b, NQden (a // b) = max 1 (b / Nat.gcd a b).
Proof.
intros.
destruct a.
-rewrite Nat.gcd_0_l.
 destruct b; [ easy | ].
 now rewrite Nat.div_same.
-destruct b.
 +rewrite NQden_0.
  rewrite Nat.gcd_0_r.
  rewrite Nat.div_0_l; [ | easy ].
  now rewrite NQden_pair_1_r.
 +unfold "//"%NQ.
  unfold NQden.
  rewrite GQden_pair.
  remember Nat.gcd as f.
  remember Nat.max as g; cbn; subst f g.
  symmetry; apply Nat.max_r.
  apply Nat.neq_0_lt_0.
  intros H.
  apply Nat.div_small_iff in H; [ | ].
  *apply Nat.nle_gt in H; apply H.
   now apply Nat_gcd_le_r.
  *intros H1.
   now apply Nat.gcd_eq_0 in H1.
Qed.

Theorem NQnum_den : ∀ x, (0 ≤ x)%NQ → x = (NQnum x // NQden x)%NQ.
Proof.
intros x Hx.
destruct x as [| px| px]; [ easy | | easy ].
unfold NQnum, NQden, "//"%NQ.
remember (GQnum px) as a eqn:Ha; symmetry in Ha.
destruct a; [ now apply GQnum_neq_0 in Ha | ].
rewrite <- Ha; f_equal.
apply GQnum_den.
Qed.

Theorem NQfrac_le : ∀ x, (0 ≤ x)%NQ → (NQfrac x ≤ x)%NQ.
Proof.
intros x Hx.
unfold NQfrac.
destruct x as [| xp| xp]; [ easy | | easy ].
cbn.
rewrite NQnum_den; [ | easy ].
apply NQle_pair; [ apply GQden_neq_0 | apply NQden_neq_0 | ].
cbn; rewrite Nat.mul_comm.
apply Nat.mul_le_mono_l, Nat.mod_le, GQden_neq_0.
Qed.

Require Import Summation.

Definition NQ_ord_ring_def :=
  {| rng_t := NQ;
     rng_zero := 0%NQ;
     rng_add := NQadd;
     rng_sub := NQsub;
     rng_mul := NQmul;
     rng_le := NQle |}.

Canonical Structure NQ_ord_ring_def.

Definition NQ_ord_ring :=
  {| rng_add_0_l := NQadd_0_l;
     rng_add_comm := NQadd_comm;
     rng_add_assoc := NQadd_assoc;
     rng_sub_diag := NQsub_diag;
     rng_mul_comm := NQmul_comm;
     rng_mul_assoc := NQmul_assoc;
     rng_mul_add_distr_l := NQmul_add_distr_l;
     rng_mul_sub_distr_l := NQmul_sub_distr_l;
     rng_le_refl := NQle_refl;
     rng_le_antisymm := NQle_antisymm;
     rng_add_le_compat := NQadd_le_mono |}.

Theorem NQsummation_pair_distr_r (rgi := nat_ord_ring) (rgq := NQ_ord_ring) :
   ∀ b e (g : _ → nat) a,
   ((Σ (i = b, e), g i) // a = Σ (i = b, e), (g i // a))%NQ.
Proof.
intros.
destruct (le_dec b e) as [Heb| Hbe]; cycle 1. {
  apply Nat.nle_gt in Hbe.
  rewrite summation_empty; [ | easy ].
  rewrite summation_empty; [ | easy ].
  easy.
}
remember (e - b) as n eqn:Hn.
assert (H : e = b + n). {
  rewrite Hn, Nat.add_comm.
  now rewrite Nat.sub_add.
}
subst e; clear Hn Heb.
rewrite summation_shift; [ symmetry | flia ].
rewrite summation_shift; [ symmetry | flia ].
rewrite Nat.add_comm, Nat.add_sub.
induction n; [ now do 2 rewrite summation_only_one | ].
rewrite summation_split_last; [ symmetry | apply Nat.le_0_l ].
rewrite summation_split_last; [ symmetry | apply Nat.le_0_l ].
rewrite <- IHn.
destruct a; [ do 3 rewrite NQden_0 | ]; now rewrite <- NQpair_add_l.
Qed.
