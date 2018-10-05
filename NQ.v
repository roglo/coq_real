(* Positive rationals where num and den are always common primes *)
(* allowing us to use Leibnitz' equality. *)

Require Import Utf8 Arith (* Morphisms *) Psatz.
Require Import GQ (*Nat_ggcd*).
Set Nested Proofs Allowed.

Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.

Delimit Scope NQ_scope with NQ.

Inductive NQ :=
  | NQ0 : NQ
  | NQpos : GQ → NQ
  | NQneg : GQ → NQ.
Arguments NQpos p%GQ.
Arguments NQneg p%GQ.

Notation "0" := (NQ0) : NQ_scope.
Notation "1" := (NQpos 1) : NQ_scope.

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

Notation "a // b" := (NQ_of_pair a b) (at level 32) : NQ_scope.

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
  | 0%NQ => f0
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

Theorem NQle_trans: ∀ x y z, (x ≤ y)%NQ → (y ≤ z)%NQ → (x ≤ z)%NQ.
Proof.
intros * Hxy Hyz.
unfold "≤"%NQ in *.
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-eapply GQle_trans; [ apply Hxy | apply Hyz ].
-eapply GQle_trans; [ apply Hyz | apply Hxy ].
Qed.

Theorem NQle_lt_trans: ∀ x y z, (x ≤ y)%NQ → (y < z)%NQ → (x < z)%NQ.
Proof.
intros * Hxy Hyz.
unfold "≤"%NQ, "<"%NQ in *.
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-eapply GQle_lt_trans; [ apply Hxy | apply Hyz ].
-eapply GQlt_le_trans; [ apply Hyz | apply Hxy ].
Qed.

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

Theorem NQadd_le_mono : ∀ x y z t,
  (x ≤ y)%NQ → (z ≤ t)%NQ → (x + z ≤ y + t)%NQ.
Proof.
intros * Hxy Hzt.
unfold "+"%NQ, "≤"%NQ.
destruct x as [| px| px].
-destruct y as [| py| py]; [ now destruct t | | easy ].
 destruct z as [| pz| pz]; [ now destruct t | | ].
 +destruct t as [| pt| pt]; [ easy | simpl | easy ].
  simpl in Hzt.
  eapply GQle_trans; [ apply Hzt | ].
  apply GQlt_le_incl, GQlt_add_l.
 +destruct t as [| pt| pt]; [ easy | easy | ].
  simpl in Hzt; simpl.
  remember (GQcompare py pt) as b eqn:Hb; symmetry in Hb.
  destruct b; GQcompare_iff; [ easy | | easy ].
  eapply GQle_trans; [ | apply Hzt ].
  apply GQlt_le_incl.
  now apply GQsub_lt.
-destruct y as [| py| py]; [ now destruct t | | easy ].
 destruct z as [| pz| pz]; simpl.
 +destruct t as [| pt| pt]; [ easy | simpl | easy ].
  eapply GQle_trans; [ apply Hxy | apply GQle_add_r ].
 +destruct t as [| pt| pt]; [ easy | simpl | easy ].
  now apply GQadd_le_mono.
 +remember (GQcompare px pz) as b eqn:Hb; symmetry in Hb.
  destruct b; GQcompare_iff.
  *destruct t as [| pt| pt]; [ easy | easy | simpl ].
   remember (GQcompare py pt) as b1 eqn:Hb1; symmetry in Hb1.
   destruct b1; GQcompare_iff; [ easy | | easy ].
   subst px; simpl in Hxy, Hzt.
   apply GQnle_gt in Hb1; apply Hb1.
   eapply GQle_trans; [ apply Hzt | apply Hxy ].
  *destruct t as [| pt| pt]; [ easy | easy | simpl ].
   remember (GQcompare py pt) as b1 eqn:Hb1; symmetry in Hb1.
   destruct b1; GQcompare_iff; [ easy | | easy ].
   simpl in Hxy, Hzt.
   now apply GQsub_le_mono.
  *destruct t as [| pt| pt]; simpl.
  --apply (GQle_trans _ (py - pz)).
   ++apply GQsub_le_mono_r; [ easy | | easy ].
     eapply GQlt_le_trans; [ apply Hb | apply Hxy ].
   ++apply GQlt_le_incl, GQsub_lt.
     eapply GQlt_le_trans; [ apply Hb | apply Hxy ].
  --apply (GQle_trans _ px).
   ++now apply GQlt_le_incl, GQsub_lt.
   ++apply (GQle_trans _ py); [ easy | apply GQle_add_r ].
  --remember (GQcompare py pt) as b1 eqn:Hb1; symmetry in Hb1.
    destruct b1; GQcompare_iff.
   ++subst py.
     apply GQnle_gt in Hb; apply Hb.
     eapply GQle_trans; [ apply Hxy | apply Hzt ].
   ++apply GQnle_gt in Hb; apply Hb.
     eapply GQle_trans; [ apply Hxy | ].
     eapply GQle_trans; [ apply GQlt_le_incl, Hb1 | easy ].
   ++now apply GQsub_le_mono.
-destruct z as [| pz| pz]; simpl.
 +destruct y as [| py| py]; [ now destruct t | now destruct t | ].
  destruct t as [| pt| pt]; [ easy | simpl | easy ].
  remember (GQcompare py pt) as b eqn:Hb; symmetry in Hb.
  destruct b; GQcompare_iff; [ easy | easy | ].
  apply (GQle_trans _ py); [ | easy ].
  now apply GQlt_le_incl, GQsub_lt.
 +destruct t as [| pt| pt]; [ easy | simpl | easy ].
  remember (GQcompare px pz) as b eqn:Hb; symmetry in Hb.
  destruct b; GQcompare_iff.
  *destruct y as [| py| py]; [ easy | easy | ].
   remember (GQcompare py pt) as b1 eqn:Hb1; symmetry in Hb1.
   destruct b1; GQcompare_iff; [ easy | easy | subst px ].
   apply GQnle_gt in Hb1; apply Hb1.
   now apply (GQle_trans _ pz).
  *destruct y as [| py| py].
  --apply (GQle_trans _ pz); [ | easy ].
    now apply GQlt_le_incl, GQsub_lt.
  --apply (GQle_trans _ pz).
   ++now apply GQlt_le_incl, GQsub_lt.
   ++apply (GQle_trans _ pt); [ easy | apply GQle_add_l ].
  --remember (GQcompare py pt) as b1 eqn:Hb1; symmetry in Hb1.
    destruct b1; GQcompare_iff.
   ++subst py.
     apply GQnle_gt in Hb; apply Hb.
     eapply GQle_trans; [ apply Hzt | apply Hxy ].
   ++now apply GQsub_le_mono.
   ++apply GQnle_gt in Hb; apply Hb.
     eapply GQle_trans; [ apply Hzt | ].
     eapply GQle_trans; [ apply GQlt_le_incl, Hb1 | easy ].
  *destruct y as [| py| py]; [ easy | easy | ].
   remember (GQcompare py pt) as b1 eqn:Hb1; symmetry in Hb1.
   destruct b1; GQcompare_iff; [ easy | easy | ].
   now apply GQsub_le_mono.
 +destruct y as [| py| py].
  *destruct t as [| pt| pt]; [ easy | easy | ].
   apply (GQle_trans _ pz); [ easy | ].
   apply GQle_add_l.
  *destruct t as [| pt| pt]; [ easy | easy | simpl ].
   remember (GQcompare py pt) as b1 eqn:Hb1; symmetry in Hb1.
   destruct b1; GQcompare_iff; [ easy | | easy ].
   apply (GQle_trans _ pt).
  --now apply GQlt_le_incl, GQsub_lt.
  --apply (GQle_trans _ pz); [ easy | apply GQle_add_l ].
  *destruct t as [| pt| pt]; simpl.
  --apply (GQle_trans _ px); [ easy | apply GQle_add_r ].
  --remember (GQcompare py pt) as b eqn:Hb; symmetry in Hb.
    destruct b; GQcompare_iff; [ easy | easy | ].
    apply (GQle_trans _ px); [ | apply GQle_add_r ].
    apply (GQle_trans _ py); [ | easy ].
    now apply GQlt_le_incl, GQsub_lt.
  --now apply GQadd_le_mono.
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
destruct a; [ easy | now rewrite GQpair_diag ].
Qed.

Theorem NQmul_1_l : ∀ a, (1 * a)%NQ = a.
Proof.
intros.
unfold "*"%NQ; simpl.
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

Theorem NQsub_pair : ∀ a b c d,
  b ≠ 0 → d ≠ 0 →
  (a // b - c // d)%NQ =
  match Nat.compare (a * d) (b * c) with
  | Eq => 0%NQ
  | Lt => NQneg ((b * c - a * d) // (b * d))
  | Gt => NQpos ((a * d - b * c) // (b * d))
  end.
Proof.
intros * Hb Hd.
destruct b; [ flia Hb | ].
destruct d; [ flia Hd | ].
unfold "-"%NQ, "+"%NQ.
destruct a.
-destruct c; [ now rewrite Nat.mul_0_r | ].
 remember (S b) as x; simpl; subst x.
 rewrite Nat.sub_0_r.
 remember (S b * S c) as bc eqn:Hbc; symmetry in Hbc.
 destruct bc; [ easy | rewrite <- Hbc ].
 rewrite <- GQmul_pair; [ | easy | easy | easy | easy ].
 rewrite GQpair_diag; [ | easy ].
 now rewrite GQmul_1_l.
-remember (S a // S b)%NQ as ab eqn:Hab; symmetry in Hab.
 destruct ab as [| pab| pab]; [ easy | | easy ].
 injection Hab; clear Hab; intros Hab; subst pab.
 unfold NQadd_pos_l.
 destruct c.
 +rewrite Nat.mul_0_r, Nat.sub_0_r.
  remember (NQpos ((S a * S d) // (S b * S d))) as x; simpl; subst x.
  rewrite <- GQmul_pair; [ | easy | easy | easy | easy ].
  rewrite GQpair_diag; [ | easy ].
  now rewrite GQmul_1_r.
 +remember (S a) as sa; remember (S b) as sb; simpl; subst sa sb.
  remember (GQcompare (S a // S b) (S c // S d)) as b1 eqn:Hb1.
  symmetry in Hb1.
  destruct b1; GQcompare_iff.
  *apply GQeq_pair in Hb1; [ | easy | easy | easy | easy ].
   now rewrite Hb1, Nat.compare_refl.
  *apply GQlt_pair in Hb1.
Check GQlt_pair.
...
(*
  remember (S a * S d ?= S b * S c) as b2 eqn:Hb2.
  symmetry in Hb1, Hb2.
  move b2 before b1.
*)

  *destruct b2; [ easy | | ].
  --apply Nat.compare_lt_iff in Hb2.
Search (_ // _ = _ // _)%GQ.
...

Theorem NQsub_pair : ∀ a b c d,
  b ≠ 0 → d ≠ 0 → (a // b - c // d = (a * d - b * c) // (b * d))%NQ.
Proof.
intros * Hb Hd.
...

Definition NQfrac q :=
  match q with
  | NQ0 => (0 // 1)%NQ
  | NQpos gq => NQpos (GQfrac gq)
  | NQneg gq => NQneg (GQfrac gq)
  end.

Definition NQintg q :=
  match q with
  | NQ0 => 0
  | NQpos gq => GQintg gq
  | NQneg gq => GQintg gq
  end.

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
