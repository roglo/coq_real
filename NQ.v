(* Positive rationals where num and den are always common primes *)
(* allowing us to use Leibnitz' equality. *)

Require Import Utf8 Arith Psatz Init.Nat.
Require Import Summation.
Require Import Misc GQ.

Set Nested Proofs Allowed.

(* "fast" lia, to improve compilation speed *)
Tactic Notation "flia" hyp_list(Hs) := clear - Hs; lia.
(* "pauto" = "auto" failing if not working *)
Tactic Notation "pauto" := progress auto.

Delimit Scope Q_scope with Q.

Module Q.

Inductive ty :=
  | Zero : ty
  | Pos : GQ → ty
  | Neg : GQ → ty.
Arguments Pos p%GQ.
Arguments Neg p%GQ.

Definition of_pair n d :=
  match n with
  | 0 => Zero
  | _ => Pos (GQ_of_pair n d)
  end.

Definition opp x :=
  match x with
  | Zero => Zero
  | Pos px => Neg px
  | Neg px => Pos px
  end.

Definition abs x :=
  match x with
  | Neg px => Pos px
  | _ => x
  end.

Definition inv x :=
  match x with
  | Zero => Zero
  | Pos px => Pos (/ px)
  | Neg px => Neg (/ px)
  end.

Definition lt x y :=
  match x with
  | Zero => match y with Pos _ => True | _ => False end
  | Pos px => match y with Pos py => GQlt px py | _ => False end
  | Neg px => match y with Neg py => GQlt py px | _ => True end
  end.
Arguments lt x%Q y%Q.

Definition le x y :=
  match x with
  | Zero => match y with Zero | Pos _ => True | _ => False end
  | Pos px => match y with Pos py => GQle px py | _ => False end
  | Neg px => match y with Neg py => GQle py px | _ => True end
  end.
Arguments le x%Q y%Q.

Definition gt x y := lt y x.
Definition ge x y := le y x.

Definition NQadd_pos_l px y :=
  match y with
  | Zero => Pos px
  | Pos py => Pos (px + py)
  | Neg py =>
      match GQcompare px py with
      | Eq => Zero
      | Lt => Neg (py - px)
      | Gt => Pos (px - py)
      end
  end.

Definition NQadd_neg_l px y :=
  match y with
  | Zero => Neg px
  | Pos py =>
      match GQcompare px py with
      | Eq => Zero
      | Lt => Pos (py - px)
      | Gt => Neg (px - py)
      end
  | Neg py => Neg (px + py)
  end.

Definition add x y :=
  match x with
  | Zero => y
  | Pos px => NQadd_pos_l px y
  | Neg px => NQadd_neg_l px y
  end.

Definition sub x y := add x (opp y).

Definition NQmul_pos_l px y :=
  match y with
  | Zero => Zero
  | Pos py => Pos (px * py)
  | Neg py => Neg (px * py)
  end.

Definition NQmul_neg_l px y :=
  match y with
  | Zero => Zero
  | Pos py => Neg (px * py)
  | Neg py => Pos (px * py)
  end.

Definition mul x y :=
  match x with
  | Zero => Zero
  | Pos px => NQmul_pos_l px y
  | Neg px => NQmul_neg_l px y
  end.

Module Notations.

Notation "a // b" := (of_pair a b) : Q_scope.
(*
Notation "0" := Zero : Q_scope.
Notation "1" := (1 // 1)%Q : Q_scope.
Notation "2" := (2 // 1)%Q : Q_scope.
Notation "3" := (3 // 1)%Q : Q_scope.
*)
Notation "x < y" := (lt x y) : Q_scope.
Notation "x ≤ y" := (le x y) : Q_scope.
Notation "x > y" := (gt x y) : Q_scope.
Notation "x ≥ y" := (ge x y) : Q_scope.
Notation "x < y < z" := (lt x y ∧ lt y z) : Q_scope.
Notation "x ≤ y < z" := (le x y ∧ lt y z) : Q_scope.
Notation "x < y ≤ z" := (lt x y ∧ le y z) : Q_scope.
Notation "x ≤ y ≤ z" := (le x y ∧ le y z) : Q_scope.
Notation "- x" := (opp x) : Q_scope.
Notation "x + y" := (add x y) : Q_scope.
Notation "x - y" := (sub x y) : Q_scope.
Notation "‖ x ‖" := (abs x) (at level 60) : Q_scope.
Notation "x * y" := (mul x y) : Q_scope.
Notation "x / y" := (mul x (inv y)) : Q_scope.
Notation "/ x" := (inv x) : Q_scope.

Import Decimal.

Definition of_decimal_uint (n : Decimal.uint) : ty :=
  match n with
  | Nil => Zero
  | D0 d => Zero
  | D1 d => Zero
  | D2 d => Zero
  | D3 d => Zero
  | D4 d => Zero
  | D5 d => (5 // 1)%Q
  | D6 d => Zero
  | D7 d => Zero
  | D8 d => Zero
  | D9 d => Zero
  end.

Definition of_decimal_int (n : Decimal.int) : ty :=
  match n with
  | Pos ui => of_decimal_uint ui
  | Neg ui => of_decimal_uint ui
  end.

Definition to_decimal_uint (gq : GQ) : Decimal.uint :=
  let (num, den) := PQ_of_GQ gq in
  Nat.to_uint (num + 1).

Definition to_decimal_int (q : ty) : option Decimal.int :=
  match q with
  | Q.Zero => Some (Pos Nil)
  | Q.Pos gq => Some (Pos (to_decimal_uint gq))
  | Q.Neg gq => Some (Neg (to_decimal_uint gq))
  end.

(*
Definition to_decimal_int (q : ty) : Decimal.int :=
  match q with
  | Q.Zero => Pos Nil
  | Q.Pos gq => Pos (to_decimal_uint gq)
  | Q.Neg gq => Neg (to_decimal_uint gq)
  end.
*)

Numeral Notation Q.ty of_decimal_int to_decimal_int : Q_scope.

Check 5%Q.
Compute (to_decimal_int 5%Q).
Compute (Nat.to_int 5).

Compute (Nat.to_uint 5).
Print Nat.to_uint.
Print Nat.to_little_uint.

Check 6%Q.

Print Decimal.uint.

Print Nat.to_uint.

...

End Notations.

Import Notations.

Check 5%Q.
Check 6%Q.

...

Definition of_nat n :=
  match n with
  | 0 => Zero
  | S _ => Pos (GQ_of_nat n)
  end.

Definition num x :=
  match x with
  | Zero => 0
  | Pos a => GQnum a
  | Neg a => GQnum a
  end.
Definition den x :=
  match x with
  | Zero => 1
  | Pos a => GQden a
  | Neg a => GQden a
  end.
Arguments num x%Q.
Arguments den x%Q.

Definition compare x y :=
  match x with
  | Zero => match y with Zero => Eq | Pos _ => Lt | Neg _ => Gt end
  | Pos px => match y with Pos py => GQcompare px py | _ => Gt end
  | Neg px => match y with Neg py => GQcompare py px | _ => Lt end
  end.

Theorem eq_dec : ∀ x y : ty, {x = y} + {x ≠ y}.
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
Arguments eq_dec x%Q y%Q.

Theorem lt_le_dec : ∀ x y : ty, {(x < y)%Q} + {(y ≤ x)%Q}.
Proof.
intros.
destruct x as [| px| px].
-destruct y as [| py| py]; [ now right | now left | now right ].
-destruct y as [| py| py]; [ now right | simpl | now right ].
 apply GQlt_le_dec.
-destruct y as [| py| py]; [ now left | now left | ].
 apply GQlt_le_dec.
Qed.
Arguments lt_le_dec x%Q y%Q.

Theorem le_lt_dec : ∀ x y : ty, {(x ≤ y)%Q} + {(y < x)%Q}.
Proof.
destruct x as [| px| px].
-destruct y as [| py| py]; [ now left | now left | now right ].
-destruct y as [| py| py]; [ now right | simpl | now right ].
 apply GQle_lt_dec.
-destruct y as [| py| py]; [ now left | now left | ].
 apply GQle_lt_dec.
Qed.
Arguments le_lt_dec x%Q y%Q.

Theorem le_refl : ∀ x, (x ≤ x)%Q.
Proof.
intros.
destruct x as [| px| px]; [ easy | apply GQle_refl | apply GQle_refl ].
Qed.

Theorem le_antisymm : ∀ x y, (x ≤ y)%Q → (y ≤ x)%Q → x = y.
Proof.
intros * Hxy Hyx.
unfold "≤"%Q in Hxy, Hyx.
destruct x as [| px| px], y as [| py| py]; try easy; simpl.
-f_equal; now apply GQle_antisymm.
-f_equal; now apply GQle_antisymm.
Qed.

Theorem match_match_comp : ∀ A c p q (f0 : A) fp fn,
  match
    match c with
    | Eq => 0%Q
    | Lt => Neg p
    | Gt => Pos q
    end
  with
  | Zero => f0
  | Pos px => fp px
  | Neg px => fn px
  end =
  match c with
  | Eq => f0
  | Lt => fn p
  | Gt => fp q
  end.
Proof. intros; now destruct c. Qed.

Theorem opp_involutive : ∀ x, (- - x)%Q = x.
Proof. intros; now destruct x. Qed.

Theorem opp_match_comp : ∀ c eq lt gt,
  (- match c with Eq => eq | Lt => lt | Gt => gt end =
   match c with Eq => - eq | Lt => - lt | Gt => - gt end)%Q.
Proof. intros; now destruct c. Qed.

Theorem match_opp_comp : ∀ c eq lt gt,
  (match c with Eq => eq | Lt => lt | Gt => gt end =
   - match c with Eq => - eq | Lt => - lt | Gt => - gt end)%Q.
Proof. now intros; destruct c; rewrite opp_involutive. Qed.

Theorem add_comm : ∀ x y, (x + y = y + x)%Q.
Proof.
intros.
unfold "+".
destruct x as [| px| px], y as [| py| py]; try easy; simpl.
-f_equal; apply GQadd_comm.
-now rewrite GQcompare_swap; destruct (GQcompare py px).
-now rewrite GQcompare_swap; destruct (GQcompare py px).
-f_equal; apply GQadd_comm.
Qed.

Theorem add_0_l : ∀ x, (0 + x = x)%Q.
Proof. easy. Qed.

Theorem add_0_r : ∀ x, (x + 0 = x)%Q.
Proof. intros; now rewrite add_comm. Qed.

Theorem sub_0_l : ∀ x, (0 - x = - x)%Q.
Proof. easy. Qed.

Theorem sub_0_r : ∀ x, (x - 0 = x)%Q.
Proof. intros; now destruct x. Qed.

Theorem nle_gt : ∀ x y, ¬ (x ≤ y)%Q ↔ (y < x)%Q.
Proof.
intros.
destruct x as [| xp| xp], y as [| yp| yp]; try now simpl.
-apply GQnle_gt.
-apply GQnle_gt.
Qed.

Theorem nlt_ge : ∀ x y, ¬ (x < y)%Q ↔ (y ≤ x)%Q.
Proof.
intros.
destruct x as [| xp| xp], y as [| yp| yp]; try now simpl.
-apply GQnlt_ge.
-apply GQnlt_ge.
Qed.

Theorem lt_irrefl : ∀ x, ¬ (x < x)%Q.
Proof.
intros * Hx.
destruct x as [| xp| xp]; [ easy | | ].
-now apply GQlt_irrefl in Hx.
-now apply GQlt_irrefl in Hx.
Qed.

Theorem add_swap_lemma1 : ∀ px py pz,
  match GQcompare (px + py) pz with
  | Eq => 0%Q
  | Lt => Neg (pz - (px + py))
  | Gt => Pos (px + py - pz)
  end =
  match GQcompare px pz with
  | Eq => Pos py
  | Lt =>
      match GQcompare (pz - px) py with
      | Eq => 0%Q
      | Lt => Pos (py - (pz - px))
      | Gt => Neg (pz - px - py)
      end
  | Gt => Pos (px - pz + py)
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

Theorem add_swap_lemma2 : ∀ px py pz,
  match GQcompare px py with
  | Eq => Neg pz
  | Lt => Neg (py - px + pz)
  | Gt =>
      match GQcompare (px - py) pz with
      | Eq => 0%Q
      | Lt => Neg (pz - (px - py))
      | Gt => Pos (px - py - pz)
      end
  end =
  match GQcompare px pz with
  | Eq => Neg py
  | Lt => Neg (pz - px + py)
  | Gt =>
      match GQcompare (px - pz) py with
      | Eq => 0%Q
      | Lt => Neg (py - (px - pz))
      | Gt => Pos (px - pz - py)
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

Theorem add_add_swap : ∀ x y z, (x + y + z = x + z + y)%Q.
Proof.
intros.
unfold "+"%Q.
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl.
-now rewrite GQadd_comm.
-now rewrite GQcompare_swap; destruct (GQcompare pz py).
-now rewrite GQcompare_swap; destruct (GQcompare pz py).
-now rewrite GQadd_comm.
-now destruct (GQcompare px pz).
-now rewrite GQadd_add_swap.
-rewrite match_match_comp.
 apply add_swap_lemma1.
-now destruct (GQcompare px py).
-rewrite match_match_comp.
 symmetry; apply add_swap_lemma1.
-do 2 (rewrite match_match_comp; symmetry).
 apply add_swap_lemma2.
-now destruct (GQcompare px pz).
-now destruct (GQcompare px py).
-rewrite GQcompare_swap, match_match_comp; symmetry.
 rewrite GQcompare_swap, match_match_comp; symmetry.
 do 2 rewrite <- add_swap_lemma1.
 now replace (pz + py)%GQ with (py + pz)%GQ by apply GQadd_comm.
-rewrite GQcompare_swap, match_match_comp; symmetry.
 rewrite match_opp_comp; simpl.
 rewrite add_swap_lemma1.
 rewrite GQcompare_swap.
 rewrite match_opp_comp; simpl.
 rewrite opp_involutive.
 now rewrite opp_match_comp.
-rewrite match_opp_comp; simpl.
 rewrite add_swap_lemma1; symmetry.
 rewrite GQcompare_swap, match_match_comp, GQcompare_swap.
 now do 2 rewrite opp_match_comp.
-now rewrite GQadd_add_swap.
Qed.

Theorem add_assoc : ∀ x y z, (x + (y + z) = (x + y) + z)%Q.
Proof.
intros.
symmetry.
rewrite add_comm.
remember (x + y)%Q as t eqn:Ht.
rewrite add_comm in Ht; rewrite Ht.
setoid_rewrite add_comm.
apply add_add_swap.
Qed.

Theorem add_sub_assoc : ∀ x y z, (x + (y - z) = (x + y) - z)%Q.
Proof. intros; apply add_assoc. Qed.

Theorem add_sub_swap : ∀ x y z, (x + y - z)%Q = (x - z + y)%Q.
Proof.
intros.
unfold sub.
apply add_add_swap.
Qed.

Theorem sub_sub_swap : ∀ x y z, (x - y - z = x - z - y)%Q.
Proof.
intros.
unfold sub.
apply add_add_swap.
Qed.

Theorem sub_diag : ∀ x, (x - x = 0)%Q.
Proof.
intros.
destruct x as [| px| px]; [ easy | | ]; simpl.
-now rewrite GQcompare_diag.
-now rewrite GQcompare_diag.
Qed.

Theorem add_opp_l : ∀ x y, (- x + y)%Q = (y - x)%Q.
Proof. intros; apply add_comm. Qed.

Theorem add_opp_r : ∀ x y, (x + - y)%Q = (x - y)%Q.
Proof. easy. Qed.

Theorem sub_add : ∀ a b, (a - b + b)%Q = a.
Proof.
intros.
unfold sub.
rewrite add_add_swap, <- add_assoc.
now rewrite add_opp_r, sub_diag, add_0_r.
Qed.

Theorem add_sub : ∀ a b, (a + b - b)%Q = a.
Proof.
intros.
unfold sub.
rewrite <- add_assoc.
now rewrite add_opp_r, sub_diag, add_0_r.
Qed.

Theorem lt_trans: ∀ x y z, (x < y)%Q → (y < z)%Q → (x < z)%Q.
Proof.
intros * Hxy Hyz.
unfold "≤"%Q in *.
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-eapply GQlt_trans; [ apply Hxy | apply Hyz ].
-eapply GQlt_trans; [ apply Hyz | apply Hxy ].
Qed.
Arguments lt_trans x%Q y%Q z%Q.

Theorem le_trans: ∀ x y z, (x ≤ y)%Q → (y ≤ z)%Q → (x ≤ z)%Q.
Proof.
intros * Hxy Hyz.
unfold "≤"%Q in *.
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-eapply GQle_trans; [ apply Hxy | apply Hyz ].
-eapply GQle_trans; [ apply Hyz | apply Hxy ].
Qed.
Arguments le_trans x%Q y%Q z%Q.

Theorem le_lt_trans: ∀ x y z, (x ≤ y)%Q → (y < z)%Q → (x < z)%Q.
Proof.
intros * Hxy Hyz.
unfold "≤"%Q, "<"%Q in *.
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-eapply GQle_lt_trans; [ apply Hxy | apply Hyz ].
-eapply GQlt_le_trans; [ apply Hyz | apply Hxy ].
Qed.
Arguments le_lt_trans x%Q y%Q z%Q.

Theorem lt_le_trans: ∀ x y z, (x < y)%Q → (y ≤ z)%Q → (x < z)%Q.
Proof.
intros * Hxy Hyz.
unfold "≤"%Q, "<"%Q in *.
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-eapply GQlt_le_trans; [ apply Hxy | apply Hyz ].
-eapply GQle_lt_trans; [ apply Hyz | apply Hxy ].
Qed.
Arguments lt_le_trans x%Q y%Q z%Q.

Theorem le_add_l : ∀ x y, (0 ≤ y)%Q → (x ≤ y + x)%Q.
Proof.
intros * Hy.
destruct y as [| py| py]; [ apply le_refl | | easy ].
simpl; unfold NQadd_pos_l.
destruct x as [| px| px]; [ easy | apply GQle_add_l | simpl ].
remember (GQcompare py px) as b eqn:Hb; symmetry in Hb.
destruct b; GQcompare_iff; [ easy | | easy ].
apply GQlt_le_incl.
now apply GQsub_lt.
Qed.

Theorem le_add_r : ∀ x y, (0 ≤ y)%Q → (x ≤ x + y)%Q.
Proof.
intros.
now rewrite add_comm; apply le_add_l.
Qed.

Theorem add_lt_mono_l : ∀ x y z, (y < z)%Q ↔ (x + y < x + z)%Q.
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
   now apply lt_irrefl in Hxy.
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
 +now apply lt_irrefl in Hxy.
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
   now apply lt_irrefl in Hxy.
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
Arguments add_lt_mono_l x%Q y%Q z%Q.

Theorem add_lt_mono_r : ∀ x y z, (x < y)%Q ↔ (x + z < y + z)%Q.
Proof.
intros *.
setoid_rewrite add_comm.
apply add_lt_mono_l.
Qed.
Arguments add_lt_mono_r x%Q y%Q z%Q.

Theorem lt_le_incl : ∀ x y, (x < y)%Q → (x ≤ y)%Q.
Proof.
intros * Hxy.
destruct x as [| xp| xp], y as [| yp| yp]; try easy.
-now apply GQlt_le_incl.
-now apply GQlt_le_incl.
Qed.

Theorem add_le_mono : ∀ x y z t,
  (x ≤ y)%Q → (z ≤ t)%Q → (x + z ≤ y + t)%Q.
Proof.
intros * Hxy Hzt.
destruct (eq_dec x y) as [H1| H1].
-subst x.
 destruct (eq_dec z t) as [H2| H2].
 +subst z; apply le_refl.
 +apply lt_le_incl, add_lt_mono_l, nle_gt.
  now intros H; apply H2, le_antisymm.
-destruct (eq_dec z t) as [H2| H2].
 +subst z.
  apply lt_le_incl, add_lt_mono_r, nle_gt.
  now intros H; apply H1, le_antisymm.
 +apply (le_trans _ (x + t)).
  *apply lt_le_incl, add_lt_mono_l, nle_gt.
   now intros H; apply H2, le_antisymm.
  *apply lt_le_incl, add_lt_mono_r, nle_gt.
   now intros H; apply H1, le_antisymm.
Qed.
Arguments add_le_mono x%Q y%Q z%Q t%Q.

Theorem add_le_mono_l : ∀ x y z, (x ≤ y)%Q ↔ (z + x ≤ z + y)%Q.
Proof.
intros.
split; intros Hxy.
-apply add_le_mono; [ apply le_refl | easy ].
-apply (add_le_mono _ _ (- z) (- z)) in Hxy; [ | apply le_refl ].
 replace (z + x)%Q with (x + z)%Q in Hxy by apply add_comm.
 replace (z + y)%Q with (y + z)%Q in Hxy by apply add_comm.
 now do 2 rewrite add_opp_r, add_sub in Hxy.
Qed.
Arguments add_le_mono_l x%Q y%Q z%Q.

Theorem add_le_mono_r : ∀ x y z, (x ≤ y)%Q ↔ (x + z ≤ y + z)%Q.
Proof.
intros.
setoid_rewrite add_comm.
apply add_le_mono_l.
Qed.
Arguments add_le_mono_r x%Q y%Q z%Q.

Theorem add_le_lt_mono : ∀ x y z t, (x ≤ y → z < t → x + z < y + t)%Q.
Proof.
intros * Hxy Hzt.
destruct (eq_dec x y) as [H1| H1].
-subst x.
 destruct (eq_dec z t) as [H2| H2].
 +now subst z; apply lt_irrefl in Hzt.
 +now apply add_lt_mono_l.
-destruct (eq_dec z t) as [H2| H2].
 +subst z.
  apply add_lt_mono_r, nle_gt.
  now intros H; apply H1, le_antisymm.
 +apply (le_lt_trans _ (x + t)).
  *apply add_le_mono; [ apply le_refl | ].
   now apply lt_le_incl.
  *apply add_lt_mono_r, nle_gt.
   now intros H; apply H1, le_antisymm.
Qed.
Arguments add_le_lt_mono x%Q y%Q z%Q t%Q.

Theorem add_lt_le_mono : ∀ x y z t, (x < y → z ≤ t → x + z < y + t)%Q.
Proof.
intros * Hxy Hzt.
setoid_rewrite add_comm.
now apply add_le_lt_mono.
Qed.
Arguments add_lt_le_mono x%Q y%Q z%Q t%Q.

Theorem add_lt_mono : ∀ x y z t, (x < y → z < t → x + z < y + t)%Q.
Proof.
intros.
apply add_le_lt_mono; [ | easy ].
now apply lt_le_incl.
Qed.

Theorem le_sub_le_add_l : ∀ x y z, (x - y ≤ z)%Q ↔ (x ≤ y + z)%Q.
Proof.
intros.
split; intros H.
-apply (add_le_mono_r _ _ y) in H.
 now rewrite sub_add, add_comm in H.
-apply (add_le_mono_r _ _ y).
 now rewrite sub_add, add_comm.
Qed.

Theorem le_sub_le_add_r : ∀ x y z, (x - y ≤ z)%Q ↔ (x ≤ z + y)%Q.
Proof.
intros.
rewrite add_comm; apply le_sub_le_add_l.
Qed.

Theorem le_add_le_sub_l : ∀ x y z, (x + y ≤ z)%Q ↔ (x ≤ z - y)%Q.
Proof.
intros.
split; intros H.
-apply (add_le_mono_r _ _ y).
 now rewrite sub_add.
-apply (add_le_mono_r _ _ y) in H.
 now rewrite sub_add in H.
Qed.

Theorem le_add_le_sub_r : ∀ x y z, (x + y ≤ z)%Q ↔ (y ≤ z - x)%Q.
Proof.
intros.
rewrite add_comm; apply le_add_le_sub_l.
Qed.

Theorem lt_sub_lt_add_l : ∀ x y z, (x - y < z)%Q ↔ (x < y + z)%Q.
Proof.
intros.
split; intros H.
-apply (add_lt_mono_r _ _ y) in H.
 now rewrite sub_add, add_comm in H.
-apply (add_lt_mono_r _ _ y).
 now rewrite sub_add, add_comm.
Qed.

Theorem lt_sub_lt_add_r : ∀ x y z, (x - y < z)%Q ↔ (x < z + y)%Q.
Proof.
intros.
rewrite add_comm; apply lt_sub_lt_add_l.
Qed.

Theorem lt_add_lt_sub_l : ∀ x y z, (x + y < z)%Q ↔ (y < z - x)%Q.
Proof.
intros.
split; intros H.
-apply (add_lt_mono_r _ _ x).
 now rewrite add_comm, sub_add.
-apply (add_lt_mono_r _ _ x) in H.
 now rewrite add_comm, sub_add in H.
Qed.

Theorem lt_add_lt_sub_r : ∀ x y z, (x + y < z)%Q ↔ (x < z - y)%Q.
Proof.
intros.
rewrite add_comm; apply lt_add_lt_sub_l.
Qed.

Theorem add_le_r : ∀ x y z, (x + z ≤ y + z ↔ x ≤ y)%Q.
Proof.
intros.
split; intros H.
-apply (add_le_mono _ _ (- z) (- z)) in H; [ | apply le_refl ].
 now do 2 rewrite add_opp_r, add_sub in H.
-apply add_le_mono; [ easy | apply le_refl ].
Qed.
Arguments add_le_r x%Q y%Q z%Q.

Theorem opp_lt_mono : ∀ x y, (x < y)%Q ↔ (- y < - x)%Q.
Proof. intros; now destruct x, y. Qed.

Theorem opp_le_mono : ∀ x y, (x ≤ y)%Q ↔ (- y ≤ - x)%Q.
Proof. intros; now destruct x, y. Qed.

Theorem sub_le_mono : ∀ x y z t,
  (x ≤ y)%Q → (z ≤ t)%Q → (x - t ≤ y - z)%Q.
Proof.
intros * Hxy Hzt.
destruct (eq_dec x y) as [H1| H1].
-subst x.
 destruct (eq_dec z t) as [H2| H2].
 +subst z; apply le_refl.
 +apply lt_le_incl, add_lt_mono_l, nle_gt.
  intros H; apply H2.
  apply le_antisymm; [ easy | ].
  now apply opp_le_mono.
-destruct (eq_dec z t) as [H2| H2].
 +subst z.
  apply lt_le_incl, add_lt_mono_r, nle_gt.
  now intros H; apply H1, le_antisymm.
 +apply (le_trans _ (y - t)).
  *apply lt_le_incl, add_lt_mono_r, nle_gt.
   now intros H; apply H1, le_antisymm.
  *apply lt_le_incl, add_lt_mono_l, nle_gt.
   intros H; apply H2, le_antisymm; [ easy | ].
   now apply opp_le_mono.
Qed.
Arguments sub_le_mono x%Q y%Q z%Q t%Q.

Theorem sub_lt_mono : ∀ x y z t,
  (x < y)%Q → (z < t)%Q → (x - t < y - z)%Q.
Proof.
intros * Hxy Hzt.
apply (lt_trans _ (y - t)).
-now apply add_lt_mono_r.
-apply add_lt_mono_l.
 now apply -> opp_lt_mono.
Qed.
Arguments sub_lt_mono x%Q y%Q z%Q t%Q.

Theorem sub_le_lt_mono : ∀ x y z t,
  (x ≤ y)%Q → (z < t)%Q → (x - t < y - z)%Q.
Proof.
intros * Hxy Hzt.
destruct (eq_dec x y) as [H1| H1].
-subst x.
 apply add_lt_mono_l.
 now apply -> opp_lt_mono.
-apply sub_lt_mono; [ | easy ].
 apply nle_gt; intros H2; apply H1; clear H1.
 now apply le_antisymm.
Qed.
Arguments sub_le_lt_mono x%Q y%Q z%Q t%Q.

Theorem sub_lt_le_mono : ∀ x y z t,
  (x < y)%Q → (z ≤ t)%Q → (x - t < y - z)%Q.
Proof.
intros * Hxy Hzt.
destruct (eq_dec z t) as [H1| H1].
-subst z.
 now apply add_lt_mono_r.
-apply sub_lt_mono; [ easy | ].
 apply nle_gt; intros H2; apply H1; clear H1.
 now apply le_antisymm.
Qed.
Arguments sub_lt_le_mono x%Q y%Q z%Q t%Q.

Theorem lt_0_sub : ∀ x y, (0 < y - x)%Q ↔ (x < y)%Q.
Proof.
intros.
destruct x as [| xp| xp].
-now rewrite sub_0_r.
-destruct y as [| yp| yp]; [ easy | cbn | easy ].
 remember (GQcompare yp xp) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff; [ | | easy ].
 +split; [ easy | subst; apply GQlt_irrefl ].
 +split; [ easy | now apply GQnlt_ge, GQlt_le_incl ].
-destruct y as [| yp| yp]; [ easy | easy | cbn ].
 remember (GQcompare yp xp) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff; [ | easy | ].
 +split; [ easy | subst; apply GQlt_irrefl ].
 +split; [ easy | now apply GQnlt_ge, GQlt_le_incl ].
Qed.

Theorem le_0_sub : ∀ x y, (0 ≤ y - x)%Q ↔ (x ≤ y)%Q.
Proof.
intros.
destruct x as [| xp| xp].
-now rewrite sub_0_r.
-destruct y as [| yp| yp]; [ easy | cbn | easy ].
 remember (GQcompare yp xp) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff.
 +split; [ intros H; subst; apply GQle_refl | easy ].
 +split; [ easy | intros H; now apply GQnlt_ge in H ].
 +split; [ intros H; now apply GQlt_le_incl | easy ].
-destruct y as [| yp| yp]; [ easy | easy | cbn ].
 remember (GQcompare yp xp) as b eqn:Hb; symmetry in Hb.
 destruct b; GQcompare_iff.
 +split; [ intros H; subst; apply GQle_refl | easy ].
 +split; [ intros H; now apply GQlt_le_incl | easy ].
 +split; [ easy | intros H; now apply GQnlt_ge in H ].
Qed.

Theorem sub_lt : ∀ x y, (0 < x)%Q → (y - x < y)%Q.
Proof.
intros * Hxy.
apply (add_lt_mono_r _ _ x).
rewrite sub_add.
replace y with (y + 0)%Q at 1 by apply add_0_r.
now apply add_lt_mono_l.
Qed.

Theorem le_sub_l : ∀ x y, (0 ≤ y)%Q → (x - y ≤ x)%Q.
Proof.
intros * Hy.
apply le_sub_le_add_r.
apply le_sub_le_add_l.
now rewrite sub_diag.
Qed.

Theorem add_cancel_l: ∀ x y z, (x + y = x + z)%Q ↔ (y = z)%Q.
Proof.
intros.
split; intros Hxy; [ | now subst y ].
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp]; try easy.
-rewrite add_0_r in Hxy; cbn in Hxy.
 injection Hxy as H; symmetry in H; rewrite GQadd_comm in H.
 now apply GQadd_no_neutral in H.
-rewrite add_0_r in Hxy; cbn in Hxy.
 remember (GQcompare xp zp) as b eqn:Hb; symmetry in Hb.
 destruct b; [ easy | easy | GQcompare_iff ].
 injection Hxy as H; symmetry in H.
 now apply GQsub_no_neutral in H.
-rewrite add_0_r in Hxy; cbn in Hxy.
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
-rewrite add_0_r in Hxy; cbn in Hxy.
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
-rewrite add_0_r in Hxy; cbn in Hxy.
 remember (GQcompare xp zp) as b eqn:Hb; symmetry in Hb.
 destruct b; [ easy | easy | GQcompare_iff ].
 injection Hxy as H; symmetry in H.
 now apply GQsub_no_neutral in H.
-rewrite add_0_r in Hxy; cbn in Hxy.
 injection Hxy as H; symmetry in H.
 rewrite GQadd_comm in H.
 now apply GQadd_no_neutral in H.
-rewrite add_0_r in Hxy; cbn in Hxy.
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
 rewrite add_0_r in Hxy; cbn in Hxy.
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

Theorem add_cancel_r : ∀ x y z, (x + z = y + z)%Q ↔ (x = y)%Q.
Proof.
intros.
setoid_rewrite add_comm.
apply add_cancel_l.
Qed.

Theorem opp_inj : ∀ x y, (- x)%Q =  (- y)%Q → x = y.
Proof.
intros * H.
destruct x as [| xp| xp], y as [| yp| yp]; try easy.
-now injection H; intros; subst xp.
-now injection H; intros; subst xp.
Qed.

Theorem sub_cancel_l : ∀ x y z, (x - y = x - z)%Q ↔ (y = z)%Q.
Proof.
unfold sub.
split; intros H; [ | now subst y ].
now apply add_cancel_l, opp_inj in H.
Qed.

Theorem sub_cancel_r : ∀ x y z, (x - z = y - z)%Q ↔ (x = y)%Q.
Proof.
unfold sub.
split; intros H; [ | now subst y ].
now apply add_cancel_r in H.
Qed.

Theorem add_move_l : ∀ x y z, (x + y)%Q = z ↔ y = (z - x)%Q.
Proof.
intros.
split; intros Hxy.
-apply (sub_cancel_r _ _ x) in Hxy.
 now rewrite add_comm, add_sub in Hxy.
-apply (add_cancel_r _ _ x) in Hxy.
 now rewrite sub_add, add_comm in Hxy.
Qed.

Theorem add_move_r : ∀ x y z, (x + y)%Q = z ↔ x = (z - y)%Q.
Proof.
intros.
rewrite add_comm.
apply add_move_l.
Qed.

Theorem add_move_0_l : ∀ x y, (x + y)%Q = 0%Q ↔ y = (- x)%Q.
Proof.
intros.
split; intros Hxy.
-now apply add_move_l in Hxy.
-subst y; apply sub_diag.
Qed.

Theorem add_move_0_r : ∀ x y, (x + y)%Q = 0%Q ↔ x = (- y)%Q.
Proof.
intros.
rewrite add_comm.
apply add_move_0_l.
Qed.

Theorem sub_opp_r : ∀ x y, (x - - y = x + y)%Q.
Proof. intros; now destruct x, y. Qed.

Theorem opp_add_distr : ∀ x y, (- (x + y))%Q = (- x - y)%Q.
Proof.
intros.
destruct x as [| xp| xp], y as [| yp| yp]; try easy.
-now cbn; destruct (GQcompare xp yp).
-now cbn; destruct (GQcompare xp yp).
Qed.

Theorem opp_sub_distr : ∀ x y, (- (x - y))%Q = (- x + y)%Q.
Proof.
intros.
unfold sub.
rewrite opp_add_distr.
apply sub_opp_r.
Qed.

Theorem sub_add_distr : ∀ x y z, (x - (y + z))%Q = (x - y - z)%Q.
Proof.
intros.
unfold sub.
rewrite opp_add_distr.
apply add_assoc.
Qed.

Theorem sub_sub_distr : ∀ x y z, (x - (y - z))%Q = (x - y + z)%Q.
Proof.
intros.
unfold sub at 2.
rewrite sub_add_distr.
now rewrite sub_opp_r.
Qed.

Theorem sub_lt_mono_l : ∀ x y z, (x < y)%Q ↔ (z - y < z - x)%Q.
Proof.
intros.
split; intros Hxy.
-apply sub_le_lt_mono; [ apply le_refl | easy ].
-apply (sub_le_lt_mono z z) in Hxy; [ | apply le_refl ].
 do 2 rewrite sub_sub_distr in Hxy.
 now rewrite sub_diag in Hxy.
Qed.
Arguments sub_lt_mono_l x%Q y%Q z%Q.

Theorem sub_lt_mono_r : ∀ x y z, (x < y)%Q ↔ (x - z < y - z)%Q.
Proof.
intros.
split; intros Hxy.
-apply sub_lt_le_mono; [ easy | apply le_refl ].
-apply (add_lt_mono_r (x - z) (y - z) z) in Hxy.
 now do 2 rewrite sub_add in Hxy.
Qed.
Arguments sub_lt_mono_r x%Q y%Q z%Q.

Theorem mul_pair : ∀ x y z t,
  y ≠ 0 → t ≠ 0 → ((x // y) * (z // t) = (x * z) // (y * t))%Q.
Proof.
intros * Hy Ht; simpl.
unfold "*"%GQ, "//"%Q; simpl.
destruct x; [ easy | ].
destruct z; [ now rewrite Nat.mul_0_r | simpl ].
f_equal.
now apply GQmul_pair.
Qed.

Theorem mul_comm : ∀ x y, (x * y = y * x)%Q.
Proof.
intros.
unfold "*".
destruct x as [| px| px], y as [| py| py]; try easy; simpl;
f_equal; apply GQmul_comm.
Qed.

Theorem mul_mul_swap : ∀ x y z, (x * y * z = x * z * y)%Q.
Proof.
intros.
unfold "*"%Q.
destruct x as [| px| px], y as [| py| py], z as [| pz| pz]; try easy; simpl;
f_equal; apply GQmul_mul_swap.
Qed.

Theorem mul_assoc : ∀ x y z, (x * (y * z) = (x * y) * z)%Q.
Proof.
intros.
symmetry.
rewrite mul_comm.
remember (x * y)%Q as t eqn:Ht.
rewrite mul_comm in Ht; rewrite Ht.
setoid_rewrite mul_comm.
apply mul_mul_swap.
Qed.

Theorem mul_add_distr_l : ∀ x y z, (x * (y + z) = x * y + x * z)%Q.
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

Theorem mul_add_distr_r : ∀ x y z, ((x + y) * z = x * z + y * z)%Q.
Proof.
intros.
setoid_rewrite mul_comm.
apply mul_add_distr_l.
Qed.

Theorem mul_sub_distr_l : ∀ x y z, (x * (y - z) = x * y - x * z)%Q.
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

Theorem mul_sub_distr_r : ∀ x y z, ((x - y) * z = x * z - y * z)%Q.
Proof.
intros.
setoid_rewrite mul_comm.
apply mul_sub_distr_l.
Qed.

Theorem eq_mul_0 : ∀ x y, (x * y = 0 → x = 0 ∨ y = 0)%Q.
Proof.
intros * Hxy.
destruct x as [| xp| xp]; [ now left | now right; destruct y | ].
destruct y as [| yp| yp]; [ now right | easy | easy ].
Qed.

Theorem mul_le_mono_nonneg : ∀ x y z t,
  (0 ≤ x)%Q → (x ≤ y)%Q → (0 ≤ z)%Q → (z ≤ t)%Q → (x * z ≤ y * t)%Q.
Proof.
intros * Hx Hxy Hz Hzt.
destruct x as [| xp| xp], y as [| yp| yp], z as [| zp| zp], t as [| tp| tp];
  try easy; cbn in *.
now apply GQmul_le_mono.
Qed.

Theorem mul_le_mono_nonneg_l : ∀ x y z, (0 ≤ x → y ≤ z → x * y ≤ x * z)%Q.
Proof.
intros * Hx Hyz.
destruct x as [| xp| xp]; [ easy | | easy ].
destruct y as [| yp| yp]; [ now destruct z | | ].
-destruct z as [| zp| zp]; [ easy | | easy ].
 now apply GQmul_le_mono_l.
-destruct z as [| zp| zp]; [ easy | easy | ].
 now apply GQmul_le_mono_l.
Qed.

Theorem mul_le_mono_nonneg_r : ∀ x y z, (0 ≤ x → y ≤ z → y * x ≤ z * x)%Q.
Proof.
setoid_rewrite mul_comm.
apply mul_le_mono_nonneg_l.
Qed.

Theorem mul_lt_mono_pos_l : ∀ x y z,
  (0 < x)%Q → (y < z)%Q ↔ (x * y < x * z)%Q.
Proof.
intros * Hx.
destruct x as [| xp| xp]; [ easy | | easy ].
destruct y as [| yp| yp]; [ now destruct z | | ].
-destruct z as [| zp| zp]; [ easy | cbn | easy ].
 apply GQmul_lt_mono_l.
-destruct z as [| zp| zp]; [ easy | easy | cbn ].
 apply GQmul_lt_mono_l.
Qed.

Theorem mul_lt_mono_pos_r : ∀ x y z,
  (0 < x)%Q → (y < z)%Q ↔ (y * x < z * x)%Q.
Proof.
setoid_rewrite mul_comm.
apply mul_lt_mono_pos_l.
Qed.

Theorem mul_le_mono_pos_l : ∀ x y z,
  (0 < x)%Q → (y ≤ z)%Q ↔ (x * y ≤ x * z)%Q.
Proof.
intros * Hx.
destruct x as [| xp| xp]; [ easy | | easy ].
destruct y as [| yp| yp]; [ now destruct z | | ].
-destruct z as [| zp| zp]; [ easy | cbn | easy ].
 apply GQmul_le_mono_l.
-destruct z as [| zp| zp]; [ easy | easy | cbn ].
 apply GQmul_le_mono_l.
Qed.

Theorem mul_le_mono_pos_r : ∀ x y z,
  (0 < x)%Q → (y ≤ z)%Q ↔ (y * x ≤ z * x)%Q.
Proof.
setoid_rewrite mul_comm.
apply mul_le_mono_pos_l.
Qed.

Theorem mul_cancel_l : ∀ x y z, x ≠ 0%Q → (x * y)%Q = (x * z)%Q ↔ y = z.
Proof.
intros * Hx.
split; intros Hyz; [ | now subst ].
destruct x as [| xp| xp]; [ easy | | ].
-destruct y as [| yp| yp], z as [| zp| zp]; try easy.
 +cbn in Hyz; f_equal.
  remember GQmul as f.
  injection Hyz; clear Hyz; intros Hyz; subst f.
  now apply GQmul_cancel_l in Hyz.
 +cbn in Hyz; f_equal.
  remember GQmul as f.
  injection Hyz; clear Hyz; intros Hyz; subst f.
  now apply GQmul_cancel_l in Hyz.
-destruct y as [| yp| yp], z as [| zp| zp]; try easy.
 +cbn in Hyz; f_equal.
  remember GQmul as f.
  injection Hyz; clear Hyz; intros Hyz; subst f.
  now apply GQmul_cancel_l in Hyz.
 +cbn in Hyz; f_equal.
  remember GQmul as f.
  injection Hyz; clear Hyz; intros Hyz; subst f.
  now apply GQmul_cancel_l in Hyz.
Qed.

Theorem mul_cancel_r : ∀ x y z, z ≠ 0%Q → (x * z)%Q = (y * z)%Q ↔ x = y.
Proof.
intros *.
setoid_rewrite mul_comm.
apply mul_cancel_l.
Qed.

Theorem le_pair : ∀ x y z t,
  y ≠ 0 → t ≠ 0 → (x // y ≤ z // t)%Q ↔ x * t ≤ y * z.
Proof.
intros * Hy Ht.
unfold "≤"%Q.
remember (x // y)%Q as a eqn:Ha; symmetry in Ha.
remember (z // t)%Q as b eqn:Hb; symmetry in Hb.
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

Theorem lt_pair : ∀ a b c d,
  b ≠ 0 → d ≠ 0 → (a // b < c // d)%Q ↔ a * d < b * c.
Proof.
intros * Hb Hd.
unfold "<"%GQ, "//"%Q; simpl.
destruct a.
-destruct c; [ now rewrite Nat.mul_0_r | simpl ].
 split; [ intros _ | easy ].
 destruct b; [ easy | simpl; flia ].
-destruct c; [ now rewrite Nat.mul_0_r | simpl ].
 now apply GQlt_pair.
Qed.

Theorem eq_pair : ∀ x y z t : nat,
   y ≠ 0 → t ≠ 0 → (x // y = z // t)%Q ↔ x * t = y * z.
Proof.
intros * Hy Ht.
remember (x // y)%Q as a eqn:Ha; symmetry in Ha.
remember (z // t)%Q as b eqn:Hb; symmetry in Hb.
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

Theorem den_0 : ∀ a, (a // 0 = a // 1)%Q.
Proof. easy. Qed.

Theorem pair_eq_r : ∀ a b c, (a // c = b // c)%Q ↔ a = b.
Proof.
intros; split; [ | now intros; subst ].
intros H.
destruct c.
-do 2 rewrite den_0 in H.
 apply eq_pair in H; [ | easy | easy ].
 rewrite Nat.mul_comm in H.
 now apply Nat.mul_cancel_l in H.
-apply eq_pair in H; [ | easy | easy ].
 rewrite Nat.mul_comm in H.
 now apply Nat.mul_cancel_l in H.
Qed.

Theorem pair_diag : ∀ a, a ≠ 0 → (a // a = 1)%Q.
Proof.
intros.
unfold "//"%Q.
destruct a; [ easy | ].
rewrite GQpair_diag; [ now rewrite GQpair_diag | easy ].
Qed.

Theorem mul_inv_pair : ∀ a b, a ≠ 0 → b ≠ 0 → (a // b * b // a = 1)%Q.
Proof.
intros * Ha Hb.
rewrite mul_pair; [ | easy | easy ].
rewrite Nat.mul_comm.
apply pair_diag.
intros H; apply Nat.eq_mul_0 in H.
now destruct H.
Qed.

Theorem le_pair_mono_l : ∀ a b c, 0 < a ≤ b → (c // b ≤ c // a)%Q.
Proof.
intros * Hab.
apply le_pair; [ flia Hab | flia Hab | ].
rewrite Nat.mul_comm.
now apply Nat.mul_le_mono_r.
Qed.

Theorem le_pair_mono_r : ∀ a b c, a ≤ b → (a // c ≤ b // c)%Q.
Proof.
intros * Hab.
destruct c.
-do 2 rewrite den_0.
 apply le_pair; [ easy | easy | ].
 rewrite Nat.mul_comm.
 now apply Nat.mul_le_mono_l.
-apply le_pair; [ easy | easy | ].
 rewrite Nat.mul_comm.
 now apply Nat.mul_le_mono_l.
Qed.

Theorem lt_pair_mono_l : ∀ a b c, 0 < a < b → 0 < c → (c // b < c // a)%Q.
Proof.
intros * Hab Hc.
apply lt_pair; [ flia Hab | flia Hab | ].
rewrite Nat.mul_comm.
now apply Nat.mul_lt_mono_pos_r.
Qed.

Theorem lt_pair_mono_r : ∀ a b c, a < b → (a // c < b // c)%Q.
Proof.
intros * Hab.
destruct c.
-do 2 rewrite den_0.
 apply lt_pair; [ easy | easy | ].
 rewrite Nat.mul_comm.
 apply Nat.mul_lt_mono_pos_l; [ pauto | easy ].
-apply lt_pair; [ easy | easy | ].
 rewrite Nat.mul_comm.
 apply Nat.mul_lt_mono_pos_l; [ | easy ].
 apply Nat.lt_0_succ.
Qed.

Theorem pair_inv_mul : ∀ a b c, b ≠ 0 → c ≠ 0 →
  (a // (b * c))%Q = (a // b * 1 // c)%Q.
Proof.
intros * Hb Hc.
rewrite mul_pair; [ | easy | easy ].
now rewrite Nat.mul_1_r.
Qed.

Theorem mul_1_l : ∀ a, (1 * a)%Q = a.
Proof.
intros.
unfold "*"%Q; simpl.
rewrite GQpair_diag; [ | easy ].
unfold NQmul_pos_l.
destruct a; [ easy | | ]; now rewrite GQmul_1_l.
Qed.

Theorem mul_1_r : ∀ a, (a * 1)%Q = a.
Proof.
intros.
rewrite mul_comm.
apply mul_1_l.
Qed.

Theorem mul_pair_mono_l : ∀ a b c,
  a ≠ 0 → c ≠ 0 → ((a * b) // (a * c) = b // c)%Q.
Proof.
intros * Ha Hc.
rewrite <- mul_pair; [ | easy | easy ].
now rewrite pair_diag, mul_1_l.
Qed.

Theorem mul_pair_mono_r : ∀ a b c,
  b ≠ 0 → c ≠ 0 → ((a * c) // (b * c) = a // b)%Q.
Proof.
intros * Hb Hc.
rewrite <- mul_pair; [ | easy | easy ].
now rewrite pair_diag, mul_1_r.
Qed.

Theorem mul_0_l : ∀ a, (0 * a)%Q = 0%Q.
Proof. easy. Qed.

Theorem mul_0_r : ∀ a, (a * 0)%Q = 0%Q.
Proof. intros; now rewrite mul_comm. Qed.

Theorem mul_opp_l : ∀ x y, (- x * y)%Q = (- (x * y))%Q.
Proof. intros; now destruct x, y. Qed.

Theorem mul_lt_le_mono_pos : ∀ x y z t,
  (0 ≤ x)%Q → (x < y)%Q → (0 < z)%Q → (z ≤ t)%Q → (x * z < y * t)%Q.
Proof.
intros * Hx Hxy Hz Hzt.
eapply lt_le_trans.
-apply mul_lt_mono_pos_r; [ easy | apply Hxy ].
-apply mul_le_mono_pos_l; [ | easy ].
 eapply le_lt_trans; [ apply Hx | apply Hxy ].
Qed.

Theorem add_pair : ∀ a b c d,
  b ≠ 0 → d ≠ 0 → (a // b + c // d = (a * d + b * c) // (b * d))%Q.
Proof.
intros * Hb Hd.
unfold "+"%Q.
remember (a // b)%Q as ab eqn:Hab; symmetry in Hab.
destruct ab as [| pab| pab]; [ | | now destruct a ].
-unfold "//"%Q in Hab.
 destruct a; [ simpl | easy ].
 rewrite <- mul_pair; [ | easy | easy ].
 rewrite pair_diag; [ | easy ].
 now rewrite mul_1_l.
-remember (c // d)%Q as cd eqn:Hcd; symmetry in Hcd.
 move cd before pab.
 destruct cd as [| pcd| pcd]; [ | | now destruct c ].
 +unfold "//"%Q in Hcd.
  destruct c; [ | easy ].
  rewrite Nat.mul_0_r, Nat.add_0_r; simpl.
  rewrite <- mul_pair; [ | easy | easy ].
  rewrite pair_diag; [ | easy ].
  now rewrite mul_1_r.
 +unfold NQadd_pos_l.
  unfold "//"%Q.
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

Theorem sub_pair_pos : ∀ a b c d,
  b ≠ 0 → d ≠ 0 → b * c ≤ a * d
  → (a // b - c // d)%Q = ((a * d - b * c) // (b * d))%Q.
Proof.
intros * Hb Hd Hle.
destruct b; [ flia Hb | ].
destruct d; [ flia Hd | ].
unfold sub.
destruct a. {
  destruct c; [ easy | cbn in Hle; flia Hle ].
}
remember (S a // S b)%Q as ab eqn:Hab; symmetry in Hab.
destruct ab as [| pab| pab]; [ easy | | easy ].
injection Hab; clear Hab; intros Hab; subst pab.
-remember (S a // S b)%Q as ab eqn:Hab; symmetry in Hab.
 destruct ab as [| pab| pab]; [ easy | | easy ].
 injection Hab; clear Hab; intros Hab; subst pab.
 destruct c.
 +rewrite Nat.mul_0_r, Nat.sub_0_r.
  rewrite <- mul_pair; [ | easy | easy ].
  rewrite pair_diag; [ | easy ].
  now rewrite mul_1_r.
 +remember (S a) as sa; remember (S b) as sb; simpl; subst sa sb.
  unfold "//"%Q.
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

Theorem sub_pair_neg : ∀ a b c d,
  b ≠ 0 → d ≠ 0 → a * d < b * c
  → (a // b - c // d)%Q = (- (b * c - a * d) // (b * d))%Q.
Proof.
intros * Hb Hd Hlt.
destruct b; [ flia Hb | ].
destruct d; [ flia Hd | ].
unfold sub.
destruct a.
-destruct c; [ now rewrite Nat.mul_0_r | ].
 remember (S b) as x; simpl; subst x.
 rewrite Nat.sub_0_r.
 remember (S b * S c) as bc eqn:Hbc; symmetry in Hbc.
 destruct bc; [ easy | rewrite <- Hbc ].
 rewrite <- mul_pair; [ | easy | easy ].
 rewrite pair_diag; [ | easy ].
 now rewrite mul_1_l.
-remember (S a // S b)%Q as ab eqn:Hab; symmetry in Hab.
 destruct ab as [| pab| pab]; [ easy | | easy ].
 injection Hab; clear Hab; intros Hab; subst pab.
 destruct c; [ now rewrite Nat.mul_0_r in Hlt | ].
 remember (S a) as sa; remember (S b) as sb; simpl; subst sa sb.
 unfold "//"%Q.
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
  remember S as f; cbn; subst f.
  f_equal; f_equal; [ f_equal; apply Nat.mul_comm | apply Nat.mul_comm ].
 *apply -> GQlt_pair in Hb1; [ | easy | easy | easy | easy ].
  setoid_rewrite Nat.mul_comm in Hb1.
  flia Hlt Hb1.
Qed.

Theorem pair_add_l : ∀ a b c,
  ((a + b) // c)%Q = (a // c + b // c)%Q.
Proof.
intros.
destruct c. {
  do 3 rewrite den_0.
  rewrite add_pair; [ | easy | easy ].
  now rewrite Nat.mul_1_l, Nat.mul_1_r.
}
rewrite add_pair; [ | easy | easy ].
rewrite Nat.mul_comm, <- Nat.mul_add_distr_l.
rewrite <- mul_pair; [ | easy | easy ].
rewrite pair_diag; [ | easy ].
now rewrite mul_1_l.
Qed.

Theorem pair_sub_l : ∀ a b c,
  b ≤ a → ((a - b) // c)%Q = (a // c - b // c)%Q.
Proof.
intros * Hba.
destruct c. {
  do 3 rewrite den_0.
  rewrite sub_pair_pos; [ | easy | easy | ].
  -now rewrite Nat.mul_1_r, Nat.mul_1_l.
  -now rewrite Nat.mul_comm; apply Nat.mul_le_mono_r.
}
rewrite sub_pair_pos; [ | easy | easy | ]; cycle 1. {
  now rewrite Nat.mul_comm; apply Nat.mul_le_mono_r.
}
rewrite Nat.mul_comm, <- Nat.mul_sub_distr_l.
rewrite <- mul_pair; [ | easy | easy ].
rewrite pair_diag; [ | easy ].
now rewrite mul_1_l.
Qed.

Theorem pair_mul_l : ∀ a b c, ((a * b) // c)%Q = (a // c * b // 1)%Q.
Proof.
intros.
destruct (zerop c) as [Hc| Hc].
-subst c; do 2 rewrite den_0.
 replace 1 with (1 * 1) at 1 by easy.
 rewrite mul_pair; [ easy | easy | flia ].
-replace c with (c * 1) at 1 by flia.
 rewrite mul_pair; [ easy | flia Hc | flia ].
Qed.

Theorem pair_mul_r : ∀ a b c, ((a * b) // c)%Q = (a // 1 * b // c)%Q.
Proof.
intros.
rewrite Nat.mul_comm, mul_comm.
apply pair_mul_l.
Qed.

Theorem mul_pair_den_num : ∀ a b c, b ≠ 0 → (a // b * b // c = a // c)%Q.
Proof.
intros * Hb.
destruct (zerop c) as [Hc| Hc].
-subst c; do 2 rewrite den_0.
 rewrite mul_pair; [ | easy | easy ].
 rewrite Nat.mul_1_r, pair_mul_r.
 rewrite pair_diag; [ now rewrite mul_1_r | easy ].
-rewrite mul_pair; [ | easy | flia Hc ].
 rewrite Nat.mul_comm.
 rewrite <- mul_pair; [ | easy | flia Hc ].
 now rewrite pair_diag, mul_1_l.
Qed.

Definition frac x := ((num x mod den x) // den x)%Q.
Definition intg x := num x / den x.

Arguments frac x%Q.
Arguments intg x%Q.

Theorem frac_pair : ∀ a b, frac (a // b) = ((a mod b) // b)%Q.
Proof.
intros.
destruct (zerop a) as [Ha| Ha].
-subst a; destruct b; [ easy | cbn; now rewrite Nat.sub_diag ].
-destruct a; [ easy | clear Ha ].
 unfold frac; cbn.
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
  rewrite <- mul_pair; [ | easy | easy ].
  rewrite pair_diag; [ | easy ].
  now rewrite mul_1_r.
Qed.

Theorem den_neq_0 : ∀ x, den x ≠ 0.
Proof.
intros x.
destruct x; [ easy | | ].
-unfold den, GQden.
 now rewrite Nat.add_1_r.
-unfold den, GQden.
 now rewrite Nat.add_1_r.
Qed.

Hint Resolve den_neq_0.

Theorem num_pair_1_r : ∀ a, num (a // 1) = a.
Proof.
intros.
destruct a; [ easy | cbn ].
now apply GQnum_pair_1_r.
Qed.

Theorem den_pair_1_r : ∀ a, den (a // 1) = 1.
Proof.
intros.
destruct a; [ easy | cbn ].
now apply GQden_pair_1_r.
Qed.

Theorem num_pair : ∀ a b, num (a // b) = a / Nat.gcd a (max 1 b).
Proof.
intros.
destruct a; [ now destruct b | ].
destruct b. {
  rewrite den_0, Nat.gcd_1_r, num_pair_1_r.
  symmetry; apply Nat.div_1_r.
}
unfold "//"%Q.
rewrite Nat.max_r; [ | flia ].
unfold num.
now rewrite GQnum_pair.
Qed.

Theorem den_pair : ∀ a b, den (a // b) = max 1 (b / Nat.gcd a b).
Proof.
intros.
destruct a.
-rewrite Nat.gcd_0_l.
 destruct b; [ easy | ].
 now rewrite Nat.div_same.
-destruct b.
 +rewrite den_0.
  rewrite Nat.gcd_0_r.
  rewrite Nat.div_0_l; [ | easy ].
  now rewrite den_pair_1_r.
 +unfold "//"%Q.
  unfold den.
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

Theorem num_den : ∀ x, (0 ≤ x)%Q → x = (num x // den x)%Q.
Proof.
intros x Hx.
destruct x as [| px| px]; [ easy | | easy ].
unfold num, den, "//"%Q.
remember (GQnum px) as a eqn:Ha; symmetry in Ha.
destruct a; [ now apply GQnum_neq_0 in Ha | ].
rewrite <- Ha; f_equal.
apply GQnum_den.
Qed.

Theorem num_den_neg : ∀ x, (x < 0)%Q → x = (- num x // den x)%Q.
Proof.
intros x Hx.
destruct x as [| px| px]; [ easy | easy | ].
unfold num, den, "//"%Q.
remember (GQnum px) as a eqn:Ha; symmetry in Ha.
destruct a; [ now apply GQnum_neq_0 in Ha | cbn ].
rewrite <- Ha; f_equal.
apply GQnum_den.
Qed.

Theorem intg_frac : ∀ x, (0 ≤ x)%Q → x = (intg x // 1 + frac x)%Q.
Proof.
intros * Hx.
unfold intg, frac.
rewrite add_pair; [ | easy | pauto ].
do 2 rewrite Nat.mul_1_l.
rewrite Nat.mul_comm.
rewrite <- Nat.div_mod; [ | pauto ].
now apply num_den.
Qed.

Theorem frac_of_intg : ∀ x, (0 ≤ x)%Q → frac x = (x - intg x // 1)%Q.
Proof.
intros * Hx.
rewrite (intg_frac x) at 2; [ | easy ].
now rewrite add_comm, add_sub.
Qed.

Theorem intg_to_frac : ∀ x, (0 ≤ x)%Q → (intg x // 1 = x - frac x)%Q.
Proof.
intros * Hx.
rewrite (intg_frac x) at 2; [ | easy ].
now rewrite add_sub.
Qed.

Theorem frac_small : ∀ x, (0 ≤ x < 1)%Q → frac x = x.
Proof.
intros * Hx.
destruct x as [| px| px]; [ easy | | easy ].
cbn in Hx; destruct Hx as (_, Hx).
rewrite (GQnum_den px) in Hx.
apply GQpair_lt_nat_r in Hx; [ | easy | easy | easy ].
rewrite Nat.mul_1_r in Hx.
unfold frac; cbn.
rewrite Nat.mod_small; [ | easy ].
unfold "//"%Q.
remember (GQnum px) as nx eqn:Hnx.
remember (GQden px) as dx eqn:Hdx.
symmetry in Hnx, Hdx.
move dx before nx.
destruct nx; [ now apply GQnum_neq_0 in Hnx | f_equal ].
destruct dx; [ now apply GQden_neq_0 in Hdx | ].
now rewrite (GQnum_den px), Hnx, Hdx.
Qed.

Theorem frac_less_small : ∀ n x,
  (n // 1 ≤ x < n // 1 + 1)%Q → frac x = (x - n // 1)%Q.
Proof.
intros * Hx.
destruct x as [| px| px].
-destruct Hx as (H, _).
 replace 0%Q with (0 // 1)%Q in H by easy.
 apply le_pair in H; [ | easy | easy ].
 rewrite Nat.mul_comm in H.
 apply Nat.mul_le_mono_pos_l in H; [ | pauto ].
 now apply Nat.le_0_r in H; subst n.
-cbn in Hx; destruct Hx as (H1, H2).
 destruct n; [ now apply frac_small | ].
 rewrite (GQnum_den px) in H1, H2; cbn in H1, H2.
 apply GQpair_le_nat_l in H1; [ | easy | easy | easy ].
 rewrite <- GQpair_add_l in H2; [ | easy | easy | easy ].
 apply GQpair_lt_nat_r in H2; [ | easy | easy | easy ].
 rewrite Nat.mul_comm in H2.
 unfold frac; cbn.
 rewrite (Nat_mod_less_small (S n)); [ | easy ].
 unfold "//"%Q.
 remember (GQnum px) as nx eqn:Hnx.
 remember (GQden px) as dx eqn:Hdx.
 symmetry in Hnx, Hdx.
 move dx before nx.
 rewrite (GQnum_den px), Hnx, Hdx.
 remember (nx - S n * dx) as x eqn:Hx.
 symmetry in Hx.
 destruct x.
 +replace nx with (S n * dx) by flia H1 Hx.
  destruct dx; [ now rewrite Nat.mul_comm in H2 | ].
  rewrite Nat.mul_comm, GQpair_mul_l; [ | easy | easy | easy ].
  rewrite GQpair_diag, GQmul_1_l; [ | easy ].
  now rewrite GQcompare_diag.
 +remember (GQcompare (nx // dx) (S n // 1)) as c eqn:Hc.
  symmetry in Hc.
  destruct c; GQcompare_iff.
  *exfalso.
   apply GQeq_pair in Hc; [ | | | easy | easy ].
  --rewrite Nat.mul_1_r, Nat.mul_comm in Hc.
    now rewrite Hc, Nat.sub_diag in Hx.
  --now intros H3; rewrite H3 in Hx.
  --now intros H3; rewrite H3, Nat.mul_0_r in H2.
  *exfalso.
   apply GQnle_gt in Hc; apply Hc; clear Hc.
   apply GQle_pair; [ easy | easy | | | ].
  --now intros H3; rewrite H3 in Hx.
  --now intros H3; rewrite H3, Nat.mul_0_r in H2.
  --now rewrite Nat.mul_1_l.
 *f_equal; rewrite Nat.mul_comm in Hx.
  rewrite GQsub_pair; [ | | | easy | easy | ].
 --now do 2 rewrite Nat.mul_1_r; rewrite Hx.
 --now intros H3; rewrite H3 in Hx.
 --now intros H3; rewrite H3, Nat.mul_0_r in H2.
 --rewrite Nat.mul_comm, Nat.mul_1_r.
   unfold GQgt in Hc.
   apply -> GQlt_pair in Hc; [ | | | easy | easy ].
  ++now rewrite Nat.mul_1_l in Hc.
  ++now intros H; rewrite H, Nat.mul_comm in H2.
  ++now intros H; rewrite H in Hx.
-now destruct n.
Qed.

Theorem intg_0 : intg 0 = 0.
Proof. easy. Qed.

Theorem intg_1 : intg 1 = 1.
Proof. easy. Qed.

Theorem frac_0 : frac 0 = 0%Q.
Proof. easy. Qed.

Theorem frac_1 : frac 1 = 0%Q.
Proof. easy. Qed.

Theorem frac_of_nat : ∀ n, frac (n // 1) = 0%Q.
Proof.
intros.
unfold frac.
rewrite num_pair_1_r.
rewrite den_pair_1_r.
now rewrite Nat.mod_1_r.
Qed.

Theorem frac_ge_0 : ∀ x, (0 ≤ frac x)%Q.
Proof.
intros.
unfold frac.
replace 0%Q with (0 // 1)%Q by easy.
apply le_pair; [ easy | easy | ].
rewrite Nat.mul_1_l; cbn; flia.
Qed.

Hint Resolve frac_ge_0.

Theorem frac_lt_1 : ∀ x, (frac x < 1)%Q.
Proof.
intros.
unfold frac.
apply lt_pair; [ easy | easy | ].
do 2 rewrite Nat.mul_1_r.
now apply Nat.mod_upper_bound.
Qed.

Theorem frac_le : ∀ x, (0 ≤ x)%Q → (frac x ≤ x)%Q.
Proof.
intros x Hx.
unfold frac.
destruct x as [| xp| xp]; [ easy | | easy ].
cbn.
rewrite num_den; [ | easy ].
apply le_pair; [ apply GQden_neq_0 | pauto | ].
cbn; rewrite Nat.mul_comm.
apply Nat.mul_le_mono_l, Nat.mod_le, GQden_neq_0.
Qed.

Theorem intg_small : ∀ x, (0 ≤ x < 1)%Q → intg x = 0.
Proof.
intros * (Hx1, Hx2).
destruct x as [| xp| xp]; [ easy | | easy ].
unfold intg; cbn.
apply Nat.div_small.
unfold "<"%Q in Hx2; cbn in Hx2.
unfold "<"%GQ in Hx2; cbn in Hx2.
unfold PQ.PQlt, PQ.nd in Hx2; cbn in Hx2.
now rewrite Nat.mul_1_r, Nat.add_0_r in Hx2.
Qed.

Theorem intg_less_small : ∀ n x,
  (n // 1 ≤ x < n // 1 + 1)%Q → intg x = n.
Proof.
intros * Hx.
apply (pair_eq_r _ _ 1).
rewrite intg_to_frac.
-rewrite (frac_less_small n); [ | easy ].
 now rewrite sub_sub_distr, sub_diag.
-eapply le_trans; [ | apply Hx ].
 replace 0%Q with (0 // 1)%Q by easy.
 apply le_pair_mono_r, Nat.le_0_l.
Qed.

Theorem eq_intg_0 : ∀ x, (0 ≤ x)%Q → intg x = 0 → (x < 1)%Q.
Proof.
intros * Hx1 Hx2.
destruct x as [| x| x]; [ easy | | easy ].
unfold intg in Hx2; cbn in Hx2; cbn.
rewrite (GQnum_den x).
apply GQlt_pair; [ easy | easy | easy | easy | ].
do 2 rewrite Nat.mul_1_r.
now apply Nat_div_small_iff.
Qed.

Theorem intg_of_frac : ∀ x, intg (frac x) = 0.
Proof.
intros.
apply intg_small.
split; [ easy | apply frac_lt_1 ].
Qed.

Theorem intg_lt_lt : ∀ a b, (0 ≤ a)%Q → intg a < b → (a < b // 1)%Q.
Proof.
intros * Ha Hab.
unfold intg in Hab.
rewrite (num_den a); [ | easy ].
apply lt_pair; [ easy | easy | ].
rewrite Nat.mul_1_r.
destruct b; [ easy | ].
apply Nat.succ_le_mono in Hab.
apply (Nat.mul_le_mono_l _ _ (den a)) in Hab.
apply (Nat.add_le_mono_r _ _ (den a)) in Hab.
rewrite <- Nat.add_1_r, Nat.mul_add_distr_l, Nat.mul_1_r.
eapply Nat.lt_le_trans; [ | apply Hab ].
specialize (Nat.div_mod (num a) (den a) (den_neq_0 _)) as H1.
rewrite H1 at 1.
apply Nat.add_lt_mono_l.
now apply Nat.mod_upper_bound.
Qed.

Theorem frac_add_nat_l : ∀ a x, (0 ≤ x)%Q →
  frac (a // 1 + x)%Q = frac x.
Proof.
intros * Hx.
unfold frac.
apply eq_pair; [ pauto | pauto | ].
rewrite (num_den x); [ | easy ].
rewrite add_pair; [ | easy | pauto ].
do 2 rewrite Nat.mul_1_l.
rewrite num_pair.
rewrite Nat.max_r; [ | apply Nat.neq_0_lt_0; pauto ].
rewrite <- num_den; [ | easy ].
rewrite den_pair.
remember (Nat.gcd (a * den x + num x) (den x)) as c eqn:Hc.
assert (Hcz : c ≠ 0). {
  intros H; rewrite Hc in H.
  apply Nat.gcd_eq_0_r in H.
  now apply den_neq_0 in H.
}
rewrite Nat.max_r; cycle 1. {
  apply Nat.div_le_lower_bound; [ easy | ].
  rewrite Nat.mul_1_r; subst c.
  apply Nat_gcd_le_r; pauto.
}
apply (Nat.mul_cancel_l _ _ c); [ easy | ].
assert (Hcd : c * (den x / c) = den x). {
  rewrite <- Nat.divide_div_mul_exact; [ | easy | ].
  -now rewrite Nat.mul_comm, Nat.div_mul.
  -rewrite Hc; apply Nat.gcd_divide_r.
}
do 2 rewrite Nat.mul_assoc.
rewrite Hcd, Nat.mul_comm; f_equal.
rewrite <- Nat.mul_mod_distr_l; [ | | easy ]; cycle 1. {
  intros H.
  apply Nat.div_small_iff in H; [ | easy ].
  apply Nat.nle_gt in H; apply H; rewrite Hc.
  apply Nat_gcd_le_r; pauto.
}
rewrite Hcd.
rewrite <- (proj2 (Nat.div_exact _ c Hcz)).
-rewrite Nat.add_comm, Nat.mod_add; [ easy | pauto ].
-rewrite Hc.
 apply Nat.mod_divide; [ now rewrite <- Hc | apply Nat.gcd_divide_l ].
Qed.

Theorem frac_sub_nat_r : ∀ a x, (0 ≤ x)%Q → (a // 1 ≤ x)%Q →
  frac (x - a // 1)%Q = frac x.
Proof.
intros * Hx Hax.
unfold frac.
apply eq_pair; [ pauto | pauto | ].
rewrite (num_den x); [ | easy ].
assert (Haxl : a * den x ≤ num x). {
  rewrite (num_den x) in Hax; [ | easy ].
  apply le_pair in Hax; [ | easy | easy ].
  now rewrite Nat.mul_1_l in Hax.
}
rewrite sub_pair_pos; [ | easy | pauto | ]; cycle 1. {
  now rewrite Nat.mul_comm, Nat.mul_1_r.
}
do 2 rewrite Nat.mul_1_r.
rewrite num_pair.
rewrite Nat.max_r; [ | apply Nat.neq_0_lt_0; pauto ].
rewrite <- num_den; [ | easy ].
rewrite den_pair.
remember (Nat.gcd (num x - den x * a) (den x)) as c eqn:Hc.
assert (Hcz : c ≠ 0). {
  intros H; rewrite Hc in H.
  apply Nat.gcd_eq_0_r in H.
  now apply den_neq_0 in H.
}
rewrite Nat.max_r; cycle 1. {
  apply Nat.div_le_lower_bound; [ easy | ].
  rewrite Nat.mul_1_r; subst c.
  apply Nat_gcd_le_r; pauto.
}
apply (Nat.mul_cancel_l _ _ c); [ easy | ].
assert (Hcd : c * (den x / c) = den x). {
  rewrite <- Nat.divide_div_mul_exact; [ | easy | ].
  -now rewrite Nat.mul_comm, Nat.div_mul.
  -rewrite Hc; apply Nat.gcd_divide_r.
}
do 2 rewrite Nat.mul_assoc.
rewrite Hcd, Nat.mul_comm; f_equal.
rewrite <- Nat.mul_mod_distr_l; [ | | easy ]; cycle 1. {
  intros H.
  apply Nat.div_small_iff in H; [ | easy ].
  apply Nat.nle_gt in H; apply H; rewrite Hc.
  apply Nat_gcd_le_r; pauto.
}
rewrite Hcd.
rewrite <- (proj2 (Nat.div_exact _ c Hcz)).
-rewrite <- (Nat.mod_add _ a); [ | easy ].
 now rewrite Nat.mul_comm, Nat.sub_add.
-rewrite Hc.
 apply Nat.mod_divide; [ now rewrite <- Hc | apply Nat.gcd_divide_l ].
Qed.

Theorem intg_interv : ∀ n x, (0 ≤ x)%Q →
  (n // 1 ≤ x < n // 1 + 1)%Q ↔ intg x = n.
Proof.
intros * Hxz.
split; intros Hx.
-unfold intg.
 replace x with (num x // den x)%Q in Hx; cycle 1. {
   now symmetry; apply num_den.
 }
 rewrite add_pair in Hx; [ | easy | easy ].
 do 2 rewrite Nat.mul_1_r in Hx.
 destruct Hx as (Hnx, Hxn).
 apply le_pair in Hnx; [ | easy | easy ].
 apply lt_pair in Hxn; [ | easy | easy ].
 rewrite Nat.mul_1_l in Hnx.
 rewrite Nat.mul_1_r, Nat.mul_comm in Hxn.
 now apply Nat_div_interv.
-subst n.
 rewrite intg_to_frac; [ | easy ].
 split; [ apply le_sub_l, frac_ge_0 | ].
 rewrite <- add_sub_swap.
 apply lt_add_lt_sub_r, add_lt_mono_l, frac_lt_1.
Qed.

Theorem frac_idemp : ∀ x, (0 ≤ x)%Q → frac (frac x) = frac x.
Proof.
intros * Hxz.
rewrite (frac_of_intg x); [ | easy ].
rewrite frac_sub_nat_r; [ | easy | now apply intg_interv ].
now apply frac_of_intg.
Qed.

Theorem intg_add_frac : ∀ x y,
  intg (frac x + frac y) =
  if lt_le_dec (frac x + frac y) 1 then 0 else 1.
Proof.
intros.
destruct (lt_le_dec (frac x + frac y) 1) as [H1| H1].
-unfold intg.
 rewrite Nat.div_small; [ easy | ].
 unfold "<"%Q in H1.
 remember (frac x + frac y)%Q as z eqn:Hz.
 symmetry in Hz.
 destruct z as [| zp| zp]; [ cbn; pauto | | ].
 +cbn in H1; cbn.
  replace zp with (GQnum zp // GQden zp)%GQ in H1 by now rewrite GQnum_den.
  apply GQpair_lt_nat_r in H1; [ | | | easy ]; cycle 1. {
    apply GQnum_neq_0.
  } {
    apply GQden_neq_0.
  }
  now rewrite Nat.mul_1_r in H1.
 +assert (H : (0 ≤ frac x + frac y)%Q). {
    replace 0%Q with (0 + 0)%Q by easy.
    apply add_le_mono; apply frac_ge_0.
  }
  now rewrite Hz in H.
-unfold intg.
 rewrite Nat_div_less_small; [ easy | ].
 cbn in H1.
 remember (frac x + frac y)%Q as z eqn:Hz.
 symmetry in Hz.
 destruct z as [| zp| zp]; [ easy | | easy ].
 replace zp with (GQnum zp // GQden zp)%GQ in H1 by now rewrite GQnum_den.
 apply GQpair_le_nat_l in H1; [ | easy | | ]; cycle 1. {
   apply GQnum_neq_0.
 } {
   apply GQden_neq_0.
 }
 rewrite Nat.mul_1_l in H1.
 split; [ easy | ].
 assert (H : (Pos zp < 2)%Q). {
   rewrite <- Hz.
   replace 2%Q with (1 + 1)%Q by easy.
   apply add_lt_mono; apply frac_lt_1.
 }
 cbn in H.
 remember mult as f; cbn; subst f.
 replace zp with (GQnum zp // GQden zp)%GQ in H by now rewrite GQnum_den.
 apply GQpair_lt_nat_r in H; [ | | | easy ]; cycle 1. {
   apply GQnum_neq_0.
 } {
   apply GQden_neq_0.
 }
 now rewrite Nat.mul_comm in H.
Qed.

Theorem intg_add : ∀ x y, (0 ≤ x)%Q → (0 ≤ y)%Q →
  intg (x + y) = intg x + intg y + intg (frac x + frac y).
Proof.
intros * Hxz Hyz.
rewrite intg_add_frac.
apply intg_interv.
-replace 0%Q with (0 + 0)%Q by easy.
 now apply add_le_mono.
-destruct (lt_le_dec (frac x + frac y) 1) as [H1| H1].
 +rewrite Nat.add_0_r.
  split.
  *rewrite pair_add_l.
   apply add_le_mono; now apply intg_interv.
  *rewrite (intg_frac x) at 1; [ | easy ].
   rewrite (intg_frac y) at 1; [ | easy ].
   rewrite pair_add_l.
   do 2 rewrite <- add_assoc.
   apply add_lt_mono_l.
   rewrite add_comm, <- add_assoc.
   apply add_lt_mono_l.
   now rewrite add_comm.
 +split.
  *rewrite (intg_frac x) at 2; [ | easy ].
   rewrite (intg_frac y) at 2; [ | easy ].
   do 2 rewrite pair_add_l.
   do 2 rewrite <- add_assoc.
   apply add_le_mono_l.
   rewrite add_assoc, add_comm, add_add_swap.
   now apply add_le_mono_r.
  *setoid_rewrite add_comm.
   do 2 rewrite pair_add_l.
   do 2 rewrite add_assoc.
   rewrite add_comm, <- add_assoc.
   apply add_le_lt_mono.
   --apply lt_le_incl; rewrite add_comm.
     now apply intg_interv.
   --now apply intg_interv.
Qed.

Theorem frac_add : ∀ x y, (0 ≤ x)%Q → (0 ≤ y)%Q →
  frac (x + y) = frac (frac x + frac y).
Proof.
intros * Hxz Hyz.
rewrite (intg_frac x Hxz) at 1.
rewrite (intg_frac y Hyz) at 1.
rewrite add_comm, <- add_assoc, frac_add_nat_l; cycle 1. {
  replace 0%Q with (0 + (0 // 1 + 0))%Q by easy.
  apply add_le_mono; [ apply frac_ge_0 | ].
  apply add_le_mono; [ | apply frac_ge_0 ].
  apply le_pair; [ easy | easy | ].
  rewrite Nat.mul_0_l, Nat.mul_1_l.
  apply Nat.le_0_l.
}
rewrite add_comm, <- add_assoc, frac_add_nat_l; cycle 1. {
  replace 0%Q with (0 + 0)%Q by easy.
  apply add_le_mono; apply frac_ge_0.
}
easy.
Qed.

Theorem frac_add_cond : ∀ x y, (0 ≤ x)%Q → (0 ≤ y)%Q →
  frac (x + y) =
    (frac x + frac y -
     if lt_le_dec (frac x + frac y) 1 then 0 else 1)%Q.
Proof.
intros * Hxz Hyz.
rewrite frac_of_intg. 2: {
  replace 0%Q with (0 + 0)%Q by easy.
  now apply add_le_mono.
}
rewrite intg_add; [ | easy | easy ].
rewrite intg_add_frac.
destruct (lt_le_dec (frac x + frac y)) as [H1| H1].
-rewrite Nat.add_0_r, sub_0_r.
 rewrite pair_add_l, sub_add_distr.
 rewrite add_sub_swap, <- add_sub_assoc.
 now f_equal; symmetry; apply frac_of_intg.
-rewrite pair_add_l, sub_add_distr.
 f_equal.
 rewrite pair_add_l, sub_add_distr.
 rewrite add_sub_swap, <- add_sub_assoc.
 now f_equal; symmetry; apply frac_of_intg.
Qed.

Theorem intg_add_cond : ∀ x y, (0 ≤ x)%Q → (0 ≤ y)%Q →
  intg (x + y) =
    intg x + intg y +
    if lt_le_dec (frac x + frac y) 1 then 0 else 1.
Proof.
intros * Hxz Hyz.
rewrite intg_add; [ | easy | easy ].
now rewrite intg_add_frac.
Qed.

Theorem intg_pair : ∀ a b, b ≠ 0 → intg (a // b) = a / b.
Proof.
intros * Hbz.
unfold intg.
rewrite num_pair, den_pair.
rewrite Nat.max_r; [ | flia Hbz ].
rewrite Nat.max_r; cycle 1. {
  specialize (Nat.gcd_divide_r a b) as H.
  destruct H as (c, Hc).
  rewrite Hc at 1.
  rewrite Nat.div_mul.
  -destruct c; [ easy | flia ].
  -intros H.
   now apply Nat.gcd_eq_0_r in H.
}
specialize (Nat.gcd_divide_r a b) as Hb.
destruct Hb as (c, Hc).
rewrite Hc at 2.
rewrite Nat.div_mul; cycle 1. {
  intros H; now apply Nat.gcd_eq_0_r in H.
}
rewrite Nat.div_div; cycle 1. {
  intros H; now apply Nat.gcd_eq_0_r in H.
}
-now intros H; subst c.
-now rewrite Nat.mul_comm, <- Hc.
Qed.

Theorem intg_le_mono : ∀ x y, (0 ≤ x)%Q → (x ≤ y)%Q → intg x ≤ intg y.
Proof.
intros * Hx Hxy.
assert (Hy : (0 ≤ y)%Q) by (eapply le_trans; [ apply Hx | apply Hxy ]).
move Hy before Hx.
specialize (proj2 (intg_interv _ _ Hx) eq_refl) as H1.
specialize (proj2 (intg_interv _ _ Hy) eq_refl) as H2.
apply Nat.lt_succ_r.
rewrite <- Nat.add_1_r.
setoid_rewrite <- Nat.mul_1_l.
rewrite Nat.mul_comm.
apply lt_pair; [ easy | easy | ].
eapply le_lt_trans; [ apply H1 | ].
eapply le_lt_trans; [ apply Hxy | ].
now rewrite pair_add_l.
Qed.

Theorem intg_add_nat_l : ∀ a x, (0 ≤ x)%Q →
  intg (a // 1 + x)%Q = a + intg x.
Proof.
intros * Hx.
rewrite intg_add; [ | | easy ]. 2: {
  replace 0%Q with (0 // 1)%Q by easy.
  apply le_pair; [ easy | easy | cbn; flia ].
}
rewrite Nat.add_shuffle0; f_equal.
rewrite intg_pair; [ | easy ].
rewrite Nat.div_1_r.
rewrite frac_of_nat, add_0_l.
now rewrite intg_of_frac, Nat.add_0_r.
Qed.

Theorem pow_pair_l : ∀ n a b, n ≠ 0 → b ≤ a →
  (n ^ a // n ^ b)%Q = (n ^ (a - b) // 1)%Q.
Proof.
intros * Hn Hba.
apply eq_pair; [ | easy | ].
-now apply Nat.pow_nonzero.
-rewrite Nat.mul_1_r.
 rewrite <- Nat.pow_add_r; f_equal.
 rewrite Nat.add_comm.
 now rewrite Nat.sub_add.
Qed.

Theorem pow_pair_r : ∀ n a b, n ≠ 0 → a ≤ b →
  (n ^ a // n ^ b)%Q = (1 // n ^ (b - a))%Q.
Proof.
intros * Hn Hab.
apply eq_pair.
-now apply Nat.pow_nonzero.
-now apply Nat.pow_nonzero.
-rewrite Nat.mul_1_r.
 rewrite <- Nat.pow_add_r; f_equal.
 rewrite Nat.add_comm.
 now rewrite Nat.sub_add.
Qed.

Theorem le_decidable : ∀ x y, Decidable.decidable (x ≤ y)%Q.
Proof.
intros.
unfold Decidable.decidable.
destruct x as [| xp| xp], y as [| yp| yp]; (try now left); (try now right).
-apply GQle_decidable.
-apply GQle_decidable.
Qed.

Theorem le_0_add : ∀ x y, (0 ≤ x)%Q → (0 ≤ y)%Q → (0 ≤ x + y)%Q.
Proof.
intros * Hx Hy.
replace 0%Q with (0 + 0)%Q by easy.
now apply add_le_mono.
Qed.

Theorem eq_add_0 : ∀ x y, (0 ≤ x)%Q → (0 ≤ y)%Q →
  (x + y = 0)%Q ↔ x = 0%Q ∧ y = 0%Q.
Proof.
intros * Hx Hy.
split.
-intros Hxy.
 split.
 +apply le_antisymm in Hx; [ easy | ].
  apply (add_le_mono_r _ _ y).
  now rewrite Hxy.
 +apply le_antisymm in Hy; [ easy | ].
  apply (add_le_mono_r _ _ x).
  now rewrite add_comm, Hxy.
-now intros (H1, H2); subst x y.
Qed.

Theorem intg_sub_nat_l_lt : ∀ n x,
  (0 < x ≤ n // 1)%Q
  → intg (n // 1 - x)%Q < n.
Proof.
intros * (Hx, Hxn).
rewrite (num_den x); [ | now apply lt_le_incl ].
rewrite (num_den x) in Hxn; [ | now apply lt_le_incl ].
rewrite sub_pair_pos; [ | easy | easy | ]. 2: {
  apply le_pair in Hxn; [ | easy | easy ].
  rewrite Nat.mul_1_r in Hxn.
  now rewrite Nat.mul_1_l, Nat.mul_comm.
}
do 2 rewrite Nat.mul_1_l.
rewrite intg_pair; [ | easy ].
rewrite le_pair in Hxn; [ | easy | easy ].
rewrite Nat.mul_1_r in Hxn.
remember (num x) as xn eqn:Hn.
remember (den x) as xd eqn:Hd.
move xd before xn.
assert (H1 : (n * xd - xn) / xd ≤ n). {
  now apply Nat_mul_sub_div_le; rewrite Nat.mul_comm.
}
apply Nat_le_neq_lt; [ easy | ].
intros H2; clear H1.
destruct x as [| x| x]; [ easy | clear Hx | easy ].
assert (H1 : xd ≠ 0) by now rewrite Hd.
assert (H3 : xn ≠ 0) by (rewrite Hn; apply GQnum_neq_0).
specialize (Nat.div_mod (n * xd - xn) xd H1) as H4.
rewrite H2 in H4.
apply Nat.add_sub_eq_nz in H4. 2: {
  intros H.
  apply Nat.eq_add_0 in H.
  destruct H as (H5, H6).
  apply Nat.eq_mul_0 in H5.
  destruct H5 as [H5| H5]; [ easy | ].
  subst n.
  rewrite Nat.mul_0_r in Hxn.
  now apply Nat.le_0_r in Hxn.
}
rewrite Nat.add_comm, <- Nat.add_assoc in H4.
apply Nat.add_sub_eq_l in H4.
rewrite Nat.mul_comm in H4.
symmetry in H4; rewrite Nat.sub_diag in H4.
now apply Nat.eq_add_0 in H4.
Qed.

Theorem le_0_pair : ∀ a b, (0 ≤ a // b)%Q.
Proof.
intros.
replace 0%Q with (0 // 1)%Q by easy.
destruct b. {
  rewrite den_0.
  apply le_pair; [ easy | easy | apply Nat.le_0_l ].
}
apply le_pair; [ easy | easy | apply Nat.le_0_l ].
Qed.

Theorem lt_0_pair : ∀ a b, (0 < a // b)%Q ↔ 0 < a.
Proof.
intros.
split; intros Ha.
-apply Nat.nle_gt; intros H.
 now apply Nat.le_0_r in H; rewrite H in Ha.
-replace 0%Q with (0 // 1)%Q by easy.
 destruct b. {
   rewrite den_0.
   apply lt_pair; [ easy | easy | ].
   now rewrite Nat.mul_1_l.
 }
 apply lt_pair; [ easy | easy | ].
 now rewrite Nat.mul_1_l.
Qed.

Theorem le_0_mul_l : ∀ a b, (0 < a → 0 ≤ a * b ↔ 0 ≤ b)%Q.
Proof.
intros * Ha.
split.
-intros Hab.
 apply (mul_le_mono_pos_l a); [ easy | ].
 now rewrite mul_comm.
-intros Hb.
 replace 0%Q with (a * 0)%Q by apply mul_0_r.
 now apply mul_le_mono_pos_l.
Qed.

Theorem le_0_mul_r : ∀ a b, (0 < b → 0 ≤ a * b ↔ 0 ≤ a)%Q.
Proof.
intros.
rewrite mul_comm.
now apply le_0_mul_l.
Qed.

Theorem mul_pos_cancel_l : ∀ a b, (0 < a → 0 < a * b ↔ 0 < b)%Q.
Proof.
intros * Ha.
split.
-intros Hab.
 apply (mul_lt_mono_pos_l a); [ easy | ].
 now rewrite mul_comm.
-intros Hb.
 replace 0%Q with (a * 0)%Q by apply mul_0_r.
 now apply mul_lt_mono_pos_l.
Qed.

Theorem mul_pos_cancel_r: ∀ a b, (0 < b → 0 < a * b ↔ 0 < a)%Q.
Proof.
intros.
rewrite mul_comm.
now apply mul_pos_cancel_l.
Qed.

Definition ord_ring_def :=
  {| rng_t := ty;
     rng_zero := 0%Q;
     rng_add := add;
     rng_sub := sub;
     rng_mul := mul;
     rng_le := le |}.

Canonical Structure ord_ring_def.

Definition ord_ring :=
  {| rng_add_0_l := add_0_l;
     rng_add_comm := add_comm;
     rng_add_assoc := add_assoc;
     rng_sub_diag := sub_diag;
     rng_mul_comm := mul_comm;
     rng_mul_assoc := mul_assoc;
     rng_mul_add_distr_l := mul_add_distr_l;
     rng_mul_sub_distr_l := mul_sub_distr_l;
     rng_le_refl := le_refl;
     rng_le_antisymm := le_antisymm;
     rng_add_le_compat := add_le_mono |}.

Theorem summation_pair_distr_r (rgi := nat_ord_ring) (rgq := ord_ring) :
   ∀ b e g a,
   ((Σ (i = b, e), g i) // a = Σ (i = b, e), (g i // a))%Q.
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
destruct a; [ do 3 rewrite den_0 | ]; now rewrite <- pair_add_l.
Qed.

Theorem summation_pair_distr_l (rgi := nat_ord_ring) (rgp := ord_ring) :
  ∀ b e g a,
  ((Σ (i = b, e), a // g i = a // 1 * Σ (i = b, e), (1 // g i))%Q).
Proof.
intros.
rewrite summation_eq_compat with (h := λ i, (a // 1 * 1 // g i)%Q). 2: {
  intros i Hi.
  destruct (eq_nat_dec (g i) 0) as [H1| H1]. {
    rewrite H1.
    do 2 rewrite den_0.
    now rewrite mul_1_r.
  }
  rewrite mul_pair; [ | easy | easy ].
  now rewrite Nat.mul_1_r, Nat.mul_1_l.
}
now rewrite <- summation_mul_distr_l.
Qed.

Theorem sum_pair (rgn := nat_ord_ring) (rnq := ord_ring) : ∀ a b e f,
  ((Σ (i = b, e), f i) // a)%Q = Σ (i = b, e), (f i // a)%Q.
Proof.
intros.
destruct (lt_dec e b) as [H1| H1]. {
  rewrite summation_empty; [ | easy ].
  now rewrite summation_empty.
}
apply Nat.nlt_ge in H1.
unfold summation.
remember (S e - b) as n eqn:Hn.
revert a b e Hn H1.
induction n; intros; [ easy | ].
cbn.
rewrite pair_add_l; f_equal.
rewrite Nat.sub_succ_l in Hn; [ | easy ].
apply Nat.succ_inj in Hn.
destruct e; [ now subst n | ].
destruct (eq_nat_dec b (S e)) as [Hbe| Hbe].
-subst b.
 now rewrite Nat.sub_diag in Hn; subst n.
-apply IHn with (e := S e); [ | flia H1 Hbe ].
 now rewrite Nat.sub_succ.
Qed.

Theorem power_summation (rg := Q.ord_ring) : ∀ a n,
  a > 1
  → (Σ (i = 0, n), 1 // a ^ i = (a ^ S n - 1) // (a ^ n * (a - 1)))%Q.
Proof.
intros * Ha.
induction n.
-rewrite summation_only_one.
 rewrite Nat.pow_0_r, Nat.pow_1_r, Nat.mul_1_l.
 symmetry; apply pair_diag; flia Ha.
-rewrite summation_split_last; [ | flia ].
 rewrite IHn.
 remember of_pair as f; remember S as g; cbn; subst f g.
 rewrite add_pair; [ | | apply Nat.pow_nonzero; flia Ha ]; cycle 1. {
   intros H.
   apply Nat.eq_mul_0 in H.
   destruct H as [H| H]; [ | flia Ha H ].
   apply Nat.pow_nonzero in H; [ easy | flia Ha ].
 }
 rewrite Nat.mul_1_r.
 apply eq_pair. {
   intros H.
   apply Nat.eq_mul_0 in H.
   destruct H as [H| H].
   -apply Nat.eq_mul_0 in H.
    destruct H as [H| H]; [ | flia Ha H ].
    apply Nat.pow_nonzero in H; [ easy | flia Ha ].
   -apply Nat.pow_nonzero in H; [ easy | flia Ha ].
 } {
   intros H.
   apply Nat.eq_mul_0 in H.
   destruct H as [H| H]; [ | flia Ha H ].
   apply Nat.pow_nonzero in H; [ easy | flia Ha ].
 }
 rewrite Nat.mul_comm; symmetry.
 rewrite Nat.mul_shuffle0, Nat.mul_comm.
 do 2 rewrite <- Nat.mul_assoc; f_equal.
 rewrite Nat.mul_comm, <- Nat.mul_assoc; f_equal.
 rewrite Nat.mul_comm; symmetry.
 rewrite Nat.pow_succ_r' at 2.
 rewrite Nat.mul_assoc, Nat.mul_comm.
 rewrite <- Nat.mul_add_distr_l; f_equal.
 rewrite Nat.mul_sub_distr_r, Nat.mul_1_l.
 rewrite Nat.add_sub_assoc; [ | flia Ha ].
 rewrite Nat.sub_add; [ now rewrite Nat.mul_comm | ].
 replace a with (1 * a) at 1 by flia.
 apply Nat.mul_le_mono_pos_r; [ flia Ha | ].
 apply Nat.neq_0_lt_0, Nat.pow_nonzero; flia Ha.
Qed.

Theorem power_summation_inv (rg := ord_ring) : ∀ a n,
  a > 0
  → (1 - 1 // a ^ S n = (1 - 1 // a) * Σ (i = 0, n), 1 // a ^ i)%Q.
Proof.
intros * Ha.
destruct (eq_nat_dec a 1) as [Ha1| Ha1]. {
  now subst a; rewrite Nat.pow_1_l, sub_diag.
}
assert (Haa : a ≠ 0 ∧ a ≠ 1) by flia Ha Ha1; clear Ha Ha1.
rewrite power_summation; [ | flia Haa ].
symmetry.
rewrite sub_pair_pos; [ | easy | flia Haa | flia Haa ].
do 2 rewrite Nat.mul_1_l.
rewrite mul_pair; [ | flia Haa | ]; cycle 1. {
  intros H; apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ | flia Haa H ].
  apply Nat.pow_nonzero in H; [ easy | flia Haa ].
}
rewrite Nat.mul_comm, Nat.mul_assoc.
rewrite <- mul_pair; [ | | flia Haa ]; cycle 1. {
  intros H; apply Nat.eq_mul_0 in H.
  destruct H as [H| H]; [ flia Haa H | ].
  apply Nat.pow_nonzero in H; [ easy | flia Haa ].
}
rewrite pair_diag; [ | flia Haa ].
rewrite mul_1_r, <- Nat.pow_succ_r'.
destruct Haa as (Ha, Ha1).
rewrite sub_pair_pos; [ | flia | now apply Nat.pow_nonzero | ]; cycle 1. {
  apply Nat.mul_le_mono_l.
  apply (Nat.lt_le_trans _ 2); [ flia | cbn ].
  replace 2 with (2 * 1) by flia.
  apply Nat.mul_le_mono; [ flia Ha Ha1 | ].
  now apply Nat.neq_0_lt_0, Nat.pow_nonzero.
}
now do 2 rewrite Nat.mul_1_l.
Qed.

End Q.

Canonical Structure Q.ord_ring_def.
