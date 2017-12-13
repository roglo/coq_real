(* Natural numbers in any radix; second version; without proofs *)
(* Can be regarded as polynomials with natural number coefficients. *)

(* Implemented using lists of nat. *)
(* No constraints of digits having to be less than radix;
   to build a number whose digits are less than radix, use normalization
   by the function xnat_norm *)

Require Import Utf8 Arith Psatz.
Require List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Misc Summation.

Class radix := { rad : nat }.

Definition radix_2 := {| rad := 2 |}.
Definition radix_10 := {| rad := 10 |}.

Record xnat := xn { xnatv : list nat }.

Fixpoint move_carry_end {r : radix} iter carry :=
  match iter with
  | 0 => []
  | S i =>
      if zerop carry then []
      else carry mod rad :: move_carry_end i (carry / rad)
  end.

Fixpoint move_carry {r : radix} carry al :=
  match al with
  | [] => move_carry_end (S carry) carry
  | a :: al' => (carry + a) mod rad :: move_carry ((carry + a) / rad) al'
  end.

Definition list_of_nat {r : radix} carry n :=
  if zerop n then [] else move_carry carry [n].
Definition nat_of_list {r : radix} accu al :=
  List.fold_right (λ a accu, accu * rad + a) accu al.

Definition xnat_of_nat {r : radix} n := xn (list_of_nat 0 n).
Definition nat_of_xnat {r : radix} a := nat_of_list 0 (xnatv a).

Definition list_norm {r : radix} al := list_of_nat 0 (nat_of_list 0 al).

Definition xnat_norm {r : radix} a := xn (list_norm (xnatv a)).

(* Conversion from and to nat *)

Lemma nat_of_list_move_end {r : radix} : ∀ iter n, 2 ≤ rad →
  n < iter
  → nat_of_list 0 (move_carry_end iter n) = n.
Proof.
intros * Hr Hni.
revert n Hni.
induction iter; intros; [ now apply Nat.nlt_0_r in Hni | simpl ].
destruct (zerop n) as [Hn| Hn]; [ easy | simpl ].
rewrite IHiter.
 rewrite Nat.mul_comm; symmetry.
 apply Nat.div_mod; lia.

 apply lt_n_Sm_le in Hni.
 destruct rad as [| m]; [ lia | ].
 destruct m as [| m]; [ lia | ].
 destruct iter; [ lia | ].
 eapply lt_le_trans; [ | eassumption ].
 destruct n; [ easy | clear ].
 apply Nat.div_lt; lia.
Qed.

Lemma nat_of_list_list_of_nat {r : radix} : 2 ≤ rad →
  ∀ n, nat_of_list 0 (list_of_nat 0 n) = n.
Proof.
intros Hr *.
unfold list_of_nat.
destruct (zerop n) as [Hn| Hn]; [ easy | simpl ].
destruct (zerop (n / rad)) as [Hs| Hs].
 apply Nat.div_small_iff in Hs; [ | lia ].
 now rewrite Nat.mod_small.

 simpl.
 rewrite nat_of_list_move_end; [ | easy | now apply Nat.div_lt ].
 remember (n / rad) as nr eqn:Hnr.
 replace (nr / rad * rad) with (rad * (nr / rad)) by lia.
 rewrite <- Nat.div_mod; [ subst nr | lia ].
 rewrite Nat.mul_comm; symmetry.
 apply Nat.div_mod; lia.
Qed.

Theorem nat_of_xnat_inv {r : radix} : 2 ≤ rad →
  ∀ a, nat_of_xnat (xnat_of_nat a) = a.
Proof.
intros Hr *.
unfold xnat_of_nat, nat_of_xnat; simpl.
now apply nat_of_list_list_of_nat.
Qed.

Theorem xnat_of_nat_inv {r : radix} : 2 ≤ rad →
  ∀ a, xnat_of_nat (nat_of_xnat a) = xnat_norm a.
Proof. easy. Qed.

(* Normalized xnat have all digits less that radix *)

Lemma list_carry_end_digits_lt_radix {r : radix} : rad ≠ 0 →
  ∀ i c, List.Forall (λ a, a < rad) (move_carry_end i c).
Proof.
intros Hr *.
revert c.
induction i; intros; [ constructor | simpl ].
destruct (zerop c) as [Hzc| Hzc]; [ easy | ].
constructor; [ now apply Nat.mod_upper_bound | ].
apply IHi.
Qed.

Lemma list_of_nat_all_lt_radix {r : radix} : rad ≠ 0 →
  ∀ al, List.Forall (λ a, a < rad) (list_of_nat 0 al).
Proof.
intros Hr *.
induction al as [| a1]; [ constructor | ].
unfold list_of_nat; simpl.
constructor; [ now apply Nat.mod_upper_bound | ].
destruct (zerop (S a1 / rad)) as [Ha| Ha]; [ constructor | ].
constructor; [ now apply Nat.mod_upper_bound | ].
now apply list_carry_end_digits_lt_radix.
Qed.

Lemma list_norm_digits_lt_radix {r : radix} : rad ≠ 0 →
  ∀ al, List.Forall (λ a, a < rad) (list_norm al).
Proof.
intros Hr *.
now apply list_of_nat_all_lt_radix.
Qed.

Theorem xnat_norm_digits_lt_radix {r : radix} : rad ≠ 0 →
  ∀ a, List.Forall (λ a, a < rad) (xnatv (xnat_norm a)).
Proof.
intros Hr *.
unfold xnat_norm; simpl.
now apply list_norm_digits_lt_radix.
Qed.

(* Addition *)

Fixpoint list_add a b :=
  match a with
  | [] => b
  | a₀ :: al =>
      match b with
      | [] => a
      | b₀ :: bl => a₀ + b₀ :: list_add al bl
      end
  end.

Definition xnat_add a b :=
  xn (list_add (xnatv a) (xnatv b)).

Definition xnat_0 := xn [].

Delimit Scope xnat_scope with X.
Notation "a + b" := (xnat_add a b) : xnat_scope.
Notation "a = b" := (nat_of_xnat a = nat_of_xnat b) : xnat_scope.
Notation "0" := (xnat_0) : xnat_scope.

Lemma list_add_comm : ∀ al bl, list_add al bl = list_add bl al.
Proof.
intros *.
revert bl.
induction al as [| a1]; intros; [ now destruct bl | simpl ].
destruct bl as [| b1]; [ easy | simpl ].
now rewrite Nat.add_comm, IHal.
Qed.

Theorem xnat_add_comm : ∀ a b, (a + b)%X = (b + a)%X.
Proof.
intros.
unfold xnat_add; simpl.
now rewrite list_add_comm.
Qed.

Theorem xnat_add_comm' {r : radix} : ∀ a b, (a + b = b + a)%X.
Proof.
intros.
unfold xnat_add; simpl.
now rewrite list_add_comm.
Qed.

Theorem xnat_add_0_l {r : radix} : ∀ a, (0 + a = a)%X.
Proof. easy. Qed.

Lemma list_add_assoc : ∀ al bl cl,
  list_add al (list_add bl cl) = list_add (list_add al bl) cl.
Proof.
intros.
revert al cl.
induction bl as [| b1]; intros; simpl.
-now replace (list_add al []) with (list_add [] al) by apply list_add_comm.

-destruct cl as [| c1]; [ now destruct al | simpl ].
 destruct al as [| a1]; [ easy | simpl ].
 rewrite IHbl; f_equal; apply Nat.add_assoc.
Qed.

Theorem xnat_add_assoc : ∀ a b c,
  (a + (b + c))%X = ((a + b) + c)%X.
Proof.
intros Hr *.
unfold xnat_add; simpl; f_equal.
apply list_add_assoc.
Qed.

Theorem xnat_add_assoc' {r : radix} : rad ≠ 0 → ∀ a b c,
  (a + (b + c) = (a + b) + c)%X.
Proof.
intros Hr *.
unfold xnat_add; simpl; f_equal; f_equal.
apply list_add_assoc.
Qed.

(* Compatiblity addition with equality *)

Lemma nat_of_list_add_distr {r : radix} : 1 < rad → ∀ al bl,
  nat_of_list 0 (list_add al bl) = nat_of_list 0 al + nat_of_list 0 bl.
Proof.
intros Hr *.
revert bl.
induction al as [| a1]; intros; [ easy | simpl ].
destruct bl as [| b1]; [ now rewrite Nat.add_0_r | ].
simpl; rewrite IHal; lia.
Qed.

Lemma nat_of_list_add_eq_compat {r : radix} : 1 < rad → ∀ al bl cl,
  nat_of_list 0 al = nat_of_list 0 bl
  → nat_of_list 0 (list_add al cl) = nat_of_list 0 (list_add bl cl).
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hab.
rewrite nat_of_list_add_distr; [ | easy ].
rewrite nat_of_list_add_distr; [ | easy ].
now rewrite Hab.
Qed.

Theorem list_add_eq_compat {r : radix} : 1 < rad → ∀ a b c,
  (a = b)%X → (a + c = b + c)%X.
Proof.
intros Hr * Hab.
unfold nat_of_xnat in Hab.
unfold nat_of_xnat.
unfold xnat_add; simpl.
now apply nat_of_list_add_eq_compat.
Qed.

(* Multiplication *)

Fixpoint list_mul_loop (rg := nat_ord_ring) iter n al bl :=
  match iter with
  | 0 => []
  | S i =>
      Σ (j = 0, n), (List.nth j al 0 * List.nth (n - j) bl 0) ::
      list_mul_loop i (S n) al bl
  end.

Definition list_mul al bl :=
  let iter := length al + length bl - 1 in
  list_mul_loop iter 0 al bl.

Definition xnat_mul a b :=
  xn (list_mul (xnatv a) (xnatv b)).

Compute (xnat_mul (xn (@list_of_nat radix_10 0 11)) (xn (@list_of_nat radix_10 0 9))).
Compute (xnat_mul (xn (@list_of_nat radix_10 0 12)) (xn (@list_of_nat radix_10 0 12))).
Compute (xnat_mul (xn (@list_of_nat radix_10 0 14)) (xn (@list_of_nat radix_10 0 14))).
Compute (xnat_mul (xn (@list_of_nat radix_10 0 279)) (xn (@list_of_nat radix_10 0 1))).
Compute (@xnat_norm radix_10 (xnat_mul (xn (@list_of_nat radix_10 0 37)) (xn (@list_of_nat radix_10 0 18)))).

Notation "a * b" := (xnat_mul a b) : xnat_scope.

Lemma list_mul_loop_comm : ∀ al bl i n,
  list_mul_loop i n al bl = list_mul_loop i n bl al.
Proof.
intros.
revert al bl n.
induction i; intros; [ easy | simpl ].
f_equal; [ | apply IHi ].
rewrite summation_rtl.
apply summation_eq_compat.
intros j Hj.
rewrite Nat.mul_comm.
rewrite Nat.add_0_r; f_equal.
f_equal; lia.
Qed.

Lemma list_mul_comm : ∀ al bl, list_mul al bl = list_mul bl al.
Proof.
intros *.
unfold list_mul.
symmetry; rewrite Nat.add_comm; symmetry.
apply list_mul_loop_comm.
Qed.

Theorem xnat_mul_comm : ∀ a b, (a * b)%X = (b * a)%X.
Proof.
intros.
unfold xnat_mul; simpl.
now rewrite list_mul_comm.
Qed.

Theorem xnat_mul_comm' {r : radix} : ∀ a b, (a * b = b * a)%X.
Proof.
intros.
unfold xnat_mul; simpl.
now rewrite list_mul_comm.
Qed.

Lemma length_list_mul_loop : ∀ i n al bl,
  length (list_mul_loop i n al bl) = i.
Proof.
intros.
revert n.
now induction i; intros; [ | simpl; rewrite IHi ].
Qed.

Lemma list_mul_assoc : ∀ al bl cl,
  list_mul al (list_mul bl cl) = list_mul (list_mul al bl) cl.
Proof.
intros.
unfold list_mul.
do 2 rewrite length_list_mul_loop.
destruct bl as [| b1].
-simpl.
 rewrite Nat.add_0_r.
 destruct al as [| a1].
 +simpl.
  destruct cl as [| c1]; [ easy | simpl ].
  rewrite Nat.sub_0_r.
  destruct cl as [| c2]; [ easy | simpl ].
  rewrite Nat.sub_0_r.
  rewrite summation_only_one; simpl.
  destruct cl as [| c3].
  *simpl.
Compute (list_mul [] (list_mul [] [3; 4])).
Compute (list_mul (list_mul [] []) [3; 4]).
bbb.

intros.
unfold list_mul.
do 2 rewrite length_list_mul_loop.
remember (length bl + length cl - 1) as len_bc eqn:Hlen_bc.
remember (length al + length bl - 1) as len_ab eqn:Hlen_ab.
remember (length al + len_bc - 1) as len_a_bc eqn:Hlen_a_bc.
remember (len_ab + length cl - 1) as len_ab_c eqn:Hlen_ab_c.
symmetry in Hlen_bc, Hlen_a_bc, Hlen_ab, Hlen_ab_c.
destruct len_bc.
-simpl.
 rewrite Nat.add_0_r in Hlen_a_bc.
 destruct len_a_bc; simpl.
 +destruct len_ab; simpl.
  *destruct len_ab_c; [ easy | simpl in Hlen_ab_c; lia ].

  *simpl in Hlen_ab_c; rewrite Nat.sub_0_r in Hlen_ab_c.
   rewrite summation_only_one.
   destruct al as [| a1]; [ simpl in Hlen_ab; lia | ].
   simpl in Hlen_a_bc; rewrite Nat.sub_0_r in Hlen_a_bc.
   simpl in Hlen_ab; rewrite Nat.sub_0_r in Hlen_ab.
   rewrite Hlen_a_bc in Hlen_ab; simpl in Hlen_ab.
   apply List.length_zero_iff_nil in Hlen_a_bc; subst al.
   rewrite Hlen_ab in Hlen_bc; simpl in Hlen_bc.
   rewrite Nat.sub_0_r in Hlen_bc.
   apply Nat.eq_add_0 in Hlen_bc.
   destruct Hlen_bc as (H, Hlen_cl); subst len_ab.
   apply List.length_zero_iff_nil in Hlen_cl; subst cl.
   now simpl in Hlen_ab_c; subst len_ab_c.

 +
bbb.

symmetry.
rewrite summation_mul_comm.
rewrite <- summation_summation_mul_swap.
(* voir Power_series.v dans Puiseux *)
bbb.

Theorem xnat_mul_assoc : ∀ a b c, (a * (b * c))%X = ((a * b) * c)%X.
Proof.
intros.
unfold xnat_mul; simpl; f_equal.
apply list_mul_assoc.
Qed.
