(* Natural numbers in any radix; second version; without proofs *)
(* Can be regarded as polynomials with natural number coefficients. *)

(* Implemented using lists of nat. *)
(* No constraints of digits having to be less than radix;
   to build a number whose digits are less than radix, use normalization
   by the function xnat_norm *)

Require Import Utf8 Arith Psatz Misc.
Require List.
Import List.ListNotations.
Open Scope list_scope.

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

Fixpoint xnatv_add a b :=
  match a with
  | [] => b
  | a₀ :: al =>
      match b with
      | [] => a
      | b₀ :: bl => a₀ + b₀ :: xnatv_add al bl
      end
  end.

Definition xnat_add {r : radix} a b :=
  xn (xnatv_add (xnatv a) (xnatv b)).

Definition xnat_0 {r : radix} := xn [].

Delimit Scope xnat_scope with X.
Notation "a + b" := (xnat_add a b) : xnat_scope.
Notation "a = b" := (nat_of_xnat a = nat_of_xnat b) : xnat_scope.
Notation "0" := (xnat_0) : xnat_scope.

Lemma xnatv_add_comm {r : radix} : ∀ al bl,
  xnatv_add al bl = xnatv_add bl al.
Proof.
intros *.
revert bl.
induction al as [| a1]; intros; [ now destruct bl | simpl ].
destruct bl as [| b1]; [ easy | simpl ].
now rewrite Nat.add_comm, IHal.
Qed.

Theorem xnat_add_comm {r : radix} : ∀ a b, (a + b = b + a)%X.
Proof.
intros.
unfold xnat_add; simpl.
now rewrite xnatv_add_comm.
Qed.

Theorem xnat_add_0_l {r : radix} : ∀ a, (0 + a = a)%X.
Proof. easy. Qed.

Lemma nat_of_list_add_assoc {r : radix} : rad ≠ 0 → ∀ al bl cl,
  nat_of_list 0 (xnatv_add al (xnatv_add bl cl)) =
  nat_of_list 0 (xnatv_add (xnatv_add al bl) cl).
Proof.
intros Hr *.
revert al cl.
induction bl as [| b1]; intros; simpl.
-now replace (xnatv_add al []) with (xnatv_add [] al) by apply xnatv_add_comm.

-destruct cl as [| c1]; [ now destruct al | simpl ].
 destruct al as [| a1]; [ easy | simpl ].
 rewrite IHbl; ring.
Qed.

Theorem xnat_add_assoc {r : radix} : rad ≠ 0 → ∀ a b c,
  (a + (b + c) = (a + b) + c)%X.
Proof.
intros Hr *.
unfold xnat_add, nat_of_xnat; simpl.
now apply nat_of_list_add_assoc.
Qed.

(* Compatiblity addition with equality *)

Lemma nat_of_list_xnatv_add_distr {r : radix} : 1 < rad → ∀ al bl,
  nat_of_list 0 (xnatv_add al bl) = nat_of_list 0 al + nat_of_list 0 bl.
Proof.
intros Hr *.
revert bl.
induction al as [| a1]; intros; [ easy | simpl ].
destruct bl as [| b1]; [ now rewrite Nat.add_0_r | ].
simpl; rewrite IHal; lia.
Qed.

Lemma nat_of_list_add_eq_compat {r : radix} : 1 < rad → ∀ al bl cl,
  nat_of_list 0 al = nat_of_list 0 bl
  → nat_of_list 0 (xnatv_add al cl) = nat_of_list 0 (xnatv_add bl cl).
Proof.
intros Hr.
assert (Hrz : rad ≠ 0) by lia.
intros * Hab.
rewrite nat_of_list_xnatv_add_distr; [ | easy ].
rewrite nat_of_list_xnatv_add_distr; [ | easy ].
now rewrite Hab.
Qed.

Theorem xnatv_add_eq_compat {r : radix} : 1 < rad → ∀ a b c,
  (a = b)%X → (a + c = b + c)%X.
Proof.
intros Hr * Hab.
unfold nat_of_xnat in Hab.
unfold nat_of_xnat.
unfold xnat_add; simpl.
now apply nat_of_list_add_eq_compat.
Qed.

(* Multiplication *)

(* hou la la: comment je fais, là ? *)
bbb.

Fixpoint xnatv_mul a b :=
  match a with
  | [] => b
  | a₀ :: al =>
      match b with
      | [] => a
      | b₀ :: bl => a₀ + b₀ :: xnatv_add al bl
      end
  end.

bbb.

Definition xnat_mul {r : radix} a b :=
  xn (xnatv_mul (xnatv a) (xnatv b)).
