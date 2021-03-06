(* ZF *)

Require Import Utf8.
Require List.
Import List.ListNotations.
Open Scope list_scope.

Reserved Notation "x '∈' S" (at level 60).
Reserved Notation "x '∉' S" (at level 60).
Reserved Notation "A '⊂' B" (at level 60).
Reserved Notation "A '⋃' B" (at level 50).
Reserved Notation "A '∩' B" (at level 40).
Reserved Notation "'∅'" (at level 0).
Reserved Notation "'〈' x '〉'" (at level 0).
Reserved Notation "'〈' x , y '〉'" (at level 0).

Class ZF := mkZF
  { zf_set : Type;
    zf_mem : zf_set → zf_set → Prop
      where "x '∈' S" := (zf_mem x S)
      and "x '∉' S" := (¬ zf_mem x S);
    zf_incl A B := ∀ x, x ∈ A → x ∈ B where "A '⊂' B" := (zf_incl A B);
    zf_extens : ∀ A B, A ⊂ B → B ⊂ A → A = B;
    zf_pair : zf_set → zf_set → zf_set where "'〈' x , y '〉'" := (zf_pair x y);
    zf_single : zf_set → zf_set where "'〈' x '〉'" := (zf_single x);
    zf_empty : zf_set where "'∅'" := (zf_empty);

    zf_union : zf_set → zf_set → zf_set where "A '⋃' B" := (zf_union A B);
    zf_inter : zf_set → zf_set → zf_set where "A '∩' B" := (zf_inter A  B);
    zf_part : ∀ a, ∃ c, ∀ x, x ∈ c → x ⊂ a;
    zf_inf : ∃ Y, ∅ ∈ Y ∧∀ y, y ∈ Y → y ⋃ 〈 y 〉 ∈ Y;
    zf_found : ∀ x, x ≠ ∅ → ∃ y, y ∈ x ∧ y ∩ x = ∅;
    zf_sch_repl : ∀ F, (∀ x y z, F x y ∧ F x z → y = z) → zf_set → zf_set;

    zf_pair_prop : ∀ a b x, x ∈ 〈 a, b 〉 ↔ x = a ∨ x = b;
    zf_single_prop : ∀ x y, y ∈ 〈 x 〉 ↔ y = x;
    zf_empty_prop : ∀ x, x ∉ ∅;
    zf_union_prop : ∀ A B x, x ∈ A ⋃ B ↔ x ∈ A ∨ x ∈ B;
    zf_inter_prop : ∀ A B x, x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B;
    zf_sch_repl_prop : ∀ F P A B,
      B = zf_sch_repl F P A ↔ (∀ y, y ∈ B ↔ ∃ x, x ∈ A ∧ F x y) }.

Notation "'∅'" := (zf_empty).
Notation "'〈' x '〉'" := (zf_single x).
Notation "'〈' x , y '〉'" := (zf_pair x y).
Notation "x '∈' S" := (zf_mem x S).
Notation "x '∉' S" := (¬ zf_mem x S).
Notation "A '⊂' B" := (zf_incl A B).
Notation "A '⋃' B" := (zf_union A B).
Notation "A '∩' B" := (zf_inter A B).

Theorem empty_is_subset {zf : ZF} : ∀ A, ∅ ⊂ A.
Proof.
intros A x Hx.
now apply zf_empty_prop in Hx.
Qed.

Theorem empty_union_any {zf : ZF} : ∀ A, ∅ ⋃ A = A.
Proof.
intros.
apply zf_extens; intros x H.
-apply zf_union_prop in H.
 destruct H as [H| ]; [ | easy ].
 now apply zf_empty_prop in H.
-now apply zf_union_prop; right.
Qed.

Theorem empty_inter_any {zf : ZF} : ∀ A, ∅ ∩ A = ∅.
Proof.
intros.
apply zf_extens; intros x H.
-now apply zf_inter_prop in H.
-now apply zf_empty_prop in H.
Qed.

Theorem subset_of_empty {zf : ZF} : ∀ A, A ⊂ ∅ → A = ∅.
Proof.
intros * HA.
apply zf_extens; intros x H.
-now apply HA.
-now apply zf_empty_prop in H.
Qed.

Theorem not_elem_itself {zf : ZF} : ∀ A, A ∉ A.
Proof.
intros A H1.
assert (H2 : zf_single A ≠ ∅). {
  intros H2.
  assert (H3 : A ∈ zf_single A) by now apply zf_single_prop.
  rewrite H2 in H3.
  now apply zf_empty_prop in H3.
}
specialize (zf_found (zf_single A) H2) as (B & H3 & H4).
apply zf_single_prop in H3.
rewrite H3 in H4.
clear H3.
rewrite <- H4 in H2.
apply H2.
apply zf_extens; intros x H.
-apply zf_inter_prop.
 split; [ | easy ].
 apply zf_single_prop in H.
 now subst x.
-now apply zf_inter_prop in H.
Qed.

Theorem pair_same {zf : ZF} : ∀ x, zf_pair x x = zf_single x.
Proof.
intros.
apply zf_extens; intros y H.
-apply zf_single_prop.
 apply zf_pair_prop in H.
 now destruct H.
-apply zf_pair_prop.
 apply zf_single_prop in H.
 now left.
Qed.

Theorem union_comm {zf : ZF} : ∀ A B, A ⋃ B = B ⋃ A.
Proof.
intros.
apply zf_extens; intros x H.
-apply zf_union_prop in H.
 apply zf_union_prop.
 now apply or_comm.
-apply zf_union_prop in H.
 apply zf_union_prop.
 now apply or_comm.
Qed.

Theorem union_half_assoc {zf : ZF} : ∀ A B C x,
  x ∈ (C ⋃ B) ⋃ A → x ∈ (A ⋃ B) ⋃ C.
Proof.
intros * H.
apply zf_union_prop in H.
apply zf_union_prop.
destruct H as [H| H].
-apply zf_union_prop in H.
 destruct H as [H| H]; [ now right | ].
 now left; apply zf_union_prop; right.
-now left; apply zf_union_prop; left.
Qed.

Theorem union_assoc {zf : ZF} : ∀ A B C, A ⋃ (B ⋃ C) = (A ⋃ B) ⋃ C.
Proof.
intros.
rewrite union_comm.
replace (B ⋃ C) with (C ⋃ B) by apply union_comm.
now apply zf_extens; intros x H; apply union_half_assoc.
Qed.

Theorem inter_comm {zf : ZF} : ∀ A B, A ∩ B = B ∩ A.
Proof.
intros.
apply zf_extens; intros x H.
-apply zf_inter_prop in H.
 apply zf_inter_prop.
 now apply and_comm.
-apply zf_inter_prop in H.
 apply zf_inter_prop.
 now apply and_comm.
Qed.

Theorem inter_half_assoc {zf : ZF} : ∀ A B C x,
  x ∈ (C ∩ B) ∩ A → x ∈ (A ∩ B) ∩ C.
Proof.
intros * H.
apply zf_inter_prop in H.
apply zf_inter_prop.
destruct H as (H1, H2).
apply zf_inter_prop in H1.
destruct H1 as (H1, H3).
split; [ | easy ].
now apply zf_inter_prop.
Qed.

Theorem inter_assoc {zf : ZF} : ∀ A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof.
intros.
rewrite inter_comm.
replace (B ∩ C) with (C ∩ B) by apply inter_comm.
now apply zf_extens; intros x H; apply inter_half_assoc.
Qed.

Theorem inter_union_distr {zf : ZF} : ∀ A B C,
  A ∩ (B ⋃ C) = (A ∩ B) ⋃ (A ∩ C).
Proof.
intros.
apply zf_extens; intros x H.
-apply zf_inter_prop in H.
 destruct H as (H1, H2).
 apply zf_union_prop in H2.
 apply zf_union_prop.
 destruct H2 as [H2| H2].
 +now left; apply zf_inter_prop.
 +now right; apply zf_inter_prop.
-apply zf_union_prop in H.
 apply zf_inter_prop.
 destruct H as [H| H]; apply zf_inter_prop in H.
 +split; [ easy | ].
  now apply zf_union_prop; left.
 +split; [ easy | ].
  now apply zf_union_prop; right.
Qed.

Theorem union_inter_distr {zf : ZF} : ∀ A B C,
  A ⋃ (B ∩ C) = (A ⋃ B) ∩ (A ⋃ C).
Proof.
intros.
apply zf_extens; intros x H.
-apply zf_union_prop in H.
 apply zf_inter_prop.
 destruct H as [H| H].
 +now split; apply zf_union_prop; left.
 +apply zf_inter_prop in H.
  now split; apply zf_union_prop; right.
-apply zf_inter_prop in H.
 destruct H as (H1, H2).
 apply zf_union_prop in H1.
 apply zf_union_prop in H2.
 apply zf_union_prop.
 destruct H1 as [H1| H1]; [ now left | ].
 destruct H2 as [H2| H2]; [ now left | ].
 now right; apply zf_inter_prop.
Qed.

(* *)

Definition zf_ord_pair {zf : ZF} a b := zf_pair (zf_single a) (zf_pair a b).

(* mouais, chais pas si c'est ça *)
Definition zf_function {zf : ZF} A B F P :=
(*
  let '(F, P) := FP in
*)
  zf_ord_pair (zf_ord_pair A B) (zf_sch_repl F P A).

Check zf_function.

(*
Record category {zf : ZF} := mkcat
  { ca_obj : zf_set;
    ca_arr : zf_set;
    ca_comp : zf_set → zf_set → zf_set;
    ca_arr_prop : ∀ a, a ∈ ca_arr →
      ∃ o₁ o₂, o₁ ∈ ca_obj ∧ o₂ = ca_obj ∧ a = zf_ord_pair o₁ o₂;
    ca_comp_prop : ∀ a₁ a₂, a₁ ∈ ca_arr → a₂ ∈ ca_arr →
      ∃ o₁ o₂ o₃, o₁ ∈ ca_obj ∧ o₂ ∈ ca_obj ∧ o₃ ∈ ca_obj ∧
      a₁ = zf_ord_pair o₁ o₂ ∧ a₂ = zf_ord_pair o₂ o₃ ∧
      ca_comp a₁ a₂ = zf_ord_pair o₁ o₃ }.

Definition cat_Set :=
  {| ca_obj := ... ???

Definition cat_Mat := ...
...
*)
