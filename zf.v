(* snake lemma & co *)

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

Class ZF := mkZF
  { zfset : Type;
    zfmem : zfset → zfset → Prop
      where "x '∈' S" := (zfmem x S)
      and "x '∉' S" := (¬ zfmem x S);
    zfempty : zfset where "'∅'" := (zfempty);
    zfsingle : zfset → zfset where "'〈' x '〉'" := (zfsingle x);
    zfincl A B := ∀ x, x ∈ A → x ∈ B where "A '⊂' B" := (zfincl A B);
    zfunion : zfset → zfset → zfset where "A '⋃' B" := (zfunion A B);
    zfinter : zfset → zfset → zfset where "A '∩' B" := (zfinter A  B);
    zfextens : ∀ A B, A ⊂ B → B ⊂ A → A = B;
    zfpart : ∀ E, ∃ P, ∀ A, (A ∈ P ↔ A ⊂ E);
    zffound : ∀ A, A ≠ ∅ → ∃ B, B ∈ A ∧ B ∩ A = ∅;
    zfempty_prop : ∀ x, x ∉ ∅;
    zfsingle_prop : ∀ x y, y ∈ zfsingle x ↔ y = x;
    zfunion_prop : ∀ A B x, x ∈ (A ⋃ B) ↔ x ∈ A ∨ x ∈ B;
    zfinter_prop : ∀ A B x, x ∈ (A ∩ B) ↔ x ∈ A ∧ x ∈ B }.

Notation "'∅'" := (zfempty).
Notation "'〈' x '〉'" := (zfsingle x).
Notation "x '∈' S" := (zfmem x S).
Notation "x '∉' S" := (¬ zfmem x S).
Notation "A '⊂' B" := (zfincl A B).
Notation "A '⋃' B" := (zfunion A B).
Notation "A '∩' B" := (zfinter A B).

Theorem empty_is_subset {zf : ZF} : ∀ A, ∅ ⊂ A.
Proof.
intros A x Hx.
now apply zfempty_prop in Hx.
Qed.

Theorem empty_union_any {zf : ZF} : ∀ A, ∅ ⋃ A = A.
Proof.
intros.
apply zfextens; intros x H.
-apply zfunion_prop in H.
 destruct H as [H| ]; [ | easy ].
 now apply zfempty_prop in H.
-now apply zfunion_prop; right.
Qed.

Theorem empty_inter_any {zf : ZF} : ∀ A, ∅ ∩ A = ∅.
Proof.
intros.
apply zfextens; intros x H.
-now apply zfinter_prop in H.
-now apply zfempty_prop in H.
Qed.

Theorem subset_of_empty {zf : ZF} : ∀ A, A ⊂ ∅ → A = ∅.
Proof.
intros * HA.
apply zfextens; intros x H.
-now apply HA.
-now apply zfempty_prop in H.
Qed.

Theorem not_elem_itself {zf : ZF} : ∀ A, A ∉ A.
Proof.
intros A H1.
assert (H2 : zfsingle A ≠ ∅). {
  intros H2.
  assert (H3 : A ∈ zfsingle A) by now apply zfsingle_prop.
  rewrite H2 in H3.
  now apply zfempty_prop in H3.
}
specialize (zffound (zfsingle A) H2) as (B & H3 & H4).
apply zfsingle_prop in H3; subst B.
rewrite <- H4 in H2; apply H2.
apply zfextens; intros x H.
-apply zfinter_prop.
 split; [ | easy ].
 apply zfsingle_prop in H.
 now subst x.
-now apply zfinter_prop in H.
Qed.

Theorem union_comm {zf : ZF} : ∀ A B, A ⋃ B = B ⋃ A.
Proof.
intros.
apply zfextens; intros x H.
-apply zfunion_prop in H.
 apply zfunion_prop.
 now apply or_comm.
-apply zfunion_prop in H.
 apply zfunion_prop.
 now apply or_comm.
Qed.

Theorem union_half_assoc {zf : ZF} : ∀ A B C x,
  x ∈ (C ⋃ B) ⋃ A → x ∈ (A ⋃ B) ⋃ C.
Proof.
intros * H.
apply zfunion_prop in H.
apply zfunion_prop.
destruct H as [H| H].
-apply zfunion_prop in H.
 destruct H as [H| H]; [ now right | ].
 now left; apply zfunion_prop; right.
-now left; apply zfunion_prop; left.
Qed.

Theorem union_assoc {zf : ZF} : ∀ A B C, A ⋃ (B ⋃ C) = (A ⋃ B) ⋃ C.
Proof.
intros.
rewrite union_comm.
replace (B ⋃ C) with (C ⋃ B) by apply union_comm.
now apply zfextens; intros x H; apply union_half_assoc.
Qed.

Theorem inter_comm {zf : ZF} : ∀ A B, A ∩ B = B ∩ A.
Proof.
intros.
apply zfextens; intros x H.
-apply zfinter_prop in H.
 apply zfinter_prop.
 now apply and_comm.
-apply zfinter_prop in H.
 apply zfinter_prop.
 now apply and_comm.
Qed.

Theorem inter_half_assoc {zf : ZF} : ∀ A B C x,
  x ∈ (C ∩ B) ∩ A → x ∈ (A ∩ B) ∩ C.
Proof.
intros * H.
apply zfinter_prop in H.
apply zfinter_prop.
destruct H as (H1, H2).
apply zfinter_prop in H1.
destruct H1 as (H1, H3).
split; [ | easy ].
now apply zfinter_prop.
Qed.

Theorem inter_assoc {zf : ZF} : ∀ A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof.
intros.
rewrite inter_comm.
replace (B ∩ C) with (C ∩ B) by apply inter_comm.
now apply zfextens; intros x H; apply inter_half_assoc.
Qed.

Theorem inter_union_distr {zf : ZF} : ∀ A B C,
  A ∩ (B ⋃ C) = (A ∩ B) ⋃ (A ∩ C).
Proof.
intros.
apply zfextens; intros x H.
-apply zfinter_prop in H.
 destruct H as (H1, H2).
 apply zfunion_prop in H2.
 apply zfunion_prop.
 destruct H2 as [H2| H2].
 +now left; apply zfinter_prop.
 +now right; apply zfinter_prop.
-apply zfunion_prop in H.
 apply zfinter_prop.
 destruct H as [H| H]; apply zfinter_prop in H.
 +split; [ easy | ].
  now apply zfunion_prop; left.
 +split; [ easy | ].
  now apply zfunion_prop; right.
Qed.

Theorem union_inter_distr {zf : ZF} : ∀ A B C,
  A ⋃ (B ∩ C) = (A ⋃ B) ∩ (A ⋃ C).
Proof.
intros.
apply zfextens; intros x H.
-apply zfunion_prop in H.
 apply zfinter_prop.
 destruct H as [H| H].
 +now split; apply zfunion_prop; left.
 +apply zfinter_prop in H.
  now split; apply zfunion_prop; right.
-apply zfinter_prop in H.
 destruct H as (H1, H2).
 apply zfunion_prop in H1.
 apply zfunion_prop in H2.
 apply zfunion_prop.
 destruct H1 as [H1| H1]; [ now left | ].
 destruct H2 as [H2| H2]; [ now left | ].
 now right; apply zfinter_prop.
Qed.

...

Record category {U} := mkcat
  { ob : set U;
    mor : set (U * U);
    src : ∀ f, f ∈ mor → ∃ A, A ∈ ob ∧ fst f = A;
    dst : ∀ f, f ∈ mor → ∃ B, B ∈ ob ∧ snd f = B }.

...

Record element {T} (S : set T) :=
  { el_val : T; in_set : el_val ∈ S }.

Record group {T} := mkgr
  { gr_set : set T;
    gr_zero : element gr_set }.

Definition zero {T} (A : @group T) := el_val (gr_set A) (gr_zero _).

Record gmorph {T} A B := mkgm
  { gm_fun : T → T;
    gr_prop : ∀ x, x ∈ gr_set A → gm_fun x ∈ gr_set B }.

Definition Im {T} (A : group) (B : group) (f : T → T) :=
  mkset (λ b, b ∈ gr_set B ∧ ∃ a, a ∈ gr_set A ∧ f a = b).
Definition Ker {T} (A : group) (B : group) (f : T → T) :=
  mkset (λ a, a ∈ gr_set A ∧ f a = zero B).

Inductive sequence {T} (A : @group T) :=
  | Seq1 : sequence A
  | Seq2 : ∀ B (f : gmorph A B), sequence B → sequence A.

Fixpoint exact_sequence {T} (A : @group T) (S : sequence A) :=
  match S with
  | Seq1 _ => True
  | Seq2 _ f B S' =>
      match S' with
      | Seq1 _ => True
      | Seq2 _ g C S'' => Im A B f ≡ Ker A B g ∧ exact_sequence B S'
      end
  end.

Arguments Seq1 {T} G.
Arguments Seq2 {T} G f H.

Lemma snake {T} :
  ∀ A B C A' B' C' (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
     (a : A → A') (b : B → B') (c : C → C')
     (cz : C → False) (za' : False → A')
  (s : exact_sequence (Seq2 f (Seq2 g (Seq2 cz Seq1))))
  (s' : exact_sequence (Seq2 za' (Seq2 f' (Seq2 g' Seq1)))),
  False.
Proof.
intros.

Lemma snake :
  ∀ A B C A' B' C' (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
     (a : A → A') (b : B → B') (c : C → C')
     (cz : C → False) (za' : False → A')
  (s : exact_sequence (Seq2 f (Seq2 g (Seq2 cz Seq1))))
  (s' : exact_sequence (Seq2 za' (Seq2 f' (Seq2 g' Seq1)))),
  False.
Proof.
intros.

...
