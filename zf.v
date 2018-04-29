(* snake lemma & co *)

Require Import Utf8.
Require List.
Import List.ListNotations.
Open Scope list_scope.

Class ZF_base := mkZF_base
  { zfset : Type;
    zfvoid : zfset;
    zfmem : zfset → zfset → Prop;
    zfvoid_prop : ∀ x, ¬ (zfmem x zfvoid) }.

Notation "∅" := (zfvoid).
Notation "x '∈' S" := (zfmem x S) (at level 60).
Notation "x '∉' S" := (¬ zfmem x S) (at level 60).

Definition zfincl {zfb : ZF_base} A B := ∀ x, x ∈ A → x ∈ B.

Notation "A '⊂' B" := (zfincl A B) (at level 60).

Definition extensionality {zfb : ZF_base} := ∀ A B,
  A ⊂ B → B ⊂ A → A = B.

Definition zfunion_def {zfb : ZF_base} zfunion := ∀ A B x,
  x ∈ (zfunion A B) ↔ x ∈ A ∨ x ∈ B.

Definition zfinter_def {zfb : ZF_base} zfinter := ∀ A B x,
  x ∈ (zfinter A B) ↔ x ∈ A ∧ x ∈ B.

Class ZF := mkZF
  { zfb : ZF_base;
    zfextens : extensionality;
    zfunion : zfset → zfset → zfset;
    zfinter : zfset → zfset → zfset;
    zfunion_prop : zfunion_def zfunion;
    zfinter_prop : zfinter_def zfinter }.

Notation "A '⋃' B" := (zfunion A B) (at level 50).
Notation "A '∩' B" := (zfinter A B) (at level 40).

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

Notation "A '⋃' B" := (zfunion A B) (at level 50).
...

Record ZF := mkZF
  { zfb : ZF_base;
    zfvem : ∀ x, x ∉ ∅;
    zfext : ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B;
    zfpai : ∀ a b, ∃ c, ∀ x, x ∈ c ↔ x = a ∨ x = b;
    zfreu : ∀ a, ∃ c, ∀ x, x ∈ c ↔ (∃ y, y ∈ a ∧ x ∈ y);
    zfpar : ∀ a, ∃ c, ∀ x, x ∈ c ↔ x ⊂ a;
    zfinf : ∃ Y, ∅ ∈ Y ∧ ∀ y, y ∈ Y → y ⋃ {y} ∈ Y }.

Record ZF := mkZF
  { zfset : Type;
    zfvoi : zfset;
    zfmem : zfset → zfset → Prop;
    zfvem : ∀ x, ¬ zfmem x zfvoi;
    zfext : ∀ A B, (∀ x, zfmem x A ↔ zfmem x B) → A = B;
    zfpai : ∀ a b, ∃ c, ∀ x, zfmem x c ↔ x = a ∨ x = b;
    zfreu : ∀ a, ∃ c, ∀ x, zfmem x c ↔ (∃ y, zfmem y a ∧ zfmem x y);
    zfpar : ∀ a, ∃ c, ∀ x, zfmem x c ↔ (∀ y, zfmem y x → zfmem y a);
    zfinf : ∃ Y,
      zfmem zfvoi Y ∧
      ∀ y, zfmem y Y → zfmem (y ∪ {y}) Y }.

Print ZF.

Notation "x '∈' S" := (zfmem _ x S) (at level 60).

Record set1 T := mkset { setp : T → Prop }.
Arguments mkset [T] _.
Arguments setp [T] _ _.
Axiom ext1 : ∀ T (A B : set1 T), (∀ x, setp A x ↔ setp B x) → A = B.
Theorem pair1 {T} : ∀ (a b : T), ∃ c, ∀ x,
  setp c x ↔ x = a ∨ x = b.
Proof.
intros.
(* exists (mkset (λ d, d = (a, b))) *)
Abort.

Definition set T := mkZF (set1 T) (λ e s, setp s e) (ext1 T).

...


Record set T := mkset { setp : T → Prop }.
Arguments mkset [T] _.
Arguments setp [T] _ _.

Notation "x '∈' S" := (setp S x) (at level 60).
Definition set_incl {T} (A B : set T) := ∀ x, x ∈ A → x ∈ B.
Notation "A '⊆' B" := (set_incl A B) (at level 70).
Definition set_eq {T} (A B : set T) := A ⊆ B ∧ B ⊆ A.
Notation "A '≡' B" := (set_eq A B) (at level 70).

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
