(* snake lemma & co *)

Require Import Utf8.

Record is_group {T} (gr_zero : T) (gr_op : T → T → T)  (gr_in : T → Prop) :=
  { ig_zero : gr_in gr_zero;
    ig_clos : ∀ x y, gr_in x → gr_in y → gr_in (gr_op x y);
    ig_lid : ∀ x, gr_in x → gr_op gr_zero x = x;
    ig_rid : ∀ x, gr_in x → gr_op x gr_zero = x }.

Record Group :=
  { gr_set : Type;
    gr_in : gr_set → Prop;
    gr_zero : gr_set;
    gr_op : gr_set → gr_set → gr_set;
    gr_prop : is_group gr_zero gr_op gr_in }.

Notation "x '∈' G" := (gr_in G x) (at level 60).
Notation "x '∉' G" := (¬ gr_in G x) (at level 60).

Record HomGr (A B : Group) :=
  { H_app : gr_set A → gr_set B;
    H_prop :
      H_app (gr_zero A) = gr_zero B ∧
      (∀ x, gr_in B (H_app x)) ∧
      (∀ x y, H_app (gr_op A x y) = gr_op B (H_app x) (H_app y)) }.

Arguments H_app [A] [B].

Inductive Gr0_set := G0 : Gr0_set.

Theorem Gr0_prop : is_group G0 (λ _ _ : Gr0_set, G0) (λ _ : Gr0_set, True).
Proof.
split; [ easy | easy | | ].
-now intros x; destruct x.
-now intros x; destruct x.
Qed.

Definition Gr0 :=
   {| gr_set := Gr0_set;
      gr_zero := G0;
      gr_op := λ _ _, G0;
      gr_in := λ _, True;
      gr_prop := Gr0_prop |}.

Definition is_initial (G : Group) :=
  ∀ H (f g : HomGr G H) (x : gr_set G), H_app f x = H_app g x.
Definition is_final (G : Group) :=
  ∀ H (f g : HomGr H G) (x : gr_set H), H_app f x = H_app g x.
Definition is_null (G : Group) := is_initial G ∧ is_final G.

Theorem is_null_Gr0 : is_null Gr0.
Proof.
split; intros H f g x.
-destruct f as (fa & fp1 & fp2); simpl in fp1, fp2.
 destruct g as (ga & gp1 & gp2); simpl in gp1, gp2.
 simpl.
 destruct x.
 now rewrite fp1, gp1.
-destruct f as (fa, fp); simpl in fp.
 destruct g as (ga, gp); simpl in gp.
 simpl.
 now destruct (fa x), (ga x).
Qed.

Theorem Im_is_group {G H} (f : HomGr G H) :
  is_group (gr_zero H) (gr_op H) (λ b, ∃ a, H_app f a = b).
Proof.
intros.
split.
-exists (gr_zero G).
 apply f.
-intros y y' (x & Hx) (x' & Hx').
 subst y y'.
 destruct G, H; simpl in *.
 destruct f; simpl in *.
...
 unfold is_group in *.
 exists (gr_op0 x x').
 apply H_prop0.
-intros y (x & Hx); subst y.
 destruct G, H, f; simpl in *.
 unfold is_group in *.
 apply gr_prop1.
 apply H_prop0.
-intros y (x & Hx); subst y.
 destruct G, H, f; simpl in *.
 unfold is_group in *.
 apply gr_prop1.
 apply H_prop0.
Qed.

Theorem Ker_is_group {G H} (f : HomGr G H) :
  is_group (gr_set G) (gr_zero G) (gr_op G) (λ a, H_app f a = gr_zero H).
Proof.
intros.
split; [ | split ].
-intros x x' Hx Hx'.
 destruct G, H, f; simpl in *.
 unfold is_group in *.
 rewrite H_prop0.
...
 replace gr_zero1 with (gr_op1 gr_zero1 gr_zero1).
 +idtac.
...

 +apply gr_prop1.
  replace gr_zero1 with (H_app0 gr_zero0) by apply H_prop0.
  apply H_prop0.
...

 subst y y'.
 destruct G, H; simpl in *.
 destruct f; simpl in *.
 unfold is_group in *.
 exists (gr_op0 x x').
 apply H_prop0.
-intros y (x & Hx); subst y.
 destruct G, H, f; simpl in *.
 unfold is_group in *.
 apply gr_prop1.
 apply H_prop0.
-intros y (x & Hx); subst y.
 destruct G, H, f; simpl in *.
 unfold is_group in *.
 apply gr_prop1.
 apply H_prop0.
Qed.

Definition Im {G H : Group} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero H;
     gr_op := gr_op H;
     gr_in := λ b, ∃ a, H_app f a = b;
     gr_prop := Im_is_group f |}.

Definition Ker {G H : Group} (f : HomGr G H) :=
  {| gr_set := gr_set G;
     gr_zero := gr_zero G;
     gr_op := gr_op G;
     gr_in := λ a : gr_set G, H_app f a = gr_zero H;
     gr_prop := Ker_is_group f |}.

Definition coKer {G H : Group} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero H;
     gr_in := λ a : gr_set H, ∃ a' : gr_set H, gr_in (Im f) (gr_op x y) |}.

Inductive sequence {A : Group} :=
  | Seq1 : sequence
  | Seq2 : ∀ {B} (f : HomGr A B), @sequence B → sequence.

Fixpoint exact_sequence {A : Group} (S : sequence) :=
  match S with
  | Seq1 => True
  | Seq2 f S' =>
      match S' with
      | Seq1 => True
      | Seq2 g S'' =>
          (∀ a, gr_in (Im f) a ↔ gr_in (Ker g) a) ∧
          exact_sequence S'
      end
  end.

Lemma snake :
  ∀ (A B C A' B' C' : Group) (f : HomGr A B) (g : HomGr B C)
     (f' : HomGr A' B') (g' : HomGr B' C')
     (a : HomGr A A') (b : HomGr B B') (c : HomGr C C')
     (cz : HomGr C Gr0) (za' : HomGr Gr0 A')
     (fk : HomGr (Ker a) (Ker b)) (gk : HomGr (Ker b) (Ker c))
     (d : HomGr (Ker c) (coKer a))
     (s : exact_sequence (Seq2 f (Seq2 g (Seq2 cz Seq1))))
     (s' : exact_sequence (Seq2 za' (Seq2 f' (Seq2 g' Seq1))))
     (fk_prop : ∀ x, gr_in (Ker a) x → H_app fk x = H_app f x)
     (gk_prop : ∀ x, gr_in (Ker b) x → H_app gk x = H_app g x),
  exact_sequence (Seq2 fk (Seq2 gk Seq1)).
Proof.
intros.
...
