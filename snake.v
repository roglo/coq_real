(* snake lemma & co *)

Require Import Utf8.

Record is_abelian_group {T} (gr_zero : T) gr_op gr_in :=
  { ig_zero : gr_in gr_zero;
    ig_clos : ∀ x y, gr_in x → gr_in y → gr_in (gr_op x y);
    ig_lid : ∀ x, gr_in x → gr_op gr_zero x = x;
    ig_rid : ∀ x, gr_in x → gr_op x gr_zero = x;
    ig_assoc : ∀ x y z, gr_in x → gr_in y → gr_in z →
      gr_op (gr_op x y) z = gr_op x (gr_op y z);
    ig_comm : ∀ x y, gr_in x → gr_in y →
      gr_op x y = gr_op y x }.

Record Group :=
  { gr_set : Type;
    gr_in : gr_set → Prop;
    gr_zero : gr_set;
    gr_op : gr_set → gr_set → gr_set;
    gr_prop : is_abelian_group gr_zero gr_op gr_in }.

Arguments gr_op [_].

Notation "x '∈' S" := (gr_in S x) (at level 60).

Record is_homgr A B H_app :=
  { ih_zero : H_app (gr_zero A) = gr_zero B;
    ih_inco : ∀ x, gr_in B (H_app x);
    ih_lin : ∀ x y, H_app (gr_op x y) = gr_op (H_app x) (H_app y) }.

Record HomGr (A B : Group) :=
  { H_app : gr_set A → gr_set B;
    H_prop : is_homgr A B H_app }.

Arguments H_app [A] [B].

Inductive Gr0_set := G0 : Gr0_set.

Theorem Gr0_prop : is_abelian_group G0 (λ _ _, G0) (λ _, True).
Proof.
split; [ easy | easy | | | easy | easy ].
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
-destruct f as (fa & fih); simpl in fih.
 destruct g as (ga & gih); simpl in gih.
 simpl.
 destruct x.
 destruct fih, gih; simpl in *.
 now rewrite ih_zero0, ih_zero1.
-destruct f as (fa & fih); simpl in fih.
 destruct g as (ga & gih); simpl in gih.
 simpl.
 now destruct (fa x), (ga x).
Qed.

Theorem Im_is_abelian_group {G H} (f : HomGr G H) :
  is_abelian_group (gr_zero H) (@gr_op H) (λ b, ∃ a, H_app f a = b).
Proof.
intros.
split.
-exists (gr_zero G).
 apply f.
-intros y y' (x & Hx) (x' & Hx').
 subst y y'.
 destruct G, H; simpl in *.
 destruct f; simpl in *.
 exists (gr_op0 x x').
 apply H_prop0.
-intros y (x & Hx); subst y.
 destruct G, H, f; simpl in *.
 apply gr_prop1.
 apply H_prop0.
-intros y (x & Hx); subst y.
 destruct G, H, f; simpl in *.
 apply gr_prop1.
 apply H_prop0.
-intros y y' y'' (x & Hx) (x' & Hx') (x'' & Hx'').
 rewrite <- Hx, <- Hx', <- Hx''.
 apply H; apply f.
-intros y y' (x & Hx) (x' & Hx').
 apply H.
 +rewrite <- Hx; apply f.
 +rewrite <- Hx'; apply f.
Qed.

Theorem Ker_is_abelian_group {G H} : ∀ (f : HomGr G H),
  is_abelian_group (gr_zero G) (gr_op (g:=G))
    (λ a, gr_in G a ∧ H_app f a = gr_zero H).
Proof.
intros.
split.
-split; [ apply G | apply f ].
-intros x x' (Hx, Hfx) (Hx', Hfx').
 split; [ now apply G | ].
 destruct f as (appf, fp); simpl in *.
 destruct fp as (fz, fin, flin); simpl in *.
 rewrite flin, Hfx, Hfx'.
 apply H, H.
-intros x (Hx, Hfx).
 now apply G.
-intros x (Hx, Hfx).
 now apply G.
-intros x x' x'' (Hx & Hfx) (Hx' & Hfx') (Hx'' & Hfx'').
 now apply G.
-intros x x' (Hx, Hfx) (Hx', Hfx').
 now apply G.
Qed.

Definition Im {G H : Group} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero H;
     gr_op := @gr_op H;
     gr_in := λ b, ∃ a, H_app f a = b;
     gr_prop := Im_is_abelian_group f |}.

Definition Ker {G H : Group} (f : HomGr G H) :=
  {| gr_set := gr_set G;
     gr_zero := gr_zero G;
     gr_op := @gr_op G;
     gr_in := λ a, gr_in G a ∧ H_app f a = gr_zero H;
     gr_prop := Ker_is_abelian_group f |}.

Theorem coKer_is_abelian_group {G H} : ∀ (f : HomGr G H),
  is_abelian_group (gr_zero H) (gr_op (g:=H))
    (λ x, gr_in H x ∧ ∃ y, gr_in H y ∧ gr_in (Im f) (gr_op x y)).
Proof.
intros.
split.
-split; [ apply H | ].
 exists (gr_zero H).
 split; [ apply H | ].
 exists (gr_zero G).
 destruct f as (appf, fp); simpl in *.
 destruct fp as (fz, fin, flin); simpl in *.
 rewrite fz.
 symmetry; apply H, H.
-intros y y' (Hy & z & Hz & x & Hx) (Hy' & z' & Hz' & x' & Hx').
 split; [ now apply H | ].
 exists (gr_op z z').
 split; [ now apply H | ].
 exists (gr_op x x').
 destruct f as (appf, fp); simpl in *.
 destruct fp as (fz, fin, flin); simpl in *.
 rewrite flin, Hx, Hx'.
 destruct H as (Hs, inH, zH, Hop, Hp); simpl in *.
 replace (Hop y z) with (Hop z y) by now apply Hp.
 remember (Hop y' z') as t eqn:Ht.
 replace (Hop (Hop z y) t) with (Hop z (Hop y t)).
 2: now subst t; symmetry; apply Hp; [ | | apply Hp ].
 subst t.
 replace (Hop y (Hop y' z')) with (Hop (Hop y y') z') by now apply Hp.
 remember (Hop y y') as t eqn:Ht.
 replace (Hop z (Hop t z')) with (Hop (Hop t z') z).
 2: subst t; symmetry; apply Hp; [ easy | ].
 2: now apply Hp; [ apply Hp | ].
 replace (Hop (Hop t z') z) with (Hop t (Hop z' z)).
 2: now subst t; symmetry; apply Hp; [ apply Hp | | ].
 now replace (Hop z' z) with (Hop z z'); [ | apply Hp ].
-now intros; apply H.
-now intros; apply H.
-now intros; apply H.
-now intros; apply H.
Qed.

Definition coKer {G H : Group} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero H;
     gr_op := @gr_op H;
     gr_in := λ x, gr_in H x ∧ ∃ y, gr_in H y ∧ gr_in (Im f) (gr_op x y);
     gr_prop := coKer_is_abelian_group f |}.

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

(*      f
    A------>B
    |       |
   g|       |h
    |       |
    v       v
    C------>D
        k
*)
Definition diagram_commutes {A B C D}
     (f : HomGr A B) (g : HomGr A C) (h : HomGr B D) (k : HomGr C D) :=
  ∀ x, H_app h (H_app f x) = H_app k (H_app g x).

Lemma snake :
  ∀ (A B C A' B' C' : Group)
     (f : HomGr A B) (g : HomGr B C)
     (f' : HomGr A' B') (g' : HomGr B' C')
     (a : HomGr A A') (b : HomGr B B') (c : HomGr C C')
     (cz : HomGr C Gr0) (za' : HomGr Gr0 A')
     (fk : HomGr (Ker a) (Ker b)) (gk : HomGr (Ker b) (Ker c))
     (d : HomGr (Ker c) (coKer a))
     (fk' : HomGr (coKer a) (coKer b)) (gk' : HomGr (coKer b) (coKer c))
     (fk_prop : ∀ x, gr_in (Ker a) x → H_app fk x = H_app f x)
     (gk_prop : ∀ x, gr_in (Ker b) x → H_app gk x = H_app g x)
     (fk'_prop : ∀ x, gr_in (coKer a) x → H_app fk' x = H_app f' x)
     (gk'_prop : ∀ x, gr_in (coKer b) x → H_app gk' x = H_app g' x),
  diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → exact_sequence (Seq2 f (Seq2 g (Seq2 cz Seq1)))
  → exact_sequence (Seq2 za' (Seq2 f' (Seq2 g' Seq1)))
  → exact_sequence (Seq2 fk (Seq2 gk (Seq2 d (Seq2 fk' (Seq2 gk' Seq1))))).
Proof.
intros * fk_prop gk_prop fk'_prop gk'_prop.
intros Hcff' Hcgg' s s'.
split.
-intros y.
 split; intros (x & Hx); simpl in x.
 +subst y.
  split; [ apply fk | simpl ].
  unfold diagram_commutes in Hcff', Hcgg'.
...
  destruct fk as (app_fk, fk_p); simpl in fk_prop; simpl.
  destruct fk_p as (fk_z, fk_in, fk_lin).
  simpl in H1.
  simpl in fk_in.

  destruct gk as (app_gk, gk_p); simpl in gk_prop; simpl.
  destruct gk_p as (gk_z, gk_in, gk_lin).
  simpl in gk_in.
simpl in gk_lin.
...
  specialize (gk_prop (H_app fk x)) as H2.
  assert (H3 : H_app fk x ∈ B ∧ H_app b (H_app fk x) = gr_zero B'). {
    apply fk.
  }
  specialize (H2 H3); rewrite H2.
...
  destruct s as (s1, s).
  simpl in s1.
  assert (H1 : x ∈ Ker a). {
    simpl.
...
  }
  rewrite fk_prop.
...
  specialize (s1 (H_app fk x)) as (s1, s'1).
destruct fk as (app_fk, fk_p); simpl in fk_prop; simpl.
simpl in s1, s'1.
...
  assert (H1 : ∃ x', H_app f x' = H_app fk x). {
    exists x.
    destruct fk as (app_fk, fk_p); simpl in fk_prop; simpl.
    symmetry; apply fk_prop.
    split.
Search x.
...

apply fk.
{

  assert (H1 : H_app fk x = gr_zero B). {
    destruct fk as (app_fk, fk_p); simpl in fk_prop; simpl.
    destruct fk_p as (fz, fin, flin).
simpl in fz.
simpl in flin.
simpl in fin.
simpl in fk_prop.
...
