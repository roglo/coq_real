(* Snake lemma *)

Require Import Utf8.

Record is_abelian_group {T} (in_gr : T → Prop) gr_zero gr_add :=
  { ig_zero : in_gr gr_zero;
    ig_clos : ∀ x y, in_gr x → in_gr y → in_gr (gr_add x y);
    ig_lid : ∀ x, in_gr x → gr_add gr_zero x = x;
    ig_rid : ∀ x, in_gr x → gr_add x gr_zero = x;
    ig_assoc : ∀ x y z, in_gr x → in_gr y → in_gr z →
      gr_add (gr_add x y) z = gr_add x (gr_add y z);
    ig_comm : ∀ x y, in_gr x → in_gr y →
      gr_add x y = gr_add y x }.

Record Group :=
  { gr_set : Type;
    gr_in : gr_set → Prop;
    gr_zero : gr_set;
    gr_add : gr_set → gr_set → gr_set;
    gr_prop : is_abelian_group gr_in gr_zero gr_add }.

Arguments gr_add [_].

Notation "x '∈' S" := (gr_in S x) (at level 60).
(*
Notation "x '⊕' y" := (gr_add x y) (at level 50).
*)

Record is_homgr A B H_app :=
  { ih_zero : H_app (gr_zero A) = gr_zero B;
    ih_inco : ∀ x, x ∈ A → H_app x ∈ B;
    ih_lin : ∀ x y, x ∈ A → y ∈ A →
      H_app (gr_add x y) = gr_add (H_app x) (H_app y) }.

Record HomGr (A B : Group) :=
  { H_app : gr_set A → gr_set B;
    H_prop : is_homgr A B H_app }.

Arguments H_app [A] [B].

Inductive Gr0_set := G0 : Gr0_set.

Theorem Gr0_prop : is_abelian_group (λ _, True) G0 (λ _ _, G0).
Proof.
split; [ easy | easy | | | easy | easy ].
-now intros x; destruct x.
-now intros x; destruct x.
Qed.

Definition Gr0 :=
   {| gr_set := Gr0_set;
      gr_zero := G0;
      gr_add := λ _ _, G0;
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
  is_abelian_group (λ b, ∃ a, a ∈ G ∧ H_app f a = b) (gr_zero H) (@gr_add H).
Proof.
intros.
split.
-exists (gr_zero G).
 split; [ apply G | apply f ].
-intros y y' (x & Hxg & Hx) (x' & Hx'g & Hx').
 subst y y'.
 destruct G as (gs, gi, gz, go, gp).
 destruct gp as (gzi, gc, gl, gr, ga, gco).
 destruct H as (hs, hi, hz, ho, hp).
 destruct f as (appf, fp).
 destruct fp as (fz, fin, flin); simpl in *.
 exists (go x x').
 split; [ now apply gc | now apply flin ].
-intros y (x & Hxg & Hx); subst y.
 now apply H, f.
-intros y (x & Hxg & Hx); subst y.
 now apply H, f.
-intros y y' y'' (x & Hgx & Hx) (x' & Hgx' & Hx') (x'' & Hgx'' & Hx'').
 rewrite <- Hx, <- Hx', <- Hx''.
 now apply H; apply f.
-intros y y' (x & Hgx & Hx) (x' & Hgx' & Hx').
 apply H.
 +now rewrite <- Hx; apply f.
 +now rewrite <- Hx'; apply f.
Qed.

Theorem Ker_is_abelian_group {G H} : ∀ (f : HomGr G H),
  is_abelian_group (λ x, x ∈ G ∧ H_app f x = gr_zero H)
    (gr_zero G) (gr_add (g:=G)).
Proof.
intros.
split.
-split; [ apply G | apply f ].
-intros x x' (Hx, Hfx) (Hx', Hfx').
 split; [ now apply G | ].
 destruct f as (appf, fp); simpl in *.
 destruct fp as (fz, fin, flin); simpl in *.
 rewrite flin; [ | easy | easy ].
 rewrite Hfx, Hfx'.
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
     gr_add := @gr_add H;
     gr_in := λ b, ∃ a, a ∈ G ∧ H_app f a = b;
     gr_prop := Im_is_abelian_group f |}.

Definition Ker {G H : Group} (f : HomGr G H) :=
  {| gr_set := gr_set G;
     gr_zero := gr_zero G;
     gr_add := @gr_add G;
     gr_in := λ a, a ∈ G ∧ H_app f a = gr_zero H;
     gr_prop := Ker_is_abelian_group f |}.

Theorem coKer_is_abelian_group {G H} : ∀ (f : HomGr G H),
  is_abelian_group (λ x, x ∈ H ∧ ∃ y, y ∈ H ∧ gr_add x y ∈ Im f)
    (gr_zero H) (gr_add (g:=H)).
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
 split; [ apply G | ].
 symmetry; apply H, H.
-intros y y' (Hy & z & Hz & x & Hgx & Hx) (Hy' & z' & Hz' & x' & Hgx' & Hx').
 split; [ now apply H | ].
 exists (gr_add z z').
 split; [ now apply H | ].
 exists (gr_add x x').
 destruct f as (appf, fp); simpl in *.
 destruct fp as (fz, fin, flin); simpl in *.
 rewrite flin; [ | easy | easy ].
 rewrite Hx, Hx'.
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
 split; [ now apply G | ].
 now replace (Hop z' z) with (Hop z z'); [ | apply Hp ].
-now intros; apply H.
-now intros; apply H.
-now intros; apply H.
-now intros; apply H.
Qed.

Definition coKer {G H : Group} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero H;
     gr_add := @gr_add H;
     gr_in := λ x, x ∈ H ∧ ∃ y, y ∈ H ∧ gr_add x y ∈ Im f;
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
      | Seq2 g S'' => (∀ a, a ∈ Im f ↔ a ∈ Ker g) ∧ exact_sequence S'
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

Theorem is_homgr_Ker_Ker {A B A' B'} :
  ∀ (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  diagram_commutes f a b f'
  → is_homgr (Ker a) (Ker b) (H_app f).
Proof.
intros * Hc.
split; [ apply f | | ].
-intros x Hx.
 assert (H : H_app a x = gr_zero A') by apply Hx.
 apply (f_equal (H_app f')) in H.
 rewrite <- Hc in H.
 split; [ now apply f; simpl in Hx | ].
 rewrite H; apply f'.
-intros x x' Hx Hx'; simpl in Hx, Hx'.
 now apply f.
Qed.

Theorem is_homgr_coKer_coKer {A B A' B'} :
  ∀ (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  diagram_commutes f a b f'
  → is_homgr (coKer a) (coKer b) (H_app f').
Proof.
intros * Hc.
split; [ apply f' | | ].
-intros x Hx.
 split; [ apply f', Hx | ].
 destruct Hx as (Hxa & y & Hy & z & Hz & Hxy).
 exists (H_app f' y).
 split; [ now apply f' | ].
 exists (H_app f z).
 split; [ now apply f | ].
 rewrite Hc, Hxy.
 now apply f'.
-intros x y Hx Hy; simpl in Hx, Hy.
 now apply f'.
Qed.

Definition HomGr_Ker_ker {A B A' B'}
    (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B')
    (Hc : diagram_commutes f a b f') :=
  {| H_app (x : gr_set (Ker a)) := H_app f x : gr_set (Ker b);
     H_prop := is_homgr_Ker_Ker f f' a b Hc |}.

Definition HomGr_coKer_coker {A B A' B'}
    (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B')
    (Hc : diagram_commutes f a b f') :=
  {| H_app (x : gr_set (coKer a)) := H_app f' x : gr_set (coKer b);
     H_prop := is_homgr_coKer_coKer f f' a b Hc |}.

Lemma snake :
  ∀ (A B C A' B' C' : Group)
     (f : HomGr A B) (g : HomGr B C)
     (f' : HomGr A' B') (g' : HomGr B' C')
     (a : HomGr A A') (b : HomGr B B') (c : HomGr C C')
     (cz : HomGr C Gr0) (za' : HomGr Gr0 A'),
  diagram_commutes f a b f'
  → diagram_commutes g b c g'
  → exact_sequence (Seq2 f (Seq2 g (Seq2 cz Seq1)))
  → exact_sequence (Seq2 za' (Seq2 f' (Seq2 g' Seq1)))
  → ∃ (fk : HomGr (Ker a) (Ker b)) (gk : HomGr (Ker b) (Ker c))
        (fk' : HomGr (coKer a) (coKer b)) (gk' : HomGr (coKer b) (coKer c)),
     ∃ (d : HomGr (Ker c) (coKer a)),
        exact_sequence (Seq2 fk (Seq2 gk (Seq2 d (Seq2 fk' (Seq2 gk' Seq1))))).
Proof.
intros *.
intros Hcff' Hcgg' s s'.
exists (HomGr_Ker_ker f f' a b Hcff').
exists (HomGr_Ker_ker g g' b c Hcgg').
exists (HomGr_coKer_coker f f' a b Hcff').
exists (HomGr_coKer_coker g g' b c Hcgg').
destruct s as (sf & sg & _).
destruct s' as (sf' & sg' & _).
enough (d : HomGr (Ker c) (coKer a)).
exists d.
simpl.
split; [ | split ].
-intros y.
 split.
 +intros (x & (Hx & Hax) & Hxy).
  split; [ split | ].
  *now rewrite <- Hxy; apply f.
  *rewrite <- Hxy, Hcff', Hax; apply f'.
  *apply sf; rewrite <- Hxy.
   exists x; easy.
 +intros ((Hy & Hby) & Hgy).
  assert (H : y ∈ Im f) by now apply sf; split.
  destruct H as (x & Hx & Hxy).
  exists x; split; [ | easy ].
  split; [ easy | ].
  rewrite <- Hxy, Hcff' in Hby.
  specialize (sf' (H_app a x)) as (H1, H2).
  assert (H3 : H_app a x ∈ Ker f') by now split; [ apply a | ].
  specialize (H2 H3).
  destruct H2 as (z & _ & Hzz).
  destruct z; rewrite <- Hzz.
  apply za'.
-intros y.
 split.
 +intros (x & (Hx & Hax) & Hxy).
  split; [ split | ].
  *now rewrite <- Hxy; apply g.
  *rewrite <- Hxy, Hcgg', Hax; apply g'.
  *assert (Hy : y ∈ Ker c). {
     split; [ now rewrite <- Hxy; apply g | ].
     apply (f_equal (H_app g')) in Hax.
     rewrite <- Hcgg', Hxy in Hax.
     rewrite Hax.
     apply g'.
   }
   destruct d as (appd, dp).
   destruct dp as (dz, din, dlin); simpl.
   simpl in dz.
   specialize (din _ Hy) as H1.
   simpl in H1.
   destruct H1 as (Hay & z & Haz & t & Hat & Ht).
   rewrite <- Hxy.
...
   apply appd.
...
-idtac.
...
   apply sg'; rewrite <- Hxy.
   exists x; easy.
 +intros ((Hy & Hby) & Hgy).
  assert (H : y ∈ Im f) by now apply sf; split.
  destruct H as (x & Hx & Hxy).
  exists x; split; [ | easy ].
  split; [ easy | ].
  rewrite <- Hxy, Hcff' in Hby.
  specialize (sf' (H_app a x)) as (H1, H2).
  assert (H3 : H_app a x ∈ Ker f') by now split; [ apply a | ].
  specialize (H2 H3).
  destruct H2 as (z & _ & Hzz).
  destruct z; rewrite <- Hzz.
  apply za'.
...
