(* Snake lemma *)

Require Import Utf8.
Require Import Classes.RelationClasses.
Require Import Setoid.

Record is_abelian_group {T} (gr_eq : T → T → Prop) in_gr gr_zero gr_add :=
  { ig_zero : in_gr gr_zero;
    ig_clos : ∀ x y, in_gr x → in_gr y → in_gr (gr_add x y);
    ig_id : ∀ x, in_gr x → gr_eq (gr_add gr_zero x) x;
    ig_assoc : ∀ x y z, in_gr x → in_gr y → in_gr z →
      gr_eq (gr_add (gr_add x y) z) (gr_add x (gr_add y z));
    ig_comm : ∀ x y, in_gr x → in_gr y →
      gr_eq (gr_add x y) (gr_add y x);
    ig_equiv : Equivalence gr_eq;
    ig_in_compat : ∀ x y, gr_eq x y → in_gr x → in_gr y;
    ig_add_compat : ∀ x y x' y',
      gr_eq x y → gr_eq x' y' → gr_eq (gr_add x x') (gr_add y y') }.

Record Group :=
  { gr_set : Type;
    gr_in : gr_set → Prop;
    gr_eq : gr_set → gr_set → Prop;
    gr_zero : gr_set;
    gr_add : gr_set → gr_set → gr_set;
    gr_prop : is_abelian_group gr_eq gr_in gr_zero gr_add }.

Arguments gr_eq [_].
Arguments gr_add [_].

Notation "x '∈' S" := (gr_in S x) (at level 60).
Notation "x '≡' y" := (gr_eq x y) (at level 70).

Record is_homgr A B f :=
  { ih_zero : f (gr_zero A) ≡ gr_zero B;
    ih_inco : ∀ x, x ∈ A → f x ∈ B;
    ih_lin : ∀ x y, x ∈ A → y ∈ A → f (gr_add x y) ≡ gr_add (f x) (f y);
    ih_compat : ∀ x y, x ∈ A → y ∈ A → x ≡ y → f x ≡ f y }.

Record HomGr (A B : Group) :=
  { H_app : gr_set A → gr_set B;
    H_prop : is_homgr A B H_app }.

Arguments H_app [A] [B].

Inductive Gr0_set := G0 : Gr0_set.

Theorem Gr0_prop : is_abelian_group eq (λ _, True) G0 (λ _ _, G0).
Proof.
split; [ easy | easy | | | easy | | easy | easy ].
-now intros x; destruct x.
-now intros x; destruct x.
-split; [ easy | easy | apply eq_Transitive ].
Qed.

Definition Gr0 :=
   {| gr_set := Gr0_set;
      gr_zero := G0;
      gr_add := λ _ _, G0;
      gr_in := λ _, True;
      gr_eq := eq;
      gr_prop := Gr0_prop |}.

Definition is_initial (G : Group) :=
  ∀ H (f g : HomGr G H) (x : gr_set G), H_app f x ≡ H_app g x.
Definition is_final (G : Group) :=
  ∀ H (f g : HomGr H G) (x : gr_set H), H_app f x ≡ H_app g x.
Definition is_null (G : Group) := is_initial G ∧ is_final G.

Theorem is_null_Gr0 : is_null Gr0.
Proof.
split; intros H f g x.
-destruct f as (fa & fih); simpl in fih.
 destruct g as (ga & gih); simpl in gih.
 simpl.
 destruct x.
 destruct fih, gih; simpl in *.
 destruct H; simpl in *.
 destruct gr_prop0; simpl in *.
 etransitivity; [ apply ih_zero0 | easy ].
-destruct f as (fa & fih); simpl in fih.
 destruct g as (ga & gih); simpl in gih.
 simpl.
 now destruct (fa x), (ga x).
Qed.

Theorem Im_is_abelian_group {G H} (f : HomGr G H) :
  is_abelian_group (@gr_eq H) (λ b, ∃ a, a ∈ G ∧ H_app f a ≡ b)
    (gr_zero H) (@gr_add H).
Proof.
intros.
split.
-exists (gr_zero G).
 split; [ apply G | apply f ].
-intros y y' (x & Hxg & Hx) (x' & Hx'g & Hx').
 destruct G as (gs, gi, geq, gz, go, gp).
 destruct gp as (gzi, gc, gid, ga, gco, geqv, gimo, gamo).
 destruct H as (hs, hi, heq, hz, ho, hp).
 destruct hp as (hzi, hc, hid, ha, hco, heqv, himo, hamo).
 destruct f as (appf, fp).
 destruct fp as (fz, fin, flin, fcomp); simpl in *.
 exists (go x x').
 split; [ now apply gc | ].
 rewrite flin; [ | easy | easy ].
 now apply hamo; [ transitivity y | ].
-intros y (x & Hxg & Hx).
 apply H.
 eapply H; [ apply Hx | now apply f ].
-intros * (ax, Hx) (ay, Hy) (az, Hz).
 apply H.
 +eapply H; [ apply Hx | apply f, Hx ].
 +eapply H; [ apply Hy | apply f, Hy ].
 +eapply H; [ apply Hz | apply f, Hz ].
-intros * (ax, Hx) (ay, Hy).
 apply H.
 +eapply H; [ apply Hx | apply f, Hx ].
 +eapply H; [ apply Hy | apply f, Hy ].
-apply H.
-intros * Hxy (ax, Hx).
 exists ax.
 split; [ easy | ].
 destruct H as (hs, hi, heq, hz, ho, hp).
 destruct hp as (hzi, hc, hid, ha, hco, heqv, himo, hamo).
 simpl in *.
 transitivity x; [ apply Hx | easy ].
-intros * Hxy Hxy'.
 destruct H as (hs, hi, heq, hz, ho, hp).
 destruct hp as (hzi, hc, hid, ha, hco, heqv, himo, hamo).
 simpl in *.
 now apply hamo.
Qed.

Theorem Ker_is_abelian_group {G H} : ∀ (f : HomGr G H),
  is_abelian_group (@gr_eq G) (λ x, x ∈ G ∧ H_app f x ≡ gr_zero H)
    (gr_zero G) (gr_add (g:=G)).
Proof.
intros.
split.
-split; [ apply G | apply f ].
-intros x x' (Hx, Hfx) (Hx', Hfx').
 split; [ now apply G | ].
 destruct f as (appf, fp).
 destruct fp as (fz, fin, flin, fcomp).
 destruct H as (hs, hi, heq, hz, ho, hp).
 destruct hp as (hzi, hc, hid, ha, hco, heqv, himo, hamo).
 simpl in *.
 etransitivity; [ now apply flin | ].
 assert (H : heq (ho hz hz) hz) by now apply hid.
 etransitivity; [ | apply H ].
 now apply hamo.
-intros x (Hx, Hfx).
 now apply G.
-intros * (ax, Hx) (ay, Hy) (az, Hz).
 now apply G.
-intros * (ax, Hx) (ay, Hy).
 now apply G.
-apply G.
-intros * Hxy (ax, Hx).
 split.
 +eapply ig_in_compat; [ apply G | apply Hxy | easy ].
 +destruct H as (hs, hi, heq, hz, ho, hp).
  destruct hp as (hzi, hc, hid, ha, hco, heqv, himo, hamo).
  destruct f as (appf, fp).
  destruct fp as (fz, fin, flin, fcomp).
  simpl in *.
  transitivity (appf x); [ | easy ].
  symmetry.
  apply fcomp; [ easy | | easy ].
  eapply G; [ apply Hxy | easy ].
-intros x y x' y' Hxy Hxy'.
 eapply ig_add_compat; [ apply G | easy | easy ].
Qed.

Definition Im {G H : Group} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero H;
     gr_eq := @gr_eq H;
     gr_in := λ b, ∃ a, a ∈ G ∧ H_app f a ≡ b;
     gr_add := @gr_add H;
     gr_prop := Im_is_abelian_group f |}.

Definition Ker {G H : Group} (f : HomGr G H) :=
  {| gr_set := gr_set G;
     gr_zero := gr_zero G;
     gr_eq := @gr_eq G;
     gr_in := λ a, a ∈ G ∧ H_app f a ≡ gr_zero H;
     gr_add := @gr_add G;
     gr_prop := Ker_is_abelian_group f |}.

Theorem coKer_is_abelian_group {G H} : ∀ (f : HomGr G H),
  is_abelian_group (gr_eq (g:=H)) (λ x, x ∈ H ∧ ∃ y, y ∈ H ∧ gr_add x y ∈ Im f)
    (gr_zero H) (gr_add (g:=H)).
Proof.
intros.
split.
-split; [ apply H | ].
 exists (gr_zero H).
 split; [ apply H | ].
 exists (gr_zero G).
 split; [ eapply ig_zero; apply G | ].
 destruct H as (hs, hi, heq, hz, ho, hp).
 destruct hp as (hzi, hc, hid, ha, hco, heqv, himo, hamo).
 destruct f as (appf, fp).
 destruct fp as (fz, fin, flin, fcomp).
 simpl in *.
 transitivity hz; [ easy | ].
 now symmetry; apply hid.
-intros y y' (Hy & z & Hz & x & Hgx & Hx) (Hy' & z' & Hz' & x' & Hgx' & Hx').
 split; [ now apply H | ].
 exists (gr_add z z').
 split; [ now apply H | ].
 exists (gr_add x x').
 destruct f as (appf, fp); simpl in *.
 destruct fp as (fz, fin, flin, fcomp); simpl in *.
 split.
 +eapply ig_clos; [ apply gr_prop | easy | easy ].
 +destruct H as (hs, hi, heq, hz, ho, hp).
  destruct hp as (hzi, hc, hid, ha, hco, heqv, himo, hamo).
  simpl in *.
  transitivity (ho (ho y z) (ho y' z')).
  *now etransitivity; [ apply flin | apply hamo ].
  *etransitivity.
  --apply ha; [ easy | easy | now apply hc ].
  --etransitivity.
   ++apply hco; [ easy | ].
     apply hc; [ easy | now apply hc ].
   ++symmetry.
     etransitivity; [ now apply hco; apply hc | ].
     symmetry.
     etransitivity.
    **apply ha; [ easy | now apply hc | easy ].
    **symmetry.
      etransitivity.
    ---apply ha; [ easy | easy | now apply hc ].
    ---apply hamo; [ easy | ].
       etransitivity.
     +++apply hco; [ easy | now apply hc ].
     +++etransitivity; [ now apply ha | ].
        symmetry.
        apply hco; [ now apply hc | easy ].
-intros x (Hx & y & Hy).
 now apply H.
-intros x y z.
 intros (Hx & x' & Hx' & Hxx) (Hy & y' & Hy' & Hyy) (Hz & z' & Hz' & Hzz).
 eapply ig_assoc; [ apply H | easy | easy | easy ].
-intros x y (Hx & x' & Hx' & Hxx) (Hy & y' & Hy' & Hyy).
 destruct H as (hs, hi, heq, hz, ho, hp).
 destruct hp as (hzi, hc, hid, ha, hco, heqv, himo, hamo).
 simpl in *.
 now apply hco.
-apply H.
-intros y y' Hyy' (Hy & y'' & Hy'' & x & Hx & Hxy).
 split.
 +eapply ig_in_compat; [ apply H | apply Hyy' | easy ].
 +exists y''.
  split; [ easy | ].
  exists x.
  split; [ easy | ].
  destruct H as (hs, hi, heq, hz, ho, hp).
  destruct hp as (hzi, hc, hid, ha, hco, heqv, himo, hamo).
  simpl in *.
  etransitivity; [ apply Hxy | now apply hamo ].
-intros x y x' y' Hxy Hxy'.
 eapply ig_add_compat; [ apply H | easy | easy ].
Qed.

Definition coKer {G H : Group} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_in := λ x, x ∈ H ∧ ∃ y, y ∈ H ∧ gr_add x y ∈ Im f;
     gr_eq := @gr_eq H;
     gr_zero := gr_zero H;
     gr_add := @gr_add H;
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
  ∀ x, H_app h (H_app f x) ≡ H_app k (H_app g x).

Theorem is_homgr_Ker_Ker {A B A' B'} :
  ∀ (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  diagram_commutes f a b f'
  → is_homgr (Ker a) (Ker b) (H_app f).
Proof.
intros * Hc.
split; [ apply f | | | ].
-intros x Hx.
 split; [ now apply f; simpl in Hx | ].
 destruct B' as (bs, bi, beq, bz, bo, bp).
 destruct bp as (bzi, bc, bid, ba, bco, beqv, bimo, bamo).
 simpl in *.
 etransitivity; [ apply Hc | ].
 transitivity (H_app f' (gr_zero A')).
 +apply f'; [ apply a, Hx | apply A' | apply Hx ].
 +apply f'.
-intros x x' Hx Hx'; simpl in Hx, Hx'.
 now apply f.
-intros x y Hx Hy Hxy.
 simpl in Hx, Hy.
 now apply f.
Qed.

Theorem is_homgr_coKer_coKer {A B A' B'} :
  ∀ (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  diagram_commutes f a b f'
  → is_homgr (coKer a) (coKer b) (H_app f').
Proof.
intros * Hc.
split; [ apply f' | | | ].
-intros x Hx.
 split; [ apply f', Hx | ].
 destruct Hx as (Hxa & y & Hy & z & Hz & Hxy).
 exists (H_app f' y).
 split; [ now apply f' | ].
 exists (H_app f z).
 split; [ now apply f | ].
 destruct B' as (bs, bi, beq, bz, bo, bp).
 destruct bp as (bzi, bc, bid, ba, bco, beqv, bimo, bamo).
 simpl in *.
 etransitivity; [ apply Hc | ].
 symmetry.
 etransitivity; [ now symmetry; apply f' | ].
 destruct A' as (ass, ai, aeq, az, ao, ap).
 destruct ap as (azi, ac, aid, aa, aco, aeqv, aimo, aamo).
 simpl in *.
 apply f'; simpl; [ now apply ac | | ].
 +eapply aimo; [ symmetry; apply Hxy | now apply ac ].
 +now symmetry.
-intros x y Hx Hy; simpl in Hx, Hy.
 now apply f'.
-intros x y Hx Hy Hxy.
 simpl in Hx, Hy.
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
assert (d : HomGr (Ker c) (coKer a)). {
  assert (appd : gr_set (Ker c) → gr_set (coKer a)). {
    intros x.
    simpl in x; simpl.
    ...
  }
  ...
}
exists d.
simpl.
split; [ | split ].
-intros y.
 split.
 +intros (x & (Hx & Hax) & Hxy).
  split; [ split | ].
  *eapply B; [ apply Hxy | now apply f ].
  *destruct B' as (b's, b'i, b'eq, b'z, b'o, b'p).
   destruct b'p as (b'zi, b'c, b'id, b'a, b'co, b'eqv, b'imo, b'amo).
   destruct B as (bs, bi, beq, bz, bo, bp).
   destruct bp as (bzi, bc, bid, ba, bco, beqv, bimo, bamo).
   simpl in *.
   transitivity (H_app b (H_app f x)).
  --apply b.
   ++eapply bimo; [ apply Hxy | now apply f ].
   ++now apply f.
   ++now symmetry.
  --etransitivity; [ apply Hcff' | ].
    transitivity (H_app f' (gr_zero A')); [ | apply f' ].
    apply f'; [ now apply a | apply A' | easy ].
  *apply sf.
   exists x; easy.
 +intros ((Hy & Hby) & Hgy).
  assert (H : y ∈ Im f) by now apply sf; split.
  destruct H as (x & Hx & Hxy).
  exists x; split; [ | easy ].
  split; [ easy | ].
  specialize (sf' (H_app a x)) as (H1, H2).
  assert (H3 : H_app a x ∈ Ker f'). {
    split; [ now apply a | ].
    specialize (Hcff' x) as H3.
    destruct B' as (b's, b'i, b'eq, b'z, b'o, b'p).
    destruct b'p as (b'zi, b'c, b'id, b'a, b'co, b'eqv, b'imo, b'amo).
    simpl in *.
    etransitivity; [ symmetry; apply H3 | ].
    transitivity (H_app b y); [ | easy ].
    apply b; [ | easy | easy ].
    destruct B as (bs, bi, beq, bz, bo, bp).
    destruct bp as (bzi, bc, bid, ba, bco, beqv, bimo, bamo).
    simpl in *.
    eapply bimo; [ symmetry; apply Hxy | easy ].
  }
  specialize (H2 H3).
  destruct H2 as (z & _ & Hzz).
  destruct z.
  destruct A' as (a's, a'i, a'eq, a'z, a'o, a'p).
  destruct a'p as (a'zi, a'c, a'id, a'a, a'co, a'eqv, a'imo, a'amo).
  simpl in *.
  etransitivity; [ symmetry; apply Hzz | ].
  apply za'.
-intros y.
 split.
 +intros (x & (Hx & Hax) & Hxy).
  split; [ split | ].
  *eapply C; [ apply Hxy | now apply g ].
  *specialize (Hcgg' x) as H1.
   destruct C' as (c's, c'i, c'eq, c'z, c'o, c'p).
   destruct c'p as (c'zi, c'c, c'id, c'a, c'co, c'eqv, c'imo, c'amo).
   simpl in *.
   transitivity (H_app c (H_app g x)).
  --eapply c; [ | now apply g | now apply C ].
    eapply C; [ apply Hxy | now apply g ].
  --etransitivity; [ apply H1 | ].
    transitivity (H_app g' (gr_zero B')); [ | apply g' ].
    apply g'; [ now apply b | apply B' | easy ].
  *destruct A' as (a's, a'i, a'eq, a'z, a'o, a'p).
   destruct a'p as (a'zi, a'c, a'id, a'a, a'co, a'eqv, a'imo, a'amo).
   simpl in *.
   transitivity (H_app d (H_app g x)).
  --eapply d; [ | | now apply C ].
    split.
   ++eapply C; [ apply Hxy | now apply g ].
   ++destruct C' as (c's, c'i, c'eq, c'z, c'o, c'p).
     destruct c'p as (c'zi, c'c, c'id, c'a, c'co, c'eqv, c'imo, c'amo).
     simpl in *.
     transitivity (H_app c (H_app g x)).
    **eapply c; [ | now apply g | now apply C ].
      eapply C; [ apply Hxy | now apply g ].
    **etransitivity; [ apply Hcgg' | ].
      transitivity (H_app g' (gr_zero B')); [ | apply g' ].
      apply g'; [ now apply b | apply B' | easy ].
   ++split; [ now apply g | ].
     destruct C' as (c's, c'i, c'eq, c'z, c'o, c'p).
     destruct c'p as (c'zi, c'c, c'id, c'a, c'co, c'eqv, c'imo, c'amo).
     simpl in *.
     etransitivity; [ apply Hcgg' | ].
     transitivity (H_app g' (gr_zero B')); [ | apply g' ].
     apply g'; [ now apply b | apply B' | easy ].
  --destruct d as (appd, dp).
    destruct dp as (dz, din, dlin, dcomp); simpl in *.
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
