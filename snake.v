(* Snake lemma *)

Require Import Utf8.
Require Import Classes.RelationClasses.
Require Import Setoid.
Require ClassicalChoice.

Record is_abelian_group {T} (gr_eq : T → T → Prop) (gr_mem : T → Prop)
       gr_zero gr_add gr_opp :=
  { ig_zero : gr_mem gr_zero;
    ig_add_mem : ∀ x y, gr_mem x → gr_mem y → gr_mem (gr_add x y);
    ig_add_0_l : ∀ x, gr_eq (gr_add gr_zero x) x;
    ig_add_assoc : ∀ x y z,
      gr_eq (gr_add (gr_add x y) z) (gr_add x (gr_add y z));
    ig_opp_mem : ∀ x, gr_mem x → gr_mem (gr_opp x);
    ig_add_opp_r : ∀ x, gr_eq (gr_add x (gr_opp x)) gr_zero;
    ig_add_comm : ∀ x y, gr_eq (gr_add x y) (gr_add y x);
    ig_equiv : Equivalence gr_eq;
    ig_mem_compat : ∀ x y, gr_eq x y → gr_mem x → gr_mem y;
    ig_add_compat : ∀ x y x' y',
      gr_eq x y → gr_eq x' y' → gr_eq (gr_add x x') (gr_add y y');
    ig_opp_compat : ∀ x y,
      gr_eq x y → gr_eq (gr_opp x) (gr_opp y) }.

Record AbGroup :=
  { gr_set : Type;
    gr_mem : gr_set → Prop;
    gr_eq : gr_set → gr_set → Prop;
    gr_zero : gr_set;
    gr_add : gr_set → gr_set → gr_set;
    gr_opp : gr_set → gr_set;
    gr_prop : is_abelian_group gr_eq gr_mem gr_zero gr_add gr_opp }.

Arguments gr_eq [_].
Arguments gr_zero [_].
Arguments gr_add [_].
Arguments gr_opp [_].

Notation "x '∈' S" := (gr_mem S x) (at level 60).
Notation "x '∉' S" := (¬ gr_mem S x) (at level 60).
Notation "x '≡' y" := (gr_eq x y) (at level 70).

Delimit Scope group_scope with G.

Notation "0" := (gr_zero) : group_scope.
Notation "a = b" := (gr_eq a b) : group_scope.
Notation "a ≠ b" := (¬ gr_eq a b) : group_scope.
Notation "a + b" := (gr_add a b) : group_scope.
Notation "a - b" := (gr_add a (gr_opp b)) : group_scope.
Notation "- a" := (gr_opp a) : group_scope.

Axiom MemDec : ∀ G x, {x ∈ G} + {x ∉ G}.

Record is_homgr A B f :=
  { ih_zero : f gr_zero ≡ gr_zero;
    ih_mem_compat : ∀ x, x ∈ A → f x ∈ B;
    ih_lin : ∀ x y, x ∈ A → y ∈ A → f (gr_add x y) ≡ gr_add (f x) (f y);
    ih_opp : ∀ x, x ∈ A → f (gr_opp x) ≡ gr_opp (f x);
    ih_compat : ∀ x y, x ∈ A → y ∈ A → x ≡ y → f x ≡ f y }.

Record HomGr (A B : AbGroup) :=
  { H_app : gr_set A → gr_set B;
    H_prop : is_homgr A B H_app }.

Arguments H_app [A] [B].

Theorem gr_zero_mem : ∀ G, gr_zero ∈ G.
Proof.
intros.
apply (ig_zero _ _ _ _ _ (gr_prop G)).
Qed.

Theorem gr_eq_refl : ∀ G (x : gr_set G), x ≡ x.
Proof.
intros.
apply (@Equivalence_Reflexive _ _ (ig_equiv _ _ _ _ _ (gr_prop G))).
Qed.

Theorem gr_eq_symm : ∀ G (x y : gr_set G), x ≡ y → y ≡ x.
Proof.
intros.
now apply (@Equivalence_Symmetric _ _ (ig_equiv _ _ _ _ _ (gr_prop G))).
Qed.

Theorem gr_eq_trans : ∀ G (x y z : gr_set G), x ≡ y → y ≡ z → x ≡ z.
Proof.
intros * Hxy Hyz.
eapply (@Equivalence_Transitive _ _ (ig_equiv _ _ _ _ _ (gr_prop G))).
apply Hxy.
apply Hyz.
Qed.

Theorem gr_add_mem : ∀ G x y, x ∈ G → y ∈ G → gr_add x y ∈ G.
Proof.
intros.
now apply (ig_add_mem _ _ _ _ _ (gr_prop G)).
Qed.

Theorem gr_add_0_l : ∀ G (x : gr_set G), (0 + x = x)%G.
Proof.
intros.
apply (ig_add_0_l _ _ _ _ _ (gr_prop G)).
Qed.

Theorem gr_add_opp_r : ∀ G (x : gr_set G), (x - x = 0)%G.
Proof.
intros.
apply (ig_add_opp_r _ _ _ _ _ (gr_prop G)).
Qed.

Theorem gr_opp_mem : ∀ G x, x ∈ G → gr_opp x ∈ G.
Proof.
intros.
now apply (ig_opp_mem _ _ _ _ _ (gr_prop G)).
Qed.

Theorem gr_add_assoc : ∀ G (x y z : gr_set G), ((x + y) + z = x + (y + z))%G.
Proof.
intros.
apply (ig_add_assoc _ _ _ _ _ (gr_prop G)).
Qed.

Theorem gr_add_comm : ∀ G (x y : gr_set G), (x + y = y + x)%G.
Proof.
intros.
apply (ig_add_comm _ _ _ _ _ (gr_prop G)).
Qed.

Theorem gr_add_0_r : ∀ G (x : gr_set G), (x + 0 = x)%G.
Proof.
intros.
eapply gr_eq_trans; [ apply gr_add_comm | ].
apply (ig_add_0_l _ _ _ _ _ (gr_prop G)).
Qed.

Theorem gr_add_compat : ∀ G (x y x' y' : gr_set G),
  x ≡ y → x' ≡ y' → gr_add x x' ≡ gr_add y y'.
Proof.
intros.
now apply (ig_add_compat _ _ _ _ _ (gr_prop G)).
Qed.

Theorem gr_opp_compat : ∀ G (x y : gr_set G),
  x ≡ y → gr_opp x ≡ gr_opp y.
Proof.
intros * Hxy.
now apply (ig_opp_compat _ _ _ _ _ (gr_prop G)).
Qed.

Theorem gr_mem_compat : ∀ G x y, x ≡ y → x ∈ G → y ∈ G.
Proof.
intros * Hxy Hx.
eapply (ig_mem_compat _ _ _ _ _ (gr_prop G)); [ apply Hxy | apply Hx ].
Qed.

Theorem gr_opp_zero : ∀ G, gr_opp gr_zero ≡ @gr_zero G.
Proof.
intros.
specialize (@gr_add_opp_r G gr_zero) as H1.
specialize (@gr_add_0_l G (gr_opp gr_zero)) as H3.
eapply gr_eq_trans; [ | apply H1 ].
now apply gr_eq_symm.
Qed.

Theorem gr_opp_add_distr : ∀ G (x y : gr_set G), (- (x + y) = - x - y)%G.
Proof.
intros *.
apply gr_eq_trans with (y := (- (x + y) + y - y)%G).
-apply gr_eq_symm.
 eapply gr_eq_trans; [ apply gr_add_assoc | ].
 apply gr_eq_trans with (y := (- (x + y) + 0)%G).
 +apply gr_add_compat; [ apply gr_eq_refl | ].
  apply gr_add_opp_r.
 +apply gr_add_0_r.
-apply gr_add_compat; [ | apply gr_eq_refl ].
...

Theorem gr_sub_move_r : ∀ G (x y z : gr_set G),
  x ∈ G → y ∈ G → (x - y = z ↔ x = z + y)%G.
...

Theorem H_zero : ∀ A B (f : HomGr A B), H_app f gr_zero ≡ gr_zero.
Proof.
intros.
apply (@ih_zero _ _ (H_app f) (H_prop _ _ f)).
Qed.

Theorem H_lin : ∀ A B (f : HomGr A B) x y, x ∈ A → y ∈ A →
  H_app f (gr_add x y) ≡ gr_add (H_app f x) (H_app f y).
Proof.
intros.
now apply (@ih_lin _ _ _ (H_prop _ _ f)).
Qed.

Theorem H_opp : ∀ A B (f : HomGr A B) x, x ∈ A →
  H_app f (gr_opp x) ≡ gr_opp (H_app f x).
Proof.
intros.
now apply (@ih_opp _ _ _ (H_prop _ _ f)).
Qed.

Theorem H_mem_compat : ∀ A B (f : HomGr A B) x, x ∈ A → H_app f x ∈ B.
Proof.
intros.
now apply (@ih_mem_compat _ _ _ (H_prop _ _ f)).
Qed.

Theorem H_compat : ∀ A B (f : HomGr A B) x y, x ∈ A → y ∈ A →
  x ≡ y → H_app f x ≡ H_app f y.
Proof.
intros.
now apply (@ih_compat _ _ _ (H_prop _ _ f)).
Qed.

Inductive Gr0_set := G0 : Gr0_set.

Theorem Gr0_prop : is_abelian_group eq (λ _, True) G0 (λ _ _, G0) (λ x, x).
Proof.
split; try easy.
-now intros x; destruct x.
-split; [ easy | easy | apply eq_Transitive ].
Qed.

Definition Gr0 :=
   {| gr_set := Gr0_set;
      gr_mem _ := True;
      gr_eq := eq;
      gr_zero := G0;
      gr_add _ _ := G0;
      gr_opp x := x;
      gr_prop := Gr0_prop |}.

Definition is_initial (G : AbGroup) :=
  ∀ H (f g : HomGr G H) (x : gr_set G), H_app f x ≡ H_app g x.
Definition is_final (G : AbGroup) :=
  ∀ H (f g : HomGr H G) (x : gr_set H), H_app f x ≡ H_app g x.
Definition is_null (G : AbGroup) := is_initial G ∧ is_final G.

Theorem is_null_Gr0 : is_null Gr0.
Proof.
split; intros H f g x.
-destruct x.
 apply gr_eq_trans with (y := gr_zero); [ apply f | apply gr_eq_symm, g ].
-now destruct (H_app f x), (H_app g x).
Qed.

Theorem Im_is_abelian_group {G H} (f : HomGr G H) :
  is_abelian_group (@gr_eq H) (λ b, ∃ a, a ∈ G ∧ H_app f a ≡ b)
    gr_zero (@gr_add H) (@gr_opp H).
Proof.
intros.
split.
-exists gr_zero.
 split; [ apply G | apply f ].
-intros y y' (x & Hxg & Hx) (x' & Hx'g & Hx').
 exists (gr_add x x').
 split; [ now apply G | ].
 eapply gr_eq_trans; [ now apply H_lin | ].
 apply gr_eq_trans with (y := gr_add y y').
 +now apply gr_add_compat.
 +apply gr_eq_refl.
-intros; apply gr_add_0_l.
-intros; apply gr_add_assoc.
-intros x (y & Hy & Hyx).
 exists (gr_opp y).
 split; [ now apply gr_opp_mem | ].
 apply gr_eq_trans with (y := gr_opp (H_app f y)).
 +now apply H_opp.
 +now apply gr_opp_compat.
-intros; apply gr_add_opp_r.
-intros; apply gr_add_comm.
-split.
 +intros x; apply gr_eq_refl.
 +intros x y; apply gr_eq_symm.
 +intros x y z; apply gr_eq_trans.
-intros * Hxy (z, Hz).
 exists z.
 split; [ easy | ].
 eapply gr_eq_trans; [ apply Hz | easy ].
-apply gr_add_compat.
-apply gr_opp_compat.
Qed.

Theorem Ker_is_abelian_group {G H} : ∀ (f : HomGr G H),
  is_abelian_group (@gr_eq G) (λ x, x ∈ G ∧ H_app f x ≡ gr_zero)
    gr_zero (@gr_add G) (@gr_opp G).
Proof.
intros.
split.
-split; [ apply gr_zero_mem | apply H_zero ].
-intros x x' (Hx, Hfx) (Hx', Hfx').
 split; [ now apply gr_add_mem | ].
 eapply gr_eq_trans; [ now apply H_lin | ].
 eapply gr_eq_trans; [ | apply gr_add_0_l ].
 now apply gr_add_compat.
-intros x; apply gr_add_0_l.
-intros; apply gr_add_assoc.
-intros x (Hx & Hfx).
 split.
 +now apply gr_opp_mem.
 +eapply gr_eq_trans; [ now apply H_opp | ].
  eapply gr_eq_trans; [ apply gr_opp_compat, Hfx | ].
  apply gr_opp_zero.
-intros; apply gr_add_opp_r.
-intros; apply gr_add_comm.
-split.
 +intros x; apply gr_eq_refl.
 +intros x y; apply gr_eq_symm.
 +intros x y z; apply gr_eq_trans.
-intros * Hxy (ax, Hx).
 split.
 +eapply gr_mem_compat; [ apply Hxy | easy ].
 +eapply gr_eq_trans; [ | apply Hx ].
  apply gr_eq_symm.
  apply H_compat; [ easy | | easy ].
  eapply gr_mem_compat; [ apply Hxy | easy ].
-intros x y x' y' Hxy Hxy'.
 now apply gr_add_compat.
-intros x y Hxy.
 now apply gr_opp_compat.
Qed.

Definition Im {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero;
     gr_eq := @gr_eq H;
     gr_mem := λ b, ∃ a, a ∈ G ∧ H_app f a ≡ b;
     gr_add := @gr_add H;
     gr_opp := @gr_opp H;
     gr_prop := Im_is_abelian_group f |}.

Definition Ker {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set G;
     gr_zero := gr_zero;
     gr_eq := @gr_eq G;
     gr_mem := λ a, a ∈ G ∧ H_app f a ≡ gr_zero;
     gr_add := @gr_add G;
     gr_opp := @gr_opp G;
     gr_prop := Ker_is_abelian_group f |}.

Definition gr_sub {G} (x y : gr_set G) := gr_add x (gr_opp y).

(* x ∈ coKer f ↔ x ∈ H/Im f
   quotient group is H with setoid, i.e. set with its own equality *)

Definition coKer_eq {G H} (f : HomGr G H) x y :=
  ∃ z, x ∉ H ∨ y ∉ H ∨ z ∈ Im f ∧ gr_sub x y ≡ z.

Theorem coKer_is_abelian_group {G H} : ∀ (f : HomGr G H),
  is_abelian_group (coKer_eq f) (gr_mem H)
    gr_zero (@gr_add H) (@gr_opp H).
Proof.
intros.
split.
-simpl; apply gr_zero_mem.
-intros * Hx Hy.
 now apply gr_add_mem.
-intros.
 exists gr_zero.
 right; right.
 split; [ apply gr_zero_mem | simpl ].
 eapply gr_eq_trans; [ apply gr_add_assoc | ].
 apply gr_eq_trans with (y := gr_add gr_zero gr_zero).
 +apply gr_add_compat; [ apply gr_eq_refl | apply gr_add_opp_r ].
 +apply gr_add_0_l.
-intros x y z.
 exists gr_zero.
 right; right.
 split; [ apply gr_zero_mem | simpl ].
 set (t := gr_add (@gr_add H x y) z).
 apply gr_eq_trans with (y := gr_add t (gr_opp t)); subst t.
 +apply gr_add_compat; [ apply gr_eq_refl | ].
  now apply gr_opp_compat, gr_eq_symm, gr_add_assoc.
 +apply gr_add_opp_r.
-intros x Hx.
 now apply gr_opp_mem.
-intros x.
 exists gr_zero.
 right; right.
 split; [ apply gr_zero_mem | simpl ].
 apply gr_eq_trans with (y := gr_add gr_zero gr_zero).
 +apply gr_add_compat; [ now apply gr_add_opp_r | ].
  apply gr_opp_zero.
 +apply gr_add_0_l.
-intros x y.
 exists gr_zero.
 right; right.
 split; [ apply gr_zero_mem | ].
 apply gr_eq_trans with (y := gr_sub (gr_add x y) (gr_add x y)).
 *simpl; apply gr_add_compat; [ apply gr_eq_refl | ].
  now apply gr_opp_compat, gr_add_comm.
 *simpl; apply gr_add_opp_r.
-unfold coKer_eq; split.
 +intros x; exists gr_zero.
  destruct (MemDec H x) as [Hx| Hx]; [ right; right | now left ].
  split; [ apply gr_zero_mem | ].
  now simpl; apply gr_add_opp_r.
 +intros x y (z & Hz).
  exists (gr_opp z).
  destruct (MemDec H x) as [Hx| Hx]; [ | now right; left ].
  destruct (MemDec H y) as [Hy| Hy]; [ | now left ].
  destruct Hz as [Hz| [Hz| Hz]]; [ easy | easy | ].
  right; right.
  split; [ now apply gr_opp_mem | ].
  apply gr_eq_trans with (y := gr_opp (gr_sub x y)).
  *apply gr_eq_symm.
   unfold gr_sub.
   eapply gr_eq_trans.
  --simpl in z; apply gr_opp_add_distr.
  --idtac.
...
  *now simpl; apply gr_opp_compat.
 +idtac.
...
 +intros x; apply gr_eq_refl.
 +intros x y; apply gr_eq_symm.
 +intros x y z; apply gr_eq_trans.
-intros * Hxy (ax, Hx).
 split.
 +eapply gr_mem_compat; [ apply Hxy | easy ].
 +eapply gr_eq_trans; [ | apply Hx ].
  apply gr_eq_symm.
  apply H_compat; [ easy | | easy ].
  eapply gr_mem_compat; [ apply Hxy | easy ].
-intros x y x' y' Hxy Hxy'.
 now apply gr_add_compat.
-intros x y Hxy.
 now apply gr_opp_compat.
...
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

Definition coKer {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_mem := λ x, x ∈ H ∧ ∃ y, y ∈ H ∧ gr_add x y ∈ Im f;
     gr_eq := @gr_eq H;
     gr_zero := gr_zero H;
     gr_add := @gr_add H;
     gr_prop := coKer_is_abelian_group f |}.

Inductive sequence {A : AbGroup} :=
  | Seq1 : sequence
  | Seq2 : ∀ {B} (f : HomGr A B), @sequence B → sequence.

Fixpoint exact_sequence {A : AbGroup} (S : sequence) :=
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

Theorem exists_ker_C_to_B : ∀ B C C' g (c : HomGr C C') (cz : HomGr C Gr0),
  (∀ a : gr_set (Im g), a ∈ Im g ↔ a ∈ Ker cz)
  → ∀ x : gr_set (Ker c), ∃ y, x ∉ C ∨ y ∈ B ∧ H_app g y ≡ x.
Proof.
intros * sg x.
destruct (InDec C x) as [H2| H2]; [ | now exists (gr_zero B); left ].
enough (H : x ∈ Im g). {
  simpl in H.
  destruct H as (y & Hy & Hyx).
  exists y; right; easy.
}
apply sg.
split; [ easy | ].
destruct cz as (appcz, czp).
destruct czp as (czz, czin, czlin, czcomp); simpl in *.
rewrite <- czlin with (x := x) (y := gr_zero C).
-apply czcomp; [ easy | | ].
 +apply C; [ easy | apply C ].
 +destruct C as (cs, ci, ceq, cz, co, cp).
  destruct cp as (czi, cc, cid, ca, cco, ceqv, cimo, camo).
  simpl in *.
  transitivity (co cz x).
  *now symmetry; apply cid.
  *now apply cco.
-easy.
-apply C.
Qed.

Lemma snake :
  ∀ (A B C A' B' C' : AbGroup)
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
specialize (exists_ker_C_to_B B C C' g c cz sg) as H1.
specialize (ClassicalChoice.choice _ H1) as (f1, Hf1).
clear H1.
remember (H_app b) as f2 eqn:Hf2.
move f2 before f1.
...
assert (d : HomGr (Ker c) (coKer a)). {
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
