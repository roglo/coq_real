(* Snake lemma *)

Require Import Utf8.
Require Import Classes.RelationClasses.
Require Import Setoid.
Require ClassicalChoice.

Reserved Notation "x '≡' y" (at level 70).

Record AbGroup :=
  { gr_set : Type;
    gr_mem : gr_set → Prop;
    gr_eq : gr_set → gr_set → Prop where "x ≡ y" := (gr_eq x y);
    gr_zero : gr_set where "0" := (gr_zero);
    gr_add : gr_set → gr_set → gr_set where "x + y" := (gr_add x y);
    gr_opp : gr_set → gr_set where "- x" := (gr_opp x);
    gr_zero_mem : gr_mem 0;
    gr_add_mem : ∀ x y, gr_mem x → gr_mem y → gr_mem (x + y);
    gr_add_0_l : ∀ x, 0 + x ≡ x;
    gr_add_assoc : ∀ x y z, (x + y) + z ≡ x + (y + z);
    gr_opp_mem : ∀ x, gr_mem x → gr_mem (- x);
    gr_add_opp_r : ∀ x, x + (- x) ≡ 0;
    gr_add_comm : ∀ x y, x + y ≡ y + x;
    gr_equiv : Equivalence gr_eq;
    gr_mem_compat : ∀ x y, x ≡ y → gr_mem x → gr_mem y;
    gr_add_compat : ∀ x y x' y', x ≡ y → x' ≡ y' → x + x' ≡ y + y';
    gr_opp_compat : ∀ x y, x ≡ y → - x ≡ - y }.

Arguments gr_eq [_].
Arguments gr_zero [_].
Arguments gr_add [_].
Arguments gr_opp [_].
Arguments gr_add_mem G : rename.
Arguments gr_add_0_l G : rename.
Arguments gr_add_assoc G : rename.
Arguments gr_opp_mem G : rename.
Arguments gr_add_opp_r G : rename.
Arguments gr_add_comm G : rename.
Arguments gr_equiv G : rename.
Arguments gr_mem_compat G : rename.
Arguments gr_add_compat G : rename.
Arguments gr_opp_compat G : rename.

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

Theorem gr_eq_refl : ∀ G (x : gr_set G), x ≡ x.
Proof.
apply gr_equiv.
Qed.

Theorem gr_eq_symm : ∀ G (x y : gr_set G), x ≡ y → y ≡ x.
Proof.
apply gr_equiv.
Qed.

Theorem gr_eq_trans : ∀ G (x y z : gr_set G), x ≡ y → y ≡ z → x ≡ z.
Proof.
apply gr_equiv.
Qed.

Theorem gr_add_0_r : ∀ G (x : gr_set G), (x + 0 = x)%G.
Proof.
intros.
eapply gr_eq_trans; [ apply gr_add_comm | ].
Check gr_add_0_l.
apply gr_add_0_l.
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
 (* déplacer x de droite (-x) à gauche (+x),
    associer (x+y) ; utiliser le fait que -(x+y)+(x+y)=0 *)
Abort. (* à reprendre plus tard...
...

Theorem gr_sub_move_r : ∀ G (x y z : gr_set G),
  (x - y = z ↔ x = z + y)%G.
...
*)

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

Theorem Gr0_add_0_l : ∀ x, (λ _ _ : Gr0_set, G0) G0 x = x.
Proof.
now intros x; destruct x.
Qed.

Definition Gr0 :=
   {| gr_set := Gr0_set;
      gr_mem _ := True;
      gr_eq := eq;
      gr_zero := G0;
      gr_add _ _ := G0;
      gr_opp x := x;
      gr_zero_mem := I;
      gr_add_mem _ _ _ _ := I;
      gr_add_0_l := Gr0_add_0_l;
      gr_add_assoc _ _ _ := eq_refl G0;
      gr_opp_mem _ H := H;
      gr_add_opp_r _ := eq_refl;
      gr_add_comm _ _ := eq_refl G0;
      gr_equiv := eq_equivalence;
      gr_mem_compat _ _ _ _ := I;
      gr_add_compat _ _ _ _ _ _ := eq_refl;
      gr_opp_compat _ _ H := H |}.

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

Theorem Im_zero_mem {G H} : ∀ (f : HomGr G H),
  ∃ a : gr_set G, a ∈ G ∧ (H_app f a = 0)%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | apply H_zero ].
Qed.

Theorem Im_add_mem {G H} : ∀ f (x y : gr_set H),
  (∃ a : gr_set G, a ∈ G ∧ (H_app f a = x)%G)
  → (∃ a : gr_set G, a ∈ G ∧ (H_app f a = y)%G)
    → ∃ a : gr_set G, a ∈ G ∧ (H_app f a = x + y)%G.
Proof.
intros f y y' (x & Hxg & Hx) (x' & Hx'g & Hx').
exists (gr_add x x').
split; [ now apply G | ].
eapply gr_eq_trans; [ now apply H_lin | ].
apply gr_eq_trans with (y := gr_add y y').
+now apply gr_add_compat.
+apply gr_eq_refl.
Qed.

Theorem Im_opp_mem {G H} : ∀ (f : HomGr G H) (x : gr_set H),
  (∃ a : gr_set G, a ∈ G ∧ (H_app f a = x)%G)
  → ∃ a : gr_set G, a ∈ G ∧ (H_app f a = - x)%G.
Proof.
intros f x (y & Hy & Hyx).
exists (gr_opp y).
split; [ now apply gr_opp_mem | ].
apply gr_eq_trans with (y := gr_opp (H_app f y)).
+now apply H_opp.
+now apply gr_opp_compat.
Qed.

Theorem Im_equiv {G} : Equivalence (@gr_eq G).
Proof.
apply gr_equiv.
Show Proof.
Qed.

Theorem Im_mem_compat {G H} : ∀ f (x y : gr_set H),
  (x = y)%G
  → (∃ a, a ∈ G ∧ (H_app f a = x)%G)
  → ∃ a, a ∈ G ∧ (H_app f a = y)%G.
intros * Hxy (z, Hz).
exists z.
split; [ easy | ].
eapply gr_eq_trans; [ apply Hz | easy ].
Qed.

Definition Im {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero;
     gr_eq := @gr_eq H;
     gr_mem := λ b, ∃ a, a ∈ G ∧ H_app f a ≡ b;
     gr_add := @gr_add H;
     gr_opp := @gr_opp H;
     gr_zero_mem := Im_zero_mem f;
     gr_add_mem := Im_add_mem f;
     gr_add_0_l := gr_add_0_l H;
     gr_add_assoc := gr_add_assoc H;
     gr_opp_mem := Im_opp_mem f;
     gr_add_opp_r := gr_add_opp_r H;
     gr_add_comm := gr_add_comm H;
     gr_equiv := gr_equiv H;
     gr_mem_compat := Im_mem_compat f;
     gr_add_compat := gr_add_compat H;
     gr_opp_compat := gr_opp_compat H |}.

Theorem Ker_zero_mem {G H} : ∀ (f : HomGr G H), 0%G ∈ G ∧ (H_app f 0 = 0)%G.
Proof.
intros f.
split; [ apply gr_zero_mem | apply H_zero ].
Qed.

Theorem Ker_add_mem {G H} : ∀ (f : HomGr G H) (x y : gr_set G),
  x ∈ G ∧ (H_app f x = 0)%G
  → y ∈ G ∧ (H_app f y = 0)%G → (x + y)%G ∈ G ∧ (H_app f (x + y) = 0)%G.
Proof.
intros f x x' (Hx, Hfx) (Hx', Hfx').
split; [ now apply gr_add_mem | ].
eapply gr_eq_trans; [ now apply H_lin | ].
eapply gr_eq_trans; [ | apply gr_add_0_l ].
now apply gr_add_compat.
Qed.

Theorem Ker_opp_mem {G H} : ∀ (f : HomGr G H) (x : gr_set G),
  x ∈ G ∧ (H_app f x = 0)%G → (- x)%G ∈ G ∧ (H_app f (- x) = 0)%G.
Proof.
intros f x (Hx & Hfx).
split.
+now apply gr_opp_mem.
+eapply gr_eq_trans; [ now apply H_opp | ].
 eapply gr_eq_trans; [ apply gr_opp_compat, Hfx | ].
 apply gr_opp_zero.
Qed.

Theorem Ker_mem_compat {G H} : ∀ (f : HomGr G H) x y,
  (x = y)%G → x ∈ G ∧ (H_app f x = 0)%G → y ∈ G ∧ (H_app f y = 0)%G.
Proof.
intros * Hxy (ax, Hx).
split.
-eapply gr_mem_compat; [ apply Hxy | easy ].
-eapply gr_eq_trans; [ | apply Hx ].
 apply gr_eq_symm.
 apply H_compat; [ easy | | easy ].
 eapply gr_mem_compat; [ apply Hxy | easy ].
Qed.

Definition Ker {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set G;
     gr_zero := gr_zero;
     gr_eq := @gr_eq G;
     gr_mem := λ a, a ∈ G ∧ H_app f a ≡ gr_zero;
     gr_add := @gr_add G;
     gr_opp := @gr_opp G;
     gr_zero_mem := Ker_zero_mem f;
     gr_add_mem := Ker_add_mem f;
     gr_add_0_l := gr_add_0_l G;
     gr_add_assoc := gr_add_assoc G;
     gr_opp_mem := Ker_opp_mem f;
     gr_add_opp_r := gr_add_opp_r G;
     gr_add_comm := gr_add_comm G;
     gr_equiv := gr_equiv G;
     gr_mem_compat := Ker_mem_compat f;
     gr_add_compat := gr_add_compat G;
     gr_opp_compat := gr_opp_compat G |}.

Definition gr_sub {G} (x y : gr_set G) := gr_add x (gr_opp y).

(* x ∈ coKer f ↔ x ∈ H/Im f
   quotient group is H with setoid, i.e. set with its own equality *)

Definition coKer_eq {G H} (f : HomGr G H) x y := x ∉ H ∨ y ∉ H ∨ (x - y)%G ∈ Im f.

(*
Theorem coKer_is_abelian_group {G H} : ∀ (f : HomGr G H),
  is_abelian_group (coKer_eq f) (@gr_opp H).
Proof.
intros.
split.
...
-intros x y Hxy.
 now apply gr_opp_compat.
...
(*
-intros * Hxy (ax, Hx).
 split.
 +eapply gr_mem_compat; [ apply Hxy | easy ].
 +eapply gr_eq_trans; [ | apply Hx ].
  apply gr_eq_symm.
  apply H_compat; [ easy | | easy ].
  eapply gr_mem_compat; [ apply Hxy | easy ].
*)
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
*)

Theorem coKer_add_0_l {G H} : ∀ (f : HomGr G H) x, coKer_eq f (0 + x)%G x.
Proof.
intros.
unfold coKer_eq.
right; right.
exists 0%G.
split; [ apply gr_zero_mem | ].
eapply gr_eq_trans; [ apply H_zero | ].
apply gr_eq_symm.
eapply gr_eq_trans; [ apply gr_add_assoc | ].
eapply gr_eq_trans; [ apply gr_add_0_l | ].
apply gr_add_opp_r.
Qed.

Theorem coKer_add_assoc {G H} : ∀ (f : HomGr G H) x y z,
  coKer_eq f (x + y + z)%G (x + (y + z))%G.
Proof.
intros.
unfold coKer_eq.
right; right.
exists 0%G.
split; [ apply gr_zero_mem | ].
eapply gr_eq_trans; [ apply H_zero | ].
apply gr_eq_symm.
...
eapply gr_eq_trans; [ apply gr_add_assoc | ].
eapply gr_eq_trans; [ apply gr_add_0_l | ].
apply gr_add_opp_r.


exists gr_zero.
 right; right.
 split; [ apply gr_zero_mem | simpl ].
 set (t := gr_add (@gr_add H x y) z).
 apply gr_eq_trans with (y := gr_add t (gr_opp t)); subst t.
 +apply gr_add_compat; [ apply gr_eq_refl | ].
  now apply gr_opp_compat, gr_eq_symm, gr_add_assoc.
 +apply gr_add_opp_r.
*)

(*
coKer_?
-intros x.
 exists gr_zero.
 right; right.
 split; [ apply gr_zero_mem | simpl ].
 apply gr_eq_trans with (y := gr_add gr_zero gr_zero).
 +apply gr_add_compat; [ now apply gr_add_opp_r | ].
  apply gr_opp_zero.
 +apply gr_add_0_l.
*)

(*
coKer_add_comm
-intros x y.
 exists gr_zero.
 right; right.
 split; [ apply gr_zero_mem | ].
 apply gr_eq_trans with (y := gr_sub (gr_add x y) (gr_add x y)).
 *simpl; apply gr_add_compat; [ apply gr_eq_refl | ].
  now apply gr_opp_compat, gr_add_comm.
 *simpl; apply gr_add_opp_r.
*)

(*
coKer_equiv
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
*)

(*
coKer_add_compat.
-intros x y x' y' (Hx & Hy & z & Hz & Hxy) (Hx' & Hy' & z' & Hz' & Hxy').
 split; [ | split ]; [ now apply gr_add_mem | now apply gr_add_mem | ].
 exists (z - z')%G.
 split.
 +apply gr_add_mem; [ easy | now apply gr_opp_mem ].
 +idtac.
*)

Definition coKer {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero;
     gr_eq := coKer_eq f;
     gr_mem := gr_mem H;
     gr_add := @gr_add H;
     gr_opp := @gr_opp H;
     gr_zero_mem := @gr_zero_mem H;
     gr_add_mem := @gr_add_mem H;
     gr_add_0_l := coKer_add_0_l f;
     gr_add_assoc := coKer_add_assoc f;
     gr_opp_mem := Ker_opp_mem f;
     gr_add_opp_r := gr_add_opp_r G;
     gr_add_comm := gr_add_comm G;
     gr_equiv := gr_equiv G;
     gr_mem_compat := Ker_mem_compat f;
     gr_add_compat := gr_add_compat G;
     gr_opp_compat := gr_opp_compat G |}.

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
