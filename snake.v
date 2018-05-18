(* Snake lemma *)

Require Import Utf8.
Require Import Classes.RelationClasses.
Require Import Setoid.
Require ClassicalChoice.

Reserved Notation "x '∈' S" (at level 60).
Reserved Notation "x '≡' y" (at level 70).

(* Abelian Groups.

   Note: group sets are setoids, i.e. there is a specific equality (gr_eq)
   which must be compatible with membership (gr_mem_compat), with addition
   (gr_add_compat), and with inverse (gr_inv_compat). This allows to define
   groups quotients by changing this equality, e.g. in cokernels *)

Record AbGroup :=
  { (* data *)
    gr_set : Type;
    gr_mem : gr_set → Prop where "x ∈ G" := (gr_mem x);
    gr_eq : gr_set → gr_set → Prop where "x ≡ y" := (gr_eq x y);
    gr_zero : gr_set where "0" := (gr_zero);
    gr_add : gr_set → gr_set → gr_set where "x + y" := (gr_add x y);
    gr_inv : gr_set → gr_set where "- x" := (gr_inv x);
    (* properties *)
    gr_zero_mem : 0 ∈ G;
    gr_add_mem : ∀ x y, x ∈ G → y ∈ G → x + y ∈ G;
    gr_add_0_l : ∀ x, 0 + x ≡ x;
    gr_add_assoc : ∀ x y z, (x + y) + z ≡ x + (y + z);
    gr_inv_mem : ∀ x, x ∈ G → - x ∈ G;
    gr_add_inv_r : ∀ x, x + (- x) ≡ 0;
    gr_add_comm : ∀ x y, x + y ≡ y + x;
    gr_equiv : Equivalence gr_eq;
    gr_mem_compat : ∀ x y, x ≡ y → x ∈ G → y ∈ G;
    gr_add_compat : ∀ x y x' y', x ≡ y → x' ≡ y' → x + x' ≡ y + y';
    gr_inv_compat : ∀ x y, x ≡ y → - x ≡ - y }.

Arguments gr_eq [_].
Arguments gr_zero [_].
Arguments gr_add [_].
Arguments gr_inv [_].
Arguments gr_zero_mem G : rename.
Arguments gr_add_mem G : rename.
Arguments gr_add_0_l G : rename.
Arguments gr_add_assoc G : rename.
Arguments gr_inv_mem G : rename.
Arguments gr_add_inv_r G : rename.
Arguments gr_add_comm G : rename.
Arguments gr_equiv G : rename.
Arguments gr_mem_compat G : rename.
Arguments gr_add_compat G : rename.
Arguments gr_inv_compat G : rename.

Notation "x '∈' S" := (gr_mem S x) (at level 60).
Notation "x '∉' S" := (¬ gr_mem S x) (at level 60).
Notation "x '≡' y" := (gr_eq x y) (at level 70).

Delimit Scope group_scope with G.

Notation "0" := (gr_zero) : group_scope.
Notation "a = b" := (gr_eq a b) : group_scope.
Notation "a ≠ b" := (¬ gr_eq a b) : group_scope.
Notation "a + b" := (gr_add a b) : group_scope.
Notation "a - b" := (gr_add a (gr_inv b)) : group_scope.
Notation "- a" := (gr_inv a) : group_scope.

Axiom MemDec : ∀ G x, {x ∈ G} + {x ∉ G}.

Record HomGr (A B : AbGroup) :=
  { H_app : gr_set A → gr_set B;
    H_mem_compat : ∀ x, x ∈ A → H_app x ∈ B;
    H_linear : ∀ x y, x ∈ A → y ∈ A → (H_app (x + y) = H_app x + H_app y)%G;
    H_compat : ∀ x y, x ∈ A → y ∈ A → (x = y)%G → (H_app x = H_app y)%G }.

Arguments H_app [A] [B].
Arguments H_mem_compat _ _ f : rename.
Arguments H_linear _ _ f : rename.
Arguments H_compat _ _ f : rename.

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

Theorem gr_add_inv_l : ∀ G (x : gr_set G), (- x + x = 0)%G.
Proof.
intros.
eapply gr_eq_trans; [ apply gr_add_comm | ].
apply gr_add_inv_r.
Qed.

Theorem gr_inv_zero : ∀ G, (- 0 = @gr_zero G)%G.
Proof.
intros.
specialize (@gr_add_inv_r G gr_zero) as H1.
specialize (@gr_add_0_l G (gr_inv gr_zero)) as H3.
eapply gr_eq_trans; [ | apply H1 ].
now apply gr_eq_symm.
Qed.

Theorem gr_sub_move_r : ∀ G (x y z : gr_set G),
  (x - y = z)%G ↔ (x = z + y)%G.
Proof.
intros.
split; intros Hxyz.
-apply gr_eq_trans with (y := ((x - y) + y)%G).
 +apply gr_eq_symm.
  eapply gr_eq_trans; [ apply gr_add_assoc | ].
  apply gr_eq_trans with (y := (x + 0)%G).
  *apply gr_add_compat; [ apply gr_eq_refl | apply gr_add_inv_l ].
  *apply gr_add_0_r.
 +apply gr_add_compat; [ easy | apply gr_eq_refl ].
-apply gr_eq_trans with (y := (z + y - y)%G).
 +apply gr_add_compat; [ easy | apply gr_eq_refl ].
 +eapply gr_eq_trans; [ apply gr_add_assoc | ].
  apply gr_eq_trans with (y := (z + 0)%G).
  *apply gr_add_compat; [ apply gr_eq_refl | apply gr_add_inv_r ].
  *apply gr_add_0_r.
Qed.

Theorem gr_sub_move_l : ∀ G (x y z : gr_set G),
  (x - y = z)%G ↔ (x = y + z)%G.
Proof.
intros.
split; intros Hxyz.
-apply gr_eq_symm.
 eapply gr_eq_trans; [ apply gr_add_comm | ].
 now apply gr_eq_symm, gr_sub_move_r.
-apply gr_sub_move_r.
 eapply gr_eq_trans; [ apply Hxyz | ].
 apply gr_add_comm.
Qed.

Theorem gr_inv_add_distr : ∀ G (x y : gr_set G), (- (x + y) = - x - y)%G.
Proof.
intros *.
apply gr_eq_symm.
apply gr_sub_move_r.
eapply gr_eq_trans.
-apply gr_eq_symm, gr_add_0_l.
-apply gr_sub_move_r.
 apply gr_eq_symm.
 eapply gr_eq_trans; [ apply gr_add_assoc | ].
 apply gr_eq_trans with (y := (- (x + y) + (x + y))%G).
 +apply gr_add_compat; [ apply gr_eq_refl | apply gr_add_comm ].
 +apply gr_add_inv_l.
Qed.

Theorem gr_inv_inv : ∀ G (x : gr_set G), (- - x = x)%G.
Proof.
intros.
apply gr_eq_trans with (y := (- - x + (- x + x))%G).
-apply gr_eq_symm.
 apply gr_eq_trans with (y := (- - x + 0)%G).
 +apply gr_add_compat; [ apply gr_eq_refl | apply gr_add_inv_l ].
 +apply gr_add_0_r.
-eapply gr_eq_trans; [ apply gr_eq_symm, gr_add_assoc | ].
 eapply gr_eq_trans; [ | apply gr_add_0_l ].
 apply gr_add_compat; [ apply gr_add_inv_l | apply gr_eq_refl ].
Qed.

Theorem H_zero : ∀ A B (f : HomGr A B), (H_app f 0 = 0)%G.
Proof.
intros.
assert (H1 : (@gr_zero A + 0 = 0)%G) by apply A.
assert (H2 : (H_app f 0 + H_app f 0 = H_app f 0)%G). {
  eapply gr_eq_trans; [ apply gr_eq_symm, f; apply A | ].
  apply f; [ apply A; apply A | apply A | apply A ].
}
assert (H3 : (H_app f 0 + H_app f 0 - H_app f 0 = H_app f 0 - H_app f 0)%G). {
  apply gr_add_compat; [ apply H2 | apply gr_eq_refl ].
}
assert (H4 : (H_app f 0 + H_app f 0 - H_app f 0 = 0)%G). {
  eapply gr_eq_trans; [ apply H3 | apply B ].
}
eapply gr_eq_trans; [ | apply H4 ].
apply gr_eq_symm.
eapply gr_eq_trans; [ apply gr_add_assoc | ].
eapply gr_eq_trans; [ | apply gr_add_0_r ].
apply gr_add_compat; [ apply gr_eq_refl | apply B ].
Qed.

Theorem H_inv : ∀ A B (f : HomGr A B) x,
  x ∈ A → (H_app f (- x) = - H_app f x)%G.
Proof.
intros * Hx.
assert (H1 : (x - x = 0)%G) by apply A.
assert (H2 : (H_app f (x - x) = H_app f 0)%G). {
  apply H_compat; [ now apply A, A | apply A | apply H1 ].
}
assert (H3 : (H_app f x + H_app f (- x) = H_app f 0)%G). {
  eapply gr_eq_trans; [ | apply H2 ].
  apply gr_eq_symm, H_linear; [ easy | now apply A ].
}
assert (H4 : (H_app f x + H_app f (- x) = 0)%G). {
  eapply gr_eq_trans; [ apply H3 | apply H_zero ].
}
apply gr_eq_trans with (y := (0 - H_app f x)%G).
-now apply gr_eq_symm, gr_sub_move_l, gr_eq_symm.
-apply gr_add_0_l.
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
      gr_inv x := x;
      gr_zero_mem := I;
      gr_add_mem _ _ _ _ := I;
      gr_add_0_l := Gr0_add_0_l;
      gr_add_assoc _ _ _ := eq_refl G0;
      gr_inv_mem _ H := H;
      gr_add_inv_r _ := eq_refl;
      gr_add_comm _ _ := eq_refl G0;
      gr_equiv := eq_equivalence;
      gr_mem_compat _ _ _ _ := I;
      gr_add_compat _ _ _ _ _ _ := eq_refl;
      gr_inv_compat _ _ H := H |}.

Definition is_initial (G : AbGroup) :=
  ∀ H (f g : HomGr G H) (x : gr_set G), H_app f x ≡ H_app g x.
Definition is_final (G : AbGroup) :=
  ∀ H (f g : HomGr H G) (x : gr_set H), H_app f x ≡ H_app g x.
Definition is_null (G : AbGroup) := is_initial G ∧ is_final G.

Theorem is_null_Gr0 : is_null Gr0.
Proof.
split; intros H f g x.
-destruct x.
 apply gr_eq_trans with (y := gr_zero); [ apply H_zero | ].
 apply gr_eq_symm, H_zero.
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
eapply gr_eq_trans; [ now apply H_linear | ].
apply gr_eq_trans with (y := gr_add y y').
+now apply gr_add_compat.
+apply gr_eq_refl.
Qed.

Theorem Im_inv_mem {G H} : ∀ (f : HomGr G H) (x : gr_set H),
  (∃ a : gr_set G, a ∈ G ∧ (H_app f a = x)%G)
  → ∃ a : gr_set G, a ∈ G ∧ (H_app f a = - x)%G.
Proof.
intros f x (y & Hy & Hyx).
exists (gr_inv y).
split; [ now apply gr_inv_mem | ].
apply gr_eq_trans with (y := gr_inv (H_app f y)).
+now apply H_inv.
+now apply gr_inv_compat.
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
     gr_inv := @gr_inv H;
     gr_zero_mem := Im_zero_mem f;
     gr_add_mem := Im_add_mem f;
     gr_add_0_l := gr_add_0_l H;
     gr_add_assoc := gr_add_assoc H;
     gr_inv_mem := Im_inv_mem f;
     gr_add_inv_r := gr_add_inv_r H;
     gr_add_comm := gr_add_comm H;
     gr_equiv := gr_equiv H;
     gr_mem_compat := Im_mem_compat f;
     gr_add_compat := gr_add_compat H;
     gr_inv_compat := gr_inv_compat H |}.

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
eapply gr_eq_trans; [ now apply H_linear | ].
eapply gr_eq_trans; [ | apply gr_add_0_l ].
now apply gr_add_compat.
Qed.

Theorem Ker_inv_mem {G H} : ∀ (f : HomGr G H) (x : gr_set G),
  x ∈ G ∧ (H_app f x = 0)%G → (- x)%G ∈ G ∧ (H_app f (- x) = 0)%G.
Proof.
intros f x (Hx & Hfx).
split.
+now apply gr_inv_mem.
+eapply gr_eq_trans; [ now apply H_inv | ].
 eapply gr_eq_trans; [ apply gr_inv_compat, Hfx | ].
 apply gr_inv_zero.
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
     gr_inv := @gr_inv G;
     gr_zero_mem := Ker_zero_mem f;
     gr_add_mem := Ker_add_mem f;
     gr_add_0_l := gr_add_0_l G;
     gr_add_assoc := gr_add_assoc G;
     gr_inv_mem := Ker_inv_mem f;
     gr_add_inv_r := gr_add_inv_r G;
     gr_add_comm := gr_add_comm G;
     gr_equiv := gr_equiv G;
     gr_mem_compat := Ker_mem_compat f;
     gr_add_compat := gr_add_compat G;
     gr_inv_compat := gr_inv_compat G |}.

Definition gr_sub {G} (x y : gr_set G) := gr_add x (gr_inv y).

(* x ∈ Coker f ↔ x ∈ H/Im f
   quotient group is H with setoid, i.e. set with its own equality *)

Definition Coker_eq {G H} (f : HomGr G H) x y := (x - y)%G ∈ Im f.

Theorem Coker_add_0_l {G H} : ∀ (f : HomGr G H) x, Coker_eq f (0 + x)%G x.
Proof.
intros.
unfold Coker_eq.
exists 0%G.
split; [ apply gr_zero_mem | ].
eapply gr_eq_trans; [ apply H_zero | ].
apply gr_eq_symm.
simpl in x; simpl.
eapply gr_eq_trans; [ apply gr_add_assoc | ].
eapply gr_eq_trans; [ apply gr_add_0_l | ].
apply gr_add_inv_r.
Qed.

Theorem Coker_add_assoc {G H} : ∀ (f : HomGr G H) x y z,
  Coker_eq f (x + y + z)%G (x + (y + z))%G.
Proof.
intros.
unfold Coker_eq.
exists 0%G.
split; [ apply gr_zero_mem | ].
eapply gr_eq_trans; [ apply H_zero | ].
apply gr_eq_symm.
simpl in x, y, z; simpl.
apply gr_sub_move_r, gr_eq_symm.
eapply gr_eq_trans; [ apply gr_add_0_l | ].
apply gr_eq_symm, gr_add_assoc.
Qed.

Theorem Coker_add_inv_r {G H} : ∀ (f : HomGr G H) x, Coker_eq f (x - x)%G 0%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | ].
eapply gr_eq_trans; [ apply H_zero | ].
apply gr_eq_symm.
simpl.
apply gr_eq_trans with (y := (0 - 0)%G).
-apply gr_add_compat; [ apply gr_add_inv_r | apply gr_eq_refl ].
-apply gr_add_inv_r.
Qed.

Theorem Coker_add_comm {G H} : ∀ (f : HomGr G H) x y,
  Coker_eq f (x + y)%G (y + x)%G.
Proof.
intros.
exists 0%G.
split; [ apply gr_zero_mem | ].
eapply gr_eq_trans; [ apply H_zero | ].
apply gr_eq_symm.
simpl.
apply gr_sub_move_r.
eapply gr_eq_trans; [ apply gr_add_comm | ].
apply gr_eq_symm.
eapply gr_eq_trans; [ apply gr_add_0_l | apply gr_eq_refl ].
Qed.

Theorem Coker_equiv {G H} : ∀ (f : HomGr G H), Equivalence (Coker_eq f).
Proof.
intros.
unfold Coker_eq; split.
-intros x.
 exists 0%G.
 split; [ apply gr_zero_mem | ].
 eapply gr_eq_trans; [ apply H_zero | ].
 simpl.
 apply gr_eq_symm, gr_add_inv_r.
-intros x y Hxy.
 destruct Hxy as (z & Hz).
 exists (- z)%G.
 split; [ now apply gr_inv_mem | ].
 eapply gr_eq_trans; [ now apply H_inv | ].
 apply gr_eq_trans with (y := (- (x - y))%G).
 +now simpl; apply gr_inv_compat.
 +simpl; eapply gr_eq_trans; [ apply gr_inv_add_distr | ].
  eapply gr_eq_trans; [ apply gr_add_comm | ].
  apply gr_add_compat; [ | apply gr_eq_refl ].
  apply gr_inv_inv.
-intros x y z Hxy Hyz.
 simpl in Hxy, Hyz.
 destruct Hxy as (t, Ht).
 destruct Hyz as (u, Hu).
 exists (t + u)%G.
 split; [ now apply gr_add_mem | ].
 eapply gr_eq_trans; [ now apply H_linear | ].
 apply gr_eq_trans with (y := (x - y + (y - z))%G).
 +now simpl; apply gr_add_compat.
 +simpl; eapply gr_eq_trans; [ apply gr_add_assoc | ].
  apply gr_add_compat; [ apply gr_eq_refl | ].
  eapply gr_eq_trans; [ apply gr_eq_symm, gr_add_assoc | ].
  apply gr_eq_trans with (y := (0 - z)%G).
  *simpl; apply gr_add_compat; [ apply gr_add_inv_l | apply gr_eq_refl ].
  *simpl; apply gr_add_0_l.
Qed.

Theorem Coker_mem_compat {G H} : ∀ (f : HomGr G H) x y,
  Coker_eq f x y → x ∈ H → y ∈ H.
Proof.
intros * Heq Hx.
destruct Heq as (z, Hz).
apply gr_mem_compat with (x := (x - H_app f z)%G).
-apply gr_eq_trans with (y := (x - (x - y))%G); simpl.
 +apply gr_add_compat; [ apply gr_eq_refl | ].
  now apply gr_inv_compat.
 +apply gr_sub_move_r, gr_eq_symm.
  eapply gr_eq_trans; [ apply gr_add_comm | ].
  eapply gr_eq_trans; [ apply gr_add_assoc | ].
  apply gr_eq_trans with (y := (x + 0)%G); simpl.
  *apply gr_add_compat; [ apply gr_eq_refl | apply gr_add_inv_l ].
  *apply gr_add_0_r.
-simpl; apply gr_add_mem; [ easy | ].
 apply gr_inv_mem.
 now apply f.
Qed.

Theorem Coker_add_compat {G H} : ∀ (f : HomGr G H) x y x' y',
  Coker_eq f x y → Coker_eq f x' y' → Coker_eq f (x + x')%G (y + y')%G.
Proof.
intros f x y x' y' (z & Hz & Hfz) (z' & Hz' & Hfz').
exists (z + z')%G.
split.
-now apply gr_add_mem.
-eapply gr_eq_trans; [ now apply f | ].
 apply gr_eq_trans with (y := ((x - y) + (x' - y'))%G); simpl.
 +now apply gr_add_compat.
 +eapply gr_eq_trans; [ apply gr_add_assoc | apply gr_eq_symm ].
  eapply gr_eq_trans; [ apply gr_add_assoc | apply gr_eq_symm ].
  apply gr_add_compat; [ apply gr_eq_refl | ].
  eapply gr_eq_trans; [ apply gr_add_comm | ].
  eapply gr_eq_trans; [ apply gr_add_assoc | ].
  apply gr_add_compat; [ apply gr_eq_refl | ].
  eapply gr_eq_trans; [ apply gr_add_comm | ].
  apply gr_eq_symm, gr_inv_add_distr.
Qed.

Theorem Coker_inv_compat {G H} :∀ (f : HomGr G H) x y,
  Coker_eq f x y → Coker_eq f (- x)%G (- y)%G.
Proof.
intros * (z & Hz & Hfz).
unfold Coker_eq; simpl.
exists (- z)%G.
split; [ now apply gr_inv_mem | ].
eapply gr_eq_trans; [ now apply H_inv | ].
apply gr_eq_trans with (y := (- (x - y))%G); simpl.
-now apply gr_inv_compat.
-apply gr_inv_add_distr.
Qed.

Definition Coker {G H : AbGroup} (f : HomGr G H) :=
  {| gr_set := gr_set H;
     gr_zero := gr_zero;
     gr_eq := Coker_eq f;
     gr_mem := gr_mem H;
     gr_add := @gr_add H;
     gr_inv := @gr_inv H;
     gr_zero_mem := @gr_zero_mem H;
     gr_add_mem := @gr_add_mem H;
     gr_add_0_l := Coker_add_0_l f;
     gr_add_assoc := Coker_add_assoc f;
     gr_inv_mem := gr_inv_mem H;
     gr_add_inv_r := Coker_add_inv_r f;
     gr_add_comm := Coker_add_comm f;
     gr_equiv := Coker_equiv f;
     gr_mem_compat := Coker_mem_compat f;
     gr_add_compat := Coker_add_compat f;
     gr_inv_compat := Coker_inv_compat f |}.

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

Theorem KK_mem_compat {A B A' B'} : ∀ (a : HomGr A A') (b : HomGr B B') f f',
  diagram_commutes f a b f'
  → ∀ x : gr_set (Ker a), x ∈ Ker a → H_app f x ∈ Ker b.
intros * Hc * Hx.
split; [ now apply f; simpl in Hx | ].
eapply gr_eq_trans; [ apply Hc | ].
apply gr_eq_trans with (y := H_app f' 0%G).
-apply f'; [ apply a, Hx | apply A' | apply Hx ].
-apply H_zero.
Qed.

Theorem KK_lin {A B A'} : ∀ (f : HomGr A B) (a : HomGr A A'),
  ∀ x y : gr_set (Ker a),
  x ∈ Ker a → y ∈ Ker a → (H_app f (x + y) = H_app f x + H_app f y)%G.
Proof.
intros * Hx Hx'; simpl in Hx, Hx'.
now apply f.
Qed.

Theorem KK_compat {A B A'} : ∀ (f : HomGr A B) (a : HomGr A A'),
  ∀ x y : gr_set (Ker a),
  x ∈ Ker a → y ∈ Ker a → (x = y)%G → (H_app f x = H_app f y)%G.
Proof.
intros * Hx Hy Hxy.
simpl in Hx, Hy.
now apply f.
Qed.

Definition HomGr_Ker_Ker {A B A' B'}
    (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B')
    (Hc : diagram_commutes f a b f') :=
  {| H_app (x : gr_set (Ker a)) := H_app f x : gr_set (Ker b);
     H_mem_compat := KK_mem_compat a b f f' Hc;
     H_linear := KK_lin f a;
     H_compat := KK_compat f a |}.

Theorem CC_mem_compat {A B A' B'} :
  ∀ (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  ∀ x : gr_set (Coker a), x ∈ Coker a → H_app f' x ∈ Coker b.
Proof.
intros * Hx.
now apply f'.
Qed.

Theorem CC_lin {A B A' B'} :
  ∀ (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  ∀ x y : gr_set (Coker a), x ∈ Coker a → y ∈ Coker a
  → @gr_eq (Coker b) (H_app f' (x + y))%G (H_app f' x + H_app f' y)%G.
Proof.
intros * Hx Hy; simpl in Hx, Hy.
exists 0%G.
split; [ apply B | ].
eapply gr_eq_trans; [ apply H_zero | apply B' ].
simpl; apply gr_sub_move_r.
apply B'.
eapply gr_eq_trans; [ apply gr_add_0_l | ].
now apply B', f'.
Qed.

Theorem CC_compat {A B A' B'} :
  ∀ (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B'),
  diagram_commutes f a b f'
  → ∀ x y : gr_set (Coker a),
  x ∈ Coker a → y ∈ Coker a → (x = y)%G
  → @gr_eq (Coker b) (H_app f' x) (H_app f' y)%G.
Proof.
intros * Hc * Hx Hy Hxy.
simpl in Hx, Hy, x, y, Hxy; simpl.
destruct Hxy as (z & Hz & Haz).
simpl; unfold Coker_eq; simpl.
exists (H_app f z).
split; [ now apply f | ].
eapply gr_eq_trans; [ apply Hc | ].
apply gr_eq_trans with (y := H_app f' (x - y)%G).
-apply H_compat; [ now apply a | | easy ].
 apply A'; [ easy | now apply A' ].
-eapply gr_eq_trans.
 +apply f'; [ easy | now apply A' ].
 +apply gr_add_compat; [ apply gr_eq_refl | now apply H_inv ].
Qed.

Definition HomGr_Coker_Coker {A B A' B'}
    (f : HomGr A B) (f' : HomGr A' B') (a : HomGr A A') (b : HomGr B B')
    (Hc : diagram_commutes f a b f') :=
  {| H_app (x : gr_set (Coker a)) := H_app f' x : gr_set (Coker b);
     H_mem_compat := CC_mem_compat f' a b;
     H_linear := CC_lin f' a b;
     H_compat := CC_compat f f' a b Hc |}.

Theorem exists_ker_C_to_B : ∀ B C C' g (c : HomGr C C') (cz : HomGr C Gr0),
  (∀ a : gr_set (Im g), a ∈ Im g ↔ a ∈ Ker cz)
  → ∀ x : gr_set (Ker c), ∃ y, x ∉ C ∨ y ∈ B ∧ H_app g y ≡ x.
Proof.
intros * sg x.
destruct (MemDec C x) as [H2| H2]; [ | now exists 0%G; left ].
enough (H : x ∈ Im g). {
  simpl in H.
  destruct H as (y & Hy & Hyx).
  exists y; right; easy.
}
apply sg.
split; [ easy | ].
simpl in x; simpl.
destruct cz as (appcz, czin, czlin, czcomp).
simpl.
now destruct (appcz x).
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
        (fk' : HomGr (Coker a) (Coker b)) (gk' : HomGr (Coker b) (Coker c)),
     ∃ (d : HomGr (Ker c) (Coker a)),
        exact_sequence (Seq2 fk (Seq2 gk (Seq2 d (Seq2 fk' (Seq2 gk' Seq1))))).
Proof.
intros *.
intros Hcff' Hcgg' s s'.
exists (HomGr_Ker_Ker f f' a b Hcff').
exists (HomGr_Ker_Ker g g' b c Hcgg').
exists (HomGr_Coker_Coker f f' a b Hcff').
exists (HomGr_Coker_Coker g g' b c Hcgg').
destruct s as (sf & sg & _).
destruct s' as (sf' & sg' & _).
specialize (exists_ker_C_to_B B C C' g c cz sg) as H1.
specialize (ClassicalChoice.choice _ H1) as (g₁, Hg₁).
assert
  (Hf'inj :
  ∀ x y, x ∈ A' → y ∈ A' → (H_app f' x = H_app f' y)%G → (x = y)%G). {
  intros * Hx Hy Hxy.
  (* it is because Im(cza')={0}=Ker(f') *)
  assert (H2 : (H_app f' x - H_app f' y = 0)%G). {
    apply gr_sub_move_r.
    eapply gr_eq_trans; [ apply Hxy | ].
    apply gr_eq_symm, gr_add_0_l.
  }
  assert (H3 : (H_app f' (x - y) = 0)%G). {
    eapply gr_eq_trans; [ | apply H2 ].
    eapply gr_eq_trans.
    -apply H_linear; [ easy | now apply A' ].
    -apply gr_add_compat; [ apply gr_eq_refl | now apply H_inv ].
  }
  assert (H4 : (x - y)%G ∈ Ker f'). {
    split; [ | apply H3 ].
    apply A'; [ easy | now apply A' ].
  }
  apply sf' in H4.
  simpl in H4.
  destruct H4 as (z & _ & H4).
  destruct z.
  assert (H5 : (x - y = 0)%G). {
    eapply gr_eq_trans; [ apply gr_eq_symm, H4 | ].
    apply H_zero.
  }
  apply gr_sub_move_r in H5.
  eapply gr_eq_trans; [ apply H5 | ].
  apply gr_add_0_l.
}
assert (H7 : ∀ x, x ∈ C → g₁ x ∈ B). {
  intros z Hz; specialize (Hg₁ z) as H; now destruct H.
}
assert (H5 : ∀ x, x ∈ Ker c → (H_app g' (H_app b (g₁ x)) = 0)%G). {
  intros z Hz.
  specialize (Hg₁ z) as H5.
  destruct H5 as [H5| H5]; [ now simpl in Hz | ].
  eapply gr_eq_trans.
  -apply gr_eq_symm, Hcgg'.
  -apply gr_eq_trans with (y := H_app c z).
   +apply H_compat; [ now apply g | now simpl in Hz | easy ].
   +now simpl in Hz.
}
assert (H2 : ∀ y', ∃ z', y' ∉ Im b ∨ z' ∈ Coker a ∧ (H_app f' z' = y')%G). {
  intros y'.
  destruct (MemDec (Im b) y') as [Hy'| Hy'].
  -assert (H2 : y' ∈ Im f'). {
     apply sg'; simpl.
     destruct Hy' as (y & Hy & Hyy').
     assert (H2 : y' ∈ B'). {
       eapply B'; [ apply Hyy' | now apply b ].
     }
     split; [ easy | ].
     apply gr_eq_trans with (y := H_app g' (H_app b y)).
     -apply g'; [ easy | now apply b | now apply gr_eq_symm ].
     -eapply gr_eq_trans; [ apply gr_eq_symm, Hcgg' | ].
      assert (H3 : (H_app g y = H_app g (g₁ (H_app g y)))%G). {
        apply gr_eq_symm.
        specialize (Hg₁ (H_app g y)) as H3.
        destruct H3 as [H3| H3]; [ | easy ].
        exfalso; apply H3; now apply g.
      }
      eapply gr_eq_trans.
      +apply H_compat; [ | | apply H3 ].
       *now apply g.
       *now apply g, H7, g.
      +idtac.
(* ah bin non, H5 ne marche que pour Ker c, pas pour C *)
...
      +eapply gr_eq_trans; [ apply Hcgg' | ].
       apply H5.
simpl.
...
assert
  (H2 : ∀ z, ∃ x', z ∉ Ker c ∨
        x' ∈ Coker a ∧ (H_app f' x' = H_app b (g₁ z))%G). {
  intros z.
  destruct (MemDec (Ker c) z) as [Hz| Hz].
  -specialize (H1 z) as (y & Hy).
   destruct Hy as [Hy| Hy].
   +exists 0%G; left; simpl; easy.
   +assert (H2 : H_app b (g₁ z) ∈ Im f'). {
      apply sg'; simpl.
      split.
      -apply b.
       specialize (Hg₁ z) as H2.
       destruct H2 as [H2| H2]; [ now simpl in Hz | easy ].
      -eapply gr_eq_trans; [ apply gr_eq_symm, Hcgg' | ].
       specialize (Hg₁ z) as H2.
       destruct H2 as [H2| H2]; [ now simpl in Hz | ].
       destruct H2 as (Hfz & Hgfz).
       apply gr_eq_trans with (y := H_app c z); [ | now simpl in Hz ].
       apply c; [ now apply g | now simpl in Hz | easy ].
    }
    destruct H2 as (x' & Hx').
    exists x'; right.
    split; [ easy | ].
    eapply gr_eq_trans; [ apply Hx' | ].
    apply gr_eq_refl.
  -exists 0%G; now left.
}
specialize (ClassicalChoice.choice _ H2) as (d, Hd).
move d before g₁.
clear H1 H2 (*H2'*).
assert (Hlin : ∀ x y, x ∈ Ker c → y ∈ Ker c → (d (x + y) = d x + d y)%G). {
  intros * Hx Hy.
  specialize (Hd x) as H1.
  destruct H1 as [H1| (Hfx, Hf'x)]; [ easy | ].
  specialize (Hd y) as H2.
  destruct H2 as [H2| (Hfy, Hf'y)]; [ easy | ].
  move Hfy before Hfx.
  enough (H1 : (H_app f' (d (x + y)) = H_app f' (d x + d y))%G). {
    destruct (MemDec A' (d (x + y)%G)) as [H2| H2].
     -apply Hf'inj in H1; [ | easy | ].
      +simpl; unfold Coker_eq; simpl.
       exists 0%G.
       split; [ apply A | ].
       eapply gr_eq_trans; [ apply H_zero | apply gr_eq_symm ].
       apply gr_sub_move_r.
       eapply gr_eq_trans; [ apply H1 | ].
       apply gr_eq_symm, gr_add_0_l.
      +simpl in Hfx, Hfy.
       now apply A'.
     -specialize (Hd (x + y)%G) as H3.
      destruct H3 as [H3| H3]; [ | easy ].
      exfalso; apply H3.
      now apply (Ker c).
  }
  specialize (Hd (x + y)%G) as H1.
  destruct H1 as [H1| H1]; [ exfalso; now apply H1, (Ker c) | ].
  destruct H1 as (Hdxy, Hfd).
  eapply gr_eq_trans; [ apply Hfd | ].
  apply gr_eq_symm.
  assert (H2 : (H_app f' (d x + d y) = H_app f' (d x) + H_app f' (d y))%G). {
    now simpl; apply H_linear.
  }
  eapply gr_eq_trans; [ apply H2 | ].
  eapply gr_eq_trans.
  -apply gr_add_compat; [ apply Hf'x | apply Hf'y ].
  -eapply gr_eq_trans.
   +apply gr_eq_symm, H_linear.
    *specialize (Hg₁ x) as H1.
     destruct H1 as [H1| H1]; [ now simpl in Hx | easy ].
    *specialize (Hg₁ y) as H1.
     destruct H1 as [H1| H1]; [ now simpl in Hy | easy ].
   +specialize (Hg₁ (x + y)%G) as H1.
    simpl in Hx, Hy.
    destruct H1 as [H1| H1]; [ exfalso; now apply H1, C | ].
    specialize (Hg₁ x) as H3.
    destruct H3 as [H3| H3]; [ exfalso; now apply H3 | ].
    specialize (Hg₁ y) as H4.
    destruct H4 as [H4| H4]; [ exfalso; now apply H4 | ].
    assert (H5 : ∀ x, x ∈ Ker c → (H_app g' (H_app b (g₁ x)) = 0)%G). {
... (* already done above *)
      intros z Hz.
      specialize (Hg₁ z) as H5.
      destruct H5 as [H5| H5]; [ now simpl in Hz | ].
      eapply gr_eq_trans.
      -apply gr_eq_symm, Hcgg'.
      -apply gr_eq_trans with (y := H_app c z).
       +apply H_compat; [ now apply g | now simpl in Hz | easy ].
       +now simpl in Hz.
    }
    assert (H6 : (H_app g' (H_app b (g₁ x + g₁ y)) = 0)%G). {
      eapply gr_eq_trans.
      -apply gr_eq_symm, Hcgg'.
      -apply gr_eq_trans with (y := H_app c (x + y)%G).
       +apply H_compat; [ apply g; now apply B | now apply C | ].
        eapply gr_eq_trans.
        *apply H_linear; easy.
        *apply gr_eq_trans with (y := (x + H_app g (g₁ y))%G); simpl.
         apply gr_add_compat; [ easy | apply gr_eq_refl ].
         apply gr_add_compat; [ apply gr_eq_refl | easy ].
       +eapply gr_eq_trans; simpl.
        *now apply H_linear.
        *apply gr_eq_trans with (y := (H_app c x + 0)%G).
        --apply gr_add_compat; [ apply gr_eq_refl | easy ].
        --eapply gr_eq_trans; [ apply gr_add_0_r | easy ].
    }
    eapply gr_eq_trans; [ now apply H_linear | ].
    assert
      (H8 : ∀ y₁ y₂, y₁ ∈ B → y₂ ∈ B →
         (H_app g y₁ = H_app g y₂)%G
         → (H_app b (g₁ (H_app g y₁)) = H_app b (g₁ (H_app g y₂)))%G). {
      clear x y Hy Hfy Hf'y Hdxy Hfd H2 H1 H4 H6 Hx Hfx Hf'x H3.
      intros * Hy₁ Hy₂ Hyy.
exfalso.
      assert (H1 : (y₁ - y₂)%G ∈ Ker g). {
        split.
        -apply B; [ easy | now apply B ].
        -eapply gr_eq_trans.
         +apply g; [ easy | now apply B ].
         +apply gr_eq_symm, gr_sub_move_r.
          eapply gr_eq_trans; [ apply gr_add_0_l | ].
          eapply gr_eq_trans; [ now apply gr_eq_symm, H_inv, B | ].
          apply gr_eq_trans with (y := H_app g y₂).
          *apply g; [ now apply B, B | easy | apply gr_inv_inv ].
          *now apply gr_eq_symm.
      }
      apply sf in H1; simpl in H1.
      destruct H1 as (z & Hz & Hfz).
      assert (H1 : (H_app b (H_app f z) = H_app b (y₁ - y₂))%G). {
        apply b; [ now apply f | | easy ].
        apply B; [ easy | now apply B ].
      }
      assert (H2 : (H_app f' (H_app a z) = H_app b (y₁ - y₂))%G). {
        eapply gr_eq_trans; [ apply gr_eq_symm, Hcff' | easy ].
      }
      assert (H3 : (H_app f' (H_app a z) = H_app b y₁ - H_app b y₂)%G). {
        eapply gr_eq_symm.
        apply gr_eq_trans with (y := (H_app b y₁ + H_app b (- y₂))%G).
        -apply gr_add_compat; [ apply gr_eq_refl | ].
         now apply gr_eq_symm, H_inv.
        -eapply gr_eq_trans.
         +apply gr_eq_symm.
          apply H_linear; [ easy | now apply B ].
         +now apply gr_eq_symm.
      }
      assert (H4 : ∃ z₁, z₁ ∈ Coker a ∧ (H_app f' z₁ = H_app b y₁)%G). {

...
      assert (H3 : H_app b (y₁ - y₂)%G ∈ Im f'). {
        exists (H_app a z).
        split; [ now apply a | easy ].
      }
      apply sg' in H3.
      simpl in H3.
      destruct H3 as (Hby, Hgby).
      assert (H4 : (H_app c (H_app g (y₁ - y₂)) = 0)%G). {
        eapply gr_eq_trans; [ apply Hcgg' | easy ].
      }
(* ouais, non, c'est pas ça... *)
...
    assert (H8 : ∀ y, y ∈ B → (H_app b (g₁ (H_app g y)) = H_app b y)%G). {
      clear x y Hy Hfy Hf'y Hdxy Hfd H2 H1 H4 H6 Hx Hfx Hf'x H3.
      intros y Hy.
...

assert ((H_app g' (H_app b (g₁ x) + H_app b (g₁ y)) = 0)%G). {
eapply gr_eq_trans; [ | apply H ].
apply gr_eq_symm.
eapply gr_eq_trans.
apply gr_eq_symm, Hcgg'.
apply gr_eq_trans with (y := H_app c (x + y)%G).
apply H_compat.
apply g.
now apply B.
now apply C.
eapply gr_eq_trans.
apply H_linear; easy.
apply gr_eq_trans with (y := (x + H_app g (g₁ y))%G); simpl.
apply gr_add_compat; [ easy | apply gr_eq_refl ].
apply gr_add_compat; [ apply gr_eq_refl | easy ].
eapply gr_eq_trans; simpl.
now apply H_linear.
...
assert ((H_app g' (H_app b (g₁ x + g₁ y)) = H_app g' (H_app b (g₁ x) + H_app b (g₁ y)))%G). {
  ============================
  (H_app c (x + y) = H_app g' (H_app b (g₁ x) + H_app b (g₁ y)))%G
}
...
    apply H_compat; [ now apply B | easy | ].
    apply gr_eq_symm.
...
  ============================
  (g₁ (x + y) = g₁ x + g₁ y)%G
...
}
...
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
