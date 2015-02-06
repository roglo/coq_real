(* addition modulo 1 in I = [0..1] ⊂ ℝ *)

Require Import Utf8 QArith NPeano.
Require Import Real01.

Open Scope nat_scope.

Definition I_add_algo x y := {| sn i := d2n (x.[i]) + d2n (y.[i]) |}.
Definition I_add_i x y i := n2d (sn (I_propag_carry_once (I_add_algo x y)) i).
Definition I_add x y := {| rm := I_add_i x y |}.

Arguments I_add_algo x%I y%I.
Arguments I_add_i x%I y%I i%nat.
Arguments I_add x%I y%I.

Notation "x + y" := (I_add x y) : I_scope.

(* commutativity *)

Theorem fst_not_1_I_add_algo_comm : ∀ x y i,
  fst_not_1 (I_add_algo x y) i = fst_not_1 (I_add_algo y x) i.
Proof.
intros x y i.
apply fst_not_1_iff; simpl.
remember (fst_not_1 (I_add_algo x y) i) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Nat.add_comm in Ht1.
 split; [ idtac | assumption ].
 intros dj Hdj.
 rewrite Nat.add_comm.
 apply Hn1; assumption.

 intros dj.
 rewrite Nat.add_comm.
 apply Hs1.
Qed.

Theorem carry_I_add_algo_comm : ∀ x y i,
  carry (I_add_algo x y) i = carry (I_add_algo y x) i.
Proof.
intros x y i.
unfold carry; simpl.
rewrite fst_not_1_I_add_algo_comm.
remember (fst_not_1 (I_add_algo y x) (S i)) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ]; [ idtac | reflexivity ].
destruct Hs1 as (Hn1, Ht1).
rewrite Nat.add_comm; reflexivity.
Qed.

Theorem I_add_i_comm : ∀ x y i, I_add_i x y i = I_add_i y x i.
Proof.
intros x y i.
unfold I_add_i; simpl.
f_equal; f_equal; [ rewrite Nat.add_comm; reflexivity | idtac ].
apply carry_I_add_algo_comm.
Qed.

Theorem I_add_comm : ∀ x y, I_eq_ext (x + y) (y + x).
Proof.
intros x y.
unfold I_eq_ext; simpl; intros i.
apply I_add_i_comm.
Qed.

(* neutral element *)

(* this theorem is false; should be I_eq (to be defined), not I_eq_ext
Theorem I_add_0_r : ∀ x, I_eq_ext (x + 0) x.
Proof.
intros x.
unfold I_eq_ext; simpl; intros i.
unfold I_add_i; simpl.
rewrite Nat.add_0_r.
unfold modb.
remember (x .[ i]) as xi eqn:Hxi .
symmetry in Hxi.
destruct xi; simpl.
 unfold n2d.
 reflexivity.

 unfold n2d.
 apply negb_false_iff.
 apply Nat.eqb_eq.
 unfold carry.
 simpl.
 remember (fst_not_1 (I_add_algo x 0) (S i)) as s1 eqn:Hs1 .
 apply fst_not_1_iff in Hs1; simpl in Hs1.
 destruct s1 as [di1| ].
  destruct Hs1 as (Hn1, Ht1).
  unfold d2n in Ht1.
  remember (x .[ S (i + di1)]) as xi1 eqn:Hxi1 .
  symmetry in Hxi1.
  destruct xi1; [ exfalso; apply Ht1; reflexivity | idtac ].
  reflexivity.

  pose proof (Hs1 0) as H; simpl in H.
  rewrite Nat.add_0_r in H.
  rewrite Nat.add_0_r in H.
  unfold d2n in H; simpl in H.
  remember (x .[ S i]) as xsi eqn:Hxsi .
  symmetry in Hxsi.
  destruct xsi; [ clear H | discriminate H ].
bbb.
*)

(* compatibility *)

Theorem fst_not_1_I_add_algo_compat_r : ∀ x y z i,
  I_eq_ext x y
  → fst_not_1 (I_add_algo x z) i = fst_not_1 (I_add_algo y z) i.
Proof.
intros x y z i Hxy.
apply fst_not_1_iff; simpl.
remember (fst_not_1 (I_add_algo x z) i) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ].
 destruct Hs1 as (Hn1, Ht1).
 rewrite Hxy in Ht1.
 split; [ idtac | assumption ].
 intros dj Hdj; rewrite <- Hxy; apply Hn1; assumption.

 intros dj; rewrite <- Hxy; apply Hs1.
Qed.

Theorem carry_I_add_algo_compat_r : ∀ x y z i,
  I_eq_ext x y
  → carry (I_add_algo x z) i = carry (I_add_algo y z) i.
Proof.
intros x y z i Hxy.
unfold carry; simpl.
erewrite fst_not_1_I_add_algo_compat_r; [ idtac | eassumption ].
remember (fst_not_1 (I_add_algo y z) (S i)) as s1 eqn:Hs1 .
apply fst_not_1_iff in Hs1; simpl in Hs1.
destruct s1 as [di1| ]; [ idtac | reflexivity ].
rewrite Hxy; reflexivity.
Qed.

Theorem I_add_compat_r : ∀ x y z, I_eq_ext x y → I_eq_ext (x + z) (y + z).
Proof.
intros x y z Hxy.
unfold I_eq_ext in Hxy.
unfold I_eq_ext; simpl; intros i.
unfold I_add_i; simpl; f_equal.
rewrite Hxy; f_equal.
apply carry_I_add_algo_compat_r.
assumption.
Qed.

(* associativity *)

Theorem I_add_assoc : ∀ x y z, I_eq_ext (x + (y + z)) ((x + y) + z).
Proof.
intros x y z.
unfold I_eq_ext; simpl; intros i.
unfold I_add_i; simpl.
unfold I_add_i; simpl.
remember (x .[ i]) as xi eqn:Hxi .
remember (y .[ i]) as yi eqn:Hyi .
remember (z .[ i]) as zi eqn:Hzi .
symmetry in Hxi, Hyi, Hzi.
destruct xi, yi, zi; try reflexivity; simpl.
bbb.

unfold I_add_i; simpl.
unfold I_add_i; simpl.
remember (x .[ i]) as xi eqn:Hxi .
remember (y .[ i]) as yi eqn:Hyi .
remember (z .[ i]) as zi eqn:Hzi .
remember (x .[ S i]) as xsi eqn:Hxsi .
remember (y .[ S i]) as ysi eqn:Hysi .
remember (z .[ S i]) as zsi eqn:Hzsi .
remember (x .[ S (S i)]) as xssi eqn:Hxssi .
remember (y .[ S (S i)]) as yssi eqn:Hyssi .
remember (z .[ S (S i)]) as zssi eqn:Hzssi .
remember (x .[ S (S (S i))]) as xsssi eqn:Hxsssi .
remember (y .[ S (S (S i))]) as ysssi eqn:Hysssi .
remember (z .[ S (S (S i))]) as zsssi eqn:Hzsssi .
symmetry in Hxi, Hyi, Hzi, Hxsi, Hysi, Hzsi, Hxssi, Hyssi, Hzssi.
symmetry in Hxsssi, Hysssi, Hzsssi.
bbb.


destruct xi, yi, zi, xsi, ysi, zsi, xssi, yssi, zssi; try reflexivity; simpl.
 destruct xsssi, ysssi, zsssi; try reflexivity; simpl.
  Focus 1.
  unfold modb, divb; simpl.
bbb.

(*
Trois, maintenant !

Il faut au moins deux propagations de retenues pour l'addition !
Exemple:
     1   0   1
   + 1   1   1
   ===========
     2   1   2
    ./0 0/1 1/0
     0   2   0
    ./0 1/0 0/0
     1   0   0
*)
