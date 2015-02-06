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
bbb.

intros x y i.
unfold I_add_i; simpl; f_equal.
f_equal; f_equal; f_equal; rewrite Nat.add_comm; reflexivity.
Qed.

Theorem I_add_comm : ∀ x y, I_eq_ext (x + y) (y + x).
Proof.
intros x y.
unfold I_eq_ext; simpl; intros i.
apply I_add_i_comm.
Qed.

(* neutral element *)

Theorem I_add_0_r : ∀ x, I_eq_ext (x + 0) x.
Proof.
intros x.
unfold I_eq_ext; simpl; intros i.
unfold I_add_i; simpl.
destruct (x .[ i]), (x .[ S i]), (x .[ S (S i)]); reflexivity.
Qed.

(* compatibility *)

Theorem I_add_compat_r : ∀ x y z, I_eq_ext x y → I_eq_ext (x + z) (y + z).
Proof.
intros x y z Hxy.
unfold I_eq_ext in Hxy.
unfold I_eq_ext; simpl; intros i.
unfold I_add_i; simpl.
do 3 rewrite Hxy; reflexivity.
Qed.

(* associativity *)

Theorem I_add_assoc : ∀ x y z, I_eq_ext (x + (y + z)) ((x + y) + z).
Proof.
intros x y z.
unfold I_eq_ext; simpl; intros i.
bbb.
(*
counterexample:
  Hxi : x .[ i] = true
  Hyi : y .[ i] = true
  Hzi : z .[ i] = true
  Hxsi : x .[ S i] = true
  Hysi : y .[ S i] = true
  Hzsi : z .[ S i] = true
  Hxssi : x .[ S (S i)] = true
  Hyssi : y .[ S (S i)] = true
  Hzssi : z .[ S (S i)] = false
  Hxsssi : x .[ S (S (S i))] = true
  Hysssi : y .[ S (S (S i))] = true
  Hzsssi : z .[ S (S (S i))] = false
  ============================
   0 = 1
*)

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
