(* multiplication in I *)

Require Import Utf8 NPeano.
Require Import Real01.

Fixpoint summation_loop b len g :=
  match len with
  | O => 0
  | S len₁ => g b + summation_loop (S b) len₁ g
  end.

Definition summation b e g := summation_loop b (S e - b) g.

Notation "'Σ' ( i = b , e ) , g" := (summation b e (λ i, (g)))
  (at level 0, i at level 0, b at level 60, e at level 60, g at level 40).

Definition b2n (b : bool) := if b then 1 else 0.

(* just sequence of convolution products, but no carry computed yet. *)
Definition I_mul_i x y i := Σ (j=1,i), (b2n (x.[j-1]) * b2n (y.[i-j])).

(* *)

(* summation model and theorems borrowed from proof of Puiseux's theorem,
   file Fsummation.v *)

Theorem summation_loop_compat : ∀ g h b1 b2 len,
  (∀ i, i < len → (g (b1 + i) = h (b2 + i)))
  → summation_loop b1 len g = summation_loop b2 len h.
Proof.
intros g h b1 b2 len Hgh.
revert b1 b2 Hgh.
induction len; intros; [ reflexivity | simpl ].
rewrite IHlen with (b2 := S b2).
 f_equal.
 pose proof (Hgh 0 (Nat.lt_0_succ len)) as H.
 do 2 rewrite Nat.add_0_r in H; assumption.

 intros i Hi.
 do 2 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hgh.
 apply Nat.succ_lt_mono in Hi; assumption.
Qed.

Theorem summation_loop_succ_last : ∀ g b len,
  summation_loop b (S len) g =
  summation_loop b len g + g (b + len).
Proof.
intros g b len.
revert b.
induction len; intros.
 simpl.
 do 2 rewrite Nat.add_0_r; reflexivity.

 remember (S len) as x; simpl; subst x.
 rewrite IHlen; simpl.
 rewrite Nat.add_succ_r, Nat.add_assoc; reflexivity.
Qed.

Theorem summation_loop_rev : ∀ b len g,
  summation_loop b len g =
  summation_loop b len (λ i, g (b + len - 1 + b - i)).
Proof.
intros b len g.
revert b.
induction len; intros; [ reflexivity | idtac ].
remember (S len) as x.
rewrite Heqx in |- * at 1; simpl; subst x.
rewrite IHlen.
rewrite summation_loop_succ_last.
rewrite Nat.add_comm; f_equal.
 apply summation_loop_compat.
 intros i Hi; f_equal.
 do 2 rewrite Nat.add_succ_r; reflexivity.

 f_equal.
 rewrite Nat.add_succ_r, Nat.sub_succ, Nat.sub_0_r.
 rewrite Nat.add_comm, Nat.add_sub; reflexivity.
Qed.

(* commutativity of sum of sequence of numbers *)

Theorem I_mul_comm : ∀ x y, (∀ i, I_mul_i x y i = I_mul_i y x i).
Proof.
intros x y i.
unfold I_mul_i; simpl.
unfold summation; simpl.
rewrite Nat.sub_0_r.
rewrite summation_loop_rev; simpl.
rewrite Nat.sub_0_r.
remember 1 as b; clear Heqb.
revert b.
induction i; intros; [ reflexivity | idtac ].
remember minus as f; simpl; subst f.
rewrite Nat.mul_comm; f_equal; [ f_equal | idtac ].
 rewrite <- Nat.add_succ_l, Nat.add_sub.
 do 2 rewrite Nat.sub_diag; reflexivity.

 rewrite <- Nat.add_succ_l.
 rewrite Nat.add_sub; reflexivity.
bbb.
