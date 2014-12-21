Require Import Utf8 QArith.
Require Import Real01Add RealAdd.

Set Implicit Arguments.

Open Scope Z_scope.

Fixpoint two_power n :=
  match n with
  | O => 1%nat
  | S n1 => (2 * two_power n1)%nat
  end.

Definition rm_mul_2 x := {| rm i := x.[S i] |}.
Arguments rm_mul_2 x%rm.

Definition rm_div_2_inc x b :=
  {| rm i := if zerop i then b else x.[i-1] |}.
Arguments rm_div_2_inc x%rm _.

Definition re_div_2 x :=
  {| re_int := re_int x / 2;
     re_frac := rm_div_2_inc (re_frac x) (Z.odd (re_int x)) |}.
Arguments re_div_2 x%R.

Fixpoint rm_equiv_div m x y :=
  match m with
  | O => (0%rm, 0%rm)
  | S m1 =>
      let x2 := re_div_2 x in
      let y2 := re_div_2 y in
      if Z.eqb (re_int x) 0 && Z.eqb (re_int y) 0 then
        (re_frac x2, re_frac y2)
      else
        rm_equiv_div m1 x2 y2
  end.
Arguments rm_equiv_div m%Z x%rm y%rm.

Definition re_is_neg x := Z.ltb (re_int x) 0.
Arguments re_is_neg x%R.

Definition re_abs x := if re_is_neg x then re_opp x else x.
Arguments re_abs x%R.

Fixpoint rm_div_eucl_i x y i :=
  match i with
  | O => if rm_lt_dec x y then (false, x) else (true, rm_sub x y)
  | S i1 =>
      let r := snd (rm_div_eucl_i x y i1) in
      let tr := rm_mul_2 r in
      if rm_lt_dec tr y then (false, tr) else (true, rm_sub tr y)
  end.
Arguments rm_div_eucl_i x%rm y%rm i%nat.

Definition rm_div_i x y i := fst (rm_div_eucl_i (rm_mul_2 x) y i).
Arguments rm_div_i x%rm y%rm i%nat.

Definition rm_div x y := {| rm := rm_div_i x y |}.
Arguments rm_div x%rm y%rm.

Fixpoint rm_eucl_div_loop m x y :=
  match m with
  | O => (O, 0%rm)
  | S m1 =>
      if rm_lt_dec x y then (O, x)
      else
        let (q, r) := rm_eucl_div_loop m1 (rm_sub x y) y in
        (S q, r)
  end.
Arguments rm_eucl_div_loop m%nat x%rm y%rm.

Definition rm_eucl_div x y :=
  match fst_same x rm_ones 0 with
  | Some jx =>
      match fst_same y rm_ones 0 with
      | Some jy =>
          if le_dec jx jy then
            let m := two_power (S (jy - jx)) in
            let (q, r) := rm_eucl_div_loop m x y in
            (q, rm_div r y)
          else
            (O, rm_div x y)
      | None => (O, y)
      end
  | None => (O, y)
  end.
Arguments rm_eucl_div x%rm y%rm.

Definition re_div x y :=
  let ax := re_abs x in
  let ay := re_abs y in
  let m := S (Z.to_nat (re_int ax + re_int ay)) in
  let (xm, ym) := rm_equiv_div m x y in
  let (q, rm) := rm_eucl_div xm ym in
  let qz := Z.of_nat q in
  {| re_int := if re_is_neg x ⊕ re_is_neg y then -qz else qz;
     re_frac := rm |}.
Arguments re_div x%R y%R.
