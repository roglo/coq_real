Require Import Utf8 QArith.
Require Import Real01Add RealAdd.

Set Implicit Arguments.

Open Scope Z_scope.

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

Definition re_is_neg x := Z_lt_dec (re_int x) 0.
Arguments re_is_neg x%R.

Definition re_abs x := if re_is_neg x then re_opp x else x.
Arguments re_abs x%R.

Definition re_div x y :=
  let ax := re_abs x in
  let ay := re_abs y in
  let m := re_int ax + re_int ay + 1 in
  let (xm, ym) := rm_equiv_div m x y in
  let (q, rm) := rm_eucl_div xm ym in
  {| re_int := if re_is_neg x = re_is_neg y then q else -q;
     re_frac := rm |}.
Arguments re_div x%R y%R.
