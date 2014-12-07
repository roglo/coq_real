Require Import Utf8 QArith NPeano.
Require Import Real01Add.

Set Implicit Arguments.

Open Scope Z_scope.

Record real := { re_int : Z; re_frac : real_mod_1 }.

Delimit Scope R_scope with R.
Arguments re_int _%R.
Arguments re_frac _%R.

Definition rm_final_carry x y :=
  match fst_same x y 0 with
  | Some j => if x.[j] then 1 else 0
  | None => 1
  end.

Definition re_add x y :=
  {| re_int := re_int x + re_int y + rm_final_carry (re_frac x) (re_frac y);
     re_frac := rm_add (re_frac x) (re_frac y) |}.

Close Scope Z_scope.
