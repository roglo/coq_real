Require Import Utf8 QArith.
Require Import Real01Add.

Set Implicit Arguments.

Open Scope nat_scope.

Record real := { re_mant : real_mod_1; re_power : nat; re_sign : bool }.

Delimit Scope R_scope with R.

Definition rm_shift_r n pad x :=
  {| rm i := if lt_dec i n then pad else x.[i-n] |}.

Definition rm_final_carry x y :=
  match fst_same x y 0 with
  | Some j => x.[j]
  | None => true
  end.

Definition re_add x y :=
  let xm := rm_shift_r (max 0 (re_power y - re_power x)) false (re_mant x) in
  let ym := rm_shift_r (max 0 (re_power x - re_power y)) false (re_mant y) in
  if bool_dec (re_sign x) (re_sign y) then
    let zm := rm_add xm ym in
    let c := rm_final_carry xm ym in
    {| re_mant := if c then rm_shift_r 1 true zm else zm;
       re_power := max (re_power x) (re_power y) + if c then 1 else 0;
       re_sign := re_sign x |}
  else
    let (zm, sign) :=
      match rm_compare xm ym with
      | Eq => (rm_zero, true)
      | Lt => (rm_sub ym xm, re_sign y)
      | Gt => (rm_sub xm ym, re_sign x)
      end
    in
    {| re_mant := zm;
       re_power := max (re_power x) (re_power y);
       re_sign := sign |}.

Notation "x + y" := (re_add x y) : R_scope.

Close Scope nat_scope.
