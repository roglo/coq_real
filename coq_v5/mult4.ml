open Printf.

type real01 = { rm : int → int };
type real = { r_int : int; r_frac : real01 }.

value b2z d = if d = 0 then 0 else 1;

value i_mul_2_pow x n = { rm i = x.rm (i+n) }.

value i_div_2_pow_i x n i = if i < n then 0 else x.rm (i-n).

value i_div_2_pow x n = { rm = i_div_2_pow_i x n }.

value rec i_mul_2_pow_from xi xf n =
  match n with
  | 0 → xi
  | _ →
      let n1 = n-1 in
      i_mul_2_pow_from (2 * xi + b2z (xf.rm n)) xf n1
  end.

value rec i_div_2_pow_from_int xi n =
  match n with
  | 0 → if xi mod 2 = 0 then 0 else 1
  | _ →
      let n1 = n-1 in
      i_div_2_pow_from_int (xi / 2) n1
  end.

value i_div_2_pow_frac_i xi xf n i =
  if i < n then i_div_2_pow_from_int xi (n-i)
  else xf.rm (i-n).

value rec i_div_2_pow_int xi n =
  match n with
  | 0 → xi
  | _ →
      let n1 = n-1 in
      i_div_2_pow_int (xi / 2) n1
  end.

value i_div_2_pow_frac xi xf n = { rm = i_div_2_pow_frac_i xi xf n }.

value r_mul_2_pow x n =
  { r_int = i_mul_2_pow_from x.r_int x.r_frac n;
    r_frac = i_mul_2_pow x.r_frac n }.

value r_div_2_pow x n =
  { r_int = i_div_2_pow_int x.r_int n;
    r_frac = i_div_2_pow_frac x.r_int x.r_frac n }.
