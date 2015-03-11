open Printf.

type real01 = { rm : int → int };
type real = { r_int : int; r_frac : real01 }.

value b = 10;

value b2z d = d mod b;

value i_mul_b_pow x n = { rm i = x.rm (i+n) }.

value i_div_b_pow_i x n i = if i < n then 0 else x.rm (i-n).

value i_div_b_pow x n = { rm = i_div_b_pow_i x n }.

value rec i_mul_b_pow_from xi xf n =
  if n < 0 then invalid_arg "i_mul_b_pow_from" else
  match n with
  | 0 → xi
  | _ →
      let n1 = n-1 in
      i_mul_b_pow_from (b * xi + b2z (xf.rm n)) xf n1
  end.

value rec i_div_b_pow_from_int xi n =
  if n < 0 then invalid_arg "i_div_b_pow_from_int" else
  match n with
  | 0 → xi mod b
  | _ →
      let n1 = n-1 in
      i_div_b_pow_from_int (xi / b) n1
  end.

value i_div_b_pow_frac_i xi xf n i =
  if i < n then i_div_b_pow_from_int xi (n-i-1)
  else xf.rm (i-n).

value rec i_div_b_pow_int xi n =
  if n < 0 then invalid_arg "i_div_b_pow_int" else
  match n with
  | 0 → xi
  | _ →
      let n1 = n-1 in
      i_div_b_pow_int (xi / b) n1
  end.

value i_div_b_pow_frac xi xf n = { rm = i_div_b_pow_frac_i xi xf n }.

value r_mul_b_pow x n =
  { r_int = i_mul_b_pow_from x.r_int x.r_frac n;
    r_frac = i_mul_b_pow x.r_frac n }.

value r_div_b_pow x n =
  { r_int = i_div_b_pow_int x.r_int n;
    r_frac = i_div_b_pow_frac x.r_int x.r_frac n }.

(* *)

value i_of_string_from s k =
  {rm i =
     if i + k ≥ String.length s then 0
     else Char.code s.[i+k] - Char.code '0'}
;

value r_of_string s =
  let (sign, i) = if s <> "" && s.[0] = '-' then (-1, 1) else (1, 0) in
  let k = try String.index_from s i '.' with [ Not_found → String.length s ] in
  { r_int = sign * int_of_string (String.sub s i (k-i));
    r_frac = i_of_string_from s (k + 1) }
;

value list_of_seq u =
  list_rec [] where rec list_rec l n =
    if n ≤ 0 then l
    else list_rec [u (n-1) :: l] (n-1)
;

value readable_i x = list_of_seq x.rm 20;
value readable_r x = (x.r_int, readable_i x.r_frac);

readable_r (r_div_b_pow (r_of_string "314.15926535") 0);
readable_r (r_div_b_pow (r_of_string "314.15926535") 1);
readable_r (r_div_b_pow (r_of_string "314.15926535") 2);
readable_r (r_div_b_pow (r_of_string "314.15926535") 3);
readable_r (r_div_b_pow (r_of_string "314.15926535") 4);

readable_r (r_div_b_pow (r_of_string "-314.15926535") 1);
