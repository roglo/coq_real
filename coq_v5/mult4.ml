open Printf.

type real01 = { rm : int → int };
type real = { r_int : int; r_frac : real01 }.

value b = 10;

value d2n d = d mod b;

value r_int x = x.r_int;
value r_frac x = x.r_frac;

value i_opp x = { rm i = b - 1 - x.rm i }.
value r_opp x = { r_int = - r_int x - 1; r_frac = i_opp (r_frac x) }.
value r_is_neg x = r_int x < 0;
value r_abs x = if r_is_neg x then r_opp x else x.

value i_mul_b_pow x n = { rm i = x.rm (i+n) }.

value i_div_b_pow_i x n i = if i < n then 0 else x.rm (i-n).

value i_div_b_pow x n = { rm = i_div_b_pow_i x n }.

value rec i_mul_b_pow_from xi xf n =
  if n < 0 then invalid_arg "i_mul_b_pow_from" else
  match n with
  | 0 → xi
  | _ →
      let n1 = n-1 in
      i_mul_b_pow_from (b * xi + d2n (xf.rm 0)) (i_mul_b_pow xf 1) n1
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
  let ax = r_abs x in
  let r =
    let xi = r_int ax in
    let xf = r_frac ax in
    { r_int = i_mul_b_pow_from xi xf n;
      r_frac = i_mul_b_pow xf n }
  in
  if r_is_neg x then r_opp r else r.

value r_div_b_pow x n =
  let ax = r_abs x in
  let r =
    let xi = r_int ax in
    let xf = r_frac ax in
    { r_int = i_div_b_pow_int xi n;
      r_frac = i_div_b_pow_frac xi xf n }
  in
  if r_is_neg x then r_opp r else r.

(* *)

value i_of_string_from s k =
  {rm i =
     if i + k ≥ String.length s then 0
     else Char.code s.[i+k] - Char.code '0'}
;

value r_of_string s =
  let (is_neg, i) = if s <> "" && s.[0] = '-' then (True, 1) else (False, 0) in
  let k = try String.index_from s i '.' with [ Not_found → String.length s ] in
  let r =
    { r_int = int_of_string (String.sub s i (k-i));
      r_frac = i_of_string_from s (k + 1) }
  in
  if is_neg then r_opp r else r
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
readable_r (r_opp (r_mul_b_pow (r_div_b_pow (r_of_string "-314.15926535") 1) 1));
readable_r (r_opp (r_mul_b_pow (r_div_b_pow (r_of_string "-314.15926535") 0) 0));
