type real01 = { rm : int → bool };

value b2n b = if b then 1 else 0;

value rec summation_loop b len g =
  match len with
  | 0 → 0
  | _ → g b + summation_loop (b + 1) (len - 1) g
  end.

value summation b e g = summation_loop b (e + 1 - b) g;

value base = ref 2;
value propag_carry u i = u i mod base.val + u (i + 1) / base.val;
value rec propag_carry_sev_times u n =
  if n ≤ 0 then u
  else propag_carry_sev_times (propag_carry u) (n-1)
;

value i_mul_i x y i =
  let u k = summation 1 k (fun j → b2n (x.rm (j - 1)) * b2n (y.rm (k - j))) in
  let n = n such that ((base^n-1)/(base-1)-n) ≥ i
  propag_carry_sev_times u n i
;
