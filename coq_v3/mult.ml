type real01 = { rm : int → bool };

value b2n b = if b then 1 else 0;

value rec summation_loop b len g =
  match len with
  | 0 → 0
  | _ → g b + summation_loop (b + 1) (len - 1) g
  end.

value summation b e g = summation_loop b (e + 1 - b) g;

value i_mul_i x y i =
  summation 1 i (fun j → b2n (x.rm (j - 1)) * b2n (y.rm (i - j)))
;
