open Printf;

type real_mod_1 = { rm : int → bool };

value fst_same x y i =
  loop 0 where rec loop di =
    if x.rm (i + di) = y.rm (i + di) then Some di
    else if di > 30 then None
    else loop (di + 1)
;

value carry x y i =
  match fst_same x y i with
  | Some dj → x.rm (i + dj)
  | None → True
  end;

value rm_add_i x y i = x.rm i <> y.rm i <> carry x y (i + 1);
value rm_add x y = {rm = rm_add_i x y};

type real = {re_int : int; re_frac : real_mod_1};

value b2z b = if b then 1 else 0;

value re_add x y =
  {re_int = x.re_int + y.re_int + b2z (carry x.re_frac y.re_frac 0);
   re_frac = rm_add x.re_frac y.re_frac};
