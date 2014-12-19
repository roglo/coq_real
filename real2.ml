open Printf;

type real_mod_1 = { rm : int → bool };

value di_max = 30;
value fst_same x y i =
  loop 0 where rec loop di =
    if x.rm (i + di) = y.rm (i + di) then Some di
    else if di > di_max then None
    else loop (di + 1)
;

value carry x y i =
  match fst_same x y i with
  | Some dj → x.rm (i + dj)
  | None → True
  end;

value rm_add_i x y i = x.rm i <> y.rm i <> carry x y (i + 1);
value rm_add x y = {rm = rm_add_i x y};
value rm_opp x = {rm i = not (x.rm i)};
value rm_zero = {rm _ = False};
value rm_norm x = rm_add x rm_zero;
value rm_mul_2 x = {rm i = x.rm (i + 1)};
value rm_div_2_inc x n = {rm i = if i = 0 then n else x.rm (i - 1)};

type comparison = [ Eq | Lt | Gt ].
value rm_compare x y =
  let nx = rm_norm x in
  match fst_same nx (rm_opp (rm_norm y)) 0 with
  | Some j → if nx.rm j then Gt else Lt
  | None → Eq
  end;

value rm_lt x y = rm_compare x y = Lt;

value mm = 50;
value f2am x =
  let x = mod_float x 1.0 in
  loop mm x [] where rec loop i x list =
    if i = 0 then Array.of_list (List.rev list)
    else
      let x = float 2 *. x in
      loop (i - 1) (mod_float x 1.0) [truncate x <> 0 :: list]
;

value am2f a =
  loop 0 0.0 (1. /. float 2) where rec loop i x pow =
    if i = Array.length a then x
    else
      loop (i + 1) (x +. float (if a.(i) then 1 else 0) *. pow)
        (pow /. float 2)
;

value f2rm x =
  let a = f2am x in
  {rm i = if i < Array.length a then a.(i) else False};

value rm2f x = am2f (Array.init mm x.rm);

type real = {re_int : int; re_frac : real_mod_1};

value b2z b = if b then 1 else 0;

value re_add x y =
  {re_int = x.re_int + y.re_int + b2z (carry x.re_frac y.re_frac 0);
   re_frac = rm_add x.re_frac y.re_frac};

value re_opp x = {re_int = - x.re_int - 1; re_frac = rm_opp x.re_frac};

value re_norm x =
  {re_int = x.re_int + b2z (carry x.re_frac rm_zero 0);
   re_frac = rm_norm x.re_frac};

value re_div_2 x =
  {re_int = x.re_int / 2;
   re_frac = rm_div_2_inc x.re_frac (x.re_int mod 2 <> 0)}
;

value rec nb_shift_upto_lt x y =
  if rm_lt x y then 0
  else 1 + nb_shift_upto_lt x (rm_mul_2 y)
;

value rm_ln_div_int x y =
  let s = nb_shift_upto_lt x y in
  s - 1
;

value rec re_div_int x y =
  if x.re_int = 0 && y.re_int = 0 then
    (* extra shift to allow y left shift to be bigger than x without
       overflowing *)
    rm_ln_div_int
      (rm_div_2_inc x.re_frac False)
      (rm_div_2_inc y.re_frac False)
  else
    re_div_int (re_div_2 x) (re_div_2 y)
;

value f2r a = {re_int = truncate (floor a); re_frac = f2rm (a -. floor a)};
value r2f x = float x.re_int +. rm2f x.re_frac;

re_div_int (f2r 34.79) (f2r 8.7);
