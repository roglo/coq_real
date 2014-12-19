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

value f2r a = {re_int = truncate (floor a); re_frac = f2rm (a -. floor a)};
value r2f x = float x.re_int +. rm2f x.re_frac;
