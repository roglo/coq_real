open Printf;

type real_mod_1 = { sm : int → int; id : int };

value new_id = let r = ref 0 in fun () → do { incr r; r.val };
value make_rm rm = {sm = rm; id = new_id ()};
value get_rm rm = rm.sm;

value rm_zero = make_rm (fun i → 0);

value fst_carry_sure base x y i =
  loop 0 where rec loop di =
    if get_rm x (i + di) + get_rm y (i + di) <> base - 1 then Some di
    else if di > 30 then
      None
    else loop (di + 1)
;

value ht = Hashtbl.create 1;
value fst_carry_sure base x y i =
  try Hashtbl.find ht (x.id, y.id, i) with
  [ Not_found → do {
      let r = fst_carry_sure base x y i in
      Hashtbl.add ht (x.id, y.id, i) r;
      r
    } ];

value sum_unit base a b = (a + b) mod base;

value gen_carry base x y i =
  match fst_carry_sure base x y i with
  | Some dj → if get_rm x (i + dj) + get_rm y (i + dj) < base then 0 else 1
  | None → 1
  end.

value carry base x y i = gen_carry base x y (i + 1);

value rm_add_i base x y i =
  sum_unit base (sum_unit base (get_rm x i) (get_rm y i)) (carry base x y i)
;

value rm_add base a b = make_rm (rm_add_i base a b);
value rm_opp base a = make_rm (fun i → base - 1 - get_rm a i);
value rm_sub base a b = rm_add base a (rm_opp base b);

value rm_add_carry base x y = gen_carry base x y 0;

value mm = 30;

value f2am base x =
  let x = mod_float x 1.0 in
  loop mm x [] where rec loop i x list =
    if i = 0 then Array.of_list (List.rev list)
    else
      let x = float base *. x in
      loop (i - 1) (mod_float x 1.0) [truncate x :: list]
;

value am2f base a =
  loop 0 0.0 (1. /. float base) where rec loop i x pow =
    if i = Array.length a then x
    else loop (i + 1) (x +. float a.(i) *. pow) (pow /. float base)
;

value f2rm base x =
  let a = f2am base x in
  make_rm (fun i → if i < Array.length a then a.(i) else 0)
;

value rm2f base x = am2f base (Array.init mm (get_rm x));

let b = 2 in rm2f b (rm_add b (f2rm b 0.28) (f2rm b 0.17));
let b = 7 in rm2f b (rm_add b (f2rm b 0.28) (f2rm b 0.17));

value am2s base a =
  "0." ^
  loop 0 "" where rec loop i s =
    if i = Array.length a then s
    else loop (i + 1) (s ^ string_of_int a.(i))
;

type comparison = [ Eq | Lt | Gt ].

value rm_compare base x y =
  match fst_carry_sure base x (rm_opp base y) 0 with
  | Some j → if get_rm x j < get_rm y j then Lt else Gt
  | None → Eq
  end
;

value rm_lt base x y = rm_compare base x y = Lt;
value rm_le base x y = rm_compare base x y <> Gt;
value rm_gt base x y = rm_compare base x y = Gt;
value rm_ge base x y = rm_compare base x y <> Lt;

value rm_shift_r n pad x =
  make_rm (fun i → if i < n then pad else get_rm x (i-n));
value rm_shift_l n x =
  make_rm (fun i → get_rm x (i+n));

value rec rm_div_i x y i =
  if i = 0 then
    if rm_lt 2 x y then 0 else 1
  else
    let x = if rm_lt 2 x y then x else rm_sub 2 x y in
    rm_div_i (rm_shift_l 1 x) y (i - 1)
;

value rm_div x y = make_rm (fun i → rm_div_i x y (i + 1));

type real = { re_abs : real_mod_1; re_power : int; re_sign : bool };

value re_add base x y =
  let xm = rm_shift_r (max 0 (y.re_power - x.re_power)) 0 x.re_abs in
  let ym = rm_shift_r (max 0 (x.re_power - y.re_power)) 0 y.re_abs in
  if x.re_sign = y.re_sign then
    let zm = rm_add base xm ym in
    let c = rm_add_carry base xm ym in
    {re_abs = if c = 1 then rm_shift_r 1 1 zm else zm;
     re_power = max x.re_power y.re_power + c;
     re_sign = x.re_sign}
  else
    let (zm, sign) =
      match rm_compare base xm ym with
      | Eq → (rm_zero, True)
      | Lt → (rm_sub base ym xm, y.re_sign)
      | Gt → (rm_sub base xm ym, x.re_sign)
      end
    in
    {re_abs = zm;
     re_power = max x.re_power y.re_power;
     re_sign = sign}
;

value f2a base x =
  let (x, p) =
    loop x 0 where rec loop x p =
      if x ≥ 1.0 then loop (x /. float base) (p + 1)
      else (x, p)
  in
  loop mm x [] where rec loop i x list =
    if i = 0 then (Array.of_list (List.rev list), p)
    else
      let x = float base *. x in
      loop (i - 1) (mod_float x 1.0) [truncate x :: list]
;

value f2r base x =
  let (a, p) = f2a base (abs_float x) in
  { re_abs = make_rm (fun i → if i < Array.length a then a.(i) else 0);
    re_power = p;
    re_sign = x ≥ 0. }
;

value r2f base a =
  loop 0 0.0 (1. /. float base) where rec loop i x pow =
    if i = mm then
      (if a.re_sign then 1. else -1.) *. x *. float base ** float a.re_power
    else
      loop (i + 1) (x +. float (get_rm (a.re_abs) i) *. pow)
        (pow /. float base)
;

let b = 3 in r2f b (re_add b (f2r b 0.28) (f2r b 0.17));
let b = 3 in r2f b (re_add b (f2r b 1.28) (f2r b 0.17));
let b = 3 in r2f b (re_add b (f2r b 17.9) (f2r b 16.9));
let b = 3 in r2f b (re_add b (f2r b (-16.9)) (f2r b (-17.9)));
let b = 3 in r2f b (re_add b (f2r b (-1.28)) (f2r b 0.17));

value rm2fshort base x = am2f base (Array.init 28 (get_rm x));

Printf.printf "%.16f\n%!" (
0.17/.0.28
);

Printf.printf "%.16f\n%!" (
let b = 2 in (rm2fshort b (rm_div (f2rm b 0.17) (f2rm b 0.28)))
);
