open Printf;

type real_mod_1 = { rm : int → int };

value rm_zero = {rm i = 0};

value fst_carry_sure base x y i =
  loop 0 where rec loop di =
    if x.rm (i + di) + y.rm (i + di) <> base - 1 then Some di
    else if di > 10000 then None
    else loop (di + 1)
;

value add_dig base a b = (a + b) mod base;

value gen_carry base x y i =
  match fst_carry_sure base x y i with
  | Some dj → if x.rm (i + dj) + y.rm (i + dj) < base - 1 then 0 else 1
  | None → 1
  end.

value carry base x y i = gen_carry base x y (i + 1);

value rm_add_i base x y i =
  add_dig base (add_dig base (x.rm i) (y.rm i)) (carry base x y i)
;

value rm_add base a b = { rm = rm_add_i base a b }.
value rm_opp base a = { rm i = base - 1 - a.rm i };
value rm_sub base a b = rm_add base a (rm_opp base b);

value rm_add_carry base x y = gen_carry base x y 0;

value f2am base x =
  let x = mod_float x 1.0 in
  loop 100 x [] where rec loop i x list =
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
  { rm i = if i < Array.length a then a.(i) else 0 }
;

value rm2f base x = am2f base (Array.init 100 x.rm);

let b = 2 in rm2f b (rm_add b (f2rm b 0.28) (f2rm b 0.17));
let b = 7 in rm2f b (rm_add b (f2rm b 0.28) (f2rm b 0.17));

value am2s base a =
  "0." ^
  loop 0 "" where rec loop i s =
    if i = Array.length a then s
    else loop (i + 1) (s ^ string_of_int a.(i))
;

(*
value rec trunc n a =
  if n = 0 then []
  else [a.rm (n-1) :: trunc (n-1) a]
;

value carry_sum_3 a b c = a && b || b && c || c && a;

value rec trunc_add_with_carry c la lb =
  match (la, lb) with
  | ([a :: la₁], [b :: lb₁]) →
      let t = xorb (xorb a b) c in
      let c₁ = carry_sum_3 a b c in
      [t :: trunc_add_with_carry c₁ la₁ lb₁]
  | _ → []
  end.

value trunc_add = trunc_add_with_carry False;

value t2s la =
  "0." ^ List.fold_left (fun s a → if a then "1" ^ s else "0" ^ s) "" la
;

value t2f la =
  List.fold_left (fun s a → (if a then 1. else 0.) +. s /. 2.) 0. la /. 2.
;

value tr_add n a b =
  let c =
    match fst_carry_sure a b n with
    | Some dn → a.rm (n + dn)
    | None → True
    end
  in
  trunc_add_with_carry c (trunc n a) (trunc n b)
;

value tr_add2 n a b = trunc_add_with_carry False (trunc n a) (trunc n b);

value n = 9;
n;
t2f (tr_add n (f2rm 0.5) (f2rm 0.2));
t2f (trunc n (rm_add (f2rm 0.5) (f2rm 0.2)));
(tr_add n (f2rm 0.5) (f2rm 0.2));
(trunc n (rm_add (f2rm 0.5) (f2rm 0.2)));
t2s (tr_add n (f2rm 0.5) (f2rm 0.2));
t2s (trunc n (rm_add (f2rm 0.5) (f2rm 0.2)));

t2f (tr_add 35 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 36 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 37 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 38 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 39 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 40 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 41 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 42 (f2rm 0.5) (f2rm 0.2));

5;

t2f (tr_add 0 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 1 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 2 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 3 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 4 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 5 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 6 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 7 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 8 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 9 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 10 (f2rm 0.5) (f2rm 0.2));
t2f (tr_add 11 (f2rm 0.5) (f2rm 0.2));

5;

t2f (trunc 0 (rm_add (f2rm 0.5) (f2rm 0.2)));
t2f (trunc 1 (rm_add (f2rm 0.5) (f2rm 0.2)));
t2f (trunc 2 (rm_add (f2rm 0.5) (f2rm 0.2)));
t2f (trunc 3 (rm_add (f2rm 0.5) (f2rm 0.2)));
t2f (trunc 4 (rm_add (f2rm 0.5) (f2rm 0.2)));
t2f (trunc 5 (rm_add (f2rm 0.5) (f2rm 0.2)));
t2f (trunc 6 (rm_add (f2rm 0.5) (f2rm 0.2)));
t2f (trunc 7 (rm_add (f2rm 0.5) (f2rm 0.2)));
t2f (trunc 8 (rm_add (f2rm 0.5) (f2rm 0.2)));
t2f (trunc 9 (rm_add (f2rm 0.5) (f2rm 0.2)));
t2f (trunc 10 (rm_add (f2rm 0.5) (f2rm 0.2)));
t2f (trunc 11 (rm_add (f2rm 0.5) (f2rm 0.2)));

value rec trunc_from n a i =
  match n with
  | 0 → []
  | _ →
      let n₁ = n - 1 in
      [a.rm (i+n₁) :: trunc_from n₁ a i]
  end.

value rm_exp_opp n = {rm i = i = n}.
value trunc_one n = trunc_from n (rm_exp_opp (pred n)) 0;
*)

type comparison = [ Eq | Lt | Gt ].

value rm_compare base x y =
  match fst_carry_sure base x (rm_opp base y) 0 with
  | Some j → if x.rm j < y.rm j then Lt else Gt
  | None → Eq
  end
;

value rm_lt base x y = rm_compare base x y = Lt;
value rm_le base x y = rm_compare base x y <> Gt;
value rm_gt base x y = rm_compare base x y = Gt;
value rm_ge base x y = rm_compare base x y <> Lt;

value rm_shift_r n pad x = { rm i = if i < n then pad else x.rm (i-n) };

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
  loop 100 x [] where rec loop i x list =
    if i = 0 then (Array.of_list (List.rev list), p)
    else
      let x = float base *. x in
      loop (i - 1) (mod_float x 1.0) [truncate x :: list]
;

value f2r base x =
  let (a, p) = f2a base (abs_float x) in
  { re_abs = {rm i = if i < Array.length a then a.(i) else 0};
    re_power = p;
    re_sign = x ≥ 0. }
;

value r2f base a =
  loop 0 0.0 (1. /. float base) where rec loop i x pow =
    if i = 100 then
      (if a.re_sign then 1. else -1.) *. x *. float base ** float a.re_power
    else
      loop (i + 1) (x +. float (a.re_abs.rm i) *. pow)
        (pow /. float base)
;

let b = 3 in r2f b (re_add b (f2r b 0.28) (f2r b 0.17));
let b = 3 in r2f b (re_add b (f2r b 1.28) (f2r b 0.17));
let b = 3 in r2f b (re_add b (f2r b 17.9) (f2r b 16.9));
let b = 3 in r2f b (re_add b (f2r b (-16.9)) (f2r b (-17.9)));
let b = 3 in r2f b (re_add b (f2r b (-1.28)) (f2r b 0.17));
