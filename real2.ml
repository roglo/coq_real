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
value rm_sub x y = rm_add x (rm_opp y);
value rm_zero = {rm _ = False};
value rm_ones = {rm _ = True};
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

value f2r a = {re_int = truncate (floor a); re_frac = f2rm (a -. floor a)};
value r2f x = float x.re_int +. rm2f x.re_frac;

(* *)

(* division using only subtractions; computation of integer part *)

value rec two_power n =
  if n < 0 then invalid_arg "two_power" else
  match n with
  | 0 → 1
  | _ →
      let n1 = n - 1 in
      2 * two_power n1
  end
;

(* iub : iterations upper bound *)
value rec rm_int_of_div_loop iub x y =
  if iub < 0 then invalid_arg "rm_int_of_div_loop" else
  match iub with
  | 0 → failwith "rm_int_of_div_loop bug: insufficient nb of iterations"
  | _ →
      let iub1 = iub - 1 in
      if rm_lt x y then 0
      else 1 + rm_int_of_div_loop iub1 (rm_sub x y) y
  end
;

(* don't try it with x / y > 7 because the division algorithm is only
   done with subtractions without shifts *)
value rm_int_of_div x y =
  match fst_same x rm_ones 0 with
  | Some jx →
      match fst_same y rm_ones 0 with
      | Some jy →
          if jx ≤ jy then
            let iub = two_power (jy - jx + 1) in
            rm_int_of_div_loop iub x y
          else 0
      | None → 0
      end
  | None → 0
  end
;

rm_int_of_div (f2rm 0.20) (f2rm 0.09);

(*
version having a problem of upper bound of iterations

value rec nb_shift_upto_lt m x y =
  match m with
  | 0 → failwith "nb_shift_upto_lt bug: insufficient nb of iterations"
  | _ →
      let m1 = m - 1 in
      if rm_lt x y then 0
      else 1 + nb_shift_upto_lt m1 x (rm_mul_2 y)
  end
;

(* floor (log2 (x / y) *)
value rm_ln_div_int x y =
  let s = nb_shift_upto_lt 14(*value to yfind*) x y in
  s - 1
;

value rm_div_int x y =
  (* extra shift to allow y left shift to be bigger than x without
     overflowing *)
  let x = rm_div_2_inc x False in
  let y = rm_div_2_inc y False in
  (* temporary result *)
  rm_ln_div_int x y
;

value rec re_div_int_loop m x y =
  match m with
  | 0 → failwith "re_div_int_loop bug: insufficient nb of iterations"
  | _ →
      let m1 = m - 1 in
      if x.re_int = 0 && y.re_int = 0 then rm_div_int x.re_frac y.re_frac
      else re_div_int_loop m1 (re_div_2 x) (re_div_2 y)
  end
;

value re_div_int x y = re_div_int_loop (x.re_int + y.re_int) x y;

value re_div_frac x y =
  failwith "re_div_frac not yet implemented"
;
*)

(*
re_div_int (f2r 34.79) (f2r 8.7);
re_div_int (f2r 34.8) (f2r 8.7);
re_div_int (f2r 1111111.) (f2r 239.);
log (1111111./.239.) /. log 2.;
*)
