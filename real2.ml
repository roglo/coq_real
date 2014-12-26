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
value rm_div_2_inc x n =
  {rm i = if i = 0 then n else x.rm (i - 1)};

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
(**)
  let r =
    loop (Array.length a) 0.0 where rec loop i x =
      if i = 0 then x
      else loop (i - 1) (float (if a.(i - 1) then 1 else 0) +. x *. 0.5)
  in
  r *. 0.5
;

value f2rm x =
  let a = f2am x in
  {rm i = if i < Array.length a then a.(i) else False};

value rm2f x = am2f (Array.init 10(*mm*) x.rm);

type real = {re_int : int; re_frac : real_mod_1};

value b2z b = if b then 1 else 0;

value re_add x y =
  {re_int = x.re_int + y.re_int + b2z (carry x.re_frac y.re_frac 0);
   re_frac = rm_add x.re_frac y.re_frac};

value re_opp x = {re_int = - x.re_int - 1; re_frac = rm_opp x.re_frac};
value re_is_neg x = x.re_int < 0;
value re_abs x = if re_is_neg x then re_opp x else x;

value re_norm x =
  {re_int = x.re_int + b2z (carry x.re_frac rm_zero 0);
   re_frac = rm_norm x.re_frac};

value z_odd x = x land 1 <> 0;

value re_div_2 x =
  {re_int = x.re_int / 2;
   re_frac = rm_div_2_inc x.re_frac (z_odd x.re_int)}
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

value rec rm_eucl_div_loop m x y =
  if m < 0 then invalid_arg "rm_eucl_div_loop" else
  match m with
  | 0 → failwith "rm_eucl_div_loop bug: insufficient nb of iterations"
  | _ →
      let m1 = m - 1 in
      if rm_lt x y then (0, x)
      else
        let (q, r) = rm_eucl_div_loop m1 (rm_sub x y) y in
        (1 + q, r)
  end
;

value rec rm_div_eucl_i x y i =
  match i with
  | 0 →
      if rm_lt x y then (False, x) else (True, rm_sub x y)
  | _ →
      let i1 = i - 1 in
      let r = snd (rm_div_eucl_i x y i1) in
(*
let _ = printf "rm_div_eucl %d ok\n%!" i in
*)
      let tr = rm_mul_2 r in
      if rm_lt tr y then (False, tr) else (True, rm_sub tr y)
  end
;

value rm_div_i x y i = fst (rm_div_eucl_i (rm_mul_2 x) y i);
value rm_div x y = {rm = rm_div_i x y};

value rm_eucl_div x y =
  match fst_same x rm_ones 0 with
  | Some jx →
      match fst_same y rm_ones 0 with
      | Some jy →
          if jx ≤ jy then
            let m = two_power (jy - jx + 1) in
            let (q, r) = rm_eucl_div_loop m x y in
            (q, rm_div r y)
          else
            (0, rm_div x y)
      | None → (0, y)
      end
  | None → (0, rm_zero)
  end
;

value (q, r) = rm_eucl_div (f2rm 0.01) (f2rm 0.03);
rm2f r;

value rec rm_equiv_div m x y =
  match m with
  | 0 → failwith "rm_equiv_div bug: insufficient nb of iterations"
  | _ →
      let m1 = m - 1 in
      let x2 = re_div_2 x in
      let y2 = re_div_2 y in
      if x.re_int = 0 && y.re_int = 0 then
        (x2.re_frac, y2.re_frac)
      else
        rm_equiv_div m1 x2 y2
  end
;

(* don't try it with x / y > 7 because the division algorithm is only
   done with subtractions without shifts and it is very very slow if
   x >> y *)
value re_div x y =
  let ax = re_abs x in
  let ay = re_abs y in
  let m = ax.re_int + ay.re_int + 1 in
  let (xm, ym) = rm_equiv_div m ax ay in
  let (q, rm) = rm_eucl_div xm ym in
  {re_int = if re_is_neg x = re_is_neg y then q else -q;
   re_frac = rm}
;

value r = re_div (f2r 1.) (f2r 3.);
printf "%d\n%!" r.re_int;
printf "%f\n%!" (rm2f r.re_frac);

(*
value r = re_div (f2r 355.) (f2r 113.);
printf "%d\n%!" r.re_int;
printf "%f\n%!" (rm2f r.re_frac);
*)
