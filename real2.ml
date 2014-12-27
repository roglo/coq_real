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

value i_add_i x y i = x.rm i <> y.rm i <> carry x y (i + 1);
value i_add x y = {rm = i_add_i x y};
value i_opp x = {rm i = not (x.rm i)};
value i_sub x y = i_add x (i_opp y);
value i_zero = {rm _ = False};
value i_ones = {rm _ = True};
value i_norm x = i_add x i_zero;
value i_mul_2 x = {rm i = x.rm (i + 1)};
value i_div_2_inc x n =
  {rm i = if i = 0 then n else x.rm (i - 1)};

type comparison = [ Eq | Lt | Gt ].

value i_compare x y =
  let nx = i_norm x in
  match fst_same nx (i_opp (i_norm y)) 0 with
  | Some j → if nx.rm j then Gt else Lt
  | None → Eq
  end;

value i_lt x y = i_compare x y = Lt;

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

type real = {r_int : int; r_frac : real_mod_1};

value b2z b = if b then 1 else 0;

value r_add x y =
  {r_int = x.r_int + y.r_int + b2z (carry x.r_frac y.r_frac 0);
   r_frac = i_add x.r_frac y.r_frac};

value r_opp x = {r_int = - x.r_int - 1; r_frac = i_opp x.r_frac};
value r_sub x y = r_add x (r_opp y);
value r_is_neg x = x.r_int < 0;
value r_abs x = if r_is_neg x then r_opp x else x;

value r_norm x =
  {r_int = x.r_int + b2z (carry x.r_frac i_zero 0);
   r_frac = i_norm x.r_frac};

value z_odd x = x land 1 <> 0;

value r_div_2 x =
  {r_int = x.r_int / 2;
   r_frac = i_div_2_inc x.r_frac (z_odd x.r_int)}
;

value f2r a = {r_int = truncate (floor a); r_frac = f2rm (a -. floor a)};
value r2f x = float x.r_int +. rm2f x.r_frac;

(* *)

value zcompare x y =
  if x < y then Lt
  else if x > y then Gt
  else Eq.

value r_compare x y =
  let nx = r_norm x in
  let ny = r_norm y in
  match zcompare nx.r_int ny.r_int with
  | Eq →
      match fst_same nx.r_frac (i_opp ny.r_frac) 0 with
      | Some j → if nx.r_frac.rm j then Gt else Lt
      | None → Eq
      end
  | Lt → Lt
  | Gt → Gt
  end.

value r_lt x y = r_compare x y = Lt.

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

value rec i_eucl_div_loop m x y =
  if m < 0 then invalid_arg "i_eucl_div_loop" else
  match m with
  | 0 → failwith "i_eucl_div_loop bug: insufficient nb of iterations"
  | _ →
      let m1 = m - 1 in
      if i_lt x y then (0, x)
      else
        let (q, r) = i_eucl_div_loop m1 (i_sub x y) y in
        (1 + q, r)
  end
;

value rec i_div_eucl_i x y i =
  match i with
  | 0 →
      if i_lt x y then (False, x) else (True, i_sub x y)
  | _ →
      let i1 = i - 1 in
      let r = snd (i_div_eucl_i x y i1) in
(*
let _ = printf "i_div_eucl %d ok\n%!" i in
*)
      let tr = i_mul_2 r in
      if i_lt tr y then (False, tr) else (True, i_sub tr y)
  end
;

value i_div_i x y i = fst (i_div_eucl_i (i_mul_2 x) y i);
value i_div x y = {rm = i_div_i x y};

value i_eucl_div x y =
  match fst_same x i_ones 0 with
  | Some jx →
      match fst_same y i_ones 0 with
      | Some jy →
          if jx ≤ jy then
            let m = two_power (jy - jx + 1) in
            let (q, r) = i_eucl_div_loop m x y in
            (q, i_div r y)
          else
            (0, i_div x y)
      | None → (0, y)
      end
  | None → (0, i_zero)
  end
;

value (q, r) = i_eucl_div (f2rm 0.01) (f2rm 0.03);
rm2f r;

value rec i_equiv_div m x y =
  match m with
  | 0 → failwith "i_equiv_div bug: insufficient nb of iterations"
  | _ →
      let m1 = m - 1 in
      let x2 = r_div_2 x in
      let y2 = r_div_2 y in
      if x.r_int = 0 && y.r_int = 0 then
        (x2.r_frac, y2.r_frac)
      else
        i_equiv_div m1 x2 y2
  end
;

value max_iter_int_part ax ay = ax.r_int + ay.r_int + 1;

value rec r_int_div_loop m ax ay =
  match m with
  | 0 → 0
  | _ →
       let m1 = m - 1 in
       if r_lt ax ay then 0
       else 1 + r_int_div_loop m1 (r_sub ax ay) ay
  end.

value r_int_div ax ay =
  r_int_div_loop (max_iter_int_part ax ay) ax ay.

(* don't try it with x / y > 7 because the division algorithm is only
   done with subtractions without shifts and it is very very slow if
   x >> y *)
value r_div x y =
  let ax = r_abs x in
  let ay = r_abs y in
  let m = max_iter_int_part ax ay in
  let (xm, ym) = i_equiv_div m ax ay in
  let (q, rm) = i_eucl_div xm ym in
  {r_int = if r_is_neg x = r_is_neg y then q else -q;
   r_frac = rm}
;

value r = r_div (f2r 1.) (f2r 3.);
printf "%d\n%!" r.r_int;
printf "%f\n%!" (rm2f r.r_frac);

(*
value r = r_div (f2r 355.) (f2r 113.);
printf "%d\n%!" r.r_int;
printf "%f\n%!" (rm2f r.r_frac);
*)
