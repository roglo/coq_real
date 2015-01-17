open Printf;

type real_mod_1 = { rm : int → bool };

value di_max = 30;
value mm = 50;
value mm1 = ref 11;

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

type comparison = [ Eq | Lt | Gt ].

value i_compare x y =
  let nx = i_norm x in
  match fst_same nx (i_opp (i_norm y)) 0 with
  | Some j → if nx.rm j then Gt else Lt
  | None → Eq
  end;

value i_lt x y = i_compare x y = Lt;

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
  if x < 0. || x >= 1.0 then invalid_arg "f2rm"
  else
    let a = f2am x in
    {rm i = if i < Array.length a then a.(i) else False};

value rm2f x = am2f (Array.init mm1.val x.rm);

value rec two_power n =
  if n < 0 then invalid_arg "two_power" else
  match n with
  | 0 → 1
  | _ →
      let n1 = n - 1 in
      2 * two_power n1
  end.

(* division in I - new version *)

value i_div_max_iter_int x y =
  match fst_same y i_ones 0 with
  | Some j → two_power (j + 1)
  | None → 0
  end.

value i_div_2_inc x b = {rm i = if i = 0 then b else x.rm (i-1)}.
value i_div_2 x = i_div_2_inc x False.

value i_mul_2 x = {rm i = x.rm (i+1)}.

value rec i_div_rem_i x y i =
  match i with
  | 0 → x
  | _ →
      let i1 = i - 1 in
      let x1 = i_mul_2 (i_div_rem_i x y i1) in
      if i_lt x1 y then x1 else i_sub x1 y
  end.

value i_div_lt_i x y i =
  if i_lt (i_mul_2 (i_div_rem_i x y i)) y then False else True;

value i_div_lt x y = {rm = i_div_lt_i (i_div_2 x) (i_div_2 y)}.

value rec i_div_int m x y =
  match m with
  | 0 → 0
  | _ →
      let m1 = m - 1 in
      if i_lt x y then 0
      else i_div_int m1 (i_sub x y) y + 1
  end.

value rec i_div_frac m x y =
  match m with
  | 0 → i_zero
  | _ →
      let m1 = m - 1 in
      if i_lt x y then i_div_lt x y
      else i_div_frac m1 (i_sub x y) y
  end.

value i_div x y = i_div_frac (i_div_max_iter_int x y) x y.

(* experimentation *)

value i_div_2_pow x i = {rm j = if j < i then False else x.rm (j-i)}.

value rec i_div_by_sub x y =
  if i_lt x y then False else not (i_div_by_sub (i_sub x y) y).

value i_div3_lt_i x y i =
let _ = printf "i_div_3_lt_i %d\n%!" i in
  if i > 4 then False else
  i_div_by_sub x (i_div_2_pow y (i+1)).

value i_div3_lt x y = {rm = i_div3_lt_i x y};

value rec i_div3_frac m x y =
  match m with
  | 0 → i_zero
  | _ →
      let m1 = m - 1 in
      if i_lt x y then i_div3_lt x y
      else i_div3_frac m1 (i_sub x y) y
  end.

value i_div3 x y = i_div3_frac (i_div_max_iter_int x y) x y.

(**)

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

(* OLD VERSION

(* division using only subtractions; computation of integer part *)

value rec i_div_eucl_i x y i =
  match i with
  | 0 →
      if i_lt x y then (False, x) else (True, i_sub x y)
  | _ →
      let i1 = i - 1 in
      let r = snd (i_div_eucl_i x y i1) in
(*
let _ = printf "i_div_eucl %f/%f %d = %f ok\n%!" (rm2f x) (rm2f y) i (rm2f r)
in
*)
      let tr = i_mul_2 r in
(*
let _ = printf "tr ok\n%!" in
let _ = printf "tr = %f\n%!" (rm2f tr) in
*)
      if i_lt tr y then (False, tr) else (True, i_sub tr y)
  end
;

value i_div_i x y i = fst (i_div_eucl_i (i_mul_2 x) y i);
value old_i_div x y = {rm = i_div_i x y};

value rec r_frac_equiv_div m x y =
  match m with
  | 0 → failwith "r_frac_equiv_div bug: insufficient nb of iterations"
  | _ →
      let m1 = m - 1 in
      let x2 = r_div_2 x in
      let y2 = r_div_2 y in
      if x.r_int = 0 && y.r_int = 0 then
        (x2.r_frac, y2.r_frac)
      else
        r_frac_equiv_div m1 x2 y2
  end
;

value max_iter_int_part ax ay = ax.r_int + ay.r_int + 1;

value rec r_div_r_int_loop m ax ay =
  match m with
  | 0 → 0
  | _ →
       let m1 = m - 1 in
       if r_lt ax ay then 0
       else 1 + r_div_r_int_loop m1 (r_sub ax ay) ay
  end.

value r_div_r_int ax ay =
  r_div_r_int_loop (max_iter_int_part ax ay) ax ay.

value max_iter_frac_part xm ym =
  match fst_same xm i_ones 0 with
  | Some jx →
      match fst_same ym i_ones 0 with
      | Some jy → two_power (max 1 (jy - jx + 1))
      | None → 0
      end
  | None → 0
  end
;

value rec r_div_r_frac_loop m x y =
  if m < 0 then invalid_arg "r_div_r_frac_loop" else
  match m with
  | 0 → failwith "r_div_r_frac_loop bug: insufficient nb of iterations"
  | _ →
      let m1 = m - 1 in
      if i_lt x y then x
      else r_div_r_frac_loop m1 (i_sub x y) y
  end
;

value r_div_r_frac ax ay =
  let m1 = max_iter_int_part ax ay in
  let (xm, ym) = r_frac_equiv_div m1 ax ay in
  let m2 = max_iter_frac_part xm ym in
(*
let _ = printf "m2 = %d\n%!" m2 in
*)
  if m2 = 0 then i_zero
  else
    let rm = r_div_r_frac_loop m2 xm ym in
    old_i_div rm ym
;

(* don't try it with x / y > 7 because the division algorithm is only
   done with subtractions without shifts and it is very very slow if
   x >> y *)
value r_div x y =
  let ax = r_abs x in
  let ay = r_abs y in
  let q = r_div_r_int ax ay in
  let r = r_div_r_frac ax ay in
  {r_int = if r_is_neg x = r_is_neg y then q else -q;
   r_frac = r}
;

value r = r_div_r_frac (f2r 0.01) (f2r 0.03);
rm2f r;
*)

value r_div_max_iter ax ay = ax.r_int + ay.r_int + 1;

value rec r_div_equiv m x y =
  match m with
  | 0 → failwith "r_div_equiv bug: insufficient nb of iterations"
  | _ →
      let m1 = m - 1 in
      if x.r_int = 0 && y.r_int = 0 then
        let (i, f) = i_div x.r_frac y.r_frac in
        {r_int = i; r_frac = f}
      else
        r_div_equiv m1 (r_div_2 x) (r_div_2 y)
  end.

value r_div x y = r_div_equiv (r_div_max_iter x y) x y.

(* *)

value r = r_div (f2r 1.) (f2r 3.);
printf "1/3 i=%d\n%!" r.r_int;
printf "1/3 f=%f\n%!" (rm2f r.r_frac);

value r = r_div (f2r 8.) (f2r 7.);
printf "8/7 i=%d\n%!" r.r_int;
printf "8/7 f=%f\n%!" (rm2f r.r_frac);

(* pourquoi est-ce si lent ?
value r = r_div (f2r 10.) (f2r 7.);
printf "10/7 i=%d\n%!" r.r_int;
printf "10/7 f=%f\n%!" (rm2f r.r_frac);
*)

(*
value r = r_div (f2r 355.) (f2r 113.);
printf "%d\n%!" r.r_int;
printf "%f\n%!" (rm2f r.r_frac);
*)
