(* nth try to define multiplication in I = [0..1[ in ℝ *)

open Printf.

type real01 = { rm : int → int };

value b2n b = b (*if b then 1 else 0*);

value add_check_ov a b =
  if a < 0 then
    failwith (sprintf "summation negative arg %d" a)
  else
    let c = a + b in
    if c < 0 then
      failwith (sprintf "summation overflow %d+%d" a b)
    else c
;

value rec summation_loop b len g =
  match len with
  | 0 → 0
  | _ → add_check_ov (g b) (summation_loop (b + 1) (len - 1) g)
  end.

value summation b e g = summation_loop b (e + 1 - b) g;

value rec int_pow a b =
  if b < 0 then invalid_arg "int_pow"
  else if b = 0 then 1
  else
    let r = a * int_pow a (b - 1) in
    if a > 0 && r < 0 then failwith (sprintf "int_pow overflow %d %d" a b)
    else r
;

value base = ref 10;

value i_mul_algo x y i =
  summation 1 i (fun j → b2n (x.rm (j - 1)) * b2n (y.rm (i - j)))
;

value q_floor p q = p / q;

value summation_for_u2z b n u i =
  summation 0 n (fun k → u (i + k) * int_pow b (n - k))
;

value logn n a = int_of_float (ceil (log (float a) /. log (float n)));

value z_of_u b u i =
  let n = max 3 (logn b (i * (b - 1) + b) + 1) in
  let c = 0 (* ou 1 : à voir *) in
  (q_floor (summation_for_u2z b n u i) (int_pow b n) + c) mod b
;

value i_mul x y =
  let u = i_mul_algo x y in
  {rm = z_of_u base.val u}
;

value r_of_string s =
  {rm i =
     if i ≥ String.length s then 0
     else Char.code s.[i] - Char.code '0'}
;

value list_of_seq u =
  list_rec [] where rec list_rec l n =
    if n ≤ 0 then l
    else list_rec [u (n-1) :: l] (n-1)
;

base.val := 10;

239*4649;
list_of_seq (i_mul (r_of_string "239") (r_of_string "4649")).rm 10;
4821*107;
list_of_seq (i_mul (r_of_string "4821") (r_of_string "107")).rm 10;
9344*685;
list_of_seq (i_mul (r_of_string "9344") (r_of_string "685")).rm 10;
9725*483;
list_of_seq (i_mul (r_of_string "9725") (r_of_string "483")).rm 10;
4656*7532;
list_of_seq (i_mul (r_of_string "4656") (r_of_string "7532")).rm 10;
(* for 64 bits *)
9468025*7023342;
list_of_seq (i_mul (r_of_string "9468025") (r_of_string "7023342")).rm 20;

(* overflows *)
value one = {rm i = base.val-1};
value u = i_mul_algo one one;
list_of_seq u 20;
carry_lower_bound_num u 0 1;
carry_lower_bound_num u 0 2;
carry_lower_bound_num u 0 3;
carry_lower_bound_num u 0 4;
carry_lower_bound_num u 0 5;
carry_lower_bound_num u 0 6;
carry_upper_bound_num u 0 6;

list_of_seq (i_mul (r_of_string "39872") one).rm 20;
list_of_seq (i_mul (r_of_string "3") one).rm 20;

value u = i_mul_algo (r_of_string "3") one;
let n = 8 in (carry_lower_bound u 0 n, carry_upper_bound u 0 n);
let n = 9 in (carry_lower_bound u 0 n, carry_upper_bound u 0 n);
let n = 6 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);

value x = {rm i = i mod base.val};

base.val := 2;
value one = {rm i = base.val-1};
list_of_seq one.rm 20;
value u = i_mul_algo one one;
list_of_seq u 20;
carry_lower_bound u 0 7;
carry_upper_bound u 0 7;
let n = 1 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
let n = 2 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
let n = 3 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
let n = 4 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
let n = 5 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
let n = 6 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);

(*
# 9344*685;
- : int = 6400640

           9  3  4  4
           x  6  8  5
      ---------------
          45 15 20 20
       72 24 32 32
    54 18 24 24
    -----------------
  0 54 90 93 71 52 20

# (0+(((((54*10+90)*10+93)*10+71)*10+52)*10+20)/1000000) mod 10;
- : int = 6
# (54+((((90*10+93)*10+71)*10+52)*10+20)/100000) mod 10;
- : int = 4
# (90+(((93*10+71)*10+52)*10+20)/10000) mod 10;
- : int = 0
# (93+((71*10+52)*10+20)/1000) mod 10;
- : int = 0
# (71+(52*10+20)/100) mod 10;
- : int = 6
# (52+20/10) mod 10;
- : int = 4
# (20/1) mod 10;
- : int = 0
*)

