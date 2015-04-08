(* nth try to define multiplication in I = [0..1[ in ℝ *)

open Printf.

value list_of_seq u =
  list_rec [] where rec list_rec l n =
    if n ≤ 0 then l
    else list_rec [u (n-1) :: l] (n-1)
;

value nn_add u v i = u i + v i;

value radix = ref 10;

value d2n d = d mod radix.val;
value n2d n = n;

type real01 = { rm : int → int };

value list_of_r x n =
  let l = list_of_seq x.rm n in
  List.map d2n l
;

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

value i_add_algo x y i = x.rm i + y.rm i;

value i_mul_algo x y i =
  summation 1 i (fun j → b2n (x.rm (j - 1)) * b2n (y.rm (i - j)))
;

value q_floor p q = p / q;

value logn n a =
  loop a a - 1 where rec loop m a =
    match m with
    | 0 → 0
    | _ →
        let m1 = m - 1 in
        if a = 0 then 0
        else 1 + loop m1 (a / n)
    end
;

value z_of_u b n u i =
  (q_floor
    (summation 0 n (fun k → u (i + k) * int_pow b (n - k))) (int_pow b n))
    mod b
;

value i_add x y =
  let u = i_add_algo x y in
  {rm = z_of_u 2 radix.val u}
;

value i2nn x i = d2n (x.rm i);
value nn2i n u =
  let b = radix.val in
  {rm i =
     let s = summation 0 n (fun k → u (i + k) * int_pow b (n - k)) in
     n2d (s / int_pow b n)}
;

value i_add2 x y = nn2i 2 (nn_add (i2nn x) (i2nn y));

(* test problem in coq proof NN2I_add_inj;
   can be removed when problem solved *)
radix.val := 2;
value u i = if i = 1 then 1 else 0;
value v i = if i = 2 then 2 else 0;
"u";
list_of_seq u 10;
list_of_r (nn2i 2 u) 10;
"v";
list_of_seq v 10;
list_of_r (nn2i 2 v) 10;
"u+v";
list_of_r (nn2i 2 (nn_add u v)) 10;
list_of_r (i_add2 (nn2i 2 u) (nn2i 2 v)) 10;

glop;

value i_mul x y =
  let u = i_mul_algo x y in
  {rm i =
     let n = logn radix.val (i * (radix.val - 1) + radix.val) + 2 in
     z_of_u radix.val n u i}
;

value r_of_string s =
  {rm i =
     if i ≥ String.length s then 0
     else
       let c = Char.code s.[i] - Char.code '0' in
       if c >= radix.val then
         failwith
           (sprintf "r_of_string \"%s\" (digit %d is %c > %d)" s i s.[i]
              (radix.val - 1))
       else c}
;

radix.val := 10;

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
value one = {rm i = radix.val-1};
value u = i_mul_algo one one;
(*
list_of_seq u 20;
carry_lower_bound_num u 0 1;
carry_lower_bound_num u 0 2;
carry_lower_bound_num u 0 3;
carry_lower_bound_num u 0 4;
carry_lower_bound_num u 0 5;
carry_lower_bound_num u 0 6;
carry_upper_bound_num u 0 6;
*)

39872*1;
list_of_seq (i_mul (r_of_string "39872") one).rm 20;
3*1;
list_of_seq (i_mul (r_of_string "3") one).rm 20;

value u = i_mul_algo (r_of_string "3") one;
(*
let n = 8 in (carry_lower_bound u 0 n, carry_upper_bound u 0 n);
let n = 9 in (carry_lower_bound u 0 n, carry_upper_bound u 0 n);
let n = 6 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
*)

value x = {rm i = i mod radix.val};

radix.val := 2;
value one = {rm i = radix.val-1};
list_of_seq one.rm 20;
value u = i_mul_algo one one;
list_of_seq u 20;
list_of_seq (i_mul one one).rm 30;
(*
carry_lower_bound u 0 7;
carry_upper_bound u 0 7;
let n = 1 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
let n = 2 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
let n = 3 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
let n = 4 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
let n = 5 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
let n = 6 in (carry_lower_bound_num u 0 n, carry_upper_bound_num u 0 n);
*)

radix.val := 2;
value one = {rm i = radix.val - 1};
list_of_seq (i_mul_algo (r_of_string "1") one) 20;
(* should answer 0.1000... but the 0.0111... is equivalent! *)
list_of_seq (i_mul (r_of_string "1") one).rm 20;

radix.val := 2;
value zero = {rm i = 0};
value x = {rm i = if i < 5 then 0 else 1};
value x0 = i_add x zero;
list_of_seq x.rm 20;
(* this implementation of add does not normalise numbers; this can be
   a good thing but this is strange: how it works? and I have to add
   a function to normalise (0.99999... → 1); how many iterations are
   required for addition? here I put the same as for multiplication
   but perhaps it is different, perhaps 1 iteration is sufficient *)

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
