open Printf.

type real01 = { rm : int → int };

value b2n b = b (*if b then 1 else 0*);

value add a b =
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
  | _ → add (g b) (summation_loop (b + 1) (len - 1) g)
  end.

value summation b e g = summation_loop b (e + 1 - b) g;

value rec int_pow a b =
  if b < 0 then invalid_arg "int_pow"
  else if b = 0 then 1
  else
    let r = a * int_pow a (b - 1) in
    if a > 0 && r < 0 then failwith "int_pow overflow"
    else r
;

value base = ref 2;

value i_mul_algo x y i =
  summation 1 i (fun j → b2n (x.rm (j - 1)) * b2n (y.rm (i - j)))
;

(* Let x, y two real numbers in base b, u their product as number with
   numbers, z their product (i.e. u where carries are propagated).

   Conjecture supposed true:
       ∀ i, zi = (ui + floor C∞) mod b
       with C∞ = Σ (k=1,∞),u_{i+k}/b^k

   C∞ is not computable since it is an infinite summation.

   But C∞ can be bounded from above using a partial summation of n terms
   and an upper bound of the rest, knowing that u_i ≤ i(b-1)².

   Let Cn being this partial summation + upper bound of the rest.

   ∀ n, C∞ ≤ Cn

   The computation gives
                               (i+n)(b-1)+b
   Cn = Σ(k=1,n),u_{i+k}/b^k + ------------
                                   b^n
   num Cn = Σ(k=1,n),u_{i+k}*b^(n-k) + (i+n)(b-1) + b
   den Cn = b^n

   zi = (ui + floor C∞) mod b
   C∞ = min Cn = lim Cn
        n ∈ ℕ    n→∞

   The sequence (Cn) is decreasing; hopefully can be computed using the
   oracle.

   Special case when b=2:
                               i+n+2
   Cn = Σ(k=1,n),u_{i+k}/2^k + -----
                                2^n
   Special case when b=10:
                                9(i+n)+10
   Cn = Σ(k=1,n),u_{i+k}/10^k + ---------
                                  10^n

 *)

value carry_lower_bound_num u i n =
  summation 1 n (fun k → u (i + k) * int_pow base.val (n - k))
;
value carry_upper_bound_num u i n =
  let a = carry_lower_bound_num u i n in
  let b = (i + n) * (base.val - 1) + base.val in
  let c = a + b in
  if b < 0 || c < 0 then failwith "carry_upper_bound_num overflow"
  else c
;
value carry_bound_den n =
  int_pow base.val n
;

value carry_lower_bound u i n =
  let num = carry_lower_bound_num u i n in
  let den = carry_bound_den n in
  if num < 0 || den < 0 then
    failwith (sprintf "carry_lower_bound: overflow (%d iterations)" n)
  else
    num / den
;
value carry_upper_bound u i n =
  let num = carry_upper_bound_num u i n in
  let den = carry_bound_den n in
  if num < 0 || den < 0 then
    failwith (sprintf "carry_upper_bound: overflow (%d iterations)" n)
  else
    num / den
;

value carry u i =
  loop 1 where rec loop n =
    let lb = carry_lower_bound u i n in
    let ub = carry_upper_bound u i n in
    if lb = ub then lb
    else loop (n + 1)
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

value i_mul x y =
  let u = i_mul_algo x y in
  {rm i = (u i + carry u i) mod base.val}
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

value x = {rm i = i mod base.val};

base.val := 2;
value one = {rm i = base.val-1};
list_of_seq one.rm 20;
value u = i_mul_algo one one;
list_of_seq u 20;
carry_lower_bound u 0 7;
carry_upper_bound u 0 7;

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
