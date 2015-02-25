open Printf.

type real01 = { rm : int → int };

value b2n b = b (*if b then 1 else 0*);

value rec summation_loop b len g =
  match len with
  | 0 → 0
  | _ → g b + summation_loop (b + 1) (len - 1) g
  end.

value summation b e g = summation_loop b (e + 1 - b) g;

value rec int_pow a b = if b ≤ 0 then 1 else a * int_pow a (b - 1);

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

value carry_upper_bound_num u i n =
  summation 1 n (fun k → u (i + k) * int_pow base.val (n - k))
  + (i + n) * (base.val - 1) + base.val
;
value carry_upper_bound_den n =
  int_pow base.val n
;

value carry_upper_bound u i n =
  let num = carry_upper_bound_num u i n in
  let den = carry_upper_bound_den n in
  num / den
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

(* 239*4649 = 1111111 *)

value u = i_mul_algo (r_of_string "239") (r_of_string "4649");
list_of_seq u 10;
239*4649;
let i = 0 in (u i+carry_upper_bound u i 2) mod 10;
let i = 1 in (u i+carry_upper_bound u i 2) mod 10;
let i = 2 in (u i+carry_upper_bound u i 2) mod 10;
let i = 3 in (u i+carry_upper_bound u i 2) mod 10;
let i = 4 in (u i+carry_upper_bound u i 2) mod 10;
let i = 5 in (u i+carry_upper_bound u i 1) mod 10;
let i = 6 in (u i+carry_upper_bound u i 1) mod 10;

(* 4821*107 = 515847 *)

value u = i_mul_algo (r_of_string "4821") (r_of_string "107");
list_of_seq u 10;
4821*107;
let i = 0 in (u i+carry_upper_bound u i (7-i)) mod 10;
let i = 1 in (u i+carry_upper_bound u i (7-i)) mod 10;
let i = 2 in (u i+carry_upper_bound u i (7-i)) mod 10;
let i = 3 in (u i+carry_upper_bound u i (7-i)) mod 10;
let i = 4 in (u i+carry_upper_bound u i (7-i)) mod 10;
let i = 5 in (u i+carry_upper_bound u i 3) mod 10;
let i = 6 in (u i+carry_upper_bound u i 2) mod 10;

(* 9344*685 = 6400640 *)

value u = i_mul_algo (r_of_string "9344") (r_of_string "685");
list_of_seq u 10;
9344*685;
let i = 0 in (u i+carry_upper_bound u i (7-i)) mod 10;
let i = 1 in (u i+carry_upper_bound u i (7-i)) mod 10;
let i = 2 in (u i+carry_upper_bound u i (7-i)) mod 10;
let i = 3 in (u i+carry_upper_bound u i (7-i)) mod 10;
let i = 4 in (u i+carry_upper_bound u i (7-i)) mod 10;
let i = 5 in (u i+carry_upper_bound u i (7-i)) mod 10;
let i = 6 in (u i+carry_upper_bound u i 2) mod 10;
();

let i = 0 in (u i+carry_upper_bound u i 1) mod 10;
let i = 0 in (u i+carry_upper_bound u i 2) mod 10;
let i = 0 in (u i+carry_upper_bound u i 3) mod 10;
let i = 0 in (u i+carry_upper_bound u i 4) mod 10;
let i = 0 in (u i+carry_upper_bound u i 5) mod 10;
let i = 0 in (u i+carry_upper_bound u i 6) mod 10;
let i = 0 in (u i+carry_upper_bound u i 7) mod 10;
();

let i = 0 in (carry_upper_bound_num u i 1, carry_upper_bound_den 1);
let i = 1 in (carry_upper_bound_num u i 1, carry_upper_bound_den 1);

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
