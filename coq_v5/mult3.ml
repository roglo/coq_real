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

(* C ≤ Σ (k=1,n), u_{i+k}/b^k + (i+n+b/(b-1))/b^n *)
(* Σ (k=1,n), u_{i+k}/b^k + (i+n+b/(b-1))/b^n =
   (Σ (k=1,n), u_{i+k}*b^(n-k) + i+n+b/(b-1)) / b^n
 *)
value partial_carry_bound_num u i n =
  summation 1 n (fun k → u (i + k) * int_pow base.val (n - k))
  + i + n + base.val / (base.val - 1)
;
value partial_carry_bound_den n =
  int_pow base.val n
;

value partial_carry_bound u i n =
  partial_carry_bound_num u i n / partial_carry_bound_den n
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
value u = i_mul_algo (r_of_string "239") (r_of_string "4649");
list_of_seq u 10;
partial_carry_bound u 0 1;
partial_carry_bound u 1 1;
partial_carry_bound u 2 1;
partial_carry_bound u 3 1;
partial_carry_bound u 4 1;
();
(u 0 + partial_carry_bound u 0 1) mod 10;
(u 1 + partial_carry_bound u 1 1) mod 10;
(u 2 + partial_carry_bound u 2 1) mod 10;
(u 3 + partial_carry_bound u 3 1) mod 10;
(u 4 + partial_carry_bound u 4 1) mod 10;

(* 4821*107 = 515847 *)

value u = i_mul_algo (r_of_string "4821") (r_of_string "107");
list_of_seq u 10;
let i = 0 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 1 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 2 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 3 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 4 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 5 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 6 in (u i+partial_carry_bound u i (7-i)) mod 10;

(* 9344*685 = 6400640 *)

value u = i_mul_algo (r_of_string "9344") (r_of_string "685");
list_of_seq u 10;
let i = 0 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 1 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 2 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 3 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 4 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 5 in (u i+partial_carry_bound u i (7-i)) mod 10;
let i = 6 in (u i+partial_carry_bound u i (7-i)) mod 10;
();

let i = 0 in (u i+partial_carry_bound u i 1) mod 10; (* erreur *)
let i = 0 in (u i+partial_carry_bound u i 2) mod 10;
let i = 0 in (u i+partial_carry_bound u i 3) mod 10;
let i = 0 in (u i+partial_carry_bound u i 4) mod 10;
let i = 0 in (u i+partial_carry_bound u i 5) mod 10;
let i = 0 in (u i+partial_carry_bound u i 6) mod 10;
let i = 0 in (u i+partial_carry_bound u i 7) mod 10;
();


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

ith digit =
  (u_i + int (Σ (k=1,∞), u_{i+k} / b^k)) mod b

C = Σ (k=1,∞), u_{i+k}/b^k)
u_i ≤ i(b-1)
C ≤ Σ (k=1,∞), (i+k)(b-1)/b^k

C = u_{i+1}/2 + Σ (k=2,∞), u_{i+k)/b^k
...
C = Σ (k=1,n), u_{i+k}/b^k + Σ (k=n+1,∞), u_{i+k}/b^k
C ≤ Σ (k=1,n), u_{i+k}/b^k + Σ (k=n+1,∞), (i+k)(b-1)/b^k
C ≤ Σ (k=1,n), u_{i+k}/b^k + Σ (k=1,∞), (i+k+n)(b-1)/b^(k+n)
C ≤ Σ (k=1,n), u_{i+k}/b^k + (b-1)/b^n Σ (k=1,∞), (i+k+n)/b^k
C ≤ Σ (k=1,n), u_{i+k}/b^k + (b-1)/b^n M

M = Σ (k=1,∞), (i+k+n)/b^k
M = (i+n) Σ (k=1,∞), 1/b^k + Σ (k=1,∞), k/b^k

1/b+1/b²+1/b³+...+1/b^n = (b^(n-1)+b^(n-2)+...+1)/b^n
                        = (b^n-1)/((b-1)b^n)
→ 1/(b-1) when n → ∞

M = (i+n)/(b-1) + Σ (k=1,∞), k/b^k

x = Σ (k = 1, ∞), k/b^k
x = 1/b + Σ (k = 2, ∞), k/b^k
x = 1/b + Σ (k = 1, ∞), (k+1)/b^(k+1)
x = 1/b + 1/b * Σ (k = 1, ∞), (k+1)/b^k
x = 1/b + 1/b * (Σ (k = 1, ∞), 1/b^k + Σ (k = 1, ∞), k/b^k)
x = 1/b + 1/b * (1/(b-1) + x)
bx = 1 + 1/(b-1) + x
bx - x = 1 + 1/(b-1)
(b-1)x = (b-1+1)/(b-1)
x = b/(b-1)²

M = (i+n)/(b-1) + b/(b-1)²
M = 1/(b-1) ((i+n) + b/(b-1))
M = 1/(b-1) (i + n + b/(b-1))

******* C ≤ Σ (k=1,n), u_{i+k}/b^k + (i+n+b/(b-1))/b^n *******

Si b = 2, C ≤ Σ (k=1,n), u_{i+k}/2^k + (i+n+2)/2^n
Si b = 10, C ≤ Σ (k=1,n), u_{i+k}/10^k + (i+n+10/9)/10^n

value i_mul_i x y =
  let m = i_mul_algo x y in
  fun i →
    (m i + floor (summation (i + 1) ∞ (fun k → m k / base.val ^ (k - i))))
    mod base.val
;

u_i ≤ i
x = Σ (k = 1, ∞), k/2^k
x = 1 + 1/2 * Σ (k = 2, ∞), (k-1)/2^(k-1) = 1 + 1/2 x
1/2 x = 1
x = 2

z₀ = (floor v₀) mod 2
v₀ = Σ (k = 1, ∞), u_k/2^k
0 ≤ v₀ ≤ 2

v₀ = u₁/2 + Σ (k = 2, ∞), u_k/2^k
   =      + 1/2 Σ (k = 1, ∞), u_{k+1}/2^k
v₀ ≤ u₁/2 + 1/2 Σ (k = 1, ∞), (k+1)/2^k
v₀ ≤ u₁/2 + 1/2 (Σ (k = 1, ∞), 1/2^k + Σ (k = 1, ∞), k/2^k)
v₀ ≤ u₁/2 + 1/2 (1 + 2)
v₀ ≤ u₁/2 + 3/2

v₀ = u₁/2 + u₂/4 + Σ (k = 3, ∞), u_k/2^k
v₀ = u₁/2 + u₂/4 + 1/4 Σ (k = 1, ∞), u_{k+2}/2^k
v₀ ≤ u₁/2 + u₂/4 + 1/4 Σ (k = 1, ∞), (k+2)/2^k
v₀ ≤ u₁/2 + u₂/4 + 1/4 (2 Σ (k = 1, ∞), 1/2^k + Σ (k = 1, ∞), k/2^k)
v₀ ≤ u₁/2 + u₂/4 + 1/4 (2 * 1 + 2)
v₀ ≤ u₁/2 + u₂/4 + 1

v₀ ≤ u₁/2 + 3/2
v₀ ≤ u₁/2 + u₂/4 + 1
v₀ ≤ u₁/2 + u₂/4 + u₃/8 + 5/8
v₀ ≤ u₁/2 + u₂/4 + u₃/8 + u₄/16 + 3/8

Σ (k=1,n), u_k/2^k ≤ v₀ ≤ Σ (k=1,n), u_k/2^k + (n+2)/2^n

∀ k ≥ 1, u_k = k → v₀ = 2
∃ n, Σ (k=1,n), u_k/2^k ≥ 1 → v₀ = 1
∃ n, Σ (k=1,n), u_k/2^k + (n+2)/2^n < 1 → v₀ = 0
*)
