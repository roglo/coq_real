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

(* Σ (k=1,n), u_{i+k}/b^k + (i+n+2)/b^n =
   (Σ (k=1,n), u_{i+k}*b^(n-k) + i+n+2) / b^n
 *)
value partial_carry_bound_num u i n =
  summation 1 n (fun k → u (i + k) * int_pow base.val (n - k))
  + i + n + 2
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
(u 1 + partial_carry_bound u 0 1) mod 10;
(u 2 + partial_carry_bound u 1 1) mod 10;
(u 3 + partial_carry_bound u 2 1) mod 10;
(u 4 + partial_carry_bound u 3 1) mod 10;
(u 5 + partial_carry_bound u 4 1) mod 10;

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

ith digit: (u_i + Σ (k=i+1,n), u_k*b^(n-k) / b^n) mod b


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
