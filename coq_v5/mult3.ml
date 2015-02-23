open Printf.

type real01 = { rm : int → int };

value b2n b = b (*if b then 1 else 0*);

value rec summation_loop b len g =
  match len with
  | 0 → 0
  | _ → g b + summation_loop (b + 1) (len - 1) g
  end.

value summation b e g = summation_loop b (e + 1 - b) g;

value base = ref 2;

value i_mul_algo x y i =
  summation 1 i (fun j → b2n (x.rm (j - 1)) * b2n (y.rm (i - j)))
;

value carry m i =
  loop 0 i 1 where rec loop num k base_pow_k_sub_i =
    if
    loop (base.val * num + m k) (k + 1) (base.val * base_pow_k_sub_i)
;

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

v₀ ≤ Σ (k=1,n), u_k/2^k + (n+2)/2^n
