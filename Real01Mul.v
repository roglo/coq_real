Require Import Real01Add.

(*
carry        1  2  3  4  5  6  7  8  9 10 11 12 12 12 11  8  ?
#1           ₀  ₁  ₂  ₃  ₄  ₅  ₆  ₇  ₈  ₉ ₁₀ ₁₁ ₁₂ ₁₃ ₁₄ ₁₅ ₁₆
x>>1      0. 0  1  1  1  1  1  1  1  1  1  1  1  1  1  1  1  1
x>>2      0. 0  0  1  1  1  1  1  1  1  1  1  1  1  1  1  1  1
x>>3      0. 0  0  0  1  1  1  1  1  1  1  1  1  1  1  1  1  1
          ...
          0. 1  1  1  1  1  1  1  1  1  1  1  1  0  1  1  1  ?

conjecture: carry x y i ≤ i+1
*)
