Require Import Utf8.

Notation "a ^ b" := (Nat.pow a b).

Theorem small : ∀ r, r ≥ 2 →
  ∀ i n, n ≥ r * (i + 2) → n * (r - 1) + r < r ^ (n - (i + 1)).
