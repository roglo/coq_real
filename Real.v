Require Import Utf8 QArith.

Open Scope nat_scope.

(* reals modulo 1 *)
Record real_mod_1 := { rm : nat → bool }.

Axiom fst_same x y i : real_mod_1 → real_mod_1 → nat → option nat.

Axiom fst_same_iff : ∀ x y i odi,
  fst_same x y i = odi ↔
  match odi with
  | Some di =>
      (∀ dj, dj < di → rm x (i + dj) ≠ rm y (i + dj))
      ∧ rm x (i + di) = rm y (i + di)
  | None =>
      ∀ dj, rm x (i + dj) ≠ rm y (i + dj)
  end.

Definition rm_add x y i :=
  match fst_same x y i with
  | Some di =>
      (* x[i+di]=y[i+di] *)
      if zerop di then
        (* x[i]=y[i] *)
        match fst_same x y (S i) with
        | Some dj =>
            (* x[i+dj]=y[i+dj] *)
            xorb (rm x i) (rm x (i + dj))
        | None =>
            false
        end
      else negb (rm x (i + di))
  | None =>
      true
  end.

Close Scope nat_scope.
