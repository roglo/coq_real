Require Import Utf8 QArith NPeano.
Require Import Real01.

Open Scope nat_scope.

Definition b2n (b : bool) := if b then 1 else 0.

Definition I_add_wn_i x y i := b2n (x.[i]) + b2n (y.[i]).

Definition I_add_wn x y := {| inat := I_add_wn_i x y |}.

Definition carry x i :=
  match fst_not_1 x i with
  | Some di => inat x (i + di)
  | None => 1
  end.

Definition Iwn2I x i := Nat.eqb (inat x i) 0 ⊕ Nat.eqb (carry x (S i)) 0.

Definition I_add x y := {| idig := Iwn2I (I_add_wn x y) |}.
