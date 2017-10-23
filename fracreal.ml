(* test real numbers *)

type digit = { dig : int };
type fracreal = { freal : int → digit };

type sum α β = [ Inl of α | Inr of β ].

value o_LPO u =
  loop 100 0 where rec loop niter i =
    if niter = 0 then Inl ()
    else if u i = 0 then loop (niter - 1) (i + 1)
    else Inr i
;

value digit_sequence_normalize r u i =
  match o_LPO (fun j → r - 1 - (u (i + j + 1)).dig) with
  | Inl _ →
      if (u i).dig + 1 < r then {dig = (u i).dig + 1}
      else {dig = 0}
  | Inr _ → u i
  end
;

(*
digit_sequence_normalize 10 (fun i -> {dig = if i < 3 then 7 else 9}) 0;
- : digit = {dig=7}
digit_sequence_normalize 10 (fun i -> {dig = if i < 3 then 7 else 9}) 1;
- : digit = {dig=7}
digit_sequence_normalize 10 (fun i -> {dig = if i < 3 then 7 else 9}) 2;
- : digit = {dig=8}
digit_sequence_normalize 10 (fun i -> {dig = if i < 3 then 7 else 9}) 3;
- : digit = {dig=0}
digit_sequence_normalize 10 (fun i -> {dig = if i < 3 then 7 else 9}) 4;
- : digit = {dig=0}
*)

value le_dec a b = a < b.
value pow a b = truncate (float a ** float b);

type radix = { rad : int }.
type digit = { dig : int }.
type fracreal = { freal : int → digit }.

value rad x = x.rad.
value dig x = x.dig.
value freal x = x.freal.

value rec summation_aux b len g =
  match len with
  | 0 → 0
  | _ →
      let len₁ = len - 1 in
      g b + summation_aux (succ b) len₁ g
  end.

value summation b e g = summation_aux b (succ e - b) g;

value sequence_mul (a : int → int) (b : int → int) i =
  summation 0 i (fun j → a j * b (i - j)).

value freal_mul_series (r : radix) a b =
  sequence_mul (fun i → dig (freal a i)) (fun i → dig (freal b i)).

value mul_test_seq (r : radix) i u k =
  let n = rad r * (i + k + 2) in
  if le_dec (pow (rad r) k - 1) (rfrac (A i u n)) then 0 else 1;

value freal_mul_to_seq (r : radix) (a : fracreal) (b : fracreal) i =
  let u = freal_mul_series r a b in
  match o_LPO (mul_test_seq i u) with
  | Inl _ →
      let n = rad * (i + 2) in
      (u i + rint (A i u n) + 1) mod rad
  | Inr (Exist _ j _) →
      let n = rad * (i + j + 2) in
      (u i + rint (A i u n)) mod rad
  end.

value freal_mul (r : radix) (a : fracreal) (b : fracreal) =
  let u = freal_mul_to_seq a b in
  {freal i = mkdig r (u i) (freal_mul_to_seq_lt_rad a b i) }.
