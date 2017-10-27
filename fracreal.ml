(* test real numbers *)

#load "nums.cma";

type sum α β = [ Inl of α | Inr of β ].
type tsig α = [ Exist of unit and α and unit ].

type digit = { dig : int };
type fracreal = { freal : int → digit };

value mkdig _ x _ = {dig = x};

value o_LPO u =
  loop 20 0 where rec loop niter i =
    if niter = 0 then Inl ()
    else if u i = 0 then loop (niter - 1) (i + 1)
    else Inr (Exist () i ())
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

value pow a b = truncate (float a ** float b);

module type IntSig =
  sig
    type t = 'abstract;
    value zero : t;
    value succ : t → t;
    value pred : t → t;
    value add : t → t → t;
    value mul : t → t → t;
    value div : t → t → t;
    value dmod : t → t → t;
    value modi : t → int → int;
    value pow : int → int → t;
    value le_dec : t → t → bool;
    value of_int : int → t;
    value to_string : t → string;
  end;

module Int : IntSig =
  struct
    open Big_int;
    type t = big_int;
    value zero = zero_big_int;
    value succ = succ_big_int;
    value pred = pred_big_int;
    value add = add_big_int;
    value mul = mult_big_int;
    value div = div_big_int;
    value dmod = mod_big_int;
    value modi a i = int_of_big_int (mod_big_int a (big_int_of_int i));
    value pow = power_int_positive_int;
    value le_dec = le_big_int;
    value of_int = big_int_of_int;
    value to_string = string_of_big_int;
  end;

type radix = { rad : int }.
type rational = { num : Int.t; den : Int.t }.
type fracreal = { freal : int → digit }.

value rad x = x.rad.
value dig x = x.dig.
value freal x = x.freal.
value mkrat n d = {num = n; den = d}.
value num q = q.num;
value den q = q.den;

value rint q = Int.div (num q) (den q).
value rfrac q = mkrat (Int.dmod (num q) (den q)) (den q).

value rec summation_aux b len g =
  match len with
  | 0 → Int.zero
  | _ →
      let len₁ = len - 1 in
      Int.add (g b) (summation_aux (succ b) len₁ g)
  end.

value summation b e g = summation_aux b (succ e - b) g;

value sequence_mul a b i =
  summation 0 i (fun j → Int.mul (a j) (b (i - j))).

value freal_mul_series (r : radix) a b i =
  match i with
  | 0 → Int.zero
  | _ →
      let i' = i - 1 in
      sequence_mul
        (fun i → Int.of_int (dig (freal a i)))
	(fun i → Int.of_int (dig (freal b i))) i'
  end.

value nA (r : radix) i u n =
  mkrat
    (summation (i + 1) (n - 1)
       (fun j → Int.mul (u j) (Int.pow (rad r) (n - 1 - j))))
    (Int.pow (rad r) (n - 1 - i)).

value mul_test_seq (r : radix) i u k =
  let n = rad r * (i + k + 2) in
  if Int.le_dec
    (Int.pred (Int.pow (rad r) k))
    (Int.div
      (Int.mul (Int.pow (rad r) k) (num (rfrac (nA r i u n))))
      (den (rfrac (nA r i u n))))
  then 0
  else 1
;

value freal_mul_to_seq (r : radix) (a : fracreal) (b : fracreal) i =
  let u = freal_mul_series r a b in
  match o_LPO (mul_test_seq r i u) with
  | Inl _ →
      let n = rad r * (i + 2) in
      Int.modi (Int.add (u i) (Int.succ (rint (nA r i u n)))) (rad r)
  | Inr (Exist _ j _) →
      let n = rad r * (i + j + 2) in
      Int.modi (Int.add (u i) (rint (nA r i u n))) (rad r)
  end.

value freal_mul_to_seq_lt_rad a b i = ();

value freal_mul (r : radix) (a : fracreal) (b : fracreal) =
  let u = freal_mul_to_seq r a b in
  {freal i = mkdig r (u i) (freal_mul_to_seq_lt_rad a b i) }.

value mkr u = {freal i = mkdig () (u i) ()};
value rzero = mkr (fun _ -> 0);
value rhalf = mkr (fun i -> if i = 0 then 5 else 0);

value prr {freal = r} i = r i;
prr (freal_mul {rad=10} rhalf rhalf) 0;
prr (freal_mul {rad=10} rhalf rhalf) 1;
prr (freal_mul {rad=10} rhalf rhalf) 2;

value rquat = freal_mul {rad=10} rhalf rhalf;
value r = mkr (fun i -> if i = 0 then 3 else 0);
