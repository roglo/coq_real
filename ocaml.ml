(* implementation of reals between 0 and 1 *)

open Big_int;

type real01 = { freal : int → int }.

value lpo_max = 20;

value big_int_0 = big_int_of_int 0;
value big_int_1 = big_int_of_int 1;

value rec pow a n =
   if n = 0 then big_int_1
   else mult_int_big_int a (pow a (n - 1)).

value rec summation_aux b len g =
  match len with
  | 0 → big_int_0
  | _ → add_big_int (g b) (summation_aux (b + 1) (len - 1) g)
  end.

value summation b e g =
  summation_aux b (e + 1 - b) g.

value nA r i n u =
  summation (i + 1) (n - 1)
    (fun j → mult_int_big_int (u j) (pow r (n - 1 - j))).

value a_ge_1 r u i k =
  let n = r * (i + k + 3) in
  let s = n - i - 1 in
  if lt_big_int
     (mod_big_int (nA r i n u) (pow r s))
     (mult_big_int
        (pred_big_int (pow r (k + 1)))
        (pow r (s - k - 1))) then False
  else True.

value lpo_fst u =
  loop lpo_max 0 where rec loop n k =
    if n = 0 then None
    else if u k then loop (n - 1) (k + 1)
    else Some k.

value nat_prop_carr r u i =
  match lpo_fst (a_ge_1 r u i) with
  | None →
      let n = r * (i + 3) in
      succ_big_int (div_big_int (nA r i n u) (pow r (n - i - 1)))
  | Some k →
      let n = r * (i + k + 3) in
      div_big_int (nA r i n u) (pow r (n - i - 1))
  end.

value prop_carr r u i =
  let d = add_int_big_int (u i) (nat_prop_carr r u i) in
  int_of_big_int (mod_big_int d (big_int_of_int r)).

value freal_series_add x y i = x.freal i + y.freal i.

value freal_add r x y = { freal = prop_carr r (freal_series_add x y) }.

value freal345 =
  {freal i = match i with | 0 → 3 | 1 → 4 | 2 → 5 | _ → 0 end} .
value freal817 =
  {freal i = match i with | 0 → 8 | 1 → 1 | 2 → 7 | _ → 0 end} .

(freal_add 10 freal345 freal817).freal 0;
(freal_add 10 freal345 freal817).freal 1;
(freal_add 10 freal345 freal817).freal 2;
(freal_add 10 freal345 freal817).freal 3;

value freal1_3 = {freal i = 3};
value freal1_6 = {freal i = 6};
(freal_add 10 freal1_3 freal1_6).freal 0;
(freal_add 10 freal1_3 freal1_6).freal 1;

value frealx = {freal i = if i < 10 then 6 else 0};
(freal_add 10 freal1_3 frealx).freal 0;
(freal_add 10 freal1_3 frealx).freal 1;
(freal_add 10 freal1_3 frealx).freal 2;
(freal_add 10 freal1_3 frealx).freal 3;
(freal_add 10 freal1_3 frealx).freal 4;
(freal_add 10 freal1_3 frealx).freal 5;
(freal_add 10 freal1_3 frealx).freal 6;
(freal_add 10 freal1_3 frealx).freal 7;
(freal_add 10 freal1_3 frealx).freal 8;
(freal_add 10 freal1_3 frealx).freal 9;
(freal_add 10 freal1_3 frealx).freal 10;
