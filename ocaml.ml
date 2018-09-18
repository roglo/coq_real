(* implementation of reals between 0 and 1 *)

(*
ocaml -I +site-lib/camlp5 camlp5r.cma nums.cma
*)

open Big_int;

value lpo_max = 20;

type real01 = { freal : int → int; freal_comp : Hashtbl.t int int }.

value max_i = ref 0;

value make_real f = {freal = f; freal_comp = Hashtbl.create 1}.
value real_val x i =
(*
  x.freal i.
*)
  try Hashtbl.find x.freal_comp i with
  | Not_found → do {
      max_i.val := max i max_i.val;
      let v = x.freal i in
      Hashtbl.add x.freal_comp i v;
      v
    }
  end.
(**)

value rec list_seq start len =
  if len ≤ 0 then []
  else [start :: list_seq (start + 1) (len - 1)].

value rec pow a n =
   if n ≤ 0 then unit_big_int
   else mult_int_big_int a (pow a (n - 1)).

value rec summation_aux b len g =
  if len ≤ 0 then 0
  else g b + summation_aux (b + 1) (len - 1) g.

value summation b e g =
  summation_aux b (e + 1 - b) g.

value rec big_int_summation_aux b len g =
  if len ≤ 0 then zero_big_int
  else add_big_int (g b) (big_int_summation_aux (b + 1) (len - 1) g).

value big_int_summation b e g =
  big_int_summation_aux b (e + 1 - b) g.

value nA r i n u =
  big_int_summation (i + 1) (n - 1)
    (fun j → mult_int_big_int (u j) (pow r (n - 1 - j))).

(* suitable for multiplications *)
value min_n r i k = r * (i + k + 3);
(* suitable for additions *)
(**)
value min_n r i k = i + k + 4;
(**)

value a_ge_1 r u i k =
  let n = min_n r i k in
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
      let n = min_n r i 0 in
      succ_big_int (div_big_int (nA r i n u) (pow r (n - i - 1)))
  | Some k →
      let n = min_n r i k in
      div_big_int (nA r i n u) (pow r (n - i - 1))
  end.

value prop_carr r u i =
  let d = add_int_big_int (u i) (nat_prop_carr r u i) in
  int_of_big_int (mod_big_int d (big_int_of_int r)).

value freal_series_add x y i = real_val x i + real_val y i.
value freal_series_mul x y i =
  match i with
  | 0 → 0
  | _ → summation 0 (i - 1) (fun j → real_val x j * real_val y (i - 1 - j))
  end.

value freal_add r x y =
  make_real (prop_carr r (freal_series_add x y));
value freal_mul r x y =
  make_real (prop_carr r (freal_series_mul x y));

value real_val_n n x =
  List.map (real_val x) (list_seq 0 n).

value freal345 =
  make_real (fun i → match i with | 0 → 3 | 1 → 4 | 2 → 5 | _ → 0 end);
value freal817 =
  make_real (fun i → match i with | 0 → 8 | 1 → 1 | 2 → 7 | _ → 0 end).
real_val_n 5 freal345;
real_val_n 5 freal817;
real_val_n 5 (freal_add 10 freal345 freal817);

value freal1_3 = make_real (fun i → 3);
value freal1_6 = make_real (fun i → 6);
real_val_n 10 freal1_3;
real_val_n 10 freal1_6;
real_val_n 10 (freal_add 10 freal1_3 freal1_6);

value frealx = make_real (fun i → if i < 10 then 6 else 0).
real_val_n 13 freal1_3;
real_val_n 13 frealx;
real_val_n 13 (freal_add 10 freal1_3 frealx);

value freal1_2 = make_real (fun i → if i = 0 then 5 else 0).
real_val_n 3 (freal_mul 10 freal1_2 freal1_2).

value freal1_7 =
  make_real
    (fun i →
     match i mod 6 with
     | 0 → 1 | 1 → 4 | 2 → 2
     | 3 → 8 | 4 → 5 | _ → 7
     end).
value freal07 = make_real (fun i → if i = 0 then 7 else 0).
real_val_n 8 freal1_7;
real_val_n 8 freal07;
real_val_n 8 (freal_mul 10 freal1_7 freal07);
value freal0n n = make_real (fun i → if i = 0 then n else 0).
real_val_n 12 freal1_7;
real_val_n 12 (freal0n 2);
real_val_n 12 (freal_mul 10 freal1_7 (freal0n 2));
