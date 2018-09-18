(* implementation of reals between 0 and 1 *)
(* translated from coq version and adapted *)

(*
ocaml -I +site-lib/camlp5 camlp5r.cma nums.cma
*)

open Big_int;

value lpo_max = 20;

type real01 = { rseq : int → int; rseq_comp : Hashtbl.t int int }.

value max_i = ref 0;

value make_real01 f = {rseq = f; rseq_comp = Hashtbl.create 1}.
value real01_val x i =
(*
  x.rseq i.
*)
  try Hashtbl.find x.rseq_comp i with
  | Not_found → do {
      max_i.val := max i max_i.val;
      let v = x.rseq i in
      Hashtbl.add x.rseq_comp i v;
      v
    }
  end.
(**)

value rec list_seq start len =
  if len ≤ 0 then []
  else [start :: list_seq (start + 1) (len - 1)].

value pow = power_int_positive_int;

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

value a_ge_1 r min_n u i k =
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

value nat_prop_carr r min_n u i =
  match lpo_fst (a_ge_1 r min_n u i) with
  | None →
      let n = min_n r i 0 in
      succ_big_int (div_big_int (nA r i n u) (pow r (n - i - 1)))
  | Some k →
      let n = min_n r i k in
      div_big_int (nA r i n u) (pow r (n - i - 1))
  end.

value prop_carr r min_n u i =
  let d = add_int_big_int (u i) (nat_prop_carr r min_n u i) in
  int_of_big_int (mod_big_int d (big_int_of_int r)).

value real01_series_add x y i = real01_val x i + real01_val y i.
value real01_series_mul x y i =
  if i = 0 then 0
  else
    summation 0 (i - 1) (fun j → real01_val x j * real01_val y (i - 1 - j)).

value min_n_add r i k = i + k + 4;
value min_n_mul r i k = r * (i + k + 3);

value real01_add r x y =
  make_real01 (prop_carr r min_n_add (real01_series_add x y));
value real01_mul r x y =
  make_real01 (prop_carr r min_n_mul (real01_series_mul x y));

value real01_val_n n x =
  List.map (real01_val x) (list_seq 0 n).

value real345 =
  make_real01 (fun i → match i with | 0 → 3 | 1 → 4 | 2 → 5 | _ → 0 end);
value real817 =
  make_real01 (fun i → match i with | 0 → 8 | 1 → 1 | 2 → 7 | _ → 0 end).
real01_val_n 5 real345;
real01_val_n 5 real817;
real01_val_n 5 (real01_add 10 real345 real817);

value real1_3 = make_real01 (fun i → 3);
value real1_6 = make_real01 (fun i → 6);
real01_val_n 10 real1_3;
real01_val_n 10 real1_6;
real01_val_n 10 (real01_add 10 real1_3 real1_6);

value realx = make_real01 (fun i → if i < 10 then 6 else 0).
real01_val_n 13 real1_3;
real01_val_n 13 realx;
real01_val_n 13 (real01_add 10 real1_3 realx);

value real1_2 = make_real01 (fun i → if i = 0 then 5 else 0).
real01_val_n 3 (real01_mul 10 real1_2 real1_2).

value real1_7 =
  make_real01
    (fun i →
     match i mod 6 with
     | 0 → 1 | 1 → 4 | 2 → 2
     | 3 → 8 | 4 → 5 | _ → 7
     end).
value real07 = make_real01 (fun i → if i = 0 then 7 else 0).
real01_val_n 8 real1_7;
real01_val_n 8 real07;
real01_val_n 8 (real01_mul 10 real1_7 real07);
value real0n n = make_real01 (fun i → if i = 0 then n else 0).
real01_val_n 12 real1_7;
real01_val_n 12 (real0n 2);
real01_val_n 12 (real01_mul 10 real1_7 (real0n 2));
