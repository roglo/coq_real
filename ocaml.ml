(* implementation of reals between 0 and 1 *)
(* should use big numbers! *)

type real01 = { freal : int → int }.

value lpo_max = 10;

value rec pow a n =
  if n = 0 then 1 else a * pow a (n - 1).

value rec summation_aux b len g =
  match len with
  | 0 → 0
  | _ → g b + summation_aux (b + 1) (len - 1) g
  end.

value summation b e g =
  summation_aux b (e + 1 - b) g.

value nA r i n u =
  summation (i + 1) (n - 1) (fun j → u j * pow r (n - 1 - j)).

value a_ge_1 r u i k =
  let n = r * (i + k + 3) in
let _ = Printf.eprintf "n = %d\n%!" n in
  let s = n - i - 1 in
let _ = Printf.eprintf "nA .. = %d\n%!" (nA r i n u mod pow r s) in
let _ = Printf.eprintf "pow ... = %d\n%!"
  ((pow r (k + 1) - 1) * pow r (s - k - 1)) in
  if nA r i n u mod pow r s <
     (pow r (k + 1) - 1) * pow r (s - k - 1) then False
  else True.

value lpo_fst u =
  loop lpo_max 0 where rec loop n k =
    if n = 0 then None
    else if u k then loop (n - 1) (k + 1)
    else Some k.

value nat_prop_carr r u i =
  match lpo_fst (a_ge_1 r u i) with
  | None →
let _ = Printf.eprintf "None\n%!" in
      let n = r * (i + 3) in
      nA r i n u / pow r (n - i - 1) + 1
  | Some k →
let _ = Printf.eprintf "Some %d\n%!" k in
      let n = r * (i + k + 3) in
      nA r i n u / pow r (n - i - 1)
  end.

value prop_carr r u i =
  let d = u i + nat_prop_carr r u i in
  d mod r.

value freal_series_add x y i = x.freal i + y.freal i.

value freal_add r x y = { freal = prop_carr r (freal_series_add x y) }.

value freal345 =
  {freal i = match i with | 0 → 3 | 1 → 4 | 2 → 5 | _ → 0 end} .
value freal817 =
  {freal i = match i with | 0 → 8 | 1 → 1 | 2 → 7 | _ → 0 end} .

(freal_add 10 freal345 freal817).freal 0;
(freal_add 10 freal345 freal817).freal 1;
(freal_add 10 freal345 freal817).freal 2;
