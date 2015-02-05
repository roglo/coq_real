type real01 = { rm : int → int };

value b2n b = b (*if b then 1 else 0*);

value rec summation_loop b len g =
  match len with
  | 0 → 0
  | _ → g b + summation_loop (b + 1) (len - 1) g
  end.

value summation b e g = summation_loop b (e + 1 - b) g;

value base = ref 2;
value propag_carry_once u i = u i mod base.val + u (i + 1) / base.val;
value rec i_propag_carry u n =
  match n with
  | 0 → u
  | _ → propag_carry_once (i_propag_carry u (n-1))
  end
;

(* (base^n-1)/(base-1) *)
value sum_bn1 n =
  loop 0 1 0 where rec loop sum b_pow_i i =
    if i = n then sum
    else loop (sum + b_pow_i) (b_pow_i * base.val) (i + 1)
;

value i_mul_algo x y i =
  summation 1 i (fun j → b2n (x.rm (j - 1)) * b2n (y.rm (i - j)))
;

value i_mul_i x y i =
  let u = i_mul_algo x y in
  let n =
    loop 0 where rec loop n = if sum_bn1 n - n > i then n else loop (n + 1)
  in
  i_propag_carry u n i
;

value list_of_seq u =
  list_rec [] where rec list_rec l n =
    if n ≤ 0 then l
    else list_rec [u (n-1) :: l] (n-1)
;

value r_one () = {rm _ = base.val - 1};

value r_of_string s =
  {rm i =
     if i ≥ String.length s then 0
     else Char.code s.[i] - Char.code '0'}
;

base.val := 10;
list_of_seq (i_mul_i (r_of_string "239") (r_of_string "4649")) 20;
list_of_seq (i_mul_i (r_of_string "10242") (r_of_string "36628")) 20;
(*
# 10242*36628;
- : int = 375143976
list_of_seq (i_mul_i (r_of_string "4649") (r_one ())) 20;
list_of_seq (i_mul_algo (r_of_string "4649") (r_one ())) 20;
*)
