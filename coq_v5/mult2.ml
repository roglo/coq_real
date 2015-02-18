open Printf.

type real01 = { rm : int → int };

value b2n b = b (*if b then 1 else 0*);

value rec summation_loop b len g =
  match len with
  | 0 → 0
  | _ → g b + summation_loop (b + 1) (len - 1) g
  end.

value summation b e g = summation_loop b (e + 1 - b) g;

value base = ref 2;

value rec fst_not_1 z i =
  loop 20 0 where rec loop n di =
    if n = 0 then None
    else if z (i + di) = base.val - 1 then loop (n - 1) (di + 1)
    else Some di
;

value propag_carry_once u i =
  match fst_not_1 u (i + 1) with
  | Some di →
      if u (i + di + 1) < base.val - 1 then
        if u i ≤ base.val - 1 then u i else u i - base.val
      else
        if u i < base.val - 1 then u i + 1 else u i - base.val + 1
  | None →
      if u i < base.val - 1 then u i + 1 else u i - base.val + 1
   end
;
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

value n_iter i =
(*
  loop 0 where rec loop n = if sum_bn1 n - n > i then n else loop (n + 1)
*)i
;

value i_add_algo x y i = x.rm i + y.rm i;

value i_mul_algo x y i =
  summation 1 i (fun j → b2n (x.rm (j - 1)) * b2n (y.rm (i - j)))
;

value i_add_i x y i = i_propag_carry (i_add_algo x y) 1 i;
value i_mul_i x y i = i_propag_carry (i_mul_algo x y) (n_iter i) i;

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

base.val := 2;
list_of_seq (i_propag_carry (i_mul_algo (r_one ()) (r_one ())) 6) 20;
list_of_seq (i_propag_carry (i_mul_algo (r_of_string "10110111") (r_one ())) 6) 20;

base.val := 10;
list_of_seq (i_propag_carry (i_mul_algo (r_of_string "239") (r_of_string "4649")) 0) 20;
list_of_seq (i_propag_carry (i_mul_algo (r_of_string "239") (r_of_string "4649")) 1) 20;
list_of_seq (i_propag_carry (i_mul_algo (r_of_string "239") (r_of_string "4649")) 2) 20;
list_of_seq (i_propag_carry (i_mul_algo (r_of_string "239") (r_of_string "4649")) 3) 20;
list_of_seq (i_propag_carry (i_mul_algo (r_of_string "239") (r_of_string "4649")) 4) 20;
list_of_seq (i_propag_carry (i_mul_algo (r_of_string "239") (r_of_string "4649")) 5) 20;
list_of_seq (i_propag_carry (i_mul_algo (r_of_string "239") (r_of_string "4649")) 6) 20;
list_of_seq (i_propag_carry (i_mul_algo (r_of_string "239") (r_of_string "4649")) 7) 20;
list_of_seq (i_propag_carry (i_mul_algo (r_of_string "239") (r_of_string "4649")) 8) 20;
list_of_seq (i_propag_carry (i_mul_algo (r_of_string "239") (r_of_string "4649")) 9) 20;

list_of_seq (i_mul_i (r_of_string "23") (r_of_string "49")) 20;

list_of_seq (i_mul_i (r_of_string "239") (r_of_string "4649")) 20;
list_of_seq (i_mul_i (r_of_string "10242") (r_of_string "36628")) 20;
(*
# 10242*36628;
- : int = 375143976
list_of_seq (i_mul_i (r_of_string "4649") (r_one ())) 20;
list_of_seq (i_mul_algo (r_of_string "4649") (r_one ())) 20;
*)
