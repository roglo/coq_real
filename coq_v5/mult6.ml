(* definition add in I, another attempt *)

open Printf.

(* summation *)

value add_check_ov a b =
  if a < 0 then
    failwith (sprintf "summation negative arg %d" a)
  else
    let c = a + b in
    if c < 0 then
      failwith (sprintf "summation overflow %d+%d" a b)
    else c
;

value rec summation_loop b len g =
  match len with
  | 0 → 0
  | _ → add_check_ov (g b) (summation_loop (b + 1) (len - 1) g)
  end.

value summation b e g = summation_loop b (e + 1 - b) g;

(* operations in numbers with numbers *)

type digit = { dig : int };

value list_of_seq u =
  list_rec [] where rec list_rec l n =
    if n ≤ 0 then l
    else list_rec [u (n-1) :: l] (n-1)
;

value nn_add u v i = u i + v i;
value nn_mul u v i = summation 1 i (fun j → u (j - 1) * v (i - j));

(* *)

value radix = ref 10;

value d2n d = d.dig mod radix.val;
value n2d n = {dig = n};

type real01 = { rm : int → digit };

value list_of_r x n =
  let l = list_of_seq x.rm n in
  List.map d2n l
;

value r_of_string s =
  {rm i =
     if i ≥ String.length s then {dig = 0}
     else
       let c = Char.code s.[i] - Char.code '0' in
       if c >= radix.val then
         failwith
           (sprintf "r_of_string \"%s\" (digit %d is %c > %d)" s i s.[i]
              (radix.val - 1))
       else {dig = c}}
;

value rec int_pow a b =
  if b < 0 then invalid_arg "int_pow"
  else if b = 0 then 1
  else
    let r = a * int_pow a (b - 1) in
    if a > 0 && r < 0 then failwith (sprintf "int_pow overflow %d %d" a b)
    else r
;

value logn n a =
  loop a a - 1 where rec loop m a =
    match m with
    | 0 → 0
    | _ →
        let m1 = m - 1 in
        if a = 0 then 0
        else 1 + loop m1 (a / n)
    end
;

value max_iter = ref (logn 2 max_int / 2);

value find_nonzero u =
  loop max_iter.val 0 where rec loop m i =
    if m = 0 then None
    else if u i = 0 then loop (m - 1) (i + 1) else Some i
;

value rec first_nonzero_loop (u : int → int) m i =
  if u i = 0 then
    match m with
    | 0 → 0
    | _ → first_nonzero_loop u (m - 1) (i + 1)
    end
  else i.

value first_nonzero u =
  match find_nonzero u with
  | Some i → Some (first_nonzero_loop u i 0)
  | None → None
  end.

(* addition *)

value partial_sum_num u n =
  summation 0 n (fun k → u k * int_pow radix.val (n - k));
value partial_sum_den (u : int → int) n =
  int_pow radix.val n;

value sum_int_part_lb u n i =
  (partial_sum_num u n * int_pow radix.val (i - min i n)) /
  partial_sum_den u (n - min i n);
value sum_int_part_ub u n i m =
  ((partial_sum_num u n + m) * int_pow radix.val (i - min i n)) /
  partial_sum_den u (n - min i n);

hou_la_la_c_est_pas_du_tout_ca.
value seq_same_int_part u i m n =
  let _ = printf "[%d≤%d]%!" (sum_int_part_lb u n i) (sum_int_part_ub u n i m) in
  if sum_int_part_lb u n i = sum_int_part_ub u n i m then 1 else 0;

value i2nn x i = d2n (x.rm i);

value nn2i_add u =
  {rm i =
     match first_nonzero (seq_same_int_part u i 2) with
     | Some n → let _ = printf "<%d>%!" n in n2d (sum_int_part_lb u n i)
     | None → n2d (sum_int_part_lb u 6 i + 1)
     end};
value i_add x y = nn2i_add (nn_add (i2nn x) (i2nn y));

(* test addition *)

(* x + 0 *)

radix.val := 2;
value zero () = {rm _ = n2d 0};
value one () = {rm _ = n2d (radix.val - 1)};
value x = {rm i = n2d (if i < 3 then 0 else radix.val - 1)}.
"0";
list_of_r (zero ()) 10;
"1";
list_of_r (one ()) 10;
"0+1";
list_of_r (i_add (zero ()) (one ())) 10;
"1+0";
list_of_r (i_add (one ()) (zero ())) 10;
"x";
list_of_r x 10;
"x+0";
list_of_r (i_add x (zero ())) 10;
"0+x";
list_of_r (i_add (zero ()) x) 10;

(* *)

value int_of_i x ndec =
  loop 0 0 where rec loop r i =
    if i = ndec then r
    else loop (r * radix.val + d2n (x.rm i)) (i + 1)
;
value d0 = {dig = 0};

value ndec = 7;
radix.val := 10;

value ar () = Array.init ndec (fun i → Random.int (radix.val));
value rx () =
  let a = ar () in
  {rm i = {dig = if i < Array.length a then a.(i) else 0} }.

value x = rx ();
value y = rx ();

list_of_r x ndec;
list_of_r y ndec;
list_of_r (i_add x y) ndec;

(* seems to work... *)

bbb.
