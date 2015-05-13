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

value i2nn x i = d2n (x.rm i);

value glop u m i =
  let x = i + logn radix.val m + 1 in
  fun n →
    if n < x then 0
    else
      let xn = summation 0 n (fun k → u k * int_pow radix.val (n - k)) in
      let rni = int_pow radix.val (n - i) in
      if xn mod rni + m < rni then 1 else 0;

(* could help proof of associativity, taking 3 instead of 2 *)
value number_of_numbers_added = 2;

value nn2i_add u =
  let m = number_of_numbers_added in
  {rm i =
(**)
     match first_nonzero (glop u m i) with
     | Some n →
         let xn = summation 0 n (fun k → u k * int_pow radix.val (n - k)) in
         let rni = int_pow radix.val (n - i) in
         n2d (xn / rni)
     | None →
         n2d 0 (* quelle valeur lui mettre ? *)
     end
(*
     loop 0 (i + logn radix.val m + 1) where rec loop niter n =
       let xn = summation 0 n (fun k → u k * int_pow radix.val (n - k)) in
       let rni = int_pow radix.val (n - i) in
       if niter > 10 then n2d (xn / rni + 1)
       else if xn mod rni + m < rni then n2d (xn / rni)
       else loop (niter + 1) (n + 1)
*)
   };
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
  let e = Random.int radix.val in
  {rm i = {dig = if i < Array.length a then a.(i) else e} }.

value x = rx ();
value y = rx ();

list_of_r x (ndec + 4);
list_of_r y (ndec + 4);
list_of_r (i_add x y) ndec;
