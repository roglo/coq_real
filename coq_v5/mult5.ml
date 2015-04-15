(* nth try to define multiplication in I = [0..1[ in ℝ *)

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

value max_iter = ref (logn 2 max_int - 4);

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

value seq_pred_r_to_0 (u : int → int) i k =
  if u (i + k) = radix.val - 1 then 0 else 1;

value fst_not_pred_r u i = first_nonzero (seq_pred_r_to_0 u i).

value carry_add u i =
  match fst_not_pred_r u (i + 1) with
  | Some n → if u (i + n + 1) < radix.val then 0 else 1
  | None → 1
  end.

value i2nn x i = d2n (x.rm i);

value nn2i_add u = {rm i = n2d (u i + carry_add u i)}.
value i_add2 x y = nn2i_add (nn_add (i2nn x) (i2nn y));

(* multiplication *)

value rec nb_iter_mul u i =
  let r = radix.val in
  loop max_iter.val 0 where rec loop m n =
    if m = 0 then None
    else
      let nt = summation 1 n (fun k → u (i + k) * int_pow r (n - k)) in
      let dt = int_pow r n in
      let ub_sum_frac =
        let ft = nt - (nt / dt) * dt in
        ft + (i + n + 1) * (r - 1) + 1
      in
      if ub_sum_frac ≥ dt then loop (m - 1) (n + 1)
      else Some n
;

value carry_mul u i =
  let r = radix.val in
  match nb_iter_mul u i with
  | Some n →
      let nt = summation 1 n (fun k → u (i + k) * int_pow r (n - k)) in
      let dt = int_pow r n in
      nt / dt
  | None →
      (* the following value of n ensures that the integer part of the
         error is 0 *)
      let n = logn r (i * (r - 1) + r) + 2 in
      let nt = summation 1 n (fun k → u (i + k) * int_pow r (n - k)) in
      let dt = int_pow r n in
let ft = nt - nt / dt * dt in
let fe = (i + n + 1) * (r - 1) + 1 in
let _ = printf "i %d et %d/%d ef %d/%d\n%!" i nt dt (ft + fe) dt in
      nt / dt + 1
  end.

value nn2i_mul u = {rm i = n2d (u i + carry_mul u i)}.
value i_mul x y = nn2i_mul (nn_mul (i2nn x) (i2nn y));

(* test multiplication *)

(* one times one *)

radix.val := 2;
value one () = {rm _ = n2d (radix.val - 1)};
"1*1";
list_of_seq (nn_mul (i2nn (one ())) (i2nn (one ()))) 15;
list_of_r (i_mul (one ()) (one ())) 50;

"1*101110";
list_of_seq (nn_mul (i2nn (one ())) (i2nn (r_of_string "101110"))) 15;
list_of_r (i_mul (one ()) (r_of_string "101110")) 15;

"101110*1";
list_of_seq (nn_mul (i2nn (r_of_string "101110")) (i2nn (one ()))) 15;
list_of_r (i_mul (r_of_string "101110") (one ())) 15;

bbb;

(* *)

value int_of_i x ndec =
  loop 0 0 where rec loop r i =
    if i = ndec then r
    else loop (r * radix.val + d2n (x.rm i)) (i + 1)
;
value d0 = {dig = 0};

(* checking; infinite lines of "." → ok *)

radix.val := 7;
value ndec = 20;

value (n_iter, x, y, axy, xy) =
  loop 0 where rec loop n =
let _ = if n mod 10 = 0 then printf ".%!" else () in
    let rn () = Array.init ndec (fun i → {dig = Random.int radix.val}) in
    let x =
      let a = rn () in {rm i = if i < Array.length a then a.(i) else d0}
    in
    let y =
      let a = rn () in {rm i = if i < Array.length a then a.(i) else d0}
    in
    let axy = int_of_i (i_mul x y) (2 * ndec) in
    let xy = int_of_i x ndec * int_of_i y ndec in
    if axy = xy then loop (n + 1)
    else (n, x, y, axy, xy)
;

value big_nn2i_mul u =
  let r = radix.val in
  {rm i =
     let n = logn r (i * (r - 1) + r) + 5 in
     let s = summation 0 n (fun k → u (i + k) * int_pow r (n - k)) in
     n2d ((s / int_pow r n) mod r)}
;

"x, y, z";
list_of_r x ndec;
list_of_r y ndec;
"x * y = nn";
let u = nn_mul (i2nn x) (i2nn y) in
list_of_seq u (3 * ndec);
"x * y (big)";
let u = nn_mul (i2nn x) (i2nn y) in
list_of_r (big_nn2i_mul u) (3 * ndec);
"x * y";
list_of_r (i_mul x y) (3 * ndec);
axy;
let _ = Printf.printf "%d*%d;\n%!" (int_of_i x ndec) (int_of_i y ndec) in
xy;

radix.val := 10;
value ndec = 40;

239*4649;
list_of_seq (nn_mul (i2nn (r_of_string "239")) (i2nn (r_of_string "4649")))
 ndec;
list_of_r (i_mul (r_of_string "239") (r_of_string "4649")) ndec;

(* addition était carrément fausse ! n=2 était insuffisant ;
   voyons ce que ça donne maintenant... *)

(*
radix.val := 2;
value x = r_of_string "011";
value y = r_of_string "001";
"x, y";
list_of_r x 7;
list_of_r y 7;
"f x + f y";
list_of_seq (nn_add (i2nn x) (i2nn y)) 7;
"x + y";
list_of_r (i_add2 x y) 7;
*)

(* est-ce que cette addition est associative ? *)

(*
radix.val := 2;
value x = r_of_string "010";
value y = r_of_string "001";
value z = r_of_string "001";
"x, y, z";
value ndec = 15;
list_of_r x ndec;
list_of_r y ndec;
list_of_r z ndec;
"(y + z), (x + y)";
list_of_r (i_add2 y z) ndec;
list_of_r (i_add2 x y) ndec;
"x + (y + z)";
"(x + y) + z";
list_of_r (i_add2 x (i_add2 y z)) ndec;
list_of_r (i_add2 (i_add2 x y) z) ndec;
*)

(* addition *)

radix.val := 10;
value d0 = {dig = 0};
value rn () =
  Array.init 10 (fun i → {dig = if i = 0 then 0 else Random.int radix.val})
;
value x = let a = rn () in {rm i = if i < Array.length a then a.(i) else d0};
value y = let a = rn () in {rm i = if i < Array.length a then a.(i) else d0};
value z = let a = rn () in {rm i = if i < Array.length a then a.(i) else d0};
"x, y, z";
value ndec = 15;
list_of_r x ndec;
list_of_r y ndec;
list_of_r z ndec;
"x + (y + z)";
"(x + y) + z";
list_of_r (i_add2 x (i_add2 y z)) ndec;
list_of_r (i_add2 (i_add2 x y) z) ndec;

(*
- : string = "x, y, z"
- : list int = [0; 0; 1; 1; 0; 0; 0]
- : list int = [0; 1; 0; 1; 0; 0; 0]
- : list int = [0; 1; 0; 0; 0; 0; 0]
- : string = "x + (y + z)"
- : string = "(x + y) + z"
- : list int = [1; 1; 0; 0; 0; 0; 0]
- : list int = [0; 1; 0; 0; 0; 0; 0]

x = 0,0011 = 1/8+1/16 = 3/16
y = 0,0101 = 1/4+1/16 = 5/16
z = 0,0100 = 1/4

en vrai x+y+z=(3+5+4)/16=12/16=3/4

x+(y+z) = 0,11 = 1/2+1/4=3/4 ok!
(x+y)+z = 0,01 = 1/4 faux
*)

(*
value x = r_of_string "0011";
value y = r_of_string "0101";
value z = r_of_string "0100";
"x, y, z";
list_of_r x 7;
list_of_r y 7;
list_of_r z 7;
"x + (y + z)";
"(x + y) + z";
list_of_r (i_add2 x (i_add2 y z)) 7;
list_of_r (i_add2 (i_add2 x y) z) 7;

list_of_r (i_add2 x y) 7;
*)

radix.val := 10;

239*4649;
list_of_r (i_mul (r_of_string "239") (r_of_string "4649")) 10;
4821*107;
list_of_r (i_mul (r_of_string "4821") (r_of_string "107")) 10;
9344*685;
list_of_r (i_mul (r_of_string "9344") (r_of_string "685")) 10;
9725*483;
list_of_r (i_mul (r_of_string "9725") (r_of_string "483")) 10;
4656*7532;
list_of_r (i_mul (r_of_string "4656") (r_of_string "7532")) 10;
(* for 64 bits *)
9468025*7023342;
list_of_r (i_mul (r_of_string "9468025") (r_of_string "7023342")) 20;

value one = r_of_string "1";

39872*1;
list_of_r (i_mul (r_of_string "39872") one) 20;
3*1;
list_of_r (i_mul (r_of_string "3") one) 20;

(*
# 9344*685;
- : int = 6400640

           9  3  4  4
           x  6  8  5
      ---------------
          45 15 20 20
       72 24 32 32
    54 18 24 24
    -----------------
  0 54 90 93 71 52 20

# (0+(((((54*10+90)*10+93)*10+71)*10+52)*10+20)/1000000) mod 10;
- : int = 6
# (54+((((90*10+93)*10+71)*10+52)*10+20)/100000) mod 10;
- : int = 4
# (90+(((93*10+71)*10+52)*10+20)/10000) mod 10;
- : int = 0
# (93+((71*10+52)*10+20)/1000) mod 10;
- : int = 0
# (71+(52*10+20)/100) mod 10;
- : int = 6
# (52+20/10) mod 10;
- : int = 4
# (20/1) mod 10;
- : int = 0
*)
