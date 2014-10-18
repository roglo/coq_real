open Printf;

type real_mod_1 = { rm : int → bool };

value fst_same a b i =
  loop 0 where rec loop di =
    if a.rm (i + di) = b.rm (i + di) then Some di
    else if di > 10000 then None
    else loop (di + 1)
;

value xorb a b = if a then not b else b.

value rm_add_i a b i =
  xorb (xorb (a.rm i) (b.rm i))
  (match fst_same a b (i + 1) with
   | Some dj → a.rm (i + dj + 1)
   | None → True
   end).

value rm_add a b = { rm = rm_add_i a b }.

value rm_add_carry a b =
  match fst_same a b 0 with
  | Some dj → a.rm dj
  | None → False
  end.

value rm_opp a = { rm i = not (a.rm i) };
value rm_sub a b = rm_add a (rm_opp b);

value f2a x =
  let x = mod_float x 1.0 in
  loop 100 x [] where rec loop i x list =
    if i = 0 then Array.of_list (List.rev list)
    else
      let x = 2. *. x in
      loop (i - 1) (mod_float x 1.0) [x >= 1. :: list]
;

value f2r x =
  let a = f2a x in
  { rm i = if i < Array.length a then a.(i) else False }
;

value r2f a =
  loop 0 0.0 0.5 where rec loop i x pow =
    if i = 100 then x
    else loop (i + 1) (if a.rm i then x +. pow else x) (pow *. 0.5)
;

r2f (rm_add (f2r 0.28) (f2r 0.17));

value rec trunc n a =
  if n = 0 then []
  else [a.rm (n-1) :: trunc (n-1) a]
;

value carry_sum_3 a b c = a && b || b && c || c && a;

value rec trunc_add_with_carry c la lb =
  match (la, lb) with
  | ([a :: la₁], [b :: lb₁]) →
      let t = xorb (xorb a b) c in
      let c₁ = carry_sum_3 a b c in
      [t :: trunc_add_with_carry c₁ la₁ lb₁]
  | _ → []
  end.

value trunc_add = trunc_add_with_carry False;

value t2s la =
  "0." ^ List.fold_left (fun s a → if a then "1" ^ s else "0" ^ s) "" la
;

value t2f la =
  List.fold_left (fun s a → (if a then 1. else 0.) +. s /. 2.) 0. la /. 2.
;

(**)

value tr_add n a b =
  let c =
    match fst_same a b n with
    | Some dn → a.rm (n + dn)
    | None → True
    end
  in
  trunc_add_with_carry c (trunc n a) (trunc n b)
;

value tr_add2 n a b = trunc_add_with_carry False (trunc n a) (trunc n b);

value n = 9;
n;
t2f (tr_add n (f2r 0.5) (f2r 0.2));
t2f (trunc n (rm_add (f2r 0.5) (f2r 0.2)));
(tr_add n (f2r 0.5) (f2r 0.2));
(trunc n (rm_add (f2r 0.5) (f2r 0.2)));
t2s (tr_add n (f2r 0.5) (f2r 0.2));
t2s (trunc n (rm_add (f2r 0.5) (f2r 0.2)));

(**)
t2f (tr_add 35 (f2r 0.5) (f2r 0.2));
t2f (tr_add 36 (f2r 0.5) (f2r 0.2));
t2f (tr_add 37 (f2r 0.5) (f2r 0.2));
t2f (tr_add 38 (f2r 0.5) (f2r 0.2));
t2f (tr_add 39 (f2r 0.5) (f2r 0.2));
t2f (tr_add 40 (f2r 0.5) (f2r 0.2));
t2f (tr_add 41 (f2r 0.5) (f2r 0.2));
t2f (tr_add 42 (f2r 0.5) (f2r 0.2));
(**)

(**)
5;

t2f (tr_add 0 (f2r 0.5) (f2r 0.2));
t2f (tr_add 1 (f2r 0.5) (f2r 0.2));
t2f (tr_add 2 (f2r 0.5) (f2r 0.2));
t2f (tr_add 3 (f2r 0.5) (f2r 0.2));
t2f (tr_add 4 (f2r 0.5) (f2r 0.2));
t2f (tr_add 5 (f2r 0.5) (f2r 0.2));
t2f (tr_add 6 (f2r 0.5) (f2r 0.2));
t2f (tr_add 7 (f2r 0.5) (f2r 0.2));
t2f (tr_add 8 (f2r 0.5) (f2r 0.2));
t2f (tr_add 9 (f2r 0.5) (f2r 0.2));
t2f (tr_add 10 (f2r 0.5) (f2r 0.2));
t2f (tr_add 11 (f2r 0.5) (f2r 0.2));

5;

t2f (trunc 0 (rm_add (f2r 0.5) (f2r 0.2)));
t2f (trunc 1 (rm_add (f2r 0.5) (f2r 0.2)));
t2f (trunc 2 (rm_add (f2r 0.5) (f2r 0.2)));
t2f (trunc 3 (rm_add (f2r 0.5) (f2r 0.2)));
t2f (trunc 4 (rm_add (f2r 0.5) (f2r 0.2)));
t2f (trunc 5 (rm_add (f2r 0.5) (f2r 0.2)));
t2f (trunc 6 (rm_add (f2r 0.5) (f2r 0.2)));
t2f (trunc 7 (rm_add (f2r 0.5) (f2r 0.2)));
t2f (trunc 8 (rm_add (f2r 0.5) (f2r 0.2)));
t2f (trunc 9 (rm_add (f2r 0.5) (f2r 0.2)));
t2f (trunc 10 (rm_add (f2r 0.5) (f2r 0.2)));
t2f (trunc 11 (rm_add (f2r 0.5) (f2r 0.2)));
(**)

value rec trunc_from n a i =
  match n with
  | 0 → []
  | _ →
      let n₁ = n - 1 in
      [a.rm (i+n₁) :: trunc_from n₁ a i]
  end.

value rm_exp_opp n = {rm i = i = n}.
value trunc_one n = trunc_from n (rm_exp_opp (pred n)) 0;
