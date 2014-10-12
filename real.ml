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
let _ = eprintf "a %b b %b c %b t %b c₁ %b\n%!" a b c t c₁ in
      [t :: trunc_add_with_carry c₁ la₁ lb₁]
  | _ → []
  end.

value trunc_add = trunc_add_with_carry False;
