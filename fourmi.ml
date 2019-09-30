(*
      2-----4
     /|    /|
    0-----1 |
    | |   | |
    | 6---|-7
    |/    |/
    3-----5

  a worm is moving from 0 to 7; each step is a move from a vertex
  to a neighbour one along an edge; randomly moving, in which average
  number of steps the worm, starting at 0, reaches 7?
    This program emulates a big number of attempts; the result seems
  to converge to 10.
    Numbered the cube from 0 to 7 such that sum of opposite vertices
  is equal to 7.

    Another way to number the cube is to ensure that the sum of the
  four vertices of each face is 14. In this example, opposite vertices
  have another special property; they are: (0, 1), (2, 3), (4, 5) and
  (6, 7). And some diagonal slice rectangles have 14 as sum too: the
  5342 and 0617. But the other four have not.
      5-----6
     /|    /|
    0-----3 |
    | |   | |
    | 2---|-1
    |/    |/
    7-----4
    Is it possible to number the cube by an algorithm that could work
  for any dimension? I would like to move my worm in an hypercube.
*)

value decomp =
  loop [] where rec loop r d n =
    if d = 0 then r else loop [n mod 2 :: r] (d - 1) (n / 2)
;

value rec neighb r dim m =
  match m with
  | [x :: l] → neighb [if dim = 0 then 1-x else x :: r] (dim - 1) l
  | [] → r
  end.

value rec recomp l =
  match l with
  | [x :: l] → 2 * recomp l + x
  | [] → 0
  end.

value make_neighb dim n =
  let m = decomp dim n in
  loop dim where rec loop d =
    if d = 0 then []
    else [recomp (neighb [] (d - 1) m) :: loop (d - 1)]
;

value rec pow a b =
  if b = 0 then 1
  else a * pow a (b - 1)
;

value make_all dim =
  loop [] (pow 2 dim) where rec loop r n =
    if n = 0 then r
    else loop [(n - 1, make_neighb dim (n - 1)) :: r] (n - 1)
;

value make_a dim =
  let a = make_all dim in
  loop [] dim where rec loop r i =
    if i = 0 then r
    else
      loop [List.map (fun (n, l) → (n, List.nth l (i - 1))) a :: r] (i - 1)
;

(*
value a =
  [[(0, 1); (1, 0); (2, 0); (3, 0); (4, 1); (5, 1); (6, 2); (7, 4)];
   [(0, 2); (1, 4); (2, 4); (3, 5); (4, 2); (5, 3); (6, 3); (7, 5)];
   [(0, 3); (1, 5); (2, 6); (3, 6); (4, 7); (5, 7); (6, 7); (7, 6)]]
;
value beg_state = 0;
value end_state = 7;
value a =
  [[(0, 3); (1, 2); (2, 1); (3, 0); (4, 7); (5, 6); (6, 5); (7, 4)];
   [(0, 5); (1, 4); (2, 7); (3, 6); (4, 1); (5, 0); (6, 3); (7, 2)];
   [(0, 7); (1, 6); (2, 5); (3, 4); (4, 3); (5, 2); (6, 1); (7, 0)]]
;
value beg_state = 0;
value end_state = 1;
*)

(*
value dim = 4;
value beg_state = 0;
value end_state = pow 2 dim - 1;
value a = make_a dim;
*)

value rec path dim a end_state n state =
  if state = end_state then n
  else
    path dim a end_state (n + 1)
      (snd (List.nth (List.nth a (Random.int dim)) state))
;

value rec sum dim a beg_state end_state r n =
  if n = 0 then r
  else
    sum dim a beg_state end_state
      (r + path dim a end_state 0 beg_state) (n - 1)
;

value test dim n =
  let a = make_a dim in
  let beg_state = 0 in
  let end_state = pow 2 dim - 1 in
  float (sum dim a beg_state end_state 0 n) /. float n;

Random.self_init ();
Printf.eprintf "%g\n%!" (test 6 10000000);
