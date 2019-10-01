(*
      6-----7
     /|    /|
    2-----3 |
    | |   | |
    | 4---|-5
    |/    |/
    0-----1

  a worm is moving from 0 to 7; each step is a move from a vertex
  to a neighbour one along an edge; randomly moving, in which average
  number of steps the worm, starting at 0, reaches 7?
    This program emulates a big number of attempts; the result seems
  to converge to 10.
    Numbered the cube from 0 to 7 by taking binary version of coordinates
  in 3 dimensions: 0 for (0,0,0), 1 for (0,0,1), ... 6 for (1,1,0) etc.
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

value path dim a end_state =
  loop where rec loop n state =
    if state = end_state then n
    else
      let x = List.nth (List.nth a (Random.int dim)) state in
      let _ = assert (fst x = state) in
      loop (n + 1) (snd x)
;

value sum dim a beg_state end_state =
  loop where rec loop r n =
    if n = 0 then r
    else loop (path dim a end_state r beg_state) (n - 1)
;

value test dim n =
  let a = make_a dim in
  let beg_state = 0 in
  let end_state = pow 2 dim - 1 in
  float (sum dim a beg_state end_state 0 n) /. float n;

Random.self_init ();
(*
Printf.eprintf "%g\n%!" (test 6 10000000);
*)
