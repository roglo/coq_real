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
  (6, 7):
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

(*
value a =
  [[(0, 1); (1, 0); (2, 0); (3, 0); (4, 1); (5, 1); (6, 2); (7, 4)];
   [(0, 2); (1, 4); (2, 4); (3, 5); (4, 2); (5, 3); (6, 3); (7, 5)];
   [(0, 3); (1, 5); (2, 6); (3, 6); (4, 7); (5, 7); (6, 7); (7, 6)]]
;
value beg_state = 0;
value end_state = 7;
*)
value a =
  [[(0, 7); (1, 6); (2, 5); (3, 4); (4, 3); (5, 2); (6, 1); (7, 0)];
   [(0, 3); (1, 2); (2, 1); (3, 0); (4, 7); (5, 6); (6, 5); (7, 4)];
   [(0, 5); (1, 4); (2, 7); (3, 6); (4, 1); (5, 0); (6, 3); (7, 2)]]
;
value beg_state = 0;
value end_state = 1;
(**)

value rec path n state =
  if state = end_state then n
  else path (n + 1) (snd (List.nth (List.nth a (Random.int 3)) state))
;

value rec test r n =
  if n = 0 then r
  else test (r + path 0 beg_state) (n - 1)
;

let n = 1000000 in float (test 0 n) /. float n;
