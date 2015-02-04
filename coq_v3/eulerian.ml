(* We are searching how carries propagate in a multiplication of real
   numbers of [0..1], represented by infinite sequences of binary digits.

   We take the worst case: product of 0.11111... by itself, normally
   returning 0.11111... (it is actually 1x1=1 since 0.11111...=1)

   The first step of the multiplication is by doing the ending sum
   without propagating the carries:
         0.1 1 1 1 1 1 ...
       x 0.1 1 1 1 1 1 ...
       -------------
       1 1 1 1 1 1 1 1 1 ...
         1 1 1 1 1 1 1 1 1 ...
           1 1 1 1 1 1 1 1 1 ...
             1 1 1 1 1 1 1 1 1 ...
               1 1 1 1 1 1 1 1 1 ...
                 ...
       -----------------------------
   0. 0 1 2 3 4 5 6 7 8 9 ...

   The result is therefore the sequence (u_n) such that u_i = i

   Then we propagate the carry step by step.

   At each step, we cut the numbers by:
     - its quotient by 2 (carry for the number of the left)
     - its remainder modulo 2

   We add this remainder and the quotient of the number of the right.

   We remove the leftmost number (normally a 0):

     a0        a1        a2        a3        a4        ...
     a0/2,a0%2 a1/2,a1%2 a2/2,a2%2 a3/2,a3%2 a3/2,a3%2 ...
     a0%2+a1/2 a1%2+a2/2 a2%2+a3/2 a3%2+a3/2 a3%2+a4/2 ...

   Here:
     0   1   2   3   4   5   6   7   8   9   ...
     0/0 0/1 1/0 1/1 2/0 2/1 3/0 3/1 4/0 4/1 ...
       0   2   1   3   2   4   3   5   4     ...

   When restarting this operation, the sequence converges to:
      1 1 1 1 1 1 1 1 ...

   This toplevel program computes the steps.
*)

value base = ref 2;

value propag_carry u i = u i mod base.val + u (i + 1) / base.val;
value rec propag_carry_sev_times u n =
  if n ≤ 0 then u
  else propag_carry_sev_times (propag_carry u) (n-1)
;

value list_of_seq u =
  list_rec [] where rec list_rec l n =
    if n ≤ 0 then l
    else list_rec [u (n-1) :: l] (n-1)
;

value u (i : int) = i;

#print_length 1001;

(*
example:
list_of_seq (propag_carry_sev_times u 3) 100;
*)

(*
result:
line n:
   (2^n-n-1) "1" / "0" / (2^n-1) "2" / "1" / (2^n-1) "3" / "2" / (2^n-1) "4" /
   "3" / ...

0 1 2 3 4 5 6 7 8 9 10 11 12 13 ...
0 2 1 3 2 4 3 5 4 6  5  7  6  8 ...
1 0 2 2 2 1 3 3 3 2  4  4  4  3 ...
1 1 1 1 0 2 2 2 2 2  2  2  1  3 ...
1 1 1 1 1 1 1 1 1 1  1  0  2  2 ...
remark:
   2^n-n-1 = A(n,1) where A is the eulerian number
*)
