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

value rec count l =
  match l with
  | [] → []
  | [x :: l] →
      match count l with
      | [] → [(1, x)]
      | [(c, y) :: l1] →
          if x = y then [(c+1, y) :: l1]
          else [(1, x); (c, y) :: l1]
      end
  end;

value u (i : int) = i;

#print_length 1001;

(*
example:
list_of_seq (propag_carry_sev_times u 3) 100;
*)

(*
result:
line n:
   (2^n-1-n) "1" / "0" / (2^n-1) "2" / "1" / (2^n-1) "3" / "2" / (2^n-1) "4" /
   "3" / ...

0 1 2 3 4 5 6 7 8 9 10 11 12 13 ...
0 2 1 3 2 4 3 5 4 6  5  7  6  8 ...
1 0 2 2 2 1 3 3 3 2  4  4  4  3 ...
1 1 1 1 0 2 2 2 2 2  2  2  1  3 ...
1 1 1 1 1 1 1 1 1 1  1  0  2  2 ...
remark:
   2^n-n-1 = A(n,1) where A is the eulerian number
*)

(*
example in base 10:
base.val:=10;
value v i = i * 81;
count (list_of_seq (propag_carry_sev_times v 2) 500);
count (list_of_seq (propag_carry_sev_times v 3) 1000);
2:     9x9 8    10x18 17    10x27 26    10x36 35 ... (1x81)
3:   108x9 8   110x18 17   110x27 26   110x36 35 ... (12x81)
4:  1107x9 8  1110x18 17  1110x27 26  1110x36 35 ... (123x81)
5: 11106x9 8 11110x18 17 11110x27 26 11110x36 35 ... (1234x81)
9 = 9*(1)                      = 10^1-1
108=9*(1x10¹+2)                = 10^2+10^1-2
1107=9*(1x10²+2x10¹+3)         = 10^3+10^2+10^1+10^0-4
11106=9*(1x10³+2x10²+3x10³+4)  = 10^4+10^3+10^2+10^1+10^0-5
n: (1x10^(n-2)+2x10^(n-3)+..+(n-1)x10^0)x9x9 8
                               = 10^(n-1)+10^(n-2)+..+10^1+10^0-n
                               = (10^n-1)/(10-1)-n
(b^n-1)/(b-1)-n
si b=2: (2^n-1)/(2-1)-n = 2^n-1-n

line n:
    ((b^n-1)/(b-1)-n)x(b-1) (b-2)
    ((b^n-1)/(b-1))x(2b-2) (2b-3)
    ((b^n-1)/(b-1))x(3b-3) (3b-4)
    ((b^n-1)/(b-1))x(4b-4) (4b-5)
*)
