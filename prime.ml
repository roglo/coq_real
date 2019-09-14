value list_nth_def i l d =
  match List.nth_opt l i with
  | Some v → v
  | None → d
  end.

type ln_series =
  { ls : int → float }.

type ln_polyn =
  { lp : list float }.

value f_zero = 0.;
value f_one = 1.;

value zeta = { ls _ = f_one }.

value rec log_prod u v n i =
  match i with
  | 0 → f_zero
  | _ →
      let i' = i - 1 in
      match (n + 1) mod i with
      | 0 → u i *. u (n + 1 - i)
      | _ → f_zero
      end +. log_prod u v n i'
  end.

value ls_mul s1 s2 =
  { ls n = log_prod s1.ls s2.ls n (n + 1) }.

value ls_of_pol p =
  { ls n = list_nth_def n p.lp f_zero }.

value ls_pol_mul_l p s =
  ls_mul (ls_of_pol p) s.

value zeta_but_mul_of d =
  { ls n =
      match (n + 1) mod d with
      | 0 → f_zero
      | _ → f_one
      end }.

value f1 = zeta_but_mul_of 2;
value f2 = ls_pol_mul_l { lp = [f_one; -. f_one] } zeta;

