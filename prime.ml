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

value rec conv_prod u v i j =
  match j with
  | 0 → 0.
  | _ → let j' = pred j in u i *. v j' +. conv_prod u v (i + 1) j'
  end.

value ls_mul s1 s2 =
  { ls n = conv_prod s1.ls s2.ls 0 (n + 1) }.

value ls_of_pol p =
  { ls n = list_nth_def n p.lp 0. }.

value ls_pol_mul_l p s =
  ls_mul (ls_of_pol p) s.

value zeta_but_mul_of d =
  { ls n =
      match (n + 1) mod d with
      | 0 → 0.
      | _ → 1.
      end }.

value f1 = zeta_but_mul_of 2;
value f2 = ls_pol_mul_l { lp = [f_one; -. f_one] } zeta;

