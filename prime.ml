value list_nth_def i l d =
if i < 0 then failwith ("glop" ^ string_of_int i) else
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

value log_prod_tail_rec u v n =
  log_prod_loop 0. where rec log_prod_loop accu i =
    match i with
    | 0 → accu
    | _ →
        let i' = i - 1 in
        let accu = accu +.
	  match (n + 1) mod i with
	  | 0 → u i' *. v ((n + 1) / i - 1)
	  | _ → f_zero
         end
         in
         log_prod_loop accu i'
    end.

value rec log_prod u v n i =
  match i with
  | 0 → f_zero
  | _ →
      let i' = i - 1 in
      match (n + 1) mod i with
      | 0 → u i' *. v ((n + 1) / i - 1)
      | _ → f_zero
      end +. log_prod u v n i'
  end.

value ls_mul s1 s2 =
  { ls n = log_prod_tail_rec s1.ls s2.ls n (n + 1) }.

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

