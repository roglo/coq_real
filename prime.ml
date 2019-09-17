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

value ζ = { ls _ = f_one }.

(* à revoir avec log_prod ci-dessous *)
value log_prod_tail_rec u v n =
  log_prod_loop 0. where rec log_prod_loop accu i =
    match i with
    | 0 → accu
    | _ →
	let j = n + 2 - i in
	let q = (n + 1) / j in
	if q < j then accu
	else
          let accu =
	    match (n + 1) mod j with
	    | 0 →
		if q = j then accu +. u (j - 1) *. v (j - 1)
		else accu +. u (j - 1) *. v (q - 1) +. u (q - 1) *. v (j - 1)
	    | _ → accu
            end
          in
          log_prod_loop accu (i - 1)
    end.

value rec log_prod u v n i =
  match i with
  | 0 → f_zero
  | _ →
      let j = n + 1 - i in
      let q = (n + 1) / (j + 1) - 1 in
      if q < j then f_zero
      else
        match (n + 1) mod (j + 1) with
        | 0 →
	    if q = j then u j *. v j
	    else u j *. v q +. u q *. v j
        | _ → f_zero
        end +. log_prod u v n (i - 1)
  end.

(* Σ (i = 1, ∞) s1_(i-1) x^ln(i) + Σ (i = 1, ∞) s2_(i-1) x^ln(i) *)
value ls_add s1 s2 =
  { ls n = s1.ls n +. s2.ls n }.

(* Σ (i = 1, ∞) s1_(i-1) x^ln(i) * Σ (i = 1, ∞) s2_(i-1) x^ln(i) *)
value ls_mul s1 s2 =
  { ls n = log_prod(*_tail_rec*) s1.ls s2.ls n (n + 1) }.

(* Σ (i = 1, ∞) s1_i x^ln(i) * Σ (i = 1, ∞) s2_i x^ln(i) *)
value ls_mul s1 s2 =
  { ls n = log_prod(*_tail_rec*) s1.ls s2.ls n (n + 1) }.

(* c*x^ln(n+1) * Σ (i = 1, ∞) s_(i-1) x^ln(i) =
   Σ (i = 1, ∞) c*s_(i-1) x^ln((n+1)*i) *)
value ls_mul_elem c n s =
  { ls i =
      match (i + 1) mod (n + 1) with
      | 0 -> c *. s.ls i
      | _ -> f_zero
      end }.

(* multiplication of a series by the first k elements of another series
   (i.e. a polynomial formed by its first k elements)
    Σ (i = 1, k) s1_(i-1) x^ln(i) * Σ (i = 1, ∞) s2_(i-1) x^ln(i) *)
value rec ls_mul_l_upto k s1 s2 =
  match k with
  | 0 -> { ls _ = f_zero }
  | _ ->
      ls_add (ls_mul_l_upto (k - 1) s1 s2)
        (ls_mul_elem (s2.ls (k - 1)) (k - 1) s1)
  end.

value ls_of_pol p =
  { ls n = list_nth_def n p.lp f_zero }.

value ls_pol_mul_l p s =
  ls_mul (ls_of_pol p) s.

(*
let p = {lp=[1.;-1.]} in (ls_pol_mul_l p ζ).ls 1;
let p = {lp=[1.;-1.]} in (ls_mul_l_upto (List.length p.lp) (ls_of_pol p) ζ).ls 1;
*)

value ζ_but_mul_of d =
  { ls n =
      match (n + 1) mod d with
      | 0 → f_zero
      | _ → f_one
      end }.

value f1 = ζ_but_mul_of 2;
value f2 = ls_pol_mul_l { lp = [f_one; -. f_one] } ζ;
