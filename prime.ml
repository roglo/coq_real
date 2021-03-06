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

value ε n i =
  match n mod i with
  | 0 → f_one
  | _ → f_zero
  end.

value log_prod_term u v n i =
  u i *. v (n / i) *. ε n i.

value rec log_prod_list cnt u v n i =
  match cnt with
  | 0 → []
  | _ → [log_prod_term u v n i :: log_prod_list (cnt - 1) u v n (i + 1)]
  end.

value log_prod u v n =
  List.fold_right \+. (log_prod_list n u v n 1) f_zero.

(*
value log_prod_term' u v n i =
  let q = n / i in
  if q < i then f_zero
  else
    match n mod i with
    | 0 →
        if q = i then u i *. v i
        else u i *. v q +. u q *. v i
    | _ → f_zero
    end.

value rec log_prod' u v n i =
   match i with
   | 0 → f_zero
   | _ → log_prod_term' u v n (n - (i - 1)) +. log_prod' u v n (i - 1)
   end.
*)

(* Σ (i = 1, ∞) s1_i x^ln(i) + Σ (i = 1, ∞) s2_i x^ln(i) *)
value ls_add s1 s2 =
  { ls n = s1.ls n +. s2.ls n }.

(* Σ (i = 1, ∞) s1_i x^ln(i) * Σ (i = 1, ∞) s2_i x^ln(i) *)
value ls_mul s1 s2 =
  { ls = log_prod s1.ls s2.ls }.

(* c*x^ln(n) * Σ (i = 1, ∞) s_(i-1) x^ln(i) =
   Σ (i = 1, ∞) c*s_(i-1) x^ln(n*i) *)
value ls_mul_elem c n s =
  { ls i =
      if i = 0 then f_zero
      else
        match i mod n with
        | 0 → c *. s.ls (i / n)
        | _ → f_zero
        end }.

(* multiplication of a series by the first k elements of another series
   (i.e. a polynomial formed by its first k elements)
    Σ (i = 1, k) s1_(i-1) x^ln(i) * Σ (i = 1, ∞) s2_(i-1) x^ln(i) *)
value rec ls_mul_l_upto k s1 s2 =
  match k with
  | 0 -> { ls _ = f_zero }
  | _ ->
      ls_add (ls_mul_l_upto (k - 1) s1 s2)
        (ls_mul_elem (s1.ls k) k s2)
  end.

value ls_of_pol p =
  { ls n =
      match n with
      | 0 → f_zero
      | _ → list_nth_def (n - 1) p.lp f_zero
      end }.

value ls_pol_mul_l p s =
  ls_mul (ls_of_pol p) s.

value rec list_repeat x n =
  match n with
  | 0 → []
  | _ → [x :: list_repeat x (n - 1)]
  end.

value pol_pow n =
  { lp = list_repeat f_zero (n - 1) @ [f_one] }.

value ζ_but_mul_of d =
  { ls n =
      if n = 0 then f_zero
      else
        match n mod d with
        | 0 → f_zero
        | _ → f_one
        end }.

value f1 = ζ_but_mul_of 2;
value f2 = ls_pol_mul_l { lp = [f_one; -. f_one] } ζ;
let n = 7 in (f1.ls n, f2.ls n);

(*
let p = {lp=[1.]} in (ls_pol_mul_l p ζ).ls 1;
let p = {lp=[1.;-1.]} in (ls_pol_mul_l p ζ).ls 1;
value p = {lp=[3.; -4.; 2.]}.
value s = {ls i = float i+.4.}.
value e1 = (ls_pol_mul_l p s).ls;
value e2 = (ls_mul_l_upto (List.length p.lp) (ls_of_pol p) s).ls;
let n = 1 in (e1 n, e2 n);
*)
