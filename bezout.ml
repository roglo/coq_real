(*
ocaml $(camlp5 -where)/camlp5r.cma nums.cma
*)

value rec f_nbezout n a b =
  match n with
  | 0 → (False, (0, 0))
  | _ →
      let n' = n - 1 in
      match b with
      | 0 → (False, (1, 0))
      | _ →
          let (q, r) = (a / b, a mod b) in
          let (is_neg, uv) = f_nbezout n' b r in
          let (u, v) = uv in
          (not is_neg, (v, u + q * v))
      end
  end.

value bezout a b = f_nbezout (b + 1) a b.

(*
value rec n_gcd_bezout n a b =
  match n with
  | 0 → failwith "n_gcd_bezout: not enough iter"
  | _ →
      let n = n - 1 in
      match b with
      | 0 → (a, (False, (1, 0)))
      | _ →
          let q = a / b in
	  let r = a mod b in
	  let (g, nuv) = n_gcd_bezout n b r in
	  let (u_is_neg, uv) = nuv in
	  let (u, v) = uv in
	  (g, (not u_is_neg, (v, u + q * v)))
      end
  end.

value gcd_bezout a b =
  n_gcd_bezout (a + b) a b.
*)
