value propag_carry u i = u i mod 2 + u (i + 1) / 2;
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
