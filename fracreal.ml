(* test real numbers *)

type digit = { dig : int };
type fracreal = { freal : int → digit };

type sum α β = [ Inl of α | Inr of β ].

value o_LPO u =
  loop 100 0 where rec loop niter i =
    if niter = 0 then Inl ()
    else if u i = 0 then loop (niter - 1) (i + 1)
    else Inr i
;

value digit_sequence_normalize r u i =
  match o_LPO (fun j → r - 1 - (u (i + j + 1)).dig) with
  | Inl _ →
      if (u i).dig + 1 < r then {dig = (u i).dig + 1}
      else {dig = 0}
  | Inr _ → u i
  end
;

(*
digit_sequence_normalize 10 (fun i -> {dig = if i < 3 then 7 else 9}) 0;
- : digit = {dig=7}
digit_sequence_normalize 10 (fun i -> {dig = if i < 3 then 7 else 9}) 1;
- : digit = {dig=7}
digit_sequence_normalize 10 (fun i -> {dig = if i < 3 then 7 else 9}) 2;
- : digit = {dig=8}
digit_sequence_normalize 10 (fun i -> {dig = if i < 3 then 7 else 9}) 3;
- : digit = {dig=0}
digit_sequence_normalize 10 (fun i -> {dig = if i < 3 then 7 else 9}) 4;
- : digit = {dig=0}
*)
