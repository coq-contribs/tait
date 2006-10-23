open Betaetaexp_nc

let rec i2n = function 0 -> O | n -> S (i2n (pred n))

let rec decode_church = function 
  | Abs (_,t) -> decode_church t
  | App (_,t) -> 1+decode_church t
  | Var _ -> 0

let main = 
  let n = i2n (int_of_string Sys.argv.(1)) 
  and m = i2n (int_of_string Sys.argv.(2))
  in Printf.printf "%d\n" (decode_church (church_power'_nc n m))
