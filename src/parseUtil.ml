open Term
open Con

let rec abs x =
    let rec abs i = function
        | Lam (y, t) ->
            Lam (y, abs (i + 1) t)
        | App (h, s) ->
            App (abs_head i h, List.map (abs i) s)
    and abs_head i = function
        | Var j -> Var j
        | Con (Single y) when x = y -> Var i
        | Con (Family (y, _)) when x = y ->
            failwith "Term.abs: abstracting indexed constants"
        | (Con _ | MVar _) as h -> h
    in abs

