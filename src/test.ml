open Hol

let _ =
    init

    |> add_type "bool"
    |> add_con "tt" "bool"
    |> add_con "ff" "bool"
    |> prove "test" "true or false"
        |> status
        |> or_right_0
        |> status
        |> true_right
        |> qed

    |> prove "there exists a natural number"
            "ex n:nat. true"
        |> status
        |> ex_right "zero"
        |> status
        |> true_right
        |> qed

    |> prove "p implies p for all p"
            "all p:o. p => p"
        |> status
        |> all_right "p"
        |> status
        |> imp_right "h"
        |> status
        |> assumption "h"
        |> qed

    |> prove "swap arguments"
            "all p:o. all q:o. p and q => q and p"
        |> status
        |> all_right "p" |> all_right "q"
        |> imp_right "h" |> and_left "h" "h0" "h1"
        |> status
        |> and_right |> assumption "h1" |> assumption "h0"
        |> qed

