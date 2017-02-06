open Hol

let _ =
    init
    |> add_con "eq" "nat -> nat -> o"
    |> add_con "lt" "nat -> nat -> o"
    |> add_con "plus" "nat -> nat -> nat"
    |> add_con "mult" "nat -> nat -> nat"

    |> axiom "nat-ind"
        ("all p: nat -> o. p zero and (all n: nat. p n => p (succ n)) =>" ^
           "all n: nat. p n") 

	|> axiom "eq-sub"
		"all n:nat. all m:nat. all p: nat -> o. eq n m and p n => p m"

    (* "eq" is an equivalence relation. *)
    |> axiom "eq-refl" "all n:nat. eq n n"
    |> axiom "eq-sym"  "all n:nat. all m:nat. eq n m => eq m n"
    |> axiom "eq-trans"
        ("all n:nat. all m:nat. all o:nat." ^
            "eq n m and eq m o => eq n o")

    |> axiom "eq-zero" "eq zero zero"
    |> axiom "eq-succ" "all n:nat. all m:nat. eq n m => eq (succ n) (succ m)"
    |> axiom "eq-zero-succ" "all n:nat. eq zero (succ n) => false"

    |> axiom "plus-zero" "all n:nat. eq (plus zero n) n"
    |> axiom "plus-succ"
        "all n:nat. all m:nat. eq (plus (succ n) m) (succ (plus n m))"

    |> prove "plus-zero-right" "all n:nat. eq (plus n zero) n"
        |> all_left "nat-ind" "\\n. eq (plus n zero) n" "h"
        |> imp_left "h" "h"
        |> and_right
        |> all_left "plus-zero" "zero" "h" |> assumption "h"
        |> all_right "n" |> imp_right "h"
        |> all_left "plus-succ" "n" "hx"
        |> all_left "hx" "zero" "hx"
        |> all_left "eq-succ" "(plus n zero)" "hy"
        |> all_left "hy" "n" "hy"
        |> imp_left "hy" "hy" |> assumption "h"
        |> all_left "eq-trans" "(plus (succ n) zero)" "hz"
        |> all_left "hz" "(succ (plus n zero))" "hz"
        |> all_left "hz" "(succ n)" "hz"
        |> imp_left "hz" "hz" |> and_right
	      	|> assumption "hx"
		|> assumption "hy"
		|> assumption "hz"
		|> assumption "h"
		|> qed

 	|> prove "plus-succ-right" ("all n:nat. all m:nat. all o:nat." ^
					"eq (plus n m) o => eq (plus n (succ m)) (succ o)")
        |> all_left "nat-ind"
			("\\n. all m:nat. all o:nat. eq (plus n m) o =>" ^
				"eq (plus n (succ m)) (succ o)") "h"
		|> imp_left "h" "h"
		|> and_right
		(* base case *)
			|> all_right "m" |> all_right "o" |> imp_right "h"
			|> all_left "plus-zero" "m" "h'"
		|> status


