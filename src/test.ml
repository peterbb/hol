open Hol

let _ =
    init
    |> add_con "eq" "nat -> nat -> o"
    |> add_con "lt" "nat -> nat -> o"
    |> add_con "plus" "nat -> nat -> nat"
    |> add_con "mult" "nat -> nat -> nat"

	|> axiom "eq-sub"
		"all n:nat. all m:nat. all p: nat -> o. eq n m and p n => p m"

    |> axiom "nat-ind"
        ("all p: nat -> o. p zero and (all n: nat. p n => p (succ n)) =>" ^
           "all n: nat. p n") 

    (* "eq" is an equivalence relation. *)
    |> axiom "eq-refl" "all n:nat. eq n n"
    |> axiom "eq-sym"  "all n:nat. all m:nat. eq n m => eq m n"
    |> axiom "eq-trans"
        ("all n:nat. all m:nat. all o:nat." ^
            "eq n m and eq m o => eq n o")

    |> axiom "eq-zero" "eq zero zero"
    |> axiom "eq-succ" "all n:nat. all m:nat. eq n m => eq (succ n) (succ m)"
    |> axiom "eq-zero-succ" "all n:nat. eq zero (succ n) => false"

    |> axiom "0+n=n" "all n:nat. eq (plus zero n) n"
    |> axiom "Sn+m=S(n+m)"
        "all n:nat. all m:nat. eq (plus (succ n) m) (succ (plus n m))"

    |> prove "plus-zero-right" "all n:nat. eq (plus n zero) n"
		|> elim "nat-ind" "h" [
        	`With "\\n. eq (plus n zero) n";
			`Imp
		]
        |> and_right
		(* Base case *)
			|> elim "0+n=n" "h" [
				`With "zero"; `Qed
			]
		(* Inductive step *)
			|> assume [`Var "n"; `Hyp "h"]
			|> elim "Sn+m=S(n+m)" "hx" [
				`With "n";
				`With "zero";
			]
			|> elim "eq-succ" "hy" [
				`With "plus n zero";
				`With "n";
				`Imp
			]
			|> assumption "h"
			|> all_left "eq-trans" "(plus (succ n) zero)" "hz"
			|> all_left "hz" "(succ (plus n zero))" "hz"
			|> all_left "hz" "(succ n)" "hz"
			|> imp_left "hz" "hz" |> and_right
				|> assumption "hx"
			|> assumption "hy"
			|> assumption "hz"
		|> assumption "h"
		|> qed

	|> prove "n=0+n" "all n:nat. eq n (plus zero n)"
		|> all_right "n" |> all_left "0+n=n" "n" "h1"
		|> all_left "eq-sym" "plus zero n" "h2" |> all_left "h2" "n" "h2"
		|> imp_left "h2" "h2" |> assumption "h1"
		|> assumption "h2"
		|> qed

	|> prove "S(n+m)=Sn+m"
			"all n:nat. all m:nat. eq (succ (plus n m)) (plus (succ n) m)"
		|> assume [`Var "n"; `Var "m"]
		|> all_left "Sn+m=S(n+m)" "n" "h0"
		|> all_left "h0" "m" "h0"
		|> all_left "eq-sym" "plus (succ n) m" "h1"
		|> all_left "h1" "succ (plus n m)" "h1"
		|> imp_left "h1" "h1" |> assumption "h0"
		|> assumption "h1"
		|> qed

 	|> prove "plus-succ-right" ("all n:nat. all m:nat." ^
					"eq (plus n (succ m)) (succ (plus n m))")
		|> all_left "nat-ind"
					"\\n. all m:nat. eq (plus n (succ m)) (succ (plus n m))"
					"h"
		|> imp_left "h" "h" |> and_right

		(* base case *)
			|> assume [`Var "m"]
			|> elim "eq-sub" "h1" [
				`With "m";
				`With "plus zero m";
				`With "\\x. eq (plus zero (succ m)) (succ x)";
				`Imp
			]
			|> and_right
			|> elim "n=0+n" "h1" [ `With "m"; `Qed ]
			|> elim "0+n=n" "h0" [ `With "succ m"; `Qed ]
			|> assumption "h1"

		(* induction case *)
			|> assume [`Var "n"; `Hyp "ih"; `Var "m"]
			|> elim "ih" "ih" [`With "m"]
			|> elim "Sn+m=S(n+m)" "h2" [
				`With "n"; `With "succ m"
			]
			|> elim "S(n+m)=Sn+m" "h3" [
				`With "n"; `With "m"
			]
			|> elim "eq-trans" "h4" [
				`With "plus n (succ m)";
				`With "succ (plus n m)";
				`With "plus (succ n) m";
				`Imp
			]
			|> and_right
				|> assumption "ih"
				|> assumption "h3"
			|> elim "eq-succ" "h5" [
				`With "plus n (succ m)";
				`With "plus (succ n) m";
				`Imp
			]
				|> assumption "h4"
			|> elim "eq-trans" "h6" [
				`With "plus (succ n) (succ m)";
				`With "succ (plus n (succ m))";
				`With "succ (plus (succ n) m)";
				`Imp
			]
				|> and_right |> assumption "h2" |> assumption "h5"
			|> assumption "h6"
		|> assumption "h"
		|> qed

	|> prove "n+m=m+n" "all n:nat. all m:nat. eq (plus n m) (plus m n)"
		|> assume [`Var "n"; `Var "m"]
		|> mvar "P" "nat -> nat -> o"
		|> elim "nat-ind" "h" [
			`With "?P m"; `Imp 
		]
	|> status
		|> set_mvar "P" "\\m.\\x. eq (plus x m) (plus m x)"
		(* Base case *)
	
	|> status

