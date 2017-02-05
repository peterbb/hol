open Hol
open HOL
open Ast


let _ = Theory.init

    |> Theory.prove "p implies p" (_all "p" o (_imp (_x 0) (_x 0)))
        |> Proof.status
        |> Proof.apply (Goal.all_right "q")
        |> Proof.status
        |> Proof.apply (Goal.imp_right "h")
        |> Proof.status
        |> Proof.apply (Goal.assumption "h")
        |> Proof.status
        |> Proof.qed

    |> Theory.prove "if p and q, then q and p"
        (_all "p" o (_all "q" o
                        (_imp (_and (_x 1) (_x 0))
                              (_and (_x 0) (_x 1)))))
        |> Proof.apply (Goal.all_right "p'")
        |> Proof.apply (Goal.all_right "q'")
        |> Proof.apply (Goal.imp_right "h")
        |> Proof.apply (Goal.and_left "h" "h0" "h1")
        |> Proof.apply Goal.and_right 
            |> Proof.apply (Goal.assumption "h1")   
            |> Proof.apply (Goal.assumption "h0")
        |> Proof.qed

