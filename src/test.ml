open State
open Term

let binop name a b = Term.App (Term.Con (name, None), [a; b])
let quant name var type_ body =
    Term.App (Term.Con (name, Some type_),
        [Term.Lam (var, body)])

let _o = Type.Atom "o"
let _i = Type.Atom "i"
let _true = Term.App (Term.Con ("true", None), [])
let _false = Term.App (Term.Con ("false", None), [])
let _var i = Term.App (Term.Var i, [])
let _and = binop "and"
let _or = binop "or"
let _imp = binop "imp"
let _all = quant "all"


let _ =
    init
    |> prove "trivial_truth" _true
        |> proof_status
        |> true_right
        |> proof_status
        |> qed

    |> prove "true_and_true" (_and _true _true)
        |> and_right
        (* Left hand side *)
            |> true_right
        (* Right hand side *)
            |> true_right
        |> qed

    |> prove "true_implies_true" (_imp _true _true)
        |> proof_status
        |> imp_right "h"
        |> proof_status
        |> true_right
        |> qed

    |> prove "true_or_false" (_or _true _false)
        |> or_right_0 |> true_right
        |> qed

    |> prove "false_or_true" (_or _false _true)
        |> or_right_1 |> true_right
        |> qed

    |> prove "false_implies_false" (_imp _false _false)
        |> proof_status
        |> imp_right "h"
        |> proof_status
        |> false_left "h"
        |> qed

    |> prove "false_and_true_implies_false"
             (_imp (_and _false _true) _false)
        |> proof_status
        |> imp_right "h"
        |> proof_status
        |> and_left "h" "h0" "h1"
        |> proof_status
        |> false_left "h0"
        |> qed

    |> prove "false_or_false_implies_false"
            (_imp (_or _false _false) _false)
        |> imp_right "h"
        |> or_left "h" "h0" "h1"
        (* First case *)
            |> proof_status
            |> false_left "h0"
        (* Second case *)
            |> proof_status
            |> false_left "h1"
        |> qed

    |> prove "forall x:i, true"
            (_all "x" _i (_all "y" _i _true))
        |> proof_status
        |> all_right "z"
        |> proof_status



