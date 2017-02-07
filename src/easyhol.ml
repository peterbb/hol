open Hol

let parse_type text =
    Parser.typ Lexer.token (Lexing.from_string text)

let parse_term ?(ctx=Typing.Ctx.empty) text =
    let term = Parser.term Lexer.token (Lexing.from_string text) in
    let rec abs i term = function
        | [] -> term
        | x :: ctx -> abs (i+1) (Ast.Term.abs x i term) ctx
    in abs 0 term (Typing.Ctx.names ctx)

let ctx_of_first_goal proof = 
    (List.nth (Proof.view proof).Proof.goals 0).Goal.ctx

type theory = Theory.t
type proof = Proof.t

let init = Theory.init

let add_type = Theory.add_type

let add_con name typ = Theory.add_con name (parse_type typ)

let prove name prop =
    Theory.prove name (parse_term prop)

let qed = Proof.qed

let status = Proof.status

let assumption h =
    Proof.apply (Tactic.assumption h)

let cut prop h proof =
    let prop = parse_term ~ctx:(ctx_of_first_goal proof) prop in
    Proof.apply (Tactic.cut prop h) proof

let true_right =
    Proof.apply Tactic.true_right

let false_left h =
    Proof.apply (Tactic.false_left h)

let and_right =
    Proof.apply Tactic.and_right

let and_left h h0 h1 =
    Proof.apply (Tactic.and_left h h0 h1)

let or_right_0 =
    Proof.apply Tactic.or_right_0

let or_right_1 =
    Proof.apply Tactic.or_right_1

let or_left h h0 h1 =
    Proof.apply (Tactic.or_left h h0 h1)

let imp_right h =
    Proof.apply (Tactic.imp_right h)

let imp_left h h' =
    Proof.apply (Tactic.imp_left h h')

let all_right x =
    Proof.apply (Tactic.all_right x)

let all_left h term h' proof =
    let term = parse_term ~ctx:(ctx_of_first_goal proof) term in
    Proof.apply (Tactic.all_left h term h') proof

let ex_right term proof =
    let term = parse_term ~ctx:(ctx_of_first_goal proof) term in
    Proof.apply (Tactic.ex_right term) proof

let ex_left x h =
    Proof.apply (Tactic.ex_left x h)

let mvar mvar type_ =
    let type_ = parse_type type_ in
    Proof.mvar mvar type_

let set_mvar mvar term =
    let term = parse_term term in
    Proof.set_mvar mvar term

let axiom name prop theory =
    theory
    |> prove name prop
        |> Proof.apply Tactic.axiom
        |> qed


let rec assume = function
    | [] -> fun proof -> proof
    | `Var x :: rest ->
        fun proof -> proof |> all_right x |> assume rest
    | `Hyp h :: rest ->
        fun proof -> proof |> imp_right h |> assume rest

let rec elim h0 h1 =
    let elim_single h h' = function
        | `With t -> all_left h t h'
        | `Imp -> imp_left h h'
        | `Qed -> assumption h
    in
    let rec elim_list = function
        | [] -> fun proof ->
            proof
        | e :: rest -> fun proof ->
            proof |> elim_single h1 h1 e |> elim_list rest
    in
    function
    | [] -> fun proof -> proof
    | start :: rest -> fun proof ->
        proof |> elim_single h0 h1 start |> elim_list rest
        

