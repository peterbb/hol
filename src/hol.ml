open Core

let parse_type text =
    Parser.typ Lexer.token (Lexing.from_string text)

let parse_term ctx text =
    let term = Parser.term Lexer.token (Lexing.from_string text) in
    let rec abs i term = function
        | [] -> term
        | x :: ctx -> abs (i+1) (Ast.Term.abs x i term) ctx
    in abs 0 term (Typing.Ctx.names ctx)

type theory = Theory.t
type proof = Proof.t

    

let init = Theory.init

let add_type = Theory.add_type

let add_con name typ = Theory.add_con name (parse_type typ)

let prove name prop =
    Theory.prove name (parse_term Typing.Ctx.empty prop)

let qed = Proof.qed

let status = Proof.status

let assumption h =
    Proof.apply (Goal.assumption h)

let cut prop h proof =
    let ctx = Proof.ctx 0 proof in
    let prop = parse_term ctx prop in
    Proof.apply (Goal.cut prop h) proof

let true_right =
    Proof.apply Goal.true_right

let false_left h =
    Proof.apply (Goal.false_left h)

let and_right =
    Proof.apply Goal.and_right

let and_left h h0 h1 =
    Proof.apply (Goal.and_left h h0 h1)

let or_right_0 =
    Proof.apply Goal.or_right_0

let or_right_1 =
    Proof.apply Goal.or_right_1

let or_left h h0 h1 =
    Proof.apply (Goal.or_left h h0 h1)

let imp_right h =
    Proof.apply (Goal.imp_right h)

let imp_left h h' =
    Proof.apply (Goal.imp_left h h')

let all_right x =
    Proof.apply (Goal.all_right x)

let all_left h term h' proof =
    let ctx = Proof.ctx 0 proof in
    let term = parse_term ctx term in
    Proof.apply (Goal.all_left h term h') proof

let ex_right term proof =
    let ctx = Proof.ctx 0 proof in
    let term = parse_term ctx term in
    Proof.apply (Goal.ex_right term) proof

let ex_left x h =
    Proof.apply (Goal.ex_left x h)

let mvar mvar type_ =
    let type_ = parse_type type_ in
    Proof.mvar mvar type_

let axiom name prop theory =
    theory
    |> prove name prop
        |> Proof.apply Goal.axiom
        |> qed
