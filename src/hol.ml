open Core

let parse_type text =
    Parser.typ Lexer.type_token (Lexing.from_string text)

let parse_term text =
    Parser.term Lexer.term_token (Lexing.from_string text)


type theory = Theory.t
type proof = Proof.t

let init = Theory.init

let add_type = Theory.add_type

let add_con name typ = Theory.add_con name (parse_type typ)

let prove name prop = Theory.prove name (parse_term prop)

let qed = Proof.qed

let status = Proof.status

let assumption h =
    Proof.apply (Goal.assumption h)

let cut prop h =
    let prop = parse_term prop in
    Proof.apply (Goal.cut prop h)

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

let all_left h term h' =
    let term = parse_term term in
    Proof.apply (Goal.all_left h term h')

let ex_right term =
    let term = parse_term term in
    Proof.apply (Goal.ex_right term)

let ex_left x h =
    Proof.apply (Goal.ex_left x h)
