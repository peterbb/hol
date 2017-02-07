open Hol

let parse_type text =
    Parser.typ Lexer.token (Lexing.from_string text)

let parse_term ?(ctx=Typing.Ctx.empty) text =
    let term = Parser.term Lexer.token (Lexing.from_string text) in
    let rec abs i term = function
        | [] -> term
        | x :: ctx -> abs (i+1) (ParseUtil.abs x i term) ctx
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
        

let display_goal goal =
    let open Goal in
    let {ctx; hyps; goal} = goal in
    let open Printf in
    let print_hyp name prop =
        printf " %s : %s\n" name (Print.term_to_string ctx prop)
    and print_var name type_ =
        printf " %s : %s\n" name (Print.type_to_string type_)
    in
    (if not (Typing.Ctx.is_empty ctx) then printf "vars:\n");
    Typing.Ctx.iter print_var ctx;
    (if not (StringMap.is_empty hyps) then printf "hyps:\n");
    StringMap.iter print_hyp hyps;
    printf "===============================================\n";
    printf " %s\n" (Print.term_to_string ctx goal)


let status proof =
    let open Printf in
    let open Proof in
    let open Tactic in
    let {mCtx; goals} = Proof.view proof in
    printf "\n\n";
    printf "Meta variables:\n";
    Typing.MCtx.iter
        (fun k t -> printf " ?%s : %s\n" k (Print.type_to_string t))
        mCtx;
    begin match goals with
    | [] -> printf "No goals left.\n"
    | [g] ->
        printf "One goal left.\n";
        display_goal g
    | g :: _ ->
        printf "%n goals left.\n" (List.length goals);
        display_goal g
    end;
    proof

