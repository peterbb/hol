open Term

type theory = {
    sign     : Sign.t;
    theorems : Term.t StringMap.t
}

let add_type name theory =
    { theory with sign = Sign.add_type name theory.sign }

let add_con name typ theory =
    { theory with sign = Sign.add_con name typ theory.sign }

let add_icon name typ theory =
    { theory with sign = Sign.add_icon name typ theory.sign }

let init = 
    let prop = Type.Atom "o" in
    let nat = Type.Atom "nat" in
    let arrow a b = Type.Arrow (a, b) in
    let binary_connective = arrow prop (arrow prop prop) in
    let quantifier =
        OpenType.Arrow (OpenType.Arrow (OpenType.Hole, OpenType.Atom "o"),
                        OpenType.Atom "o")
    in
    {
        sign = Sign.empty;
        theorems = StringMap.empty
    }
    |> add_type "o"
    |> add_type "nat"
    |> add_con "zero" nat
    |> add_con "succ" (arrow nat nat)
    |> add_con "true" prop
    |> add_con "false" prop
    |> add_con "and" binary_connective
    |> add_con "or" binary_connective
    |> add_con "imp" binary_connective
    |> add_icon "all" quantifier
    |> add_icon "ex" quantifier


type goal = {
    ctx : Ctx.t ;
    hyps : Term.t StringMap.t;
    goal : Term.t
}

let shift  hyps  =
    StringMap.map Term.shift hyps 

let init_goal goal =
    { goal; ctx = Ctx.empty; hyps = StringMap.empty }

type proof = {
    goals : goal list;
    name : string;
    result : Term.t;
    theory : theory
}

let prove name goal theory =
    Term.check theory.sign Ctx.empty goal (Type.Atom "o");
    let goals = [init_goal goal] in
    { goals; name; result = goal; theory }

let proof_status ({ goals } as state) = 
    let open Printf in
    let print_goal {ctx; hyps; goal} =
        let print_hyp name prop =
            printf " (%s)\t %s\n" name (Term.to_string ctx prop)
        and print_var name type_ =
            printf " %s : %s\n" name (Type.to_string type_)
        in
        (if not (Ctx.is_empty ctx) then printf "vars:\n");
        Ctx.iter print_var ctx;
        (if not (StringMap.is_empty hyps) then printf "hyps:\n");
        StringMap.iter print_hyp hyps;
        printf "===============================================\n";
        printf " %s\n" (Term.to_string ctx goal)
    in
    printf "\n\n";
    begin match goals with
    | [] -> printf "No goals left.\n"
    | [g] ->
        printf "One goal left.\n";
        print_goal g
    | g :: _ ->
        printf "%n goals left.\n" (List.length goals);
        print_goal g
    end;
    state
    

let qed = function
    | { goals = []; name; result; theory } ->
      let theorems = StringMap.add_unique name result theory.theorems in
      { theory with theorems }
    | _ ->
      failwith "qed: still goals left"

let apply f = function
    | { goals = g :: gs } as state ->
        { state with goals = (f g) @ gs }
    | { goals = [] } ->
        failwith "apply: no goals"

let true_right = apply begin function
    | {goal = Term.App (Term.Con ("true", None), []) } ->
        []
    | _ -> failwith "true_right"
end

let false_left h = apply begin function { hyps } as g ->
    begin match StringMap.find h hyps with
    | Term.App (Term.Con ("false", None), []) ->
        []
    | _ -> failwith "false_left"
    end
end
    

let and_right = apply begin function
    | {goal = Term.App (Term.Con ("and", None), [a; b]) } as g ->
        [ { g with goal = a }; {g with goal = b } ]
    | _ -> failwith "and_right"
end

let and_left h h0 h1 =
    apply begin function { hyps } as g ->
        begin match StringMap.find h hyps with
        | Term.App (Term.Con ("and", None), [a; b]) ->
            hyps
            |> StringMap.remove h
            |> StringMap.add h0 a
            |> StringMap.add h1 b
            |> fun hyps -> [ { g with hyps } ]
        | _ -> failwith "and_left"
        end
    end

let or_right_0 =
    apply begin function
    | { goal = Term.App (Term.Con ("or", None), [a; _]) } as g ->
        [ { g with goal = a } ]
    | _ -> failwith "or_right_0"
    end

let or_right_1 = apply begin function
    | { goal = Term.App (Term.Con ("or", None), [_; b]) } as g ->
        [ { g with goal = b } ]
    | _ -> failwith "or_right_1"
end

let or_left h h0 h1 = apply begin function { hyps } as g ->
    begin match StringMap.find h hyps with
    | Term.App (Term.Con ("or", None), [a; b]) ->
        let hyps = StringMap.remove h hyps in
        [
            { g with hyps = StringMap.add h0 a hyps };
            { g with hyps = StringMap.add h1 b hyps }
        ]
    | _ -> failwith "or_left"
    end
end

let imp_right h = apply begin function
    | { goal = Term.App (Term.Con ("imp", None), [a; b]) } as g ->
	    [ { g with goal = b; hyps = StringMap.add h a g.hyps } ]
    | _ -> failwith "imp_right"
end

let imp_left h h' = apply begin function { hyps } as g ->
    begin match StringMap.find h hyps with
    | Term.App (Term.Con ("imp", None), [a; b]) ->
        let hyps = StringMap.remove h hyps in
        let g = { g with hyps } in
        [ { g with goal = a }; { g with hyps = StringMap.add h' b hyps }]  
    | _ -> failwith "imp_left"
    end
end

let all_right x = apply begin function
    | { goal = Term.App (Term.Con ("all", Some typ), [body]) } as g ->
        (* XXX: must shift whole context by one *)
        let body_type = Type.Arrow (typ, Type.Atom "o") in
        let head = Term.Redex (body, body_type) in
        let arg = Term.App (Term.Var 0, []) in
        let goal = Term.App (head, [arg]) in
        let ctx = Ctx.add x typ g.ctx in
        let hyps = shift g.hyps in
        [ { g with goal; ctx; hyps } ]
    | _ -> failwith "all_right"
end 

let all_left h e = apply begin function { hyps } as g ->
    (* XXX: must check e : typ *)
    begin match StringMap.find h hyps with
    | Term.App (Term.Con ("all", Some typ), [body]) ->
        let body_type = Type.Arrow (typ, Type.Atom "o") in
        let head = Term.Redex (body, body_type) in
        hyps
        |> StringMap.add h (Term.App (head, [e]))
        |> fun hyps -> [{ g with hyps }]
    | _ -> failwith "all_left"
    end
end

