open Term

module rec Theory : sig
    type t = {
        sign     : Sign.t;
        theorems : Term.t StringMap.t
    }

    val init : t
    val add_type : string -> t -> t
    val add_con : string -> Type.t -> t -> t

    val check_term : t -> Ctx.t -> Term.t -> Type.t -> unit

    val prove : string -> Term.t -> t -> Proof.t

end = struct
    type t = {
        sign     : Sign.t;
        theorems : Term.t StringMap.t
    }

    let check_term {sign} ctx e a =
        Term.check sign ctx e a

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

    let prove name goal theory =
        check_term theory Ctx.empty goal (Type.Atom "o");
        let open Proof in
        let goals = [Goal.init goal] in
        { goals; name; result = goal; theory }

end
and Goal : sig
    type t
    type tactic = Theory.t -> t -> t list

    val display : t -> unit

    val init : Term.t -> t

    val assumption : string -> tactic
    val cut        : Term.t -> string -> tactic
    val true_right : tactic
    val false_left : string -> tactic
    val and_right  : tactic
    val and_left   : string -> string -> string -> tactic
    val or_right_0 : tactic
    val or_right_1 : tactic
    val or_left    : string -> string -> string -> tactic
    val imp_right  : string -> tactic
    val imp_left   : string -> string -> tactic
    val all_right  : string -> tactic
    val all_left   : string -> Term.t -> string -> tactic
    val ex_right   : Term.t -> tactic
    val ex_left    : string -> string -> tactic

end = struct
    type t = {
        ctx : Ctx.t ;
        hyps : Term.t StringMap.t;
        goal : Term.t
    }
    type tactic = Theory.t -> t -> t list

    let init goal =
        { goal; ctx = Ctx.empty; hyps = StringMap.empty }

    let shift_hyps ({hyps} as g) =
        let hyps = StringMap.map Term.shift hyps in
        { g with hyps }

    let shift_conc ({goal} as g) =
        let goal = Term.shift goal in
        { g with goal }

    let display {ctx; hyps; goal} =
        let open Printf in
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
        

    (*
     * ----------------------------------------
     *   Gamma; Delta, h: A |- A
     *)
    let assumption h _ {hyps; goal} =
        match StringMap.find h hyps with
        | hyp when Term.eq goal hyp -> 
            []
        | _ -> failwith "assumption"

    (*
     * Gamma; Delta |- A    Gamma; Delta, h: A |- C
     * ----------------------------------------------
     * Gamma; Delta |- C
     *)
    let cut e h theory ({ctx; hyps} as g) =
        Theory.check_term theory ctx e (Type.Atom "o");
        let hyps = StringMap.add h e hyps in
        [ { g with goal = e }; { g with hyps }]


    (*
     *  -----------------
     *      |- true
     *)
    let true_right _ = function
        | {goal = Term.App (Term.Con ("true", None), []) } ->
            []
        | _ -> failwith "true_right"

    (*
     *  --------------------
     *    h:false |-
     *)
    let false_left h _ = function { hyps } ->
        begin match StringMap.find h hyps with
        | Term.App (Term.Con ("false", None), []) ->
            []
        | _ -> failwith "false_left"
        end

    (*   |- A     |- B
     *  ----------------
     *     |- and A B
     *)
    let and_right _ = function
        | {goal = Term.App (Term.Con ("and", None), [a; b]) } as g ->
            [ { g with goal = a }; {g with goal = b } ]
        | _ -> failwith "and_right"

    (*
     * h0: A, h1: B |-
     * ----------------------
     *  h: and A B |-
     *)
    let and_left h h0 h1 _ =
        function { hyps } as g ->
            begin match StringMap.find h hyps with
            | Term.App (Term.Con ("and", None), [a; b]) ->
                hyps
                |> StringMap.remove h
                |> StringMap.add h0 a
                |> StringMap.add h1 b
                |> fun hyps -> [ { g with hyps } ]
            | _ -> failwith "and_left"
            end

    (*
     *      |- A
     * ----------------------
     *      |- or A B
     *)
    let or_right_0 _ = function
        | { goal = Term.App (Term.Con ("or", None), [a; _]) } as g ->
            [ { g with goal = a } ]
        | _ -> failwith "or_right_0"

    (*
     *      |- B
     * -------------------
     *      |- or A B
     *)
    let or_right_1 _ = function
        | { goal = Term.App (Term.Con ("or", None), [_; b]) } as g ->
            [ { g with goal = b } ]
        | _ -> failwith "or_right_1"


    (*
     *  Gamma; Delta, h0: A |- C       Gamma; Delta, h1: A |- C
     * ---------------------------------------------------------
     *   h: or A B |- C
     *)
    let or_left h h0 h1 _ = function { hyps } as g ->
        begin match StringMap.find h hyps with
        | Term.App (Term.Con ("or", None), [a; b]) ->
            let hyps = StringMap.remove h hyps in
            [
                { g with hyps = StringMap.add h0 a hyps };
                { g with hyps = StringMap.add h1 b hyps }
            ]
        | _ -> failwith "or_left"
        end

    (*
     *  Gamma; Delta, h: A |- B
     * ----------------------------------
     *  Gamma; Delta       |- imp A B
     *)
    let imp_right h _ = function
        | { goal = Term.App (Term.Con ("imp", None), [a; b]) } as g ->
            [ { g with goal = b; hyps = StringMap.add h a g.hyps } ]
        | _ -> failwith "imp_right"


    (*
     *  Gamma; Delta |- A      Gamma; Delta, h': B |- C
     * --------------------------------------------------
     *  Gamma; Delta, h: imp A B |- C
     *)
    let imp_left h h' _ = function { hyps } as g ->
        begin match StringMap.find h hyps with
        | Term.App (Term.Con ("imp", None), [a; b]) ->
            let hyps = StringMap.remove h hyps in
            let g = { g with hyps } in
            [ { g with goal = a }; { g with hyps = StringMap.add h' b hyps }]  
        | _ -> failwith "imp_left"
        end


    (*
     *   Gamma, x:tau; shift(Delta) |- A[x]
     * --------------------------------------
     *   Gamma; Delta |- all x:tau. A[x]
     *)
    let all_right x _ = function
        | { goal = Term.App (Term.Con ("all", Some typ), [body]) } as g ->
            let arg = Term.App (Term.Var 0, []) in
            let goal = Term.redex body [arg] in
            let ctx = Ctx.add x typ g.ctx in
            [ { g with goal; ctx } |> shift_hyps]
        | _ -> failwith "all_right"

    (*
     *    Gamma |- e : tau      Gamma; Delta, h': A[e] |- C
     * -------------------------------------------------------
     *    Gamma; Delta, h: all x:tau. A[x] |- C
     *)
    let all_left h e h' theory ({ctx; hyps} as g) =
        match StringMap.find h hyps with
        | Term.App (Term.Con ("all", Some typ), [body]) ->
            Theory.check_term theory ctx e typ;
            hyps
            |> StringMap.remove h
            |> StringMap.add h' (Term.redex body [e])
            |> fun hyps -> [{ g with hyps }]
        | _ -> failwith "all_left"

    (*
     *  Gamma |- e : tau     Gamma; \Delta |- A[e]
     * ---------------------------------------------
     *  Gamma; Delta |- ex x:tau, A[x]
     *)
    let ex_right e theory = function
        | ({ctx; goal = Term.App (Term.Con ("ex", Some typ), [body])}) as g ->
            Theory.check_term theory ctx e typ;
            let goal = Term.redex body [e] in
            [ { g with goal }]
        | _ -> failwith "ex_right"

    (*
     *  Gamma, x:tau; wk(Delta), h: A[x] |- wk(C)
     * ------------------------------------------
     *  Gamma; Delta, h: ex x:tau, A[x] |- C
     *)
    let ex_left h x _ {ctx; hyps; goal} =
        match StringMap.find h hyps with
        | Term.App (Term.Con ("ex", Some typ), [body]) ->
            let ctx = Ctx.add x typ ctx in
            let hyps = hyps |>
                       StringMap.remove h |>
                       StringMap.map Term.shift |>
                       StringMap.add h body in
            let goal = Term.shift goal in
            [{ ctx; hyps; goal }]
        | _ -> failwith "ex_left"

end
and Proof : sig
    type t = {
        goals : Goal.t list;
        name  : string;
        result : Term.t;
        theory : Theory.t
    }
    val apply : Goal.tactic -> t -> t
    val qed : t -> Theory.t
    val status : t -> t
end = struct
    type t = {
        goals : Goal.t list;
        name : string;
        result : Term.t;
        theory : Theory.t
    }

    let apply f = function
        | { goals = g :: gs; theory } as proof ->
            { proof with goals = (f theory g) @ gs }
        | { goals = [] } ->
            failwith "apply: no goals"

    let qed proof = 
        let open Theory in
        match proof with
        | { goals = []; name; result; theory } ->
          let theorems = StringMap.add_unique name result theory.theorems in
          { theory with theorems = theorems }
        | _ ->
          failwith "qed: still goals left"

    let status ({goals} as proof)=
        let open Printf in
        let open Proof in
        let open Goal in
        printf "\n\n";
        begin match goals with
        | [] -> printf "No goals left.\n"
        | [g] ->
            printf "One goal left.\n";
            Goal.display g
        | g :: _ ->
            printf "%n goals left.\n" (List.length goals);
            Goal.display g
        end; 
        proof
end

