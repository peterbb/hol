module rec Theory : sig
    type view = {
        sign     : Typing.Sign.t;
        theorems : Ast.Term.t StringMap.t
    }

    type t = view

    val view : t -> view

    val init : t
    val add_type : string -> t -> t
    val add_con : string -> Type.t -> t -> t

    val check_type : t -> Type.t -> unit
    val check_term : t -> Typing.MCtx.t -> Typing.Ctx.t ->
                     Ast.Term.t -> Type.t -> unit

    val prove : string -> Ast.Term.t -> t -> Proof.t

end = struct
    type view = {
        sign     : Typing.Sign.t;
        theorems : Ast.Term.t StringMap.t
    }
    type t = view

    let view theory = theory

    let check_type {sign} type_ =
        Typing.Sign.check_type sign type_

    let check_term {sign} mCtx ctx e a =
        Typing.Term.check sign mCtx ctx e a

    let add_type name theory =
        { theory with sign = Typing.Sign.add_type name theory.sign }

    let add_con name typ theory =
        { theory with sign = Typing.Sign.add_con name typ theory.sign }

    let add_icon name typ theory =
        { theory with sign = Typing.Sign.add_icon name typ theory.sign }

    let init = 
        let prop = Type.Atom "o" in
        let nat = Type.Atom "nat" in
        let arrow a b = Type.Arrow (a, b) in
        let binary_connective = arrow prop (arrow prop prop) in
        let quantifier =
            Typing.OpenType.Arrow (Typing.OpenType.Arrow
                                (Typing.OpenType.Hole, Typing.OpenType.Atom "o"),
                             	Typing.OpenType.Atom "o")
        in
        {
            sign = Typing.Sign.empty;
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
        check_term theory Typing.MCtx.empty Typing.Ctx.empty
                   goal (Type.Atom "o");
        let open Proof in
        let goals = [Tactic.init goal] in
        let mCtx = Typing.MCtx.empty in
        { mCtx; goals; name; result = goal; theory }

end

and Goal : sig
    type view = {
        ctx  : Typing.Ctx.t ;
        hyps : Ast.Term.t StringMap.t;
        goal : Ast.Term.t
    }
    type t = view

    val view : t -> view
end = struct
    type view = {
        ctx : Typing.Ctx.t ;
        hyps : Ast.Term.t StringMap.t;
        goal : Ast.Term.t
    }
    type t = view
    let view goal = goal
end 

and Tactic : sig
    type view = Theory.view -> Typing.MCtx.t -> Goal.view -> Goal.view list
    type t = view

    val view : t -> view

    val mvar_subst : Ast.Term.t -> string -> Goal.t -> Goal.t

    val init : Ast.Term.t -> Goal.t

    val assumption : string -> t
    val cut        : Ast.Term.t -> string -> t
    val true_right : t
    val false_left : string -> t
    val and_right  : t
    val and_left   : string -> string -> string -> t
    val or_right_0 : t
    val or_right_1 : t
    val or_left    : string -> string -> string -> t
    val imp_right  : string -> t
    val imp_left   : string -> string -> t
    val all_right  : string -> t
    val all_left   : string -> Ast.Term.t -> string -> t
    val ex_right   : Ast.Term.t -> t
    val ex_left    : string -> string -> t

    val axiom      : t
end = struct
    type view = Theory.view -> Typing.MCtx.t -> Goal.view -> Goal.view list
    type t = view
 
    let view tactic = tactic

    open Goal

    let mvar_subst term mvar ({hyps; goal} as g) =
        let goal = Ast.Term.mvar_subst term mvar goal in
        let hyps = StringMap.map (Ast.Term.mvar_subst term mvar) hyps in
        { g with goal; hyps }

    let init goal =
        let ctx = Typing.Ctx.empty in
        { goal; ctx; hyps = StringMap.empty }


    let lookup_hyp h theory hyps =
        try StringMap.find h hyps with
        | Not_found -> begin
            try StringMap.find h theory.Theory.theorems with
            | Not_found -> failwith ("unknown hyp " ^ h)
        end

    (*
     * ----------------------------------------
     *   Gamma; Delta, h: A |- A
     *)
    let assumption h theory _ {hyps; goal} =
        match lookup_hyp h theory hyps with
        | hyp when Ast.Term.eq goal hyp -> 
            []
        | _ -> failwith "assumption"

    (*
     * Gamma; Delta |- A    Gamma; Delta, h: A |- C
     * ----------------------------------------------
     * Gamma; Delta |- C
     *)
    let cut e h theory mCtx ({ctx; hyps} as g) =
        Theory.check_term theory mCtx ctx e (Type.Atom "o");
        let hyps = StringMap.add h e hyps in
        [ { g with goal = e }; { g with hyps }]


    open Ast

    (*
     *  -----------------
     *      |- true
     *)
    let true_right _ _ = function
        | {goal = Term.App (Term.Con (Con.Single "true"), []) } ->
            []
        | _ -> failwith "true_right"

    (*
     *  --------------------
     *    h:false |-
     *)
    let false_left h theory _ = function { hyps } ->
        begin match lookup_hyp h theory hyps with
        | Term.App (Term.Con (Con.Single "false"), []) ->
            []
        | _ -> failwith "false_left"
        end

    (*   |- A     |- B
     *  ----------------
     *     |- and A B
     *)
    let and_right _ _ = function
        | {goal = Term.App (Term.Con (Con.Single "and"), [a; b]) } as g ->
            [ { g with goal = a }; {g with goal = b } ]
        | _ -> failwith "and_right"

    (*
     * h0: A, h1: B |-
     * ----------------------
     *  h: and A B |-
     *)
    let and_left h h0 h1 theory _ =
        function { hyps } as g ->
            begin match lookup_hyp h theory hyps with
            | Term.App (Term.Con (Con.Single "and"), [a; b]) ->
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
    let or_right_0 _ _ = function
        | { goal = Term.App (Term.Con (Con.Single "or"), [a; _]) } as g ->
            [ { g with goal = a } ]
        | _ -> failwith "or_right_0"

    (*
     *      |- B
     * -------------------
     *      |- or A B
     *)
    let or_right_1 _ _ = function
        | { goal = Term.App (Term.Con (Con.Single "or"), [_; b]) } as g ->
            [ { g with goal = b } ]
        | _ -> failwith "or_right_1"


    (*
     *  Gamma; Delta, h0: A |- C       Gamma; Delta, h1: A |- C
     * ---------------------------------------------------------
     *   h: or A B |- C
     *)
    let or_left h h0 h1 theory _ = function { hyps } as g ->
        begin match lookup_hyp h theory hyps with
        | Term.App (Term.Con (Con.Single "or"), [a; b]) ->
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
    let imp_right h _ _ = function
        | { goal = Term.App (Term.Con (Con.Single "imp"), [a; b]) } as g ->
            [ { g with goal = b; hyps = StringMap.add h a g.hyps } ]
        | _ -> failwith "imp_right"


    (*
     *  Gamma; Delta |- A      Gamma; Delta, h': B |- C
     * --------------------------------------------------
     *  Gamma; Delta, h: imp A B |- C
     *)
    let imp_left h h' theory _ = function { hyps } as g ->
        begin match lookup_hyp h theory hyps with
        | Term.App (Term.Con (Con.Single "imp"), [a; b]) ->
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
    let all_right x _ _ = function
        | { hyps; goal = Term.App (Term.Con (Con.Family ("all", typ)), [body]) } as g ->
            let goal = Term.redex (Term.shift body) [Term.var 0 []] in
            let ctx = Typing.Ctx.add x typ g.ctx in
            let hyps = StringMap.map Term.shift hyps in
            [ { ctx; hyps; goal }]
        | _ -> failwith "all_right"

    (*
     *    Gamma |- e : tau      Gamma; Delta, h': A[e] |- C
     * -------------------------------------------------------
     *    Gamma; Delta, h: all x:tau. A[x] |- C
     *)
    let all_left h e h' theory mCtx ({ctx; hyps} as g) =
        match lookup_hyp h theory hyps with
        | Term.App (Term.Con (Con.Family ("all", typ)), [body]) ->
            Theory.check_term theory mCtx ctx e typ;
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
    let ex_right e theory mCtx = function
        | ({ctx; goal = Term.App (Term.Con (Con.Family ("ex", typ)), [body])}) as g ->
            Theory.check_term theory mCtx ctx e typ;
            let goal = Term.redex body [e] in
            [ { g with goal }]
        | _ -> failwith "ex_right"

    (*
     *  Gamma, x:tau; wk(Delta), h: A[x] |- wk(C)
     * ------------------------------------------
     *  Gamma; Delta, h: ex x:tau, A[x] |- C
     *)
    let ex_left h x theory _ {ctx; hyps; goal}=
        match lookup_hyp h theory hyps with
        | Term.App (Term.Con (Con.Family ("ex", typ)), [body]) ->
            let ctx = Typing.Ctx.add x typ ctx in
            let hyps = hyps |>
                       StringMap.remove h |>
                       StringMap.map Term.shift |>
                       StringMap.add h
                          (Term.redex (Term.shift body) [Term.var 0 []]) in
            let goal = Term.shift goal in
            [{ ctx; hyps; goal }]
        | _ -> failwith "ex_left"

    let axiom _ _ _ = []

end
and Proof : sig
    type view = {
        mCtx : Typing.MCtx.t;
        goals : Goal.view list;
        name  : string;
        result : Ast.Term.t;
        theory : Theory.view
    }
    type t = view

    val view : t -> view

    val apply : Tactic.t -> t -> t
    val qed : t -> Theory.t
    val mvar : string -> Type.t -> t -> t
    val set_mvar : string -> Ast.Term.t -> t -> t
end = struct
    type view = {
        mCtx : Typing.MCtx.t;
        goals : Goal.view list;
        name : string;
        result : Ast.Term.t;
        theory : Theory.view
    }
    type t = view

    let view proof = proof

    let mvar name typ ({theory; mCtx} as proof) =
        Theory.check_type theory typ;
        let mCtx = Typing.MCtx.add name typ mCtx in
        { proof with mCtx }

    let set_mvar mvar term ({theory; mCtx; goals} as proof) =
        match Typing.MCtx.lookup mvar mCtx with
        | typ ->
            let mCtx = Typing.MCtx.remove mvar mCtx in
            Theory.check_term theory mCtx Typing.Ctx.empty term typ;
            let goals = List.map (Tactic.mvar_subst term mvar) goals in
            { proof with mCtx; goals }
        | exception Not_found ->
            failwith ("set_mvar: no mvar named" ^ mvar)

    let apply f = function
        | { mCtx; goals = g :: gs; theory } as proof ->
            { proof with goals = (f theory mCtx g) @ gs }
        | { goals = [] } ->
            failwith "apply: no goals"

    let qed proof = 
        let open Theory in
        match proof with
        | { mCtx; goals = []; name; result; theory }
              when Typing.MCtx.is_empty mCtx ->
          let theorems = StringMap.add_unique name result theory.theorems in
          { theory with theorems = theorems }
        | _ ->
          failwith "qed: still unresolved goals/meta variables"
end

