%token <string> NAME
%token ALL EX IMP AND OR
%token LPAR RPAR
%token BACKSLASH DOT COLON
%token ARROW
%token EOF

%{
    open Ast

    let abs x =
        let open Term in
        let rec abs lvl = function
            | Lam (y, t) ->
                Lam (y, abs (lvl + 1) t)
            | App (h, s) ->
                App (abs_head lvl h, List.map (abs lvl) s)
        and abs_head lvl = function
            | Var i -> Var i
            | Con (Con.Single y) when x = y ->
                Var lvl
            | Con (Con.Family (y, _)) when x = y ->
                failwith "abs"
            | Con _ as c ->
                c
    in abs 0
                
%}

%start <Ast.Term.t> term
%start <Ast.Type.t> typ

%%

term:
    | t=term0 EOF
        { t }

term0:
    | t=term1
        { t }
    | t0=term1 IMP t1=term0
        { Term.App (Term.Con (Con.Single "imp"), [t0; t1]) }
    | BACKSLASH x = NAME DOT t = term0
        { Term.Lam (x, abs x t) }
    | ALL x=NAME COLON t=typ0 DOT b=term0
        { Term.App (Term.Con (Con.Family ("all", t)), [Term.Lam (x, abs x b)]) }
    | EX x=NAME COLON t=typ0 DOT b=term0
        { Term.App (Term.Con (Con.Family ("ex", t)), [Term.Lam (x, abs x b)]) }

term1:
    | t=term2
        { t }
    | t0=term2 OR t1=term1
        { Term.App (Term.Con (Con.Single "or"), [t0; t1]) }

term2:
    | t=term3
        { t }
    | t0=term3 AND t1=term2
        { Term.App (Term.Con (Con.Single "and"), [t0; t1]) }

term3:
    | name=NAME spine=list(arg)
        { Term.App (Term.Con (Con.Single name), spine) }

arg:
   | name=NAME
       { Term.App (Term.Con (Con.Single name), []) }
   | LPAR t=term0 RPAR
        { t }


typ:
    | typ=typ0 EOF
        { typ }

typ0:
    | name=NAME
        { Type.Atom name }
    | name=NAME ARROW t=typ0
        { Type.Arrow (Type.Atom name, t) }
    | LPAR t0=typ0 RPAR ARROW t1=typ0
        { Type.Arrow (t0, t1) }

