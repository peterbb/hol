%token <string> NAME QNAME
%token ALL EX IMP AND OR
%token LPAR RPAR
%token BACKSLASH DOT COLON
%token ARROW
%token EOF

%{
    open Ast
    open ParseUtil
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
        { Term.Lam (x, abs x 0 t) }
    | ALL x=NAME COLON t=typ0 DOT b=term0
        { Term.App (Term.Con (Con.Family ("all", t)), [Term.Lam (x, abs x 0 b)]) }
    | EX x=NAME COLON t=typ0 DOT b=term0
        { Term.App (Term.Con (Con.Family ("ex", t)), [Term.Lam (x, abs x 0 b)]) }

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
    | name=QNAME spine=list(arg)
        { Term.App (Term.MVar name, spine) }
    | name=NAME spine=list(arg)
        { Term.App (Term.Con (Con.Single name), spine) }
    | LPAR t=term0 RPAR
        { t }

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

