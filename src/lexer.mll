{ open Parser }

let letter = [ 'a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let diglet = digit | letter
let sym = '_' | '-'

let name = letter (sym | diglet)*

rule type_token = parse
    | [' ' '\t' '\n']+          { type_token lexbuf }
    | "->"                      { ARROW }
    | '('                       { LPAR }
    | ')'                       { RPAR }
    | name                      { NAME (Lexing.lexeme lexbuf) }
    | eof                       { EOF }

and term_token = parse
    | [' ' '\t' '\n']+          { term_token lexbuf }
    | "=>"                      { IMP }
    | "and"                     { AND }
    | "or"                      { OR }
    | '('                       { LPAR }
    | ')'                       { RPAR }
    | '.'                       { DOT }
    | ':'                       { COLON }
    | '\\'                      { BACKSLASH }
    | "all"                     { ALL }
    | "ex"                      { EX }
    | name                      { NAME (Lexing.lexeme lexbuf) }
    | eof                       { EOF }

