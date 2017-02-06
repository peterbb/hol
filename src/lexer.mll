{ open Parser }

let letter = [ 'a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let diglet = digit | letter
let sym = '_' | '-'

let name = letter (sym | diglet)*

rule token = parse
    | [' ' '\t' '\n']+          { token lexbuf }
    | "->"                      { ARROW }
    | "=>"                      { IMP }
    | "and"                     { AND }
    | "or"                      { OR }
    | "all"                     { ALL }
    | "ex"                      { EX }
    | '('                       { LPAR }
    | ')'                       { RPAR }
    | '.'                       { DOT }
    | ':'                       { COLON }
    | '\\'                      { BACKSLASH }
    | (name as name)            { NAME name }
    | '?' (name as name)        { QNAME name }
    | eof                       { EOF }

